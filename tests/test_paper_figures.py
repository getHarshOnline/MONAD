"""Check figure replacement and failure recovery with the shared TeX recipe."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


RECIPE = Path(__file__).resolve().parents[1] / "paper" / "Makefile"


class FigureBuildTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        missing = [name for name in ("make", "pdflatex", "bibtex", "pdftotext")
                   if shutil.which(name) is None]
        if missing:
            raise RuntimeError("Figure build tests require: " + ", ".join(missing))

    def setUp(self):
        scratch = tempfile.TemporaryDirectory(prefix="monad-figure-test-")
        self.addCleanup(scratch.cleanup)
        self.paper = Path(scratch.name) / "Example" / "paper"
        self.paper.mkdir(parents=True)
        shutil.copyfile(RECIPE, self.paper / "Makefile")
        self.env = dict(os.environ, LC_ALL="C", TZ="UTC")
        self.env.pop("MAKEFLAGS", None)
        self.env.pop("MFLAGS", None)

    def write(self, name, text):
        path = self.paper / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        return path

    def figure(self, name, body):
        return self.write(
            f"figures/tikz/{name}.tex",
            "\\documentclass{article}\n\\pagestyle{empty}\n"
            "\\begin{document}\n" + body + "\n\\end{document}\n",
        )

    def master(self, *figures):
        body = "Ordinary paper.\n" + "\n".join(
            rf"\includegraphics[width=.4\textwidth]{{figures/pdf/{name}.pdf}}"
            for name in figures
        )
        self.write("Example.tex", "\\documentclass{article}\n"
                   "\\usepackage{graphicx}\n\\begin{document}\n"
                   + body + "\n\\end{document}\n")

    def run_tool(self, *args):
        return subprocess.run(
            args, cwd=self.paper, env=self.env, stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            timeout=60,
        )

    def build(self, succeeds=True):
        result = self.run_tool("make", "all", "MASTER=Example.tex")
        if succeeds:
            self.assertEqual(result.returncode, 0, result.stdout)
        else:
            self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertEqual(list(self.paper.glob("figures/pdf/.build.*")), [])
        return result

    def pdf_text(self, name="Example.pdf"):
        result = self.run_tool("pdftotext", name, "-")
        self.assertEqual(result.returncode, 0, result.stdout)
        return result.stdout

    def good_outputs(self):
        return {p: p.read_bytes() for p in [self.paper / "Example.pdf",
                *sorted(self.paper.glob("figures/pdf/*.pdf"))]}

    def assert_preserved(self, outputs):
        for path, data in outputs.items():
            self.assertEqual(path.read_bytes(), data, str(path))

    def test_nested_edit_ignores_unchanged_size_and_time_and_repairs_damaged_pdf(self):
        nested = self.write("figures/inputs/label.tex", "OLDMARKER\n")
        self.figure("first", r"\input{figures/inputs/label.tex}")
        self.master("first")
        self.build()
        self.assertIn("OLDMARKER", self.pdf_text())
        before = nested.stat()
        nested.write_text("NEWMARKER\n")
        os.utime(nested, ns=(before.st_atime_ns, before.st_mtime_ns))
        self.assertEqual(nested.stat().st_size, before.st_size)
        self.assertEqual(nested.stat().st_mtime_ns, before.st_mtime_ns)
        self.build()
        self.assertIn("NEWMARKER", self.pdf_text())
        self.assertNotIn("OLDMARKER", self.pdf_text())
        (self.paper / "figures/pdf/first.pdf").write_bytes(b"damaged output")
        self.build()
        self.assertIn("NEWMARKER", self.pdf_text("figures/pdf/first.pdf"))
        self.assertIn("NEWMARKER", self.pdf_text())

    def test_missing_nested_input_preserves_outputs_across_retries(self):
        nested = self.write("figures/inputs/label.tex", "ORIGINAL\n")
        self.figure("first", r"\input{figures/inputs/label.tex}")
        self.master("first")
        self.build()
        outputs = self.good_outputs()
        nested.unlink()
        for _ in range(2):
            self.build(succeeds=False)
            self.assert_preserved(outputs)
        nested.write_text("REPAIRED\n")
        self.build()
        self.assertIn("REPAIRED", self.pdf_text())

    def test_failed_first_figure_publishes_no_partial_or_later_output(self):
        self.figure("01-first", r"Partial page.\clearpage\undefinedFigureCommand")
        self.figure("02-second", "Later figure.")
        self.master("01-first", "02-second")
        native_dir = self.paper / "native-control"
        native_dir.mkdir()
        # Nonstop TeX can write a PDF despite an error. The recipe must refuse it.
        native = self.run_tool("pdflatex", "-interaction=nonstopmode",
                               "-output-directory=native-control", "figures/tikz/01-first.tex")
        self.assertNotEqual(native.returncode, 0, native.stdout)
        self.assertTrue((native_dir / "01-first.pdf").exists())
        result = self.build(succeeds=False)
        self.assertEqual(list(self.paper.glob("figures/pdf/*.pdf")), [])
        self.assertFalse((self.paper / "Example.pdf").exists())
        self.assertNotIn("Building figures/tikz/02-second.tex", result.stdout)

    def test_failed_rebuild_ignores_cached_log_and_keeps_last_good_papers(self):
        self.figure("01-first", "FIRSTGOOD")
        self.figure("02-second", "SECONDGOOD")
        self.master("01-first", "02-second")
        self.build()
        outputs = self.good_outputs()
        first = self.figure("01-first", r"Partial page.\clearpage\undefinedFigureCommand")
        self.figure("02-second", "SECONDNEW")
        self.write("figures/pdf/01-first.log", "! Cached failed TeX run.\n")
        # A newer cached PDF must not hide a failing source and failed log.
        cached_time = (self.paper / "figures/pdf/01-first.pdf").stat().st_mtime_ns
        os.utime(first, ns=(cached_time - 1_000_000_000, cached_time - 1_000_000_000))
        for _ in range(2):
            result = self.build(succeeds=False)
            self.assert_preserved(outputs)
            self.assertNotIn("Building figures/tikz/02-second.tex", result.stdout)
        self.figure("01-first", "FIRSTNEW")
        self.build()
        self.assertIn("FIRSTNEW", self.pdf_text())
        self.assertIn("SECONDNEW", self.pdf_text())

    def test_zero_page_figure_is_refused_despite_successful_tex_exit(self):
        self.figure("first", "LASTGOOD")
        self.master("first")
        self.build()
        outputs = self.good_outputs()
        self.figure("first", "")
        native_dir = self.paper / "native-control"
        native_dir.mkdir()
        native = self.run_tool("pdflatex", "-halt-on-error", "-interaction=nonstopmode",
                               "-output-directory=native-control", "figures/tikz/first.tex")
        self.assertEqual(native.returncode, 0, native.stdout)
        self.assertFalse((native_dir / "first.pdf").exists())
        result = self.build(succeeds=False)
        self.assertIn("Figure produced no PDF", result.stdout)
        self.assert_preserved(outputs)

    def test_paper_without_figures_creates_no_figure_directory(self):
        self.master()
        self.build()
        self.assertIn("Ordinary paper", self.pdf_text())
        self.assertFalse((self.paper / "figures/pdf").exists())


if __name__ == "__main__":
    unittest.main()
