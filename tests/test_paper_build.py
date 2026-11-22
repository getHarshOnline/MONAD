"""Exercise the shared paper recipe with real TeX and bibliography tools."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


RECIPE = Path(__file__).resolve().parents[1] / "paper" / "Makefile"
REFERENCE = r"""@book{known,
  author = {Example, Alice},
  title = {A Distinct Bibliography Title},
  publisher = {Example Press},
  year = {2026}
}
"""


class BibliographyBuildTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        required = ("make", "pdflatex", "bibtex", "pdftotext")
        missing = [tool for tool in required if shutil.which(tool) is None]
        if missing:
            raise RuntimeError("Paper build tests require: " + ", ".join(missing))

    def setUp(self):
        scratch = tempfile.TemporaryDirectory(prefix="monad-paper-test-")
        self.addCleanup(scratch.cleanup)
        self.paper = Path(scratch.name) / "Example" / "paper"
        self.paper.mkdir(parents=True)
        shutil.copyfile(RECIPE, self.paper / "Makefile")
        self.env = dict(os.environ, LC_ALL="C", TZ="UTC")
        self.env.pop("MAKEFLAGS", None)
        self.env.pop("MFLAGS", None)
        self.write("references.bib", REFERENCE)

    def write(self, name, text):
        path = self.paper / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def master(self, body, bibliography=True, database="references", style="plain"):
        declarations = (
            rf"\bibliographystyle{{{style}}}" + "\n"
            + rf"\bibliography{{{database}}}" + "\n"
            if bibliography else ""
        )
        self.write(
            "Example.tex",
            "\\documentclass{article}\n\\begin{document}\n"
            + body + "\n" + declarations + "\\end{document}\n",
        )

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
        return result

    def pdf_text(self):
        result = self.run_tool("pdftotext", "Example.pdf", "-")
        self.assertEqual(result.returncode, 0, result.stdout)
        return result.stdout

    def assert_reference_present(self):
        bibliography = (self.paper / "Example.bbl").read_text()
        self.assertIn(r"\bibitem{known}", bibliography)
        self.assertIn("A Distinct Bibliography Title", self.pdf_text())
        self.assertNotIn("undefined", (self.paper / "Example.log").read_text())

    def seed_stale_output(self):
        self.write("Example.bbl", "Stale bibliography must disappear.\n")
        self.write("Example.blg", "Stale successful bibliography log.\n")

    def assert_no_bibliography(self):
        self.assertFalse((self.paper / "Example.bbl").exists())
        text = self.pdf_text()
        self.assertIn("Ordinary body", text)
        self.assertNotIn("Stale bibliography", text)
        self.assertNotIn("References", text)

    def test_valid_citation_is_in_bibliography_and_pdf(self):
        self.master(r"Ordinary body cites \cite{known}.")
        self.build()
        self.assert_reference_present()

    def test_citation_in_included_chapter_is_resolved(self):
        self.write("chapters/cited.tex", r"A chapter cites \cite{known}.")
        self.master(r"\include{chapters/cited}")
        self.build()
        self.assert_reference_present()

    def test_master_without_bibliography_removes_stale_output(self):
        self.master("Ordinary body.", bibliography=False)
        self.seed_stale_output()
        self.build()
        self.assert_no_bibliography()

    def test_uncited_declared_bibliography_removes_stale_output(self):
        self.master("Ordinary body.")
        self.seed_stale_output()
        self.build()
        self.assert_no_bibliography()

    def test_malformed_bibliography_is_refused(self):
        self.master(r"Ordinary body cites \cite{known}.")
        self.write("references.bib", "@book{known, title = {Unclosed title\n")
        self.build(succeeds=False)
        log = (self.paper / "Example.blg").read_text()
        self.assertIn("references.bib", log)
        self.assertIn("error", log.lower())

    def test_missing_cited_bibliography_is_refused(self):
        self.master(r"Ordinary body cites \cite{known}.", database="missing_database")
        self.build(succeeds=False)
        self.assertIn(
            "I couldn't open database file missing_database.bib",
            (self.paper / "Example.blg").read_text(),
        )

    def test_missing_uncited_bibliography_is_not_treated_as_empty(self):
        self.master("Ordinary body.", database="missing_database")
        self.seed_stale_output()
        self.build(succeeds=False)
        self.assertIn(
            "I couldn't open database file missing_database.bib",
            (self.paper / "Example.blg").read_text(),
        )
        self.assertNotIn("Stale bibliography", self.pdf_text())

    def test_missing_bibliography_style_is_refused(self):
        self.master(r"Ordinary body cites \cite{known}.", style="missing_style")
        self.build(succeeds=False)
        self.assertIn(
            "I couldn't open style file missing_style.bst",
            (self.paper / "Example.blg").read_text(),
        )

    def test_unknown_key_fails_even_when_bibtex_exits_successfully(self):
        self.master(r"Ordinary body cites \cite{unknown}.")
        result = self.build(succeeds=False)
        self.assertIn("Unresolved bibliography entries", result.stdout)
        # BibTeX reports this missing key as a warning, with a successful exit.
        native = self.run_tool("bibtex", "Example")
        self.assertEqual(native.returncode, 0, native.stdout)
        self.assertIn("I didn't find a database entry for", native.stdout)
        self.assertNotIn(r"\bibitem{unknown}", (self.paper / "Example.bbl").read_text())


if __name__ == "__main__":
    unittest.main()
