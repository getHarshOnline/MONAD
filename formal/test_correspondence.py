"""Regression tests for the structural gate; these do not replace Lean proofs."""

from pathlib import Path
from contextlib import contextmanager, redirect_stdout
import io
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_correspondence as audit


@contextmanager
def paper_fixture(register: str, marker: str = "claim-review"):
    """A wired paper and library; only the external Lean process is substituted."""
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory).resolve()
        formal, paper = root / "formal", root / "paper"
        (formal / "MonadFormal").mkdir(parents=True)
        (paper / "MonadFormal").mkdir(parents=True)
        (formal / "MonadFormal.lean").write_text("import MonadFormal.X\n")
        (formal / "MonadFormal/X.lean").write_text("theorem claim : True := True.intro\n")
        (formal / "coverage.toml").write_text(register)
        (paper / "MONAD.tex").write_text("\\input{MonadFormal/X}\n")
        (paper / "MonadFormal/X.tex").write_text(
            f"% monad-open: {marker}\n"
            "\\begin{proof}\\leanproof{MonadFormal.X.claim}\\end{proof}\n")
        with (patch.object(audit, "ROOT", root), patch.object(audit, "FORMAL", formal),
              patch.object(audit, "PAPER", paper)):
            yield formal, paper


class CorrespondenceTests(unittest.TestCase):
    """Keep diagnostic refactoring from weakening the correspondence checks."""

    def test_ascii_identifiers_only(self):
        """The concise regex preserves the previous ASCII identifier contract."""
        for name in ("MonadFormal.Repair.optimalCost", "MonadFormal.X.test_2"):
            self.assertIsNotNone(audit.IDENTIFIER.fullmatch(name))
        for name in ("MonadFormal", "MonadFormal.2bad", "MonadFormal.X.α", "MonadFormal.X.aé"):
            self.assertIsNone(audit.IDENTIFIER.fullmatch(name))

    def test_kernel_type_references_and_explicit_gaps(self):
        """Each public type carries a resolvable name or a reason it has none."""
        text = ("/// Comparison only; no conformance proof.\n"
                "/// Lean: `MonadFormal.Approximation.tv`.\n"
                "#[derive(Clone)]\npub struct Distance;\n"
                "/// Lean: none. Caller-chosen machine encoding.\n"
                "pub type Index = usize;\n")
        with patch.object(Path, "read_text", return_value=text):
            references, failures = audit.kernel_bindings(audit.ROOT / "kernel/src/test.rs")
        self.assertEqual(references, {"MonadFormal.Approximation.tv"})
        self.assertFalse(failures)

    def test_missing_and_invalid_kernel_references(self):
        """Malformed markers, unexplained gaps and an unmarked type fail."""
        for docs in ("", "/// Lean: none.\n", "/// Lean: `MonadFormal.2bad`.\n",
                     "/// Lean: `MonadFormal.A`.\n/// Lean: `MonadFormal.B`.\n",
                     "// Lean: `MonadFormal.A`.\n"):
            with self.subTest(docs=docs), patch.object(Path, "read_text", return_value=docs + "pub trait Test {}"):
                _, failures = audit.kernel_bindings(audit.ROOT / "kernel/src/test.rs")
                self.assertEqual(len(failures), 1)

    def test_unresolved_declaration_fails(self):
        """A stale kernel or paper name fails the shared actual-Lean audit."""
        result = subprocess.CompletedProcess([], 1, "unknown constant", "")
        with (patch.object(audit.subprocess, "run", return_value=result),
              redirect_stdout(io.StringIO())):
            failures = audit.declaration_failures({"MonadFormal.missing"})
        self.assertIn("Lean declaration/axiom audit failed", failures)

    def test_kernel_references_reach_shared_lean_audit(self):
        """The full check resolves Rust references alongside paper bindings."""
        register = 'schema = 1\n[[open]]\nid = "claim-review"\nscope = "Review."\n'
        with paper_fixture(register):
            source = audit.ROOT / "kernel/src/lib.rs"
            source.parent.mkdir(parents=True)
            source.write_text("/// Lean: `MonadFormal.kernelReference`.\npub struct Kernel;\n")
            lean = subprocess.CompletedProcess([], 0, "", "")
            with (patch("sys.argv", ["check_correspondence.py", "--allow-open"]),
                  patch.object(audit.subprocess, "run", return_value=lean),
                  patch.object(audit, "declaration_failures", return_value=[]) as resolve,
                  redirect_stdout(io.StringIO())):
                self.assertEqual(audit.main(), 0)
            resolve.assert_called_once_with({"MonadFormal.X.claim", "MonadFormal.kernelReference"})

    def test_comments_do_not_supply_bindings(self):
        """A commented-out proof marker does not certify a displayed proof."""
        text = "\\begin{proof}\n% \\leanproof{MonadFormal.X.fake}\ntext\n\\end{proof}"
        with patch.object(Path, "read_text", return_value=text):
            names, count, failures = audit.paper_bindings(audit.PAPER / "test.tex")
        self.assertEqual(names, set())
        self.assertEqual(count, 1)
        self.assertEqual(len(failures), 1)
        self.assertIn("Unbound proof", failures[0])

    def test_bound_proof(self):
        """Multiple declarations resolve to a deduplicated reference set."""
        text = ("\\begin{proof}text\\leanproof{MonadFormal.X.a, MonadFormal.X.b}"
                "\\end{proof}\\leandef{MonadFormal.X.a}")
        with patch.object(Path, "read_text", return_value=text):
            names, count, failures = audit.paper_bindings(audit.PAPER / "test.tex")
        self.assertEqual(names, {"MonadFormal.X.a", "MonadFormal.X.b"})
        self.assertEqual(count, 1)
        self.assertFalse(failures)

    def test_source_checks(self):
        """An actual placeholder and ASCII mathematical spellings remain failures."""
        source = audit.FORMAL / "MonadFormal" / "Test.lean"
        companion = audit.PAPER / "MonadFormal" / "Test.tex"
        with patch.object(Path, "read_text", return_value="def f := fun x => x\nsorry\n"):
            failures = audit.source_failures(source, {companion}, "import MonadFormal.Test\n")
        self.assertEqual(len(failures), 2)
        self.assertTrue(any("Untrusted" in issue for issue in failures))
        self.assertTrue(any("Noncanonical" in issue for issue in failures))

    def test_missing_mirror_and_import(self):
        """A clean body cannot excuse an absent companion or public import."""
        source = audit.FORMAL / "MonadFormal" / "Test.lean"
        with patch.object(Path, "read_text", return_value="def f := fun x ↦ x\n"):
            failures = audit.source_failures(source, set(), "")
        self.assertEqual(len(failures), 2)

    def test_trusted_axioms(self):
        """Lean's permitted foundational axioms still pass the dependency check."""
        result = subprocess.CompletedProcess([], 0,
            "depends on axioms: [propext, Classical.choice, Quot.sound]", "")
        with patch.object(audit.subprocess, "run", return_value=result):
            self.assertFalse(audit.declaration_failures({"MonadFormal.X.a"}))

    def test_commented_import_is_not_wiring(self):
        """Comments cannot make a missing public import appear present."""
        text = "-- import MonadFormal.X\n/- import MonadFormal.Y\n-/\nimport MonadFormal.Z\n"
        self.assertEqual(audit.library_imports(text), ["MonadFormal.Z"])

    def test_duplicate_and_stale_imports(self):
        """The public root must not keep moved or repeated modules."""
        imports = "import MonadFormal.X\nimport MonadFormal.X\n"
        with patch.object(Path, "rglob", return_value=[]):
            failures = audit.wiring_failures([], set(), imports)
        self.assertEqual(len(failures), 2)

    def test_orphan_companion(self):
        """Reverse parity catches an old TeX file left after a move."""
        companion = audit.PAPER / "MonadFormal" / "Old.tex"
        with patch.object(Path, "rglob", return_value=[companion]):
            failures = audit.wiring_failures([], set(), "")
        self.assertEqual(len(failures), 2)
        self.assertTrue(any("no Lean source" in issue for issue in failures))
        self.assertTrue(any("Unwired" in issue for issue in failures))

    def test_duplicate_tex_input(self):
        """Set union must not hide a companion typeset twice."""
        with patch.object(Path, "read_text", side_effect=[
                "\\input{child}\\input{child}", "text"]):
            with self.assertRaisesRegex(ValueError, "Duplicate TeX input"):
                audit.included_files(audit.PAPER / "test.tex")

    def test_cyclic_tex_input(self):
        """A cycle is diagnosed before recursive traversal continues."""
        with patch.object(Path, "read_text", return_value="\\input{test}"):
            with self.assertRaisesRegex(ValueError, "Cyclic TeX input"):
                audit.included_files(audit.PAPER / "test.tex")

    def test_custom_axiom_rejected(self):
        """A hidden assumption cannot pass merely because the declaration exists."""
        result = subprocess.CompletedProcess([], 0, "depends on axioms: [sorryAx]", "")
        with patch.object(audit.subprocess, "run", return_value=result):
            failures = audit.declaration_failures({"MonadFormal.X.a"})
        self.assertEqual(failures, ["Unapproved axioms: ['sorryAx']"])

    def test_register_cannot_hide_open_source_claims(self):
        """An emptied register fails both modes; only a matching partial check passes."""
        populated = 'schema = 1\n[[open]]\nid = "claim-review"\nscope = "Review the claim."\n'
        for register in (populated, "schema = 1\n"):
            for allow_open in (False, True):
                with self.subTest(register=register, allow_open=allow_open):
                    with paper_fixture(register):
                        output = io.StringIO()
                        argv = ["check_correspondence.py"] + (["--allow-open"] if allow_open else [])
                        lean = subprocess.CompletedProcess([], 0, "", "")
                        with (patch("sys.argv", argv), redirect_stdout(output),
                              patch.object(audit.subprocess, "run", return_value=lean)):
                            status = audit.main()
                        self.assertEqual(status, 0 if register == populated and allow_open else 1)
                        if register != populated:
                            self.assertIn("Open source obligation absent from coverage", output.getvalue())

    def test_coverage_requires_source_and_unique_ids(self):
        """Stale, duplicated and malformed register entries cannot pass silently."""
        cases = [
            ('schema = 1\n[[open]]\nid = "other"\nscope = "Review."', "no included source marker"),
            ('schema = 1\n' + '[[open]]\nid = "claim-review"\nscope = "Review."\n' * 2,
             "Duplicate coverage obligation"),
            ('schema = 1\n[[open]]\nid = "claim-review"', "nonempty scope"),
            ('schema = 1\nopen = "claim-review"', "array of tables"),
            ('schema = true', "schema = 1"),
            ('schema = 1\nclosed = []', "only open entries"),
            ('schema = [', "Cannot read coverage register"),
        ]
        for register, message in cases:
            with self.subTest(register=register), paper_fixture(register) as (_, paper):
                _, failures = audit.coverage_failures({paper / "MonadFormal/X.tex"})
                self.assertTrue(any(message in failure for failure in failures), failures)

    def test_missing_register_and_invalid_marker(self):
        """A missing register or malformed source reference reports a failure."""
        with paper_fixture("schema = 1", "bad id") as (formal, paper):
            (formal / "coverage.toml").unlink()
            _, failures = audit.coverage_failures({paper / "MonadFormal/X.tex"})
            self.assertTrue(any("Invalid open-obligation marker" in f for f in failures))
            self.assertTrue(any("Cannot read coverage register" in f for f in failures))

    def test_matching_obligation_does_not_excuse_unbound_proof(self):
        """Partial coverage still rejects a displayed proof with no Lean binding."""
        register = 'schema = 1\n[[open]]\nid = "claim-review"\nscope = "Review."\n'
        with paper_fixture(register) as (_, paper):
            companion = paper / "MonadFormal/X.tex"
            companion.write_text("% monad-open: claim-review\n\\begin{proof}text\\end{proof}")
            lean = subprocess.CompletedProcess([], 0, "", "")
            output = io.StringIO()
            with (patch("sys.argv", ["check_correspondence.py", "--allow-open"]),
                  patch.object(audit.subprocess, "run", return_value=lean), redirect_stdout(output)):
                self.assertEqual(audit.main(), 1)
            self.assertIn("Unbound proof", output.getvalue())


if __name__ == "__main__":
    unittest.main()
