#!/usr/bin/env python3
"""Check mirrored modules, proof bindings and Lean axioms; never certify prose meaning.

No source files are rewritten. The temporary Lean audit is generated from the
paper's correspondence markers. Outstanding obligations fail the default gate;
--allow-open permits an explicitly partial development check, not release.
"""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import re
import subprocess
import tempfile
import tomllib
import unicodedata


FORMAL = Path(__file__).resolve().parent
ROOT = FORMAL.parent
PAPER = ROOT / "paper"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MARKER = re.compile(r"\\lean(?:proof|def)\{([^}]+)\}")
PROOF = re.compile(r"\\begin\{proof\}(.*?)\\end\{proof\}", re.S)
INPUT = re.compile(r"\\input\{([^}]+)\}")
IDENTIFIER = re.compile(r"MonadFormal(?:\.[A-Za-z_]\w*)+", re.ASCII)
OBLIGATION_ID = re.compile(r"[a-z][a-z0-9-]*", re.ASCII)


def uncomment_tex(text: str) -> str:
    """Remove unescaped TeX comments before following inputs and proof markers."""
    return re.sub(r"(?<!\\)%[^\n]*", "", text)


def included_files(path: Path, visiting: tuple[Path, ...] = (),
                   seen: set[Path] | None = None) -> set[Path]:
    """Resolve the TeX graph, rejecting cycles and duplicate inclusions."""
    path = path.resolve()
    if seen is None:
        seen = set()
    if path in visiting:
        raise ValueError(f"Cyclic TeX input: {path}")
    if path in seen:
        raise ValueError(f"Duplicate TeX input: {path}")
    seen.add(path)
    text = uncomment_tex(path.read_text())
    result = {path}
    for name in INPUT.findall(text):
        child = PAPER / name
        if not child.suffix:
            child = child.with_suffix(".tex")
        result |= included_files(child, (*visiting, path), seen)
    return result


def library_imports(text: str) -> list[str]:
    """Read active public imports, not commented-out wiring."""
    code = re.sub(r"/-.*?-/|--[^\n]*", "", text, flags=re.S)
    return re.findall(r"^import\s+(MonadFormal(?:\.[\w]+)+)\s*$", code, re.M)


def wiring_failures(sources: list[Path], included: set[Path],
                    root_imports: str) -> list[str]:
    """Check reverse companions and reject stale or duplicate public imports."""
    failures: list[str] = []
    modules = {".".join(path.relative_to(FORMAL).with_suffix("").parts)
               for path in sources}
    for module, count in Counter(library_imports(root_imports)).items():
        if module not in modules:
            failures.append(f"Public import has no local source: {module}")
        if count > 1:
            failures.append(f"Duplicate public import: {module}")
    for companion in sorted((PAPER / "MonadFormal").rglob("*.tex")):
        source = FORMAL / companion.relative_to(PAPER).with_suffix(".lean")
        if source not in sources:
            failures.append(f"TeX companion has no Lean source: {companion.relative_to(ROOT)}")
        if companion.resolve() not in included:
            failures.append(f"Unwired TeX companion: {companion.relative_to(ROOT)}")
    return failures


def source_failures(source: Path, included: set[Path], root_imports: str) -> list[str]:
    """Check one Lean module's public import, companion, encoding and spelling."""
    failures: list[str] = []
    relative = source.relative_to(FORMAL)
    module = ".".join(relative.with_suffix("").parts)
    if module not in library_imports(root_imports):
        failures.append(f"Module absent from public root import: {module}")
    companion = PAPER / relative.with_suffix(".tex")
    if companion.resolve() not in included:
        failures.append(f"Missing included companion: {companion.relative_to(ROOT)}")
    text = source.read_text()
    if unicodedata.normalize("NFC", text) != text:
        failures.append(f"Non-normalized Unicode: {relative}")
    # Comments are included when checking for copied editor input hints.
    for token in ("\\rightarrow", "\\imp", "\\to", "\\->", "using \\r"):
        if token in text:
            failures.append(f"Copied input escape {token!r}: {relative}")
    # This scan supplements the actual axiom-dependency check below.
    code = re.sub(r"/-.*?-/|--[^\n]*", "", text, flags=re.S)
    if re.search(r"\bfun\b[^\n↦]*=>|->|\bforall\b|\bexists\b", code):
        failures.append(f"Noncanonical mathematical spelling: {relative}")
    if re.search(r"\b(sorry|admit|axiom|unsafe)\b", code):
        failures.append(f"Untrusted placeholder/declaration: {relative}")
    return failures


def paper_bindings(path: Path) -> tuple[set[str], int, list[str]]:
    """Collect one TeX file's bindings and reject unbound displayed proofs."""
    failures: list[str] = []
    references: set[str] = set()
    text = uncomment_tex(path.read_text())
    proofs = PROOF.findall(text)
    for proof in proofs:
        if not re.search(r"\\leanproof\{[^}]+\}", proof):
            failures.append(f"Unbound proof: {path.relative_to(ROOT)}")
    for marker in MARKER.findall(text):
        for identifier in marker.split(","):
            identifier = identifier.strip()
            if not IDENTIFIER.fullmatch(identifier):
                failures.append(f"Invalid declaration reference: {identifier!r}")
            else:
                references.add(identifier)
    return references, len(proofs), failures


def declaration_failures(references: set[str]) -> list[str]:
    """Resolve declarations and check actual axiom dependencies in pinned Lean."""
    failures: list[str] = []
    with tempfile.TemporaryDirectory(prefix="monad-proof-audit-") as directory:
        audit = Path(directory) / "Correspondence.lean"
        audit.write_text("import MonadFormal\n" + "\n".join(
            f"#check {name}\n#print axioms {name}" for name in sorted(references)) + "\n")
        result = subprocess.run(["lake", "env", "lean", str(audit)], cwd=FORMAL,
                                text=True, capture_output=True, check=False)
    if result.returncode:
        failures.append("Lean declaration/axiom audit failed")
        print(result.stdout + result.stderr)
    for axiom_list in re.findall(r"depends on axioms:\s*\[([^]]*)\]", result.stdout):
        extra = {item.strip() for item in axiom_list.split(",")} - ALLOWED_AXIOMS - {""}
        if extra:
            failures.append(f"Unapproved axioms: {sorted(extra)}")
    return failures


def coverage_failures(included: set[Path]) -> tuple[list[dict[str, str]], list[str]]:
    """Match source-declared open claims to their scopes in the coverage register.

    A standalone `% monad-open: id` comment names unfinished proof or review
    work at its source. These comments do not appear in the rendered paper.
    They are not proof bindings and cannot excuse a missing or untrusted proof.
    """
    failures: list[str] = []
    declared: dict[str, list[str]] = {}
    for path in sorted(included):
        for number, line in enumerate(path.read_text().splitlines(), 1):
            if not line.lstrip().startswith("% monad-open:"):
                continue
            identifier = line.lstrip().removeprefix("% monad-open:").strip()
            location = f"{path.relative_to(ROOT)}:{number}"
            if not OBLIGATION_ID.fullmatch(identifier):
                failures.append(f"Invalid open-obligation marker: {location}")
            else:
                declared.setdefault(identifier, []).append(location)
    try:
        register = tomllib.loads((FORMAL / "coverage.toml").read_text())
    except (OSError, tomllib.TOMLDecodeError) as error:
        return [], failures + [f"Cannot read coverage register: {error}"]
    if (type(register.get("schema")) is not int or register["schema"] != 1
            or set(register) - {"schema", "open"}):
        failures.append("Coverage register requires schema = 1 and only open entries")
    pending = register.get("open", [])
    if not isinstance(pending, list):
        return [], failures + ["Coverage open entries must be an array of tables"]
    entries: dict[str, dict[str, str]] = {}
    for item in pending:
        if (not isinstance(item, dict) or set(item) != {"id", "scope"}
                or not isinstance(item["id"], str)
                or not OBLIGATION_ID.fullmatch(item["id"])
                or not isinstance(item["scope"], str) or not item["scope"].strip()):
            failures.append("Each coverage entry needs a valid id and nonempty scope")
            continue
        if item["id"] in entries:
            failures.append(f"Duplicate coverage obligation: {item['id']}")
        entries[item["id"]] = item
    for identifier in sorted(declared.keys() - entries.keys()):
        failures.append(f"Open source obligation absent from coverage: {identifier} "
                        f"({', '.join(declared[identifier])})")
    for identifier in sorted(entries.keys() - declared.keys()):
        failures.append(f"Coverage obligation has no included source marker: {identifier}")
    return list(entries.values()), failures


def kernel_bindings(path: Path) -> tuple[set[str], list[str]]:
    """Read the Lean comparison, or explicit gap, on each public kernel type.

    Fields and associated methods use their type's reference and qualifications.
    Resolving a reference checks its existence and axioms, not Rust conformance.
    """
    references: set[str] = set()
    failures: list[str] = []
    docs: list[str] = []
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if line.startswith("///"):
            docs.append(line[3:].strip())
            continue
        if not line.strip() or line.startswith("#["):
            continue
        item = re.match(r"pub (?:struct|enum|trait|type) (\w+)\b", line)
        if item:
            location = f"{path.relative_to(ROOT)}:{number} ({item[1]})"
            markers = [doc.removeprefix("Lean: ") for doc in docs if doc.startswith("Lean:")]
            if len(markers) != 1:
                failures.append(f"Kernel type needs one Lean reference or explained gap: {location}")
            else:
                marker = markers[0]
                name = re.fullmatch(r"`([^`]+)`\.", marker)
                if name and IDENTIFIER.fullmatch(name[1]):
                    references.add(name[1])
                elif not (marker.startswith("none. ") and marker[6:].strip()):
                    failures.append(f"Invalid kernel Lean reference: {location}")
        docs = []
    return references, failures


def main() -> int:
    """Build Lean and audit structural parity without claiming prose equivalence."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--allow-open", action="store_true")
    args = parser.parse_args()
    build = subprocess.run(["lake", "build"], cwd=FORMAL,
                           text=True, capture_output=True, check=False)
    if build.returncode:
        print(build.stdout + build.stderr)
        print("FAIL: fresh Lean build did not pass")
        return 1
    try:
        included = included_files(PAPER / "MONAD.tex")
    except (OSError, ValueError) as error:
        print(f"FAIL: TeX inclusion graph: {error}")
        return 1
    sources = sorted((FORMAL / "MonadFormal").rglob("*.lean"))
    root_imports = (FORMAL / "MonadFormal.lean").read_text()
    failures = wiring_failures(sources, included, root_imports)
    for source in sources:
        failures.extend(source_failures(source, included, root_imports))
    references: set[str] = set()
    proof_count = 0
    for path in sorted(included):
        names, count, issues = paper_bindings(path)
        references.update(names)
        proof_count += count
        failures.extend(issues)
    kernel_references: set[str] = set()
    for path in sorted((ROOT / "kernel" / "src").rglob("*.rs")):
        names, issues = kernel_bindings(path)
        kernel_references.update(names)
        failures.extend(issues)
    failures.extend(declaration_failures(references | kernel_references))

    pending, issues = coverage_failures(included)
    failures.extend(issues)
    print(f"Checked {len(sources)} mirrored modules, {proof_count} paper proofs, "
          f"{len(references)} declaration bindings.")
    print(f"Checked {len(kernel_references)} kernel Lean references; "
          "reference resolution does not prove implementation correspondence.")
    for item in pending:
        print(f"OPEN {item['id']}: {item['scope']}")
    if pending and not args.allow_open:
        failures.append(f"{len(pending)} outstanding proof/claim obligations")
    for failure in failures:
        print(f"FAIL: {failure}")
    if failures:
        return 1
    print("PARTIAL CORRESPONDENCE CHECK PASSED; open obligations remain."
          if pending else "CORRESPONDENCE CHECK PASSED; semantic review remains necessary.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
