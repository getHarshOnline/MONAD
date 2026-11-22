# Getting started

Build the Rust kernel to use it from code, the Lean library to read or extend proofs, or the paper to read the mathematical exposition. Start from a local source checkout and run each block from the repository root. The subshell commands return you to that root when they finish.

For a first calculation, follow [a first Rust call](kernel.md#a-first-rust-call). For a first formal statement, build Lean below and continue with [the preservation example](mathematics.md#read-a-preservation-claim-in-lean).

> [!IMPORTANT]
>
> **There is no released package.** The Lean library and paper build from `formal/` and `paper/` in this repository. A mathematics, paper or kernel change needs all the checks below; a documentation-only change needs its examples and affected links checked.

## The full check set needs four toolchains

::::tabs

:::tab "Rust kernel"

Install Rust with Cargo, Clippy and Rustfmt. The kernel has no external dependencies.

:::

:::tab "Lean library"

Install Lean through `elan`. The versions in `formal/lean-toolchain`, `formal/lakefile.toml` and `formal/lake-manifest.json` keep Lean, mathlib and the other dependencies in step.

:::

:::tab "Correspondence checker"

Install Python 3.11 or later and prepare the Lean environment. Use Python for the checker and its tests.

:::

:::tab "Paper"

Install a TeX distribution with `pdflatex` and `bibtex`, plus Make and Bash. Install `pdftotext` to check the rendered text. The validator reports that check as skipped when the tool is missing.

:::

::::

## Run the checked-in examples and build targets

`make examples` runs the [Rust calculation](../kernel/examples/first_use.rs) and the [Lean reading example](../formal/examples/ReadExample.lean). Use `make example-rust` or `make example-lean` for just one. The Lean target builds the pinned library first.

`make check-formal` builds Lean and runs the strict correspondence checker. It returns failure while the three registered obligation groups remain open; the target does not turn that refusal into success. `make check-formal-partial` runs the same build and the explicitly partial check. The individual commands and their meanings follow below.

`make check-protos` requires `protoc` and sibling source checkouts named MUON, HENA, Q-MUON and Q-HENA, and, when `MONAD_PRIVATE_CONSUMERS` names it, another consumer's checkout. Set that variable to a comma-separated list of sibling checkout names; the script's `--help` explains it. It compiles each header separately, including imports, and writes descriptors and compiler dependency files under the ignored `target/proto-checks/` directory. Override `SIBLING_ROOT` if those checkouts are elsewhere, or `PROTOC` to select the compiler executable. Missing source directories fail before compilation.

Classical HENA uses MUON’s `muon/unit.proto`; Q-HENA uses Q-MUON’s copy of that same virtual path. Their include roots stay separate. The `.d` dependency files identify the physical compiler inputs: equal descriptors do not establish that the same source was read. These are header syntax and import checks, with unused-import warnings expected in message-free headers. They do not check a consumer’s runtime behaviour, pin a release’s source revisions or prove quantum compatibility. Reckon’s self-contained schemas are outside this MONAD-dependent check.

## Build the Lean library

```bash
(cd formal && lake build)
```

The first build downloads mathlib and may take time. Later builds reuse its cache. A successful build means the Lean modules compile; the paper comparison is a separate check.

## Check the paper against Lean

The correspondence checker pairs Lean modules with TeX companions and checks that every displayed proof names a real declaration. It also checks that the proofs depend only on the permitted axioms.

::::steps

:::step "Run the partial check"

```bash
(cd formal && python3 check_correspondence.py --allow-open)
```

This checks the module and proof bindings while allowing the open obligations in the coverage register.

:::

:::step "Run the strict check"

```bash
(cd formal && python3 check_correspondence.py)
```

The strict check runs the same checks and also fails while source-declared obligations remain open. Both modes require `formal/coverage.toml` to match the open-obligation comments in the included TeX sources; an emptied or inconsistent register fails. Strict failure on the three current groups is expected. Close an obligation in its source and register only when its proof or review is complete. The [formal guide](../formal/README.md) explains the markers and the limits of this check.

:::

:::step "Test the checker"

```bash
(cd formal && python3 -m unittest -v test_correspondence)
```

These tests check the checker’s behavior. Reviewing a paper statement still requires comparing its exact hypotheses and conclusion with Lean.

:::

::::

## Test the kernel

Run the tests, lint and formatting check:

```bash
cargo test --manifest-path kernel/Cargo.toml
cargo clippy --manifest-path kernel/Cargo.toml -- -D warnings
cargo fmt --manifest-path kernel/Cargo.toml -- --check
```

## Build the paper

`make check-paper-build` tests the shared bibliography and figure recipe with small temporary papers. It requires Make, Python, `pdflatex`, `bibtex` and `pdftotext`. The bibliography tests check actual entries and rendered text, including citations in included chapters, stale output and errors that BibTeX reports with a successful exit. The figure tests check nested changes, damaged output, failed builds and recovery, including preservation of the last good figure and paper. They leave the research paper unchanged.

```bash
(cd paper && make all && ./validate.sh)
```

`make` finds the master TeX file. The validator checks the sources and build log, then the rendered text when both the PDF and `pdftotext` are available. It reports overfull boxes and optional ChkTeX warnings as counts; review the log as well as the exit code. A skipped text check, an undefined reference or an overfull box still needs attention.

The paper builds on its own. When sibling repositories are cloned beside MONAD, the validator also lints their linked definitions under `paper/shared/`.

Continue with [the kernel](kernel.md) for code integration or [working on the mathematics](mathematics.md) for the formal workflow.
