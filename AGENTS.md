# Working on MONAD

MONAD studies what a description preserves, hides or loses when the descriptions and the questions asked of them can change. It supplies the mathematical foundations for the Causality research family: Lean owns the definitions and proofs, the paper explains them, and a small Rust kernel supplies types and finite-distribution calculations to consumers. Calibration and further proving are paused; documentation edits do not resume them.

Start with the [README](README.md), [getting started](docs/getting-started.md), [formal conventions and module index](formal/README.md), and the [kernel's guarantees and limits](docs/kernel.md).

## Keep each mathematical meaning in its owner

Definitions and proofs live in `formal/MonadFormal/`, with same-path TeX companions under `paper/MonadFormal/`. Shared definitions belong in their owning module; imports and declaration bindings connect their users. Follow the formal guide's notation, documentation and refactoring conventions, updating companions, imports and bindings together. Reuse existing mathematics before introducing new definitions, and compare exact assumptions and conclusions when relating results.

The Rust source in `kernel/src/` implements part of the mathematics and needs its own tests. Read its documented compatibility limits and units before changing or using a type; a Lean theorem does not establish that a Rust consumer implements it. Contract bundles, SDKs, integrations and GPU paths remain designs without implementations. The library runs inside its caller, with no service to start.

## Run the checks for the changed part

The setup guide owns prerequisites, including the pinned Lean/mathlib environment, Python 3.11 or later, Rust and TeX tools. From the repository root:

```sh
cargo test --manifest-path kernel/Cargo.toml
cargo clippy --manifest-path kernel/Cargo.toml -- -D warnings
cargo fmt --manifest-path kernel/Cargo.toml -- --check
(cd formal && lake build)
(cd formal && python3 check_correspondence.py --allow-open)
(cd formal && python3 check_correspondence.py)
(cd formal && python3 -m unittest -v test_correspondence)
(cd paper && make all && ./validate.sh)
```

When changing the mathematics, paper or kernel, run the full set described in the setup guide. Documentation-only edits need their examples and affected links checked. During proof work, also inspect Lean InfoView and editor diagnostics as the formal guide describes.

Lean builds check proofs under their stated hypotheses; the correspondence checker checks module and declaration bindings, kernel type references and permitted axioms. Strict mode currently fails on the open groups in [coverage.toml](formal/coverage.toml); `--allow-open` permits a partial check. Both modes require the register to match the open-obligation comments in the included paper sources. Missing bindings and untrusted proofs fail in either mode. The checker cannot discover every obligation in mathematical prose; keep source markers and register entries until their proof or review is complete. Statement-level review, Rust behaviour and the rendered paper each need their own check; review validator warnings and skipped checks as well as its exit code.

<!-- BEGIN shared repository rules -->

- Review a source file above 1,000 lines and split it by concern before 1,500.
- Keep Rust tests under `tests/`; keep Go's `_test.go` files beside their package.
- Finish a goal with the codebase the same size or smaller unless a requested feature requires growth. Preserve the behaviour, tests, cases and examples.
- Every engine must build from a fresh clone on Linux and macOS.
- Keep generated API reference and build output out of Git; change their source or generator.
- Write comments and API documentation for the code's reader. A crate or module comment first says what it is for in the system, what it builds on and what builds on it, then its purpose, inputs, results and useful edge cases, with the purpose written problem-first in the present tense: the problem it solves and what solves it today. One plain line after that opening says what is not built yet, as the problem now in front of it, and a negative appears only where a reader would expect the opposite: a limit stated as a property of what exists stays ("it runs on loopback with no caller authentication"), while a negative measured against the finished design is a hedge. Keep them self-contained, with links inside the repository.
- Push each repository as one commit whose whole message is `init`, with Harsh as author and committer under the account the folder uses and no `Co-Authored-By` or `Claude-Session` trailers; later commits stay short and plain.
- Describe the present design and research. The repository neither links nor ships lineage: earlier papers, predecessor versions, history tags and the commits behind them.
- Public repository files, including generated text, link within the repository or to public addresses their readers can open.
- A README is the repository's front door: it carries the product account for the technical reader who arrives there, opening with the product's plain name and the problem it solves, in the words its published pages use.
- Name every operation, command, tool, type, field and variable so a reader without its author's context can tell what it does, what it enables and when to use it; docstrings say the same. Keep full-field record schemas for the engine's consistency, named in plain words like everything else, and author each surface's schemas separately, one per intent, in its caller's terms: SDKs and APIs, the command line, the language server and the agent protocols (MCP, A2A, ACP) are different surfaces with different callers, and the agent protocols compose intents over the operations the others expose.
- Write each Markdown paragraph on one source line. Run the repository's formatter with `proseWrap: never` on changed Markdown.

<!-- END shared repository rules -->

Before handing back:

- Are the definitions, hypotheses, notation and paper statements consistent with their owning Lean declarations?
- Does each claim distinguish formal results, executable behaviour and remaining obligations?
- Did the checks cover the changed part, with their limits stated and the research pause preserved?
