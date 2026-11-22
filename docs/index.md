# MONAD

MONAD studies what a description can tell apart and which distinctions survive compression or a change of description. Its Lean library defines and proves mathematical results. A paper explains them, and a small Rust kernel provides types and numerical operations for other research code.

Use the Rust kernel to compare finite observation laws from a local checkout. Use Lean to follow a proof or extend the formal library. [Descriptions and repair](https://causality.in/monad/descriptions-and-repair/) and its [four-state worked example](https://causality.in/monad/what-a-summary-preserves/) explain the research without requiring a build. The name is short for Minimal Ontological Notions for Axiomatic Distinction. Category theory and programming languages use “monad” for a different concept.

## MONAD has three surfaces

Lean owns the formal definitions and proofs. Each mathematical module has a matching TeX chapter, so the paper explains the same objects and results. The Rust kernel represents only part of a finite observer model. Its type names and operations need the interpretation in [the kernel guide](kernel.md#what-the-kernel-types-establish).

MONAD runs in a caller’s process. There is no daemon, CLI or service to start.

## The mathematics is partly proved and nothing is published

The Lean library and paper share 42 mathematical modules. The correspondence checker links 82 displayed proofs to Lean declarations. The [coverage register](../formal/coverage.toml) lists open work on coding and local testing, quantum correspondence and review of the paper's statements. Private calibration and further proving are paused.

> [!IMPORTANT]
>
> **Build from a source checkout.** No package is published. The Lean library and paper are in `formal/` and `paper/`, and the wider SDKs and integrations are designs with no implementation. The instructions below assume access to a local checkout.

## Read these pages next

::::card-group

:::card

[Use the Rust kernel](kernel.md#a-first-rust-call)

Create a consumer project and compare two finite probability distributions.

:::

:::card

[Read a theorem in Lean](mathematics.md#read-a-preservation-claim-in-lean)

Translate the four-state example into definitions and inspect the preservation and quotient results.

:::

:::card

[Prepare the toolchains](getting-started.md)

Build the kernel, Lean library or paper and understand what each check covers.

:::

:::card

[Find a formal definition](../formal/README.md#contents)

Look up the mathematical modules and the notation that connects Lean to the paper.

:::

::::

The [repository overview](../README.md) explains the dependency direction and licensing. Return to [the product explanation](https://causality.in/monad/descriptions-and-repair/) for the broader research question.

The [library design](library-design.md) explains the planned language interfaces, shared scene records and acceleration, and what must exist before they are implemented.

Maintainers use `docs/stage-checks.md` in the source checkout to distinguish resolved dependencies from mathematical correspondence when a Causality candidate uses MONAD.
