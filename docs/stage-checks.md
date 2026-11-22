# Check a Causality stage candidate

A Causality stage compares a classical candidate and its quantum adaptations at exact source revisions. This is a planned conformance specification, not a report that any repository implements these contracts. A plain stage note records the selected sources, what was compared, the limits, results and unresolved failures. Signed adaptation records wait until a second person or a release needs them.

## Record the resolved candidate

Record producer and consumer revisions, lockfiles, selected features, dependency or promotion paths, schemas, symbols and the mechanical checks that apply. For each mathematical claim, also identify the accepted profile, symbol and field mapping, assumptions, consumer portability class and conformance result. A type-only relationship may make no such claim; state that explicitly instead of treating a build as mathematical evidence.

The repaired finite observer profile is accepted as 0.2, with the interpretation of the detectability threshold and the isolation of a variable's contribution still open. Historical claims using the defective 0.1 interpretation require review. Record whether each consumer remains on its original interpretation, uses a parity-tested adapter, migrates deliberately, uses the result only as historical or comparative evidence, or is blocked. Existing kernel types can support MUON's first stock stack while MONAD's private calibration remains paused.

For schema checks, record the ordered include roots and the physical files resolved by the compiler. Reject substituted or shadowing inputs even when they yield the same descriptor bytes. Use dependency output from the compiler to identify the selected files; matching serialized descriptors alone is insufficient.

## Check each applicable connection

The commands below run from a directory containing the named sibling checkouts. Select exact revisions before running them. The native build guide in each repository owns prerequisites and feature selection. A passing build or test command supplies only the behaviour its checks actually exercise; the contract suite may still be unimplemented.

| Connection | Role at stage close | Required evidence |
| --- | --- | --- |
| MONAD → MUON | Required type dependency | Exact-pin kernel tests, accepted profile, symbol mapping, portability classes and conformance results for the claims used. |
| MONAD → Reckon | Required mathematical correspondence wherever the candidate uses MONAD | Reckon's formula and symbol mapping, assumptions and comparison results. Reckon's current kernel does not import `monad-kernel`; do not claim a Cargo edge. |
| MONAD → HENA | Required type dependency | Exact-pin kernel tests and the hierarchy and resource mapping to the accepted profile. |
| MUON → HENA | Required unit-slot contract | `cargo test --manifest-path HENA/kernel/Cargo.toml` and the slot conformance suite. The present slot is a draft. |
| Reckon → HENA | Required record protocol | HENA kernel tests and the selected store conformance and replay suite. HENA owns its store; the proposed trait and division of verbs are not a published API. |
| MUON → Q-MUON | Required at global close | The exact classical revision Q-MUON builds on, the exact revision of its quantum adaptation, the review of that adaptation and its tests; `cargo test --manifest-path Q-MUON/kernel/Cargo.toml`; inherited slot conformance. |
| HENA → Q-HENA | Required at global close | The exact classical revision Q-HENA builds on, the exact revision of its quantum adaptation, the review of that adaptation and its tests; `cargo test --manifest-path Q-HENA/kernel/Cargo.toml`; inherited swarm conformance. |
| MONAD → Q-MUON and Q-HENA | Required direct kernel dependencies at global close | Exact-pin kernel tests, selected profile, quantum compatibility mapping and conformance results. |
| Q-MUON → Q-HENA | Required at global close | Q-HENA kernel tests and the stage note identifying unit profiles, checkpoints and swarm recovery results. |
| Reckon → Q-HENA | Required at global close | Q-HENA kernel tests and the stage note identifying the Reckon revision, Q-HENA store conformance and replay results. |
| Reckon → Scope | Observational; paced by Scope and Pale | Golden-file parity for the named algorithm and panel contract tests. Rights and compatibility govern the optional Reckon profile. Scope owns its independent runtime check. |
| Admitted case → Reckon corpus → experiment | Independent of stage close | A frozen, secret-free case, permission evidence and curator decision; then a record of permitted use of an exact minted corpus version. Admission and use do not authorize promotion of a learned change. |
| MONAD → other downstream research projects | Observational; wiring only | Building each project's kernel checks wiring. Its own interpretation needs its own consistency check. |
| Evolution mechanism → each host | Proposed, beginning with the stock stack | Evidence for the rule genome against the slot, history in the host store and resource limits from MONAD; separate admission by each affected owner. |

The listed draft contracts begin at v0 unless the candidate names a later version. Contract versions begin with the current draft design and grow compatibly within a stage. Breaking changes require an explicit stage boundary. A global close uses the frozen classical candidate first, then Q-MUON's adaptation, then Q-HENA's composition of the admitted units. The plain note preserves what each check establishes and what remains missing; the programme owner decides whether the stage is complete.

For the quantum evidence fields, recovery refusal cases and later signing design, see [Q-HENA's adaptation specification](https://github.com/getHarshOnline/Q-HENA/blob/main/docs/adaptation-receipt.md). Future relationships between HENA, RawFish and Pale need their own contracts and evidence; they do not follow from a successful Causality stage.
