# The ABA case study — file guide

Machine-checked safety (Validity ∧ Agreement) for randomized asynchronous binary
agreement, following the "Verifying ABA with Leslie" blueprint. Every headline is in
`Results.lean` — `ABA.main`, `ABA.refines`, `ABA.simComposed`, `ABA.deployed_safe`,
`ABA.deployed_spec`, `ABA.deployed_traces`, `ABA.layeredSpec_spec`, `ABA.layered_safe` —
all axiom-clean and guarded.

The architecture in one line, all of it in deployment coordinates:

```
deployed  ⊑  layered  ⊑  layeredSpec  ⊑  ABA.spec
```

- `deployed` — the protocol as it runs: `n` corruption-blind programs beside the network
  adversary, which owns the message pools and the corrupted set, and the coin oracle,
  the only factor whose transitions are not Dirac. A program holds its round loop and one
  graded-agreement stage record, that of the round the loop is in, which the round advance
  resets (D20).
- `layered` — the same protocol read with a layer boundary as a component boundary: the
  round subsystems, the `n` round loops, the DECIDED layer, and the coin oracle.
  `deployedSim` carries `deployed` into it along the Dirac lift of `DepRel`, and
  `deployed_layered` is the inclusion it yields. The link is one-directional: a layered
  state holds one graded-agreement subsystem per round at every moment, where a deployed
  process node holds the stage record of the round it is in and nothing else (D20), so the
  retained per-round memory is specification-side state. This is where the chain passes
  from implementation to specification.
- `layeredSpec` — each round's subsystem replaced by the graded agreement specification
  (`substSim`), the other three factors untouched. This is what the core simulation runs on.
- `ABA.spec` — the single-automaton reading of agreement, reached by `coreSim`.

Components talk only through synchronized labels, and no component reads another's state.
Why the cut sits there, and what it buys, is `../DESIGN-Layering.md`.

## Scope

GBCA is verified to **implementation** level; WCC is **assumed** at specification level
(its coin is `wccPMF`). `ValidityTrace` is the paper-form predicate (D13): every return of
`b` is preceded by a `callABA _ b` from a caller that is never corrupted anywhere in the
trace. The `f + 1` `SuppOK` support counts are the invariant machinery that makes this
provable, not the predicate itself. Safety only — no termination, liveness,
unpredictability or fairness.

## Deviations

Each departure from the source blueprint carries a label cited at the point where it
applies. The registry — every label glossed, with D2, D6 and D7 declared unused — is the
Deviations paragraph of `../../blueprint/src/content.tex`. `../NOTES-Fidelity.md` covers
how the encoding stands against its two sources beyond that registry.

## The files

Each file's module docstring is the account of record for it; the table says only what
the file is. The order is the dependency order.

| file | lines | what it is |
|---|---|---|
| `Params.lean` | 127 | The parameters `P` — `n`, `f` with `n > 3f`, and the coin distribution `wccPMF` with its ε/δ bounds. |
| `Labels.lean` | 146 | The shared label alphabet `Lab n`: the visible API, the hidden sub-protocol handshakes, `τ`. |
| `Spec.lean` | 263 | **The top-level ABA specification**, the system all safety is measured against. Ten rules over `SpecState`. |
| `WCCSpec.lean` | 131 | The weak common coin specification, per round. Held at specification level by design. |
| `GBCASpec.lean` | 267 | The graded binding crusader agreement specification, per round. Binding is negative (D19). |
| `SpecSafety.lean` | 929 | `spec_safe`: every positive-mass trace of `ABA.spec` is valid and agreeing. The trace predicates live here. |
| `GBCASafety.lean` | 598 | Binding, graded agreement and Validity's safety half for the GBCA specification instance. |
| `GBCAImpl.lean` | 707 | **The GBCA implementation**, ABDY22's Algorithm 6 in full (D18). Its state is the stage records beside the round's fabric. |
| `GBCASim.lean` | 1780 | The per-instance refinement `implRefines`, by kill-on-demand: `dead` carried as a receipt-pattern certificate. |
| `GBCAFamily.lean` | 86 | Broadcast compatibility of that refinement's relation with the `fail` act, which the family lifting consumes. |
| `Core.lean` | 225 | **The ABA round loop**, per process and nothing else: the phase machine, the control record, the round-loop node. |
| `CoreView.lean` | 331 | The ABA-side state as one object: the round-loop nodes beside the DECIDED network, with the accessors the invariant is stated in. |
| `CoreSimRel.lean` | 700 | The core simulation's relation: the lazy abstract twin `Abs` and the concrete invariant `Inv`. |
| `CoreSimInv.lean` | 3809 | Step inversion for `layeredSpec`, then preservation of `Inv` across every row. The bulk of the proof text. |
| `CoreSimAbs.lean` | 336 | `Abs` preservation for the stutter rows, and the assembly `Inv.step`. |
| `CoreSimBurst.lean` | 187 | The abstract-twin burst kit: how the twin catches up in one weak step. |
| `CoreSim.lean` | 698 | **`coreSim`**: the simulation proof itself, one row per concrete step class. |
| `Deployed.lean` | 1509 | **The protocol as it runs**, and the subject of the whole chain: the programs, the network adversary, the coin oracle, and the pipeline that composes them. |
| `GBCASubsystem.lean` | 1532 | **The round's graded-agreement subsystem** and the licence to replace it, `subSim`. |
| `Layered.lean` | 1097 | **`layered`**: the same protocol read as four factors, one round subsystem per round retained at every moment. |
| `DeployedSim.lean` | 1091 | **`deployedSim`**, **`deployed_layered`**: the deployed protocol carried into that reading along `DepRel`. |
| `LayeredSpec.lean` | 480 | **`substSim`**: the graded-agreement factor replaced by its specification, under the four congruences. |
| `Results.lean` | 217 | The deliverables, gathered so every citable statement is in one file. Fifteen `#guard_msgs` axiom firewalls. |
| `NonVacuity.lean` | 619 | A concrete 21-step run of `layeredSpec P4` to a `retABA` decision, so the simulation about it is not vacuous. |

## Suggested first read

`Params` → `Labels` → `Spec` → skim `SpecSafety`'s two trace predicates → `Core`'s module
docstring → `Deployed`'s (the system the headlines are about) → `LayeredSpec`'s (the system
the core simulation starts from) → `Results`, whose docstring names the three steps of the
chain and their files. Follow it into the statements along `DeployedSim.deployedSim` →
`LayeredSpec.substSim` → `CoreSim.coreSim`, with `CoreView`'s `ABAState` beside the last.
That is roughly 700 lines of reading and gives the full statement-level picture; descend
into the GBCA and core-simulation proofs only when you want them.

## Where else to look

`../README.md` maps the library and its shared framework. `../DESIGN-Layering.md` is why
the chain is cut where it is; `../DESIGN-CoreSim.md` and `../DESIGN-GBCASim.md` are the
narrative accounts of the two large proofs; `../NOTES-Fidelity.md` is the encoding against
its sources and `../NOTES-Liveness-Roadmap.md` what termination would take. The prose
account is the ABA chapter of `../../blueprint/src/`, in two editions over one set of
statements: the default one (`content.tex`, each object and result stated against its Lean
declaration) and the full one (`content-full.tex`, adding the rule inventories, the
pseudocode and the proof bodies).

## Future work

- **Achievability theorem**: one explicit scheduler for `deployed P4` driving a two-return
  decision trace `t`, with `∃ D ∈ achievableTraceDists (deployed P4), D t ≠ 0` — the
  machine-checked non-vacuity for `main`'s own system, exercising Agreement with two returns.
- **Budget as an assumption throughout** (not pursued): the alternative shape is an
  unguarded `fail` in every system, `|F| ≤ f` relativized out of the invariants, and every
  headline conditional on a trace-level budget predicate. It is unnecessary here: in
  `Deployed.lean` the budget is a component guard on the one box that owns the corrupted
  set, so `deployed_safe` and `deployed_traces` need no hypothesis on the trace.
- **`ValidityTrace` witness strengthening**: the current witness clause accepts any
  preceding `callABA id' b`; the proof yields a stronger ghost-backed witness. Care: the
  D13 ghost is *last*-rule-1-write (D16 junk-erasure), so a "first call" restatement is not
  immediate.
