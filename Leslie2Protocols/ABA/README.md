# The ABA case study — file guide

Machine-checked safety (Validity ∧ Agreement) for randomized asynchronous binary
agreement, following the "Verifying ABA with Leslie" blueprint. Every headline is in
`Results.lean` — `ABA.main`, `ABA.refines`, `ABA.chainSim`, `ABA.protocol_safe`,
`ABA.protocol_traces`, `ABA.hybrid_spec`, `ABA.composed_safe` — all axiom-clean and
guarded.

The architecture in one line, all of it in the protocol's own coordinates:

```
protocol  ⊑  composed  ⊑  hybrid  ⊑  ABA.spec
```

- `protocol` — the protocol as it runs: `n` corruption-blind programs beside the network
  adversary, which owns the message pools and the corrupted set, and the coin oracle,
  the only component whose transitions are not Dirac. A program holds its round loop beside
  its stage-side record — the stage record of every round the process has touched, in a
  finite map — and terminates once its own return has fired and `2f + 1` DECIDED receipts
  are on record (D22).
- `composed` — the same protocol read as a composition of components: the round
  instances, the `n` round loops, the ABA-side network holding the DECIDED pools, and the
  coin oracle. `protocolSim` carries `protocol` into it along the Dirac lift of
  `ProtocolRel`, and `protocol_composed` is the inclusion it yields. The relation pins every
  composed coordinate against the protocol state: the entry of process `j` in the instance of
  round `r` is the stage record of round `r` that `j` holds (D22). What makes the inclusion
  one-directional is on the composed side. A round instance has a row for the Byzantine
  graded-agreement drives and no program of the protocol has one (D11), and the instance's
  stage rules carry no termination guard, so the instance answers a send or a delivery at a
  process the protocol has terminated. This is where the chain passes from implementation to
  specification.
- `hybrid` — each round's instance replaced by the graded agreement specification
  (`substSim`), the other three components untouched. This is what the core simulation runs on.
- `ABA.spec` — the single-automaton reading of agreement, reached by `coreSim`.

Components talk only through synchronized labels, and no component reads another's state.
Why the cut sits there, and what it buys, is `../DESIGN-Composition.md`.

## Scope

GBCA is verified to **implementation** level; WCC is **assumed** at specification level
(its coin is `wccPMF`). `ValidityTrace` is the paper-form predicate (D13): every return of
`b` is preceded by a `callABA _ b` from a caller that is never corrupted anywhere in the
trace. The `f + 1` `SuppOK` support counts are the invariant machinery that makes this
provable, not the predicate itself. Safety only — no termination, liveness,
unpredictability or fairness. The protocol's `terminate` rule is a rule of the model, not a
result: no theorem says when it fires, or that it ever does.

## Deviations

Each departure from the source blueprint carries a label D1–D22, cited at the point where
it applies. The registry — every active label glossed — is the Deviations paragraph of
`../../blueprint/src/content.tex`.
`../NOTES-Fidelity.md` covers how the encoding stands against its two sources beyond that
registry.

## The files

Each file's module docstring is the account of record for it; the table says only what
the file is. The order is the dependency order.

| file | lines | what it is |
|---|---|---|
| `Params.lean` | 125 | The parameters `P` — `n`, `f` with `n > 3f`, and the coin distribution `wccPMF` with its ε/δ bounds. |
| `Labels.lean` | 141 | The shared label alphabet `Lab n`: the visible API, the hidden sub-protocol handshakes, `τ`. |
| `Spec.lean` | 196 | **The top-level ABA specification**, the system all safety is measured against. Six rules over `SpecState`, whose control mode carries the flip (D21). The decision is gated on the `f + 1` support guard `SuppOK` alone (D13). |
| `WCCSpec.lean` | 163 | The weak common coin specification, per round, and the coin value domain `TVal`. Held at specification level by design. |
| `GBCASpec.lean` | 268 | The graded binding crusader agreement specification, per round. Binding is negative (D19). |
| `SpecSafety.lean` | 567 | `spec_safe`: every positive-mass trace of `ABA.spec` is valid and agreeing. The trace predicates live here. |
| `GBCASafety.lean` | 590 | Binding, graded agreement and Validity's safety half for the GBCA specification instance. |
| `GBCAImpl.lean` | 748 | **The GBCA implementation**, ABDY22's Algorithm 6 in full (D18). Its state is the stage records beside the round's fabric. |
| `GBCASim.lean` | 1808 | The per-instance refinement `implRefines`, by kill-on-demand: `dead` carried as a receipt-pattern certificate; and the broadcast compatibility of its relation with the `fail` act (`instRel_corrupt`), which the family lifting consumes. |
| `Core.lean` | 223 | **The ABA round loop**, per process and nothing else: the phase machine, the control record, the round-loop record. |
| `Components.lean` | 838 | The extended alphabet `NLab n`, the coin oracle read along its label pullback, the round loop of one process, and the ABA-side network — the pieces the two compositions are built from. |
| `ABAState.lean` | 327 | The ABA-side state as one object: the round-loop records beside the DECIDED network, with the accessors the invariant is stated in. |
| `Protocol.lean` | 1379 | **The protocol as it runs**, and the subject of the whole chain: the programs, each holding its round loop beside its stage-side record (D22), the network adversary, and the pipeline that composes them beside the coin oracle. |
| `GBCAInstances.lean` | 1635 | **The round's graded-agreement instance** and the licence to replace it, `subSim`. |
| `Hybrid.lean` | 729 | **`composed`**, **`substSim`**: the same protocol read as four components, one round instance per round retained at every moment, and that graded-agreement component then replaced by its specification under the four congruences. |
| `CoreSimRel.lean` | 667 | The core simulation's relation: the lazy abstract twin `Abs` and the concrete invariant `Inv`. |
| `CoreSimInv.lean` | 3809 | Step inversion for `hybrid`, then preservation of `Inv` across every row. The bulk of the proof text. |
| `CoreSimAbs.lean` | 335 | `Abs` preservation for the stutter rows, and the assembly `Inv.step`. |
| `CoreSimBurst.lean` | 53 | The abstract-twin burst kit: `SpecStep.decide` as a τ-burst (`decide_step`), and a burst closed by a visible step (`weakStep_of_burst_then_step`). |
| `CoreSim.lean` | 406 | **`coreSim`**: the simulation proof itself, one row per concrete step class. |
| `ProtocolSim.lean` | 1004 | **`protocolSim`**, **`protocol_composed`**: the protocol carried into the composed reading along `ProtocolRel`, whose five unguarded conjuncts determine the composed state. |
| `Results.lean` | 209 | The deliverables, gathered so every citable statement is in one file. Twelve `#guard_msgs` axiom firewalls. |
| `NonVacuity.lean` | 623 | A concrete 21-step run of `hybrid P4` to a `retABA` decision, so the simulation about it is not vacuous. |

The pieces both compositions are built from are in `Components.lean`. `Protocol.lean` and
`GBCAInstances.lean` each import it and neither imports the other, so the two readings of
the protocol are assembled independently over one set of components. The specification side —
`GBCAInstances.lean`, `Hybrid.lean` and the core simulation above them — never imports
`Protocol.lean`; the protocol enters only at `ProtocolSim.lean`, which is where the two
readings meet, and `Results.lean` reaches it through that file.

## Suggested first read

`Params` → `Labels` → `Spec` → skim `SpecSafety`'s two trace predicates → `Core`'s module
docstring → `Protocol`'s (the system the headlines are about) → `Hybrid`'s (the system the
core simulation starts from) → `Results`, whose docstring names the three steps of the
chain and their files. Follow it into the statements along `ProtocolSim.protocolSim` →
`Hybrid.substSim` → `CoreSim.coreSim`, with `ABAState`'s `ABAState` beside the last.
That is roughly 700 lines of reading and gives the full statement-level picture; descend
into the GBCA and core-simulation proofs only when you want them.

## Where else to look

`../README.md` maps the library and its shared framework. `../DESIGN-Composition.md` is why
the chain is cut where it is; `../DESIGN-CoreSim.md` and `../DESIGN-GBCASim.md` are the
narrative accounts of the two large proofs; `../NOTES-Fidelity.md` is the encoding against
its sources and `../NOTES-Liveness-Roadmap.md` what termination would take. The prose
account is the ABA chapter of `../../blueprint/src/`, in two editions over one set of
statements: the default one (`content.tex`, each object and result stated against its Lean
declaration) and the full one (`content-full.tex`, adding the rule inventories, the
pseudocode and the proof bodies).

## Future work

- **Achievability theorem**: one explicit scheduler for `protocol P4` driving a two-return
  decision trace `t`, with `∃ D ∈ achievableTraceDists (protocol P4), D t ≠ 0` — the
  machine-checked non-vacuity for `main`'s own system, exercising Agreement with two returns.
- **Budget as an assumption throughout** (not pursued): the alternative shape is an
  unguarded `fail` in every system, `|F| ≤ f` relativized out of the invariants, and every
  headline conditional on a trace-level budget predicate. It is unnecessary here: in
  `Protocol.lean` the budget is a component guard on the one box that owns the corrupted
  set, so `protocol_safe` and `protocol_traces` need no hypothesis on the trace.
- **`ValidityTrace` witness strengthening**: the current witness clause accepts any
  preceding `callABA id' b`; the proof yields a stronger ghost-backed witness. Care: while
  nothing is decided the D13 ghost record holds the bit of the *last* `SpecStep.callSet`
  (D16 overwrite), so a "first call" restatement is not immediate.
