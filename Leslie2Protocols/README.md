# Leslie2Protocols — the protocol case studies

The second of the repository's three Lake libraries. It imports the core `Leslie2` and
nothing in the core imports it. Both are default `lake build` targets, so the API
documentation covers them and the blueprint's links resolve.

## `ABA/`

The asynchronous binary agreement development: machine-checked safety for randomized ABA,
from the protocol as it runs down to a small specification, by probabilistic forward
simulation. 24 files, and its own file guide in [`ABA/README.md`](ABA/README.md).

## `Framework/`

The protocol-independent combinators the case study composes with. One of them —
restriction along the left summand of an extended alphabet — is a fourth precongruence,
beside the three in the core.

| file | lines | what it is |
|---|---|---|
| [`TraceSupport.lean`](Framework/TraceSupport.lean) | 594 | From trace-distribution support to genuine executions: the safety transfer, the invariant inductions, and the label-side transport of a run. |
| [`IdleFamily.lean`](Framework/IdleFamily.lean) | 221 | Idle padding, partial label pullbacks, and ℕ-indexed instance families with a broadcast disjunct. |
| [`FamilySim.lean`](Framework/FamilySim.lean) | 385 | Forward simulation is a congruence for `System.family`: per-instance refinement lifts to the family. |
| [`SyncProduct.lean`](Framework/SyncProduct.lean) | 164 | Full-synchronisation product of a finite family — a visible label moves every component, τ moves one. |
| [`Relabel.lean`](Framework/Relabel.lean) | 471 | Extended alphabets and restriction along the left summand, with the precongruence for it. |

## Notes

| file | what it is for |
|---|---|
| [`DESIGN-Composition.md`](DESIGN-Composition.md) | Why the chain is cut where it is: what the composition buys, where each network is external, and what the DECIDED model already weakens. |
| [`DESIGN-CoreSim.md`](DESIGN-CoreSim.md) | The narrative account of the core simulation `hybrid ⊑ ABA.spec` — the abstract twin, the invariant, and the certificates decided values ride on. |
| [`DESIGN-GBCASim.md`](DESIGN-GBCASim.md) | The narrative account of the per-instance GBCA refinement — kill-on-demand, the receipt-pattern certificates, and the burst structure. |
| [`NOTES-Fidelity.md`](NOTES-Fidelity.md) | How the encoding stands against its two sources, the Leslie blueprint and ABDY22: where it follows one against the other, and what it deliberately does not reproduce. |
| [`NOTES-Liveness-Roadmap.md`](NOTES-Liveness-Roadmap.md) | Termination is out of scope; this is what proving it would take. |

The prose account of the case study is the ABA chapter of the repository's blueprint
(`../blueprint/src/`), which carries it in two editions over one set of statements.
