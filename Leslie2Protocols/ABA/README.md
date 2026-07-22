# The ABA case study — file guide

Machine-checked safety (Validity ∧ Agreement) for randomized Asynchronous Binary
Agreement, following the "Verifying ABA with Leslie" blueprint: WCC held at spec
level (the ε-coin is an assumption), GBCA verified implementation-against-spec,
everything composed with the core algorithm and related to a small top-level ABA
specification by probabilistic forward simulation. Headline theorems: `ABA.main`,
`ABA.refines`, `ABA.simComposed` in `Main.lean` — all axiom-clean and guarded.

The architecture in one line:

```
hybridImpl := (GBCA.implFamily ∥ (core ∥ WCC.specFamily)).abstract hiddenAPI
   ⊑ hybridSpec (substitution: swap GBCA impl for its spec, Results 3+5)
   ⊑ ABA.spec   (the core simulation `coreSim`)
```

Components talk only through synchronized handshake labels (`callG`/`retG`/
`callW`/`retW`), which the outer `abstract` hides; no component reads another's
state. Design rationale for the core simulation: `../DESIGN-CoreSim.md`.

## Reading order

### Layer 0 — vocabulary
| file | lines | what it is |
|---|---|---|
| `Params.lean` | 78 | The protocol parameters `P : Params` — `n`, `f` (with `n > 3f`), the coin distribution `coinPMF` and its ε-bounds. Everything is parametrized by `P`. |
| `Labels.lean` | 147 | The single label alphabet `Lab n`: visible API (`callABA`/`retABA`/`fail`), hidden handshakes (`callG`/`retG`/`callW`/`retW`, round-tagged), `τ`; the `hiddenAPI` selector used by `abstract`; round projections. |

### Layer 1 — the three specifications
| file | lines | what it is |
|---|---|---|
| `Spec.lean` | 169 | **The top-level ABA specification** (`ABA.spec`): a small PLTS over `SpecState` (`F`, `ret`, `val`, `bind`, `coin`, `call`) with 9 rules. Rule 7's re-propose carries the **D3 repair** of the blueprint's Agreement bug (`val = ⊥ ∨ b = val`). This is the system all safety is measured against. |
| `WCCSpec.lean` | 114 | The Weak Common Coin **specification** (per-round instance): call quorum, then a genuine `coinPMF` flip — the only probabilistic step in the whole stack. Held at spec level by design. |
| `GBCASpec.lean` | 148 | The Graded Binary Consensus **specification** (per-round instance): call slots, quorum-gated binding, grades (A/B/C), returns. |

### Layer 2 — spec-level safety of ABA
| file | lines | what it is |
|---|---|---|
| `SpecSafety.lean` | 526 | The trace predicates `ValidityTrace`/`AgreementTrace`, the spec invariant `SpecInv`, and `spec_safe`: every positive-mass trace of `ABA.spec` is valid and agreeing. Also `safety_transfer` (refinement + spec safety ⇒ implementation safety). This file is where the D3 repair proves its worth. |

### Layer 3 — GBCA: implementation and refinement
| file | lines | what it is |
|---|---|---|
| `GBCAImpl.lean` | 517 | The ABDY22-style GBCA **implementation** (echo/vote message counting) as a per-round PLTS. |
| `GBCASim.lean` | 1096 | The per-instance forward simulation `GBCA.impl ⊑ GBCA.spec` (`implRefines`) — invariant + step matching. The largest single proof outside the core simulation. |
| `GBCAFamily.lean` | 133 | Lifts the per-instance refinement to the ℕ-indexed **family** (`familyRefines`) via the framework's family congruence. |

### Layer 4 — the algorithm and its composition
| file | lines | what it is |
|---|---|---|
| `Core.lean` | 579 | **The ABA core algorithm**: per-process five-phase handshake machine, estimates, rounds, DECIDED gossip; 15 step constructors incl. the `…Byz` variants for corrupted ids. Module docstring has the constructor table and deviations D9–D12. Core holds *no* GBCA/WCC state — see the handshake discipline above. |
| `Hybrid.lean` | 70 | Assembles `context := core ∥ WCC.specFamily`, then `hybridImpl`/`hybridSpec` by parallel-composing the GBCA family and hiding the handshakes; proves `substitution : hybridImpl ⊑ hybridSpec` from `familyRefines` by precongruence. |

### Layer 5 — the core simulation (`hybridSpec ⊑ ABA.spec`)
| file | lines | what it is |
|---|---|---|
| `CoreSimRel.lean` | 3714 | The relation and the heavy lifting: the abstract-twin constraints `Abs` (never-flipping lazy twin: `coin_bot`, `val_cert`, `bind_ready`, …), the concrete invariant `Inv` (~30 conjuncts), `DissentResidue`, invariant preservation for every step class, quorum transfer. Read the two structure docstrings first; `../DESIGN-CoreSim.md` is the narrative version. |
| `CoreSimBurst.lean` | 196 | The abstract τ-burst kit: `fill_chain`, `rebind_mixed`/`rebind_unanim`, `val_force`, `weakStep_of_burst_then_step` — how the lazy twin catches up in one weak step. |
| `CoreSim.lean` | 755 | The simulation proof itself, one row per concrete step class (stutters, bursts, the coupled coin row, `retABA` burst-then-return), assembled into `coreSim`. |

### Layer 6 — results
| file | lines | what it is |
|---|---|---|
| `Main.lean` | 83 | The deliverables: `refines` (trace-distribution inclusion), `main` (Validity ∧ Agreement for every positive-mass trace of `hybridImpl`), `simComposed` (the single composed simulation via transitivity). `#guard_msgs` axiom firewall — the build fails if any of them ever acquires `sorryAx`. |
| `Examples.lean` | 270 | Non-vacuity: a concrete n = 4, f = 1 happy-path run of the hybrid (calls → GBCA bind → coin → DECIDED → returns), showing the composition isn't deadlocked. |

## Shared framework (`../Framework/`)
| file | lines | what it is |
|---|---|---|
| `TraceSupport.lean` | 420 | Bridge from trace-distribution inclusion to per-trace properties (support-level safety transfer). |
| `IdleFamily.lean` | 117 | ℕ-indexed instance families with idle self-loops — how round-`r` instances ignore other rounds' labels under full-sync `parallel`. |
| `FamilySim.lean` | 328 | Congruence: per-instance refinement lifts to the family. |

## Suggested first read

`Params` → `Labels` → `Spec` → skim `SpecSafety`'s two trace predicates →
`Core`'s module docstring → `Hybrid` → `Main`. That path (≈ 600 lines of
reading) gives the full statement-level picture; descend into Layer 3 and
Layer 5 only when you want the proofs. For liveness context (deliberately out
of scope here) see `../NOTES-Liveness-Roadmap.md`.
