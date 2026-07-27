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

**Scope.** GBCA is verified to
*implementation* level; WCC is *assumed* at specification level (the ε-coin is
`coinPMF`). The `ValidityTrace` predicate is the **paper-form**
Validity (D13): every return of `b` is preceded by a `callABA _ b` from a
caller that is **never corrupted** anywhere in the trace — matching the papers'
correct-process Validity. The `f + 1` `SuppOK` support counts are the
*invariant machinery* that makes this provable, not the predicate itself.
Safety only: no termination/liveness/unpredictability/fairness.

**Deviation numbering.** D2, D6 and D7 are intentionally unused; the set in use
across the ABA docstrings is **D1, D3–D5, D8–D16**, with D12 refined to **D12′**
(per-process DECIDED pools). D13/D14 are the Validity repairs, D15 the
F-blind counting form of their support guards (`f+1` callers-or-corrupted),
D16 the ultra-lazy twin of the core simulation.

## Reading order

### Layer 0 — vocabulary
| file | lines | what it is |
|---|---|---|
| `Params.lean` | 78 | The protocol parameters `P : Params` — `n`, `f` (with `n > 3f`), the coin distribution `coinPMF` and its ε-bounds. Everything is parametrized by `P`. |
| `Labels.lean` | 145 | The single label alphabet `Lab n`: visible API (`callABA`/`retABA`/`fail`), hidden handshakes (`callG`/`retG`/`callW`/`retW`, round-tagged), `τ`; the `hiddenAPI` selector used by `abstract`; round projections. |

### Layer 1 — the three specifications
| file | lines | what it is |
|---|---|---|
| `Spec.lean` | 225 | **The top-level ABA specification** (`ABA.spec`): a small PLTS over `SpecState` (`F`, `ret`, `val`, `bind`, `coin`, `call`) with 10 rules (incl. the `callByzFill` τ-rule). Carries the **D3** Agreement repair (rule 7 guard `val = ⊥ ∨ b = val`) *and* the **D13** Validity repair: ghost `input` (rule 1 unconditional, rule 2 first-write-wins), the rule-4 `f+1`-support bind guard, the provenance-preserving rule-7 re-propose guard, and the `callByzFill` τ-rule. This is the system all safety is measured against. |
| `WCCSpec.lean` | 114 | The Weak Common Coin **specification** (per-round instance): call quorum, then a genuine `coinPMF` flip — the only probabilistic step in the whole stack. Held at spec level by design (assumed, not implemented). |
| `GBCASpec.lean` | 182 | The Graded Binding Crusader Agreement **specification** (per-round instance): call slots, quorum-gated binding, grades (A/B/C), returns. The `A`/`B`-returns hand out the bound value; the bind-free `C`-return hands out no bit. **D14**: every provenance guard is an `f+1` F-blind count of callers (`call = b ∨ ∈ F`, the D15 `SuppOK` form) rather than a single witness — on the bound bit at `bindSet`, on the dissenting bit at `retB`, and on **both** bits at `retC`, which is what certifies that no single bit can be handed out. With at most `f` ever corrupted, any such set contains a never-corrupted genuine caller — the fix that makes paper-form Validity provable. |

### Layer 2 — spec-level safety of ABA
| file | lines | what it is |
|---|---|---|
| `SpecSafety.lean` | 929 | The trace predicates `ValidityTrace`/`AgreementTrace`, the spec invariant `SpecInv`, and `spec_safe`: every positive-mass trace of `ABA.spec` is valid and agreeing. `ValidityTrace` is **paper-form** (D13): positional (`t.get? k`), each return's bit witnessed by a preceding `callABA` from one `NeverCorrupted` caller (the `f+1` `SuppOK` counts are the invariant machinery), with the provenance conjuncts `call_prov`/`bind_supp`/`val_supp`/`bound_prov`. Also `safety_transfer` (refinement + spec safety ⇒ implementation safety). Where the D3+D13 repairs prove their worth. |

### Layer 3 — GBCA: implementation and refinement
| file | lines | what it is |
|---|---|---|
| `GBCAImpl.lean` | 449 | The blueprint's **GBCA implementation** `alg:GBCA` (echo/vote message counting) as a per-round PLTS. The state is the protocol's own data — per-process local states, the D5 set-based network, `F` — and the three returns are Algorithm 2's three wait-until cases verbatim, reading nothing beyond the receipts those cases name; the specification's `bind`/`grade` are abstractions of those receipt patterns and live only on the specification side. This is a **4-round compression** of ABDY22's 5-round Algorithm 6 (the `echo5` round elided, decide conditions read one level down), not a transcription of it — the theorems still hold under `n > 3f`. |
| `GBCASim.lean` | 1636 | The per-instance forward simulation `GBCA.impl ⊑ GBCA.spec` (`implRefines`) — invariant + step matching, **lazy-bind**: the specification's bookkeeping is carried as receipt certificates (`bind_cert`, an `n − f` `ECHO v` quorum; `gradeA_ev`/`gradeC_ev`, `n − f` `BIND v`/`BIND ⊥` quorums), and the specification's internal `bindSet` fires inside a weak step at the **first** `A`/`B`-return (`firstRetA_burst`/`firstRetB_burst`), so a run that only ever `C`-returns never binds. The largest single proof outside the core simulation. |
| `GBCAFamily.lean` | 139 | Lifts the per-instance refinement to the ℕ-indexed **family** (`familyRefines`) via the framework's family congruence. |

### Layer 4 — the algorithm and its composition
| file | lines | what it is |
|---|---|---|
| `Core.lean` | 619 | **The ABA core algorithm**: per-process five-phase handshake machine, estimates, rounds, DECIDED gossip; 15 step constructors incl. the `…Byz` variants for corrupted ids. Module docstring has the constructor table and deviations D9–D12′. **D12′** closes the DECIDED-equivocation gap: per-process `decidedSent`/`decidedRecv` *pools* (a corrupted process may hold both bits via `byzDecided`), delivered per-(receiver, sender, bit). Core holds *no* GBCA/WCC state — see the handshake discipline above. |
| `Hybrid.lean` | 70 | Assembles `context := core ∥ WCC.specFamily`, then `hybridImpl`/`hybridSpec` by parallel-composing the GBCA family and hiding the handshakes; proves `substitution : hybridImpl ⊑ hybridSpec` from `familyRefines` by precongruence. |

### Layer 5 — the core simulation (`hybridSpec ⊑ ABA.spec`)
| file | lines | what it is |
|---|---|---|
| `CoreSimRel.lean` | 3886 | The relation and the heavy lifting: the abstract-twin constraints `Abs` (ultra-lazy two-phase twin: `coin_bot`, `phase`) plus the frame lemma, the concrete invariant `Inv` (~30 conjuncts, incl. the I26/I27 `bind_supp`/`clock_supp` support pools and the D12′ per-bit DECIDED conjuncts) with its round skeleton keyed on `Closed g r := (g r).bind ≠ none ∨ (g r).grade = some false`, `DissentResidue`, invariant preservation for every step class, quorum transfer. Read the two structure docstrings first; `../DESIGN-CoreSim.md` is the narrative version. |
| `CoreSimBurst.lean` | 184 | The abstract τ-burst kit: `fill_chain`, `byz_fill_chain`, `rebind_mixed`/`rebind_unanim`, `weakStep_of_burst_then_step` — how the twin catches up in one weak step; bursts fire only at `retABA`. |
| `CoreSim.lean` | 690 | The simulation proof itself, one row per concrete step class (stutters + the single `decide_burst` + the coupled coin row + `retABA` burst-then-return), assembled into `coreSim`. |

### Layer 6 — results
| file | lines | what it is |
|---|---|---|
| `Main.lean` | 89 | The deliverables: `refines` (trace-distribution inclusion), `main` (Validity ∧ Agreement for every positive-mass trace of `hybridImpl` — GBCA at impl level, WCC assumed at spec level), `simComposed` (the single composed simulation via transitivity). `#guard_msgs` axiom firewall — the build fails if any of them ever acquires `sorryAx`. |
| `Examples.lean` | 600 | Non-vacuity: a concrete n = 4, f = 1, ε = 1/2 happy-path run carried all the way to a `retABA` decision (21 steps) — **on `hybridSpec`**; `hybridImpl` (the system `main` is about) is witnessed to a single step, and the positive-probability remark is informal (no machine-checked `achievableTraceDists` membership on either side — see Future work). |

### Layer 7 — the per-process presentation
| file | lines | what it is |
|---|---|---|
| `GBCAProc.lean` | 861 | One GBCA process as its own PLTS (`ProcNode`: local record, outbox, inbox rows, `F` copy; every guard reads the node alone), the network as rendezvous labels `net(i, j, m)` over `Lab ⊕ GNet`, and **`perProcInst_atd`**: the hidden-network composition of the n automata and the monolithic `implInst` have the same achievable trace distributions — a step-for-step forward simulation in each direction along the packing map. |
| `CoreProc.lean` | 1264 | The same for the core: `CoreNode` (control record, DECIDED pool, inbox rows, `F` copy), gossip as `net(i, j, b)` rendezvous, and **`perProcCore_atd`**. The per-(receiver, sender, bit) DECIDED pools (D12′) are what let the delivery guard split sender/receiver-locally. |
| `Assembly.lean` | 236 | Both per-process layers substituted into the hybrid at once: `perProcGBCAFamily` (the ℕ-indexed family of per-process GBCA instances) beside `perProcCore`, with the coin oracle the one box left at spec level, and **`hybridPerProc_atd`**: that composition and `hybridImpl` achieve the same trace distributions. Assembled from the two layer equivalences by the `parallel`/`abstract` precongruences alone, chained by transitivity of `⊆`; `atd_parallel_left` is the mirror precongruence (context on the left), obtained by conjugating Result 3 with the coordinate exchange. `hybridPerProc_safe` reads `main` along the equality. |
| `FlatABA.lean` | 1727 | The layer boundary removed: `ABAProc P j` is **the program of process j** — one `ABANode` (round-loop record plus one graded-agreement stage per round) and 41 rules, with each `callG`/`retG` handshake fused into a single atomic rule of the two halves of the *same* process, both networks (`gnet` round-tagged, `dnet`) carried by the auxiliary alphabet `FlatNet` that the composition hides, and every guard reading `j`'s own node. **`flatABA_atd`**: `n` such programs beside the coin oracle achieve exactly the trace distributions of `hybridImpl` — a strong functional matching along the unflattening map `unflat` and its converse, the coin flip appearing on both sides as the same pushforward of `coinPMF`. `flatABA_safe` reads `main` along the equality. |

## Future work

- **Achievability theorem**: one explicit scheduler for `hybridImpl P4` driving a
  two-return decision trace `t`, with `∃ D ∈ achievableTraceDists (hybridImpl P4), D t ≠ 0`
  (probOf ≥ the ε-product via a traceProb single-execution lower bound) — the
  machine-checked non-vacuity for `main`'s own system, exercising Agreement with two
  returns.
- **`ValidityTrace` witness strengthening**: the current witness clause accepts any
  preceding `callABA id' b`; the proof yields a stronger ghost-backed witness. Care:
  the D13 ghost is *last*-rule-1-write (D16 junk-erasure), so a "first call" restatement
  is not immediate.

## Shared framework (`../Framework/`)
| file | lines | what it is |
|---|---|---|
| `TraceSupport.lean` | 506 | Bridge from trace-distribution inclusion to per-trace properties (support-level safety transfer). |
| `IdleFamily.lean` | 117 | ℕ-indexed instance families with idle self-loops — how round-`r` instances ignore other rounds' labels under full-sync `parallel`. |
| `FamilySim.lean` | 328 | Congruence: per-instance refinement lifts to the family. |
| `SyncProduct.lean` | 118 | `System.syncProduct`: the n-ary full-synchronisation product — a visible label moves every component, τ moves exactly one. With idle self-loops on non-owned labels this is the rendezvous idiom of the per-process presentation. |
| `Relabel.lean` | 77 | `System.relabel`: transport of a system over `Label ⊕ Extra` back to `Label` along the left embedding, after the extra (network) alphabet has been hidden; plus `abstract_isLTS`. |

## Suggested first read

`Params` → `Labels` → `Spec` → skim `SpecSafety`'s two trace predicates →
`Core`'s module docstring → `Hybrid` → `Main`. That path (≈ 600 lines of
reading) gives the full statement-level picture; descend into Layer 3 and
Layer 5 only when you want the proofs. For liveness context (deliberately out
of scope here) see `../NOTES-Liveness-Roadmap.md`; for how the encoding stands
against the source blueprint and ABDY22 beyond the D-registry above, see
`../NOTES-Fidelity.md`.
