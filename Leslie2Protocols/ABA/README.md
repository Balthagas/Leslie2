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
*implementation* level; WCC is *assumed* at specification level (its coin is
`wccPMF`). The `ValidityTrace` predicate is the **paper-form**
Validity (D13): every return of `b` is preceded by a `callABA _ b` from a
caller that is **never corrupted** anywhere in the trace — matching the papers'
correct-process Validity. The `f + 1` `SuppOK` support counts are the
*invariant machinery* that makes this provable, not the predicate itself.
Safety only: no termination/liveness/unpredictability/fairness.

**Deviation numbering.** D2, D6 and D7 are intentionally unused; the set in use
across the ABA docstrings is **D1, D3–D5, D8–D19**, with D12 refined to **D12′**
(per-process DECIDED pools). D13/D14 are the Validity repairs, D15 the
F-blind counting form of their support guards (`f+1` callers-or-corrupted),
D16 the ultra-lazy twin of the core simulation, D17 the δ-mass delivery-failure
outcome carried by *both* coin resolutions — the WCC specification's flip and
the ABA specification's rule 5, which resolve by the same `wccPMF`; a dead ABA
round is frozen (neither adopt nor re-propose is enabled). D18 is the GBCA
implementation shape (ABDY22's Algorithm 6 in full, against the source
blueprint's Binding-violating four-round compression) and D19 the GBCA
specification state shape (an exclusion set in place of a bound value).

## Reading order

### Layer 0 — vocabulary
| file | lines | what it is |
|---|---|---|
| `Params.lean` | 127 | The protocol parameters `P : Params` — `n`, `f` (with `n > 3f`), the coin distribution `wccPMF` (over `CoinOutcome`: ε on each bit, δ on the `dead` delivery-failure outcome, the rest on `⊤`), and its ε/δ-bounds. `wccPMF` is *the* coin of the development: both the ABA specification's rule 5 and the WCC specification's flip resolve by it. Everything is parametrized by `P`. |
| `Labels.lean` | 145 | The single label alphabet `Lab n`: visible API (`callABA`/`retABA`/`fail`), hidden handshakes (`callG`/`retG`/`callW`/`retW`, round-tagged), `τ`; the `hiddenAPI` selector used by `abstract`; round projections. |

### Layer 1 — the three specifications
| file | lines | what it is |
|---|---|---|
| `Spec.lean` | 263 | **The top-level ABA specification** (`ABA.spec`): a small PLTS over `SpecState` (`F`, `ret`, `val`, `bind`, `coin`, `call`) with 10 rules (incl. the `callByzFill` τ-rule). Carries the **D3** Agreement repair (rule 7 guard `val = ⊥ ∨ b = val`) *and* the **D13** Validity repair: ghost `input` (rule 1 unconditional, rule 2 first-write-wins), the rule-4 `f+1`-support bind guard, the provenance-preserving rule-7 re-propose guard, and the `callByzFill` τ-rule. **D17**: rule 5 resolves by `wccPMF`, so `coin` may come out `dead`; such a round is *frozen* — rule 6 is disabled (`TVal.agrees` fails on `dead`) and rule 7 by its `hd` guard, so a process that never receives the coin neither adopts nor re-proposes. Also home to `CoinOutcome.toTVal`, the outcome-to-`TVal` map shared with `WCCSpec.lean`. This is the system all safety is measured against. |
| `WCCSpec.lean` | 131 | The Weak Common Coin **specification** (per-round instance): call quorum, then a genuine `wccPMF` flip — the same distribution the ABA specification's rule 5 uses. **D17**: the flip carries a δ-mass `dead` outcome (delivery failure); the positive `ret` guard means a dead round hands out nothing. Held at spec level by design (assumed, not implemented). |
| `GBCASpec.lean` | 237 | The Graded Binding Crusader Agreement **specification** (per-round instance): call slots, quorum-gated binding, grades (A/B/C), returns. **D19**: binding is *negative*. The state carries `dead : Finset Bool`, the bits the instance can no longer hand out, in place of a bound value; the internal `bindUnset b` kills one bit at a time (write-once per bit, `dead` monotone), the `A`/`B`-returns carry the guard pair `v ∉ dead ∧ !v ∈ dead`, and `retC` needs only `1 ≤ dead.card`. The bound value embeds (`⊥ ↦ ∅`, `b ↦ {!b}`) and `dead = {0,1}` — no bit available at all — is the point it adds. **D14**: every provenance guard is an `f+1` F-blind count of callers (`call = b ∨ ∈ F`, the D15 `SuppOK` form) rather than a single witness — at `bindUnset` on the *surviving* bit, on the dissenting bit at `retB`, and on **both** bits at `retC`, which is what certifies that no single bit was forced. With at most `f` ever corrupted, any such set contains a never-corrupted genuine caller — the fix that makes paper-form Validity provable. |

### Layer 2 — spec-level safety of ABA
| file | lines | what it is |
|---|---|---|
| `SpecSafety.lean` | 929 | The trace predicates `ValidityTrace`/`AgreementTrace`, the spec invariant `SpecInv`, and `spec_safe`: every positive-mass trace of `ABA.spec` is valid and agreeing. `ValidityTrace` is **paper-form** (D13): positional (`t.get? k`), each return's bit witnessed by a preceding `callABA` from one `NeverCorrupted` caller (the `f+1` `SuppOK` counts are the invariant machinery), with the provenance conjuncts `call_prov`/`bind_supp`/`val_supp`/`bound_prov`. Also `safety_transfer` (refinement + spec safety ⇒ implementation safety). Where the D3+D13 repairs prove their worth. |

### Layer 3 — GBCA: binding, implementation and refinement
| file | lines | what it is |
|---|---|---|
| `GBCASafety.lean` | 231 | **Binding and graded agreement of the GBCA specification instance.** `Step.dead_mono` (the exclusion set never shrinks) lifted to runs, `retG_value_guards` (inverting the two value-bearing return rows), and the three headlines: `retG_value_agree` — any two returns of one execution that hand out a bit hand out the same bit; `specInst_binding` — the same on every positive-mass trace of `specInst` (`BindingTrace`, `outValue`); `retC_dead_nonempty` — a `C`-return leaves `dead` nonempty forever, the Graded Binding witness. All from monotonicity plus the return guards, no auxiliary invariant. `#guard_msgs` axiom firewall on the two headlines. |
| `GBCAImpl.lean` | 504 | The **GBCA implementation** as a per-round PLTS. **D18**: this transcribes ABDY22's **Algorithm 6 in full** — six rounds, the message ladder `INPUT/ECHO/VOTE/BIND/SEAL` (= the paper's `echo`…`echo5`), and its three decide conditions (`retA` an `n − f` `SEAL v` quorum, `retB` an `n − f` any-`SEAL` quorum containing `SEAL v` with `f + 1` `BIND v` and `|Valid| > 1`, `retC` an `n − f` `SEAL ⊥` quorum with `|Valid| > 1`) — rather than the source blueprint's `alg:GBCA`, which is a 4-round compression of it and **violates Graded Binding**: one echo-stage process held in reserve plus one corruption steers the grade-1 bit after a `C`-return. The `f + 1` `BIND v` witness is what the depth buys — it forces an honest `BIND v` sender, hence an `n − f` `VOTE v` quorum over the write-once `VOTE` level, the object the paper's binding argument counts. The state is the protocol's own data — per-process local states, the D5 set-based network, `F` — and the returns read nothing beyond the receipts their own cases name; the specification's `dead`/`grade` are abstractions of those receipt patterns and live only on the specification side. |
| `GBCASim.lean` | 1895 | The per-instance forward simulation `GBCA.impl ⊑ GBCA.spec` (`implRefines`) — invariant + step matching, **kill-on-demand**: the specification's `dead` is carried as a monotone receipt-pattern *kill certificate* per dead bit (`dead_cert`; `DeadCert b := EchoQuorum (!b) ∨ VoteWall b`, the two ways an `n − f` `VOTE b` quorum is made impossible forever), and its `grade` by `n − f` `SEAL v`/`SEAL ⊥` quorums. The internal `bindUnset` fires inside a weak burst at any return whose kill is missing (`killThenRetA_burst`/`killThenRetB_burst`/`killThenRetC_burst`); every return row, `C`-returns included, does the same case split on `dead`. The largest single proof outside the core simulation. Design narrative: `../DESIGN-GBCASim.md`. |
| `GBCAFamily.lean` | 139 | Lifts the per-instance refinement to the ℕ-indexed **family** (`familyRefines`) via the framework's family congruence. |

### Layer 4 — the algorithm and its composition
| file | lines | what it is |
|---|---|---|
| `Core.lean` | 619 | **The ABA core algorithm**: per-process five-phase handshake machine, estimates, rounds, DECIDED gossip; 15 step constructors incl. the `…Byz` variants for corrupted ids. Module docstring has the constructor table and deviations D9–D12′. **D12′** closes the DECIDED-equivocation gap: per-process `decidedSent`/`decidedRecv` *pools* (a corrupted process may hold both bits via `byzDecided`), delivered per-(receiver, sender, bit). Core holds *no* GBCA/WCC state — see the handshake discipline above. |
| `Hybrid.lean` | 70 | Assembles `context := core ∥ WCC.specFamily`, then `hybridImpl`/`hybridSpec` by parallel-composing the GBCA family and hiding the handshakes; proves `substitution : hybridImpl ⊑ hybridSpec` from `familyRefines` by precongruence. |

### Layer 5 — the core simulation (`hybridSpec ⊑ ABA.spec`)
| file | lines | what it is |
|---|---|---|
| `CoreSimRel.lean` | 4577 | The relation and the heavy lifting: the abstract-twin constraints `Abs` (ultra-lazy two-phase twin: `coin_bot`, `phase`) plus the frame lemma, the concrete invariant `Inv` (I1–I30, incl. the I26/I27 `bind_supp`/`clock_supp` support pools and the D12′ per-bit DECIDED conjuncts) with its round skeleton keyed on `Closed g r := (g r).dead ≠ ∅ ∨ (g r).grade = some false`, the frontier reading `IsLastBound g r := (g r).dead ≠ ∅ ∧ (g (r+1)).dead = ∅`, `DissentResidue`, invariant preservation for every step class, quorum transfer. Since D19 admits **burned rounds** — a second `bindUnset` after a value-bearing return reaches `dead = {0,1}`, where the exclusion set alone no longer names the decided bit — decided values ride on **certificates** rather than on the live pair `(!v) ∈ dead ∧ v ∉ dead`: `ACommit`/`ACert` (an `A`-locked round together with its permanent commitments) sit inside `decided_src`, `grade_A_src` and phase 2 of `Abs`; `dead_supp` (I28) keeps every kill's D15 support guard permanently, so harvesting recovers an honest caller of the spared bit; `carrier_agree`/`alock_agree` (I29/I30) pin honest holders of a round's outcome and of an `A`-decision to one bit; and each `Inv.step_*` lemma returns an `AbsFrame` transporting the certificates and the holder universal across its row. Read the two structure docstrings first; `../DESIGN-CoreSim.md` is the narrative version. |
| `CoreSimBurst.lean` | 187 | The abstract τ-burst kit: `fill_chain`, `byz_fill_chain`, `rebind_mixed`/`rebind_unanim`, `weakStep_of_burst_then_step` — how the twin catches up in one weak step; bursts fire only at `retABA`. `fill_chain` carries the D17 side condition `coin ≠ dead`, discharged at every call site from the twin's `coin = ⊥`. |
| `CoreSim.lean` | 691 | The simulation proof itself, one row per concrete step class (stutters + the single `decide_burst` + the coupled coin row + `retABA` burst-then-return), assembled into `coreSim`. Each row consumes the `AbsFrame` its `Inv.step_*` lemma returns, which is what carries the `A`-certificate and the honest-holder universal of `Abs`'s phase 2 across the step. |

### Layer 6 — results
| file | lines | what it is |
|---|---|---|
| `Main.lean` | 89 | The deliverables: `refines` (trace-distribution inclusion), `main` (Validity ∧ Agreement for every positive-mass trace of `hybridImpl` — GBCA at impl level, WCC assumed at spec level), `simComposed` (the single composed simulation via transitivity). `#guard_msgs` axiom firewall — the build fails if any of them ever acquires `sorryAx`. |
| `Examples.lean` | 598 | Non-vacuity: a concrete n = 4, f = 1, ε = 1/2 happy-path run carried all the way to a `retABA` decision (21 steps) — **on `hybridSpec`**; `hybridImpl` (the system `main` is about) is witnessed to a single step, and the positive-probability remark is informal (no machine-checked `achievableTraceDists` membership on either side — see Future work). |

### Layer 7 — the per-process presentation
| file | lines | what it is |
|---|---|---|
| `GBCAProc.lean` | 899 | One GBCA process as its own PLTS (`ProcNode`: local record, outbox, inbox rows, `F` copy; every guard reads the node alone), the network as rendezvous labels `net(i, j, m)` over `Lab ⊕ GNet`, and **`perProcInst_atd`**: the hidden-network composition of the n automata and the monolithic `implInst` have the same achievable trace distributions — a step-for-step forward simulation in each direction along the packing map. `ProcStep` has 21 rules: the full D18 ladder is carried locally, so the `SEAL` level has its own pair of τ-multicasts (`sealBit` on an `n − f` `BIND b` quorum, `sealBot` on `n − f` any-`BIND` plus `|Valid| > 1`), and all three returns read that level off the node's inbox — `retA` an `n − f` `SEAL v` quorum, `retB` an `n − f` any-`SEAL` count (`sealCount`) with a `SEAL v` witness and `f + 1` `BIND v`, `retC` an `n − f` `SEAL ⊥` quorum. The counting bridges to the monolithic reading are the `unpack_*` simp lemmas, `unpack_sealCount` among them. |
| `CoreProc.lean` | 1264 | The same for the core: `CoreNode` (control record, DECIDED pool, inbox rows, `F` copy), gossip as `net(i, j, b)` rendezvous, and **`perProcCore_atd`**. The per-(receiver, sender, bit) DECIDED pools (D12′) are what let the delivery guard split sender/receiver-locally. |
| `Assembly.lean` | 236 | Both per-process layers substituted into the hybrid at once: `perProcGBCAFamily` (the ℕ-indexed family of per-process GBCA instances) beside `perProcCore`, with the coin oracle the one box left at spec level, and **`hybridPerProc_atd`**: that composition and `hybridImpl` achieve the same trace distributions. Assembled from the two layer equivalences by the `parallel`/`abstract` precongruences alone, chained by transitivity of `⊆`; `atd_parallel_left` is the mirror precongruence (context on the left), obtained by conjugating Result 3 with the coordinate exchange. `hybridPerProc_safe` reads `main` along the equality. |
| `FlatABA.lean` | 1760 | The layer boundary removed: `ABAProc P j` is **the program of process j** — one `ABANode` (round-loop record plus one graded-agreement stage per round) and 43 rules, with each `callG`/`retG` handshake fused into a single atomic rule of the two halves of the *same* process, both networks (`gnet` round-tagged, `dnet`) carried by the auxiliary alphabet `FlatNet` that the composition hides, and every guard reading `j`'s own node. Nine of the 43 are the process's τ-stage rules — `stageRelay`, `stageEcho`, the two `stageVote*`, the two `stageBind*`, the two `stageSeal*` and `stageByz` — and the six fused return rows (`retG_A`/`_B`/`_C` and their `retGByz*` twins) carry the SEAL-level guards of the stage node verbatim. **`flatABA_atd`**: `n` such programs beside the coin oracle achieve exactly the trace distributions of `hybridImpl` — a strong functional matching along the unflattening map `unflat` and its converse, the coin flip appearing on both sides as the same pushforward of `wccPMF`. `flatABA_safe` reads `main` along the equality. |

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
