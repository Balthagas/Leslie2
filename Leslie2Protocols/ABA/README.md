# The ABA case study — file guide

Machine-checked safety (Validity ∧ Agreement) for randomized Asynchronous Binary
Agreement, following the "Verifying ABA with Leslie" blueprint: WCC held at spec
level (the ε-coin is an assumption), GBCA verified implementation-against-spec,
and the protocol as it runs — one program per process beside a network adversary
and the coin oracle — related to a small top-level ABA specification by
probabilistic forward simulation. Every headline is in `Main.lean` —
`ABA.main`, `ABA.refines`, `ABA.simComposed`, `ABA.deployed_safe`,
`ABA.deployed_spec`, `ABA.deployed_traces`, `ABA.layeredSpec_spec`,
`ABA.layered_safe` — all axiom-clean and guarded.

The architecture in one line, all of it in deployment coordinates:

```
deployed  =ATD=  layered  ⊑  layeredSpec  ⊑  ABA.spec
```

- `deployed` — the protocol as it runs: `n` corruption-blind programs, one per
  process, beside two boxes that are not processes — the network adversary, which
  owns the message pools, the DECIDED pools and the corrupted set with its budget,
  and the coin oracle, the only factor whose transitions are not Dirac.
- `layered` — the same system cut so that a *layer* boundary is a *component*
  boundary: the family of graded-agreement round subsystems (each a group of stage
  programs beside that round's own message fabric), the `n` round loops, the
  DECIDED layer beside the corrupted set, and the coin oracle. `layered_atd`: the
  two presentations achieve exactly the same trace distributions, so the cut adds
  no behaviour and loses none.
- `layeredSpec` — each round's subsystem replaced by the graded agreement
  specification, the other three factors untouched (`substSim`). Both sub-protocols
  are now at specification level, so the round loop's environment is exactly the two
  oracles it calls, and this is the subject of the hand-built core simulation.
- `ABA.spec` — the single-automaton reading of agreement (`coreSim`), the
  hand-built simulation, proved in the layered coordinates: the round
  specifications, the `n` round loops, the ABA-side network and the coin oracle are
  each still a factor of the state its relation is defined on.

Components talk only through synchronized labels: the sub-protocol handshakes
`callG`/`retG`/`callW`/`retW`, which the outer `abstract` hides, and — in the
deployed coordinates — an auxiliary rendezvous alphabet naming the message
layers and the Byzantine drives, hidden before the read-back to `Lab n`. No
component reads another's state. Design rationale for the core simulation:
`../DESIGN-CoreSim.md`.

**What the layering buys.** A layer is swappable exactly when its factor boundary
owns its network. Giving each round its own message fabric makes the round a
factor, and a factor can be replaced: the substitution is *one* family congruence
plus *one* parallel precongruence, then `abstract`, `relabel`, `abstract` to run
the composition pipeline out. That is a modular axis. Varying the power of the
message layer — losses, reordering, a different forgery model — is a change inside
the round subsystem, swapped in by the same precongruence with nothing else in the
chain touched. Idealizing the round also exposes the vanish/survive asymmetry: the
round's pools, its delivery guards and its injections die with the graded-agreement
idealization, while the DECIDED layer, the corruption budget and the authorisation
`k ∈ F` of every Byzantine drive survive it, at the ABA-side network.

**Where each network is external.** Two networks carry the protocol, and neither is
internal to a process. The round's message fabric `GSub.gNet` is a factor of `layered`
and of `layeredSpec`, and it disappears at the substitution, inside the factor that is
exchanged. Weakening it — losses, reordering, a different forgery model — is therefore
a change to `GSub.gNet` alone, carried by the same precongruence with nothing else in
the chain touched. The ABA-side DECIDED network `aNet` is a factor of every system in
the chain, and a factor of the state `coreRel` is defined on. The core simulation reads
it through the view of `CoreView.lean`, so the invariant names the network's own pools
rather than a copy of them inside a record.

Much of the weakening is already in the DECIDED model, which is what tells a reader
what is left to do. `dpool` is a `Finset`, so there is no delivery order to disturb.
Receipts are sets too, and `CoreNodeN.recvDec` files by insertion, so a repeated
delivery of one (receiver, sender, bit) triple carries no information: `ANetStep.ddlv`
consumes nothing, and the receiver's `CoreProcStepN.ddlvRecv` declines the repeat under
`b ∉ decIn k` rather than taking a step that would change no state. Duplication is thus
immaterial here, not assumed away. No rule forces a delivery,
so any subset of the multicasts may be lost. `byzD` injects either bit for any
`k ∈ F`, so a corrupted process may equivocate at the DECIDED layer. What remains
assumed is unforgeability of an honest process's DECIDED multicast: the delivery guard
`b ∈ dpool j` attributes every receipt to a genuine send by the named sender.

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
| `Labels.lean` | 146 | The single label alphabet `Lab n`: visible API (`callABA`/`retABA`/`fail`), hidden handshakes (`callG`/`retG`/`callW`/`retW`, round-tagged), `τ`; the `hiddenAPI` selector used by `abstract`; round projections. |

### Layer 1 — the three specifications
| file | lines | what it is |
|---|---|---|
| `Spec.lean` | 263 | **The top-level ABA specification** (`ABA.spec`): a small PLTS over `SpecState` (`F`, `ret`, `val`, `bind`, `coin`, `call`) with 10 rules (incl. the `callByzFill` τ-rule). Carries the **D3** Agreement repair (rule 7 guard `val = ⊥ ∨ b = val`) *and* the **D13** Validity repair: ghost `input` (rule 1 unconditional, rule 2 first-write-wins), the rule-4 `f+1`-support bind guard, the provenance-preserving rule-7 re-propose guard, and the `callByzFill` τ-rule. **D17**: rule 5 resolves by `wccPMF`, so `coin` may come out `dead`; such a round is *frozen* — rule 6 is disabled (`TVal.agrees` fails on `dead`) and rule 7 by its `hd` guard, so a process that never receives the coin neither adopts nor re-proposes. Also home to `CoinOutcome.toTVal`, the outcome-to-`TVal` map shared with `WCCSpec.lean`. This is the system all safety is measured against. |
| `WCCSpec.lean` | 131 | The Weak Common Coin **specification** (per-round instance): call quorum, then a genuine `wccPMF` flip — the same distribution the ABA specification's rule 5 uses. **D17**: the flip carries a δ-mass `dead` outcome (delivery failure); the positive `ret` guard means a dead round hands out nothing. Held at spec level by design (assumed, not implemented). |
| `GBCASpec.lean` | 267 | The Graded Binding Crusader Agreement **specification** (per-round instance): call slots, quorum-gated binding, grades (A/B/C), returns. **D19**: binding is *negative*. The state carries `dead : Finset Bool`, the bits the instance can no longer hand out, in place of a bound value; the internal `bindUnset b` kills one bit under the guard `dead = ∅` (once per instance, `dead` monotone), the `A`/`B`-returns carry the guard pair `v ∉ dead ∧ !v ∈ dead`, and `retC` needs only `1 ≤ dead.card`. Reachable states are exactly `dead ∈ {∅, {b}}`, which the bound value embeds onto (`⊥ ↦ ∅`, `b ↦ {!b}`), so the two state shapes differ in the guards and not in the cardinality. The once-only guard is also what keeps a round completable: a second kill after an `A`-return would strand the un-returned processes, the value-bearing returns needing a live bit and `retC` being blocked by the A-latch. **D14**: every provenance guard is an `f+1` F-blind count of callers (`call = b ∨ ∈ F`, the D15 `SuppOK` form) rather than a single witness — at `bindUnset` on the *surviving* bit, on the dissenting bit at `retB`, and on **both** bits at `retC`, which is what certifies that no single bit was forced. With at most `f` ever corrupted, any such set contains a never-corrupted genuine caller — the fix that makes paper-form Validity provable. |

### Layer 2 — spec-level safety of ABA
| file | lines | what it is |
|---|---|---|
| `SpecSafety.lean` | 929 | The trace predicates `ValidityTrace`/`AgreementTrace`, the spec invariant `SpecInv`, and `spec_safe`: every positive-mass trace of `ABA.spec` is valid and agreeing. `ValidityTrace` is **paper-form** (D13): positional (`t.get? k`), each return's bit witnessed by a preceding `callABA` from one `NeverCorrupted` caller (the `f+1` `SuppOK` counts are the invariant machinery), with the provenance conjuncts `call_prov`/`bind_supp`/`val_supp`/`bound_prov`. Also `safety_transfer` (refinement + spec safety ⇒ implementation safety). Where the D3+D13 repairs prove their worth. |

### Layer 3 — GBCA: binding, implementation and refinement
| file | lines | what it is |
|---|---|---|
| `GBCASafety.lean` | 598 | **Binding, graded agreement and Validity's safety half for the GBCA specification instance.** `Step.dead_mono` (the exclusion set never shrinks) lifted to runs, `retG_value_guards` (inverting the two value-bearing return rows), and five headlines: `retG_value_agree` — any two returns of one execution that hand out a bit hand out the same bit; `specInst_binding` — the same on every positive-mass trace of `specInst` (`BindingTrace`, `outValue`); `retC_dead_nonempty` — a `C`-return leaves `dead` nonempty forever, the Graded Binding witness; `dead_card_le_one` — every state of every execution has `dead.card ≤ 1`, from the `dead = ∅` guard on the single writer, which pins the reachable shape to `dead ∈ {∅, {b}}`; and the Validity pair `specInst_validity`/`specInst_no_retC` — on a trace where every round-`r` call carries `v` unless its caller is corrupted somewhere along it (`UnanimousInput`, over `SpecSafety`'s `NeverCorrupted`), every return hands out `v` (`ValidityTrace`) and no `C`-return occurs. The first four are monotonicity plus the return guards, no auxiliary invariant; Validity adds the bookkeeping invariant `CallInv` (pending inputs attributed to `callG` events, `F` the fold of the history's `fail` labels) and a budget pigeonhole (`supp_le_of_unanimous`, `dead_notMem_of_unanimous`). The other two halves of the papers' Validity clause — top grade, and every non-faulty process answered — are fairness statements, out of scope here. `#guard_msgs` axiom firewall on all five headlines. |
| `GBCAImpl.lean` | 504 | The **GBCA implementation** as a per-round PLTS. **D18**: this transcribes ABDY22's **Algorithm 6 in full** — six rounds, the message ladder `INPUT/ECHO/VOTE/BIND/SEAL` (= the paper's `echo`…`echo5`), and its three decide conditions (`retA` an `n − f` `SEAL v` quorum, `retB` an `n − f` any-`SEAL` quorum containing `SEAL v` with `f + 1` `BIND v` and `|Valid| > 1`, `retC` an `n − f` `SEAL ⊥` quorum with `|Valid| > 1`) — rather than the source blueprint's `alg:GBCA`, which is a 4-round compression of it and **violates Graded Binding**: one echo-stage process held in reserve plus one corruption steers the grade-1 bit after a `C`-return. The `f + 1` `BIND v` witness is what the depth buys — it forces an honest `BIND v` sender, hence an `n − f` `VOTE v` quorum over the write-once `VOTE` level, the object the paper's binding argument counts. The state is the protocol's own data — per-process local states, the D5 set-based network, `F` — and the returns read nothing beyond the receipts their own cases name; the specification's `dead`/`grade` are abstractions of those receipt patterns and live only on the specification side. |
| `GBCASim.lean` | 1775 | The per-instance forward simulation `GBCA.impl ⊑ GBCA.spec` (`implRefines`) — invariant + step matching, **kill-on-demand**: the specification's `dead` is carried as a monotone receipt-pattern *kill certificate* per dead bit (`dead_cert`; `DeadCert b := EchoQuorum (!b) ∨ VoteWall b`, the two ways an `n − f` `VOTE b` quorum is made impossible forever), and its `grade` by `n − f` `SEAL v`/`SEAL ⊥` quorums. The internal `bindUnset` fires inside a weak burst at any return whose kill is missing (`killThenRetA_burst`/`killThenRetB_burst`/`killThenRetC_burst`, each taking the rule's own guard `hd0 : t.dead = ∅`, supplied at the value returns by `dead_empty_of_both` and at `retC` by the empty branch of its case split); every return row, `C`-returns included, does the same case split on `dead`. The largest single proof outside the core simulation. Design narrative: `../DESIGN-GBCASim.md`. |
| `GBCAFamily.lean` | 85 | `instRel_corrupt`, the compatibility of the per-instance relation with the broadcast `fail` act, proved directly rather than through `implRefines`; the round subsystem's family lifting consumes it, and it is where `ForwardSimulation.family` (`Framework/FamilySim.lean`) is first applied. |

### Layer 4 — the algorithm
| file | lines | what it is |
|---|---|---|
| `Core.lean` | 174 | **The ABA core algorithm**, per process and nothing else: the five-phase handshake machine `Phase`, the estimate a graded outcome dictates (`GbcaOut.est`), and the control record `ProcCore` — input, estimate, round, phase, last grade, returned flag. Module docstring has the pseudocode and deviations D9–D12′. The record holds *no* GBCA/WCC state (the handshake discipline above) and no network state: the DECIDED pools and the corrupted set belong to the network. The transitions over the shared alphabet are `Layered.CoreProcStepN` and `Net.ABAProcStepN`. |

### Layer 5 — the core simulation (`layeredSpec ⊑ ABA.spec`)
| file | lines | what it is |
|---|---|---|
| `CoreView.lean` | 331 | **The ABA-side state, read as one object.** `ABAState P := (∀ j, CoreNodeN) × ANetState` — the `n` round-loop nodes beside the ABA-side network — with the accessors that gather what the two factors hold apart: `procs` (each node's control record), `decidedRecv` (each node's receipts), `decidedSent` and `F` (the network's sent pools and corrupted set). The update helpers `setProc`/`sendDecided`/`deliverDecided`/`stepRound`/`corrupt` name a row's effect on the pair, and `stepRound_plain`/`stepRound_pub` read the fused round advance (D10) back into the round loop's own advance beside the network's publication. The invariant and relation of the core simulation are stated through these accessors, so the relation reads the layered state with no change of system and the network stays a named component. |
| `CoreSimRel.lean` | 706 | The relation itself: the abstract-twin constraints `Abs` (ultra-lazy two-phase twin: `coin_bot`, `phase`) plus the frame lemma, the concrete invariant `Inv` (I1–I30, incl. the I26/I27 `bind_supp`/`clock_supp` support pools and the D12′ per-bit DECIDED conjuncts) with its round skeleton keyed on `Closed g r := (g r).dead ≠ ∅ ∨ (g r).grade = some false`, the frontier reading `IsLastBound g r := (g r).dead ≠ ∅ ∧ (g (r+1)).dead = ∅`, `DissentResidue`, invariant preservation for every step class, quorum transfer. Decided values ride on **certificates** rather than on the live pair `(!v) ∈ dead ∧ v ∉ dead`, a certificate naming its bit off the single permanent membership `(!b) ∈ dead`: `ACommit`/`ACert` (an `A`-locked round together with its permanent commitments) sit inside `decided_src`, `grade_A_src` and phase 2 of `Abs`; `dead_supp` (I28) keeps every kill's D15 support guard permanently, so harvesting recovers an honest caller of the spared bit; `carrier_agree`/`alock_agree` (I29/I30) pin honest holders of a round's outcome and of an `A`-decision to one bit; and each `Inv.step_*` lemma returns an `AbsFrame` transporting the certificates and the holder universal across its row. This file stops at the initial states; the proof that `coreR` is a simulation relation runs in the two files below. Read the two structure docstrings first; `../DESIGN-CoreSim.md` is the narrative version. |
| `CoreSimInv.lean` | 3809 | **Stage A**, step inversion for `layeredSpec`: one lemma per visible label class (`layered_step_callABA`, `_retABA`, `_fail`) and `layered_step_tau`, the seven-way disjunction the τ-side dispatches on, each reading a composite transition of the four factors back into the component rows that produced it and delivering the ABA-side content in the view's coordinates. **Stage B**, preservation of `Inv`: one `Inv.step_*` lemma per row of that inversion, each carrying all thirty-nine invariant fields across the row and returning the `AbsFrame` the simulation consumes. The bulk of the case study's proof text. |
| `CoreSimAbs.lean` | 336 | **Stage C**, `Abs` preservation for the stutter rows: six instances of the single frame argument `Abs.frame`, since the ultra-lazy twin (D16) is untouched by every hidden row. Then the assembly, `Inv.step` — `Inv` is preserved by every `layeredSpec` step, dispatching on the label class through Stage A and calling the matching Stage B helper. |
| `CoreSimBurst.lean` | 187 | The abstract τ-burst kit: `fill_chain`, `byz_fill_chain`, `rebind_mixed`/`rebind_unanim`, `weakStep_of_burst_then_step` — how the twin catches up in one weak step; bursts fire only at `retABA`. `fill_chain` carries the D17 side condition `coin ≠ dead`, discharged at every call site from the twin's `coin = ⊥`. |
| `CoreSim.lean` | 698 | The simulation proof itself, one row per concrete step class (stutters + the single `decide_burst` + the coupled coin row + `retABA` burst-then-return), assembled into `coreSim`. Each row consumes the `AbsFrame` its `Inv.step_*` lemma returns, which is what carries the `A`-certificate and the honest-holder universal of `Abs`'s phase 2 across the step. |

### Layer 6 — the deployed system and the chain
| file | lines | what it is |
|---|---|---|
| `Deployed.lean` | 1669 | **The protocol as it runs**, and the subject of the whole chain. Three kinds of component. (1) `Net.ABAProcN P j` is *the program of process j*, and it is **corruption-blind**: one `ABANodeN = CoreNodeN × (ℕ → GBCA.ProcNodeN)` — the round-loop node and one graded-agreement stage per round, each carrying only its own control record and its inbox rows — with **no** corrupted set, **no** corruption flag and **no** outbox anywhere in the node, so no guard of its table can ask whether the process is honest or what it has multicast. 44 rules, all Dirac, and **none of them fires on τ** (`procStepN_no_tau`): 16 over the shared alphabet `Lab n`, 28 over the rendezvous alphabet `NetEvt` (`gsnd`/`gdlv`/`dsnd`/`ddlv`, the fused `retWPub`, `gcallLoop`, and the five Byzantine drives), which the composition hides. Every label has a row — the participant's or an idle self-loop — so the sub-protocol ports are **input-enabled**: a driven call opens the stage record exactly as an honest call would (`byzCallG`) and the three `byzRetG` rows mark it returned under the same SEAL-level evidence as `retG_A`/`_B`/`_C`, the program supplying the instance-side content and never a round-loop write. (2) `Net.netAdv P` is *the network adversary*, holding everything a process may not see: `NetState = pool : ℕ → Fin n → Finset Msg` (D5), `dpool : Fin n → Finset Bool` (D12′) and `F`. 20 rules, all Dirac; the send rows pool (`gsnd`, `callG`, `retWPub`, `dsnd` under the write-once `b ∉ dpool j`), the delivery rows carry the soundness guards `m ∈ pool r j` / `b ∈ dpool j` and consume nothing, `retABA` requires `b ∈ dpool id`, seven rows read `F` — the five drive authorisations plus the two τ injections `byzG` (arbitrary stage message) and `byzD` (either DECIDED bit, hence equivocation) — and `fail` is `NetState.corrupt`, the total Dirac transform **guarded by `k ∉ F ∧ |F| < f`**. The corruption budget is that component guard: nothing restricts the transition relation and no theorem assumes it of a trace. (3) `WCC.specFamily` enters as it stands, joined over the extended alphabet through a partial label pullback (`PLTS.System.mapIdle` along `wccPull`: `byzCallW`/`byzRetW`/`retWPub` map onto the oracle's own `callW`/`retW` rows, every other rendezvous label leaves it idle), keeping its own copy of `F` and its own budget-guarded `corrupt`; it is the one component with a non-Dirac rule. Assembly: `deployedPre = syncProduct ABAProcN ∥ (netAdv ∥ wccLift)`, `deployedGroup = (deployedPre.abstract netEvtLabels).relabel`, `deployed = deployedGroup.abstract hiddenAPI`. This file is where the deployed transition relation is pinned down — the three rule tables, the pipeline, and the inversion lemmas that read a composite transition back into the rows its components contributed. |
| `GBCASub.lean` | 1668 | **The round's graded-agreement subsystem**, the unit the analysis replaces, drawn to be exactly what that replacement may see. `GSub.gbcaProc P r j` is the local stage program of process `j` in round `r`: one stage record — the process's own protocol data and the messages delivered to it, indexed by sender (`GBCA.ProcNodeN`) — and nothing else, with no corrupted set, no corruption flag, no record of what it has multicast, and no round-loop data. `GSub.gNet P r` is **the round's own message fabric**: the per-sender pools beside the corrupted set. A multicast is a joint step of the sender, which writes its record, and the fabric, which pools the message; a delivery is a joint step of the fabric, which checks the message is pooled under the named sender, and the receiver, which files it under that sender's inbox row. Both rendezvous are labels of the subsystem-internal alphabet `GLab n = NLab n ⊕ GEvt n` and are hidden before anything outside sees the subsystem, so `sub P r` speaks the deployed alphabet `NLab n` and its interface is exactly the round's ports `callG r`, `retG r`, `gcallLoop r` and the three Byzantine graded-agreement drives of round `r`. **D11 splits here**: the subsystem carries a drive's *effect* (`byzCallG` opens the stage record and pools its `INPUT` under no `k ∈ F` guard, `byzRetG` sets `returned` on the same evidence an honest return needs) and the *authorisation* belongs to the network that surrounds it. `gbcaSide` is the ℕ-indexed family of these subsystems: a round-tagged label moves its round, `τ` moves one round, and `fail` is a broadcast, which is what keeps the per-round copies of the corrupted set in lockstep. The replacement licence is **`subSim`**, in two legs. The first is strong and functional: `subDefl` reads a subsystem state as one monolithic `GBCA.ImplState` (the programs' records and inboxes beside the fabric's pools and corrupted set — the same four fields under a different partition) and `sub_projects` matches every subsystem transition with the monolithic instance's, one step for one step with no stuttering. The second is `GBCA.implRefines` used as it stands, its weak answer lifted along a section of `gPull`, the projection onto the specification alphabet that reads a Byzantine call drive as a call, a Byzantine return drive as a return, and the two call loops as calls. `liftedSpecG` — the specification read back along `gPull` — is the system that replaces the subsystem. |
| `Layered.lean` | 2348 | **Layer boundaries as component boundaries**, all of it in namespace `Layer` (`PLTS.ABA.Layer`, the layer-cut counterpart of the deployed reading's `Net`). The same deployed system, cut into four factors over the extended alphabet: `GSub.gbcaSide` (the round subsystems), `syncProduct (coreProcN P)` (the `n` round loops — `CoreProcStepN` is the core-slice half of every deployed program row), `aNet P` (what the network adversary keeps once the rounds own their fabrics: the DECIDED pools, the corrupted set with its budget, and the authorisation `k ∈ F` of every Byzantine drive), and the coin oracle through the same pullback `Net.wccLift`. Then the deployed system's own pipeline, factor for factor: `layeredPre` → `layeredGroup = (layeredPre.abstract netEvtLabels).relabel` → `layered = layeredGroup.abstract hiddenAPI`. `regroup` re-partitions a deployed state — stage slices and round-tagged pools gathered per round, core slices gathered per process, DECIDED pools and corrupted set to `aNet`, oracle carried across untouched — and it both preserves (`layeredForward`) and reflects (`layeredConverse`) transitions, giving `layeredSim`/`layeredSimConverse` by `ofStrongFunctional`/`_converse` and hence **`layered_atd`**. No reachability, no invariant: every copy of the corrupted set on the layered side *is* the adversary's one set read through `regroup`, so the drive authorisation on either side is the same proposition. `#guard_msgs` firewall on the three. |
| `LayeredSpec.lean` | 487 | The **deployment-shaped specification side**: `specSide` is the ℕ-indexed family of round specifications read over the deployed extended alphabet, `layeredSpecPre` is `layeredPre` with its graded-agreement factor replaced by it, and `layeredSpec` runs the same pipeline. `famSubSim` lifts the per-round `GSub.subSim` to the family by `ForwardSimulation.family` (broadcast compatibility from `GSub.subSim_failAct`), `famSubSimProb` crosses to a probabilistic simulation once, at family level, and **`substSim`** applies the four congruences under the layered system's own context — `parallel_right` for the three untouched factors, `abstract` for the rendezvous alphabet, `relabel` for the read-back over `Lab n`, `abstract` for the sub-protocol API — yielding `substitution` and `deployed_layeredSpec`. The rest of the file reads `layeredSpec` row by row, in both directions: the rows of the specification side and of the coin oracle's family, a joint transition of the four factors read into its component rows and built from them, and the three routes a labelled transition takes through the two hiding layers. That vocabulary is what the core simulation and the non-vacuity witnesses run on. The headlines that chain this into the deployed protocol's guarantee are in `Main.lean`. |

### Layer 7 — results
| file | lines | what it is |
|---|---|---|
| `Main.lean` | 214 | The deliverables: `refines` (`ATD (deployed) ⊆ ATD (spec)`), `main` (Validity ∧ Agreement for every positive-mass trace of the deployed protocol `deployed` — GBCA at impl level, WCC assumed at spec level), `simComposed` (the three simulations of the chain joined by `ProbabilisticForwardSimulation.trans`, along the composite of their three relations — the graph of the regrouping, the pointwise round substitution, and the core relation). The inclusion route and the composed-simulation route are independent: `refines` chains soundness inclusions and never invokes transitivity of simulation. Also the headline set the reader is meant to cite, gathered here so that every citable statement is in one file: `layeredSpec_spec`, `deployed_spec`, the **hypothesis-free** **`deployed_safe`** (every positive-probability trace of the deployed protocol is valid and agreeing — the corruption budget is the network adversary's own component guard, so nothing is assumed of the trace), **`deployed_traces`** (such a trace has positive probability under an achievable trace distribution of `layeredSpec`) and `layered_safe`. Fifteen `#guard_msgs` axiom firewalls — the build fails if any headline, or a framework result the chain rests on, ever acquires `sorryAx`. |
| `Examples.lean` | 619 | Non-vacuity: a concrete n = 4, f = 1, ε = 1/2 happy-path run of `layeredSpec P4` carried all the way to a `retABA` decision (21 steps), plus a `fail` broadcast synchronising all four factors. Every step but the coin flip is Dirac and the flip's chosen branch has mass `ε`, so the path is a positive-probability execution; the positive-probability remark itself is informal (no machine-checked `achievableTraceDists` membership — see Future work). The ABA-side factors are named through the view of `CoreView.lean`. |

## Future work

- **Externalize the round's message fabric in the graded-agreement proof.** The round
  subsystem `GSub.sub P r` carries its fabric `GSub.gNet` as a component, but the
  refinement into the round specification runs through `GBCA.ImplState`, whose `sent`
  field holds the fabric's pools: `GSub.subDefl` maps `(σ.1 j).proc`, `σ.2.pool`,
  `(σ.1 i).inbox` and `σ.2.F` into the four fields of one record, and `GBCASim.lean`'s
  invariant is stated over that record. The consequence is a coupling. Substituting a
  weaker fabric — losses, reordering, a different forgery model — leaves the chain
  untouched, since the whole subsystem is the exchanged factor, but it obliges a rewrite
  of `subDefl`/`sub_projects` and of the invariant, because neither names `gNet`.
  The remedy is the one `ABA/CoreView.lean` applies on the ABA side: give the pair
  `(∀ j, GBCA.ProcNodeN) × GSub.GNetState` the accessors `proc`/`sent`/`recv`/`F` under
  their present names, state the invariant through them, and let the fabric stay a
  factor of the state the relation is defined on. `subDefl` is a bijection — `ProcNodeN`
  holds exactly `proc` and `inbox`, `GNetState` exactly `pool` and `F` — so the invariant
  transports field for field rather than being re-derived.
- **Achievability theorem**: one explicit scheduler for `deployed P4` driving a
  two-return decision trace `t`, with `∃ D ∈ achievableTraceDists (deployed P4), D t ≠ 0`
  (probOf ≥ the ε-product via a traceProb single-execution lower bound) — the
  machine-checked non-vacuity for `main`'s own system, exercising Agreement with two
  returns.
- **Budget as an assumption throughout** (not pursued): the alternative shape is an
  unguarded `fail` in every system, `|F| ≤ f` relativized out of the invariants, and
  every headline conditional on a trace-level budget predicate — a full-replacement
  campaign. It is unnecessary here. In `Deployed.lean` the budget is a component
  guard (`NetState.corrupt`, `k ∉ F ∧ |F| < f`) on the one box that owns the corrupted
  set, so the deployed system enforces it structurally and `deployed_safe`/`deployed_traces`
  need no hypothesis on the trace; every step of the chain relates plain systems, plain
  against plain, `layered_atd` included.
- **`ValidityTrace` witness strengthening**: the current witness clause accepts any
  preceding `callABA id' b`; the proof yields a stronger ghost-backed witness. Care:
  the D13 ghost is *last*-rule-1-write (D16 junk-erasure), so a "first call" restatement
  is not immediate.

## Shared framework (`../Framework/`)
| file | lines | what it is |
|---|---|---|
| `TraceSupport.lean` | 594 | Bridge from trace-distribution inclusion to per-trace properties (support-level safety transfer): `is_exec_of_probOf_ne_zero`, `exists_exec_of_traceProb_ne_zero`, the invariant inductions `is_exec_induction`/`is_exec_induction_labels`, `safety_transfer`. Also the label-side transport of a run — `AlterSeq.mapLab` and its `stateAt`/`endState`/termination glue, `is_partial_exec_mapLab`, `System.trace_mapLab` — which both `IdleFamily.lean` and `Relabel.lean` build on. |
| `IdleFamily.lean` | 221 | Three combinators and their LTS preservation. `System.withIdle`: idle self-loops outside a busy set. `System.mapIdle φ`: a system read over a finer alphabet along a partial label map, with `mapIdle_isLTS` and the read-back of both weak transitions along a section of `φ` (`System.weakLSilent_mapIdle`, `System.weakLStep_mapIdle`). `System.family`: ℕ-indexed instance families — how round-`r` instances ignore other rounds' labels under full-sync `parallel`, with a broadcast disjunct keeping every instance's copy of shared bookkeeping in lockstep. |
| `FamilySim.lean` | 385 | Congruence: per-instance refinement lifts to the family (`ForwardSimulation.family`). Carries the single-step weak-transition kit it needs — `System.weakLSilent_of_step`, `System.weakLStep_of_step`, the two-step burst `weakLStep_tauThen` — and the `AlterSeq.map` transport glue. |
| `SyncProduct.lean` | 164 | `System.syncProduct`: the n-ary full-synchronisation product — a visible label moves every component, τ moves exactly one. With idle self-loops on non-owned labels this is the rendezvous idiom of the deployed presentation. Both determinacy results for compositions live here (`syncProduct_isLTS`, `System.parallel_isLTS`) with the Dirac-product lemmas they run on (`piPMF_pure`, `prodPMF_pure_pure`, `prodPMF_pure_left_apply`, `map_apply_inj`). |
| `Relabel.lean` | 471 | `System.relabel`: transport of a system over `Label ⊕ Extra` back to `Label` along the left embedding, after the extra (network) alphabet has been hidden; plus `abstract_isLTS`. And the matching precongruence **`ProbabilisticForwardSimulation.relabel`** — a probabilistic forward simulation survives the restriction — with the weak-scheduler transport it needs: `WeakScheduler.relabel` and its emission identities `relabel_next_none`/`relabel_next_some`, `probOf_relabel`, `haltMass_relabel`, `weakTau_relabel`, `weakStep_relabel`. |

## Suggested first read

`Params` → `Labels` → `Spec` → skim `SpecSafety`'s two trace predicates →
`Core`'s module docstring → `Deployed`'s module docstring (the system the
headlines are about) → `LayeredSpec`'s module docstring (the system the core
simulation starts from) → `Main`, whose module docstring names the three steps
of the chain and their files. Follow it into the statements themselves along
`Layered.layered_atd` → `LayeredSpec.substSim` → `CoreSim.coreSim`, with
`CoreView`'s `ABAState` beside the last of them. That path (≈ 700 lines of
reading) gives the full statement-level picture; descend into Layer 3 and
Layer 5 only when you want the proofs. For liveness context (deliberately out
of scope here) see `../NOTES-Liveness-Roadmap.md`; for how the encoding stands
against the source blueprint and ABDY22 beyond the D-registry above, see
`../NOTES-Fidelity.md`. The prose account of this case study is the ABA chapter
of the repository's own blueprint (`../../blueprint/src/`), which carries it in
two editions over one set of statements: the default one (`content.tex`, a
reference stating each object and result against its Lean declaration, built by
`leanblueprint pdf` / `leanblueprint web`) and a full one (`content-full.tex`,
adding the rule inventories, the pseudocode and the proof bodies, built by
`bash blueprint/build-full.sh`).
