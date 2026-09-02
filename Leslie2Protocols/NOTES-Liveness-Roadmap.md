# Liveness roadmap: ABA fair termination and the `Leslie_LTS_Liveness` machinery

Technical memo (2026-07-22). Context: the ABA safety stack in this repo is complete and
axiom-clean (`ABA/Results.lean`); liveness (termination) is deliberately out of scope so far.
This note records what ABA liveness would require, what already exists in the sibling
repo `Leslie` (branch `Leslie_LTS_Liveness`), and how the pieces fit. All file:line
references into `Leslie` are as of that branch's current HEAD.

## 1. The target property

ABA termination is a **fair** property, and with the coin this development encodes it is
not a probability-1 property. The target is **fair almost-sure termination** — for every *fair*
scheduler, the protocol decides with probability 1 — at `δ_f = 0`, and **fair
`(1 − g(ε, δ_f))`-sure termination** — for every *fair* scheduler, the protocol decides
with probability at least `1 − g(ε, δ_f)` — in general.

The failure mass is in the encoding, not in the statement of the goal. Both coin
resolutions of the development follow `ABA.Params.wccPMF` (`ABA/Params.lean`), which puts
mass `δ_f` (the Lean field `Params.δ`, `δ_f` in the blueprint) on the outcome `dead`: the
coin resolves without delivering. In TS 3 that outcome is absorbing — `WCC.Step.flip`
fires once per instance and `WCC.Step.ret` has a positive guard — so the
processes awaiting a `dead` round's return never return, in any extension, under any
scheduler. A single such round therefore strands positive mass, and no fairness
assumption recovers it. The honest target carries the failure mass.

The function `g` is protocol-side, and its value there is left open. Each round is a race
between the `δ_f` failure mass and a decision: a resolution matches the round's surviving
bit with probability `ε` and fails to deliver with probability `δ_f`, and how those
compound over the round sequence depends on the fairness constraint chosen and on the
round structure the proof exposes.

The specification pins the target the race is measured against. `ABA.spec` runs that race
at one point, in the mode loop of §5: from `Mode.idle`, and only where both bits carry
`f + 1` support, a flip locks with probability `ε` and kills with probability `δ_f`, the
release mass `1 − ε − δ_f` returns to `Mode.idle`, and a lock is never discarded. A
flip-only scheduler from such a state therefore reaches the terminal mode
`Mode.dead` with probability `δ_f / (ε + δ_f)`, and that is the specification-level bound
a transfer would carry:

```
g(ε, δ_f) ≤ δ_f / (ε + δ_f),    g(ε, 0) = 0
```

so the `δ_f = 0` instance is exact fair AST. The safety chain already proved is
indifferent to `δ_f` either way.

Both quantifiers of the `δ_f = 0` instance are irreducible (validated against
`Papers/consensus-src`, which proves fair AST for Ben-Or and graded consensus via ranking
supermartingales in Caesar):

- fairness is a qualitative, per-run constraint on the *scheduler* (unfair schedulers
  genuinely prevent termination);
- almost-sureness is a measure-1 quantifier over the *coins* (the all-bad-coins run is
  fair, consistent, and non-terminating — it merely has measure zero). Hence no purely
  qualitative fairness assumption yields per-run termination for ABA.

**What binding contributes.** Every fair-termination argument for this protocol family
turns on a precondition the coin cannot see: the round's value is fixed before the coin
resolves, so a resolution matching it decides. That precondition is structural here rather
than an assumption a liveness proof would have to carry. At the specification, GBCA's
exclusion set `dead` only grows — its single writer inserts and corruption does not touch
it — and both value-bearing returns demand `v ∉ dead ∧ !v ∈ dead`, so any two graded
returns of one round hand out the same bit and a `C`-return pins a bit that no extension
of the run hands out at grade ≥ 1: `retG_value_agree`, `specInst_binding`,
`retC_dead_nonempty` (`ABA/GBCASafety.lean`), each from monotonicity alone, no invariant.
At the implementation the encoding is ABDY22's Algorithm 6 in full (D18), whose Binding
the paper proves. The precondition is therefore available on both sides of the refinement,
and a liveness effort inherits it rather than re-deriving it; what it must supply is the
probabilistic part, the race between the coin's `ε` mass and the `δ_f` failure mass.

In this repo's terms: the statement lives naturally at the trace-distribution level —
"every fair-achievable trace distribution of `ABA.spec` gives mass at least
`1 − g(ε, δ_f)` to traces where every honest process fires `retABA`" — and such mass
bounds DO transfer along fair-trace-distribution inclusions, being universally quantified
over the trace distributions of the including system.

## 2. What exists today, per repo

**Leslie2 (this repo)** — probabilistic simulation, *complete*:
- Weak probabilistic forward simulation with proven soundness AND transitivity
  (`Results.lean`; the ω-composition is `weakTau_flatten`).
- The full ABA safety chain, stated in the protocol's own coordinates: the protocol
  carried into its reading as a composition of components, the substitution of each
  round's graded-agreement instance by its specification (`GBCA impl ⊑ spec` under one
  family congruence), and the core simulation of the hybrid against the ABA
  specification.
- `Leslie2Extra/Fairness`: fairness-marked PLTS + ranked **strong** probabilistic
  simulation, sound for surely-fair achievable trace distributions
  (`fairAchievableTraceDists_subset`, needs `ImageFinite` for a König lift). Proven.
- No liveness proof rules, no martingale/variant machinery, no trajectory-measure link
  from the Fairness line (a separate Ionescu–Tulcea line exists in `Leslie2Extra/Measure`).

**Leslie, branch `Leslie_LTS_Liveness`** — possibilistic liveness, *complete*; probabilistic
port, *started*:
- `Leslie_LTS/Framework/{Liveness,Divergence,LTL,Rules,Trace,Simulation}.lean`: TLA-style
  weak/strong fairness per label, leads-to + WF1 + lattice rules, shallow LTL (incl. past
  operators, `[ltl| …]` DSL), fair-divergence notions — all **sorry-free**.
- The ranked witness `ForwardSim.WeakDivPreserving` (`Simulation.lean:1339`): decorates the
  weak/stuttering `ForwardSim`; well-founded rank on concrete states; obligations keyed on
  fair-vs-unfair concrete steps and on the abstract answer being empty / non-`AllFair`;
  fair-deadlock clause. Transfer theorems **proven**: `preserves_fair_weak_divergence`
  (:1506), `transfers_satisfaction` (:2110), `transfers_leads_to` (:2246). This formalizes
  the possibilistic fair version of Gaspard's CONCUR 2026 material (§6.2 + §6.4 per
  `plans/fair-weak-div-sim.md`); §6.3 (the probabilistic version) is not formalized there.
- `Leslie_LTS/Framework/Probabilistic.lean`: a PLTS model with **the identical step shape
  to Leslie2's** (`step : State → Label → PMF State → Prop`) plus proven LTS↔PLTS adapters
  (`fromLTS` Dirac embedding, `toLTS` support unfolding, roundtrip lemma). The layers atop
  it (`WeakProbabilistic.lean`, `ProbSimulation.lean` — weak τ-transitions, coupling-based
  `WeakProbSim`) are sorried (9 + 4): they are, structurally, an unfinished re-derivation
  of exactly what Leslie2 has already proven end-to-end.
- `Leslie/Prob/`: the certificate line on a different (functional, gated-action) model
  `ProbActionSpec` — `FairASTCertificate` (Majumdar–Sathiyanarayana POPL'25 Rule 3.2 +
  fair extension) with `sound` **proven**, conditional on caller-supplied trajectory
  witnesses (`TrajectoryFairProgress` etc.); Ionescu–Tulcea trace measures; probabilistic
  Abadi–Lamport refinement. Two real sorries remain (`RandomisedAdversary.lean`). No
  bridge from `ProbActionSpec` to the relational PLTS model.

The two repos are complementary halves of one program: Leslie has liveness without
(finished) probabilistic simulation; Leslie2 has probabilistic simulation without liveness.

## 3. Is the ranked fair-divergence witness "exactly what ABA needs"?

**It is the right design on the wrong model — with one hard-won warning attached.**

*Right design*: it handles precisely what `Leslie2Extra/Fairness` does not — stuttering.
The ABA chain's simulations are weak (the core simulation's lazy twin stutters on almost
every row), so any fairness-preservation for ABA must discipline stutters exactly the way
`WeakDivPreserving` does (rank must decrease when the abstract answers a fair concrete
step with silence).

*Wrong model*: it is qualitative; ABA's property is a mass bound over fair schedulers
(§1). A port into the
probabilistic setting is needed — i.e., the not-yet-formalized §6.3, for which Leslie2's
proven weak-simulation stack is the natural substrate.

*The warning* (empirical, from the possibilistic-liveness proofs themselves): **both flagship
protocol proofs on that branch (BRB, BCA) abandoned the witness-transfer route** — a
"corrupt-sender fairness mismatch": an action that is unconditionally fair on the ideal
side corresponds, under a corrupt sender, to only-unfair concrete steps, making the
antecedent-transfer obligation (`h_ante_transfer`) and the fair-deadlock clause
unprovable; ideal-side fair weak divergence *genuinely fails*. Both protocols instead
prove liveness **directly** on the concrete system via `assumes_fair_wf` + WF1/leads-to
chains (sorry-free), keeping simulation for safety only. ABA has the same corruption
structure (Byzantine processes, adversarial delivery), so the same mismatch should be
expected at the `protocol ↔ ABA.spec` boundary.

## 4. Recommended shape of an ABA liveness effort

Ordered by expected value-for-effort:

1. **Spec-level liveness, simulation for safety only** (mirrors the successful BRB/BCA
   pivot AND the consensus-src architecture). Prove the §1 target for `ABA.spec`
   directly: port the fairness/WF1/leads-to toolkit to PLTS traces, state the decide-mass
   property over fair schedulers, and discharge it with a supermartingale/variant
   certificate — either by bridging `Leslie/Prob`'s proven-conditional
   `FairASTCertificate.sound` to the PLTS model, or by re-deriving the rule on
   Leslie2's model (the `Leslie2Extra/Measure` Ionescu–Tulcea line supplies the
   trajectory measure). consensus-src's GBCA/Ben-Or certificates show what the variant
   functions look like. Deliverable: "under fair scheduling, `ABA.spec` decides with
   probability at least `1 − g(ε, δ_f)`", the `δ_f = 0` case reading as a.s. decision;
   combined with the existing safety refinement this is already a strong end-point.
2. **The §6.3 port** (ambitious add-on): `FairWeakProbabilisticSimulation` — merge
   `WeakDivPreserving`'s stutter-ranking with `Leslie2Extra/Fairness`'s probabilistic
   descent/König machinery over Leslie2's weak simulation. Sound transfer of fair
   trace-distribution inclusion would push the spec-level mass bound down the chain to
   `protocol`, which is where a fair-scheduling statement about this protocol belongs.
   All three steps are inclusions in the same direction, `protocol ⊑ composed ⊑
   hybrid ⊑ ABA.spec`, so a mass bound established at `ABA.spec` has to be
   transported down all three, the composition link (`protocolSim`,
   `ABA/ProtocolSim.lean`) included. That link imposes no constraint on the amplification
   axis. Under D22 a process retains the stage record of every round it has touched and
   answers that round's traffic under an instance-local guard, whichever round its loop is
   in, which is the behaviour ABDY22's Lemmas 4.6 and E.5 are stated under; and
   `ABAProcStepN.terminate` fires only once the process's own return has fired and `2f + 1`
   DECIDED receipts are on record, so the concrete stopping point is a terminate in the
   paper's sense — the endpoint a fairness marking would stop at. Nothing in the
   development says when that step fires, or that it ever does: the marking itself and
   every statement about it are what a campaign has to supply.
   Budget the corrupt-fairness mismatch as the primary risk: the fairness markings on
   both sides must be chosen so that ideal-side actions are fair only under honest
   enablement (state-dependent `fair_labels` — the witness already supports
   state-dependence; the BRB/BCA failure was a modeling choice as much as a theorem gap).
   The two failure outcomes agree by construction (§5), so the markings have nothing to
   reconcile on that axis.
3. **Model unification** (background hygiene): Leslie_LTS's PLTS + adapters are
   step-shape-identical to Leslie2's `System`; its sorried `WeakProbabilistic`/
   `ProbSimulation` layers are subsumed by Leslie2's proven ones. Converging on one
   probabilistic model would let the LTS liveness toolkit and Leslie2's simulation
   stack meet without duplication.

One cost note, on any of the three. The achievability item of `ABA/README.md` — an
explicit scheduler driving `protocol P4` to a two-return trace of positive mass — is
expensive under the wait-until order and the case denials: every stage send
waits on the sender's own send at the level below, and every return but `retA` discharges
the denials of the cases above it, so a witness has to schedule the full five-level
exchange at each participating process and then exhibit those denials at each returner.

## 5. Design note: the two failure outcomes under fairness

The `δ_f` mass is encoded twice, and the two encodings agree. Neither is visible to
safety; both matter to any fair-inclusion proof.

In TS 3 the failure outcome is absorbing. `WCC.Step.flip` requires `hv : s.val = .bot`,
so an instance resolves once, and `WCC.Step.ret`'s guard `s.val = .top ∨ s.val = .bit b`
is positive, so a resolution at `TVal.dead` enables no return in any extension.

In TS 1 the same mass drives the control mode `Mode.dead`, which is globally absorbing
(D17). `PLTS.ABA.SpecStep.coinFlip` is one-shot: its guard `hm : s.mode = .idle` admits it
only at `Mode.idle`, and its `kill` outcome — mass `δ_f` under `PLTS.ABA.flipPMF` — leaves
the state at `Mode.dead`. The only other `τ`-rule is `PLTS.ABA.SpecStep.decide`, whose
guard `hm : s.mode ≠ .dead` excludes exactly that mode. A killed specification therefore
decides nothing and returns nothing, in any extension, under any scheduler, which is what
the absorbed TS 3 instance does one level down. The two encodings agree on what a fair
scheduler can be obliged to do, and no marking has anything to reconcile between them.

The lock is the symmetric half. `flipPMF` puts mass `ε` on `lock`, whose post-state is
`Mode.locked`; there the flip demands `Mode.idle`, so `SpecStep.decide` is the only
`τ`-rule that can be enabled at all. It is enabled exactly when some bit carries `f + 1`
support, and a state that has passed the flip's own guard leaves some bit supported ever
after. The forcing runs on the *sum* of the two support counts. Neither count is monotone
by itself: `SpecStep.callSet`'s overwrite takes its writer out of one of the two supporter
sets. The sum is. An overwrite moves a supporter from one set to the other and leaves the
sum where it was; a write into an empty slot raises it by one; a `fail` puts its
identifier into both sets through the `id ∈ s.F` disjunct and raises it by one or two;
`SpecStep.callByz` writes only at identifiers that disjunct already counts at both bits,
so it moves neither count. The flip's `hmix` guard asks `f + 1` at each bit, so the sum
stands at `2f + 2` or above at every lock, hence at every later state one of the two counts
is `f + 1` or above and `SpecStep.decide` is enabled. A lock is never discarded: at a
locked state the one internal move a scheduler has is the decision. The release mass
`1 − ε − δ_f` returns the
state to `Mode.idle`, where the flip is enabled again, so a flip-only scheduler runs the
`ε`-versus-`δ_f` race to absorption and locks with probability `ε / (ε + δ_f)`. That is
the bound §1 records.

**The gate and the liveness half of Validity.** `hmix` also settles the unanimous case
structurally, at the specification and with no proof obligation. A supported bit has a
never-corrupted recorded inputter (`SuppOK.honest_supporter`, `SpecSafety.lean`), so under
honest unanimity on `v` the bit `!v` is supported by corrupted identifiers alone, at most
`f` of them, and `hmix` fails at every state such a run reaches. The flip is then
unreachable, and with it every probabilistic branch of the system: the unanimous path is
Dirac, and `SpecStep.decide` can write only `v`. That is the liveness half of Validity —
"if all correct processes input `v` then all correct processes return `v`" — held by the
shape of the guard rather than by an argument.

**Transfer caveat: the δ-exposure of the unanimous path.** The spec-level guarantee
transfers to the protocol only at `δ_f = 0`, or under a protocol-side reordering. With
`δ_f > 0` the implementation consults the coin under unanimity: the round loop's phase
machine calls `WCC_r` after every graded-agreement return, the coin adoption being a later
line of ABDY22's Algorithm 2 than the call, so a unanimous round still runs a resolution
that carries mass `δ_f` on the outcome that delivers to nothing and strands the processes
awaiting it. The specification's unanimous path has no such branch, so the two agree on
the unanimous case only when `δ_f = 0` or when the protocol is reordered to skip the coin
call on a grade the round has already settled. This is the campaign's transfer caveat and
is recorded here rather than repaired.

**The transfer hook.** The specification names no coin bit. `flipPMF` is `Params.wccPMF`
pushed forward along a map that forgets which bit was delivered: one bit to `lock`, the
other bit and the adversarial outcome to `release`, the failure outcome to `kill`. The
three masses are all the rules read. Reading `lock` as "the coin agreed with the round's
surviving bit" is accordingly not a component of TS 1 — it is what a liveness refinement
would supply, as an outcome coupling between the concrete flip and `flipPMF`: the
agree-outcome, of mass `ε`, coupled to `lock`; the disagree- and adversarial outcomes to
`release`; the failure outcome, of mass `δ_f`, to `kill`. Safety needs none of it, which
is why the specification carries the mode and not the bit.

## 6. Design note: the GBCA kill under fairness

The GBCA specification's `bindUnset` carries the guard `dead = ∅` (`ABA/GBCASpec.lean`), so
one kill happens per instance. Safety is indifferent to the guard — every statement of
`GBCASafety.lean` rests on monotonicity of `dead` and would hold without it — but a fair
reading of the specification is not.

Suppose the guard were the per-bit one, `b ∉ dead`, so that a round could kill both bits in
turn. Take a mixed round: a quorum, `f + 1` F-blind support at each bit, and an `A`-return
of `v` already fired. `bindUnset v` is then enabled — its guards would be the quorum, `f + 1`
support for the spared bit `!v`, and `v` not yet dead, none of which the return disturbs —
so under a blanket-fair marking of the internal transitions every fair scheduler must
eventually fire it. After that kill no bit is alive: `retA` and `retB` are disabled at both
bits, and `retC` is disabled by the A-latch (`grade = some true`). The processes that had
not yet returned never return, in any extension, under any scheduler. Spec-level
Termination — "if `n − f` correct processes take part then all correct processes eventually
return" — would then be false of the specification itself, and no marking on the
implementation side could repair it.

The `dead = ∅` guard removes those states rather than the obligation. Every reachable state
has `dead ∈ {∅, {b}}` (`GBCASafety.dead_card_le_one`), the surviving bit stays alive, and
the A-latch still admits `A`- and `B`-returns. The resolution is structural, so no marking
has anything to decide here. The same holds of TS 1's flip (§5), where the one-shot guard
and the absorbing `Mode.dead` settle the question in the step relation rather than in a
marking.

**Termination proof sketch for the specification as encoded.** Assume the `n − f` honest
processes have called, so the quorum guard holds and holds forever (the count is monotone
in `call` and `F`). The quorum's `n − f ≥ 2f + 1` callers-or-corrupted fall on two bits, so
some bit `v` carries `f + 1` of them by pigeonhole — the `SuppOK(v)` count, itself monotone.
All three guards of `bindUnset (!v)` therefore hold, and they persist until the rule is
taken, so weak fairness fires it; `dead = {!v}` from then on, and `v` is alive at every
later state.

Split on whether the dissent count at `!v` ever reaches `f + 1`. If it never does, `retB`
and `retC` stay disabled forever — each asks `f + 1` at the dissenting bit, `retC` at both
bits — and no `C`-lock can arise, so `retA v` is enabled at every un-returned process for
the rest of the run and the round decides. This is the near-unanimous case: under unanimous
honest input the count is capped by the corruption budget outright
(`GBCASafety.supp_le_of_unanimous`). If the count does reach `f + 1`, then from that point
`retB v` is enabled at every un-returned process, whatever the grade lock, since `retB`
reads no grade. Either way each un-returned process has a return enabled from some point on
and permanently, so a fair scheduler answers it. Nothing in the sketch mentions the coin: it
is a statement about one GBCA instance, and it is what item 1 of §4 would have to supply for
the sub-protocol slot.

## 7. Pointers

- Ranked witness + transfers: `Leslie_LTS/Framework/Simulation.lean:1339,1506,2110,2246`
- Fairness/WF1/LTL: `Leslie_LTS/Framework/{Liveness,LTL,Divergence}.lean`
- BRB/BCA pivot rationale: `Leslie_LTS/Examples/BRB_Liveness.lean:33-49`,
  `Examples/BCA_Liveness.lean:726-751`
- PLTS + adapters in Leslie: `Leslie_LTS/Framework/Probabilistic.lean:34-70`
- Certificates: `Leslie/Prob/Liveness.lean` (`FairASTCertificate`, `sound` at :1719)
- This repo's fairness line: `Leslie2Extra/Fairness/Simulation/{Defs,Soundness}.lean`
- The protocol, whose programs read their own replacement flag and nothing else about
  corruption (D23): `ABA/Protocol.lean` (`protocol`, `netAdv`), with
  its reading as a composition of components in `ABA/Hybrid.lean` (`composed`) and the
  inclusion into it in `ABA/ProtocolSim.lean` (`ProtocolRel`, `protocolSim`,
  `protocol_composed`) — the presentation to state fair
  termination over if it is to be stated of the protocol: the `fail` row belongs
  to the network adversary and is guarded by `k ∉ F ∧ |F| < f`, so `fail` is enabled
  exactly while budget remains and the marking of `fail` is read off that component's
  own state.
- Paper validation of fair AST for this protocol family: `Papers/consensus-src`
  (Ben-Or + graded consensus, SMT-checked in Caesar)
