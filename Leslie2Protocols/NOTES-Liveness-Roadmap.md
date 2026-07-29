# Liveness roadmap: ABA fair termination and the `Leslie_LTS_Liveness` machinery

Technical memo (2026-07-22). Context: the ABA safety stack in this repo is complete and
axiom-clean (`ABA/Main.lean`); liveness (termination) is deliberately out of scope so far.
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
coin resolves without delivering. In TS 3 that outcome is absorbing — `Step.flip` fires
once per instance and `Step.ret` has a positive guard (`ABA/WCCSpec.lean:91,97`) — so the
processes awaiting a `dead` round's return never return, in any extension, under any
scheduler. A single such round therefore strands positive mass, and no fairness
assumption recovers it. The honest target carries the failure mass.

The function `g` is left open here. Each round is a race between the `δ_f` failure mass
and a decision: a resolution matches the bound bit with probability `ε` and fails to
deliver with probability `δ_f`, and how those compound over the round sequence depends on
the fairness constraint chosen and on the round structure the proof exposes. Fixing `g` —
including whether it is simply `δ_f`, or a ratio of the two masses — is part of the work
below, not an input to it. What is settled is the shape: `g(ε, 0) = 0`, so the `δ_f = 0`
instance is exact fair AST, and the safety chain already proved is indifferent to
`δ_f` either way.

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
  (`Results.lean`; the ω-composition `weakTau_flatten` closed 2026-07-22).
- The full ABA safety chain (`GBCA impl ⊑ spec`, substitution, the core simulation).
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
expected at the `hybridImpl ↔ ABA.spec` boundary.

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
   trace-distribution inclusion would push the spec-level mass bound down to
   `hybridImpl`.
   Budget the corrupt-fairness mismatch as the primary risk: the fairness markings on
   both sides must be chosen so that ideal-side actions are fair only under honest
   enablement (state-dependent `fair_labels` — the witness already supports
   state-dependence; the BRB/BCA failure was a modeling choice as much as a theorem gap).
   The dead-coin asymmetry of §5 is a second constraint on the same markings.
3. **Model unification** (background hygiene): Leslie_LTS's PLTS + adapters are
   step-shape-identical to Leslie2's `System`; its sorried `WeakProbabilistic`/
   `ProbSimulation` layers are subsumed by Leslie2's proven ones. Converging on one
   probabilistic model would let the LTS liveness toolkit and Leslie2's simulation
   stack meet without duplication.

## 5. Design note: the two dead coins under fairness

The `dead` outcome is encoded twice, and the two encodings are not symmetric. The
asymmetry is invisible to safety and load-bearing for any fair-inclusion proof.

In TS 3 (`ABA/WCCSpec.lean:91,97`) `dead` is **absorbing**. `Step.flip` requires
`hv : s.val = .bot`, so an instance resolves once; `Step.ret`'s guard
`s.val = .top ∨ s.val = .bit b` is positive, so a `dead` instance enables no return in
any extension.

In TS 1 (`ABA/Spec.lean:201,220,228`) `dead` **freezes the round but is re-flippable**.
Rule 6 is disabled because `TVal.agrees` fails on `dead`, and rule 7 by its
`hd : s.coin ≠ .dead` conjunct, so the round takes no honest input. Rule 5's own guard —
every call slot empty, `bind` set — is still satisfied in that state, so a second
resolution is enabled and can unfreeze the round. Only the Byzantine fill (rule 10,
`callByzFill`) makes the freeze permanent: it occupies a call slot, which disables rule 5,
and from `f` corrupted callers alone no quorum is reachable, so rules 3 and 4 never reset
the slots.

Under fairness the two encodings diverge. A fairness marking that counts rule 5 as fair
obliges every fair scheduler to re-resolve a `dead` round of TS 1, so the specification
recovers the `δ_f` mass that the implementation cannot: behind that round sits a TS 3
instance already absorbed in `dead`, and no scheduler makes it deliver. The
implementation would then have a fair-achievable trace distribution — stranded mass on a
never-returning round — that the specification does not, and fair trace-distribution
inclusion fails in exactly the direction item 2 of §4 needs it.

Two repairs are available; this note records both and decides neither.

- **Mark rule 5 unfair.** No fair scheduler is then obliged to re-flip, a `dead` round of
  TS 1 may stand frozen, and the two systems agree on what a fair scheduler must do. A
  marking is not part of the step relation, so nothing already discharged about TS 1 is
  touched.
- **Make TS 1's `dead` absorbing.** Add a once-per-round flip guard to rule 5 — the
  analogue of TS 3's `hv` — so that a resolved round is not re-resolved and the two
  `dead` states agree by construction. This changes the step relation, so the core
  simulation and the safety chain over TS 1 have to be re-checked against it.

Which is right depends on what the fair-inclusion proof needs from the markings, so the
choice belongs to that proof rather than to this note.

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
has anything to decide here. That is the opposite of TS 1's rule 5 (§5), where the two
repairs on the table each cost something a proof depends on and the choice is open.

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
- Own-flag deployed model and its conservativity bridge: `ABA/FlatOwnFlag.lean`
  (`ownFlagFlatB_bridge`, `BudgetTrace`) — the presentation to state fair termination
  over if it is to be stated of the deployed system: `fail` is always enabled there and
  the budget is a hypothesis on traces, so the marking of `fail` is an explicit choice
  rather than one the state makes.
- Paper validation of fair AST for this protocol family: `Papers/consensus-src`
  (Ben-Or + graded consensus, SMT-checked in Caesar)
