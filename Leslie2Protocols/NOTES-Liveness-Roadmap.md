# Liveness roadmap: ABA fair-AST and the `Leslie_LTS_Liveness` machinery

Technical memo (2026-07-22). Context: the ABA safety stack in this repo is complete and
axiom-clean (`ABA/Main.lean`); liveness (termination) is deliberately out of scope so far.
This note records what ABA liveness would require, what already exists in the sibling
repo `Leslie` (branch `Leslie_LTS_Liveness`), and how the pieces fit. All file:line
references into `Leslie` are as of that branch's current HEAD.

## 1. The target property

ABA termination is **fair almost-sure termination** (fair AST): for every *fair*
scheduler, the protocol decides with probability 1. Both quantifiers are irreducible
(validated against `Papers/consensus-src`, which proves fair AST for Ben-Or and graded
consensus via ranking supermartingales in Caesar):

- fairness is a qualitative, per-run constraint on the *scheduler* (unfair schedulers
  genuinely prevent termination);
- almost-sureness is a measure-1 quantifier over the *coins* (the all-bad-coins run is
  fair, consistent, and non-terminating — it merely has measure zero). Hence no purely
  qualitative fairness assumption yields per-run termination for ABA.

In this repo's terms: the statement lives naturally at the trace-distribution level —
"every fair-achievable trace distribution of `ABA.spec` gives mass 1 to traces where
every honest process fires `retABA`" — and such mass-1 properties DO transfer along
fair-trace-distribution inclusions.

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

*Wrong model*: it is qualitative; ABA's property is fair AST (§1). A port into the
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
   pivot AND the consensus-src architecture). Prove fair AST of `ABA.spec` directly:
   port the fairness/WF1/leads-to toolkit to PLTS traces, state the mass-1 decide
   property over fair schedulers, and discharge it with a supermartingale/variant
   certificate — either by bridging `Leslie/Prob`'s proven-conditional
   `FairASTCertificate.sound` to the PLTS model, or by re-deriving the rule on
   Leslie2's model (the `Leslie2Extra/Measure` Ionescu–Tulcea line supplies the
   trajectory measure). consensus-src's GBCA/Ben-Or certificates show what the variant
   functions look like. Deliverable: "under fair scheduling, `ABA.spec` decides a.s.";
   combined with the existing safety refinement this is already a strong end-point.
2. **The §6.3 port** (ambitious add-on): `FairWeakProbabilisticSimulation` — merge
   `WeakDivPreserving`'s stutter-ranking with `Leslie2Extra/Fairness`'s probabilistic
   descent/König machinery over Leslie2's weak simulation. Sound transfer of fair
   trace-distribution inclusion would push spec-level fair AST down to `hybridImpl`.
   Budget the corrupt-fairness mismatch as the primary risk: the fairness markings on
   both sides must be chosen so that ideal-side actions are fair only under honest
   enablement (state-dependent `fair_labels` — the witness already supports
   state-dependence; the BRB/BCA failure was a modeling choice as much as a theorem gap).
3. **Model unification** (background hygiene): Leslie_LTS's PLTS + adapters are
   step-shape-identical to Leslie2's `System`; its sorried `WeakProbabilistic`/
   `ProbSimulation` layers are subsumed by Leslie2's proven ones. Converging on one
   probabilistic model would let the LTS liveness toolkit and Leslie2's simulation
   stack meet without duplication.

## 5. Pointers

- Ranked witness + transfers: `Leslie_LTS/Framework/Simulation.lean:1339,1506,2110,2246`
- Fairness/WF1/LTL: `Leslie_LTS/Framework/{Liveness,LTL,Divergence}.lean`
- BRB/BCA pivot rationale: `Leslie_LTS/Examples/BRB_Liveness.lean:33-49`,
  `Examples/BCA_Liveness.lean:726-751`
- PLTS + adapters in Leslie: `Leslie_LTS/Framework/Probabilistic.lean:34-70`
- Certificates: `Leslie/Prob/Liveness.lean` (`FairASTCertificate`, `sound` at :1719)
- This repo's fairness line: `Leslie2Extra/Fairness/Simulation/{Defs,Soundness}.lean`
- Paper validation of fair AST for this protocol family: `Papers/consensus-src`
  (Ben-Or + graded consensus, SMT-checked in Caesar)
