/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Construction.LowerGen
import MyMathlibProject.Construction.DistFair
import MyMathlibProject.Model.ResolvedScheduler

/-!
# Superset direction of the fair `𝒟f`-equivalence (resolved schedulers)

This file targets the **superset** inclusion of the fair distribution-monad equivalence, under the
resolved-scheduler semantics:

  `fairAchievableTraceDists F.dist ⊆ fairAchievableTraceDists F`.

Given a fair resolved `𝒟f(sys,F)`-execution `PE'` achieving trace distribution `D`, we reconstruct a
fair resolved `sys`-execution achieving `D`. The Dirac lift (`Construction/DistFair.lean`) gives the
reverse inclusion.

## The witness and the μ-blind baseline

`(sys.distF F).step` is definitionally `𝒟(sys).step` plus a `Resolvable` side-condition, so `PE'`'s
emissions are valid `𝒟(sys)`-steps.

* **`lowerCoe` — the μ-blind baseline.** Coercing the plain reconstruction of `PE'.average` back to
  a resolved execution realises `PE'`'s trace **for free** (`lowerCoe_traceProbR`). Its scheduler
  ignores the recorded `μ`s, so it is not sure-fair; it is kept only to *state* the trace crux
  (crux A) against a trace-faithful reference.

* **`lowerFairR` — the μ-reading witness (the one used).** At each history it samples a *resolved*
  belief-run `R'` from the **resolved trace-cone** `beliefTCR` (which records the emitted `ω`s and
  every intermediate belief), restricted to the **time-local** coherence `RCoherentTL` with the
  concrete history `r`, and emits through the fairness-revealing kernel `distFairHyperKernel` over
  `R'.toExec`. `RCoherentTL` is resolved, time-local (each recorded step is matched at *that step's*
  belief `(R'.take n).toExec.endState`), and prefix-local — exactly what a König lift and the
  fairness down-transfer consume. `beliefTCR` pushes forward to the plain `beliefTC` along `toExec`
  (`beliefTCR_map_toExec`); `valid` reduces to `distFairHyperKernel_valid`.

## Status (the finite-branching route)

The transformation is `lower_of_finiteBranching`: a fair `PE'` that is **finitely branching**
(`FinitelyBranching`) and **finite mass-splitting** (`FiniteMassSplitting`) is lowered by
`lowerFairR` to a fair resolved `sys`-execution with the same trace distribution and the Dirac
start. These are
the two branching axes of the belief-lift tree; the `FairStrongProbabilisticSimulation` construction
that produces `PE'` supplies finite branching for free
(`abstractMarginal_simJointExecR_next_support_finite`). **No `[Fintype State]`, no tightness, no
image-finiteness of `sys`.**

* **Fairness (`inf_fair`) — PROVEN, axiom-clean** (`lowerFairR_phantom_free_of_finiteBranching`,
  via `exists_timeLocal_coherent_resolved_lift`): under the two branching hypotheses the belief-lift
  tree is genuinely finitely branching, so König (`exists_infinite_chain`) threads an infinite
  `PE'`-consistent `RCoherentTL`-coherent belief-run `R'` (no phantom — a genuine consistent run,
  not a compactness limit; survives beliefs escaping to infinity); `PE'.IsFair.inf_fair` on `R'` and
  `distFairHyperKernel_fair_transfer` carry `F.dist`-fairness down to `F`-fairness of `r`.

* **Trace (`lowerFairR_traceProbR`) — reduced to one true residual**
  `lowerFairR_average_labMass_eq_lowerWith`. Crux A is *true*, but its natural per-history route
  is **false**: the `RCoherentTL` filter is informative about the recorded `μ`s, so mass
  redistributes *across* tight histories of the same trace, not within one history's `toExec`-fibre
  (a rational toy pins the per-`e` gap at `70/13 ≠ 6`; see the residual's docstring). The surviving
  identity is the **label-summed** conservation `AV.labMass labs g = (lowerWith
  distFairHyperKernel).labMass labs g` (`AV := (lowerFairR).average`) — the fair-filtered analogue
  of the proven `dist_traceProb_eq`, needing a `labMass`-style recursion summing over the extension
  state at each step (no finiteness). It feeds `lowerFairR_avgWeight_traceSum_eq_lowerWith` (the
  trace-summed form) via `lowerFairR_average_labProb_eq_aux`.

* **Halt (`lowerFairR_halt_fairDeadlock`) — PROVEN modulo one residual**
  `lowerFairR_halt_restricted_cone_pos` (a consistent terminating run's restricted belief-cone is
  non-empty at its full trace; a corollary once the trace-sum identity lands). The realisable branch
  uses `PE'.IsFair.halt_fairDeadlock` + `distF_fairDeadlock_belief`.
-/

open Stream'

namespace PLTS

variable {State Label : Type} [Silent Label]

/-! ### Forgetting `𝒟f(sys,F)` to `𝒟(sys)`

`traceProb`/`probOf`/`kernel` never inspect the step relation (only `Scheduler.valid` does), so a
`𝒟f(sys,F)`-execution *forgets* into a `𝒟(sys)`-execution for free by weakening the validity witness
`(sys.distF F).step ⇒ 𝒟(sys).step` (drop the `Resolvable` conjunct). -/

/-- The forgetful coercion of a plain `𝒟f(sys,F)`-execution to a plain `𝒟(sys)`-execution: same
initial distribution and same scheduler emissions, with the validity obligation weakened from a
`distF`-step to its underlying `hyperStep` (= `𝒟(sys)`-step). -/
noncomputable def ProbabilisticExecution.distFToDist {sys : System State Label} (F : Fairness sys)
    (pe : ProbabilisticExecution (sys.distF F)) : ProbabilisticExecution 𝒟(sys) where
  initState := pe.initState
  scheduler :=
    { next := pe.scheduler.next
      valid := fun e n s hterm hstate l μ hsupp =>
        (pe.scheduler.valid e n s hterm hstate l μ hsupp).1 }

@[simp] theorem ProbabilisticExecution.distFToDist_initState {sys : System State Label}
    (F : Fairness sys) (pe : ProbabilisticExecution (sys.distF F)) :
    (pe.distFToDist F).initState = pe.initState := rfl

/-- `distFToDist` preserves the plain trace distribution: `traceProb` never inspects the step
relation, only the scheduler and initial distribution (both unchanged), and `trace`/`IsTight` depend
only on the label type — so the two sides are definitionally equal. -/
theorem ProbabilisticExecution.distFToDist_traceProb {sys : System State Label} (F : Fairness sys)
    (pe : ProbabilisticExecution (sys.distF F)) (τ : Seq Label) :
    (sys.distF F).traceProb pe τ = 𝒟(sys).traceProb (pe.distFToDist F) τ := rfl

/-! ### The fairness-revealing decomposition kernel

`distFairHyperKernel` is a `lowerWith`-kernel that reveals fairness: at an emission `(l, ω)` whose
end-state belief `F.dist`-*fairly*-enables `(l, ω)`, it returns the all-`F`-fair realizer `p` of
that fair step (so every produced `sys`-step is `F`-fair); otherwise it falls back to the generic
`distHyperKernel`. Either way it has the same post-marginal `ω.bind id`, so it satisfies the same
validity and marginal-decomposition obligations as `distHyperKernel`. -/

open Classical in
/-- The **fairness-revealing decomposition kernel**. On the fair branch (the end-state belief
`F.dist`-fairly-enables the emission `(l, ω)`) it returns the all-`F`-fair realizer of that fair
step; otherwise it is the generic `distHyperKernel`. Its post-marginal is `ω.bind id` in both
branches. -/
noncomputable def ProbabilisticExecution.distFairHyperKernel {sys : System State Label}
    (F : Fairness sys) (pe' : ProbabilisticExecution 𝒟(sys))
    (E : AlterSeq (PMF State) Label) (l : Label) (ω : PMF (PMF State)) :
    State → PMF (PMF State) :=
  if h : ∃ hE : E.trans.Terminates, (F.dist).fair (E.endState hE) l ω then
    h.choose_spec.2.choose
  else
    pe'.distHyperKernel E l ω

/-- **Validity of `distFairHyperKernel`.** Every distribution in the fairness-revealing kernel's
support is a valid `sys`-step post-distribution: on the fair branch it is an all-`F`-fair realizer
(hence `F`-fair, hence a `sys`-step via `step_of_fair`); on the else branch it inherits validity
from `distHyperKernel_step`. -/
theorem ProbabilisticExecution.distFairHyperKernel_valid {sys : System State Label}
    (F : Fairness sys) (pe' : ProbabilisticExecution 𝒟(sys)) :
    LowerKernelValid pe' (pe'.distFairHyperKernel F) := by
  classical
  intro E hE l ω h_supp s hs μ hμ
  by_cases h : ∃ hE' : E.trans.Terminates, (F.dist).fair (E.endState hE') l ω
  · -- Fair branch: the kernel is the all-`F`-fair realizer `p := h.choose_spec.2.choose`.
    set p := h.choose_spec.2.choose with hp_def
    have hp_fair : ∀ s ∈ (E.endState h.choose).support, ∀ μ' ∈ (p s).support, F.fair s l μ' :=
      h.choose_spec.2.choose_spec.1
    have h_def : pe'.distFairHyperKernel F E l ω = p := by
      unfold ProbabilisticExecution.distFairHyperKernel
      rw [dif_pos h]
    rw [h_def] at hμ
    -- Reconcile the two `Terminates` proofs so `s ∈ (E.endState h.choose).support`.
    have h_choose : h.choose = hE := Subsingleton.elim _ _
    rw [← h_choose] at hs
    exact F.step_of_fair s l μ (hp_fair s hs μ hμ)
  · -- Else branch: the kernel is `distHyperKernel`.
    have h_def : pe'.distFairHyperKernel F E l ω = pe'.distHyperKernel E l ω := by
      unfold ProbabilisticExecution.distFairHyperKernel
      rw [dif_neg h]
    rw [h_def] at hμ
    exact pe'.distHyperKernel_step hE h_supp hs hμ

/-- **Marginal decomposition of `distFairHyperKernel`.** Integrating the fairness-revealing
per-state kernel `bind id` against the end-state distribution recovers `ω.bind id`: on the fair
branch this is the realizer bind-equality conjunct of `F.dist.fair`, on the else branch it is
`hyperStep_marginal_decomp`. -/
theorem ProbabilisticExecution.distFairHyperKernel_decomp {sys : System State Label}
    (F : Fairness sys) (pe' : ProbabilisticExecution 𝒟(sys)) :
    LowerKernelDecomp pe' (pe'.distFairHyperKernel F) := by
  classical
  intro E hE l ω h_supp q
  by_cases h : ∃ hE' : E.trans.Terminates, (F.dist).fair (E.endState hE') l ω
  · -- Fair branch: the kernel is the all-`F`-fair realizer `p := h.choose_spec.2.choose`.
    set p := h.choose_spec.2.choose with hp_def
    have hp_eq : ω.bind id = (E.endState h.choose).bind (fun s => (p s).bind id) :=
      h.choose_spec.2.choose_spec.2
    have h_def : pe'.distFairHyperKernel F E l ω = p := by
      unfold ProbabilisticExecution.distFairHyperKernel
      rw [dif_pos h]
    -- Reconcile the two `Terminates` proofs.
    have h_choose : h.choose = hE := Subsingleton.elim _ _
    rw [h_def, ← h_choose]
    conv_lhs => rw [hp_eq]
    rw [PMF.bind_apply]
  · -- Else branch: the kernel is `distHyperKernel`; use `hyperStep_marginal_decomp`.
    have h_def : pe'.distFairHyperKernel F E l ω = pe'.distHyperKernel E l ω := by
      unfold ProbabilisticExecution.distFairHyperKernel
      rw [dif_neg h]
    rw [h_def]
    exact pe'.hyperStep_marginal_decomp hE h_supp q

/-- **`g`-integrated marginal decomposition** (the "`μ` washes out when averaged over the belief"
fact). Integrating any `g : State → ENNReal` against the two sides of `distFairHyperKernel_decomp`
and summing shows that the belief-average (over `s ∈ E.endState`) of the `g`-integral of the
fairness-revealing per-state post-marginal recovers the `g`-integral of `ω.bind id`. This is the
endstate-marginal content of the joint-law disintegration: the concrete step's `μ`-dependence
integrates out over the end-belief, leaving only `ω.bind id`. Reusable at the append step of any
proof of `lowerFairR_average_step_washout` (the crux-A residual). -/
theorem ProbabilisticExecution.distFairHyperKernel_decomp_gsum {sys : System State Label}
    (F : Fairness sys) (pe' : ProbabilisticExecution 𝒟(sys))
    {E : AlterSeq (PMF State) Label} (hE : E.trans.Terminates)
    {l : Label} {ω : PMF (PMF State)}
    (h_supp : some (l, ω) ∈ (pe'.scheduler.next E).support) (g : State → ENNReal) :
    (∑' q : State, (ω.bind id) q * g q)
      = ∑' s : State, (E.endState hE) s
          * (∑' q : State, ((pe'.distFairHyperKernel F E l ω s).bind id) q * g q) := by
  have hdec := pe'.distFairHyperKernel_decomp F hE h_supp
  calc (∑' q : State, (ω.bind id) q * g q)
      = ∑' q : State, (∑' s : State, (E.endState hE) s
            * ((pe'.distFairHyperKernel F E l ω s).bind id) q) * g q := by
        exact tsum_congr (fun q => by rw [hdec q])
    _ = ∑' q : State, ∑' s : State, (E.endState hE) s
            * ((pe'.distFairHyperKernel F E l ω s).bind id) q * g q := by
        exact tsum_congr (fun q => by rw [ENNReal.tsum_mul_right])
    _ = ∑' s : State, ∑' q : State, (E.endState hE) s
            * ((pe'.distFairHyperKernel F E l ω s).bind id) q * g q := ENNReal.tsum_comm
    _ = ∑' s : State, (E.endState hE) s
            * (∑' q : State, ((pe'.distFairHyperKernel F E l ω s).bind id) q * g q) := by
        refine tsum_congr (fun s => ?_)
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr (fun q => mul_assoc _ _ _)

/-- **Fairness transfer through the fairness-revealing kernel.** If the belief-step `(l, ω)` is
`F.dist`-fair at the end-belief `E.endState`, then every concrete state `s` in that belief and every
concrete transition `μ` in the kernel's support from `s` is `F`-fair. This is the step that carries
`F.dist`-fairness of the abstract belief-run down to `F`-fairness of the concrete run in crux B
(the finite-branching route): on the fair branch `distFairHyperKernel` returns the all-`F`-fair
realiser `p` of `F.dist.fair`, whose support beliefs `μ` are `F.fair` by construction. -/
theorem ProbabilisticExecution.distFairHyperKernel_fair_transfer {sys : System State Label}
    (F : Fairness sys) (pe' : ProbabilisticExecution 𝒟(sys))
    (E : AlterSeq (PMF State) Label) (hE : E.trans.Terminates) (l : Label) (ω : PMF (PMF State))
    (hfair : F.dist.fair (E.endState hE) l ω)
    (s : State) (hs : s ∈ (E.endState hE).support)
    (μ : PMF State) (hμ : μ ∈ (pe'.distFairHyperKernel F E l ω s).support) :
    F.fair s l μ := by
  classical
  have h : ∃ hE' : E.trans.Terminates, F.dist.fair (E.endState hE') l ω := ⟨hE, hfair⟩
  have hker : pe'.distFairHyperKernel F E l ω s = h.choose_spec.2.choose s := by
    unfold ProbabilisticExecution.distFairHyperKernel; rw [dif_pos h]
  rw [hker] at hμ
  have hchoose : h.choose = hE := Subsingleton.elim _ _
  have hfair_p := h.choose_spec.2.choose_spec.1
  rw [hchoose] at hfair_p
  exact hfair_p s hs μ hμ

/-! ### The trace side: the coercion witness (`lowerCoe`)

`lowerCoe` realises `PE'`'s trace distribution as a resolved `sys`-execution, reusing the plain
reconstruction. It is **not** sure-fair (see the module docstring); it exists only to show the trace
half is free. -/

/-- The **coercion (trace) witness**: the plain trace-cone reconstruction `lower` of the forgetful
reading of `PE'.average`, coerced to a resolved execution. Realises `PE'`'s trace distribution but
is not sure-fair. -/
noncomputable def ResolvedProbabilisticExecution.lowerCoe {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F)) :
    ResolvedProbabilisticExecution sys :=
  (((PE'.average).distFToDist F).lower).toResolved

/-- The coercion witness realises `PE'`'s trace distribution — the trace half of the superset, free
via `traceProbR_toResolved`, `lower_traceProb_eq`, `distFToDist_traceProb`, `traceProb_average`. -/
theorem ResolvedProbabilisticExecution.lowerCoe_traceProbR {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F)) (τ : Seq Label) :
    (PE'.lowerCoe F).traceProbR τ = PE'.traceProbR τ := by
  rw [ResolvedProbabilisticExecution.lowerCoe,
    ProbabilisticExecution.traceProbR_toResolved,
    ProbabilisticExecution.lower_traceProb_eq,
    ← ProbabilisticExecution.distFToDist_traceProb, PE'.traceProb_average τ]

/-- The coercion witness starts from the Dirac initial distribution `pure sys.init`. -/
theorem ResolvedProbabilisticExecution.lowerCoe_initState {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (hinit : PE'.initState = PMF.pure (sys.distF F).init) :
    (PE'.lowerCoe F).initState = PMF.pure sys.init := by
  change PE'.initState.bind id = PMF.pure sys.init
  rw [hinit, PMF.pure_bind]
  rfl

/-! ### Fair-enabledness of a resolvable belief -/

/-- If a belief `ν` has a **common fair label** `l` (every state in its support fair-enables `l`),
then `ν` is `F.dist`-fair-enabled: the belief-step to `(ν.bind μ).map PMF.pure` — clustering the
common per-state fair kernel `μ` down to Diracs — is `F.dist`-fair. -/
theorem Fairness.commonFairLabel_distFairEnabled {sys : System State Label} (F : Fairness sys)
    {ν : PMF State} (h : F.CommonFairLabel ν) : (F.dist).FairEnabled ν := by
  classical
  obtain ⟨l, hl⟩ := h
  choose! μ hμ using hl
  -- The flattened target `ν.bind μ`, clustered to Diracs and then flattened back, is `ν.bind μ`.
  have hkey : ((ν.bind μ).map PMF.pure).bind id = ν.bind μ := by
    rw [PMF.bind_map]; exact PMF.bind_pure (ν.bind μ)
  -- The witness step, kernel and per-state fair kernel `p := fun s => PMF.pure (μ s)`.
  refine ⟨l, (ν.bind μ).map PMF.pure, ⟨⟨fun s => PMF.pure (μ s), ?_, ?_⟩, ?_⟩,
    fun s => PMF.pure (μ s), ?_, ?_⟩
  · -- `hyperStep` validity: `μ' = μ s`, and `sys.step s l (μ s)` from fairness.
    intro s hs μ' hμ'
    rw [PMF.mem_support_pure_iff] at hμ'
    subst hμ'
    exact F.step_of_fair s l (μ s) (hμ s hs)
  · -- `hyperStep` post-equality: `PMF.pure (μ s)).bind id = μ s`, then `hkey`.
    rw [hkey]
    simp only [PMF.pure_bind, Function.id_def]
  · -- Every successor belief is a Dirac, hence resolvable.
    intro ν' hν'
    rw [PMF.mem_support_map_iff] at hν'
    obtain ⟨t, _, rfl⟩ := hν'
    exact F.resolvable_pure t
  · -- The all-fair conjunct of `Fairness.dist.fair`: `μ' = μ s`, fair from `hμ`.
    intro s hs μ' hμ'
    rw [PMF.mem_support_pure_iff] at hμ'
    subst hμ'
    exact hμ s hs
  · -- The bind-equality conjunct: same clustering computation as the `hyperStep` post-equality.
    rw [hkey]
    simp only [PMF.pure_bind, Function.id_def]

/-- If a resolvable belief `ν` is a `F.dist`-fair-deadlock, every state in `ν.support` is an
`F`-fair-deadlock. Resolvability forces the dichotomy: a common fair label would make `ν`
`F.dist`-fair-enabled (`commonFairLabel_distFairEnabled`), contradicting the deadlock; so `ν`
must be a genuine (all-states) fair deadlock, which is exactly the goal. -/
theorem Fairness.distF_fairDeadlock_belief {sys : System State Label} (F : Fairness sys)
    {ν : PMF State} (hres : F.Resolvable ν) (hdl : (F.dist).FairDeadlock ν) :
    ∀ s ∈ ν.support, F.FairDeadlock s := by
  rcases hres with hcfl | hafd
  · exact absurd (F.commonFairLabel_distFairEnabled hcfl) hdl
  · exact hafd

/-! ### Resolved belief-trace-cone (the time-local rebuild of the coherence)

The plain `beliefTC` filter is de-resolved (reads `PE'.average`), non-time-local (its kernel's
fair-branch is at the single final belief), and non-prefix-nesting — so it cannot supply the
time-local *resolved* coherent lift the fairness crux needs
(`exists_timeLocal_coherent_resolved_lift`). The rebuild replaces it with a **resolved** trace-cone
`beliefTCR` — a posterior over resolved `PE'`-runs `R'` (which record the emitted `ω`'s and every
intermediate belief `R'.stateAt m`), pushing forward to the plain `beliefTC` along `toExec` (their
normalizers coincide by `probOf_average` / `avgWeight`). Sampling a resolved `R'` and reading its
recorded step `m` at the time-`m` belief `(R'.take m).toExec.endState` makes coherence time-local,
resolved, and prefix-local — exactly what König + `distFairHyperKernel_fair_transfer` consume. -/

/-- Unnormalized resolved belief-trace-cone weight: resolved `PE'`-runs `R'` whose plain projection
`toExec R'` carries label-list `labs`, weighted by `probOfR PE' R'` times the end-belief mass at
`s`. Summed over the `toExec`-fibre it reproduces `beliefTCw` (`beliefTCRw_tsum_eq`). -/
noncomputable def ResolvedProbabilisticExecution.beliefTCRw {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (labs : List Label) (s : State) (R' : ResolvedExec (PMF State) Label) : ENNReal :=
  open Classical in
  if h : R'.trans.Terminates ∧ (ResolvedExec.toExec R').trans.map Prod.fst = Seq.ofList labs then
    PE'.probOfR R' h.1
      * ((ResolvedExec.toExec R').endState ((ResolvedExec.toExec_terminates_iff R').mpr h.1)) s
  else 0

/-- **The workhorse fibre identity.** Summing the unnormalised resolved weight `beliefTCRw` over the
`toExec`-fibre reproduces the plain unnormalised weight `beliefTCw` of the forgetful average
`PE'.average.distFToDist F`. Each resolved run `R'` is grouped under its plain image `E = toExec R'`
— inside a fibre the guard and end-belief depend only on `E`, so the `probOfR`-fibre-sum collapses
to `avgWeight E = (PE'.average.distFToDist F).probOf E` (`probOf_average`). -/
theorem ResolvedProbabilisticExecution.beliefTCRw_tsum_eq {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (labs : List Label) (s : State) :
    (∑' R', PE'.beliefTCRw F labs s R')
      = ∑' E, (PE'.average.distFToDist F).beliefTCw labs s E := by
  classical
  -- Reindex the `R'`-sum as a sigma over `E` and its `toExec`-fibre.
  have hsig : (∑' R', PE'.beliefTCRw F labs s R')
      = ∑' p : Σ E : AlterSeq (PMF State) Label, {R' : ResolvedExec (PMF State) Label //
          ResolvedExec.toExec R' = E}, PE'.beliefTCRw F labs s p.2.1 := by
    refine tsum_eq_tsum_of_ne_zero_bij (fun p => p.1.2.1) ?_ ?_ ?_
    · intro a b h
      -- `h : a.1.2.1 = b.1.2.1`; the `E`s agree since each is the `toExec` of its run.
      have hfst : a.1.1 = b.1.1 := by rw [← a.1.2.2, ← b.1.2.2]; exact congrArg _ h
      exact Subtype.ext (Sigma.subtype_ext hfst h)
    · intro R' hR'
      exact ⟨⟨⟨ResolvedExec.toExec R', R', rfl⟩, hR'⟩, rfl⟩
    · intro p; rfl
  rw [hsig, ENNReal.tsum_sigma']
  refine tsum_congr (fun E => ?_)
  -- Fibre sum at `E`.
  by_cases hg : E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs
  · -- Guard holds: each fibre summand is `probOfR R' · (E.endState) s`; sum = avgWeight · mass.
    have hbw : (PE'.average.distFToDist F).beliefTCw labs s E
        = PE'.avgWeight E hg.1 * (E.endState hg.1) s := by
      unfold ProbabilisticExecution.beliefTCw
      rw [dif_pos hg]
      congr 1
      change (PE'.average.probOf E hg.1) = PE'.avgWeight E hg.1
      exact PE'.probOf_average E hg.1
    rw [hbw]
    -- Rewrite each fibre summand to `probOfR b.1 · (E.endState hg.1) s`.
    have hsummand : ∀ b : {R' : ResolvedExec (PMF State) Label // ResolvedExec.toExec R' = E},
        PE'.beliefTCRw F labs s (⟨E, b⟩ : Σ E, _).snd.1
          = PE'.probOfR b.1 (ResolvedExec.terminates_of_toExec_eq hg.1 b.2)
            * (E.endState hg.1) s := by
      intro b
      obtain ⟨R', hR'⟩ := b
      -- Substitute `E = toExec R'` so both `endState`s are literally `(toExec R').endState`.
      subst hR'
      have hg' : R'.trans.Terminates ∧
          (ResolvedExec.toExec R').trans.map Prod.fst = Seq.ofList labs :=
        ⟨(ResolvedExec.toExec_terminates_iff R').mp hg.1, hg.2⟩
      unfold ResolvedProbabilisticExecution.beliefTCRw
      rw [dif_pos hg']
    rw [tsum_congr hsummand, ENNReal.tsum_mul_right]
    congr 1
  · -- Guard fails: both sides are `0`.
    have hbw : (PE'.average.distFToDist F).beliefTCw labs s E = 0 := by
      unfold ProbabilisticExecution.beliefTCw; rw [dif_neg hg]
    rw [hbw]
    refine ENNReal.tsum_eq_zero.mpr (fun R' => ?_)
    unfold ResolvedProbabilisticExecution.beliefTCRw
    rw [dif_neg]
    rintro ⟨hT, hlab⟩
    refine hg ⟨R'.2 ▸ (ResolvedExec.toExec_terminates_iff R'.1).mpr hT, ?_⟩
    rw [← R'.2]; exact hlab

open Classical in
/-- **Per-`E` fibre form** (the `PMF.map`-shaped variant of `beliefTCRw_tsum_eq`): the `beliefTCRw`
mass of the `toExec`-fibre over a *fixed* plain history `E₀` equals the plain `beliefTCw` weight at
`E₀`. This is exactly the pushforward `((·).map toExec)`-summand `∑' R', [E₀ = toExec R'] w R'`. -/
theorem ResolvedProbabilisticExecution.beliefTCRw_fibre_eq {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (labs : List Label) (s : State) (E₀ : AlterSeq (PMF State) Label) :
    (∑' R', (if E₀ = ResolvedExec.toExec R' then PE'.beliefTCRw F labs s R' else 0))
      = (PE'.average.distFToDist F).beliefTCw labs s E₀ := by
  classical
  by_cases hg : E₀.trans.Terminates ∧ E₀.trans.map Prod.fst = Seq.ofList labs
  · -- Guard holds: reindex to the fibre and collapse to `avgWeight · endState-mass`.
    have hbw : (PE'.average.distFToDist F).beliefTCw labs s E₀
        = PE'.avgWeight E₀ hg.1 * (E₀.endState hg.1) s := by
      unfold ProbabilisticExecution.beliefTCw
      rw [dif_pos hg]
      change (PE'.average.probOf E₀ hg.1) * _ = _
      rw [PE'.probOf_average E₀ hg.1]
    rw [hbw]
    -- Reindex the indicator sum onto the fibre `{R' // toExec R' = E₀}`.
    rw [show PE'.avgWeight E₀ hg.1 * (E₀.endState hg.1) s
          = ∑' p : {R' : ResolvedExec (PMF State) Label // ResolvedExec.toExec R' = E₀},
              PE'.probOfR p.1 (ResolvedExec.terminates_of_toExec_eq hg.1 p.2)
                * (E₀.endState hg.1) s from by
        unfold ResolvedProbabilisticExecution.avgWeight; rw [ENNReal.tsum_mul_right]]
    -- Per-fibre-element: the indicator summand at `p.1.1` equals `probOfR · endState-mass`.
    have hfib : ∀ p : {R' : ResolvedExec (PMF State) Label // ResolvedExec.toExec R' = E₀},
        (if E₀ = ResolvedExec.toExec p.1 then PE'.beliefTCRw F labs s p.1 else 0)
          = PE'.probOfR p.1 (ResolvedExec.terminates_of_toExec_eq hg.1 p.2)
              * (E₀.endState hg.1) s := by
      rintro ⟨R', hR'⟩
      subst hR'
      rw [if_pos rfl]
      unfold ResolvedProbabilisticExecution.beliefTCRw
      rw [dif_pos (⟨(ResolvedExec.toExec_terminates_iff R').mp hg.1, hg.2⟩ :
        R'.trans.Terminates ∧ (ResolvedExec.toExec R').trans.map Prod.fst = Seq.ofList labs)]
    refine tsum_eq_tsum_of_ne_zero_bij (fun p => p.1.1) ?_ ?_ ?_
    · intro a b h; exact Subtype.ext (Subtype.ext h)
    · -- support of the indicator sits in the range: a positive indicator forces `toExec R' = E₀`.
      intro R' hR'
      rw [Function.mem_support] at hR'
      have hmatch : E₀ = ResolvedExec.toExec R' := by
        by_contra hne; exact hR' (if_neg hne)
      refine ⟨⟨⟨R', hmatch.symm⟩, ?_⟩, rfl⟩
      rw [Function.mem_support, ← hfib ⟨R', hmatch.symm⟩]
      exact hR'
    · intro p; exact hfib p.1
  · -- Guard fails: both sides vanish.
    have hbw : (PE'.average.distFToDist F).beliefTCw labs s E₀ = 0 := by
      unfold ProbabilisticExecution.beliefTCw; rw [dif_neg hg]
    rw [hbw]
    refine ENNReal.tsum_eq_zero.mpr (fun R' => ?_)
    by_cases hmatch : E₀ = ResolvedExec.toExec R'
    · rw [if_pos hmatch]
      unfold ResolvedProbabilisticExecution.beliefTCRw
      rw [dif_neg]
      rintro ⟨hT, hlab⟩
      exact hg ⟨hmatch ▸ (ResolvedExec.toExec_terminates_iff R').mpr hT, by rw [hmatch]; exact hlab⟩
    · rw [if_neg hmatch]

/-- The **resolved belief-trace-cone**: normalize `beliefTCRw`; fallback to the length-0 run at the
Dirac belief `pure s`. Resolved analogue of `beliefTC`; `beliefTCR_map_toExec` shows it pushes
forward to `beliefTC` along `toExec`. -/
noncomputable def ResolvedProbabilisticExecution.beliefTCR {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (labs : List Label) (s : State) : PMF (ResolvedExec (PMF State) Label) :=
  open Classical in
  if h0 : (∑' R', PE'.beliefTCRw F labs s R') ≠ 0 then
    PMF.normalize (PE'.beliefTCRw F labs s) h0
      (by rw [PE'.beliefTCRw_tsum_eq F labs s]
          exact (PE'.average.distFToDist F).beliefTCw_tsum_ne_top labs s)
  else
    PMF.pure ⟨PMF.pure s, Seq.nil⟩

/-- **`beliefTCR` pushes forward to the plain `beliefTC` along `toExec`.** The resolved trace-cone,
after forgetting the recorded `μ`s, is exactly the plain trace-cone of the forgetful average. Both
sides normalise the same total mass (`beliefTCRw_tsum_eq`), so their fallback guards agree; the
normalise branch matches pointwise via the fibre identity (`beliefTCRw_fibre_eq`), and the fallback
branch is the pushforward of the length-0 run `⟨pure s, nil⟩` (fixed by `toExec`). -/
theorem ResolvedProbabilisticExecution.beliefTCR_map_toExec {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (labs : List Label) (s : State) :
    (PE'.beliefTCR F labs s).map ResolvedExec.toExec
      = (PE'.average.distFToDist F).beliefTC labs s := by
  classical
  unfold ResolvedProbabilisticExecution.beliefTCR ProbabilisticExecution.beliefTC
  -- The two normalisers agree by the workhorse identity, so the guards agree.
  have hZ : (∑' R', PE'.beliefTCRw F labs s R')
      = ∑' E, (PE'.average.distFToDist F).beliefTCw labs s E := PE'.beliefTCRw_tsum_eq F labs s
  by_cases h0 : (∑' R', PE'.beliefTCRw F labs s R') ≠ 0
  · -- Both normalise. Compare pointwise.
    rw [dif_pos h0, dif_pos (hZ ▸ h0)]
    refine PMF.ext (fun E₀ => ?_)
    rw [PMF.map_apply, PMF.normalize_apply]
    -- Rewrite each `normalize`-summand and pull the `Z⁻¹` out of the fibre sum.
    rw [show (∑' R', if E₀ = ResolvedExec.toExec R'
            then (PMF.normalize (PE'.beliefTCRw F labs s) h0
                (by rw [hZ]; exact (PE'.average.distFToDist F).beliefTCw_tsum_ne_top labs s)) R'
            else 0)
          = (∑' R', if E₀ = ResolvedExec.toExec R' then PE'.beliefTCRw F labs s R' else 0)
              * (∑' x, PE'.beliefTCRw F labs s x)⁻¹ from by
        rw [← ENNReal.tsum_mul_right]; refine tsum_congr (fun R' => ?_)
        rw [PMF.normalize_apply]
        by_cases hm : E₀ = ResolvedExec.toExec R' <;> simp [hm]]
    rw [PE'.beliefTCRw_fibre_eq F labs s E₀, hZ]
  · -- Both fallback: pushforward of the length-0 run.
    rw [not_not] at h0
    rw [dif_neg (by rw [h0]; simp), dif_neg (by rw [← hZ, h0]; simp)]
    rw [PMF.pure_map]
    congr 1

/-- **Support characterisation of `beliefTCR`** (under positive cone mass). A resolved run `R'` in
`beliefTCR`'s support terminates, its `toExec`-projection carries the label list `labs`, its
end-belief has `s` in its support, and it has positive resolved probability. The positive-cone-mass
hypothesis `hpos` excludes the length-0 fallback run (whose label list is `[]`, breaking the label
clause when `labs ≠ []`, and whose `probOfR` may vanish); the consumer always has positive cone
mass, so requiring `hpos` is exactly right. -/
theorem ResolvedProbabilisticExecution.beliefTCR_support {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (labs : List Label) (s : State) (hpos : (∑' R', PE'.beliefTCRw F labs s R') ≠ 0)
    (R' : ResolvedExec (PMF State) Label) (hR' : R' ∈ (PE'.beliefTCR F labs s).support) :
    ∃ hT : R'.trans.Terminates,
      (ResolvedExec.toExec R').trans.map Prod.fst = Seq.ofList labs ∧
      s ∈ ((ResolvedExec.toExec R').endState
        ((ResolvedExec.toExec_terminates_iff R').mpr hT)).support ∧
      PE'.probOfR R' hT ≠ 0 := by
  classical
  -- The positive cone mass forces the normalise branch of `beliefTCR`.
  rw [ResolvedProbabilisticExecution.beliefTCR, dif_pos hpos,
    PMF.mem_support_normalize_iff] at hR'
  -- Unfold the weight and split on its guard.
  unfold ResolvedProbabilisticExecution.beliefTCRw at hR'
  split_ifs at hR' with hg
  · obtain ⟨hT, hlab⟩ := hg
    refine ⟨hT, hlab, ?_, ?_⟩
    · -- `s ∈ (endState).support` from `(endState) s ≠ 0`.
      rw [PMF.mem_support_iff]
      intro hzero
      rw [hzero, mul_zero] at hR'
      exact hR' rfl
    · -- `probOfR R' hT ≠ 0` from the product being nonzero.
      intro hzero
      rw [hzero, zero_mul] at hR'
      exact hR' rfl
  · exact absurd rfl hR'

/-- **Time-local resolved coherence.** A concrete run `r` is coherent with a resolved
`PE'`-belief-run `R'` when, at every recorded position `n`, `r`'s step `((l,μ),s')` is matched by
`R'`'s belief-step `((l,ω),ν')` at the same label, with `r`'s state `s` in the time-`n` belief
`R'.stateAt n` and `μ` realised by the fairness-revealing kernel at the **time-`n`** belief-history
`(R'.take n).toExec`.
Unlike the old μ-blind coherence filter, this is resolved (reads `R'`'s recorded `ω`'s), time-local
(kernel at the per-step belief, not the final one), and prefix-local (position `n` reads only
`R'.take n`). -/
def ResolvedProbabilisticExecution.RCoherentTL {sys : System State Label} (F : Fairness sys)
    (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (r : ResolvedExec State Label) (R' : ResolvedExec (PMF State) Label) : Prop :=
  ∀ (n : ℕ) (s : State) (l : Label) (μ : PMF State) (s' : State),
    r.stateAt n = some s → r.trans.get? n = some ((l, μ), s') →
      ∃ (ν : PMF State) (ω : PMF (PMF State)) (ν' : PMF State),
        R'.stateAt n = some ν ∧ R'.trans.get? n = some ((l, ω), ν') ∧
        s ∈ ν.support ∧
        μ ∈ ((PE'.average.distFToDist F).distFairHyperKernel F
              (ResolvedExec.toExec (R'.take n)) l ω s).support

/-- The **μ-reading resolved witness scheduler.** Mirrors `Scheduler.lower`
(`Construction/DistTrace.lean`) on the forgetful reading `PE'.average.distFToDist F`, but the
resolved belief-run `R'` is sampled from the resolved trace-cone `beliefTCR` *restricted* to those
`R'` time-locally coherent with the full resolved history `r` (`RCoherentTL`), so it reads the
recorded `μ`s. The emission uses the fairness-revealing kernel `distFairHyperKernel` on the plain
projection `R'.toExec`. When the restricted mass is `0` (the `μ`-pattern is unrealisable) it halts
(`PMF.pure none`).

`valid` mirrors `Scheduler.lower`'s: the coherence restriction only shrinks the resolved
belief-support, so `beliefTCR_support` still supplies `s ∈ (R'.toExec.endState).support` and
validity reduces to `distFairHyperKernel_valid`. -/
noncomputable def ResolvedProbabilisticExecution.lowerFairRSched {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F)) :
    ResolvedScheduler sys where
  next r :=
    open Classical in
    if h_term : r.toExec.trans.Terminates then
      if h0 : (∑' R', Set.indicator {R' | PE'.RCoherentTL F r R'}
          (PE'.beliefTCR F ((r.toExec.trans.toList h_term).map Prod.fst)
            (r.toExec.endState h_term)) R') ≠ 0 then
        ((PE'.beliefTCR F ((r.toExec.trans.toList h_term).map Prod.fst)
            (r.toExec.endState h_term)).filter {R' | PE'.RCoherentTL F r R'}
          (by
            obtain ⟨R', hR'⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr h0)
            obtain ⟨hmem, hsupp⟩ := Set.indicator_apply_ne_zero.mp hR'
            exact ⟨R', hmem, hsupp⟩)).bind (fun R' =>
          ((PE'.average.distFToDist F).scheduler.next (ResolvedExec.toExec R')).bind (fun opt =>
            match opt with
            | none         => PMF.pure none
            | some (l, ω)  =>
              ((PE'.average.distFToDist F).distFairHyperKernel F (ResolvedExec.toExec R') l ω
                  (r.toExec.endState h_term)).map (fun μ' => some (l, μ'))))
      else PMF.pure none
    else PMF.pure none
  valid := by
    classical
    intro r n s r_term_n r_stateAt_eq l μ h_supp
    have h_term_e : r.toExec.trans.Terminates :=
      (ResolvedExec.toExec_terminates_iff r).mpr ⟨n, r_term_n⟩
    have h_term : r.trans.Terminates := ⟨n, r_term_n⟩
    -- Reduce `r.stateAt`/`r.trans.TerminatedAt` to `r.toExec`'s, then reuse the `lower` shape.
    have e_term_n : r.toExec.trans.TerminatedAt n :=
      (ResolvedExec.toExec_terminatedAt_iff r n).mpr r_term_n
    have e_stateAt_eq : r.toExec.stateAt n = some s := by
      rw [ResolvedExec.toExec_stateAt]; exact r_stateAt_eq
    have h_find_le : Nat.find h_term_e ≤ n := Nat.find_le e_term_n
    have h_n_le : n ≤ Nat.find h_term_e := by
      by_contra h_lt
      push Not at h_lt
      rcases n with _ | k
      · exact absurd h_lt (Nat.not_lt_zero _)
      · have hk_ge : Nat.find h_term_e ≤ k := Nat.lt_succ_iff.mp h_lt
        have h_term_k : r.toExec.trans.TerminatedAt k :=
          Stream'.Seq.terminated_stable r.toExec.trans hk_ge (Nat.find_spec h_term_e)
        have h_state_none : r.toExec.stateAt (k + 1) = none := by
          change (r.toExec.trans.get? k).map Prod.snd = none
          rw [show r.toExec.trans.get? k = none from h_term_k]
          rfl
        rw [h_state_none] at e_stateAt_eq
        exact Option.some_ne_none s e_stateAt_eq.symm
    have h_n_eq : n = Nat.find h_term_e := le_antisymm h_n_le h_find_le
    have h_s_eq : s = r.toExec.endState h_term_e := by
      have h := AlterSeq.stateAt_find_eq_endState r.toExec h_term_e
      rw [← h_n_eq] at h
      rw [h] at e_stateAt_eq
      exact (Option.some.inj e_stateAt_eq).symm
    subst h_s_eq
    set pe' := PE'.average.distFToDist F with hpe'
    set labs := (r.toExec.trans.toList h_term_e).map Prod.fst with hlabs
    set s₀ := r.toExec.endState h_term_e with hs₀
    -- Unfold the emission; the coherence filter only shrinks `beliefTCR`'s support.
    change some (l, μ) ∈
      (open Classical in
        if h_term' : r.toExec.trans.Terminates then
          if h0 : (∑' R', Set.indicator {R' | PE'.RCoherentTL F r R'}
              (PE'.beliefTCR F ((r.toExec.trans.toList h_term').map Prod.fst)
                (r.toExec.endState h_term')) R') ≠ 0 then
            ((PE'.beliefTCR F ((r.toExec.trans.toList h_term').map Prod.fst)
                (r.toExec.endState h_term')).filter {R' | PE'.RCoherentTL F r R'} _).bind (fun R' =>
              (pe'.scheduler.next (ResolvedExec.toExec R')).bind (fun opt =>
                match opt with
                | none         => PMF.pure none
                | some (l', ω) =>
                  (pe'.distFairHyperKernel F (ResolvedExec.toExec R') l' ω
                      (r.toExec.endState h_term')).map (fun μ' => some (l', μ'))))
          else PMF.pure none
        else PMF.pure none).support at h_supp
    rw [dif_pos h_term_e] at h_supp
    split_ifs at h_supp with h0
    · rw [PMF.mem_support_bind_iff] at h_supp
      obtain ⟨R', hR'_belief, h_supp⟩ := h_supp
      rw [PMF.mem_support_filter_iff] at hR'_belief
      obtain ⟨-, hR'_belief⟩ := hR'_belief
      rw [PMF.mem_support_bind_iff] at h_supp
      obtain ⟨opt, hopt_sch, h_supp⟩ := h_supp
      set E := ResolvedExec.toExec R' with hE
      -- Recover `E.Terminates` and `s₀ ∈ E.endState.support`, either from `beliefTCR_support`
      -- (positive cone mass) or from the length-0 fallback run `⟨pure s₀, nil⟩`.
      obtain ⟨hE_term, h_endState⟩ :
          ∃ hE_term : E.trans.Terminates, s₀ ∈ (E.endState hE_term).support := by
        by_cases hpos : (∑' R'', PE'.beliefTCRw F labs s₀ R'') ≠ 0
        · obtain ⟨hT, -, h_mem, -⟩ := PE'.beliefTCR_support F labs s₀ hpos R' hR'_belief
          exact ⟨(ResolvedExec.toExec_terminates_iff R').mpr hT, h_mem⟩
        · -- Fallback: `beliefTCR` is `pure ⟨pure s₀, nil⟩`, so `R' = ⟨pure s₀, nil⟩`.
          rw [not_not] at hpos
          rw [ResolvedProbabilisticExecution.beliefTCR, dif_neg (by rw [hpos]; simp),
            PMF.mem_support_pure_iff] at hR'_belief
          subst hR'_belief
          have hE_nil : E.trans = Seq.nil := by rw [hE]; rfl
          refine ⟨hE_nil ▸ Stream'.Seq.terminates_nil, ?_⟩
          have hend : E.endState (hE_nil ▸ Stream'.Seq.terminates_nil) = PMF.pure s₀ := by
            rw [AlterSeq.endState_of_trans_nil E hE_nil]; rw [hE]; rfl
          rw [hend, PMF.support_pure, Set.mem_singleton_iff]
      cases opt with
      | none =>
        change some (l, μ) ∈ (PMF.pure (α := Option (Label × PMF State)) none).support at h_supp
        rw [PMF.support_pure, Set.mem_singleton_iff] at h_supp
        exact absurd h_supp (by simp)
      | some lω =>
        obtain ⟨l', ω⟩ := lω
        change some (l, μ) ∈ ((pe'.distFairHyperKernel F E l' ω s₀).map
          (fun μ' => some (l', μ'))).support at h_supp
        rw [PMF.mem_support_map_iff] at h_supp
        obtain ⟨μ', h_μ'_kernel, h_eq⟩ := h_supp
        simp only [Option.some.injEq, Prod.mk.injEq] at h_eq
        obtain ⟨rfl, rfl⟩ := h_eq
        exact pe'.distFairHyperKernel_valid F hE_term hopt_sch h_endState h_μ'_kernel
    · change some (l, μ) ∈ (PMF.pure (α := Option (Label × PMF State)) none).support at h_supp
      rw [PMF.support_pure, Set.mem_singleton_iff] at h_supp
      exact absurd h_supp (by simp)

/-- The **μ-reading resolved witness execution**: initial distribution `PE'.initState.bind id`
(a Dirac on `sys.init` under the `fairAchievableTraceDists` requirement), with scheduler
`lowerFairRSched`. Reads the recorded `μ`s (via the `RCoherentTL` filter), killing the naive
chimeras that `lowerCoe` admits. -/
noncomputable def ResolvedProbabilisticExecution.lowerFairR {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F)) :
    ResolvedProbabilisticExecution sys :=
  ⟨PE'.initState.bind id, PE'.lowerFairRSched F⟩

/-- The μ-reading witness starts from the Dirac initial distribution `pure sys.init` (same one-line
proof as `lowerCoe_initState`: `initState = PE'.initState.bind id`, then `hinit`,
`PMF.pure_bind`). -/
theorem ResolvedProbabilisticExecution.lowerFairR_initState {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (hinit : PE'.initState = PMF.pure (sys.distF F).init) :
    (PE'.lowerFairR F).initState = PMF.pure sys.init := by
  change PE'.initState.bind id = PMF.pure sys.init
  rw [hinit, PMF.pure_bind]
  rfl

/-! ### Prefix machinery and resolved liftability

The `take_*` helpers below are local copies of the finite-prefix lemmas (`take_terminates`,
`take_stateAt`, `take_endState`, …) used by the fairness cruxes downstream; `Simulation/Fair/`
carries the analogous copies for its own resolved objects. `exists_positive_resolved_of_probOf`
lifts a positive plain belief-history `E` of `PE'.average` to a positive-path-mass resolved
`PE'`-run `R'` with `toExec R' = E` (via `probOf E = avgWeight E = ∑ probOfR` over the fibre); it is
König's `hchain` premise for crux B. Support-level and `[Fintype State]`-free. -/

/-- `Seq.take n s` reads back `s.get?` below `n` (local copy; the analogue in
`Simulation/Fair/Soundness.lean` lives downstream of this file). -/
private theorem seq_getElem?_take {α : Type} (s : Seq α) (n m : ℕ) (h : m < n) :
    (Seq.take n s)[m]? = s.get? m := by
  induction n generalizing s m with
  | zero => omega
  | succ k ih =>
    induction s using Stream'.Seq.recOn with
    | nil => simp [Stream'.Seq.take_nil, Stream'.Seq.get?_nil]
    | cons a t =>
      rw [Stream'.Seq.take_succ_cons]
      cases m with
      | zero => simp [Stream'.Seq.get?_cons_zero]
      | succ j =>
        rw [List.getElem?_cons_succ, Stream'.Seq.get?_cons_succ]
        exact ih t j (Nat.lt_of_succ_lt_succ h)

/-- The finite prefix `r.take n` records the same transitions as `r` below `n` (local copy of the
analogue in `Simulation/Fair/Soundness.lean`, which is downstream of this file). -/
private theorem take_trans_get? {S L : Type} (r : AlterSeq S L) {n m : ℕ} (h : m < n) :
    (r.take n).trans.get? m = r.trans.get? m := by
  change (Seq.ofList (Seq.take n r.trans)).get? m = _
  rw [Stream'.Seq.ofList_get?, seq_getElem?_take r.trans n m h]

/-- The length-`n` prefix always terminates (it is a finite list). -/
private theorem take_terminates {S L : Type} (r : AlterSeq S L) (n : ℕ) :
    (r.take n).trans.Terminates :=
  Stream'.Seq.terminates_ofList _

/-- For an infinite `r`, the length-`n` prefix terminates exactly at `n`. -/
private theorem take_terminatedAt {S L : Type} (r : AlterSeq S L) (n : ℕ)
    (hinf : ¬ r.trans.Terminates) : (r.take n).trans.TerminatedAt n := by
  change (Seq.ofList (Seq.take n r.trans)).get? n = none
  rw [Stream'.Seq.ofList_get?]
  apply List.getElem?_eq_none
  have hlen : (Seq.take n r.trans).length = n :=
    Stream'.Seq.length_take_of_le_length (fun h => absurd h hinf)
  omega

/-- For an infinite `r`, the canonical terminating index of `r.take n` is `n`. -/
private theorem take_find {S L : Type} (r : AlterSeq S L) (n : ℕ)
    (hinf : ¬ r.trans.Terminates) : Nat.find (take_terminates r n) = n := by
  apply le_antisymm
  · exact Nat.find_le (take_terminatedAt r n hinf)
  · rw [Nat.le_find_iff]
    intro m hm
    change ¬ (Seq.ofList (Seq.take n r.trans)).get? m = none
    rw [Stream'.Seq.ofList_get?, seq_getElem?_take r.trans n m hm]
    exact fun hc => hinf ⟨m, hc⟩

/-- `r.take n` reads the same state as `r` at positions `≤ n`. -/
private theorem take_stateAt {S L : Type} (r : AlterSeq S L) {n m : ℕ} (hm : m ≤ n) :
    (r.take n).stateAt m = r.stateAt m := by
  cases m with
  | zero => rfl
  | succ k =>
    change ((r.take n).trans.get? k).map Prod.snd = (r.trans.get? k).map Prod.snd
    rw [take_trans_get? r (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hm)]

/-- For an infinite `r`, the end-state of the length-`n` prefix is `r.stateAt n`. -/
private theorem take_endState {S L : Type} (r : AlterSeq S L) (n : ℕ)
    (hinf : ¬ r.trans.Terminates) {s : S} (hs : r.stateAt n = some s) :
    (r.take n).endState (take_terminates r n) = s := by
  have hfind := take_find r n hinf
  have heq := AlterSeq.stateAt_find_eq_endState (r.take n) (take_terminates r n)
  rw [hfind, take_stateAt r (Nat.le_refl n), hs] at heq
  exact (Option.some.inj heq).symm

/-! ### Consistency ↔ positivity bridge helpers (local copies from `Simulation/Fair/Soundness.lean`)

`DistFairLower` is downstream of `Simulation/Fair/Soundness.lean` in the module graph (it is not
importable from here), so the generic consistency/`probOfR` bridge lemmas are duplicated here as
`private`. This is a temporary duplication used by the finite-branching König lift
(`exists_timeLocal_coherent_resolved_lift`). -/

omit [Silent Label] in
/-- **Bridge:** the length-`(prev.toList).length` prefix of a resolved history whose `trans` splits
as `prev.append (cons last nil)` is exactly `⟨r.init, prev⟩` (local copy). -/
private theorem take_prev_of_split {S : Type}
    (r : ResolvedExec S Label)
    (prev : Seq ((Label × PMF S) × S)) (last : (Label × PMF S) × S)
    (hprev : prev.Terminates) (hsplit : r.trans = prev.append (Seq.cons last Seq.nil)) :
    r.take (prev.toList hprev).length = ⟨r.init, prev⟩ := by
  unfold AlterSeq.take
  simp only [AlterSeq.mk.injEq, true_and]
  have hkey : Stream'.Seq.take (prev.toList hprev).length r.trans = prev.toList hprev := by
    apply List.ext_getElem?
    intro k
    rw [Stream'.Seq.getElem?_take, Stream'.Seq.getElem?_toList]
    by_cases hk : k < (prev.toList hprev).length
    · rw [if_pos hk, hsplit, Stream'.Seq.length_toList] at *
      have hnt : ¬ prev.TerminatedAt k :=
        fun ht => absurd (Stream'.Seq.length_le_iff.mpr ht) (not_le.mpr hk)
      exact Stream'.Seq.get?_append_before_length hnt
    · rw [if_neg hk, Stream'.Seq.length_toList] at *
      exact (Stream'.Seq.length_le_iff.mp (Nat.le_of_not_lt hk)).symm
  rw [hkey, Stream'.Seq.ofList_toList]

omit [Silent Label] in
/-- **Bridge:** the transition at position `(prev.toList).length` of a history that splits as
`prev.append (cons last nil)` is `last` (local copy). -/
private theorem get?_last_of_split {S : Type}
    (r : ResolvedExec S Label)
    (prev : Seq ((Label × PMF S) × S)) (last : (Label × PMF S) × S)
    (hprev : prev.Terminates) (hsplit : r.trans = prev.append (Seq.cons last Seq.nil)) :
    r.trans.get? (prev.toList hprev).length = some last := by
  rw [hsplit]
  have hlen : (prev.toList hprev).length = Nat.find hprev := Stream'.Seq.length_toList prev hprev
  rw [hlen]
  have := Stream'.Seq.get?_append_find hprev (Seq.cons last Seq.nil) 0
  rw [Nat.add_zero] at this
  rw [this]; rfl

omit [Silent Label] in
/-- **Helper (local copy).** A run consistent with a resolved probabilistic execution has positive
path mass: `pe.Consistent r → pe.probOfR r hT ≠ 0`. -/
private theorem consistent_imp_probOfR_ne_zero {S : Type} {sys : System S Label}
    (pe : ResolvedProbabilisticExecution sys) (r : ResolvedExec S Label)
    (hcons : pe.Consistent r) (hT : r.trans.Terminates) :
    pe.probOfR r hT ≠ 0 := by
  suffices H : ∀ n (r : ResolvedExec S Label) (hcons : pe.Consistent r)
      (hT : r.trans.Terminates), (r.trans.toList hT).length = n → pe.probOfR r hT ≠ 0 from
    H _ r hcons hT rfl
  intro n
  induction n with
  | zero =>
    intro r hcons hT hlen
    have htoList : r.trans.toList hT = [] := List.length_eq_zero_iff.mp hlen
    obtain ⟨i, t⟩ := r
    have h_nil : t = Seq.nil := by
      have h := Stream'.Seq.ofList_toList t hT
      rw [htoList, Stream'.Seq.ofList_nil] at h
      exact h.symm
    subst h_nil
    rw [pe.probOfR_nil i]
    exact hcons.1
  | succ k ih =>
    intro r hcons hT hlen
    have hne : r.trans.toList hT ≠ [] := by
      intro h; rw [h, List.length_nil] at hlen; exact Nat.succ_ne_zero k hlen.symm
    obtain ⟨prev, last, hprev, hsplit, hprevlist, -⟩ :=
      Stream'.Seq.exists_split_last r.trans hT hne
    have happ : (prev.append (Seq.cons last Seq.nil)).Terminates := hsplit ▸ hT
    have hr_eq : r = ⟨r.init, prev.append (Seq.cons last Seq.nil)⟩ := by
      obtain ⟨ri, rt⟩ := r; exact congrArg (AlterSeq.mk ri) hsplit
    have hlen_prev : (prev.toList hprev).length = k := by
      have h1 : (prev.toList hprev).length = (r.trans.toList hT).length - 1 := by
        rw [hprevlist, List.length_dropLast]
      omega
    have hcons_prev : pe.Consistent ⟨r.init, prev⟩ := by
      refine ⟨hcons.1, ?_⟩
      intro m l μ s' hget
      have hntm : ¬ prev.TerminatedAt m := by
        intro htm; rw [Stream'.Seq.TerminatedAt] at htm; rw [htm] at hget
        exact absurd hget (by simp)
      have hgetr : r.trans.get? m = some ((l, μ), s') := by
        rw [hsplit]; rw [Stream'.Seq.get?_append_before_length hntm]; exact hget
      obtain ⟨hnext, hμ⟩ := hcons.2 m l μ s' hgetr
      refine ⟨?_, hμ⟩
      have htake_eq : r.take m = (⟨r.init, prev⟩ : ResolvedExec S Label).take m := by
        unfold AlterSeq.take
        simp only [AlterSeq.mk.injEq, true_and]
        congr 1
        apply List.ext_getElem?
        intro j
        rw [Stream'.Seq.getElem?_take, Stream'.Seq.getElem?_take]
        by_cases hj : j < m
        · rw [if_pos hj, if_pos hj, hsplit]
          have hntj : ¬ prev.TerminatedAt j :=
            fun ht => hntm (Stream'.Seq.terminated_stable prev (Nat.le_of_lt hj) ht)
          exact Stream'.Seq.get?_append_before_length hntj
        · rw [if_neg hj, if_neg hj]
      rw [htake_eq] at hnext
      exact hnext
    have hcongr : pe.probOfR r hT
        = pe.probOfR ⟨r.init, prev.append (Seq.cons last Seq.nil)⟩ happ := by
      cases r; cases hr_eq; rfl
    rw [hcongr, pe.probOfR_append_singleton r.init prev hprev last happ]
    have hgetlast : r.trans.get? (prev.toList hprev).length = some last :=
      get?_last_of_split r prev last hprev hsplit
    obtain ⟨la, qa⟩ := last
    obtain ⟨ll, μμ⟩ := la
    obtain ⟨hnextl, hμl⟩ := hcons.2 (prev.toList hprev).length ll μμ qa hgetlast
    have htake_prev : r.take (prev.toList hprev).length = ⟨r.init, prev⟩ :=
      take_prev_of_split r prev ((ll, μμ), qa) hprev hsplit
    rw [htake_prev] at hnextl
    have hker_ne : pe.rkernel ⟨r.init, prev⟩ ((ll, μμ), qa) ≠ 0 := by
      unfold ResolvedProbabilisticExecution.rkernel
      exact mul_ne_zero hnextl hμl
    exact mul_ne_zero (ih ⟨r.init, prev⟩ hcons_prev hprev hlen_prev) hker_ne

omit [Silent Label] in
/-- **Converse (local copy).** A run with positive path mass is consistent. -/
private theorem probOfR_ne_zero_imp_consistent {S : Type} {sys : System S Label}
    (pe : ResolvedProbabilisticExecution sys) (r : ResolvedExec S Label)
    (hT : r.trans.Terminates) (hpm : pe.probOfR r hT ≠ 0) :
    pe.Consistent r := by
  suffices H : ∀ n (r : ResolvedExec S Label) (hT : r.trans.Terminates),
      (r.trans.toList hT).length = n → pe.probOfR r hT ≠ 0 → pe.Consistent r from
    H _ r hT rfl hpm
  intro n
  induction n with
  | zero =>
    intro r hT hlen hpm
    have htoList : r.trans.toList hT = [] := List.length_eq_zero_iff.mp hlen
    obtain ⟨i, t⟩ := r
    have h_nil : t = Seq.nil := by
      have h := Stream'.Seq.ofList_toList t hT
      rw [htoList, Stream'.Seq.ofList_nil] at h
      exact h.symm
    subst h_nil
    refine ⟨?_, ?_⟩
    · rw [pe.probOfR_nil i] at hpm; exact hpm
    · intro m l μ s' hget
      change (Seq.nil : Seq ((Label × PMF S) × S)).get? m = _ at hget
      rw [Stream'.Seq.get?_nil] at hget
      exact absurd hget (by simp)
  | succ k ih =>
    intro r hT hlen hpm
    have hne : r.trans.toList hT ≠ [] := by
      intro h; rw [h, List.length_nil] at hlen; exact Nat.succ_ne_zero k hlen.symm
    obtain ⟨prev, last, hprev, hsplit, hprevlist, -⟩ :=
      Stream'.Seq.exists_split_last r.trans hT hne
    have happ : (prev.append (Seq.cons last Seq.nil)).Terminates := hsplit ▸ hT
    have hr_eq : r = ⟨r.init, prev.append (Seq.cons last Seq.nil)⟩ := by
      obtain ⟨ri, rt⟩ := r; exact congrArg (AlterSeq.mk ri) hsplit
    have hlen_prev : (prev.toList hprev).length = k := by
      have h1 : (prev.toList hprev).length = (r.trans.toList hT).length - 1 := by
        rw [hprevlist, List.length_dropLast]
      omega
    have hcongr : pe.probOfR r hT
        = pe.probOfR ⟨r.init, prev.append (Seq.cons last Seq.nil)⟩ happ := by
      cases r; cases hr_eq; rfl
    rw [hcongr, pe.probOfR_append_singleton r.init prev hprev last happ] at hpm
    have hpm_prev : pe.probOfR ⟨r.init, prev⟩ hprev ≠ 0 := fun h => hpm (by rw [h, zero_mul])
    have hker : pe.rkernel ⟨r.init, prev⟩ last ≠ 0 := fun h => hpm (by rw [h, mul_zero])
    have hcons_prev : pe.Consistent ⟨r.init, prev⟩ := ih ⟨r.init, prev⟩ hprev hlen_prev hpm_prev
    refine ⟨hcons_prev.1, ?_⟩
    intro m l μ s' hget
    by_cases hmk : m < (prev.toList hprev).length
    · have hntm : ¬ prev.TerminatedAt m := by
        rw [Stream'.Seq.length_toList] at hmk
        exact fun ht => absurd (Stream'.Seq.length_le_iff.mpr ht) (not_le.mpr hmk)
      have hgetprev : prev.get? m = some ((l, μ), s') := by
        rw [hsplit] at hget; rwa [Stream'.Seq.get?_append_before_length hntm] at hget
      obtain ⟨hnext, hμ⟩ := hcons_prev.2 m l μ s' hgetprev
      refine ⟨?_, hμ⟩
      have htake_eq : r.take m = (⟨r.init, prev⟩ : ResolvedExec S Label).take m := by
        unfold AlterSeq.take
        simp only [AlterSeq.mk.injEq, true_and]
        congr 1
        apply List.ext_getElem?
        intro j
        rw [Stream'.Seq.getElem?_take, Stream'.Seq.getElem?_take]
        by_cases hj : j < m
        · rw [if_pos hj, if_pos hj, hsplit]
          have hntj : ¬ prev.TerminatedAt j :=
            fun ht => hntm (Stream'.Seq.terminated_stable prev (Nat.le_of_lt hj) ht)
          exact Stream'.Seq.get?_append_before_length hntj
        · rw [if_neg hj, if_neg hj]
      rw [htake_eq]; exact hnext
    · have hmk' : (prev.toList hprev).length ≤ m := Nat.le_of_not_lt hmk
      have hget_last : r.trans.get? (prev.toList hprev).length = some last :=
        get?_last_of_split r prev last hprev hsplit
      have hlenk : (prev.toList hprev).length = Nat.find hprev :=
        Stream'.Seq.length_toList prev hprev
      have hterm1 : r.trans.TerminatedAt ((prev.toList hprev).length + 1) := by
        rw [hsplit, hlenk]
        exact Stream'.Seq.terminatedAt_append_find hprev
          (show (Seq.cons last Seq.nil).TerminatedAt 1 from rfl)
      have hntm : ¬ r.trans.TerminatedAt m := by
        intro ht
        rw [Stream'.Seq.TerminatedAt, hget] at ht
        exact absurd ht (by simp)
      have hm_le : m ≤ (prev.toList hprev).length := by
        by_contra hlt
        exact hntm (Stream'.Seq.terminated_stable r.trans (Nat.succ_le_of_lt (Nat.lt_of_not_le hlt))
          hterm1)
      have hmeq : m = (prev.toList hprev).length := Nat.le_antisymm hm_le hmk'
      subst hmeq
      rw [hget_last] at hget
      obtain rfl : last = ((l, μ), s') := Option.some.inj hget
      have htake_prev : r.take (prev.toList hprev).length = ⟨r.init, prev⟩ :=
        take_prev_of_split r prev ((l, μ), s') hprev hsplit
      rw [htake_prev]
      unfold ResolvedProbabilisticExecution.rkernel at hker
      exact ⟨fun h => hker (by rw [h, zero_mul]), fun h => hker (by rw [h, mul_zero])⟩

omit [Silent Label] in
/-- **Consistency is prefix-closed (local copy).** -/
private theorem consistent_take {S : Type} {sys : System S Label}
    (pe : ResolvedProbabilisticExecution sys) (r : ResolvedExec S Label)
    (hcons : pe.Consistent r) (n : ℕ) : pe.Consistent (r.take n) := by
  refine ⟨hcons.1, ?_⟩
  intro m l μ s' hget
  have hmn : m < n := by
    by_contra hc
    have : (r.take n).trans.get? m = none := by
      change (Seq.ofList (Seq.take n r.trans)).get? m = none
      rw [Stream'.Seq.ofList_get?]
      apply List.getElem?_eq_none
      exact Nat.le_trans (Stream'.Seq.length_take_le) (Nat.le_of_not_lt hc)
    rw [this] at hget; exact absurd hget (by simp)
  rw [take_trans_get? r hmn] at hget
  obtain ⟨hnext, hμ⟩ := hcons.2 m l μ s' hget
  refine ⟨?_, hμ⟩
  have htk : (r.take n).take m = r.take m := by
    unfold AlterSeq.take
    simp only [AlterSeq.mk.injEq, true_and]
    congr 1
    apply List.ext_getElem?
    intro j
    rw [Stream'.Seq.getElem?_take, Stream'.Seq.getElem?_take]
    by_cases hj : j < m
    · rw [if_pos hj, if_pos hj, Stream'.Seq.ofList_get?, seq_getElem?_take r.trans n j
        (Nat.lt_trans hj hmn)]
    · rw [if_neg hj, if_neg hj]
  rw [htk]; exact hnext

omit [Silent Label] in
/-- **Prefixes of a positive-mass history have positive mass (local copy).** -/
private theorem probOfR_take_ne_zero {S : Type} {sys : System S Label}
    (pe : ResolvedProbabilisticExecution sys) (r : ResolvedExec S Label)
    (hT : r.trans.Terminates) (hpm : pe.probOfR r hT ≠ 0) (k : ℕ) :
    pe.probOfR (r.take k) (take_terminates r k) ≠ 0 :=
  consistent_imp_probOfR_ne_zero pe (r.take k)
    (consistent_take pe r (probOfR_ne_zero_imp_consistent pe r hT hpm) k) (take_terminates r k)

/-- **Nested prefixes collapse (local copy):** `(r.take n).take m = r.take m` for `m ≤ n`. -/
private theorem take_take {S L : Type} (r : ResolvedExec S L) (n m : ℕ) (hmn : m ≤ n) :
    (r.take n).take m = r.take m := by
  unfold AlterSeq.take
  simp only [AlterSeq.mk.injEq, true_and]
  congr 1
  apply List.ext_getElem?
  intro j
  rw [Stream'.Seq.getElem?_take, Stream'.Seq.getElem?_take]
  by_cases hj : j < m
  · rw [if_pos hj, if_pos hj, Stream'.Seq.ofList_get?, seq_getElem?_take r.trans n j
      (Nat.lt_of_lt_of_le hj hmn)]
  · rw [if_neg hj, if_neg hj]

/-- **A history terminated at `n` equals its own length-`n` prefix (local copy).** -/
private theorem take_self_of_terminatedAt {S L : Type} (r : AlterSeq S L) (n : ℕ)
    (hT : r.trans.TerminatedAt n) : r.take n = r := by
  obtain ⟨i, t⟩ := r
  apply AlterSeq.mk.injEq .. |>.mpr
  refine ⟨rfl, ?_⟩
  apply Stream'.Seq.ext
  intro m
  by_cases hm : m < n
  · change (Seq.ofList (Seq.take n t)).get? m = _
    rw [Stream'.Seq.ofList_get?, seq_getElem?_take t n m hm]
  · have hmn : n ≤ m := Nat.le_of_not_lt hm
    have e1 : (Seq.ofList (Seq.take n t)).get? m = none := by
      rw [Stream'.Seq.ofList_get?]
      apply List.getElem?_eq_none
      exact Nat.le_trans (Stream'.Seq.length_take_le) hmn
    change (Seq.ofList (Seq.take n t)).get? m = t.get? m
    rw [e1, Stream'.Seq.le_stable t hmn hT]

/-- **Two histories agreeing below `n`, both terminated at `n`, are equal (local copy).** -/
private theorem resolvedExec_eq_of_take_get?
    {S L : Type} (w₁ w₂ : ResolvedExec S L) (n : ℕ)
    (hi : w₁.init = w₂.init)
    (hle : w₁.take n = w₂.take n)
    (hn : w₁.trans.get? n = w₂.trans.get? n)
    (hT₁ : w₁.trans.TerminatedAt (n + 1)) (hT₂ : w₂.trans.TerminatedAt (n + 1)) :
    w₁ = w₂ := by
  obtain ⟨i₁, t₁⟩ := w₁
  obtain ⟨i₂, t₂⟩ := w₂
  simp only at hi; subst hi
  congr 1
  apply Stream'.Seq.ext
  intro m
  rcases lt_trichotomy m n with hm | hm | hm
  · have := congrArg (fun (e : ResolvedExec S L) => e.trans.get? m) hle
    simpa only [take_trans_get? _ hm] using this
  · subst hm; exact hn
  · have e1 : t₁.get? m = none :=
      Stream'.Seq.le_stable _ (Nat.succ_le_of_lt hm) hT₁
    have e2 : t₂.get? m = none :=
      Stream'.Seq.le_stable _ (Nat.succ_le_of_lt hm) hT₂
    rw [e1, e2]

/-- **Resolved lift of a positive plain history.** A plain belief-history `E` of `PE'.average` with
positive path mass is the plain projection (`toExec`) of a positive-path-mass resolved `PE'`-run
`R'`. Via `probOf E = avgWeight E = ∑ probOfR` over the `toExec`-fibre (`probOf_average`; the
`distFToDist` reading is definitionally the `PE'.average` one); a positive summand supplies `R'`.
Carries positivity (not `Consistent`) — the `probOfR ≠ 0 → Consistent` conversion is deferred to
König's assembly, exactly as `exists_positive_coupled_prefix`. Left as a documented `sorry`. -/
theorem ResolvedProbabilisticExecution.exists_positive_resolved_of_probOf
    {sys : System State Label} (F : Fairness sys)
    (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (E : AlterSeq (PMF State) Label) (hE : E.trans.Terminates)
    (hpos : (PE'.average.distFToDist F).probOf E hE ≠ 0) :
    ∃ R' : ResolvedExec (PMF State) Label,
      ResolvedExec.toExec R' = E ∧ ∃ hT : R'.trans.Terminates, PE'.probOfR R' hT ≠ 0 := by
  classical
  have hpos' : PE'.avgWeight E hE ≠ 0 := by
    have hdef : (PE'.average.distFToDist F).probOf E hE = PE'.average.probOf E hE := rfl
    rw [hdef, PE'.probOf_average E hE] at hpos; exact hpos
  rw [ResolvedProbabilisticExecution.avgWeight] at hpos'
  obtain ⟨r, hr⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hpos')
  exact ⟨r.1, r.2, ResolvedExec.terminates_of_toExec_eq hE r.2, hr⟩

/-- **Resolved normaliser cancellation** (resolved analogue of `beliefTC_normalize_cancel`).
For any weight `w` on resolved runs, the total unnormalised resolved cone mass times the
`w`-integral of the *normalised* resolved cone `beliefTCR` equals the `w`-integral of the
*unnormalised* `beliefTCRw`. On the zero-cone branch both sides vanish; on the positive branch the
`beliefTCR = beliefTCRw · Z⁻¹` factorisation cancels `Z · Z⁻¹ = 1` (finiteness of `Z` via
`beliefTCRw_tsum_eq` + `beliefTCw_tsum_ne_top`). Proven and kept for the resolved-cone telescoping;
the crux-A residual (`lowerFairR_average_step_washout`) is where it feeds in. -/
theorem ResolvedProbabilisticExecution.beliefTCR_normalize_cancel {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (labs : List Label) (s : State) (w : ResolvedExec (PMF State) Label → ENNReal) :
    (∑' R', PE'.beliefTCRw F labs s R') * (∑' R', PE'.beliefTCR F labs s R' * w R')
      = ∑' R', PE'.beliefTCRw F labs s R' * w R' := by
  classical
  by_cases hZ : (∑' R', PE'.beliefTCRw F labs s R') = 0
  · rw [hZ, zero_mul]
    have hz : ∀ R', PE'.beliefTCRw F labs s R' = 0 := ENNReal.tsum_eq_zero.mp hZ
    exact (ENNReal.tsum_eq_zero.mpr (fun R' => by rw [hz R', zero_mul])).symm
  · have hZtop : (∑' R', PE'.beliefTCRw F labs s R') ≠ ⊤ := by
      rw [PE'.beliefTCRw_tsum_eq F labs s]
      exact (PE'.average.distFToDist F).beliefTCw_tsum_ne_top labs s
    have hbel : ∀ R', PE'.beliefTCR F labs s R'
        = PE'.beliefTCRw F labs s R' * (∑' R'', PE'.beliefTCRw F labs s R'')⁻¹ := by
      intro R'
      unfold ResolvedProbabilisticExecution.beliefTCR
      rw [dif_pos hZ, PMF.normalize_apply]
    rw [show (∑' R', PE'.beliefTCR F labs s R' * w R')
          = ∑' R', (PE'.beliefTCRw F labs s R'
              * (∑' R'', PE'.beliefTCRw F labs s R'')⁻¹) * w R' from
        tsum_congr (fun R' => by rw [hbel R']),
      ← ENNReal.tsum_mul_left]
    refine tsum_congr (fun R' => ?_)
    rw [show (∑' R'', PE'.beliefTCRw F labs s R'') *
          (PE'.beliefTCRw F labs s R' * (∑' R'', PE'.beliefTCRw F labs s R'')⁻¹ * w R')
          = ((∑' R'', PE'.beliefTCRw F labs s R'') * (∑' R'', PE'.beliefTCRw F labs s R'')⁻¹) *
            (PE'.beliefTCRw F labs s R' * w R') by ring,
      ENNReal.mul_inv_cancel hZ hZtop, one_mul]

/-! ### Crux A — trace faithfulness (no finiteness)

Crux A (`lowerFairR_average_labMass_eq_lowerWith`) is proved by a direct `reverseRecOn` induction
comparing the `.average`d μ-reading witness `AV := (PE'.lowerFairR F).average` to the μ-blind
trace-cone witness `W := pe'.lowerWith (distFairHyperKernel F)` (mirroring
`ProbabilisticExecution.lowerWith_labProb_eq_aux`), whose single genuine open residual is the
resolved-cone step washout `lowerFairR_average_step_washout` (‡). The following two mechanical
reindexings are standby helpers for a full proof of (‡):

* `probOfR_full_eq_step` — the sys-side cons-end (snoc) reindex: the *step form*
  `∑'_{r' : labs} probOfR r' · (∑'_μ next r' (l,μ) · ∑'_{s'} μ s' · g s')` equals the *full-run
  form* `∑'_{r : labs ++ [l]} probOfR r · g (r.endState)`, via the bijection
  `(r', μ, s') ↦ r' `snoc` ((l, μ), s')` (`snoc_value_identity` + `coverage_split`).
* `rhs_reindex` — the belief-side `toExec`-fibre reindex: `pe'.labMass Λ (μ ↦ ∑' s, μ s · g s)`
  equals `∑'_{R : belief-run, labs Λ} PE'.probOfR R · (∑' s, (R.endState) s · g s)`, via
  `probOf_average` / `avgWeight` over the `toExec`-fibre.

The genuine open content is then isolated in `lowerFairR_average_step_washout`. -/

/-- `Seq.ofList` commutes with a right cons-end append (`L ++ [x]`). -/
private theorem seq_ofList_append_singleton {α : Type} (L : List α) (x : α) :
    (Seq.ofList L).append (Seq.cons x Seq.nil) = Seq.ofList (L ++ [x]) := by
  induction L with
  | nil => simp [Stream'.Seq.ofList_nil, Stream'.Seq.nil_append, Stream'.Seq.ofList_cons]
  | cons a L ih => rw [List.cons_append, Stream'.Seq.ofList_cons, Stream'.Seq.cons_append, ih,
      Stream'.Seq.ofList_cons]

/-- Appending a single-element tail to a terminating sequence terminates. -/
private theorem seq_append_singleton_terminates {α : Type} (s : Seq α) (hs : s.Terminates)
    (x : α) : (s.append (Seq.cons x Seq.nil)).Terminates := by
  rw [← Stream'.Seq.ofList_toList s hs, seq_ofList_append_singleton]
  exact Stream'.Seq.terminates_ofList _

/-- Right-cancellation of a single-element cons-end append for terminating sequences. -/
private theorem append_singleton_cancel {α : Type} (s t : Seq α) (hs : s.Terminates)
    (ht : t.Terminates) (a b : α)
    (h : s.append (Seq.cons a Seq.nil) = t.append (Seq.cons b Seq.nil)) :
    s = t ∧ a = b := by
  rw [← Stream'.Seq.ofList_toList s hs, ← Stream'.Seq.ofList_toList t ht,
      seq_ofList_append_singleton, seq_ofList_append_singleton] at h
  have hlist : s.toList hs ++ [a] = t.toList ht ++ [b] := Stream'.Seq.ofList_injective h
  have h1 : s.toList hs = t.toList ht := List.append_inj_left' hlist rfl
  have h2 : a = b := by have := List.append_inj_right' hlist rfl; simpa using this
  exact ⟨by rw [← Stream'.Seq.ofList_toList s hs, ← Stream'.Seq.ofList_toList t ht, h1], h2⟩

omit [Silent Label] in
/-- The label list of a resolved run's plain projection reads `p.1.1` off each recorded step. -/
private theorem toExec_labels_eq_map (r : ResolvedExec State Label) :
    (ResolvedExec.toExec r).trans.map Prod.fst = r.trans.map (fun p => p.1.1) := by
  change Seq.map Prod.fst (Seq.map (fun p => (p.1.1, p.2)) r.trans) = _
  rw [← Stream'.Seq.map_comp]; rfl

/-- `Seq.ofList` commutes with `Seq.map`. -/
private theorem map_ofList_gen {α β : Type} (f : α → β) (L : List α) :
    (Seq.ofList L).map f = Seq.ofList (L.map f) := by
  induction L with
  | nil => simp [Stream'.Seq.ofList_nil, Stream'.Seq.map_nil]
  | cons a L ih => rw [Stream'.Seq.ofList_cons, Stream'.Seq.map_cons, ih, List.map_cons,
      Stream'.Seq.ofList_cons]

omit [Silent Label] in
/-- The recorded label list of a resolved run's finite prefix, as a list identity. -/
private theorem labels_toList (r : ResolvedExec State Label)
    (hT : r.trans.Terminates) (Λ : List Label)
    (h : (ResolvedExec.toExec r).trans.map Prod.fst = Seq.ofList Λ) :
    (r.trans.toList hT).map (fun p => p.1.1) = Λ := by
  rw [toExec_labels_eq_map, ← Stream'.Seq.ofList_toList r.trans hT, map_ofList_gen] at h
  exact Stream'.Seq.ofList_injective h

omit [Silent Label] in
open Classical in
/-- **Cons-end split of a resolved run at label list `labs ++ [l]`.** A resolved run whose recorded
labels are `labs ++ [l]` splits as `r'` snoc a resolved step `((l, μ), s')`, with `r'` carrying the
labels `labs`. The reverse of the snoc bijection used in `probOfR_full_eq_step`. -/
private theorem coverage_split (r : ResolvedExec State Label)
    (labs : List Label) (l : Label)
    (hguard : r.trans.Terminates ∧
        (ResolvedExec.toExec r).trans.map Prod.fst = Seq.ofList (labs ++ [l])) :
    ∃ (r' : ResolvedExec State Label) (μ : PMF State) (s' : State),
      r = ⟨r'.init, r'.trans.append (Seq.cons ((l, μ), s') Seq.nil)⟩ ∧
      r'.trans.Terminates ∧ (ResolvedExec.toExec r').trans.map Prod.fst = Seq.ofList labs := by
  have hlabsL : (r.trans.toList hguard.1).map (fun p => p.1.1) = labs ++ [l] :=
    labels_toList r hguard.1 (labs ++ [l]) hguard.2
  have hne : r.trans.toList hguard.1 ≠ [] := by
    intro hnil; rw [hnil, List.map_nil] at hlabsL
    exact (List.append_ne_nil_of_right_ne_nil labs (List.cons_ne_nil l [])) hlabsL.symm
  obtain ⟨prev, last, hprev, hsplit, hprevlist, hlast⟩ :=
    Stream'.Seq.exists_split_last r.trans hguard.1 hne
  obtain ⟨⟨lab, μ⟩, s'⟩ := last
  have hmapne : (r.trans.toList hguard.1).map (fun p => p.1.1) ≠ [] := by
    rw [hlabsL]; exact List.append_ne_nil_of_right_ne_nil labs (List.cons_ne_nil l [])
  have hlab : lab = l := by
    have hh : lab = ((r.trans.toList hguard.1).getLast hne).1.1 := congrArg (fun p => p.1.1) hlast
    have hstep : ((r.trans.toList hguard.1).map (fun p => p.1.1)).getLast hmapne
        = ((r.trans.toList hguard.1).getLast hne).1.1 := List.getLast_map hmapne
    calc lab = ((r.trans.toList hguard.1).map (fun p => p.1.1)).getLast hmapne := by rw [hstep, hh]
      _ = (labs ++ [l]).getLast (List.append_ne_nil_of_right_ne_nil labs (List.cons_ne_nil l [])) :=
            List.getLast_congr _ _ hlabsL
      _ = l := List.getLast_concat
  subst hlab
  have hprevlabs : (ResolvedExec.toExec ⟨r.init, prev⟩).trans.map Prod.fst = Seq.ofList labs := by
    rw [toExec_labels_eq_map]
    change prev.map (fun p => p.1.1) = _
    rw [← Stream'.Seq.ofList_toList prev hprev, map_ofList_gen, hprevlist, List.map_dropLast,
        hlabsL, List.dropLast_concat]
  refine ⟨⟨r.init, prev⟩, μ, s', ?_, hprev, hprevlabs⟩
  obtain ⟨ri, rt⟩ := r
  simp only at hsplit ⊢
  exact congrArg (AlterSeq.mk ri) hsplit

omit [Silent Label] in
open Classical in
/-- **The value identity of the snoc bijection.** Producing `r'` then a resolved step `((l, μ), s')`
carries the level-`labs ++ [l]` full-run summand at the snoc onto the step summand at `r'`, via
`probOfR_append_singleton` (`probOfR` factorises) and `endState_append_singleton` (the end state is
`s'`). -/
private theorem snoc_value_identity {sys : System State Label}
    (pe : ResolvedProbabilisticExecution sys) (labs : List Label) (l : Label) (g : State → ENNReal)
    (r' : ResolvedExec State Label) (μ : PMF State) (s' : State)
    (hlabs : (ResolvedExec.toExec r').trans.map Prod.fst = Seq.ofList labs)
    (hterm : r'.trans.Terminates) :
    (dite ((⟨r'.init, r'.trans.append (Seq.cons ((l, μ), s') Seq.nil)⟩ :
          ResolvedExec State Label).trans.Terminates ∧
        (ResolvedExec.toExec ⟨r'.init, r'.trans.append (Seq.cons ((l, μ), s') Seq.nil)⟩).trans.map
            Prod.fst = Seq.ofList (labs ++ [l]))
      (fun h => pe.probOfR ⟨r'.init, r'.trans.append (Seq.cons ((l, μ), s') Seq.nil)⟩ h.1
          * g ((ResolvedExec.toExec ⟨r'.init,
              r'.trans.append (Seq.cons ((l, μ), s') Seq.nil)⟩).endState
              ((ResolvedExec.toExec_terminates_iff _).mpr h.1)))
      (fun _ => 0))
      = pe.probOfR r' hterm * (pe.scheduler.next r' (some (l, μ)) * (μ s' * g s')) := by
  have hsnoc_term : (r'.trans.append (Seq.cons ((l, μ), s') Seq.nil)).Terminates :=
    seq_append_singleton_terminates r'.trans hterm _
  have hlabs_snoc : (ResolvedExec.toExec ⟨r'.init,
        r'.trans.append (Seq.cons ((l, μ), s') Seq.nil)⟩).trans.map Prod.fst
      = Seq.ofList (labs ++ [l]) := by
    rw [toExec_labels_eq_map]
    change (r'.trans.append (Seq.cons ((l, μ), s') Seq.nil)).map (fun p => p.1.1) = _
    rw [Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil,
        show (r'.trans.map fun p => p.1.1) = Seq.ofList labs from by
          rw [← toExec_labels_eq_map]; exact hlabs, seq_ofList_append_singleton]
  rw [dif_pos ⟨hsnoc_term, hlabs_snoc⟩]
  have hprob : pe.probOfR ⟨r'.init, r'.trans.append (Seq.cons ((l, μ), s') Seq.nil)⟩ hsnoc_term
      = pe.probOfR r' hterm * pe.rkernel r' ((l, μ), s') :=
    pe.probOfR_append_singleton r'.init r'.trans hterm ((l, μ), s') hsnoc_term
  have hend : (ResolvedExec.toExec ⟨r'.init,
        r'.trans.append (Seq.cons ((l, μ), s') Seq.nil)⟩).endState
        ((ResolvedExec.toExec_terminates_iff _).mpr hsnoc_term) = s' := by
    have htoExec : (ResolvedExec.toExec ⟨r'.init,
          r'.trans.append (Seq.cons ((l, μ), s') Seq.nil)⟩)
        = ⟨r'.init, ((ResolvedExec.toExec r').trans).append (Seq.cons (l, s') Seq.nil)⟩ := by
      unfold ResolvedExec.toExec
      simp only [Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil]
    rw [AlterSeq.endState_congr_pub htoExec]
    exact AlterSeq.endState_append_singleton (ResolvedExec.toExec r')
      ((ResolvedExec.toExec_terminates_iff r').mpr hterm) l s'
  rw [hprob, hend]
  unfold ResolvedProbabilisticExecution.rkernel
  ring

omit [Silent Label] in
open Classical in
/-- **Step form as a `(r', μ, s')`-sigma.** Flattens the step-form summand's inner `∑'_μ ∑'_{s'}`
into a single sum over the product `ResolvedExec × PMF State × State`. -/
private theorem step_eq_sigma {sys : System State Label}
    (pe : ResolvedProbabilisticExecution sys) (labs : List Label) (l : Label)
    (g : State → ENNReal) :
    (∑' r' : ResolvedExec State Label,
          dite (r'.trans.Terminates ∧
              (ResolvedExec.toExec r').trans.map Prod.fst = Seq.ofList labs)
            (fun h => pe.probOfR r' h.1
                * (∑' μ : PMF State, pe.scheduler.next r' (some (l, μ))
                    * (∑' s' : State, μ s' * g s')))
            (fun _ => 0))
      = ∑' p : (ResolvedExec State Label) × (PMF State) × State,
          dite (p.1.trans.Terminates ∧
              (ResolvedExec.toExec p.1).trans.map Prod.fst = Seq.ofList labs)
            (fun h => pe.probOfR p.1 h.1
                * (pe.scheduler.next p.1 (some (l, p.2.1)) * (p.2.1 p.2.2 * g p.2.2)))
            (fun _ => 0) := by
  rw [ENNReal.tsum_prod']
  refine tsum_congr (fun r' => ?_)
  simp only
  rw [ENNReal.tsum_prod']
  by_cases hc : r'.trans.Terminates ∧
      (ResolvedExec.toExec r').trans.map Prod.fst = Seq.ofList labs
  · simp only [dif_pos hc]
    rw [show (∑' (a : PMF State) (b : State), pe.probOfR r' hc.1
              * (pe.scheduler.next r' (some (l, a)) * (a b * g b)))
          = pe.probOfR r' hc.1 * ∑' (a : PMF State) (b : State),
              (pe.scheduler.next r' (some (l, a)) * (a b * g b)) from by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr (fun a => ?_); rw [← ENNReal.tsum_mul_left]]
    congr 1
    refine tsum_congr (fun μ => ?_)
    rw [← ENNReal.tsum_mul_left]
  · simp only [dif_neg hc, tsum_zero]

omit [Silent Label] in
open Classical in
/-- **Full-run form as a `(r', μ, s')`-sigma** (the sys-side snoc bijection). The full-run summand
at level `labs ++ [l]` equals the step summand's sigma, via the bijection
`(r', μ, s') ↦ r' `snoc` ((l, μ), s')` (`snoc_value_identity`, `coverage_split`,
`append_singleton_cancel`). -/
private theorem full_eq_sigma {sys : System State Label}
    (pe : ResolvedProbabilisticExecution sys) (labs : List Label) (l : Label)
    (g : State → ENNReal) :
    (∑' r : ResolvedExec State Label,
        dite (r.trans.Terminates ∧
            (ResolvedExec.toExec r).trans.map Prod.fst = Seq.ofList (labs ++ [l]))
          (fun h => pe.probOfR r h.1
              * g ((ResolvedExec.toExec r).endState
                  ((ResolvedExec.toExec_terminates_iff r).mpr h.1)))
          (fun _ => 0))
      = ∑' p : (ResolvedExec State Label) × (PMF State) × State,
          dite (p.1.trans.Terminates ∧
              (ResolvedExec.toExec p.1).trans.map Prod.fst = Seq.ofList labs)
            (fun h => pe.probOfR p.1 h.1
                * (pe.scheduler.next p.1 (some (l, p.2.1)) * (p.2.1 p.2.2 * g p.2.2)))
            (fun _ => 0) := by
  classical
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun x =>
      (⟨x.1.1.init, x.1.1.trans.append (Seq.cons ((l, x.1.2.1), x.1.2.2) Seq.nil)⟩ :
        ResolvedExec State Label)) ?_ ?_ ?_
  · -- injective
    rintro ⟨⟨r'₁, μ₁, s'₁⟩, hx₁⟩ ⟨⟨r'₂, μ₂, s'₂⟩, hx₂⟩ h
    simp only at h
    rw [Function.mem_support] at hx₁ hx₂
    have hg₁ : r'₁.trans.Terminates ∧
        (ResolvedExec.toExec r'₁).trans.map Prod.fst = Seq.ofList labs := by
      by_contra hn; rw [dif_neg hn] at hx₁; exact hx₁ rfl
    have hg₂ : r'₂.trans.Terminates ∧
        (ResolvedExec.toExec r'₂).trans.map Prod.fst = Seq.ofList labs := by
      by_contra hn; rw [dif_neg hn] at hx₂; exact hx₂ rfl
    have hinit : r'₁.init = r'₂.init := congrArg (fun e => e.init) h
    have htrans := congrArg (fun e => e.trans) h
    simp only at htrans
    obtain ⟨htr, hlast⟩ := append_singleton_cancel r'₁.trans r'₂.trans hg₁.1 hg₂.1 _ _ htrans
    obtain ⟨hμ, hs⟩ : μ₁ = μ₂ ∧ s'₁ = s'₂ := by
      injection hlast with h1 h2; injection h1 with _ h4; exact ⟨h4, h2⟩
    subst hμ; subst hs
    have hr' : r'₁ = r'₂ := by
      cases r'₁; cases r'₂; simp only [AlterSeq.mk.injEq]; exact ⟨hinit, htr⟩
    subst hr'; rfl
  · -- support of the full-run summand is covered by the snoc range
    intro r hr
    rw [Function.mem_support] at hr
    have hguard : r.trans.Terminates ∧
        (ResolvedExec.toExec r).trans.map Prod.fst = Seq.ofList (labs ++ [l]) := by
      by_contra hn; rw [dif_neg hn] at hr; exact hr rfl
    obtain ⟨r', μ, s', hreq, hr'term, hr'labs⟩ := coverage_split r labs l hguard
    refine ⟨⟨(r', μ, s'), ?_⟩, ?_⟩
    · rw [Function.mem_support, dif_pos ⟨hr'term, hr'labs⟩]
      -- the sigma summand equals the full summand at the snoc (= r), which is `≠ 0`.
      have hval := snoc_value_identity pe labs l g r' μ s' hr'labs hr'term
      intro hz
      apply hr
      rw [hreq, hval]
      exact hz
    · simp only; rw [← hreq]
  · -- value preservation
    rintro ⟨⟨r', μ, s'⟩, hx⟩
    rw [Function.mem_support] at hx
    have hguard : r'.trans.Terminates ∧
        (ResolvedExec.toExec r').trans.map Prod.fst = Seq.ofList labs := by
      by_contra hn; rw [dif_neg hn] at hx; exact hx rfl
    simp only
    rw [dif_pos hguard]
    exact snoc_value_identity pe labs l g r' μ s' hguard.2 hguard.1

omit [Silent Label] in
open Classical in
/-- **The sys-side cons-end reindex.** The full-run form at level `labs ++ [l]` (each terminating
resolved run with those labels, weighted by `probOfR · g (endState)`) equals the step form (the
`probOfR`-weighted one-step functional over the level-`labs` runs). Composes `full_eq_sigma` with
`step_eq_sigma`. No finiteness. -/
private theorem probOfR_full_eq_step {sys : System State Label}
    (pe : ResolvedProbabilisticExecution sys) (labs : List Label) (l : Label)
    (g : State → ENNReal) :
    (∑' r : ResolvedExec State Label,
        dite (r.trans.Terminates ∧
            (ResolvedExec.toExec r).trans.map Prod.fst = Seq.ofList (labs ++ [l]))
          (fun h => pe.probOfR r h.1
              * g ((ResolvedExec.toExec r).endState
                  ((ResolvedExec.toExec_terminates_iff r).mpr h.1)))
          (fun _ => 0))
      = ∑' r' : ResolvedExec State Label,
          dite (r'.trans.Terminates ∧
              (ResolvedExec.toExec r').trans.map Prod.fst = Seq.ofList labs)
            (fun h => pe.probOfR r' h.1
                * (∑' μ : PMF State, pe.scheduler.next r' (some (l, μ))
                    * (∑' s' : State, μ s' * g s')))
            (fun _ => 0) :=
  (full_eq_sigma pe labs l g).trans (step_eq_sigma pe labs l g).symm

open Classical in
/-- **The belief-side `toExec`-fibre reindex.** The belief execution
`pe' := PE'.average.distFToDist F`'s
`g`-integrated level mass `pe'.labMass Λ (μ ↦ ∑' s, μ s · g s)` equals the sum, over terminating
resolved `PE'`-belief-runs `R` with recorded labels `Λ`, of `PE'.probOfR R` times the `g`-integral
of `R`'s end-belief. Uses `probOf_average` (`pe'.probOf E = avgWeight E = ∑' probOfR` over the
`toExec`-fibre) and the same `Sigma` reindex as `traceProbR_eq_sum_avgWeight`. -/
private theorem rhs_reindex {sys : System State Label} (F : Fairness sys)
    (PE' : ResolvedProbabilisticExecution (sys.distF F)) (Λ : List Label) (g : State → ENNReal) :
    (PE'.average.distFToDist F).labMass Λ (fun μ : PMF State => ∑' s : State, μ s * g s)
      = ∑' R : ResolvedExec (PMF State) Label,
          dite (R.trans.Terminates ∧
              (ResolvedExec.toExec R).trans.map Prod.fst = Seq.ofList Λ)
            (fun h => PE'.probOfR R h.1
                * (∑' s : State,
                    ((ResolvedExec.toExec R).endState
                      ((ResolvedExec.toExec_terminates_iff R).mpr h.1)) s * g s))
            (fun _ => 0) := by
  classical
  set C : PMF State → ENNReal := fun μ => ∑' s : State, μ s * g s with hC
  unfold ProbabilisticExecution.labMass
  have hstep : (∑' E : AlterSeq (PMF State) Label,
        dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList Λ)
          (fun h => (PE'.average.distFToDist F).probOf E h.1 * C (E.endState h.1)) (fun _ => 0))
      = ∑' E : AlterSeq (PMF State) Label,
          dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList Λ)
            (fun h => ∑' R : {R : ResolvedExec (PMF State) Label // R.toExec = E},
                PE'.probOfR R.1 (ResolvedExec.terminates_of_toExec_eq h.1 R.2) * C (E.endState h.1))
            (fun _ => 0) := by
    refine tsum_congr (fun E => ?_)
    by_cases hc : E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList Λ
    · rw [dif_pos hc, dif_pos hc]
      have hpo : (PE'.average.distFToDist F).probOf E hc.1 = PE'.avgWeight E hc.1 := by
        change PE'.average.probOf E hc.1 = _; exact PE'.probOf_average E hc.1
      rw [hpo]; unfold ResolvedProbabilisticExecution.avgWeight; rw [ENNReal.tsum_mul_right]
    · rw [dif_neg hc, dif_neg hc]
  rw [hstep]
  have hpull : (∑' E : AlterSeq (PMF State) Label,
        dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList Λ)
          (fun h => ∑' R : {R : ResolvedExec (PMF State) Label // R.toExec = E},
              PE'.probOfR R.1 (ResolvedExec.terminates_of_toExec_eq h.1 R.2) * C (E.endState h.1))
          (fun _ => 0))
      = ∑' (E : AlterSeq (PMF State) Label)
          (R : {R : ResolvedExec (PMF State) Label // R.toExec = E}),
          dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList Λ)
            (fun h => PE'.probOfR R.1 (ResolvedExec.terminates_of_toExec_eq h.1 R.2)
                * C (E.endState h.1))
            (fun _ => 0) := by
    refine tsum_congr (fun E => ?_)
    by_cases hc : E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList Λ
    · simp only [dif_pos hc]
    · simp only [dif_neg hc, tsum_zero]
  rw [hpull, ← ENNReal.tsum_sigma' (f := fun p : Σ E : AlterSeq (PMF State) Label,
      {R : ResolvedExec (PMF State) Label // R.toExec = E} =>
      dite (p.1.trans.Terminates ∧ p.1.trans.map Prod.fst = Seq.ofList Λ)
        (fun h => PE'.probOfR p.2.1 (ResolvedExec.terminates_of_toExec_eq h.1 p.2.2)
            * C (p.1.endState h.1))
        (fun _ => 0))]
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun R => (⟨ResolvedExec.toExec R.1, ⟨R.1, rfl⟩⟩ :
      Σ E : AlterSeq (PMF State) Label, {R : ResolvedExec (PMF State) Label // R.toExec = E}))
    ?_ ?_ ?_
  · intro a b h; exact Subtype.ext (congrArg (fun q => q.2.1) h)
  · intro p hp
    rw [Function.mem_support] at hp
    rcases p with ⟨E, ⟨R, hReq⟩⟩
    subst hReq
    refine ⟨⟨R, ?_⟩, rfl⟩
    rw [Function.mem_support]
    rwa [show (dite (R.trans.Terminates ∧ Seq.map Prod.fst R.toExec.trans = ↑Λ)
          (fun h => PE'.probOfR R h.1 * ∑' s : State,
            ((ResolvedExec.toExec R).endState
              ((ResolvedExec.toExec_terminates_iff R).mpr h.1)) s * g s)
          (fun _ => 0))
        = dite (R.toExec.trans.Terminates ∧ Seq.map Prod.fst R.toExec.trans = ↑Λ)
          (fun h => PE'.probOfR R (ResolvedExec.terminates_of_toExec_eq h.1 rfl)
            * C (R.toExec.endState h.1)) (fun _ => 0) from
      dite_congr (by rw [ResolvedExec.toExec_terminates_iff]) (fun h => rfl) (fun _ => rfl)]
  · intro R
    rcases R with ⟨R, hRne⟩
    simp only
    refine dite_congr (by rw [ResolvedExec.toExec_terminates_iff]) (fun h => rfl) (fun _ => rfl)

open Classical in
/-- **State-function de-average of a resolved-witness level mass.** For any resolved `pe` and any
per-state functional `φ`, the averaged level mass `pe.average.labMass Λ φ` de-averages onto the
resolved-run fibre: it sums `pe.probOfR r · φ (r.toExec.endState)` over the terminating resolved
runs `r` whose plain projection carries labels `Λ`. This is the `some`-free analogue of
`lowerFairR_average_labMass_append_resolved` (same `probOf_average`/`avgWeight` `Sigma` reindex as
`rhs_reindex`, of which this is the `pe := PE'`, `φ := (μ ↦ ∑' s, μ s · g s)` instance). Durable and
crux-independent. -/
private theorem average_labMass_state {sys : System State Label}
    (pe : ResolvedProbabilisticExecution sys) (Λ : List Label) (φ : State → ENNReal) :
    pe.average.labMass Λ φ
      = ∑' r : ResolvedExec State Label,
          dite (r.trans.Terminates ∧
              (ResolvedExec.toExec r).trans.map Prod.fst = Seq.ofList Λ)
            (fun h => pe.probOfR r h.1
                * φ ((ResolvedExec.toExec r).endState
                    ((ResolvedExec.toExec_terminates_iff r).mpr h.1)))
            (fun _ => 0) := by
  classical
  unfold ProbabilisticExecution.labMass
  -- Rewrite `probOf = avgWeight`, expand the fibre sum, reindex the `Sigma` onto the `r`-fibre.
  have hstep : (∑' e : AlterSeq State Label,
        dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList Λ)
          (fun h => pe.average.probOf e h.1 * φ (e.endState h.1)) (fun _ => 0))
      = ∑' e : AlterSeq State Label,
          dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList Λ)
            (fun h => ∑' r : {r : ResolvedExec State Label // r.toExec = e},
                pe.probOfR r.1 (ResolvedExec.terminates_of_toExec_eq h.1 r.2) * φ (e.endState h.1))
            (fun _ => 0) := by
    refine tsum_congr (fun e => ?_)
    by_cases hc : e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList Λ
    · rw [dif_pos hc, dif_pos hc, pe.probOf_average e hc.1]
      unfold ResolvedProbabilisticExecution.avgWeight; rw [ENNReal.tsum_mul_right]
    · rw [dif_neg hc, dif_neg hc]
  rw [hstep]
  have hpull : (∑' e : AlterSeq State Label,
        dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList Λ)
          (fun h => ∑' r : {r : ResolvedExec State Label // r.toExec = e},
              pe.probOfR r.1 (ResolvedExec.terminates_of_toExec_eq h.1 r.2) * φ (e.endState h.1))
          (fun _ => 0))
      = ∑' (e : AlterSeq State Label) (r : {r : ResolvedExec State Label // r.toExec = e}),
          dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList Λ)
            (fun h => pe.probOfR r.1 (ResolvedExec.terminates_of_toExec_eq h.1 r.2)
                * φ (e.endState h.1))
            (fun _ => 0) := by
    refine tsum_congr (fun e => ?_)
    by_cases hc : e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList Λ
    · simp only [dif_pos hc]
    · simp only [dif_neg hc, tsum_zero]
  rw [hpull, ← ENNReal.tsum_sigma' (f := fun p : Σ e : AlterSeq State Label,
      {r : ResolvedExec State Label // r.toExec = e} =>
      dite (p.1.trans.Terminates ∧ p.1.trans.map Prod.fst = Seq.ofList Λ)
        (fun h => pe.probOfR p.2.1 (ResolvedExec.terminates_of_toExec_eq h.1 p.2.2)
            * φ (p.1.endState h.1))
        (fun _ => 0))]
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun r => (⟨ResolvedExec.toExec r.1, ⟨r.1, rfl⟩⟩ :
      Σ e : AlterSeq State Label, {r : ResolvedExec State Label // r.toExec = e})) ?_ ?_ ?_
  · intro a b h; exact Subtype.ext (congrArg (fun q => q.2.1) h)
  · intro p hp
    rw [Function.mem_support] at hp
    rcases p with ⟨e, ⟨r, hreq⟩⟩
    subst hreq
    refine ⟨⟨r, ?_⟩, rfl⟩
    rw [Function.mem_support]
    rwa [show (dite (r.trans.Terminates ∧ Seq.map Prod.fst r.toExec.trans = ↑Λ)
          (fun h => pe.probOfR r h.1 * φ ((ResolvedExec.toExec r).endState
              ((ResolvedExec.toExec_terminates_iff r).mpr h.1)))
          (fun _ => 0))
        = dite (r.toExec.trans.Terminates ∧ Seq.map Prod.fst r.toExec.trans = ↑Λ)
          (fun h => pe.probOfR r (ResolvedExec.terminates_of_toExec_eq h.1 rfl)
            * φ (r.toExec.endState h.1)) (fun _ => 0) from
      dite_congr (by rw [ResolvedExec.toExec_terminates_iff]) (fun h => rfl) (fun _ => rfl)]
  · intro r
    rcases r with ⟨r, hrne⟩
    simp only
    refine dite_congr (by rw [ResolvedExec.toExec_terminates_iff]) (fun h => rfl) (fun _ => rfl)

/-- **Per-history de-average identity (`some`-step).** At a fixed terminating `sys`-history `e'`,
the averaged one-step contribution `AV.probOf e' · ∑' s', AV.kernel e' (l, s') · g s'`
(`AV := (PE'.lowerFairR F).average`) equals the un-normalised `LF`-posterior sum over the
`toExec`-fibre of `e'` of the per-run functional
`B(r') := ∑' μ, LF.scheduler.next r' (some (l, μ)) · (∑' s', μ s' · g s')`
(`LF := PE'.lowerFairR F`). The `avgWeight · avgWeight⁻¹` cancels to `1` on the positive branch
and both sides vanish when `avgWeight e' = 0`. No filter/coherence content — pure `average`
bookkeeping (`probOf_average`, `average_next_some`). -/
private theorem lowerFairR_average_step_deaverage {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (e' : AlterSeq State Label) (he' : e'.trans.Terminates) (l : Label) (g : State → ENNReal) :
    ((PE'.lowerFairR F).average).probOf e' he'
        * (∑' s' : State, ((PE'.lowerFairR F).average).kernel e' (l, s') * g s')
      = ∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'},
          (PE'.lowerFairR F).probOfR r'.1
              (ResolvedExec.terminates_of_toExec_eq he' r'.2)
            * (∑' μ : PMF State, (PE'.lowerFairR F).scheduler.next r'.1 (some (l, μ))
                * (∑' s' : State, μ s' * g s')) := by
  classical
  set LF := PE'.lowerFairR F with hLF
  set AV := LF.average with hAV
  -- Abbreviate the per-run functional `B`.
  set B : {r' : ResolvedExec State Label // r'.toExec = e'} → ENNReal := fun r' =>
      ∑' μ : PMF State, LF.scheduler.next r'.1 (some (l, μ)) * (∑' s' : State, μ s' * g s')
    with hB
  set W := LF.avgWeight e' he' with hW
  set X := ∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'},
      LF.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2) * B r' with hX
  -- `AV.probOf e' = LF.avgWeight e'`.
  rw [show AV.probOf e' he' = W from LF.probOf_average e' he']
  -- The `some`-step contribution, written with `avgWeight⁻¹` pulled out to the front.
  have hkernel : (∑' s' : State, AV.kernel e' (l, s') * g s') = W⁻¹ * X := by
    simp only [ProbabilisticExecution.kernel]
    -- `AV.scheduler.next e' (some (l, μ)) = (∑' fibre …) * W⁻¹`.
    have hnext : ∀ μ : PMF State, AV.scheduler.next e' (some (l, μ))
        = (∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'},
              LF.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)
                * LF.scheduler.next r'.1 (some (l, μ))) * W⁻¹ :=
      fun μ => LF.average_next_some e' he' l μ
    simp only [hnext]
    -- Reindex the `s'`/`μ`-sum to a fibre-outer `∑' r'`, cancelling `W⁻¹`.
    rw [hX, hB]
    -- Canonical triple `∑' s' μ r'` → factor `W⁻¹, probOfR, next` out to `W⁻¹ · ∑' r' probOfR · B`.
    have e1 : (∑' s' : State, (∑' μ : PMF State,
          (∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'},
              LF.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)
                * LF.scheduler.next r'.1 (some (l, μ))) * W⁻¹ * μ s') * g s')
        = ∑' (s' : State) (μ : PMF State)
            (r' : {r' : ResolvedExec State Label // r'.toExec = e'}),
            W⁻¹ * (LF.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)
              * (LF.scheduler.next r'.1 (some (l, μ)) * (μ s' * g s'))) := by
      refine tsum_congr (fun s' => ?_)
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr (fun μ => ?_)
      rw [show (∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'},
                LF.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)
                  * LF.scheduler.next r'.1 (some (l, μ))) * W⁻¹ * μ s' * g s'
            = (∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'},
                LF.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)
                  * LF.scheduler.next r'.1 (some (l, μ))) * (W⁻¹ * μ s' * g s') from by ring,
        ← ENNReal.tsum_mul_right]
      refine tsum_congr (fun r' => ?_)
      ring
    rw [e1]
    rw [ENNReal.tsum_comm (f := fun s' μ =>
        ∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'},
          W⁻¹ * (LF.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)
            * (LF.scheduler.next r'.1 (some (l, μ)) * (μ s' * g s'))))]
    rw [show (∑' (μ : PMF State) (s' : State)
            (r' : {r' : ResolvedExec State Label // r'.toExec = e'}),
            W⁻¹ * (LF.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)
              * (LF.scheduler.next r'.1 (some (l, μ)) * (μ s' * g s'))))
          = ∑' (r' : {r' : ResolvedExec State Label // r'.toExec = e'}) (μ : PMF State)
              (s' : State),
            W⁻¹ * (LF.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)
              * (LF.scheduler.next r'.1 (some (l, μ)) * (μ s' * g s'))) from by
        rw [show (∑' (μ : PMF State) (s' : State)
                (r' : {r' : ResolvedExec State Label // r'.toExec = e'}),
                W⁻¹ * (LF.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)
                  * (LF.scheduler.next r'.1 (some (l, μ)) * (μ s' * g s'))))
              = ∑' (μ : PMF State)
                  (r' : {r' : ResolvedExec State Label // r'.toExec = e'}) (s' : State),
                W⁻¹ * (LF.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)
                  * (LF.scheduler.next r'.1 (some (l, μ)) * (μ s' * g s'))) from
            tsum_congr (fun μ => ENNReal.tsum_comm)]
        rw [ENNReal.tsum_comm]]
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr (fun r' => ?_)
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    refine tsum_congr (fun μ => ?_)
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  rw [hkernel]
  -- Cancel `W · W⁻¹ = 1` (positive branch) or both sides `0` (zero branch).
  by_cases hW0 : W = 0
  · -- `W = 0`: then `∑' r' probOfR = 0`, so every `probOfR r' = 0`, so `X = 0`.
    have hXz : X = 0 := by
      rw [hX]
      refine ENNReal.tsum_eq_zero.mpr (fun r' => ?_)
      have hsum0 : (∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'},
          LF.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq he' r'.2)) = 0 := hW0
      rw [ENNReal.tsum_eq_zero.mp hsum0 r', zero_mul]
    rw [hW0, hXz, mul_zero, mul_zero]
  · have hWtop : W ≠ ⊤ :=
      (((LF.avgWeight_le_init e' he').trans (PMF.coe_le_one _ _)).trans_lt ENNReal.one_lt_top).ne
    rw [← mul_assoc, ENNReal.mul_inv_cancel hW0 hWtop, one_mul]

open Classical in
/-- **De-average reformulation of the appended-step level mass.** The `g`-integrated level mass of
`AV := (PE'.lowerFairR F).average` at `labs ++ [l]` equals a sum over the *resolved* `PE'`-runs `r'`
whose plain projection `toExec r'` carries label list `labs`, of the `LF`-posterior weight
`LF.probOfR r'` (`LF := PE'.lowerFairR F`) times the per-run one-step functional
`∑' μ, LF.scheduler.next r' (some (l, μ)) · (∑' s', μ s' · g s')`. The `average` normaliser is
cancelled (`lowerFairR_average_step_deaverage`); the plain-history level-`labs` sum is reindexed
along `toExec` onto the resolved-run fibre (same `Sigma`/`tsum_eq_tsum_of_ne_zero_bij` pattern as
`traceProbR_eq_sum_avgWeight`). This eliminates the `average` and states the level mass purely in
terms of `LF.probOfR` and `LF.scheduler.next`. -/
private theorem lowerFairR_average_labMass_append_resolved {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (labs : List Label) (l : Label) (g : State → ENNReal) :
    ((PE'.lowerFairR F).average).labMass (labs ++ [l]) g
      = ∑' r' : ResolvedExec State Label,
          dite (r'.trans.Terminates ∧
              (ResolvedExec.toExec r').trans.map Prod.fst = Seq.ofList labs)
            (fun h => (PE'.lowerFairR F).probOfR r' h.1
                * (∑' μ : PMF State, (PE'.lowerFairR F).scheduler.next r' (some (l, μ))
                    * (∑' s' : State, μ s' * g s')))
            (fun _ => 0) := by
  classical
  set LF := PE'.lowerFairR F with hLF
  set AV := LF.average with hAV
  -- Step form of the level mass, then de-average each terminating summand.
  rw [AV.labMass_step labs l g]
  have hstep : (∑' e' : AlterSeq State Label,
        dite (e'.trans.Terminates ∧ e'.trans.map Prod.fst = Seq.ofList labs)
          (fun h => AV.probOf e' h.1 * ∑' s' : State, AV.kernel e' (l, s') * g s')
          (fun _ => 0))
      = ∑' e' : AlterSeq State Label,
          dite (e'.trans.Terminates ∧ e'.trans.map Prod.fst = Seq.ofList labs)
            (fun h => ∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'},
                LF.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq h.1 r'.2)
                  * (∑' μ : PMF State, LF.scheduler.next r'.1 (some (l, μ))
                      * (∑' s' : State, μ s' * g s')))
            (fun _ => 0) := by
    refine tsum_congr (fun e' => ?_)
    by_cases hc : e'.trans.Terminates ∧ e'.trans.map Prod.fst = Seq.ofList labs
    · rw [dif_pos hc, dif_pos hc]
      exact lowerFairR_average_step_deaverage F PE' e' hc.1 l g
    · rw [dif_neg hc, dif_neg hc]
  rw [hstep]
  -- Pull the `dite` inside the fibre sum, so the whole is `∑' e' ∑' (r' : fibre)`.
  have hpull : (∑' e' : AlterSeq State Label,
        dite (e'.trans.Terminates ∧ e'.trans.map Prod.fst = Seq.ofList labs)
          (fun h => ∑' r' : {r' : ResolvedExec State Label // r'.toExec = e'},
              LF.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq h.1 r'.2)
                * (∑' μ : PMF State, LF.scheduler.next r'.1 (some (l, μ))
                    * (∑' s' : State, μ s' * g s')))
          (fun _ => 0))
      = ∑' (e' : AlterSeq State Label) (r' : {r' : ResolvedExec State Label // r'.toExec = e'}),
          dite (e'.trans.Terminates ∧ e'.trans.map Prod.fst = Seq.ofList labs)
            (fun h => LF.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq h.1 r'.2)
                * (∑' μ : PMF State, LF.scheduler.next r'.1 (some (l, μ))
                    * (∑' s' : State, μ s' * g s')))
            (fun _ => 0) := by
    refine tsum_congr (fun e' => ?_)
    by_cases hc : e'.trans.Terminates ∧ e'.trans.map Prod.fst = Seq.ofList labs
    · simp only [dif_pos hc]
    · rw [dif_neg hc]; simp only [dif_neg hc, tsum_zero]
  rw [hpull, ← ENNReal.tsum_sigma' (f := fun p : Σ e' : AlterSeq State Label,
      {r' : ResolvedExec State Label // r'.toExec = e'} =>
      dite (p.1.trans.Terminates ∧ p.1.trans.map Prod.fst = Seq.ofList labs)
        (fun h => LF.probOfR p.2.1 (ResolvedExec.terminates_of_toExec_eq h.1 p.2.2)
            * (∑' μ : PMF State, LF.scheduler.next p.2.1 (some (l, μ))
                * (∑' s' : State, μ s' * g s')))
        (fun _ => 0))]
  -- The RHS support guard: a resolved run `r'` in the RHS support satisfies the dite guard.
  have guard_of_supp : ∀ r' : ResolvedExec State Label,
      (dite (r'.trans.Terminates ∧
          (ResolvedExec.toExec r').trans.map Prod.fst = Seq.ofList labs)
        (fun h => LF.probOfR r' h.1
            * (∑' μ : PMF State, LF.scheduler.next r' (some (l, μ))
                * (∑' s' : State, μ s' * g s')))
        (fun _ => 0)) ≠ 0 →
      r'.trans.Terminates ∧ (ResolvedExec.toExec r').trans.map Prod.fst = Seq.ofList labs := by
    intro r' hr'
    by_contra hn; rw [dif_neg hn] at hr'; exact hr' rfl
  -- Bijection `r' ↦ ⟨toExec r', r'⟩` : `(resolved runs in support) → (Σ e', toExec-fibre)`.
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun r' => (⟨ResolvedExec.toExec r'.1, ⟨r'.1, rfl⟩⟩ :
      Σ e' : AlterSeq State Label, {r' : ResolvedExec State Label // r'.toExec = e'})) ?_ ?_ ?_
  · -- injective
    intro a b h
    exact Subtype.ext (congrArg (fun q => q.2.1) h)
  · -- the LHS support is covered
    intro p hp
    rw [Function.mem_support] at hp
    have hguard : p.1.trans.Terminates ∧ p.1.trans.map Prod.fst = Seq.ofList labs := by
      by_contra hn; rw [dif_neg hn] at hp; exact hp rfl
    have htermR : p.2.1.trans.Terminates :=
      ResolvedExec.terminates_of_toExec_eq hguard.1 p.2.2
    have hlabsR : (ResolvedExec.toExec p.2.1).trans.map Prod.fst = Seq.ofList labs := by
      rw [p.2.2]; exact hguard.2
    refine ⟨⟨p.2.1, ?_⟩, ?_⟩
    · rw [Function.mem_support, dif_pos ⟨htermR, hlabsR⟩]
      rw [dif_pos hguard] at hp
      exact hp
    · -- the chosen sigma `⟨toExec p.2.1, ⟨p.2.1, rfl⟩⟩` reconstructs `p`.
      rcases p with ⟨e', ⟨r', hr'eq⟩⟩
      subst hr'eq
      rfl
  · -- the bijection preserves the summand
    intro r'
    have htermR : r'.1.trans.Terminates := (guard_of_supp r'.1 r'.2).1
    have hlabsR : (ResolvedExec.toExec r'.1).trans.map Prod.fst = Seq.ofList labs :=
      (guard_of_supp r'.1 r'.2).2
    have hE_term : (ResolvedExec.toExec r'.1).trans.Terminates :=
      (ResolvedExec.toExec_terminates_iff r'.1).mpr htermR
    change dite _ _ _ = _
    rw [dif_pos ⟨hE_term, hlabsR⟩, dif_pos ⟨htermR, hlabsR⟩]

/-! ### Durable one-step recursion bricks (crux-A infrastructure)

Two mechanical, correct-independent-of-the-crux factorisations of the resolved objects along a
final concrete step. Both are the resolved analogue of how the *plain* belief trace-cone `beliefTCw`
recurses, obtained from the `probOfR` cons-end law `probOfR_append_singleton` (via the already
proven `snoc_value_identity`). They are the raw material of any genuine attempt at the washout
`(†)` — expressing the length-`n+1` resolved cone weight `beliefTCRw` and the μ-reading witness's
posterior weight `lowerFairR.probOfR` through their length-`n` data plus a last concrete step. -/

open Classical in
/-- **Brick 1 — `beliefTCRw` one-step (cons-end) recursion.** The length-`n+1` unnormalised resolved
cone weight of the belief-run `R'` snoc a recorded belief-step `((l, ω), ν')` factors through the
length-`n` data of `R'`: the resolved posterior weight `probOfR R'`, the abstract scheduler's
emission `scheduler.next R' (some (l, ω))`, the recorded `ω`-mass `ω ν'` of the sampled belief `ν'`,
and the end-belief mass `ν' s'`. This is the resolved analogue of the plain
`beliefTCw`-recursion, read off the `probOfR` cons-end law (`snoc_value_identity` at `pe := PE'`,
`g := (· s')`) together with `toExec_append_singleton`/`endState_append_singleton` (the appended
step's end-belief is `ν'`). It is TRUE and reusable regardless of the crux. -/
theorem ResolvedProbabilisticExecution.beliefTCRw_append_singleton {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (labs : List Label) (l : Label) (s' : State)
    (R' : ResolvedExec (PMF State) Label) (ω : PMF (PMF State)) (ν' : PMF State)
    (hR' : R'.trans.Terminates)
    (hlab : (ResolvedExec.toExec R').trans.map Prod.fst = Seq.ofList labs) :
    PE'.beliefTCRw F (labs ++ [l]) s'
        ⟨R'.init, R'.trans.append (Seq.cons ((l, ω), ν') Seq.nil)⟩
      = PE'.probOfR R' hR' * PE'.scheduler.next R' (some (l, ω)) * ω ν' * ν' s' := by
  classical
  -- `beliefTCRw ls s R'' = dite guard (probOfR R'' · endState s') 0`, i.e. `snoc_value_identity`
  -- specialised to `g := (· s')` (the endstate-belief evaluated at `s'`).
  have hsnoc := snoc_value_identity PE' labs l (fun ρ : PMF State => ρ s') R' ω ν' hlab hR'
  -- The `beliefTCRw`-`dite` is literally the `snoc_value_identity`-`dite` with `g := (· s')`.
  rw [ResolvedProbabilisticExecution.beliefTCRw]
  rw [hsnoc]
  ring

open Classical in
/-- **Brick 2 — `lowerFairR.probOfR` one-step (cons-end) recursion.** The μ-reading witness's
posterior weight of a concrete run `r'` snoc a concrete step `((l, μ), s')` factors as the weight
of the prefix `r'` times the witness scheduler's emission `lowerFairRSched.next r' (some (l, μ))`
(which
carries the last-step renormaliser `1/m(r')`, `m(r') := ∑'_{RCoherentTL r'} beliefTCR`) times the
sampled next-state mass `μ s'`. Read off the `probOfR` cons-end law `probOfR_append_singleton` at
`pe := lowerFairR F` (whose `rkernel` is `next · μ s'`). The renormaliser is *inside*
`lowerFairRSched.next r'`; `lowerFairR_emission_integral` below extracts it explicitly. TRUE and
reusable regardless of the crux. -/
theorem ResolvedProbabilisticExecution.lowerFairR_probOfR_append_singleton
    {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (r' : ResolvedExec State Label) (l : Label) (μ : PMF State) (s' : State)
    (hr' : r'.trans.Terminates)
    (happ : (⟨r'.init, r'.trans.append (Seq.cons ((l, μ), s') Seq.nil)⟩ :
        ResolvedExec State Label).trans.Terminates) :
    (PE'.lowerFairR F).probOfR
        ⟨r'.init, r'.trans.append (Seq.cons ((l, μ), s') Seq.nil)⟩ happ
      = (PE'.lowerFairR F).probOfR r' hr'
          * (PE'.lowerFairR F).scheduler.next r' (some (l, μ)) * μ s' := by
  have hfact := (PE'.lowerFairR F).probOfR_append_singleton
    r'.init r'.trans hr' ((l, μ), s') happ
  rw [hfact]
  unfold ResolvedProbabilisticExecution.rkernel
  ring

open Classical in
/-- **Brick 2b — emission integral of the μ-reading witness, renormaliser exposed.** For a concrete
run `r'` whose plain projection terminates and whose `RCoherentTL r'`-restricted resolved cone has
positive mass `m(r') ≠ 0`, the `g`-integrated one-step emission of the witness scheduler equals the
renormalised cone-average of the per-history one-step post-marginal functional `Demit`:

  `∑' μ, lowerFairRSched.next r' (some (l, μ)) · (∑' s', μ s' · g s')`
      `= (1/m(r')) · ∑' R', ⟦RCoherentTL r' R'⟧ · beliefTCR labs s₀ R' · Demit (toExec R') s₀`,

with `labs := toExec r'`'s labels, `s₀ := r'`'s end-belief-state, and
`Demit E s₀ := ∑' ω, pe'.scheduler.next E (some (l, ω)) · (∑' q, ((dfhk E l ω s₀).bind id) q · g q)`
(`pe' := PE'.average.distFToDist F`, `dfhk := pe'.distFairHyperKernel F`). This unfolds
`lowerFairRSched.next` (the `PMF.filter`/`bind` emission), integrates the inner
`distFairHyperKernel` post-marginal via `distFairHyperKernel_decomp_gsum`'s companion
`bind id`, and pulls the
`1/m(r')` renormaliser out of the `PMF.filter`. It is the explicit form of `B(r')` used in `(†)`.
TRUE and reusable regardless of the crux. -/
theorem ResolvedProbabilisticExecution.lowerFairR_emission_integral
    {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (r' : ResolvedExec State Label) (l : Label) (g : State → ENNReal)
    (h_term : r'.toExec.trans.Terminates)
    (h0 : (∑' R', Set.indicator {R' | PE'.RCoherentTL F r' R'}
        (PE'.beliefTCR F ((r'.toExec.trans.toList h_term).map Prod.fst)
          (r'.toExec.endState h_term)) R') ≠ 0) :
    (∑' μ : PMF State, (PE'.lowerFairR F).scheduler.next r' (some (l, μ))
        * (∑' s' : State, μ s' * g s'))
      = (∑' R', Set.indicator {R' | PE'.RCoherentTL F r' R'}
            (PE'.beliefTCR F ((r'.toExec.trans.toList h_term).map Prod.fst)
              (r'.toExec.endState h_term)) R')⁻¹
        * ∑' R' : ResolvedExec (PMF State) Label,
            (Set.indicator {R' | PE'.RCoherentTL F r' R'}
              (PE'.beliefTCR F ((r'.toExec.trans.toList h_term).map Prod.fst)
                (r'.toExec.endState h_term)) R')
            * (∑' ω : PMF (PMF State),
                (PE'.average.distFToDist F).scheduler.next (ResolvedExec.toExec R') (some (l, ω))
                  * (∑' q : State,
                      (((PE'.average.distFToDist F).distFairHyperKernel F
                          (ResolvedExec.toExec R') l ω (r'.toExec.endState h_term)).bind id) q
                        * g q)) := by
  classical
  set pe' := PE'.average.distFToDist F with hpe'
  set labs := (r'.toExec.trans.toList h_term).map Prod.fst with hlabs
  set s₀ := r'.toExec.endState h_term with hs₀
  set cone : ResolvedExec (PMF State) Label → ENNReal := fun R' =>
    Set.indicator {R' | PE'.RCoherentTL F r' R'} (PE'.beliefTCR F labs s₀) R' with hcone
  set m : ENNReal := ∑' R', cone R' with hm
  -- The witness scheduler's `some (l, μ)` emission (positive-restricted-mass branch).
  have hnext : ∀ μ : PMF State, (PE'.lowerFairR F).scheduler.next r' (some (l, μ))
      = ((PE'.beliefTCR F labs s₀).filter {R' | PE'.RCoherentTL F r' R'}
            (by
              obtain ⟨R', hR'⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr h0)
              obtain ⟨hmem, hsupp⟩ := Set.indicator_apply_ne_zero.mp hR'
              exact ⟨R', hmem, hsupp⟩)).bind (fun R' =>
          (pe'.scheduler.next (ResolvedExec.toExec R')).bind (fun opt =>
            match opt with
            | none         => PMF.pure none
            | some (l', ω) =>
              (pe'.distFairHyperKernel F (ResolvedExec.toExec R') l' ω s₀).map
                (fun μ' => some (l', μ')))) (some (l, μ)) := by
    intro μ
    change (PE'.lowerFairRSched F).next r' (some (l, μ)) = _
    unfold ResolvedProbabilisticExecution.lowerFairRSched
    simp only
    rw [dif_pos h_term, dif_pos h0]
  -- Abbreviate the `g`-integral `φ μ = ∑' s', μ s' · g s'`.
  set φ : PMF State → ENNReal := fun μ => ∑' s' : State, μ s' * g s' with hφ
  -- The filter's support witness (reused from `hnext`).
  have hfsupp : ∃ a ∈ {R' | PE'.RCoherentTL F r' R'}, a ∈ (PE'.beliefTCR F labs s₀).support := by
    obtain ⟨R', hR'⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr h0)
    obtain ⟨hmem, hsupp⟩ := Set.indicator_apply_ne_zero.mp hR'
    exact ⟨R', hmem, hsupp⟩
  -- The inner post-emission `PMF` bound to each sampled belief-run `R'`.
  set inner : ResolvedExec (PMF State) Label → PMF (Option (Label × PMF State)) := fun R' =>
    (pe'.scheduler.next (ResolvedExec.toExec R')).bind (fun opt =>
      match opt with
      | none         => PMF.pure none
      | some (l', ω) =>
        (pe'.distFairHyperKernel F (ResolvedExec.toExec R') l' ω s₀).map
          (fun μ' => some (l', μ'))) with hinner
  -- **Step 1.** `∑' μ, next(some(l,μ)) · φ μ`
  --   `= ∑' R', filter(R') · (∑' μ, inner R' (some(l,μ)) · φ μ)`.
  have hstep1 : (∑' μ : PMF State, (PE'.lowerFairR F).scheduler.next r' (some (l, μ)) * φ μ)
      = ∑' R' : ResolvedExec (PMF State) Label,
          ((PE'.beliefTCR F labs s₀).filter {R' | PE'.RCoherentTL F r' R'} hfsupp) R'
            * (∑' μ : PMF State, inner R' (some (l, μ)) * φ μ) := by
    simp only [hnext, PMF.bind_apply]
    -- `∑' μ (∑' R', filter R' · inner R' (some(l,μ))) · φ μ`; swap to `R'`-outer.
    rw [show (∑' μ : PMF State,
          (∑' R' : ResolvedExec (PMF State) Label,
            ((PE'.beliefTCR F labs s₀).filter {R' | PE'.RCoherentTL F r' R'} hfsupp) R'
              * inner R' (some (l, μ))) * φ μ)
        = ∑' μ : PMF State, ∑' R' : ResolvedExec (PMF State) Label,
            ((PE'.beliefTCR F labs s₀).filter {R' | PE'.RCoherentTL F r' R'} hfsupp) R'
              * (inner R' (some (l, μ)) * φ μ) from
      tsum_congr (fun μ => by rw [← ENNReal.tsum_mul_right]; exact tsum_congr (fun R' => by ring))]
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun R' => ?_)
    rw [← ENNReal.tsum_mul_left]
  rw [hstep1]
  -- **Step 2.** `filter(R') = cone(R') · m⁻¹` (`PMF.filter_apply` + `indicator`), pull `m⁻¹` out.
  have hfilter : ∀ R' : ResolvedExec (PMF State) Label,
      ((PE'.beliefTCR F labs s₀).filter {R' | PE'.RCoherentTL F r' R'} hfsupp) R'
        = cone R' * m⁻¹ := by
    intro R'
    rw [PMF.filter_apply hfsupp R']
  simp only [hfilter]
  -- **Step 3.** `∑' μ, inner R' (some(l,μ)) · φ μ = Demit(toExec R', s₀)` (the per-history value).
  have hQ : ∀ R' : ResolvedExec (PMF State) Label,
      (∑' μ : PMF State, inner R' (some (l, μ)) * φ μ)
        = ∑' ω : PMF (PMF State),
            (pe'.scheduler.next (ResolvedExec.toExec R')) (some (l, ω))
              * ∑' q : State,
                  ((pe'.distFairHyperKernel F (ResolvedExec.toExec R') l ω s₀).bind id) q
                    * g q := by
    intro R'
    set E := ResolvedExec.toExec R' with hEdef
    -- Abbreviate the abstract emission `next E opt` and the post-kernel `M opt`
    -- (`none => pure none`; `some(l',ω) => map (some(l',·)) (dfhk E l' ω s₀)`).
    set M : Option (Label × PMF (PMF State)) → PMF (Option (Label × PMF State)) := fun opt =>
      match opt with
      | none         => PMF.pure none
      | some (l', ω) =>
        (pe'.distFairHyperKernel F E l' ω s₀).map (fun μ' => some (l', μ')) with hM
    -- `inner R' o = ∑' opt, next E opt · M opt o` (`PMF.bind_apply`).
    have hinner_o : ∀ o : Option (Label × PMF State),
        inner R' o = ∑' opt : Option (Label × PMF (PMF State)),
          (pe'.scheduler.next E) opt * (M opt) o := by
      intro o; rw [hinner]; simp only; rw [PMF.bind_apply]
    -- Swap `∑' μ ∑' opt`, so the `opt`-sum is outer.
    calc (∑' μ : PMF State, inner R' (some (l, μ)) * φ μ)
        = ∑' μ : PMF State, ∑' opt : Option (Label × PMF (PMF State)),
            (pe'.scheduler.next E) opt * ((M opt) (some (l, μ)) * φ μ) := by
          refine tsum_congr (fun μ => ?_)
          rw [hinner_o (some (l, μ)), ← ENNReal.tsum_mul_right]
          exact tsum_congr (fun opt => by ring)
      _ = ∑' opt : Option (Label × PMF (PMF State)),
            (pe'.scheduler.next E) opt
              * (∑' μ : PMF State, (M opt) (some (l, μ)) * φ μ) := by
          rw [ENNReal.tsum_comm]
          exact tsum_congr (fun opt => by rw [ENNReal.tsum_mul_left])
      -- Reindex the `opt`-sum onto `ω` via the injection `ω ↦ some (l, ω)`: the `none` and
      -- `some (l'≠l, ω)` summands integrate to `0` (their `M` output lands in `some (l', ·)`).
      _ = ∑' ω : PMF (PMF State),
            (pe'.scheduler.next E) (some (l, ω))
              * (∑' μ : PMF State,
                  (M (some (l, ω))) (some (l, μ)) * φ μ) := by
          refine tsum_eq_tsum_of_ne_zero_bij (fun ω => some (l, ω.1)) ?_ ?_ ?_
          · intro a b hab
            simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hab
            exact Subtype.ext hab
          · -- support ⊆ range: a nonzero `opt`-summand forces `opt = some (l, ω)`.
            intro opt hopt
            rw [Function.mem_support] at hopt
            match opt with
            | none =>
                exact absurd (by simp [hM] : (pe'.scheduler.next E) none
                    * (∑' μ : PMF State, (M none) (some (l, μ)) * φ μ) = 0) hopt
            | some (l', ω) =>
                by_cases hll : l' = l
                · subst hll; exact ⟨⟨ω, by
                    simp only [Function.mem_support]; exact hopt⟩, rfl⟩
                · -- `M (some (l', ω)) (some (l, μ)) = 0` since `some (l, μ) ≠ some (l', μ')`.
                  exfalso; apply hopt
                  have hMzero : ∀ μ : PMF State, (M (some (l', ω))) (some (l, μ)) = 0 := by
                    intro μ
                    simp only [hM, PMF.map_apply]
                    refine ENNReal.tsum_eq_zero.mpr (fun μ' => ?_)
                    rw [if_neg (by simp [Ne.symm hll])]
                  have hsum0 : (∑' μ : PMF State, (M (some (l', ω))) (some (l, μ)) * φ μ) = 0 :=
                    ENNReal.tsum_eq_zero.mpr (fun μ => by rw [hMzero μ, zero_mul])
                  rw [hsum0, mul_zero]
          · intro ω; rfl
      -- The inner `μ`-integral of the `map`: change of variables + the `bind id` reduction.
      _ = ∑' ω : PMF (PMF State),
            (pe'.scheduler.next E) (some (l, ω))
              * ∑' q : State,
                  ((pe'.distFairHyperKernel F E l ω s₀).bind id) q * g q := by
          refine tsum_congr (fun ω => ?_)
          congr 1
          -- `∑' μ, (map (some(l,·)) (dfhk E l ω s₀)) (some(l,μ)) · φ μ = ∑' μ, (dfhk) μ · φ μ`.
          have hmap : ∀ μ : PMF State,
              (M (some (l, ω))) (some (l, μ))
                = (pe'.distFairHyperKernel F E l ω s₀) μ := by
            intro μ
            simp only [hM, PMF.map_apply]
            rw [tsum_eq_single μ (fun μ' hμ' => by
              rw [if_neg (by simp [Ne.symm hμ'])]), if_pos rfl]
          simp only [hmap, hφ]
          -- `∑' μ, (dfhk) μ · (∑' s', μ s' · g s') = ∑' q, ((dfhk).bind id) q · g q`.
          simp only [PMF.bind_apply, id_eq]
          rw [show (∑' q : State,
                (∑' ν : PMF State, (pe'.distFairHyperKernel F E l ω s₀) ν * ν q) * g q)
              = ∑' q : State, ∑' ν : PMF State,
                  (pe'.distFairHyperKernel F E l ω s₀) ν * (ν q * g q) from
            tsum_congr (fun q => by rw [← ENNReal.tsum_mul_right]
                                    exact tsum_congr (fun ν => by ring))]
          rw [ENNReal.tsum_comm]
          refine tsum_congr (fun ν => ?_)
          rw [ENNReal.tsum_mul_left]
  simp only [hQ]
  -- **Step 4.** Pull `m⁻¹` out of the `R'`-sum:
  --   `∑' R', cone R' · m⁻¹ · Demit = m⁻¹ · ∑' R', cone · Demit`.
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr (fun R' => ?_)
  simp only [hcone]
  ring

/-! ### The resolved-cone step washout (crux A residual) and its projective-consistency gap

**(RS) — the resolved-cone step washout.** For every label list `labs`, label `l` and `g`, the
`g`-integrated appended-step level mass of the `.average`d μ-reading witness
`AV := (PE'.lowerFairR F).average` equals `AV`'s level mass at `labs` against the *per-state*
one-step functional

  `Hfun s := ∑' E, pe'.beliefTC labs s E · (∑' ω, pe'.scheduler.next E (some (l, ω))
      · (∑' q, ((dfhk E l ω s).bind id) q · g q))`

of the forgetful belief execution `pe' := PE'.average.distFToDist F` and its fairness-revealing
kernel `dfhk := pe'.distFairHyperKernel F`. This is the resolved analogue of the (mechanical) `hL`
step of `lowerWith_labProb_eq_aux`, but on the *resolved* witness the analogous per-history one-step
identity is **false**: unfolding `AV.labMass (labs ++ [l])` de-averages to a `LF.probOfR`-weighted
sum over resolved runs `r'` (`LF := PE'.lowerFairR F`) of
`∑'_μ (lowerFairRSched F PE').next r' (some (l, μ)) · (∑'_{s'} μ s' · g s')`, in which
`lowerFairRSched.next` samples the `RCoherentTL r'`-*filtered* resolved cone `beliefTCR` (carrying
the per-run renormaliser `1/m(r')`, `m(r') := ∑'_{RCoherentTL r'} beliefTCR`). The filter
renormaliser redistributes mass *across* the extension states of a fixed history and cancels only
once summed over the whole `LF.probOfR`-weighted `r'`-fibre (a rational toy pins the per-`r'` gap at
`70/13 ≠ 6`; see the module history). Matching the RHS `AV.labMass labs Hfun` — which is the
*unfiltered* belief cone read through `probOf_average`/`beliefTCR_map_toExec` and pushed to the
`ω.bind id` post-marginal via `distFairHyperKernel_decomp_gsum` — requires the label-summed
consistency (a martingale/disintegration property) of the resolved cone `probOfR` against the belief
`beliefTCR`, cancelling the `m(r')` filter renormaliser (`beliefTCR_normalize_cancel`). That
renormaliser telescoping along the resolved path `probOfR` (no plain-cone analogue exists) is
precisely what remains open — and is now isolated, `g`/`Demit`/`lowerFairRSched`/`average`-free, as
the single gap `lowerFairR_projective_consistency` below, from which the washout is proven. -/

open Classical in
/-- **(PC) — the projective-consistency gap (the strictly-sharper single residual).**
This is the washout `(†)` after *all* of the `lowerFairRSched`/`average`/`labMass` bookkeeping and
the `distFairHyperKernel`/`g` post-marginal integration are discharged (via the Phase-1 bricks and
`beliefTCR_map_toExec`), leaving a statement about the μ-reading posterior `lowerFairR.probOfR`, the
resolved cone `beliefTCR`, the time-local coherence `RCoherentTL`, and the coherence-restricted
renormaliser `m(r')`. The post-weight family `D : State → ResolvedExec (PMF State) Label → ENNReal`
is *exactly* the discharged `Demit`-values (pinned by `hD`, so this gap is **equivalent** to the
washout, not a stronger claim), read at the end-belief `s₀` and the sampled resolved belief-run
`R'`. The claim: the `lowerFairR.probOfR`-weighted sum over the terminating concrete runs `r'` at
label list `labs`, of the **filtered-renormalised** cone-average of `D`, equals the same sum of the
**unfiltered** cone-average of `D`:

  `∑'_{r' term, labs} probOfR r' · m(r')⁻¹`
    `· ∑'_{R'} ⟦RCoherentTL r' R'⟧ · beliefTCR(labs,s₀) R' · D s₀ R'`
    `= ∑'_{r' term, labs} probOfR r' · ∑'_{R'} beliefTCR(labs,s₀) R' · D s₀ R'`,

with `s₀ := r'.endState`, `m(r') := ∑'_{R'} ⟦RCoherentTL r' R'⟧·beliefTCR(labs,s₀) R'` (the
coherence-restricted cone mass, `= 0` handled by the `dif`-guard: the witness then halts and both
summands vanish). Per-`r'` these two cone-averages differ (filter + renormaliser redistribute mass;
a rational toy pins the gap at `70/13 ≠ 6`); the claim is that they **wash out** once summed over
the whole `probOfR`-weighted `r'`-fibre. This is exactly the label-summed martingale/disintegration
consistency of `probOfR` against `beliefTCR` — the renormaliser telescoping along the resolved path
(`beliefTCR_normalize_cancel` cancels each `m(r'.take k)` against the restricted cone mass of the
`k`-th step). Strictly sharper than the washout: the `lowerFairRSched` emission, the `average`,
`labMass`, and `beliefTC` (pushed to `beliefTCR`) are all discharged; only the `probOfR`/`beliefTCR`
projective consistency of the (still `g`-parametrised, `Demit`-shaped) post-weight `D` remains. -/
private theorem lowerFairR_projective_consistency {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (labs : List Label) (l : Label) (g : State → ENNReal)
    (D : State → ResolvedExec (PMF State) Label → ENNReal)
    (hD : ∀ (s₀ : State) (R' : ResolvedExec (PMF State) Label),
      D s₀ R' = ∑' ω : PMF (PMF State),
        (PE'.average.distFToDist F).scheduler.next (ResolvedExec.toExec R') (some (l, ω))
          * ∑' q : State,
              (((PE'.average.distFToDist F).distFairHyperKernel F
                  (ResolvedExec.toExec R') l ω s₀).bind id) q * g q) :
    (∑' r' : ResolvedExec State Label,
        dite (r'.trans.Terminates ∧
            (ResolvedExec.toExec r').trans.map Prod.fst = Seq.ofList labs)
          (fun h =>
            (PE'.lowerFairR F).probOfR r' h.1
              * (dite ((∑' R', Set.indicator {R' | PE'.RCoherentTL F r' R'}
                    (PE'.beliefTCR F labs
                      ((ResolvedExec.toExec r').endState
                        ((ResolvedExec.toExec_terminates_iff r').mpr h.1))) R') ≠ 0)
                  (fun h0 => (∑' R', Set.indicator {R' | PE'.RCoherentTL F r' R'}
                        (PE'.beliefTCR F labs
                          ((ResolvedExec.toExec r').endState
                            ((ResolvedExec.toExec_terminates_iff r').mpr h.1))) R')⁻¹
                      * ∑' R' : ResolvedExec (PMF State) Label,
                          Set.indicator {R' | PE'.RCoherentTL F r' R'}
                            (PE'.beliefTCR F labs
                              ((ResolvedExec.toExec r').endState
                                ((ResolvedExec.toExec_terminates_iff r').mpr h.1))) R'
                          * D ((ResolvedExec.toExec r').endState
                                ((ResolvedExec.toExec_terminates_iff r').mpr h.1)) R')
                  (fun _ => 0)))
          (fun _ => 0))
      = ∑' r' : ResolvedExec State Label,
          dite (r'.trans.Terminates ∧
              (ResolvedExec.toExec r').trans.map Prod.fst = Seq.ofList labs)
            (fun h =>
              (PE'.lowerFairR F).probOfR r' h.1
                * ∑' R' : ResolvedExec (PMF State) Label,
                    PE'.beliefTCR F labs
                      ((ResolvedExec.toExec r').endState
                        ((ResolvedExec.toExec_terminates_iff r').mpr h.1)) R'
                    * D ((ResolvedExec.toExec r').endState
                          ((ResolvedExec.toExec_terminates_iff r').mpr h.1)) R')
            (fun _ => 0) := by
  sorry

open Classical in
/-- **(RS) — the resolved-cone step washout, PROVEN from the projective-consistency gap
`lowerFairR_projective_consistency`.** All of the `lowerFairRSched`/`distFairHyperKernel`/`g`/
`average`/`labMass` reductions are discharged here mechanically via the Phase-1 bricks
(`lowerFairR_average_labMass_append_resolved`, `average_labMass_state`,
`lowerFairR_emission_integral`) and `beliefTCR_map_toExec`; the only remaining content is the
projective consistency `(PC)`. -/
private theorem lowerFairR_average_step_washout {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (labs : List Label) (l : Label) (g : State → ENNReal) :
    ((PE'.lowerFairR F).average).labMass (labs ++ [l]) g
      = ((PE'.lowerFairR F).average).labMass labs
          (fun s => ∑' E : AlterSeq (PMF State) Label,
            (PE'.average.distFToDist F).beliefTC labs s E *
              (∑' ω : PMF (PMF State),
                (PE'.average.distFToDist F).scheduler.next E (some (l, ω)) *
                  (∑' q : State,
                    (((PE'.average.distFToDist F).distFairHyperKernel F E l ω s).bind id) q
                      * g q))) := by
  classical
  set pe' := PE'.average.distFToDist F with hpe'
  -- The discharged post-weight family: `D s₀ R' := Demit (toExec R') s₀`.
  set D : State → ResolvedExec (PMF State) Label → ENNReal := fun s₀ R' =>
    ∑' ω : PMF (PMF State),
      pe'.scheduler.next (ResolvedExec.toExec R') (some (l, ω))
        * ∑' q : State,
            ((pe'.distFairHyperKernel F (ResolvedExec.toExec R') l ω s₀).bind id) q * g q
    with hD
  -- **LHS.** De-average the appended step onto the `r'`-fibre, then rewrite `B(r')` via brick 3.
  rw [lowerFairR_average_labMass_append_resolved F PE' labs l g]
  have hLHS : (∑' r' : ResolvedExec State Label,
        dite (r'.trans.Terminates ∧
            (ResolvedExec.toExec r').trans.map Prod.fst = Seq.ofList labs)
          (fun h => (PE'.lowerFairR F).probOfR r' h.1
              * (∑' μ : PMF State, (PE'.lowerFairR F).scheduler.next r' (some (l, μ))
                  * (∑' s' : State, μ s' * g s')))
          (fun _ => 0))
      = ∑' r' : ResolvedExec State Label,
          dite (r'.trans.Terminates ∧
              (ResolvedExec.toExec r').trans.map Prod.fst = Seq.ofList labs)
            (fun h =>
              (PE'.lowerFairR F).probOfR r' h.1
                * (dite ((∑' R', Set.indicator {R' | PE'.RCoherentTL F r' R'}
                      (PE'.beliefTCR F labs
                        ((ResolvedExec.toExec r').endState
                          ((ResolvedExec.toExec_terminates_iff r').mpr h.1))) R') ≠ 0)
                    (fun h0 => (∑' R', Set.indicator {R' | PE'.RCoherentTL F r' R'}
                          (PE'.beliefTCR F labs
                            ((ResolvedExec.toExec r').endState
                              ((ResolvedExec.toExec_terminates_iff r').mpr h.1))) R')⁻¹
                        * ∑' R' : ResolvedExec (PMF State) Label,
                            Set.indicator {R' | PE'.RCoherentTL F r' R'}
                              (PE'.beliefTCR F labs
                                ((ResolvedExec.toExec r').endState
                                  ((ResolvedExec.toExec_terminates_iff r').mpr h.1))) R'
                            * D ((ResolvedExec.toExec r').endState
                                  ((ResolvedExec.toExec_terminates_iff r').mpr h.1)) R')
                    (fun _ => 0)))
            (fun _ => 0) := by
    refine tsum_congr (fun r' => ?_)
    by_cases hc : r'.trans.Terminates ∧
        (ResolvedExec.toExec r').trans.map Prod.fst = Seq.ofList labs
    · rw [dif_pos hc, dif_pos hc]
      congr 1
      -- `r'.toExec` terminates; its own label list is `labs`; its end-belief-state is `s₀`.
      have h_term : (ResolvedExec.toExec r').trans.Terminates :=
        (ResolvedExec.toExec_terminates_iff r').mpr hc.1
      -- The witness scheduler's own label list at `r'` is `labs` (from `hc.2`).
      have hlabs_eq : ((ResolvedExec.toExec r').trans.toList h_term).map Prod.fst = labs := by
        have hh := hc.2
        rw [← Stream'.Seq.ofList_toList (ResolvedExec.toExec r').trans h_term,
          map_ofList_gen] at hh
        exact Stream'.Seq.ofList_injective hh
      by_cases h0 : (∑' R', Set.indicator {R' | PE'.RCoherentTL F r' R'}
          (PE'.beliefTCR F labs
            ((ResolvedExec.toExec r').endState h_term)) R') ≠ 0
      · rw [dif_pos h0]
        -- Apply brick 3 (`lowerFairR_emission_integral`), matching the label list via `hlabs_eq`.
        have hemit := PE'.lowerFairR_emission_integral F r' l g h_term (by
          rw [hlabs_eq]; exact h0)
        rw [hlabs_eq] at hemit
        rw [hemit, hD]
      · rw [dif_neg h0]
        -- `m(r') = 0` ⇒ the witness halts, so `next (some (l, μ)) = 0`, so the `μ`-integral is `0`.
        refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
        have hz : (PE'.lowerFairR F).scheduler.next r' (some (l, μ)) = 0 := by
          change (PE'.lowerFairRSched F).next r' (some (l, μ)) = 0
          unfold ResolvedProbabilisticExecution.lowerFairRSched
          simp only
          rw [dif_pos h_term, dif_neg (by rw [hlabs_eq]; exact h0)]
          rw [PMF.pure_apply, if_neg (by simp)]
        rw [hz, zero_mul]
    · rw [dif_neg hc, dif_neg hc]
  rw [hLHS]
  -- **RHS.** De-average the state functional onto the `r'`-fibre, then push `beliefTC` to
  -- `beliefTCR` along `toExec` (`beliefTCR_map_toExec`), matching the unfiltered cone-average
  -- of `D`.
  rw [average_labMass_state (PE'.lowerFairR F) labs (fun s =>
    ∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
      (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
        (∑' q : State, ((pe'.distFairHyperKernel F E l ω s).bind id) q * g q)))]
  have hRHS : (∑' r' : ResolvedExec State Label,
        dite (r'.trans.Terminates ∧
            (ResolvedExec.toExec r').trans.map Prod.fst = Seq.ofList labs)
          (fun h => (PE'.lowerFairR F).probOfR r' h.1
              * (fun s => ∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
                  (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                    (∑' q : State, ((pe'.distFairHyperKernel F E l ω s).bind id) q * g q)))
                ((ResolvedExec.toExec r').endState
                  ((ResolvedExec.toExec_terminates_iff r').mpr h.1)))
          (fun _ => 0))
      = ∑' r' : ResolvedExec State Label,
          dite (r'.trans.Terminates ∧
              (ResolvedExec.toExec r').trans.map Prod.fst = Seq.ofList labs)
            (fun h =>
              (PE'.lowerFairR F).probOfR r' h.1
                * ∑' R' : ResolvedExec (PMF State) Label,
                    PE'.beliefTCR F labs
                      ((ResolvedExec.toExec r').endState
                        ((ResolvedExec.toExec_terminates_iff r').mpr h.1)) R'
                    * D ((ResolvedExec.toExec r').endState
                          ((ResolvedExec.toExec_terminates_iff r').mpr h.1)) R')
            (fun _ => 0) := by
    refine tsum_congr (fun r' => ?_)
    by_cases hc : r'.trans.Terminates ∧
        (ResolvedExec.toExec r').trans.map Prod.fst = Seq.ofList labs
    · rw [dif_pos hc, dif_pos hc]
      congr 1
      set s₀ := (ResolvedExec.toExec r').endState
        ((ResolvedExec.toExec_terminates_iff r').mpr hc.1) with hs₀
      simp only
      -- `Hfun s₀ = ∑' E, beliefTC(labs,s₀) E · D s₀'-of-E`, and `beliefTC = beliefTCR.map toExec`.
      rw [← PE'.beliefTCR_map_toExec F labs s₀]
      rw [hD]
      -- `∑' E, (beliefTCR.map toExec) E · f E = ∑' R', beliefTCR R' · f (toExec R')`.
      simp only [PMF.map_apply]
      rw [show (∑' E : AlterSeq (PMF State) Label,
            (∑' R', if E = ResolvedExec.toExec R' then (PE'.beliefTCR F labs s₀) R' else 0)
              * (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                  (∑' q : State, ((pe'.distFairHyperKernel F E l ω s₀).bind id) q * g q)))
          = ∑' (E : AlterSeq (PMF State) Label) (R' : ResolvedExec (PMF State) Label),
              (if E = ResolvedExec.toExec R' then (PE'.beliefTCR F labs s₀) R' else 0)
                * (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                    (∑' q : State, ((pe'.distFairHyperKernel F E l ω s₀).bind id) q * g q))
          from tsum_congr (fun E => by rw [ENNReal.tsum_mul_right])]
      rw [ENNReal.tsum_comm]
      refine tsum_congr (fun R' => ?_)
      rw [tsum_eq_single (ResolvedExec.toExec R') (fun E hE => by
        rw [if_neg hE, zero_mul]), if_pos rfl]
    · rw [dif_neg hc, dif_neg hc]
  rw [hRHS]
  -- Both sides are now the two sides of the projective-consistency gap (`D` is the `Demit`-family).
  exact lowerFairR_projective_consistency F PE' labs l g D (fun s₀ R' => by rw [hD])

open Classical in
/-- **Trace faithfulness (the crux A statement).** Direct `reverseRecOn` induction comparing the
`.average`d μ-reading witness `AV := (PE'.lowerFairR F).average` to the μ-blind trace-cone witness
`W := pe'.lowerWith dfhk` (`pe' := PE'.average.distFToDist F`, `dfhk := pe'.distFairHyperKernel F`),
mirroring `ProbabilisticExecution.lowerWith_labProb_eq_aux`.

* `nil`: both level masses are `∑' i, (PE'.initState.bind id) i · g i`, since
  `AV.initState = W.initState = PE'.initState.bind id` (`lowerFairR.initState = PE'.initState.bind
  id` definitionally, `average` preserves `initState`, and `W.initState = pe'.initState.bind id`
  with `pe'.initState = PE'.initState`).
* `append_singleton`: with the per-state one-step functional `Hfun` (identical to
  `lowerWith_labProb_eq_aux`'s, with `K := dfhk`), the μ-blind side reduces `W.labMass (labs ++ [l])
  g = W.labMass labs Hfun` mechanically (`labMass_step` + `lowerWith_kernel_g_sum` per history,
  `hLW`), the resolved side reduces `AV.labMass (labs ++ [l]) g = AV.labMass labs Hfun` by the
  resolved-cone step washout (`lowerFairR_average_step_washout`, `hRS` — the crux-A residual), and
  the induction hypothesis `ih` closes `AV.labMass labs Hfun = W.labMass labs Hfun`. -/
private theorem lowerFairR_average_labMass_eq_lowerWith {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (labs : List Label) (g : State → ENNReal) :
    ((PE'.lowerFairR F).average).labMass labs g
      = ((PE'.average.distFToDist F).lowerWith
            ((PE'.average.distFToDist F).distFairHyperKernel F)
            ((PE'.average.distFToDist F).distFairHyperKernel_valid F)).labMass labs g := by
  classical
  set pe' := PE'.average.distFToDist F with hpe'
  set dfhk := pe'.distFairHyperKernel F with hdfhk
  have hvalid : LowerKernelValid pe' dfhk := pe'.distFairHyperKernel_valid F
  set AV := (PE'.lowerFairR F).average with hAV
  set W := pe'.lowerWith dfhk hvalid with hW
  -- Direct induction comparing `AV` to `W`; no intermediate `lowerWith_labProb_eq_aux`.
  revert g
  induction labs using List.reverseRecOn with
  | nil =>
      intro g
      rw [AV.labMass_nil g, W.labMass_nil g]
      -- Both initial distributions are `PE'.initState.bind id`.
      have hinitAV : AV.initState = pe'.initState.bind id := rfl
      have hinitW : W.initState = pe'.initState.bind id := rfl
      rw [hinitAV, hinitW]
  | append_singleton labs l ih =>
      intro g
      -- The per-state one-step functional `Hfun` (identical to `lowerWith_labProb_eq_aux`'s `hL`).
      set Hfun : State → ENNReal := fun s =>
          ∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
            (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
              (∑' q : State, ((dfhk E l ω s).bind id) q * g q)) with hHfun
      -- (W side, mechanical) — copy of `lowerWith_labProb_eq_aux`'s `hL` with `K := dfhk`.
      have hLW : W.labMass (labs ++ [l]) g = W.labMass labs Hfun := by
        rw [W.labMass_step labs l g]
        unfold ProbabilisticExecution.labMass
        refine tsum_congr (fun e' => ?_)
        by_cases hc : e'.trans.Terminates ∧ e'.trans.map Prod.fst = Seq.ofList labs
        · rw [dif_pos hc, dif_pos hc]; congr 1
          have map_ofList : ∀ (L : List (Label × State)),
              (Seq.ofList L).map Prod.fst = Seq.ofList (L.map Prod.fst) := by
            intro L; induction L with
            | nil => simp [Stream'.Seq.ofList_nil, Stream'.Seq.map_nil]
            | cons a L ihL => rw [Stream'.Seq.ofList_cons, Stream'.Seq.map_cons, ihL,
                List.map_cons, Stream'.Seq.ofList_cons]
          have h_labs : (e'.trans.toList hc.1).map Prod.fst = labs := by
            apply Stream'.Seq.ofList_injective
            rw [← map_ofList, Stream'.Seq.ofList_toList e'.trans hc.1]; exact hc.2
          rw [hW, pe'.lowerWith_kernel_g_sum dfhk hvalid labs l g e' hc.1 h_labs
            (e'.endState hc.1) rfl]
        · rw [dif_neg hc, dif_neg hc]
      -- (AV side, the crux residual) — the resolved-cone step washout.
      have hRS : AV.labMass (labs ++ [l]) g = AV.labMass labs Hfun := by
        rw [hAV, hHfun, hpe', hdfhk]
        exact lowerFairR_average_step_washout F PE' labs l g
      rw [hRS, hLW, ih Hfun]

/-- **Trace-cone invariant (`g`-indexed) for the μ-reading witness's average.** The `.average`d
μ-reading witness `(PE'.lowerFairR F).average` assigns the same `g`-integrated level mass to
`sys`-histories with label list `labs` as `pe' := PE'.average.distFToDist F` assigns to
`𝒟(sys)`-histories, integrated against the `bind id` push-forward `μ ↦ ∑' s, μ s · g s`.

Proven in two honest steps: (1) `lowerFairR_average_labMass_eq_lowerWith` — the μ-reading average
has the same `g`-integrated level mass as the μ-blind trace-cone witness `pe'.lowerWith
(distFairHyperKernel F)` (the label-summed probability-matching identity; the per-history version is
false, see that lemma); (2) `lowerWith_labProb_eq_aux` — the μ-blind witness's level mass equals
`pe'`'s level mass under the `bind id` push-forward. The previous `reverseRecOn` route through a
per-history one-step kernel identity was unsound (that per-`e` identity is false — the `RCoherentTL`
filter renormaliser redistributes mass across the extension states of a fixed trace, cancelling only
at the label-summed level). -/
private theorem lowerFairR_average_labProb_eq_aux {sys : System State Label} (F : Fairness sys)
    (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (labs : List Label) (g : State → ENNReal) :
    ((PE'.lowerFairR F).average).labMass labs g
      = (PE'.average.distFToDist F).labMass labs
          (fun μ : PMF State => ∑' s : State, μ s * g s) := by
  classical
  rw [lowerFairR_average_labMass_eq_lowerWith F PE' labs g,
    (PE'.average.distFToDist F).lowerWith_labProb_eq_aux
      ((PE'.average.distFToDist F).distFairHyperKernel F)
      ((PE'.average.distFToDist F).distFairHyperKernel_valid F)
      ((PE'.average.distFToDist F).distFairHyperKernel_decomp F) labs g]

open Classical in
/-- **`g = 1` slice of `lowerFairR_average_labProb_eq_aux`.** For each label list `labs`, the
`.average`d μ-reading witness assigns the same total `probOf`-mass to `sys`-executions with label
list `labs` as `pe' := PE'.average.distFToDist F` assigns to `𝒟(sys)`-histories. -/
private theorem lowerFairR_average_labProb_eq {sys : System State Label} (F : Fairness sys)
    (PE' : ResolvedProbabilisticExecution (sys.distF F)) (labs : List Label) :
    (∑' e : AlterSeq State Label,
        dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs)
          (fun h => ((PE'.lowerFairR F).average).probOf e h.1) (fun _ => 0))
    = ∑' E : AlterSeq (PMF State) Label,
        dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
          (fun h => (PE'.average.distFToDist F).probOf E h.1) (fun _ => 0) := by
  classical
  have h := lowerFairR_average_labProb_eq_aux F PE' labs (fun _ => 1)
  simpa only [ProbabilisticExecution.labMass, mul_one, PMF.tsum_coe] using h

/-- **Crux A, the trace-summed residual — now a real proof (modulo the one-step invariant).** For a
fixed trace `τ`, the total `avgWeight` that the μ-reading witness `lowerFairR` assigns to the tight
terminating histories with trace `τ` equals the total `probOf` that the μ-blind trace-cone witness
`lowerWith distFairHyperKernel` assigns to them.

The identity holds strictly at the trace-sum level (the per-history append identity is FALSE: the
`PMF.filter` renormaliser redistributes mass across the extension states of the same trace, not
within the fibre of a fixed history). It is discharged here by regrouping both sides by label list
(`traceProb_eq_labProb_sum`), and per label list applying `lowerFairR_average_labProb_eq` (the
`.average`d μ-reading witness's level mass equals `pe'`'s, via the one-step invariant
`lowerFairR_average_kernel_g_sum`) together with `lowerWith_labProb_eq` (the μ-blind witness's level
mass also equals `pe'`'s) — both routing through the plain `pe' := PE'.average.distFToDist F` level
mass, hence equal. No finiteness hypothesis is needed. Consumed directly by
`lowerFairR_traceProbR_eq_lowerCoe` below. -/
private theorem lowerFairR_avgWeight_traceSum_eq_lowerWith {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F)) (τ : Seq Label) :
    (∑' e : {e : AlterSeq State Label //
        e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e},
          (PE'.lowerFairR F).avgWeight e.1 e.2.1)
      = ∑' e : {e : AlterSeq State Label //
          e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e},
          ((PE'.average.distFToDist F).lowerWith
            ((PE'.average.distFToDist F).distFairHyperKernel F)
            ((PE'.average.distFToDist F).distFairHyperKernel_valid F)).probOf e.1 e.2.1 := by
  classical
  set pe' := PE'.average.distFToDist F with hpe'
  set AV := (PE'.lowerFairR F).average with hAV
  -- The LHS is `sys.traceProb AV τ` (each summand `avgWeight = AV.probOf` by `probOf_average`);
  -- the RHS is `sys.traceProb (pe'.lowerWith …) τ` by definition of `traceProb`.
  have hLHS : (∑' e : {e : AlterSeq State Label //
        e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e},
          (PE'.lowerFairR F).avgWeight e.1 e.2.1)
      = sys.traceProb AV τ := by
    unfold System.traceProb
    exact tsum_congr (fun e => ((PE'.lowerFairR F).probOf_average e.1 e.2.1).symm)
  have hRHS : (∑' e : {e : AlterSeq State Label //
        e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e},
          (pe'.lowerWith (pe'.distFairHyperKernel F) (pe'.distFairHyperKernel_valid F)).probOf
            e.1 e.2.1)
      = sys.traceProb (pe'.lowerWith (pe'.distFairHyperKernel F)
          (pe'.distFairHyperKernel_valid F)) τ := rfl
  rw [hLHS, hRHS]
  -- Regroup both `traceProb`s by label list; per label list both level masses route through the
  -- plain `pe'` level mass (`lowerFairR_average_labProb_eq` and `lowerWith_labProb_eq`).
  rw [System.traceProb_eq_labProb_sum sys AV τ,
      System.traceProb_eq_labProb_sum sys (pe'.lowerWith (pe'.distFairHyperKernel F)
        (pe'.distFairHyperKernel_valid F)) τ]
  refine tsum_congr fun labs => ?_
  by_cases h : sys.traceTightLabs τ labs
  · rw [if_pos h, if_pos h, lowerFairR_average_labProb_eq F PE' labs,
      pe'.lowerWith_labProb_eq (pe'.distFairHyperKernel F) (pe'.distFairHyperKernel_valid F)
        (pe'.distFairHyperKernel_decomp F) labs]
  · rw [if_neg h, if_neg h]

/-- **Crux A, the genuine residual: `lowerFairR` and `lowerCoe` realise the same trace
distribution.** This is the one probability-matching fact of crux A, stated against the μ-blind
baseline whose trace is already free (`lowerCoe_traceProbR`). The two resolved witnesses do *not*
agree run-by-run — `lowerFairR` emits via the fairness-revealing `distFairHyperKernel`, `lowerCoe`
via the generic `distHyperKernel`, so a fixed decorated run gets different `probOfR` mass. But the
two kernels share the **same post-marginal** `ω.bind id` (`distFairHyperKernel_decomp` /
`distHyperKernel`'s decomposition), so integrating the `μ`-decorations out — which is exactly what
summing `probOfR` over the `toExec`-fibre of a fixed *trace* does — yields the same mass; and
`beliefTCR_map_toExec` collapses the resolved `beliefTCR` sampling onto the plain `beliefTC` that
`lowerCoe` reads, while the `RCoherentTL r` filter removes no *terminating*-run mass (a finite
`μ`-pattern is always `distFairHyperKernel`-realisable). The whole statement is reduced
(structurally, here) to the single **trace-summed** residual
`lowerFairR_avgWeight_traceSum_eq_lowerWith` — note the reduction is *not* per-history (the
per-history append identity is false; see that residual's docstring). -/
theorem ResolvedProbabilisticExecution.lowerFairR_traceProbR_eq_lowerCoe {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (_hinit : PE'.initState = PMF.pure (sys.distF F).init) (τ : Seq Label) :
    (PE'.lowerFairR F).traceProbR τ = (PE'.lowerCoe F).traceProbR τ := by
  classical
  set pe' := PE'.average.distFToDist F with hpe'
  -- RHS: `lowerCoe` realises `PE'`'s trace, which is the `distFairHyperKernel`-lowering of `pe'`.
  have hRHS : (PE'.lowerCoe F).traceProbR τ
      = sys.traceProb (pe'.lowerWith (pe'.distFairHyperKernel F)
          (pe'.distFairHyperKernel_valid F)) τ := by
    rw [PE'.lowerCoe_traceProbR F τ,
      pe'.lowerWith_traceProb_eq (pe'.distFairHyperKernel F) (pe'.distFairHyperKernel_valid F)
        (pe'.distFairHyperKernel_decomp F) τ,
      ← ProbabilisticExecution.distFToDist_traceProb F PE'.average τ, PE'.traceProb_average τ]
  rw [hRHS, ← (PE'.lowerFairR F).traceProbR_eq_sum_avgWeight τ]
  -- Both sides are now sums over the tight terminating trace-`τ` histories. The summands do NOT
  -- match per history (the filter redistributes mass across the extension states of the same
  -- trace); the equality holds only at the trace-sum level (`..._traceSum_eq_lowerWith`).
  unfold System.traceProb
  exact lowerFairR_avgWeight_traceSum_eq_lowerWith F PE' τ

/-- **Crux A: the μ-reading witness realises `PE'`'s trace distribution.** Unlike `lowerCoe` (which
inherits its trace for free from the plain reconstruction), `lowerFairR` *excludes* the
non-liftable (chimera) belief-runs through the `RCoherentTL` filter and redistributes their
label-mass onto the liftable runs. The claim is reduced to the μ-blind baseline by
`lowerFairR_traceProbR_eq_lowerCoe` (the "filter removes no terminating mass" step — the genuine
residual), after which `lowerCoe_traceProbR` closes it for free. Finite runs lift trivially (a
finite `μ`-pattern is always realisable), so **no finiteness hypothesis is needed**. -/
theorem ResolvedProbabilisticExecution.lowerFairR_traceProbR {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (hinit : PE'.initState = PMF.pure (sys.distF F).init) (τ : Seq Label) :
    (PE'.lowerFairR F).traceProbR τ = PE'.traceProbR τ :=
  (PE'.lowerFairR_traceProbR_eq_lowerCoe F hinit τ).trans (PE'.lowerCoe_traceProbR F τ)

/-! ### The halt clause (mechanical residue, documented `sorry`)

`halt_fairDeadlock` is quantified over `Consistent` runs, and this is *not* a genuine crux — it is
reachability bookkeeping. Two branches:
* **Realisable** (restricted belief-mass positive): factors, exactly like `lowerWith_next_none`,
  through a coherent belief-history `E` at which `PE'.average` halts, then the `𝒟f→𝒟` fair-deadlock
  transfer (`PE'.IsFair.halt_fairDeadlock` + `distF_fairDeadlock_belief`, the resolvable
  belief-deadlock transfer) carries the deadlock down to the concrete end-state — pure reuse.
* **Fallback** (`RCoherentTL`-restricted mass `0`, witness emits `PMF.pure none`): **vacuous** on a
  `Consistent` `r`. A consistent run is *generated* by coherent belief-histories, so its restricted
  belief support is non-empty and the fallback never fires; making that formal needs only a
  *qualitative* reachability lemma ("a consistent `r` admits a coherent belief-history" —
  support-level, strictly weaker than crux A's quantitative probability-matching).
Both halves are `[Fintype State]`-free reachability bookkeeping; the clause was never separately
proven for `lowerCoe` either (it lived inside the old bundled `sorry`). Isolated here as a `sorry`,
distinct from the two genuine cruxes. -/

/-- **Resolvability of a reached belief.** Every belief `ν` in the support of a recorded successor
`s' = R.stateAt (n+1)` of a `PE'`-consistent resolved `sys.distF F`-run is `F.Resolvable`: the step
into it is a valid `(sys.distF F)`-step (from `PE'.scheduler.valid`), whose emitted successor
beliefs are all `F.Resolvable` by the `distF` clustering restriction, and the sampled destination
`s'` lies in that emitted `μ.support` (`μ s' ≠ 0` from consistency). -/
private theorem ResolvedProbabilisticExecution.resolvable_of_consistent_step
    {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (R : ResolvedExec (PMF State) Label) (hcons : PE'.Consistent R)
    (n : ℕ) (s : PMF State) (l : Label) (μ : PMF (PMF State)) (s' : PMF State)
    (hstate : R.stateAt n = some s)
    (hget : R.trans.get? n = some ((l, μ), s')) :
    F.Resolvable s' := by
  obtain ⟨hnext, hμs'⟩ := hcons.2 n l μ s' hget
  -- `R.trans` is not terminated at `n` (it has a step there), so `R.take n` has exactly `n` steps.
  have hntn : ¬ R.trans.TerminatedAt n := by
    intro ht; rw [Stream'.Seq.TerminatedAt, hget] at ht; exact absurd ht (by simp)
  have hlen : (Seq.take n R.trans).length = n :=
    Stream'.Seq.length_take_of_le_length
      (fun ht => Nat.le_of_lt (not_le.mp (fun hle => hntn (Stream'.Seq.length_le_iff.mp hle))))
  have htake_term : (R.take n).trans.TerminatedAt n := by
    change (Seq.ofList (Seq.take n R.trans)).get? n = none
    rw [Stream'.Seq.ofList_get?]; exact List.getElem?_eq_none (by rw [hlen])
  have htake_state : (R.take n).stateAt n = some s := by
    rw [take_stateAt R (le_refl n)]; exact hstate
  -- `scheduler.valid` gives the `(sys.distF F)`-step; its `distF` clause is resolvability of `s'`.
  have hstep : (sys.distF F).step s l μ :=
    PE'.scheduler.valid (R.take n) n s htake_term htake_state l μ
      ((PMF.mem_support_iff _ _).mpr hnext)
  exact hstep.2 s' ((PMF.mem_support_iff _ _).mpr hμs')

/-- **The end-belief of a consistent terminating run is resolvable.** If a `PE'`-consistent resolved
`(sys.distF F)`-run `R` terminates, its end-belief `R.endState h` is `F.Resolvable`. Two cases:
* `R` has a last recorded step `((l, μ), ν')`: then `R.endState = ν'` is a recorded successor
  belief, resolvable by `resolvable_of_consistent_step`.
* `R` has no steps (`R.trans = nil`): then `R.endState = R.init`, which lies in the support of
  `PE'.initState = pure (sys.distF F).init = pure (pure sys.init)` by consistency, so it is
  `pure sys.init`, resolvable by `Fairness.resolvable_pure`. -/
private theorem ResolvedProbabilisticExecution.resolvable_of_consistent_endState
    {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (R : ResolvedExec (PMF State) Label) (hcons : PE'.Consistent R)
    (h : R.trans.Terminates)
    (hinit : PE'.initState = PMF.pure (sys.distF F).init) :
    F.Resolvable (R.endState h) := by
  classical
  by_cases hne : R.trans.toList h ≠ []
  · -- Last recorded step: `R.endState` is its successor belief, resolvable via consistency.
    obtain ⟨prev, last, hprev, hsplit, hprevlist, -⟩ :=
      Stream'.Seq.exists_split_last R.trans h hne
    obtain ⟨⟨l, μ⟩, ν'⟩ := last
    have happ : (prev.append (Seq.cons ((l, μ), ν') Seq.nil)).Terminates := hsplit ▸ h
    have hr_eq : R = ⟨R.init, prev.append (Seq.cons ((l, μ), ν') Seq.nil)⟩ := by
      obtain ⟨ri, rt⟩ := R; exact congrArg (AlterSeq.mk ri) hsplit
    -- The recorded last step is at position `Nat.find hprev` (`prev` terminated there).
    have hget : R.trans.get? (Nat.find hprev) = some ((l, μ), ν') := by
      have := Stream'.Seq.get?_append_find hprev (Seq.cons ((l, μ), ν') Seq.nil) 0
      rw [Nat.add_zero, ← hsplit] at this
      rw [this]; rfl
    set n := Nat.find hprev with hn
    -- `R.stateAt n` is `some` of *some* belief (there is a step there, so no earlier termination).
    have hstate_ne : R.stateAt n ≠ none := by
      have hntn : ¬ R.trans.TerminatedAt n := by
        intro ht; rw [Stream'.Seq.TerminatedAt, hget] at ht; exact absurd ht (by simp)
      cases hnc : n with
      | zero => exact Option.some_ne_none R.init
      | succ k =>
        change (R.trans.get? k).map Prod.snd ≠ none
        have hntk : ¬ R.trans.TerminatedAt k := by
          intro ht
          exact hntn (hnc ▸ Stream'.Seq.terminated_stable R.trans (Nat.le_succ k) ht)
        exact fun hc => hntk (Option.map_eq_none_iff.mp hc)
    obtain ⟨s, hstate⟩ := Option.ne_none_iff_exists'.mp hstate_ne
    -- `R.endState h = ν'` (successor of the appended last step).
    have hend : R.endState h = ν' := by
      have hkey := AlterSeq.endState_append_singleton
        (⟨R.init, prev⟩ : AlterSeq (PMF State) (Label × PMF (PMF State))) hprev (l, μ) ν'
      have hcongr : R.endState h
          = (⟨R.init, prev.append (Seq.cons ((l, μ), ν') Seq.nil)⟩
              : ResolvedExec (PMF State) Label).endState happ := by
        cases R; cases hr_eq; rfl
      rw [hcongr]; exact hkey
    rw [hend]
    exact resolvable_of_consistent_step F PE' R hcons n s l μ ν' hstate hget
  · -- No recorded step: `R.endState = R.init ∈ supp(pure (pure sys.init))`, so `= pure sys.init`.
    rw [not_not] at hne
    have hnil : R.trans = Seq.nil := by
      have := Stream'.Seq.ofList_toList R.trans h
      rw [hne, Stream'.Seq.ofList_nil] at this; exact this.symm
    have hend : R.endState h = R.init := AlterSeq.endState_of_trans_nil R hnil h
    have hinit_mem : PE'.initState R.init ≠ 0 := hcons.1
    rw [hinit] at hinit_mem
    have hR_init : R.init = (sys.distF F).init := by
      by_contra hc
      rw [PMF.pure_apply, if_neg hc] at hinit_mem
      exact hinit_mem rfl
    rw [hend, hR_init]
    change F.Resolvable (PMF.pure sys.init)
    exact F.resolvable_pure sys.init

omit [Silent Label] in
/-- **A prefix always terminates by its length.** The length-`k` prefix `r.take k` records at most
`k` transitions, so it terminates at `k` (local copy; unconditional). -/
private theorem take_terminatedAt_le {S L : Type} (r : AlterSeq S L) (k : ℕ) :
    (r.take k).trans.TerminatedAt k := by
  change (Seq.ofList (Seq.take k r.trans)).get? k = none
  rw [Stream'.Seq.ofList_get?]
  exact List.getElem?_eq_none (Nat.le_trans Stream'.Seq.length_take_le (Nat.le_refl _))

omit [Silent Label] in
/-- **Canonical terminating index of a terminating prefix.** For `r` terminating at `N` and
`k ≤ N`, the prefix `r.take k` terminates *exactly* at `k` (positions below `k ≤ N` are genuine
steps). -/
private theorem take_find_of_le {S L : Type} (r : AlterSeq S L) {N : ℕ}
    (h : r.trans.Terminates) (hN : N = Nat.find h) {k : ℕ} (hk : k ≤ N) :
    Nat.find (take_terminates r k) = k := by
  apply le_antisymm
  · exact Nat.find_le (take_terminatedAt_le r k)
  · rw [Nat.le_find_iff]
    intro m hm
    change ¬ (Seq.ofList (Seq.take k r.trans)).get? m = none
    rw [Stream'.Seq.ofList_get?, seq_getElem?_take r.trans k m hm]
    -- position `m < k ≤ N = Nat.find h`, so `r` is not terminated at `m`.
    exact Nat.find_min h (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hm hk) (le_of_eq hN))

omit [Silent Label] in
/-- **End-state of a terminating prefix.** For `r` terminating at `N` and `k ≤ N`, the end-state of
`r.take k` is `r.stateAt k` (the state after `k` transitions). -/
private theorem take_endState_of_le {S L : Type} (r : AlterSeq S L) {N : ℕ}
    (h : r.trans.Terminates) (hN : N = Nat.find h) {k : ℕ} (hk : k ≤ N) {s : S}
    (hs : r.stateAt k = some s) :
    (r.take k).endState (take_terminates r k) = s := by
  have hfind := take_find_of_le r h hN hk
  have heq := AlterSeq.stateAt_find_eq_endState (r.take k) (take_terminates r k)
  rw [hfind, take_stateAt r (Nat.le_refl k), hs] at heq
  exact (Option.some.inj heq).symm

/-- **The coherent resolved-positive lift of the halt clause's last step (the single sharp
residual).** For a `lowerFairR`-consistent terminating run `r` whose last recorded step is at
position `k` (`Nat.find h = k + 1`, `r.trans.get? k = some ((l, μ), s')`, state-before-step
`r.stateAt k = some sk`, with `μ s' ≠ 0`), there **exists** a resolved `PE'`-belief-prefix `w'`
(with an accompanying internal emission `ω`) that

* terminates exactly at `k` (`Nat.find hwT' = k`) with the same label list as `(r.take k).toExec`,
* is time-locally coherent with `r.take k` (`RCoherentTL F (r.take k) w'`),
* carries positive resolved path-mass (`PE'.probOfR w' hwT' ≠ 0`),
* has `sk` in its plain end-belief,
* has its forgetful plain projection `toExec w'` emit `some (l, ω)` with positive *average* mass,
* has positive **resolved** emission mass on that step (`PE'.scheduler.next w' (some (l, ω)) ≠ 0`),
* and realises `μ` through the fairness-revealing kernel at the last-step belief.

This is an **existential over `w'`** — *not* the (false) claim that a *specific* coherent `w`
handed by consistency has positive resolved next. `lowerFairR`-consistency at the last step unfolds
`lowerFairRSched.next (r.take k)` to a coherent, `PE'.probOfR`-positive belief-prefix `w` whose
forgetful average emits `some (l, ω)` positively; by `average_next_some` this average is
`avgWeight⁻¹ · ∑'_{R'' : toExec R'' = toExec w} probOfR R'' · scheduler.next R'' (some (l, ω))`, so
*some* run in the `toExec`-fibre carries positive **resolved** emission — but that mass need not sit
on `w` itself (the internal `ω`s a fibre-mate records are forgotten by `toExec`, so `RCoherentTL`
does not transport along the fibre), which is exactly why the specific-`w` form is unprovable. The
existential form dodges this: it asks only for *a* coherent resolved-positive lift of `r`'s realised
last step, which exists because `r`'s trace is genuinely achievable. It is *strictly weaker* than
crux A (`lowerFairR_projective_consistency` / `lowerFairR_traceProbR_eq_lowerCoe`): the quantitative
probability-matching supplies it as a corollary (equal masses force a positive coherent resolved
witness), but it is not mechanical. Everything except the resolved-next positivity is discharged
below from consistency; only `PE'.scheduler.next w' (some (l, ω)) ≠ 0` stays a `sorry` (the genuine
qualitative resolved-reachability content of `r`'s realised final step). The coherent length-`N`
belief-run with positive `beliefTCRw` is then assembled in
`lowerFairR_halt_nonnil_coherent_witness` from this lift. -/
private theorem lowerFairR_halt_coherent_resolved_lift {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (r : ResolvedExec State Label) (h : r.trans.Terminates)
    (hcons : (PE'.lowerFairR F).Consistent r)
    (hinit : PE'.initState = PMF.pure (sys.distF F).init)
    (k : ℕ) (l : Label) (μ : PMF State) (s' sk : State)
    (hkfind : Nat.find h = k + 1)
    (hrget : r.trans.get? k = some ((l, μ), s'))
    (hsk : r.stateAt k = some sk)
    (hnext : (PE'.lowerFairR F).scheduler.next (r.take k) (some (l, μ)) ≠ 0)
    (hμs' : μ s' ≠ 0) :
    ∃ (w' : ResolvedExec (PMF State) Label) (ω : PMF (PMF State)) (hwT' : w'.trans.Terminates),
      Nat.find hwT' = k ∧
      (ResolvedExec.toExec w').trans.map Prod.fst
        = (ResolvedExec.toExec (r.take k)).trans.map Prod.fst ∧
      PE'.RCoherentTL F (r.take k) w' ∧
      PE'.probOfR w' hwT' ≠ 0 ∧
      sk ∈ ((ResolvedExec.toExec w').endState
        ((ResolvedExec.toExec_terminates_iff w').mpr hwT')).support ∧
      some (l, ω) ∈ ((PE'.average.distFToDist F).scheduler.next (ResolvedExec.toExec w')).support ∧
      PE'.scheduler.next w' (some (l, ω)) ≠ 0 ∧
      μ ∈ ((PE'.average.distFToDist F).distFairHyperKernel F
        (ResolvedExec.toExec w') l ω sk).support := by
  classical
  set pe' := PE'.average.distFToDist F with hpe'
  have hkN : k < Nat.find h := by rw [hkfind]; exact Nat.lt_succ_self k
  -- `(r.take k).toExec` terminates (finite prefix); its label list is `labs'` and its end-state is
  -- `sk = r.stateAt k` (`take_endState_of_le`).
  have hTe : (ResolvedExec.toExec (r.take k)).trans.Terminates :=
    (ResolvedExec.toExec_terminates_iff (r.take k)).mpr (take_terminates r k)
  set labs' := ((ResolvedExec.toExec (r.take k)).trans.toList hTe).map Prod.fst with hlabs'
  have hs₀_sk : (ResolvedExec.toExec (r.take k)).endState hTe = sk := by
    have hfind : Nat.find hTe = k := by
      have h1 : Nat.find hTe = Nat.find (take_terminates r k) :=
        Nat.find_congr' (fun {m} => ResolvedExec.toExec_terminatedAt_iff (r.take k) m)
      rw [h1, take_find_of_le r h rfl (Nat.le_of_lt hkN)]
    have heq := AlterSeq.stateAt_find_eq_endState (ResolvedExec.toExec (r.take k)) hTe
    rw [hfind, ResolvedExec.toExec_stateAt,
      take_stateAt r (Nat.le_refl k), hsk] at heq
    exact (Option.some.inj heq).symm
  -- Unfold the μ-reading scheduler emission at `r.take k` (mirror of `lowerFairRSched.valid`).
  have hmem : some (l, μ) ∈ ((PE'.lowerFairR F).scheduler.next (r.take k)).support :=
    (PMF.mem_support_iff _ _).mpr hnext
  change some (l, μ) ∈
    (open Classical in
      if h_term : (ResolvedExec.toExec (r.take k)).trans.Terminates then
        if h0 : (∑' R', Set.indicator {R' | PE'.RCoherentTL F (r.take k) R'}
            (PE'.beliefTCR F (((ResolvedExec.toExec (r.take k)).trans.toList h_term).map Prod.fst)
              ((ResolvedExec.toExec (r.take k)).endState h_term)) R') ≠ 0 then
          ((PE'.beliefTCR F (((ResolvedExec.toExec (r.take k)).trans.toList h_term).map Prod.fst)
              ((ResolvedExec.toExec (r.take k)).endState h_term)).filter
              {R' | PE'.RCoherentTL F (r.take k) R'} _).bind (fun R' =>
            ((PE'.average.distFToDist F).scheduler.next (ResolvedExec.toExec R')).bind (fun opt =>
              match opt with
              | none         => PMF.pure none
              | some (l', ω) =>
                ((PE'.average.distFToDist F).distFairHyperKernel F (ResolvedExec.toExec R') l' ω
                    ((ResolvedExec.toExec (r.take k)).endState h_term)).map
                    (fun μ' => some (l', μ'))))
        else PMF.pure none
      else PMF.pure none).support at hmem
  rw [dif_pos hTe] at hmem
  split_ifs at hmem with h0
  swap
  · rw [PMF.mem_support_pure_iff] at hmem; exact absurd hmem (by simp)
  rw [PMF.mem_support_bind_iff] at hmem
  obtain ⟨w, hw_filter, hw_emit⟩ := hmem
  rw [PMF.mem_support_filter_iff] at hw_filter
  obtain ⟨hw_coh, hw_belief⟩ := hw_filter
  -- Fold `labs'` and `sk` into the cone membership and the guard.
  rw [← hlabs', hs₀_sk] at hw_belief h0
  -- The `w`-emission is `some (l, μ)`: unfold the inner `bind` to get an emission `some (l, ω)`
  -- and the kernel membership of `μ`.
  rw [hs₀_sk, PMF.mem_support_bind_iff] at hw_emit
  obtain ⟨opt, hopt_supp, hμ_supp⟩ := hw_emit
  -- The `match` forces `opt = some (l, ω)`.
  set E := ResolvedExec.toExec w with hE
  obtain (_ | ⟨l', ω⟩) := opt
  · rw [PMF.mem_support_pure_iff] at hμ_supp; exact absurd hμ_supp (by simp)
  rw [PMF.mem_support_map_iff] at hμ_supp
  obtain ⟨μ', hμ'_supp, hμ'_eq⟩ := hμ_supp
  -- `some (l', μ') = some (l, μ)` ⟹ `l' = l`, `μ' = μ`.
  rw [Option.some.injEq, Prod.mk.injEq] at hμ'_eq
  obtain ⟨hll', hμμ'⟩ := hμ'_eq
  subst hll'
  rw [hμμ'] at hμ'_supp
  -- **The four facts about `w`.** `w` terminates, its `toExec`-label list is `labs'`, `sk` lies in
  -- its end-belief, and it has positive resolved path-mass.  When the cone mass is positive this is
  -- `beliefTCR_support`; when it is `0`, `beliefTCR = pure ⟨pure sk, nil⟩` so `w = ⟨pure sk, nil⟩`
  -- (length 0), which then forces `labs' = []` and supplies the four facts explicitly.
  obtain ⟨hwT, hwlab, hsk_mem, hwpm⟩ :
      ∃ hwT : w.trans.Terminates,
        (ResolvedExec.toExec w).trans.map Prod.fst = Seq.ofList labs' ∧
        sk ∈ ((ResolvedExec.toExec w).endState
          ((ResolvedExec.toExec_terminates_iff w).mpr hwT)).support ∧
        PE'.probOfR w hwT ≠ 0 := by
    by_cases hcone : (∑' R'', PE'.beliefTCRw F labs' sk R'') ≠ 0
    · exact PE'.beliefTCR_support F labs' sk hcone w hw_belief
    · rw [not_not] at hcone
      have hbtcr : PE'.beliefTCR F labs' sk = PMF.pure ⟨PMF.pure sk, Seq.nil⟩ := by
        rw [ResolvedProbabilisticExecution.beliefTCR, dif_neg (by rw [hcone]; simp)]
      rw [hbtcr, PMF.mem_support_pure_iff] at hw_belief
      -- The zero-cone case forces `w = ⟨pure sk, nil⟩` (length 0).  Coherence of `w` with
      -- `r.take k` excludes `k ≥ 1` (a recorded step at position `0` would demand a belief-step of
      -- the nil `w`), so `k = 0`, `labs' = []`, `sk = r.init`; the nil run supplies the four facts.
      have hk0 : k = 0 := by
        by_contra hkne
        have hkpos : 0 < k := Nat.pos_of_ne_zero hkne
        have hr0ne : r.trans.get? 0 ≠ none :=
          fun hc => Nat.find_min h (Nat.lt_trans hkpos hkN) hc
        obtain ⟨t0, hr0get'⟩ := Option.ne_none_iff_exists'.mp hr0ne
        obtain ⟨⟨l0, μ0⟩, s0'⟩ := t0
        have hr0take : (r.take k).trans.get? 0 = some ((l0, μ0), s0') := by
          rw [take_trans_get? r hkpos]; exact hr0get'
        obtain ⟨ν, ω0, ν', hwstate, hwget, -, -⟩ :=
          hw_coh 0 r.init l0 μ0 s0' rfl hr0take
        rw [hw_belief] at hwget
        change (Seq.nil : Seq ((Label × PMF (PMF State)) × PMF State)).get? 0 = _ at hwget
        rw [Stream'.Seq.get?_nil] at hwget
        exact absurd hwget (by simp)
      subst hk0
      have hr_init : r.init = sys.init := by
        have hi : (PE'.lowerFairR F).initState r.init ≠ 0 := hcons.1
        change PE'.initState.bind id r.init ≠ 0 at hi
        rw [hinit, PMF.pure_bind] at hi
        change ((sys.distF F).init : PMF State) r.init ≠ 0 at hi
        rw [show ((sys.distF F).init : PMF State) = PMF.pure sys.init from rfl, PMF.pure_apply]
          at hi
        by_contra hc
        rw [if_neg hc] at hi
        exact hi rfl
      have hsk_init : sk = r.init := by
        have hst : r.stateAt 0 = some r.init := rfl
        rw [hst] at hsk; exact (Option.some.inj hsk).symm
      have hlabs_nil : labs' = [] := by
        have hnil : (ResolvedExec.toExec (r.take 0)).trans = Seq.nil := rfl
        rw [hlabs', Stream'.Seq.toList_congr_pub hnil hTe Stream'.Seq.terminates_nil,
          Stream'.Seq.toList_nil, List.map_nil]
      subst hw_belief
      refine ⟨Stream'.Seq.terminates_nil, ?_, ?_, ?_⟩
      · rw [hlabs_nil, Stream'.Seq.ofList_nil,
          show (ResolvedExec.toExec (⟨PMF.pure sk, Seq.nil⟩ :
            ResolvedExec (PMF State) Label)).trans = Seq.nil from rfl, Stream'.Seq.map_nil]
      · rw [show (ResolvedExec.toExec (⟨PMF.pure sk, Seq.nil⟩ : ResolvedExec (PMF State)
          Label)).endState ((ResolvedExec.toExec_terminates_iff _).mpr Stream'.Seq.terminates_nil)
          = PMF.pure sk from by rw [AlterSeq.endState_of_trans_nil _ (by rfl)]; rfl]
        rw [PMF.support_pure]; exact Set.mem_singleton _
      · rw [PE'.probOfR_nil, hinit, hsk_init, hr_init]
        rw [show ((sys.distF F).init : PMF State) = PMF.pure sys.init from rfl, PMF.pure_apply,
          if_pos rfl]
        exact one_ne_zero
  -- `labs'.length = k` (the length-`k` prefix's label list).
  have hlabs'_len : labs'.length = k := by
    rw [hlabs', List.length_map, Stream'.Seq.length_toList]
    have hfind : Nat.find hTe = k :=
      (Nat.find_congr' (fun {m} => ResolvedExec.toExec_terminatedAt_iff (r.take k) m)).trans
        (take_find_of_le r h rfl (Nat.le_of_lt hkN))
    change Nat.find hTe = k; exact hfind
  -- `w` terminates exactly at `k` (its `toExec`-label list is `labs'`, of length `k`).
  have hwfind : Nat.find hwT = k := by
    have hiff : ∀ m, w.trans.TerminatedAt m ↔ (Seq.ofList labs' : Seq Label).TerminatedAt m := by
      intro m
      rw [← ResolvedExec.toExec_terminatedAt_iff w m]
      unfold Stream'.Seq.TerminatedAt
      rw [← hwlab, Stream'.Seq.map_get?, Option.map_eq_none_iff]
    have hofl : ∀ m, (Seq.ofList labs' : Seq Label).TerminatedAt m ↔ labs'.length ≤ m := by
      intro m
      unfold Stream'.Seq.TerminatedAt
      rw [Stream'.Seq.ofList_get?, List.getElem?_eq_none_iff]
    apply le_antisymm
    · rw [Nat.find_le_iff]
      exact ⟨k, Nat.le_refl k, (hiff k).mpr ((hofl k).mpr (Nat.le_of_eq hlabs'_len))⟩
    · rw [Nat.le_find_iff]
      intro n hn
      rw [hiff n, hofl n]; omega
  -- Convert the `Seq.ofList labs'` label identity to the raw `Seq`-of-labels form.
  have hwlab_raw : (ResolvedExec.toExec w).trans.map Prod.fst
      = (ResolvedExec.toExec (r.take k)).trans.map Prod.fst := by
    rw [hwlab, hlabs', ← map_ofList_gen, Stream'.Seq.ofList_toList]
  -- **The genuine residual — an honest existential, NOT the specific-`w` positivity.** The
  -- construction above extracts, from consistency at the last step, a coherent,
  -- `PE'.probOfR`-positive belief-prefix `w` whose *forgetful average* emits `some (l, ω)`
  -- (`hopt_supp`) and whose kernel realises `μ` (`hμ'_supp`). What remains is a coherent prefix
  -- with positive *resolved* emission. This does NOT hold for `w`: `average_next_some` places the
  -- resolved mass on some `toExec`-fibre mate `R'' ≠ w`, and coherence is not transported along the
  -- fibre (fibre-mates' recorded internal `ω`s, fed to `distFairHyperKernel`, are forgotten by
  -- `toExec`). So the goal is the genuine *existence* of a coherent resolved-positive lift `w'` of
  -- `r`'s last step — true because `r`'s trace is achievable, strictly weaker than crux A (which
  -- supplies it as a corollary), but not mechanical.
  sorry

/-- **The non-nil resolved reachability of the halt clause (assembled from the coherent
resolved-positive lift `lowerFairR_halt_coherent_resolved_lift`).**
For a `lowerFairR`-consistent terminating run `r` with at least one recorded step
(`0 < Nat.find h`), there is a *resolved* `PE'`-belief-run `R'` that is time-locally coherent with
`r` (`RCoherentTL F r`) **and** carries positive un-normalised full-cone weight
(`beliefTCRw F labs s₀ R' ≠ 0`, i.e. `R'` terminates on the full label-list `labs`, has positive
resolved path-mass `PE'.probOfR`, and its end-belief contains the concrete end-state `s₀`).

`r` terminates at `N := Nat.find h ≥ 1`, so its last recorded step is at position `k = N-1`,
`r.trans.get? k = some ((l, μ), s')` with `s' = r.endState h` and state-before-step
`sk = r.stateAt k`. Reading `lowerFairR`-consistency at that last step yields the emission
positivity `hnext` and `μ s' ≠ 0`, which we hand to `lowerFairR_halt_coherent_resolved_lift`; the
residual returns a coherent, `PE'.probOfR`-positive belief-prefix `w` (terminating at `k`) whose
plain projection emits `some (l, ω)` in the average, whose fairness-revealing kernel realises `μ` at
the last-step belief, **and** — crucially — that has positive *resolved* emission
`PE'.scheduler.next w (some (l, ω)) ≠ 0` on that step. The extension state `ν' ∈ ω.support` with
`ν' s' ≠ 0` is selected from the kernel marginal decomposition (`distFairHyperKernel_decomp`), and
`R' := ⟨w.init, w.trans ++ [((l, ω), ν')]⟩` is the length-`N` coherent belief-run. Its `beliefTCRw`
factors by `beliefTCRw_append_singleton` into `PE'.probOfR w · PE'.scheduler.next w (some (l, ω)) ·
ω ν' · ν' s'`; every factor is now supplied — the resolved-emission factor by the residual — so no
`sorry` remains here. Everything downstream (`lowerFairR_halt_restricted_cone_pos`,
`lowerFairR_halt_fairDeadlock`) builds on top of it. -/
private theorem lowerFairR_halt_nonnil_coherent_witness {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (r : ResolvedExec State Label) (h : r.trans.Terminates)
    (hcons : (PE'.lowerFairR F).Consistent r)
    (hinit : PE'.initState = PMF.pure (sys.distF F).init)
    (hNpos : 0 < Nat.find h)
    (h_e : r.toExec.trans.Terminates) :
    ∃ R', PE'.RCoherentTL F r R' ∧
      PE'.beliefTCRw F ((r.toExec.trans.toList h_e).map Prod.fst)
        (r.toExec.endState h_e) R' ≠ 0 := by
  classical
  set pe' := PE'.average.distFToDist F with hpe'
  set N := Nat.find h with hN
  -- `r` has a genuine last recorded step at position `N-1`.
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hNpos.ne'
  -- `k = N - 1`; `r.trans.get? k = some ((l, μ), s')`.
  have hkN : k < N := by rw [hk]; exact Nat.lt_succ_self k
  have hrget_ne : r.trans.get? k ≠ none := by
    have : ¬ r.trans.TerminatedAt k := Nat.find_min h hkN
    exact this
  obtain ⟨t, hrget'⟩ := Option.ne_none_iff_exists'.mp hrget_ne
  obtain ⟨⟨l, μ⟩, s'⟩ := t
  have hrget : r.trans.get? k = some ((l, μ), s') := hrget'
  -- `s' = r.endState h`: position `N = k+1` reads `stateAt N = (get? k).map snd = some s'`.
  have hend : r.endState h = s' := by
    have hst : r.stateAt N = some s' := by
      rw [hk]; change (r.trans.get? k).map Prod.snd = some s'; rw [hrget]; rfl
    have := AlterSeq.stateAt_find_eq_endState r h
    rw [← hN, hst] at this; exact (Option.some.inj this).symm
  -- Concrete `s_k := r.stateAt k` (the state before the last step), which exists since `k < N`.
  have hsk_isSome : (r.stateAt k).isSome := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0]; rfl
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
      rw [hj]
      change ((r.trans.get? j).map Prod.snd).isSome
      rw [Option.isSome_map]
      refine Option.isSome_iff_ne_none.mpr ?_
      exact Nat.find_min h (Nat.lt_trans (hj ▸ Nat.lt_succ_self j) hkN)
  obtain ⟨sk, hsk⟩ := Option.isSome_iff_exists.mp hsk_isSome
  -- **Step 1. Read `lowerFairR`-consistency at the last step `k`, and obtain the coherent
  -- resolved-positive lift `w` of that step from the residual
  -- `lowerFairR_halt_coherent_resolved_lift`.**
  obtain ⟨hnext, hμs'⟩ := hcons.2 k l μ s' hrget
  have hkfind : Nat.find h = k + 1 := hN.symm.trans hk
  obtain ⟨w, ω, hwT, hwfind, hwlab_raw, hw_coh, hwpm, hsk_mem, hopt_supp, hnext_pos, hμ'_supp⟩ :=
    lowerFairR_halt_coherent_resolved_lift F PE' r h hcons hinit k l μ s' sk hkfind hrget hsk
      hnext hμs'
  -- `(r.take k).toExec` terminates; `labs'` is its label list.
  have hTe : (ResolvedExec.toExec (r.take k)).trans.Terminates :=
    (ResolvedExec.toExec_terminates_iff (r.take k)).mpr (take_terminates r k)
  set labs' := ((ResolvedExec.toExec (r.take k)).trans.toList hTe).map Prod.fst with hlabs'
  -- Recover the `Seq.ofList labs'` form of `w`'s label identity from the raw `Seq`-of-labels form.
  have hwlab : (ResolvedExec.toExec w).trans.map Prod.fst = Seq.ofList labs' := by
    rw [hwlab_raw, hlabs', ← map_ofList_gen, Stream'.Seq.ofList_toList]
  set E := ResolvedExec.toExec w with hE
  -- **Step 2. Select the extension belief `ν' ∈ ω.support` with `ν' s' ≠ 0`.**
  -- `E.trans.Terminates` (as `w.trans` does).
  have hE_term : E.trans.Terminates := (ResolvedExec.toExec_terminates_iff w).mpr hwT
  -- Marginal decomposition of the kernel at `q = s'`:
  --   `(ω.bind id) s' = ∑' s, (E.endState) s · ((dfhk E l ω s).bind id) s'`.
  have hdecomp := pe'.distFairHyperKernel_decomp F hE_term hopt_supp s'
  -- The `s = sk` summand is positive: `(E.endState) sk ≠ 0` (`hsk_mem`), and
  --   `((dfhk E l ω sk).bind id) s' ≥ (dfhk E l ω sk) μ · μ s' > 0`.
  have hbind_sk_pos : ((pe'.distFairHyperKernel F E l ω sk).bind id) s' ≠ 0 := by
    rw [PMF.bind_apply]
    intro hz
    have := ENNReal.tsum_eq_zero.mp hz μ
    rw [id, mul_eq_zero] at this
    rcases this with h1 | h2
    · exact (PMF.mem_support_iff _ _).mp hμ'_supp h1
    · exact hμs' h2
  have hend_sk_pos : (w.toExec.endState hE_term) sk ≠ 0 := (PMF.mem_support_iff _ _).mp hsk_mem
  -- Hence `(ω.bind id) s' ≠ 0`.
  have hωbind_pos : (ω.bind id) s' ≠ 0 := by
    rw [hdecomp]
    intro hz
    have := ENNReal.tsum_eq_zero.mp hz sk
    rw [mul_eq_zero] at this
    rcases this with h1 | h2
    · exact hend_sk_pos h1
    · exact hbind_sk_pos h2
  -- Unfold `(ω.bind id) s' = ∑' ν', ω ν' · ν' s'` to get the witness `ν'`.
  rw [PMF.bind_apply] at hωbind_pos
  obtain ⟨ν', hν'⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hωbind_pos)
  rw [id] at hν'
  have hων' : ω ν' ≠ 0 := fun hz => hν' (by rw [hz, zero_mul])
  have hν's' : ν' s' ≠ 0 := fun hz => hν' (by rw [hz, mul_zero])
  -- **The `r.trans` decomposition at the last step.**  `r.trans = (r.take k).trans ++ [step]`.
  have hrtrans : r.trans
      = (r.take k).trans.append (Seq.cons ((l, μ), s') Seq.nil) := by
    have hnonempty : r.trans.toList h ≠ [] := by
      intro hnil
      have hlen : (r.trans.toList h).length = Nat.find h := Stream'.Seq.length_toList _ h
      rw [hnil, List.length_nil, ← hN] at hlen
      exact hNpos.ne' hlen.symm
    obtain ⟨prev, last, hprevT, hsplit, hprevList, hlast⟩ :=
      Stream'.Seq.exists_split_last r.trans h hnonempty
    -- `(prev.toList).length = k` (dropLast of the length-`(k+1)` `toList`).
    have hprevlen : (prev.toList hprevT).length = k := by
      have hlen : (r.trans.toList h).length = Nat.find h := Stream'.Seq.length_toList _ h
      rw [hprevList, List.length_dropLast, hlen, ← hN, hk, Nat.succ_sub_one]
    -- `last = ((l, μ), s')`: it is the last recorded step, i.e. `r.trans.get? k`.
    have hlast_eq : last = ((l, μ), s') := by
      have hgetlast := get?_last_of_split r prev last hprevT hsplit
      rw [hprevlen, hrget] at hgetlast
      exact (Option.some.inj hgetlast).symm
    -- `prev = (r.take k).trans` via `take_prev_of_split`.
    have hprev_eq : (r.take k).trans = prev := by
      have := take_prev_of_split r prev last hprevT hsplit
      rw [hprevlen] at this
      rw [this]
    rw [hsplit, hlast_eq, hprev_eq]
  -- **`labs = labs' ++ [l]`** and **`r.toExec.endState h_e = s'`**.
  have hend_e : r.toExec.endState h_e = s' := by
    have hfind : Nat.find h = Nat.find h_e :=
      Nat.find_congr' (fun {n} => (ResolvedExec.toExec_terminatedAt_iff r n).symm)
    apply Option.some.inj
    rw [← AlterSeq.stateAt_find_eq_endState r.toExec h_e, ← hfind, ResolvedExec.toExec_stateAt,
      ← hN, hk]
    change (r.trans.get? k).map Prod.snd = some s'
    rw [hrget]; rfl
  have hlabs_split : (r.toExec.trans.toList h_e).map Prod.fst = labs' ++ [l] := by
    -- `r.toExec.trans = (r.take k).toExec.trans ++ [(l, s')]`.
    have htoE_split : r.toExec.trans
        = (ResolvedExec.toExec (r.take k)).trans.append (Seq.cons (l, s') Seq.nil) := by
      change r.trans.map (fun p => (p.1.1, p.2)) = _
      rw [hrtrans, Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil]
      rfl
    have hpT : (ResolvedExec.toExec (r.take k)).trans.Terminates := hTe
    have hcT : (Seq.cons (l, s') Seq.nil : Seq (Label × State)).Terminates :=
      Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
    have heq_toList : r.toExec.trans.toList h_e
        = (ResolvedExec.toExec (r.take k)).trans.toList hpT
          ++ (Seq.cons (l, s') Seq.nil : Seq (Label × State)).toList hcT := by
      rw [Stream'.Seq.toList_congr_pub htoE_split h_e (by rw [← htoE_split]; exact h_e)]
      exact Stream'.Seq.toList_append _ _ hpT hcT _
    rw [heq_toList, List.map_append]
    congr 1
    rw [Stream'.Seq.toList_cons hcT]
    simp [Stream'.Seq.toList_nil]
  -- **Step 3+4. Assemble `R'` and finish.**
  set R' : ResolvedExec (PMF State) Label :=
    ⟨w.init, w.trans.append (Seq.cons ((l, ω), ν') Seq.nil)⟩ with hR'def
  -- `w` terminates exactly at `k` (`hwfind` supplied by the residual).
  have hkT : w.trans.TerminatedAt k := hwfind ▸ Nat.find_spec hwT
  -- `R'.take k = w` (positions `< k` unaffected by the append; `w.take k = w` as `w` ends at `k`).
  have hRtake : R'.take k = w := by
    have hwtake : w.take k = w := take_self_of_terminatedAt w k hkT
    rw [← hwtake]
    -- `R'.take k` and `w.take k` agree: their `trans` match below `k`.
    change (⟨w.init, Seq.ofList (Seq.take k R'.trans)⟩ : ResolvedExec (PMF State) Label)
      = ⟨w.init, Seq.ofList (Seq.take k w.trans)⟩
    congr 1
    apply Stream'.Seq.ext
    intro m
    rw [Stream'.Seq.ofList_get?, Stream'.Seq.ofList_get?]
    by_cases hm : m < k
    · rw [seq_getElem?_take R'.trans k m hm, seq_getElem?_take w.trans k m hm]
      change (w.trans.append (Seq.cons ((l, ω), ν') Seq.nil)).get? m = w.trans.get? m
      exact Stream'.Seq.get?_append_before_length
        (fun ht => Nat.find_min hwT (hwfind ▸ hm) ht)
    · rw [List.getElem?_eq_none (Nat.le_trans Stream'.Seq.length_take_le (Nat.le_of_not_lt hm)),
        List.getElem?_eq_none (Nat.le_trans Stream'.Seq.length_take_le (Nat.le_of_not_lt hm))]
  -- `R'.stateAt`/`get?`/`take` below `k` agree with `w`.
  have hR'get_lt : ∀ m, m < k → R'.trans.get? m = w.trans.get? m := by
    intro m hm
    change (w.trans.append (Seq.cons ((l, ω), ν') Seq.nil)).get? m = w.trans.get? m
    exact Stream'.Seq.get?_append_before_length (fun ht => Nat.find_min hwT (hwfind ▸ hm) ht)
  have hR'state_le : ∀ m, m ≤ k → R'.stateAt m = w.stateAt m := by
    intro m hm
    cases m with
    | zero => rfl
    | succ j =>
      change (R'.trans.get? j).map Prod.snd = (w.trans.get? j).map Prod.snd
      rw [hR'get_lt j (Nat.lt_of_succ_le hm)]
  have hR'take_lt : ∀ m, m ≤ k → R'.take m = w.take m := by
    intro m hm
    change (⟨w.init, Seq.ofList (Seq.take m R'.trans)⟩ : ResolvedExec (PMF State) Label)
      = ⟨w.init, Seq.ofList (Seq.take m w.trans)⟩
    congr 1
    apply Stream'.Seq.ext
    intro j
    rw [Stream'.Seq.ofList_get?, Stream'.Seq.ofList_get?]
    by_cases hj : j < m
    · rw [seq_getElem?_take R'.trans m j hj, seq_getElem?_take w.trans m j hj,
        hR'get_lt j (Nat.lt_of_lt_of_le hj hm)]
    · rw [List.getElem?_eq_none (Nat.le_trans Stream'.Seq.length_take_le (Nat.le_of_not_lt hj)),
        List.getElem?_eq_none (Nat.le_trans Stream'.Seq.length_take_le (Nat.le_of_not_lt hj))]
  refine ⟨R', ?_, ?_⟩
  · -- **Coherence `RCoherentTL F r R'`.**
    intro n s ln μn sn' hstate hget
    -- `n ≤ k`: `r` has no recorded step past `N = k+1`.
    have hnk : n ≤ k := by
      by_contra hc
      have hle : Nat.find h ≤ n := by rw [hkfind]; exact Nat.succ_le_of_lt (Nat.lt_of_not_le hc)
      have : r.trans.TerminatedAt n :=
        Stream'.Seq.terminated_stable r.trans hle (Nat.find_spec h)
      rw [this] at hget; exact absurd hget (by simp)
    rcases Nat.lt_or_ge n k with hnlt | hnge
    · -- **Internal position `n < k`: reuse `w`'s coherence.**
      have hstate_k : (r.take k).stateAt n = some s := by
        rw [take_stateAt r (Nat.le_of_lt hnlt)]; exact hstate
      have hget_k : (r.take k).trans.get? n = some ((ln, μn), sn') := by
        rw [take_trans_get? r hnlt]; exact hget
      obtain ⟨ν, ωn, νn', hwstate, hwget, hsupp, hker⟩ := hw_coh n s ln μn sn' hstate_k hget_k
      refine ⟨ν, ωn, νn', ?_, ?_, hsupp, ?_⟩
      · rw [hR'state_le n (Nat.le_of_lt hnlt)]; exact hwstate
      · rw [hR'get_lt n hnlt]; exact hwget
      · rw [hR'take_lt n (Nat.le_of_lt hnlt)]; exact hker
    · -- **Last position `n = k`: the appended step.**
      have hnk_eq : n = k := Nat.le_antisymm hnk hnge
      -- `s = sk`, `ln = l`, `μn = μ`, `sn' = s'` (the recorded step at `n = k`).
      have hs_sk : s = sk := by
        rw [hnk_eq, hsk] at hstate; exact (Option.some.inj hstate).symm
      have hstep : ((ln, μn), sn') = ((l, μ), s') := by
        rw [hnk_eq, hrget] at hget; exact (Option.some.inj hget).symm
      obtain ⟨hll, hμμn, hsn⟩ : ln = l ∧ μn = μ ∧ sn' = s' := by
        rw [Prod.mk.injEq, Prod.mk.injEq] at hstep
        exact ⟨hstep.1.1, hstep.1.2, hstep.2⟩
      -- `w.toExec` terminates exactly at `k` (same position as `w`).
      have hEfind : Nat.find hE_term = k :=
        (Nat.find_congr' (hp := hE_term) (hq := hwT)
          (fun {m} => ResolvedExec.toExec_terminatedAt_iff w m)).trans hwfind
      refine ⟨w.toExec.endState hE_term, ω, ν', ?_, ?_, ?_, ?_⟩
      · -- `R'.stateAt n = w.stateAt k = some (w.toExec.endState hE_term)`.
        rw [hnk_eq, hR'state_le k (Nat.le_refl k), ← ResolvedExec.toExec_stateAt w k, ← hEfind]
        exact AlterSeq.stateAt_find_eq_endState w.toExec hE_term
      · -- `R'.trans.get? n = some ((ln, ω), ν')` (the appended step), using `ln = l`.
        rw [hnk_eq, hll]
        change (w.trans.append (Seq.cons ((l, ω), ν') Seq.nil)).get? k = _
        have := Stream'.Seq.get?_append_find hwT (Seq.cons ((l, ω), ν') Seq.nil) 0
        rw [Nat.add_zero] at this
        rw [hwfind] at this
        rw [this]; rfl
      · -- `s ∈ (w.toExec.endState).support` from `s = sk` and `hsk_mem`.
        rw [hs_sk]; exact hsk_mem
      · -- `μn ∈ (dfhk (toExec (R'.take n)) ln ω s).support`: `R'.take k = w`, `ln = l`, `s = sk`.
        rw [hnk_eq, hRtake, hll, hμμn, hs_sk]; exact hμ'_supp
  · -- **Positive `beliefTCRw`.**
    rw [hlabs_split, hend_e]
    rw [PE'.beliefTCRw_append_singleton F labs' l s' w ω ν' hwT hwlab]
    -- All four factors are nonzero; the resolved-next factor is supplied by the residual
    -- (`hnext_pos`).
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hwpm hnext_pos) hων') hν's'

/-- **Fallback-exclusion at a consistent terminating run (the single sharp support-level residual
of the halt clause).** On a `lowerFairR`-consistent terminating run `r`, the *restricted* resolved
belief-cone at `r`'s full trace `labs` and end-state `s₀` carries positive mass. Equivalently the
`PMF.pure none` fallback of `lowerFairRSched.next r` (which fires exactly when this restricted mass
is `0`) never fires on a consistent `r`, so the halting emission always factors through a coherent
belief-history.

Why this is not already delivered by `exists_positive_coherent_prefix`: that lemma reads
`lowerFairR`-consistency at a *genuine internal step* (position `n < Nat.find h`) of an
*infinite* run, forcing the `h0` branch of `lowerFairRSched.next (r.take n)` — a cone at the
length-`n` *prefix* trace. Here the cone is at `r`'s **full** trace (including the terminal step)
and `r` terminates, so there is no recorded step at `Nat.find h` for consistency to read; the fact
that `r`'s realised full trace admits a coherent belief-lift is the genuinely new *qualitative*
(support-level) reachability input — strictly weaker than crux A's quantitative probability-matching
(`lowerFairR_traceProbR_eq_lowerCoe`), which would supply it as a corollary. The `nil` sub-case is
discharged (`s₀ = r.init`, the length-0 belief run is vacuously coherent and carries the positive
initial mass); the non-nil sub-case — a consistent terminating trace lifts to a coherent belief
history — is the isolated residual. -/
private theorem lowerFairR_halt_restricted_cone_pos {sys : System State Label} (F : Fairness sys)
    (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (r : ResolvedExec State Label) (h : r.trans.Terminates)
    (hcons : (PE'.lowerFairR F).Consistent r)
    (hinit : PE'.initState = PMF.pure (sys.distF F).init) :
    (∑' R', Set.indicator {R' | PE'.RCoherentTL F r R'}
      (PE'.beliefTCR F ((r.toExec.trans.toList
        ((ResolvedExec.toExec_terminates_iff r).mpr h)).map Prod.fst)
        (r.toExec.endState ((ResolvedExec.toExec_terminates_iff r).mpr h))) R') ≠ 0 := by
  classical
  have h_e : r.toExec.trans.Terminates := (ResolvedExec.toExec_terminates_iff r).mpr h
  set labs := (r.toExec.trans.toList h_e).map Prod.fst with hlabs
  set s₀ := r.toExec.endState h_e with hs₀
  -- **Reduction.** It suffices to exhibit one `R'` that is `RCoherentTL F r`-coherent and has
  -- positive `beliefTCR` mass at the full cone; its `indicator` value is then positive.
  suffices hwit : ∃ R', PE'.RCoherentTL F r R' ∧ PE'.beliefTCR F labs s₀ R' ≠ 0 by
    obtain ⟨R', hcoh, hmass⟩ := hwit
    rw [ne_eq, ENNReal.tsum_eq_zero, not_forall]
    refine ⟨R', fun hz => hmass ?_⟩
    rwa [Set.indicator_of_mem hcoh] at hz
  -- **Bridge:** `beliefTCRw ≠ 0 ⟹ beliefTCR ≠ 0` (the contributing run forces the normalise
  -- branch, where `beliefTCR = beliefTCRw · Z⁻¹` with `Z` finite and nonzero).
  suffices hwit : ∃ R', PE'.RCoherentTL F r R' ∧ PE'.beliefTCRw F labs s₀ R' ≠ 0 by
    obtain ⟨R', hcoh, hmass⟩ := hwit
    have hpos : (∑' R'', PE'.beliefTCRw F labs s₀ R'') ≠ 0 :=
      fun hz => hmass (ENNReal.tsum_eq_zero.mp hz R')
    refine ⟨R', hcoh, ?_⟩
    rw [ResolvedProbabilisticExecution.beliefTCR, dif_pos hpos, PMF.normalize_apply]
    refine mul_ne_zero hmass (ENNReal.inv_ne_zero.mpr ?_)
    rw [PE'.beliefTCRw_tsum_eq F labs s₀]
    exact (PE'.average.distFToDist F).beliefTCw_tsum_ne_top labs s₀
  -- `r.init = sys.init` from `lowerFairR`-consistency (`initState.bind id = pure sys.init`), hinit.
  have hinit_bind : (PE'.lowerFairR F).initState = (PMF.pure sys.init : PMF State) := by
    change PE'.initState.bind id = _
    rw [hinit]
    change (PMF.pure (PMF.pure sys.init)).bind id = _
    rw [PMF.pure_bind]; rfl
  have hr_init : r.init = sys.init := by
    have hi : (PE'.lowerFairR F).initState r.init ≠ 0 := hcons.1
    rw [hinit_bind] at hi
    by_contra hc
    rw [PMF.pure_apply, if_neg hc] at hi; exact hi rfl
  -- Case split on the length `N = Nat.find h` of `r`.
  rcases Nat.eq_zero_or_pos (Nat.find h) with hN0 | hNpos
  · -- **Nil sub-case** (`N = 0`): `r.trans = nil`, `labs = []`, `s₀ = r.init = sys.init`.  The
    -- length-0 belief run `⟨pure sys.init, nil⟩` is vacuously coherent and carries positive mass.
    have hr_nil : r.trans = Seq.nil :=
      Stream'.Seq.terminatedAt_zero_iff.mp (hN0 ▸ Nat.find_spec h)
    have htoExec_nil : r.toExec.trans = Seq.nil := by
      rw [ResolvedExec.toExec_trans, hr_nil]; rfl
    have hlabs_nil : labs = [] := by
      rw [hlabs, Stream'.Seq.toList_congr_pub htoExec_nil h_e Stream'.Seq.terminates_nil,
        Stream'.Seq.toList_nil, List.map_nil]
    have hs₀_init : s₀ = sys.init := by
      rw [hs₀, AlterSeq.endState_of_trans_nil r.toExec htoExec_nil, ResolvedExec.toExec_init,
        hr_init]
    -- Witness: the length-0 belief run `⟨pure sys.init, nil⟩`.
    refine ⟨⟨PMF.pure sys.init, Seq.nil⟩, ?_, ?_⟩
    · -- Coherence is vacuous: `r` has no recorded step.
      intro m s l μ s' _ hget
      rw [hr_nil] at hget
      change (Seq.nil : Seq ((Label × PMF State) × State)).get? m = _ at hget
      rw [Stream'.Seq.get?_nil] at hget; exact absurd hget (by simp)
    · -- Positive `beliefTCRw`: guard holds (nil, empty labels), mass `= 1 · 1 ≠ 0`.
      rw [ResolvedProbabilisticExecution.beliefTCRw, hlabs_nil, hs₀_init, dif_pos]
      · rw [PE'.probOfR_nil, hinit]
        have hend : (ResolvedExec.toExec (⟨PMF.pure sys.init, Seq.nil⟩ : ResolvedExec (PMF State)
            Label)).endState ((ResolvedExec.toExec_terminates_iff _).mpr Stream'.Seq.terminates_nil)
            = PMF.pure sys.init := by
          rw [AlterSeq.endState_of_trans_nil _ (by rfl)]; rfl
        rw [hend]
        change (PMF.pure (PMF.pure sys.init) (PMF.pure sys.init)) * (PMF.pure sys.init) sys.init ≠ 0
        rw [PMF.pure_apply, if_pos rfl, PMF.pure_apply, if_pos rfl, one_mul]
        exact one_ne_zero
      · refine ⟨Stream'.Seq.terminates_nil, ?_⟩
        rw [show (ResolvedExec.toExec (⟨PMF.pure sys.init, Seq.nil⟩ : ResolvedExec (PMF State)
          Label)).trans = Seq.nil from rfl, Stream'.Seq.map_nil, Stream'.Seq.ofList_nil]
  · -- **Non-nil sub-case** (`0 < Nat.find h`): the resolved belief-cone realizability of `r`'s
    -- full trace at the terminal step is the single isolated residual.
    exact lowerFairR_halt_nonnil_coherent_witness F PE' r h hcons hinit hNpos h_e

/-- **Fallback-exclusion + halting lift (the single support-level residual of the halt clause).**
On a `lowerFairR`-consistent terminating run `r` at which the μ-reading witness halts
(`lowerFairRSched.next r none ≠ 0`), the emission factors through a coherent belief-history: there
is a resolved `PE'`-run `R''` with a positive path mass (hence `PE'`-consistent), whose end-belief
contains the concrete end-state `r.endState h`, at which `PE'` itself halts
(`PE'.scheduler.next R'' none ≠ 0`).

This is the finite analogue of `exists_positive_coherent_prefix` (which reads consistency at a
genuine internal step of an *infinite* `r`): here we read consistency at `r`'s *last* step and
extend the coherent prefix by that step, so the fallback `PMF.pure none` of `lowerFairRSched.next r`
is never fired on a consistent `r` and the sampled belief-run lifts to a positive-mass resolved
`PE'`-run. Purely *qualitative* (support-level) reachability — strictly weaker than crux A's
quantitative probability-matching — isolated here as the halt clause's one residual `sorry`.
Everything downstream (the `𝒟f→𝒟` fair-deadlock transfer via `IsFair.halt_fairDeadlock`,
`resolvable_of_consistent_step` and `distF_fairDeadlock_belief`) is discharged unconditionally in
`lowerFairR_halt_fairDeadlock`. -/
private theorem lowerFairR_halt_coherent_lift {sys : System State Label} (F : Fairness sys)
    (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (r : ResolvedExec State Label) (h : r.trans.Terminates)
    (hcons : (PE'.lowerFairR F).Consistent r)
    (h_none : (PE'.lowerFairR F).scheduler.next r none ≠ 0)
    (hinit : PE'.initState = PMF.pure (sys.distF F).init) :
    ∃ (R'' : ResolvedExec (PMF State) Label) (hT'' : R''.trans.Terminates),
      PE'.probOfR R'' hT'' ≠ 0 ∧
      r.endState h ∈ (R''.endState hT'').support ∧
      F.Resolvable (R''.endState hT'') ∧
      PE'.scheduler.next R'' none ≠ 0 := by
  classical
  set pe' := PE'.average.distFToDist F with hpe'
  -- The concrete end-state, identified with `r.toExec`'s end-state.
  have h_e : r.toExec.trans.Terminates := (ResolvedExec.toExec_terminates_iff r).mpr h
  have hend_eq : r.endState h = r.toExec.endState h_e := by
    have hfind : Nat.find h = Nat.find h_e :=
      Nat.find_congr' (fun {n} => (ResolvedExec.toExec_terminatedAt_iff r n).symm)
    apply Option.some.inj
    rw [← AlterSeq.stateAt_find_eq_endState r h, ← AlterSeq.stateAt_find_eq_endState r.toExec h_e,
      hfind, ResolvedExec.toExec_stateAt]
  set labs := (r.toExec.trans.toList h_e).map Prod.fst with hlabs
  set s₀ := r.toExec.endState h_e with hs₀
  -- `none ∈ (lowerFairRSched.next r).support`; unfold the emission (mirror of `.valid`).
  have hmem : none ∈ ((PE'.lowerFairR F).scheduler.next r).support :=
    (PMF.mem_support_iff _ _).mpr h_none
  change none ∈
    (open Classical in
      if h_term : r.toExec.trans.Terminates then
        if h0 : (∑' R', Set.indicator {R' | PE'.RCoherentTL F r R'}
            (PE'.beliefTCR F ((r.toExec.trans.toList h_term).map Prod.fst)
              (r.toExec.endState h_term)) R') ≠ 0 then
          ((PE'.beliefTCR F ((r.toExec.trans.toList h_term).map Prod.fst)
              (r.toExec.endState h_term)).filter {R' | PE'.RCoherentTL F r R'} _).bind (fun R' =>
            (pe'.scheduler.next (ResolvedExec.toExec R')).bind (fun opt =>
              match opt with
              | none         => PMF.pure none
              | some (l', ω) =>
                (pe'.distFairHyperKernel F (ResolvedExec.toExec R') l' ω
                    (r.toExec.endState h_term)).map (fun μ' => some (l', μ'))))
        else PMF.pure none
      else PMF.pure none).support at hmem
  rw [dif_pos h_e] at hmem
  -- The live branch (positive restricted cone mass) must hold: on the fallback the emission is
  -- `PMF.pure none`, and a `lowerFairR`-consistent terminating run forbids it.
  have h0 : (∑' R', Set.indicator {R' | PE'.RCoherentTL F r R'}
      (PE'.beliefTCR F labs s₀) R') ≠ 0 :=
    lowerFairR_halt_restricted_cone_pos F PE' r h hcons hinit
  rw [dif_pos h0] at hmem
  -- Factor the `none`-mass through the filter-bind: it can only arise from the `opt = none` case.
  rw [PMF.mem_support_bind_iff] at hmem
  obtain ⟨R', hR'_filter, hmem⟩ := hmem
  rw [PMF.mem_support_filter_iff] at hR'_filter
  obtain ⟨hR'_coh, hR'_belief⟩ := hR'_filter
  set E := ResolvedExec.toExec R' with hE
  rw [PMF.mem_support_bind_iff] at hmem
  obtain ⟨opt, hopt_sch, hmem⟩ := hmem
  -- Recover `E.Terminates`, `s₀ ∈ E.endState.support`, and `avgWeight E ≠ 0`.
  -- Two cases: positive cone mass (`beliefTCR_support`), or the length-0 fallback which — since
  -- `h0` holds and the fallback run is coherent with `r` — forces `r` to have no step, whence
  -- `s₀ = r.init = sys.init` and `avgWeight ⟨pure s₀, nil⟩ = PE'.initState (pure sys.init) = 1`.
  obtain ⟨hE_term, h_endState, hW⟩ :
      ∃ hE_term : E.trans.Terminates, s₀ ∈ (E.endState hE_term).support ∧
        PE'.avgWeight E hE_term ≠ 0 := by
    by_cases hpos : (∑' R'', PE'.beliefTCRw F labs s₀ R'') ≠ 0
    · obtain ⟨hT, -, h_mem, hpm⟩ := PE'.beliefTCR_support F labs s₀ hpos R' hR'_belief
      refine ⟨(ResolvedExec.toExec_terminates_iff R').mpr hT, h_mem, ?_⟩
      -- `avgWeight E = ∑' (toExec = E) probOfR ≥ probOfR R' > 0`.
      rw [ResolvedProbabilisticExecution.avgWeight]
      intro hz
      exact hpm (ENNReal.tsum_eq_zero.mp hz ⟨R', hE.symm⟩)
    · rw [not_not] at hpos
      rw [ResolvedProbabilisticExecution.beliefTCR, dif_neg (by rw [hpos]; simp),
        PMF.mem_support_pure_iff] at hR'_belief
      -- The fallback belief run is `⟨pure s₀, nil⟩`; it is `RCoherentTL`-coherent with `r` (from
      -- the filter membership), which forbids `r` having a step at position 0, so `r` is nil.
      subst hR'_belief
      have hE_nil : E.trans = Seq.nil := by rw [hE]; rfl
      -- `r` has no step at position 0.
      have hr0 : r.trans.get? 0 = none := by
        by_contra hc
        obtain ⟨⟨⟨l0, μ0⟩, s0'⟩, hr0get⟩ := Option.ne_none_iff_exists'.mp hc
        obtain ⟨ν, ω, ν', hwstate, hwget, -, -⟩ :=
          hR'_coh 0 r.init l0 μ0 s0' rfl hr0get
        change (Seq.nil : Seq ((Label × PMF (PMF State)) × PMF State)).get? 0 = _ at hwget
        rw [Stream'.Seq.get?_nil] at hwget
        exact absurd hwget (by simp)
      have hr_nil : r.trans = Seq.nil := Stream'.Seq.terminatedAt_zero_iff.mp hr0
      -- `s₀ = r.endState = r.init`.
      have hr_end : r.endState h = r.init := AlterSeq.endState_of_trans_nil r hr_nil h
      have hs₀_init : s₀ = r.init := by rw [← hend_eq, hr_end]
      -- `r.init = sys.init` from `lowerFairR`-consistency + `hinit`.
      have hinit_mem : (PE'.lowerFairR F).initState r.init ≠ 0 := hcons.1
      have hinit_bind : (PE'.lowerFairR F).initState = (PMF.pure sys.init : PMF State) := by
        change PE'.initState.bind id = _
        rw [hinit]
        change (PMF.pure (PMF.pure sys.init)).bind id = _
        rw [PMF.pure_bind]; rfl
      rw [hinit_bind] at hinit_mem
      have hr_init : r.init = sys.init := by
        by_contra hc
        rw [PMF.pure_apply, if_neg hc] at hinit_mem; exact hinit_mem rfl
      have hs₀_eq : s₀ = sys.init := by rw [hs₀_init, hr_init]
      -- `E = ⟨PMF.pure s₀, nil⟩`.
      have hEeq : E = (⟨PMF.pure s₀, Seq.nil⟩ : AlterSeq (PMF State) Label) := by
        have h1 : E.init = PMF.pure s₀ := by rw [hE]; rfl
        calc E = ⟨E.init, E.trans⟩ := rfl
          _ = ⟨PMF.pure s₀, Seq.nil⟩ := by rw [h1, hE_nil]
      refine ⟨hE_nil ▸ Stream'.Seq.terminates_nil, ?_, ?_⟩
      · have hend : E.endState (hE_nil ▸ Stream'.Seq.terminates_nil) = PMF.pure s₀ := by
          rw [AlterSeq.endState_of_trans_nil E hE_nil]; rw [hE]; rfl
        rw [hend, PMF.support_pure, Set.mem_singleton_iff]
      · -- `avgWeight ⟨pure s₀, nil⟩ = PE'.initState (pure s₀) = 1 ≠ 0`.
        rw [PE'.avgWeight_congr E ⟨PMF.pure s₀, Seq.nil⟩ hEeq _ Stream'.Seq.terminates_nil,
          PE'.avgWeight_nil (PMF.pure s₀), hs₀_eq, hinit]
        change (PMF.pure (PMF.pure sys.init)) (PMF.pure sys.init) ≠ 0
        rw [PMF.pure_apply, if_pos rfl]; exact one_ne_zero
  -- Only the `opt = none` branch of the match can carry mass on `none`.
  have hopt_none : opt = none := by
    cases opt with
    | none => rfl
    | some lω =>
      obtain ⟨l', ω⟩ := lω
      exfalso
      change none ∈ ((pe'.distFairHyperKernel F E l' ω s₀).map
        (fun μ' => some (l', μ'))).support at hmem
      rw [PMF.mem_support_map_iff] at hmem
      obtain ⟨μ', -, h_eq⟩ := hmem
      exact absurd h_eq (by simp)
  subst hopt_none
  -- So `pe'.scheduler.next E none ≠ 0`, i.e. `PE'.average.scheduler.next E none ≠ 0`.
  have hpe'_none : PE'.average.scheduler.next E none ≠ 0 := (PMF.mem_support_iff _ _).mp hopt_sch
  rw [PE'.average_next_none E hE_term hW] at hpe'_none
  -- The numerator is nonzero: extract a positive-mass `R''` with `toExec R'' = E` halting at `PE'`.
  have hN : (∑' r'' : {r'' : ResolvedExec (PMF State) Label // r''.toExec = E},
      PE'.probOfR r''.1 (ResolvedExec.terminates_of_toExec_eq hE_term r''.2)
        * PE'.scheduler.next r''.1 none) ≠ 0 := fun hz => hpe'_none (by rw [hz, zero_mul])
  obtain ⟨r'', hr''⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hN)
  set hT'' := ResolvedExec.terminates_of_toExec_eq hE_term r''.2 with hT''def
  have hpm'' : PE'.probOfR r''.1 hT'' ≠ 0 := fun hz => hr'' (by rw [hz, zero_mul])
  have hcons'' : PE'.Consistent r''.1 := probOfR_ne_zero_imp_consistent PE' r''.1 hT'' hpm''
  -- `R''.endState = E.endState` (same `toExec`).
  have hend2 : r''.1.endState hT'' = E.endState hE_term := by
    have hfind : Nat.find hT'' = Nat.find hE_term := by
      refine Nat.find_congr' (fun {n} => ?_)
      rw [← ResolvedExec.toExec_terminatedAt_iff r''.1, r''.2]
    apply Option.some.inj
    rw [← AlterSeq.stateAt_find_eq_endState r''.1 _,
      ← AlterSeq.stateAt_find_eq_endState E hE_term, hfind,
      ← ResolvedExec.toExec_stateAt, r''.2]
  refine ⟨r''.1, hT'', hpm'', ?_, ?_, ?_⟩
  · -- `r.endState h ∈ (R''.endState).support`.
    rw [hend_eq, hend2]; exact h_endState
  · -- Resolvability of `R''.endState` (consistent terminating run).
    exact ResolvedProbabilisticExecution.resolvable_of_consistent_endState
      F PE' r''.1 hcons'' hT'' hinit
  · -- `PE'.scheduler.next R'' none ≠ 0`.
    exact fun hz => hr'' (by rw [hz, mul_zero])

/-- **The witness halts only from a fair deadlock.** If the μ-reading witness halts at a terminating
consistent run `r`, its end-state `r.endState` is an `F`-fair-deadlock. The halt (`h_none`) factors,
via the reachability lift `lowerFairR_halt_coherent_lift`, through a positive-mass (hence
consistent) resolved `PE'`-belief-run `R''` at which `PE'` itself halts, with
`r.endState h ∈ (R''.endState)` and `R''.endState` `F.Resolvable`. The `𝒟f`-fairness of `PE'`
(`hfair.halt_fairDeadlock`) makes
`R''.endState` an `F.dist`-fair-deadlock belief; resolvability then lets
`distF_fairDeadlock_belief` carry the deadlock down to every state in its support — in particular to
`r.endState h`. -/
theorem ResolvedProbabilisticExecution.lowerFairR_halt_fairDeadlock {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (hfair : PE'.IsFair F.dist) (r : ResolvedExec State Label) (h : r.trans.Terminates)
    (_hcons : (PE'.lowerFairR F).Consistent r)
    (h_none : (PE'.lowerFairR F).scheduler.next r none ≠ 0)
    (hinit : PE'.initState = PMF.pure (sys.distF F).init) :
    F.FairDeadlock (r.endState h) := by
  classical
  -- Reachability lift: a positive-mass resolved `PE'`-run `R''` at which `PE'` halts, whose
  -- end-belief `R''.endState` contains the concrete end-state `r.endState h` and is resolvable.
  obtain ⟨R'', hT'', hpm'', hmem'', hres, hnone''⟩ :=
    lowerFairR_halt_coherent_lift F PE' r h _hcons h_none hinit
  have hcons'' : PE'.Consistent R'' := probOfR_ne_zero_imp_consistent PE' R'' hT'' hpm''
  -- `𝒟f`-fairness: `PE'` halts at the consistent `R''` only from an `F.dist`-fair-deadlock belief.
  have hdl : F.dist.FairDeadlock (R''.endState hT'') :=
    hfair.halt_fairDeadlock R'' hT'' hcons'' hnone''
  -- Transfer the belief-fair-deadlock to the concrete end-state via resolvability.
  exact F.distF_fairDeadlock_belief hres hdl (r.endState h) hmem''

/-! ### The finite-branching route to crux B (finitely-branching + finite mass-splitting)

The route this development takes, in place of a compactness/tightness input. When the achieving
execution `PE'` is *finitely branching* (at every history only finitely many transitions are
scheduled with positive probability) **and** *finite mass-splitting* (every emitted
`ω : PMF (PMF State)` has finite support), the belief-lift tree of crux B is genuinely finitely
branching, so an infinite coherent
`PE'`-belief-run is threaded by König (`exists_infinite_chain`) — exactly as in
`FairStrongProbabilisticSimulation.exists_infinite_coupled_lift` — with **no tightness, no
continuity, no `[Fintype State]`, and no image-finiteness of `sys`**, and no phantom (König threads
a genuine consistent run rather than taking a compactness limit, so it survives beliefs escaping to
infinity).

The two conditions are exactly the two branching axes: finite branching bounds the emitted `(l, ω)`;
finite mass-splitting bounds the sampled successor beliefs `ν ∈ ω.support`. Dropping either
re-admits an accumulation counterexample. Finite branching is what the
`FairStrongProbabilisticSimulation` construction provides for free
(`abstractMarginal_simJointExecR_next_support_finite`, under an image-finite simulation source), so
these are the natural hypotheses for lowering a simulation-built `PE'`. -/

/-- **Finite branching.** At every terminating history the scheduler emits only finitely many
transitions with positive probability. This is the property established for the schedulers built by
`FairStrongProbabilisticSimulation.abstractMarginal_simJointExecR_next_support_finite`. -/
def ResolvedProbabilisticExecution.FinitelyBranching {S L : Type} {sys : System S L}
    (pe : ResolvedProbabilisticExecution sys) : Prop :=
  ∀ r : ResolvedExec S L, r.trans.Terminates → (pe.scheduler.next r).support.Finite

/-- **Finite mass-splitting.** Every emitted hyper-distribution `ω : PMF (PMF State)` splits the
current belief into only finitely many sub-beliefs (`ω.support` finite). This is *not* forced by
`𝒟f`'s step relation (`hyperStep` constrains only the flattened `ω.bind id`), so it is a genuine
extra hypothesis on `PE'` — the second branching axis of the belief-lift tree. -/
def ResolvedProbabilisticExecution.FiniteMassSplitting {sys : System State Label} (F : Fairness sys)
    (PE' : ResolvedProbabilisticExecution (sys.distF F)) : Prop :=
  ∀ (E : ResolvedExec (PMF State) Label) (l : Label) (ω : PMF (PMF State)),
    some (l, ω) ∈ (PE'.scheduler.next E).support → ω.support.Finite

/-! ### The time-local coherence bridge (crux B on the finite-branching route)

The finite-branching route to crux B lifts the concrete run `r` to an infinite `PE'`-**Consistent**
*resolved* belief-run `R' : ResolvedExec (PMF State) Label` and reads its `F.dist`-fairness through
`PE'.IsFair.inf_fair`, transferring it to `r` by `distFairHyperKernel_fair_transfer`. That transfer
is **time-local**: to make step `n` of `r` fair it needs `r`'s recorded `μ` reproduced by
`distFairHyperKernel F (R'.take n) l ω s` at the belief-history `R'.take n`, whose *fair-branch is
read at its final belief* `(R'.take n).endState = R'.stateAt n` — the **time-`n` belief** — with the
concrete state `s = r.stateAt n` in that belief's support.

This is exactly the reading `lowerFairR`'s own consistency records: its scheduler samples a resolved
belief-run from `beliefTCR` restricted to the resolved, time-local, prefix-local coherence
`RCoherentTL F r`, which matches each recorded step `n` at *its own* time-`n` belief
`(R'.take n).toExec.endState` (unlike a de-resolved, final-belief filter, whose per-prefix readings
would not nest into a König chain of resolved belief-prefixes).

`exists_timeLocal_coherent_resolved_lift` produces `R'` by König (`exists_infinite_chain`) over the
finitely-branching tree of resolved belief-prefixes (`hfb` bounds the emitted `(l, ω)`, `hms` the
sampled successor beliefs `ν`), each finite prefix supplied by `exists_positive_coherent_prefix`
(via `beliefTCR_support`). Everything downstream of it — the König assembly of `R'` and the
`F.dist → F` fairness transfer — is discharged unconditionally by
`lowerFairR_phantom_free_of_finiteBranching`, below. -/

/-- **König chain source (crux B).** For every `n ≥ 1`, the `lowerFairR`-consistency of the infinite
concrete run `r` supplies a length-`n` (terminated at `n`) resolved `PE'`-belief-run `w` that is
time-locally coherent with `r.take n` and has positive `PE'`-path-mass. Read `hcons` at position
`n` (a genuine step, since `r` is infinite): it forces the `h_term`/`h0` branch of
`lowerFairRSched.next (r.take n)`, whose emission binds through the
`RCoherentTL (r.take n)`-filtered
`beliefTCR`; a support element `w` of that filter is coherent with all of `r.take n` and, by
`beliefTCR_support`, terminates and has positive `probOfR`. Its label list is `r.take n`'s labels
(length `n`), so it terminates exactly at `n`. The hypothesis `1 ≤ n` excludes the length-0 cone
fallback: its RCoherence at position `0` would demand a step the length-0 run lacks, so the cone
mass is genuinely positive and `beliefTCR_support` applies. (The `n = 0` node of the König tree is
the root, supplied directly.) -/
private theorem exists_positive_coherent_prefix {sys : System State Label} (F : Fairness sys)
    (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (r : ResolvedExec State Label) (hinf : ¬ r.trans.Terminates)
    (hcons : (PE'.lowerFairR F).Consistent r) (n : ℕ) (hn : 1 ≤ n) :
    ∃ w : ResolvedExec (PMF State) Label,
      w.trans.TerminatedAt n ∧ PE'.RCoherentTL F (r.take n) w ∧
      ∃ hT : w.trans.Terminates, PE'.probOfR w hT ≠ 0 := by
  classical
  set pe' := PE'.average.distFToDist F with hpe'
  -- `r` has a genuine recorded step at position `n`.
  have hrne : r.trans.get? n ≠ none := fun hc => hinf ⟨n, hc⟩
  obtain ⟨t, hrget'⟩ := Option.ne_none_iff_exists'.mp hrne
  obtain ⟨⟨l, μ⟩, s'⟩ := t
  have hrget : r.trans.get? n = some ((l, μ), s') := hrget'
  -- Read `lowerFairR`-consistency at position `n`.
  obtain ⟨hnext, -⟩ := hcons.2 n l μ s' hrget
  -- `(r.take n).toExec` terminates (finite prefix); force the `h_term`/`h0` branch.
  have hTe : (ResolvedExec.toExec (r.take n)).trans.Terminates :=
    (ResolvedExec.toExec_terminates_iff (r.take n)).mpr (take_terminates r n)
  set labs := ((ResolvedExec.toExec (r.take n)).trans.toList hTe).map Prod.fst with hlabs
  set s₀ := (ResolvedExec.toExec (r.take n)).endState hTe with hs₀
  -- Unfold the scheduler emission (mirror of `lowerFairRSched.valid`).
  have hmem : some (l, μ) ∈ ((PE'.lowerFairR F).scheduler.next (r.take n)).support :=
    (PMF.mem_support_iff _ _).mpr hnext
  change some (l, μ) ∈
    (open Classical in
      if h_term : (ResolvedExec.toExec (r.take n)).trans.Terminates then
        if h0 : (∑' R', Set.indicator {R' | PE'.RCoherentTL F (r.take n) R'}
            (PE'.beliefTCR F (((ResolvedExec.toExec (r.take n)).trans.toList h_term).map Prod.fst)
              ((ResolvedExec.toExec (r.take n)).endState h_term)) R') ≠ 0 then
          ((PE'.beliefTCR F (((ResolvedExec.toExec (r.take n)).trans.toList h_term).map Prod.fst)
              ((ResolvedExec.toExec (r.take n)).endState h_term)).filter
              {R' | PE'.RCoherentTL F (r.take n) R'} _).bind (fun R' =>
            ((PE'.average.distFToDist F).scheduler.next (ResolvedExec.toExec R')).bind (fun opt =>
              match opt with
              | none         => PMF.pure none
              | some (l', ω) =>
                ((PE'.average.distFToDist F).distFairHyperKernel F (ResolvedExec.toExec R') l' ω
                    ((ResolvedExec.toExec (r.take n)).endState h_term)).map
                    (fun μ' => some (l', μ'))))
        else PMF.pure none
      else PMF.pure none).support at hmem
  rw [dif_pos hTe] at hmem
  split_ifs at hmem with h0
  · rw [PMF.mem_support_bind_iff] at hmem
    obtain ⟨w, hw_filter, -⟩ := hmem
    rw [PMF.mem_support_filter_iff] at hw_filter
    obtain ⟨hw_coh, hw_belief⟩ := hw_filter
    -- `r`'s step at position `0` (exists since `r` is infinite and `n ≥ 1`, so position `0 < n`).
    have hr0ne : r.trans.get? 0 ≠ none := fun hc => hinf ⟨0, hc⟩
    obtain ⟨t0, hr0get'⟩ := Option.ne_none_iff_exists'.mp hr0ne
    obtain ⟨⟨l0, μ0⟩, s0'⟩ := t0
    have hr0take : (r.take n).trans.get? 0 = some ((l0, μ0), s0') := by
      rw [take_trans_get? r hn]; exact hr0get'
    have hr0state : (r.take n).stateAt 0 = some r.init := rfl
    -- Positive cone mass. Otherwise `beliefTCR = pure ⟨pure s₀, nil⟩`, so `w = ⟨pure s₀, nil⟩`
    -- (length 0); but coherence at position `0` demands a step `w` (length 0) does not have.
    have hpos : (∑' R'', PE'.beliefTCRw F labs s₀ R'') ≠ 0 := by
      intro hzero
      have hbtcr : PE'.beliefTCR F labs s₀ = PMF.pure ⟨PMF.pure s₀, Seq.nil⟩ := by
        rw [ResolvedProbabilisticExecution.beliefTCR, dif_neg (by rw [hzero]; simp)]
      rw [hbtcr, PMF.mem_support_pure_iff] at hw_belief
      -- Coherence of the length-0 fallback at position `0`: no such belief-step exists.
      obtain ⟨ν, ω, ν', hwstate, hwget, -, -⟩ :=
        hw_coh 0 r.init l0 μ0 s0' hr0state hr0take
      rw [hw_belief] at hwget
      change (Seq.nil : Seq ((Label × PMF (PMF State)) × PMF State)).get? 0 = _ at hwget
      rw [Stream'.Seq.get?_nil] at hwget
      exact absurd hwget (by simp)
    obtain ⟨hwT, hwlab, -, hwpm⟩ := PE'.beliefTCR_support F labs s₀ hpos w hw_belief
    -- `labs` has length `n` (the label list of the length-`n` prefix `r.take n`), so `w`, whose
    -- `toExec`-label list is `labs`, terminates exactly at `n`.
    have hlabs_len : labs.length = n := by
      rw [hlabs, List.length_map]
      have hlen : ((ResolvedExec.toExec (r.take n)).trans.toList hTe).length = Nat.find hTe :=
        Stream'.Seq.length_toList _ hTe
      rw [hlen]
      -- `Nat.find hTe = n`: `toExec (r.take n)` terminates exactly where `r.take n` does, at `n`.
      have hfind : Nat.find hTe = Nat.find (take_terminates r n) :=
        Nat.find_congr' (fun {m} => ResolvedExec.toExec_terminatedAt_iff (r.take n) m)
      rw [hfind, take_find r n hinf]
    have hwtermn : w.trans.TerminatedAt n := by
      rw [← ResolvedExec.toExec_terminatedAt_iff]
      have hiff : (ResolvedExec.toExec w).trans.TerminatedAt n ↔
          (Seq.map Prod.fst (ResolvedExec.toExec w).trans).TerminatedAt n := by
        unfold Stream'.Seq.TerminatedAt
        rw [Stream'.Seq.map_get?, Option.map_eq_none_iff]
      rw [hiff, hwlab]
      change (Seq.ofList labs).get? n = none
      rw [Stream'.Seq.ofList_get?]
      exact List.getElem?_eq_none (by rw [hlabs_len])
    exact ⟨w, hwtermn, hw_coh, hwT, hwpm⟩
  · -- Fallback branch is impossible (the emission is `PMF.pure none`).
    rw [PMF.mem_support_pure_iff] at hmem
    exact absurd hmem (by simp)

/-- **König chain source with a common initial belief (the single residual crux-B gap).**
Strengthens `exists_positive_coherent_prefix` by pinning *one* initial belief `μ₀` shared by the
coherent positive prefixes at *every* level. This is exactly the fact `exists_infinite_chain`
requires (a fixed `root`): König threads a chain of prefixes that must all start at the same node,
and the reconstructed `R'.init` is that common `μ₀`.

Why it is the residue and not derivable from `exists_positive_coherent_prefix` alone: the
per-level prefixes returned by `exists_positive_coherent_prefix` are drawn from the belief-cone
`beliefTCR`, whose runs are only constrained to have *some* initial belief in the support of
`PE'.initState` (a `PMF (PMF State)`); when `PE'.initState` is not a Dirac the different levels may
a priori choose *different* initial beliefs, and neither `hfb` (finite branching of the scheduler)
nor `hms` (finite mass-splitting) bounds the initial-belief support. In the intended use
(`lower_of_finiteBranching`) `PE'.initState = PMF.pure (sys.distF F).init` is Dirac, so
`μ₀ = (sys.distF F).init` is forced and this lemma is immediate; but the ambient statement of
`exists_timeLocal_coherent_resolved_lift` does not carry that `hinit`, so the common-initial-belief
selection is isolated in this helper. Everything else — the finitely-branching König tree, its
reconstruction, consistency and time-local coherence of the assembled infinite run — is proven
unconditionally on top of it. -/
private theorem exists_positive_coherent_prefix_common_init {sys : System State Label}
    (F : Fairness sys) (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (_hfb : PE'.FinitelyBranching) (_hms : PE'.FiniteMassSplitting F)
    (r : ResolvedExec State Label) (hinf : ¬ r.trans.Terminates)
    (hcons : (PE'.lowerFairR F).Consistent r)
    (hinit : PE'.initState = PMF.pure (sys.distF F).init) :
    ∃ μ₀ : PMF State, ∀ n : ℕ, ∃ w : ResolvedExec (PMF State) Label,
      w.init = μ₀ ∧ w.trans.TerminatedAt n ∧ PE'.RCoherentTL F (r.take n) w ∧
      ∃ hT : w.trans.Terminates, PE'.probOfR w hT ≠ 0 := by
  classical
  refine ⟨PMF.pure sys.init, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    refine ⟨⟨PMF.pure sys.init, Seq.nil⟩, rfl, Stream'.Seq.terminatedAt_zero_iff.mpr rfl, ?_,
      Stream'.Seq.terminates_nil, ?_⟩
    · intro m s l μ s' _ hget
      have hnone : (r.take 0).trans.get? m = none :=
        Stream'.Seq.terminated_stable _ (Nat.zero_le m) (take_terminatedAt r 0 hinf)
      rw [hnone] at hget
      exact absurd hget (by simp)
    · rw [PE'.probOfR_nil, hinit]
      change (PMF.pure (PMF.pure sys.init)) (PMF.pure sys.init) ≠ 0
      simp
  · obtain ⟨w, hterm, hcoh, hT, hpm⟩ :=
      exists_positive_coherent_prefix F PE' r hinf hcons n hn1
    have hi : PE'.initState w.init ≠ 0 := (probOfR_ne_zero_imp_consistent PE' w hT hpm).1
    rw [hinit] at hi
    have hwi : w.init = (sys.distF F).init := by
      have h2 : w.init ∈ (PMF.pure ((sys.distF F).init)).support := (PMF.mem_support_iff _ _).mpr hi
      rw [PMF.support_pure, Set.mem_singleton_iff] at h2
      exact h2
    exact ⟨w, hwi, hterm, hcoh, hT, hpm⟩

/-- **`RCoherentTL` is prefix-stable.** Time-local coherence with `r.take n` restricts to coherence
of the length-`k` prefix `w.take k` with `r.take k`, for `k ≤ n`: position `m < k` reads only data
below `k` on both sides (`take_stateAt`, `take_trans_get?`, `take_take`, all agreeing with the
un-truncated readings). -/
private theorem RCoherentTL_take {sys : System State Label} (F : Fairness sys)
    (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (r : ResolvedExec State Label) (w : ResolvedExec (PMF State) Label) {n k : ℕ} (hkn : k ≤ n)
    (hcoh : PE'.RCoherentTL F (r.take n) w) :
    PE'.RCoherentTL F (r.take k) (w.take k) := by
  intro m s l μ s' hstate hget
  -- The recorded step of `r.take k` at `m` requires `m < k`.
  have hmk : m < k := by
    by_contra hc
    have : (r.take k).trans.get? m = none := by
      change (Seq.ofList (Seq.take k r.trans)).get? m = none
      rw [Stream'.Seq.ofList_get?]
      exact List.getElem?_eq_none
        (Nat.le_trans Stream'.Seq.length_take_le (Nat.le_of_not_lt hc))
    rw [this] at hget; exact absurd hget (by simp)
  -- Translate the `r.take k`-readings to `r.take n`-readings (both equal `r`'s readings at `m`).
  have hmn : m < n := Nat.lt_of_lt_of_le hmk hkn
  have hstate_n : (r.take n).stateAt m = some s := by
    rw [take_stateAt r (Nat.le_of_lt hmn)]
    rw [take_stateAt r (Nat.le_of_lt hmk)] at hstate; exact hstate
  have hget_n : (r.take n).trans.get? m = some ((l, μ), s') := by
    rw [take_trans_get? r hmn]
    rw [take_trans_get? r hmk] at hget; exact hget
  obtain ⟨ν, ω, ν', hwstate, hwget, hsupp, hker⟩ := hcoh m s l μ s' hstate_n hget_n
  refine ⟨ν, ω, ν', ?_, ?_, hsupp, ?_⟩
  · rw [take_stateAt w (Nat.le_of_lt hmk)]; exact hwstate
  · rw [take_trans_get? w hmk]; exact hwget
  · rw [take_take w k m (Nat.le_of_lt hmk)]; exact hker

/-- **The residual crux-B gap: a time-local coherent infinite resolved belief-lift.** From a
`lowerFairR`-consistent infinite concrete run `r`, under finite branching (`hfb`) and finite
mass-splitting (`hms`), there is an infinite `PE'`-**Consistent** *resolved* belief-run `R'` that is
**time-locally coherent** with `r`: at every position `n`, `r`'s recorded step `((l, μ), s')` is
matched by a resolved belief-step `((l, ω), ν')` of `R'` at the *same* label `l`, with the current
concrete state `s = r.stateAt n` lying in the *time-`n`* belief `R'.stateAt n`'s support, and `μ`
reproduced by the fairness-revealing kernel evaluated at the prefix `R'.take n` (whose fair-branch
is read at `(R'.take n).endState = R'.stateAt n = ν`).

This is precisely the reading the `F.dist → F` transfer consumes, and precisely the resolved,
time-local, prefix-local reading `lowerFairR`'s own `RCoherentTL`-based consistency records (a
de-resolved, single-final-belief filter would not supply it — see the section docstring).

Proven here by a finitely-branching König lift mirroring
`FairStrongProbabilisticSimulation.exists_infinite_coupled_lift`: the tree nodes are the length-`n`
positive coherent belief-prefixes of `r` (supplied with a common initial belief by
`exists_positive_coherent_prefix_common_init`); a node's children extend it by one belief-step
`((lₙ, ω), ν')` whose label `lₙ` is pinned by `r`'s `n`-th step (via `RCoherentTL`), whose emission
`ω` ranges over the finite `PE'.scheduler.next`-support (`hfb`) and whose sampled successor belief
`ν' ∈ ω.support` is finite (`hms`), so branching is finite; `exists_infinite_chain` threads the
infinite run `R'`, reconstructed from the König path, and its consistency and time-local coherence
are read off each level-`(n+1)` node (both prefix-stable). -/
theorem ResolvedProbabilisticExecution.exists_timeLocal_coherent_resolved_lift
    {sys : System State Label} (F : Fairness sys)
    (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (hfb : PE'.FinitelyBranching) (hms : PE'.FiniteMassSplitting F)
    (r : ResolvedExec State Label) (hinf : ¬ r.trans.Terminates)
    (hcons : (PE'.lowerFairR F).Consistent r)
    (hinit : PE'.initState = PMF.pure (sys.distF F).init) :
    ∃ R' : ResolvedExec (PMF State) Label,
      ¬ R'.trans.Terminates ∧ PE'.Consistent R' ∧
      ∀ (n : ℕ) (s : State) (l : Label) (μ : PMF State) (s' : State),
        r.stateAt n = some s → r.trans.get? n = some ((l, μ), s') →
          ∃ (ν : PMF State) (ω : PMF (PMF State)) (ν' : PMF State),
            R'.stateAt n = some ν ∧ R'.trans.get? n = some ((l, ω), ν') ∧
            s ∈ ν.support ∧
            μ ∈ ((PE'.average.distFToDist F).distFairHyperKernel F
                (ResolvedExec.toExec (R'.take n)) l ω s).support := by
  classical
  -- A common initial belief `μ₀` and coherent positive prefixes of every length (crux-B source).
  obtain ⟨μ₀, hpref⟩ :=
    exists_positive_coherent_prefix_common_init F PE' hfb hms r hinf hcons hinit
  -- The König tree.  A node at level `n` is a length-`n` (terminated at `n`) belief-run coherent
  -- with `r.take n`, starting at `μ₀`, with positive path mass.  `succ n w w'` extends `w` by one
  -- belief-step to such a level-`(n+1)` node.
  set root : ResolvedExec (PMF State) Label := ⟨μ₀, Seq.nil⟩ with hroot
  set succ : ℕ → ResolvedExec (PMF State) Label → ResolvedExec (PMF State) Label → Prop :=
    fun n w w' =>
      w'.take n = w ∧ PE'.RCoherentTL F (r.take (n + 1)) w' ∧
        w'.trans.TerminatedAt (n + 1) ∧
        ∃ hT' : w'.trans.Terminates, PE'.probOfR w' hT' ≠ 0
    with hsucc
  -- **(A) König chains of every length.**
  have hchain : ∀ n : ℕ, ∃ f : ℕ → ResolvedExec (PMF State) Label,
      f 0 = root ∧ ∀ i, i < n → succ i (f i) (f (i + 1)) := by
    intro n
    obtain ⟨W, hWinit, hWterm, hWcoh, hWT, hWpm⟩ := hpref n
    refine ⟨fun i => W.take i, ?_, ?_⟩
    · -- `f 0 = root`: `W.take 0 = ⟨W.init, nil⟩ = ⟨μ₀, nil⟩`.
      change W.take 0 = root
      apply AlterSeq.mk.injEq .. |>.mpr
      exact ⟨hWinit, rfl⟩
    · intro i hi
      refine ⟨take_take W (i + 1) i (Nat.le_succ i), ?_, ?_, ?_⟩
      · -- coherence of the length-`(i+1)` prefix `W.take (i+1)` with `r.take (i+1)`.
        exact RCoherentTL_take F PE' r W (Nat.succ_le_of_lt hi) hWcoh
      · -- terminated at `i+1`: the length-`(i+1)` prefix's transition stream has length `≤ i+1`.
        change (Seq.ofList (Seq.take (i + 1) W.trans)).get? (i + 1) = none
        rw [Stream'.Seq.ofList_get?]
        exact List.getElem?_eq_none (Nat.le_trans Stream'.Seq.length_take_le (Nat.le_refl _))
      · exact ⟨take_terminates W (i + 1), probOfR_take_ne_zero PE' W hWT hWpm (i + 1)⟩
  -- **(B) Finite branching.**  A child `w'` of `w` at level `n` is determined by its last
  -- belief-transition `w'.trans.get? n = some ((lₙ, ω), ν')`, whose label `lₙ` is pinned by `r`'s
  -- `n`-th step (via `RCoherentTL`), and whose `ω` ranges over the finite `PE'.scheduler.next w`-
  -- support (`hfb`) with `ν' ∈ ω.support` finite (`hms`).  Inject `w' ↦ (ω, ν')`.
  have hfinChildren : ∀ (n : ℕ) (w : ResolvedExec (PMF State) Label),
      {w' | succ n w w'}.Finite := by
    intro n w
    -- `r`'s recorded step at `n` (exists since `r` is infinite).
    obtain ⟨cstep, hrget⟩ : ∃ t, r.trans.get? n = some t := by
      rcases hc : r.trans.get? n with _ | t
      · exact absurd ⟨n, hc⟩ hinf
      · exact ⟨t, rfl⟩
    obtain ⟨⟨lₙ, μₙ⟩, sₙ'⟩ := cstep
    -- `r`'s current state at `n`.
    obtain ⟨sₙ, hrstate⟩ : ∃ s, r.stateAt n = some s := by
      rcases n with _ | k
      · exact ⟨r.init, rfl⟩
      · have hne : r.stateAt (k + 1) ≠ none := by
          intro hc
          change (r.trans.get? k).map Prod.snd = none at hc
          rw [Option.map_eq_none_iff] at hc
          exact hinf ⟨k, hc⟩
        exact Option.ne_none_iff_exists'.mp hne
    -- Pin the readings of `r.take (n+1)` at position `n` to `r`'s.
    have hrget_np1 : (r.take (n + 1)).trans.get? n = some ((lₙ, μₙ), sₙ') := by
      rw [take_trans_get? r (Nat.lt_succ_self n)]; exact hrget
    have hrstate_np1 : (r.take (n + 1)).stateAt n = some sₙ := by
      rw [take_stateAt r (Nat.le_succ n)]; exact hrstate
    -- A child forces `w` to terminate (`w'.take n = w` is a finite prefix).  Otherwise the child
    -- set is empty.
    by_cases hwT : w.trans.Terminates
    swap
    · -- No child: `succ n w w'` gives `w'.take n = w`, but `w'.take n` always terminates.
      apply Set.Finite.subset Set.finite_empty
      rintro w' ⟨htake, -, -, -⟩
      exact absurd (htake ▸ take_terminates w' n) hwT
    -- Target finite set: pairs `(ω, ν')` with a scheduled emission `some (lₙ, ω)` and `ν' ∈ ω`.
    have hFinTarget : {p : PMF (PMF State) × PMF State |
        some (lₙ, p.1) ∈ (PE'.scheduler.next w).support ∧ p.2 ∈ p.1.support}.Finite := by
      -- `{ω | some (lₙ, ω) ∈ supp(next w)}` is finite (preimage of the finite support under the
      -- injective `ω ↦ some (lₙ, ω)`).
      have hωfin :
          {ω : PMF (PMF State) | some (lₙ, ω) ∈ (PE'.scheduler.next w).support}.Finite := by
        apply Set.Finite.preimage _ (hfb w hwT)
        intro ω₁ _ ω₂ _ heq
        simp only [Option.some.injEq, Prod.mk.injEq, true_and] at heq
        exact heq
      apply Set.Finite.subset
        (Set.Finite.biUnion hωfin (t := fun ω => (fun ν' => (ω, ν')) '' ω.support)
          (fun ω hω => (hms w lₙ ω hω).image _))
      rintro ⟨ω, ν'⟩ ⟨hsched, hν'⟩
      exact Set.mem_biUnion hsched ⟨ν', hν', rfl⟩
    -- Per-child data: the `n`-th belief-step is `((lₙ, ω), ν')` with `ω`, `ν'` in the target.
    have hchildData : ∀ w' ∈ {w' | succ n w w'}, ∃ (ω : PMF (PMF State)) (ν' : PMF State),
        w'.trans.get? n = some ((lₙ, ω), ν') ∧
        some (lₙ, ω) ∈ (PE'.scheduler.next w).support ∧ ν' ∈ ω.support := by
      rintro w' ⟨htake, hcoh, hterm, hT', hpm⟩
      -- Coherence at `n` pins the label to `lₙ` and exposes `w'`'s belief-step.
      obtain ⟨ν, ω, ν', hw'state, hw'get, -, -⟩ :=
        hcoh n sₙ lₙ μₙ sₙ' hrstate_np1 hrget_np1
      -- Consistency of `w'` (positive path mass) at `n`.
      have hcons' : PE'.Consistent w' := probOfR_ne_zero_imp_consistent PE' w' hT' hpm
      obtain ⟨hnext, hων'⟩ := hcons'.2 n lₙ ω ν' hw'get
      rw [htake] at hnext
      exact ⟨ω, ν', hw'get, (PMF.mem_support_iff _ _).mpr hnext,
        (PMF.mem_support_iff _ _).mpr hων'⟩
    -- Finiteness via injective image.
    apply Set.Finite.of_injOn
      (f := fun w' => (w'.trans.get? n).map (fun t => (t.1.2, t.2)))
      (t := (fun p => some p) '' {p : PMF (PMF State) × PMF State |
        some (lₙ, p.1) ∈ (PE'.scheduler.next w).support ∧ p.2 ∈ p.1.support})
    · rintro w' hw'
      obtain ⟨ω, ν', hget, hsched, hν'⟩ := hchildData w' hw'
      refine ⟨(ω, ν'), ⟨hsched, hν'⟩, ?_⟩
      simp only [hget, Option.map_some]
    · -- Injectivity on children.
      rintro w'₁ hw'₁ w'₂ hw'₂ heq
      obtain ⟨ω₁, ν'₁, hget₁, -, -⟩ := hchildData w'₁ hw'₁
      obtain ⟨ω₂, ν'₂, hget₂, -, -⟩ := hchildData w'₂ hw'₂
      simp only [hget₁, hget₂, Option.map_some, Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨hω, hν⟩ := heq
      subst hω; subst hν
      have hgeteq : w'₁.trans.get? n = w'₂.trans.get? n := by rw [hget₁, hget₂]
      obtain ⟨htake₁, -, hterm₁, -⟩ := hw'₁
      obtain ⟨htake₂, -, hterm₂, -⟩ := hw'₂
      refine resolvedExec_eq_of_take_get? w'₁ w'₂ n ?_ (by rw [htake₁, htake₂]) hgeteq hterm₁ hterm₂
      have e1 : w'₁.init = w.init := by rw [← htake₁]; rfl
      have e2 : w'₂.init = w.init := by rw [← htake₂]; rfl
      rw [e1, e2]
    · exact hFinTarget.image _
  -- **(C) König's lemma.**
  obtain ⟨f, hf0, hfstep⟩ := exists_infinite_chain succ root hfinChildren hchain
  have hfstep' : ∀ i, (f (i + 1)).take i = f i ∧
      PE'.RCoherentTL F (r.take (i + 1)) (f (i + 1)) ∧
      (f (i + 1)).trans.TerminatedAt (i + 1) ∧
      ∃ hT' : (f (i + 1)).trans.Terminates, PE'.probOfR (f (i + 1)) hT' ≠ 0 := hfstep
  -- **Prefix stability.**  `(f j).take i = f i` for `i ≤ j`.
  have hstable : ∀ i j, i ≤ j → (f j).take i = f i := by
    intro i j hij
    induction j with
    | zero =>
      obtain rfl : i = 0 := Nat.le_zero.mp hij
      rw [hf0]; rfl
    | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hij) with hlt | heq
      · have hik : i ≤ k := Nat.lt_succ_iff.mp hlt
        rw [← take_take (f (k + 1)) k i hik, (hfstep' k).1]
        exact ih hik
      · subst heq; exact take_self_of_terminatedAt (f (k + 1)) (k + 1) (hfstep' k).2.2.1
  -- Each `f (n+1)` has a genuine `n`-th transition (via coherence with `r`'s `n`-th step).
  have hsome : ∀ n, (f (n + 1)).trans.get? n ≠ none := by
    intro n htn
    -- `r`'s `n`-th step exists (infinite); coherence gives `f (n+1)` a step at `n`.
    obtain ⟨cstep, hrget⟩ : ∃ t, r.trans.get? n = some t := by
      rcases hc : r.trans.get? n with _ | t
      · exact absurd ⟨n, hc⟩ hinf
      · exact ⟨t, rfl⟩
    obtain ⟨⟨lₙ, μₙ⟩, sₙ'⟩ := cstep
    obtain ⟨sₙ, hrstate⟩ : ∃ s, r.stateAt n = some s := by
      rcases n with _ | k
      · exact ⟨r.init, rfl⟩
      · have hne : r.stateAt (k + 1) ≠ none := by
          intro hc
          change (r.trans.get? k).map Prod.snd = none at hc
          rw [Option.map_eq_none_iff] at hc
          exact hinf ⟨k, hc⟩
        exact Option.ne_none_iff_exists'.mp hne
    have hrget_np1 : (r.take (n + 1)).trans.get? n = some ((lₙ, μₙ), sₙ') := by
      rw [take_trans_get? r (Nat.lt_succ_self n)]; exact hrget
    have hrstate_np1 : (r.take (n + 1)).stateAt n = some sₙ := by
      rw [take_stateAt r (Nat.le_succ n)]; exact hrstate
    obtain ⟨ν, ω, ν', -, hw'get, -, -⟩ :=
      (hfstep' n).2.1 n sₙ lₙ μₙ sₙ' hrstate_np1 hrget_np1
    rw [htn] at hw'get; exact absurd hw'get (by simp)
  -- Position-`n` transition of the assembled run is `f m`'s for any `m > n`.
  have hgetstable : ∀ n m, n < m → (f m).trans.get? n = (f (n + 1)).trans.get? n := by
    intro n m hnm
    have h1 : (f m).take (n + 1) = f (n + 1) := hstable (n + 1) m hnm
    rw [← h1, take_trans_get? (f m) (Nat.lt_succ_self n)]
  -- **(D) Assemble the infinite belief-run `R'`.**
  have hstreamSeq : ∀ n, (fun m => (f (m + 1)).trans.get? m) n = none →
      (fun m => (f (m + 1)).trans.get? m) (n + 1) = none := fun n hn => absurd hn (hsome n)
  set R' : ResolvedExec (PMF State) Label :=
    ⟨μ₀, ⟨fun n => (f (n + 1)).trans.get? n, hstreamSeq _⟩⟩ with hR'
  have hR'get : ∀ n, R'.trans.get? n = (f (n + 1)).trans.get? n := fun n => rfl
  have hR'inf : ¬ R'.trans.Terminates := by
    rintro ⟨n, hn⟩
    rw [Stream'.Seq.TerminatedAt, hR'get n] at hn
    exact hsome n hn
  have hR'take : ∀ n, R'.take n = f n := by
    intro n
    have hfnterm : (f n).trans.TerminatedAt n := by
      cases n with
      | zero => rw [hf0]; exact Stream'.Seq.terminatedAt_zero_iff.mpr rfl
      | succ k => exact (hfstep' k).2.2.1
    have hfninit : (f n).init = μ₀ := by
      have := hstable 0 n (Nat.zero_le n)
      rw [hf0] at this
      have h2 : (f n).init = ((f n).take 0).init := rfl
      rw [h2, this]
    apply AlterSeq.mk.injEq .. |>.mpr
    refine ⟨hfninit.symm, ?_⟩
    apply Stream'.Seq.ext
    intro m
    by_cases hm : m < n
    · rw [Stream'.Seq.ofList_get?, seq_getElem?_take R'.trans n m hm, hR'get m,
        ← hgetstable m n hm]
    · have hle : n ≤ m := Nat.le_of_not_lt hm
      rw [Stream'.Seq.ofList_get?]
      rw [List.getElem?_eq_none (Nat.le_trans Stream'.Seq.length_take_le hle),
        Stream'.Seq.le_stable (f n).trans hle hfnterm]
  refine ⟨R', hR'inf, ?_, ?_⟩
  · -- `PE'.Consistent R'`.
    refine ⟨?_, ?_⟩
    · -- Initial mass: `R'.init = μ₀ = (f 1).init`, whose consistency (positive prefix `f 1`)
      -- supplies `PE'.initState μ₀ ≠ 0`.
      obtain ⟨hT1, hpm1⟩ := (hfstep' 0).2.2.2
      have hcons1 : PE'.Consistent (f 1) := probOfR_ne_zero_imp_consistent PE' _ hT1 hpm1
      have hf1init : (f 1).init = μ₀ := by
        have := hstable 0 1 (Nat.zero_le 1)
        rw [hf0] at this
        have h2 : (f 1).init = ((f 1).take 0).init := rfl
        rw [h2, this]
      change PE'.initState R'.init ≠ 0
      rw [show R'.init = μ₀ from rfl, ← hf1init]
      exact hcons1.1
    · -- Step consistency at each `n`: transfer from the consistent node `f (n+1)`.
      intro n l μ s' hget
      obtain ⟨hTn, hpmn⟩ := (hfstep' n).2.2.2
      have hconsn : PE'.Consistent (f (n + 1)) := probOfR_ne_zero_imp_consistent PE' _ hTn hpmn
      have hgetn : (f (n + 1)).trans.get? n = some ((l, μ), s') := by
        rw [← hR'get n]; exact hget
      obtain ⟨hnext, hμ⟩ := hconsn.2 n l μ s' hgetn
      refine ⟨?_, hμ⟩
      rw [hR'take n, ← (hfstep' n).1]
      exact hnext
  · -- Time-local coherence `RCoherentTL F r R'` (the `∀ n …` conjunct, definitionally).
    intro n s l μ s' hrstate hrget
    -- Read coherence at position `n` from the level-`(n+1)` node `f (n+1)`.
    have hrstate_np1 : (r.take (n + 1)).stateAt n = some s := by
      rw [take_stateAt r (Nat.le_succ n)]; exact hrstate
    have hrget_np1 : (r.take (n + 1)).trans.get? n = some ((l, μ), s') := by
      rw [take_trans_get? r (Nat.lt_succ_self n)]; exact hrget
    obtain ⟨ν, ω, ν', hstate, hgetω, hsupp, hker⟩ :=
      (hfstep' n).2.1 n s l μ s' hrstate_np1 hrget_np1
    refine ⟨ν, ω, ν', ?_, ?_, hsupp, ?_⟩
    · -- `R'.stateAt n = (f (n+1)).stateAt n = ν` (positions `≤ n+1` of `R'` agree with `f (n+1)`).
      have hR'sn : R'.stateAt n = (f (n + 1)).stateAt n := by
        rw [← hR'take (n + 1), take_stateAt R' (Nat.le_succ n)]
      rw [hR'sn]; exact hstate
    · rw [hR'get n]; exact hgetω
    · -- Kernel history `R'.take n = f n = (f (n+1)).take n` (prefix stability).
      rw [hR'take n]; rw [(hfstep' n).1] at hker; exact hker

/-! ### Crux B via finite branching (the route this development takes) -/

/-- **Crux B, finite-branching route (PROVEN).** Every infinite consistent concrete run `r` of the
μ-reading witness takes infinitely many `F`-fair steps, given that `PE'` is finitely branching and
finite mass-splitting. Proof (mirroring
`FairStrongProbabilisticSimulation.exists_infinite_coupled_lift`): König
(`exists_infinite_chain`) on the tree of coherent consistent `PE'`-belief-prefixes projecting onto
`r`'s prefixes, packaged as `exists_timeLocal_coherent_resolved_lift`.

* **Nodes / finite branching.** A child extends a coherent prefix by one belief-step `((l, ω), ν)`.
  The emitted `(l, ω)` ranges over `supp(PE'.next E)` — finite by `hfb`; the sampled successor
  belief `ν ∈ ω.support` — finite by `hms`. So each node has finitely many children (the concrete
  side is
  pinned by `r`, as in `exists_infinite_coupled_lift`'s `hfinChildren`).
* **Arbitrarily long chains.** Every finite prefix `r.take n` lifts to a coherent belief-prefix
  (`exists_positive_coherent_prefix`, via `beliefTCR_support`). No finiteness.
* **Assembly.** König threads a genuine infinite consistent coherent `PE'`-belief-run `R'`
  (consistency is prefix-local, so no phantom — unlike the compactness route). `R'` is infinite and
  `PE'`-consistent, so `PE'.IsFair.inf_fair` gives it infinitely many `F.dist`-fair belief-steps;
  the fairness-revealing kernel `distFairHyperKernel` carries each down to an `F`-fair concrete step
  of
  `r` (`F.dist.fair`'s realiser `p` has `F.fair s l μ` for `μ ∈ (p s).support`, and `RCoherentTL`
  places `r`'s recorded `μ` there).

No tightness, no continuity, no `[Fintype State]`, no `ImageFinite sys`; survives belief escape. -/
theorem ResolvedProbabilisticExecution.lowerFairR_phantom_free_of_finiteBranching
    {sys : System State Label} (F : Fairness sys)
    (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (hfb : PE'.FinitelyBranching) (hms : PE'.FiniteMassSplitting F) (hfair : PE'.IsFair F.dist)
    (r : ResolvedExec State Label) (hinf : ¬ r.trans.Terminates)
    (hcons : (PE'.lowerFairR F).Consistent r)
    (hinit : PE'.initState = PMF.pure (sys.distF F).init) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ F.FairStepAt r n := by
  classical
  intro N
  set pe' := PE'.average.distFToDist F with hpe'
  -- Lift `r` to an infinite `PE'`-consistent resolved belief-run `R'`, time-locally coherent with
  -- `r` (the residual crux-B gap).
  obtain ⟨R', hR'inf, hR'cons, hcoh⟩ :=
    PE'.exists_timeLocal_coherent_resolved_lift F hfb hms r hinf hcons hinit
  -- `R'` is `F.dist`-fair infinitely often (its recorded belief-steps).
  obtain ⟨m, hmN, hfairstep⟩ := hfair.inf_fair R' hR'inf hR'cons N
  refine ⟨m, hmN, ?_⟩
  -- Unpack the `F.dist`-fair belief-step at position `m`: `R'.stateAt m = some ν`,
  -- `R'.trans.get? m = some ((l, ω), ν')`, and `F.dist.fair ν l ω`.
  obtain ⟨ν, l, ω, ν', hR'state, hR'get, hνfair⟩ := hfairstep
  -- `r` has a genuine recorded step at `m` (it is infinite) with current concrete state `s`.
  have hrne : r.trans.get? m ≠ none := fun hc => hinf ⟨m, hc⟩
  obtain ⟨t, hrget'⟩ := Option.ne_none_iff_exists'.mp hrne
  obtain ⟨⟨lr, μ⟩, s'⟩ := t
  have hrget : r.trans.get? m = some ((lr, μ), s') := hrget'
  obtain ⟨s, hrstate⟩ : ∃ s, r.stateAt m = some s := by
    have hne : r.stateAt m ≠ none := by
      rcases m with _ | k
      · exact fun hc => by simp [AlterSeq.stateAt] at hc
      · intro hc
        change (r.trans.get? k).map Prod.snd = none at hc
        rw [Option.map_eq_none_iff] at hc
        exact hinf ⟨k, hc⟩
    exact Option.ne_none_iff_exists'.mp hne
  -- The time-local coherence at `m` matches `r`'s step to a belief-step of `R'` at the same label.
  obtain ⟨ν₀, ω₀, ν'₀, hR'state₀, hR'get₀, hs_supp, hμ_ker⟩ := hcoh m s lr μ s' hrstate hrget
  -- The two readings of `R'`'s state / recorded step at `m` coincide: identify `ν₀ = ν`,
  -- `lr = l`, `ω₀ = ω` and push these into the coherence data.
  obtain rfl : ν₀ = ν := by rw [hR'state₀] at hR'state; exact Option.some.inj hR'state
  have hget_eq : ((lr, ω₀), ν'₀) = ((l, ω), ν') := by
    rw [hR'get₀] at hR'get; exact Option.some.inj hR'get
  have hlr : l = lr := (congrArg (·.1.1) hget_eq).symm
  have hω₀ : ω = ω₀ := (congrArg (·.1.2) hget_eq).symm
  subst hlr hω₀
  -- The plain projection of the prefix `R'.take m` has end-belief `ν₀` (= the time-`m` belief).
  have hTe : (ResolvedExec.toExec (R'.take m)).trans.Terminates :=
    (ResolvedExec.toExec_terminates_iff (R'.take m)).mpr (take_terminates R' m)
  have hend : (ResolvedExec.toExec (R'.take m)).endState hTe = ν₀ := by
    have hst : (ResolvedExec.toExec (R'.take m)).stateAt (Nat.find hTe) = some ν₀ := by
      rw [ResolvedExec.toExec_stateAt]
      have hfind : Nat.find hTe = m := by
        have hm : Nat.find (take_terminates R' m) = m := take_find R' m hR'inf
        rw [show Nat.find hTe = Nat.find (take_terminates R' m) from
          Nat.find_congr' (fun {k} => ResolvedExec.toExec_terminatedAt_iff (R'.take m) k)]
        exact hm
      rw [hfind, take_stateAt R' (Nat.le_refl m)]; exact hR'state
    have h := AlterSeq.stateAt_find_eq_endState (ResolvedExec.toExec (R'.take m)) hTe
    rw [hst] at h; exact (Option.some.inj h).symm
  -- Fairness transfer: `F.dist.fair ν₀ l ω` at `ν₀ = end-belief`, `s ∈ ν₀.support`, `μ` in kernel.
  have hfair_dist : F.dist.fair ((ResolvedExec.toExec (R'.take m)).endState hTe) l ω := by
    rw [hend]; exact hνfair
  have hs_supp' : s ∈ ((ResolvedExec.toExec (R'.take m)).endState hTe).support := by
    rw [hend]; exact hs_supp
  have hF_fair : F.fair s l μ :=
    pe'.distFairHyperKernel_fair_transfer F (ResolvedExec.toExec (R'.take m)) hTe l ω
      hfair_dist s hs_supp' μ hμ_ker
  exact ⟨s, l, μ, s', hrstate, hrget, hF_fair⟩

/-- **The μ-reading witness is sure-fair (finite-branching route).** Combines the halt clause
(`lowerFairR_halt_fairDeadlock`) with the finite-branching phantom-freeness
(`lowerFairR_phantom_free_of_finiteBranching`). Fairness rests on `PE'.FinitelyBranching` and
`PE'.FiniteMassSplitting F` — no tightness, no `[Fintype State]`. -/
theorem ResolvedProbabilisticExecution.lowerFairR_isFair_of_finiteBranching
    {sys : System State Label} (F : Fairness sys)
    (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (hfb : PE'.FinitelyBranching) (hms : PE'.FiniteMassSplitting F) (hfair : PE'.IsFair F.dist)
    (hinit : PE'.initState = PMF.pure (sys.distF F).init) :
    (PE'.lowerFairR F).IsFair F where
  halt_fairDeadlock := fun r h hcons h_none =>
    PE'.lowerFairR_halt_fairDeadlock F hfair r h hcons h_none hinit
  inf_fair := fun r hinf hcons N =>
    PE'.lowerFairR_phantom_free_of_finiteBranching F hfb hms hfair r hinf hcons hinit N

/-! ### The transformation theorem (finite-branching route) -/

/-- **Transforming a fair `𝒟f(sys,F)`-execution into a fair `sys`-execution.** A fair resolved
`𝒟f(sys,F)`-execution `PE'` that is finitely branching and finite mass-splitting is transformed by
the μ-reading reconstruction `lowerFairR` into a fair resolved `sys`-execution with the **same trace
distribution** and the Dirac start. This is the per-execution form of the superset direction under
the branching hypotheses (no `[Fintype State]`, no tightness): exactly what lowers the scheduler
built by `FairStrongProbabilisticSimulation` on `𝒟f(sys,F)` back to `sys`.

Proven from `lowerFairR_initState` (Dirac start), `lowerFairR_isFair_of_finiteBranching` (fairness,
via crux B on the finite-branching route + the halt clause) and `lowerFairR_traceProbR` (trace,
crux A — finiteness-free). -/
theorem lower_of_finiteBranching {sys : System State Label} (F : Fairness sys)
    (PE' : ResolvedProbabilisticExecution (sys.distF F))
    (hinit : PE'.initState = PMF.pure (sys.distF F).init)
    (hfb : PE'.FinitelyBranching) (hms : PE'.FiniteMassSplitting F) (hfair : PE'.IsFair F.dist) :
    ∃ PE : ResolvedProbabilisticExecution sys,
      PE.initState = PMF.pure sys.init ∧ PE.IsFair F ∧
        ∀ τ, PE.traceProbR τ = PE'.traceProbR τ :=
  ⟨PE'.lowerFairR F, PE'.lowerFairR_initState F hinit,
    PE'.lowerFairR_isFair_of_finiteBranching F hfb hms hfair hinit,
    fun τ => PE'.lowerFairR_traceProbR F hinit τ⟩

end PLTS
