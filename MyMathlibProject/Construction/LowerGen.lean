/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Construction.DistTrace

/-!
# Kernel-parametric disintegration `lowerWith`

`Construction/DistTrace.lean` inverts the distribution-monad lift with
`ProbabilisticExecution.lower`: it reconstructs a `sys`-execution from a
`𝒟(sys)`-execution realising the same trace distribution, sampling a
`𝒟(sys)`-history from the trace-cone belief `beliefTC` and stepping through the
per-state decomposition kernel `distHyperKernel`.

That trace-cone argument is **agnostic to the decomposition kernel**: the entire
chain (`lower_kernel_g_sum`, `lower_labProb_eq_aux`, `lower_traceProb_eq`) treats
the kernel as an opaque `State → PMF (PMF State)`; the only kernel-specific fact
is the *marginal decomposition* `∑ₛ (E.endState s)·((K E l ω s).bind id) q =
(ω.bind id) q`.

This file abstracts that kernel into a parameter `K`, taking validity
(`LowerKernelValid`) and the marginal decomposition (`LowerKernelDecomp`) as
hypotheses, and re-runs the chain once to obtain

  `lowerWith_traceProb_eq : sys.traceProb (pe'.lowerWith K hvalid) τ = 𝒟(sys).traceProb pe' τ`.

`DistTrace.lean`'s `lower` is the instance `lowerWith distHyperKernel`; the fair
reconstruction of `Construction/DistFair.lean` is the instance
`lowerWith distFairHyperKernel`. All generic helpers (`beliefTC`, `labMass_*`,
`beliefTC_normalize_cancel`) are reused verbatim from `DistTrace.lean`.
-/

open Stream'

namespace PLTS

variable {State Label : Type}

/-- **Validity obligation** for a `lowerWith` decomposition kernel `K`: at an
emission `(l, ω)` in the support of `pe'.scheduler.next E` (with `E` finite),
every `μ ∈ (K E l ω s).support` for `s ∈ (E.endState hE).support` is a valid
`sys`-step post-distribution from `s`. This is exactly what `distHyperKernel_step`
proves for the canonical kernel. -/
def LowerKernelValid {sys : System State Label}
    (pe' : ProbabilisticExecution 𝒟(sys))
    (K : AlterSeq (PMF State) Label → Label → PMF (PMF State) → State → PMF (PMF State)) :
    Prop :=
  ∀ {E : AlterSeq (PMF State) Label} (hE : E.trans.Terminates)
    {l : Label} {ω : PMF (PMF State)},
    some (l, ω) ∈ (pe'.scheduler.next E).support → ∀ {s : State},
      s ∈ (E.endState hE).support → ∀ {μ : PMF State},
        μ ∈ (K E l ω s).support → sys.step s l μ

/-- **Marginal-decomposition obligation** for a `lowerWith` decomposition kernel
`K`: integrating the per-state kernel `bind id` against the end-state
distribution recovers the belief-level post-marginal `ω.bind id`. Any `hyperStep`
witness kernel satisfies this. -/
def LowerKernelDecomp {sys : System State Label}
    (pe' : ProbabilisticExecution 𝒟(sys))
    (K : AlterSeq (PMF State) Label → Label → PMF (PMF State) → State → PMF (PMF State)) :
    Prop :=
  ∀ {E : AlterSeq (PMF State) Label} (hE : E.trans.Terminates)
    {l : Label} {ω : PMF (PMF State)},
    some (l, ω) ∈ (pe'.scheduler.next E).support → ∀ q : State,
      (ω.bind id) q = ∑' s : State, (E.endState hE) s * ((K E l ω s).bind id) q

/-- The **kernel-parametric witness scheduler**. Identical in shape to
`Scheduler.lower`, with the abstract decomposition kernel `K` in place of
`distHyperKernel`; validity is discharged from `hvalid`. -/
noncomputable def Scheduler.lowerWith
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys))
    (K : AlterSeq (PMF State) Label → Label → PMF (PMF State) → State → PMF (PMF State))
    (hvalid : LowerKernelValid pe' K) :
    Scheduler sys where
  next e :=
    open Classical in
    if h_term : e.trans.Terminates then
      (pe'.beliefTC ((e.trans.toList h_term).map Prod.fst) (e.endState h_term)).bind (fun E =>
        (pe'.scheduler.next E).bind (fun opt =>
          match opt with
          | none         => PMF.pure none
          | some (l, ω)  =>
            (K E l ω (e.endState h_term)).map
              (fun μ' => some (l, μ'))))
    else
      PMF.pure none
  valid := by
    classical
    intro e n s e_term_n e_stateAt_eq l μ h_supp
    have h_term : e.trans.Terminates := ⟨n, e_term_n⟩
    have h_find_le : Nat.find h_term ≤ n := Nat.find_le e_term_n
    have h_n_le : n ≤ Nat.find h_term := by
      by_contra h_lt
      push Not at h_lt
      rcases n with _ | k
      · exact absurd h_lt (Nat.not_lt_zero _)
      · have hk_ge : Nat.find h_term ≤ k := Nat.lt_succ_iff.mp h_lt
        have h_term_k : e.trans.TerminatedAt k :=
          Stream'.Seq.terminated_stable e.trans hk_ge (Nat.find_spec h_term)
        have h_state_none : e.stateAt (k + 1) = none := by
          change (e.trans.get? k).map Prod.snd = none
          rw [show e.trans.get? k = none from h_term_k]
          rfl
        rw [h_state_none] at e_stateAt_eq
        exact Option.some_ne_none s e_stateAt_eq.symm
    have h_n_eq : n = Nat.find h_term := le_antisymm h_n_le h_find_le
    have h_s_eq : s = e.endState h_term := by
      have h := AlterSeq.stateAt_find_eq_endState e h_term
      rw [← h_n_eq] at h
      rw [h] at e_stateAt_eq
      exact (Option.some.inj e_stateAt_eq).symm
    subst h_s_eq
    change some (l, μ) ∈
      (open Classical in
        if h_term' : e.trans.Terminates then
          (pe'.beliefTC ((e.trans.toList h_term').map Prod.fst) (e.endState h_term')).bind (fun E =>
            (pe'.scheduler.next E).bind (fun opt =>
              match opt with
              | none => PMF.pure none
              | some (l', ω) =>
                (K E l' ω (e.endState h_term')).map
                  (fun μ' => some (l', μ'))))
        else PMF.pure none).support at h_supp
    rw [dif_pos h_term] at h_supp
    rw [PMF.mem_support_bind_iff] at h_supp
    obtain ⟨E, hE_belief, h_supp⟩ := h_supp
    rw [PMF.mem_support_bind_iff] at h_supp
    obtain ⟨opt, hopt_sch, h_supp⟩ := h_supp
    obtain ⟨hE_term, h_endState⟩ :=
      pe'.beliefTC_support ((e.trans.toList h_term).map Prod.fst) (e.endState h_term) hE_belief
    cases opt with
    | none =>
      change some (l, μ) ∈ (PMF.pure (α := Option (Label × PMF State)) none).support at h_supp
      rw [PMF.support_pure, Set.mem_singleton_iff] at h_supp
      exact absurd h_supp (by simp)
    | some lω =>
      obtain ⟨l', ω⟩ := lω
      change some (l, μ) ∈ ((K E l' ω (e.endState h_term)).map
        (fun μ' => some (l', μ'))).support at h_supp
      rw [PMF.mem_support_map_iff] at h_supp
      obtain ⟨μ', h_μ'_kernel, h_eq⟩ := h_supp
      simp only [Option.some.injEq, Prod.mk.injEq] at h_eq
      obtain ⟨rfl, rfl⟩ := h_eq
      exact hvalid hE_term hopt_sch h_endState h_μ'_kernel

/-- The **kernel-parametric witness execution**: initial distribution
`initState.bind id`, scheduler `Scheduler.lowerWith`. `lower` is the instance
`lowerWith distHyperKernel`. -/
noncomputable def ProbabilisticExecution.lowerWith
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys))
    (K : AlterSeq (PMF State) Label → Label → PMF (PMF State) → State → PMF (PMF State))
    (hvalid : LowerKernelValid pe' K) :
    ProbabilisticExecution sys where
  initState := pe'.initState.bind id
  scheduler := Scheduler.lowerWith pe' K hvalid

/-- **Lowered scheduler at `none`.** For a terminating `sys`-history `e`, the lowered witness halts
(`schedules `none``) exactly by sampling a trace-cone belief-history `E` and then having `pe'` halt
there: the halting mass factors through the trace-cone belief as `∑' E, beliefTC · E · next E none`.
The kernel `K` never contributes to the `none` outcome (it only produces `some (l, μ')`). -/
theorem ProbabilisticExecution.lowerWith_next_none
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys))
    (K : AlterSeq (PMF State) Label → Label → PMF (PMF State) → State → PMF (PMF State))
    (hvalid : LowerKernelValid pe' K)
    (e : AlterSeq State Label) (h_term : e.trans.Terminates) :
    (pe'.lowerWith K hvalid).scheduler.next e none
      = ∑' E : AlterSeq (PMF State) Label,
          pe'.beliefTC ((e.trans.toList h_term).map Prod.fst) (e.endState h_term) E *
            pe'.scheduler.next E none := by
  classical
  change (if h : e.trans.Terminates then
      (pe'.beliefTC ((e.trans.toList h).map Prod.fst) (e.endState h)).bind (fun E =>
        (pe'.scheduler.next E).bind (fun opt =>
          match opt with
          | none => PMF.pure none
          | some (l, ω) =>
            (K E l ω (e.endState h)).map (fun μ' => some (l, μ'))))
    else PMF.pure none) none = _
  rw [dif_pos h_term, PMF.bind_apply]
  refine tsum_congr (fun E => ?_)
  congr 1
  rw [PMF.bind_apply, tsum_eq_single none ?_]
  · -- The `none` term: the inner `match` is `PMF.pure none`, which is `1` at `none`.
    rw [PMF.pure_apply]
    simp only [if_true, mul_one]
  · -- Every `some (l, ω)` term vanishes: the `map (some ∘ ·)` is `0` at `none`.
    rintro (_ | ⟨l, ω⟩) hopt
    · exact absurd rfl hopt
    · rw [show ((PMF.map (fun μ' => some (l, μ')) (K E l ω (e.endState h_term))) none) = 0 from by
          rw [PMF.map_apply]; exact ENNReal.tsum_eq_zero.mpr (fun μ' => if_neg (by simp)),
        mul_zero]

/-- **Lowered scheduler at `some (l, ν)`.** For a terminating `sys`-history `e`, the lowered
witness schedules `some (l, ν)` by sampling a trace-cone belief-history `E`, then having `pe'`
schedule some `some (l, ω)` there, then applying the decomposition kernel `K` at `ν`. This is the
`some`-analogue of `lowerWith_next_none`; it factors the transition mass through the trace-cone
belief and the per-state kernel. -/
theorem ProbabilisticExecution.lowerWith_next_some
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys))
    (K : AlterSeq (PMF State) Label → Label → PMF (PMF State) → State → PMF (PMF State))
    (hvalid : LowerKernelValid pe' K)
    (e : AlterSeq State Label) (h_term : e.trans.Terminates) (l : Label) (ν : PMF State) :
    (pe'.lowerWith K hvalid).scheduler.next e (some (l, ν))
      = ∑' E : AlterSeq (PMF State) Label,
          pe'.beliefTC ((e.trans.toList h_term).map Prod.fst) (e.endState h_term) E *
            ∑' ω : PMF (PMF State),
              pe'.scheduler.next E (some (l, ω)) * K E l ω (e.endState h_term) ν := by
  classical
  change (if h : e.trans.Terminates then
      (pe'.beliefTC ((e.trans.toList h).map Prod.fst) (e.endState h)).bind (fun E =>
        (pe'.scheduler.next E).bind (fun opt =>
          match opt with
          | none => PMF.pure none
          | some (l, ω) =>
            (K E l ω (e.endState h)).map (fun μ' => some (l, μ'))))
    else PMF.pure none) (some (l, ν)) = _
  rw [dif_pos h_term]
  rw [PMF.bind_apply]
  refine tsum_congr (fun E => ?_)
  congr 1
  rw [PMF.bind_apply]
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun ω : Function.support (fun ω : PMF (PMF State) =>
      pe'.scheduler.next E (some (l, ω)) * K E l ω (e.endState h_term) ν) =>
      (some (l, (ω : PMF (PMF State))) : Option (Label × PMF (PMF State)))) ?hinj ?hf ?hfg
  case hinj =>
    rintro x y hxy
    exact Subtype.ext (Prod.mk.inj (Option.some.inj hxy)).2
  case hf =>
    intro opt hopt
    rw [Function.mem_support] at hopt
    rcases opt with _ | ⟨l₀, ω⟩
    · simp only [PMF.pure_apply_of_ne _ _ (by simp : (some (l, ν)) ≠ none), mul_zero,
        ne_eq, not_true_eq_false] at hopt
    · -- The map factor forces `l₀ = l`; produce the range witness.
      have hmap : (PMF.map (fun μ' => some (l₀, μ'))
          (K E l₀ ω (e.endState h_term))) (some (l, ν)) ≠ 0 := right_ne_zero_of_mul hopt
      rw [PMF.map_apply] at hmap
      have hl : l₀ = l := by
        by_contra hne
        apply hmap
        rw [ENNReal.tsum_eq_zero]
        intro a
        exact if_neg (fun ha => hne (Prod.mk.inj (Option.some.inj ha)).1.symm)
      subst hl
      -- The map factor at `(some (l₀, ν))` evaluates to `K E l₀ ω (e.endState h_term) ν`.
      have hmap_eval : (PMF.map (fun μ' => some (l₀, μ'))
          (K E l₀ ω (e.endState h_term))) (some (l₀, ν)) = K E l₀ ω (e.endState h_term) ν := by
        rw [PMF.map_apply]
        simp only [Option.some.injEq, Prod.mk.injEq, true_and, @eq_comm _ ν]
        exact tsum_ite_eq ν _
      rw [hmap_eval] at hopt
      exact ⟨⟨ω, hopt⟩, rfl⟩
  case hfg =>
    rintro ⟨ω, hω⟩
    simp only
    congr 1
    rw [PMF.map_apply]
    simp only [Option.some.injEq, Prod.mk.injEq, true_and, @eq_comm _ ν]
    exact tsum_ite_eq ν _

/-- **Lowered one-step kernel, integrated against `g`.** For a `sys`-history `e`
with label list `labs` and end-state `s`, the lowered kernel's `g`-expectation
factors through the trace-cone belief and the per-state hyper-kernel `bind id`. -/
theorem ProbabilisticExecution.lowerWith_kernel_g_sum
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys))
    (K : AlterSeq (PMF State) Label → Label → PMF (PMF State) → State → PMF (PMF State))
    (hvalid : LowerKernelValid pe' K)
    (labs : List Label) (l : Label) (g : State → ENNReal)
    (e : AlterSeq State Label) (h_term : e.trans.Terminates)
    (h_labs : (e.trans.toList h_term).map Prod.fst = labs)
    (s : State) (h_end : e.endState h_term = s) :
    (∑' s' : State, (pe'.lowerWith K hvalid).kernel e (l, s') * g s')
      = ∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
          ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
            (∑' q : State, ((K E l ω s).bind id) q * g q) := by
  classical
  have key : ∀ ν : PMF State, (pe'.lowerWith K hvalid).scheduler.next e (some (l, ν))
      = ∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
          (∑' ω : PMF (PMF State),
            pe'.scheduler.next E (some (l, ω)) * K E l ω s ν) := by
    intro ν
    rw [pe'.lowerWith_next_some K hvalid e h_term l ν, h_labs, h_end]
  -- The `bind id` push-forward abbreviation `C ν = ∑' q, ν q * g q`.
  set C : PMF State → ENNReal := fun ν => ∑' q : State, ν q * g q with hC_def
  -- Common normal form for the RHS.
  have hRHS : (∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
        ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
          (∑' q : State, ((K E l ω s).bind id) q * g q))
      = ∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
          ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
            (∑' ν : PMF State, K E l ω s ν * C ν) := by
    refine tsum_congr (fun E => ?_)
    congr 1
    refine tsum_congr (fun ω => ?_)
    congr 1
    -- `∑' q, (∑' ν, dhk ν * ν q) * g q = ∑' ν, dhk ν * C ν`.
    simp only [hC_def, PMF.bind_apply, id_eq]
    rw [show (∑' q : State, (∑' ν : PMF State, K E l ω s ν * ν q) * g q)
        = ∑' q : State, ∑' ν : PMF State, K E l ω s ν * (ν q * g q) from
      tsum_congr (fun q => by rw [← ENNReal.tsum_mul_right]; exact tsum_congr (fun ν => by ring))]
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun ν => ?_)
    rw [ENNReal.tsum_mul_left]
  -- The "push `* g s'` in, swap, pull weight out" reorganization, reused twice.
  have reorg : ∀ K : PMF State → ENNReal,
      (∑' s' : State, (∑' ν : PMF State, K ν * ν s') * g s')
        = ∑' ν : PMF State, K ν * C ν := by
    intro K
    rw [show (∑' s' : State, (∑' ν : PMF State, K ν * ν s') * g s')
        = ∑' s' : State, ∑' ν : PMF State, K ν * (ν s' * g s') from
      tsum_congr (fun s' => by rw [← ENNReal.tsum_mul_right]; exact tsum_congr (fun ν => by ring))]
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun ν => ?_)
    rw [hC_def, ENNReal.tsum_mul_left]
  rw [hRHS]
  -- Rewrite the LHS kernel and the lowered `next` via `key`, then reorganize.
  simp only [ProbabilisticExecution.kernel]
  rw [show (∑' s' : State,
        (∑' ν : PMF State, (pe'.lowerWith K hvalid).scheduler.next e (some (l, ν)) * ν s') * g s')
      = ∑' ν : PMF State,
          (pe'.lowerWith K hvalid).scheduler.next e (some (l, ν)) * C ν from reorg _]
  simp only [key]
  -- Reorganize `∑' ν, (∑' E, bel E * ∑' ω, next * dhk ν) * C ν` to the common form.
  rw [show (∑' ν : PMF State,
        (∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
          ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
            K E l ω s ν) * C ν)
      = ∑' E : AlterSeq (PMF State) Label, ∑' ν : PMF State,
          (pe'.beliefTC labs s E *
            ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
              K E l ω s ν) * C ν from by
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun ν => ?_)
    rw [← ENNReal.tsum_mul_right]]
  refine tsum_congr (fun E => ?_)
  -- Pull `beliefTC E` out of the `ν`-sum on the left.
  rw [show (∑' ν : PMF State,
        (pe'.beliefTC labs s E *
          ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
            K E l ω s ν) * C ν)
      = pe'.beliefTC labs s E * ∑' ν : PMF State,
          (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
            K E l ω s ν) * C ν from by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr (fun ν => by ring)]
  congr 1
  -- Now `∑' ν, (∑' ω, next * dhk ν) * C ν = ∑' ω, next * ∑' ν, dhk ν * C ν`.
  rw [show (∑' ν : PMF State,
        (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
          K E l ω s ν) * C ν)
      = ∑' ν : PMF State, ∑' ω : PMF (PMF State),
          pe'.scheduler.next E (some (l, ω)) * (K E l ω s ν * C ν) from
    tsum_congr (fun ν => by rw [← ENNReal.tsum_mul_right]; exact tsum_congr (fun ω => by ring))]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun ω => ?_)
  rw [ENNReal.tsum_mul_left]

open Classical in
/-- **Trace-cone invariant (`g`-indexed).** The headline identity `ρ = Ω.bind id`:
the lowered witness's `g`-integrated level mass equals `pe'`'s level mass
integrated against the `bind id` push-forward `μ ↦ ∑' s, μ s · g s`. Proven by
induction on `labs`: the base is `labMass_nil` + `initState.bind id`; the step
chains `labMass_append`, `lowerWith_kernel_g_sum`, the IH, `beliefTC_normalize_cancel`
and `hdecomp` (the `K`→ω collapse). -/
theorem ProbabilisticExecution.lowerWith_labProb_eq_aux
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys))
    (K : AlterSeq (PMF State) Label → Label → PMF (PMF State) → State → PMF (PMF State))
    (hvalid : LowerKernelValid pe' K) (hdecomp : LowerKernelDecomp pe' K)
    (labs : List Label)
    (g : State → ENNReal) :
    (pe'.lowerWith K hvalid).labMass labs g
      = pe'.labMass labs (fun μ : PMF State => ∑' s : State, μ s * g s) := by
  classical
  revert g
  induction labs using List.reverseRecOn with
  | nil =>
      intro g
      rw [(pe'.lowerWith K hvalid).labMass_nil g,
        pe'.labMass_nil (fun μ : PMF State => ∑' s, μ s * g s)]
      have hinit : (pe'.lowerWith K hvalid).initState = pe'.initState.bind id := rfl
      rw [hinit]
      simp_rw [PMF.bind_apply, id_eq]
      simp_rw [← ENNReal.tsum_mul_right]
      rw [ENNReal.tsum_comm]
      refine tsum_congr (fun a => ?_)
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr (fun s₀ => by ring)
  | append_singleton labs l ih =>
      intro g
      have hL : (pe'.lowerWith K hvalid).labMass (labs ++ [l]) g
          = (pe'.lowerWith K hvalid).labMass labs (fun s => ∑' E : AlterSeq (PMF State) Label,
              pe'.beliefTC labs s E * (∑' ω : PMF (PMF State),
                pe'.scheduler.next E (some (l, ω)) *
                  (∑' q : State, ((K E l ω s).bind id) q * g q))) := by
        rw [(pe'.lowerWith K hvalid).labMass_step labs l g]
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
          rw [pe'.lowerWith_kernel_g_sum K hvalid labs l g e' hc.1 h_labs (e'.endState hc.1) rfl]
        · rw [dif_neg hc, dif_neg hc]
      rw [hL, ih (fun s => ∑' E : AlterSeq (PMF State) Label,
            pe'.beliefTC labs s E * (∑' ω : PMF (PMF State),
              pe'.scheduler.next E (some (l, ω)) *
                (∑' q : State, ((K E l ω s).bind id) q * g q)))]
      have hR : pe'.labMass (labs ++ [l]) (fun μ : PMF State => ∑' s, μ s * g s)
          = ∑' E : AlterSeq (PMF State) Label,
              dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
                (fun h => pe'.probOf E h.1 * (∑' ω : PMF (PMF State),
                  pe'.scheduler.next E (some (l, ω)) *
                    (∑' s : State, ((ω.bind id) s) * g s))) (fun _ => 0) := by
        rw [pe'.labMass_step labs l (fun μ : PMF State => ∑' s, μ s * g s)]
        refine tsum_congr (fun E => ?_)
        by_cases hc : E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs
        · rw [dif_pos hc, dif_pos hc]; congr 1
          simp only [ProbabilisticExecution.kernel]
          simp_rw [← ENNReal.tsum_mul_right]
          rw [ENNReal.tsum_comm]
          refine tsum_congr (fun μ => ?_)
          rw [← ENNReal.tsum_mul_left]
          simp_rw [mul_assoc]
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
          congr 1
          simp_rw [PMF.bind_apply, id_eq]
          simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
          rw [ENNReal.tsum_comm]
          refine tsum_congr (fun a => ?_)
          refine tsum_congr (fun s => ?_)
          ring
        · rw [dif_neg hc, dif_neg hc]
      have hLmid : (pe'.labMass labs (fun μ : PMF State => ∑' s : State,
            μ s * (∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
              (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                (∑' q : State, ((K E l ω s).bind id) q * g q)))))
          = ∑' E : AlterSeq (PMF State) Label,
              dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
                (fun h => pe'.probOf E h.1 * (∑' ω : PMF (PMF State),
                  pe'.scheduler.next E (some (l, ω)) *
                    (∑' s : State, ((ω.bind id) s) * g s))) (fun _ => 0) := by
        -- Abbreviate the per-state inner factor `H s`.
        set Hfun : State → ENNReal := fun s =>
            ∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
              (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                (∑' q : State, ((K E l ω s).bind id) q * g q)) with hHfun
        have stepA : (pe'.labMass labs (fun μ : PMF State => ∑' s : State, μ s * Hfun s))
            = ∑' E₀ : AlterSeq (PMF State) Label, ∑' s : State,
                pe'.beliefTCw labs s E₀ * Hfun s := by
          unfold ProbabilisticExecution.labMass
          refine tsum_congr (fun E₀ => ?_)
          by_cases hc : E₀.trans.Terminates ∧ E₀.trans.map Prod.fst = Seq.ofList labs
          · rw [dif_pos hc, ← ENNReal.tsum_mul_left]
            refine tsum_congr (fun s => ?_)
            have hbw : pe'.beliefTCw labs s E₀ = pe'.probOf E₀ hc.1 * (E₀.endState hc.1) s := by
              unfold ProbabilisticExecution.beliefTCw; rw [dif_pos hc]
            rw [hbw]; ring
          · rw [dif_neg hc]
            have hz : ∀ s : State, pe'.beliefTCw labs s E₀ = 0 := by
              intro s; unfold ProbabilisticExecution.beliefTCw; rw [dif_neg hc]
            simp only [hz, zero_mul, tsum_zero]
        rw [stepA, ENNReal.tsum_comm]
        simp_rw [ENNReal.tsum_mul_right]
        simp only [hHfun]
        -- Apply the normalizer cancellation per state `b`.
        have stepB : ∀ b : State,
            (∑' i : AlterSeq (PMF State) Label, pe'.beliefTCw labs b i) *
              (∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs b E *
                (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                  (∑' q : State, ((K E l ω b).bind id) q * g q)))
            = ∑' E : AlterSeq (PMF State) Label, pe'.beliefTCw labs b E *
                (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                  (∑' q : State, ((K E l ω b).bind id) q * g q)) := by
          intro b
          exact pe'.beliefTC_normalize_cancel labs b
            (fun E => ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
              (∑' q : State, ((K E l ω b).bind id) q * g q))
        simp_rw [stepB]
        rw [ENNReal.tsum_comm]
        -- The marginal collapse: per terminating `E`, integrating the per-state
        -- hyper-kernel against the end-state distribution recovers `ω.bind id`.
        have decomp_g : ∀ (E : AlterSeq (PMF State) Label) (hE : E.trans.Terminates),
            (∑' s : State, (E.endState hE) s *
              (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                (∑' q : State, ((K E l ω s).bind id) q * g q)))
            = ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                (∑' s : State, ((ω.bind id) s) * g s) := by
          intro E hE
          -- Push `(E.endState hE) s` into the ω-sum, swap `s ↔ ω`, pull `next` out.
          have hpush : ∀ s : State, (E.endState hE) s *
              (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                (∑' q : State, ((K E l ω s).bind id) q * g q))
              = ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                  ((E.endState hE) s * (∑' q : State,
                    ((K E l ω s).bind id) q * g q)) := by
            intro s
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr (fun ω => ?_)
            ring
          rw [tsum_congr hpush, ENNReal.tsum_comm]
          refine tsum_congr (fun ω => ?_)
          rw [ENNReal.tsum_mul_left]
          by_cases hω : pe'.scheduler.next E (some (l, ω)) = 0
          · simp [hω]
          · congr 1
            have h_supp : some (l, ω) ∈ (pe'.scheduler.next E).support :=
              (PMF.mem_support_iff _ _).mpr hω
            symm
            simp_rw [hdecomp hE h_supp]
            simp_rw [← ENNReal.tsum_mul_right]
            rw [ENNReal.tsum_comm]
            refine tsum_congr (fun s => ?_)
            rw [← ENNReal.tsum_mul_left]
            exact tsum_congr (fun s' => by ring)
        refine tsum_congr (fun E => ?_)
        by_cases hc : E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs
        · rw [dif_pos hc]
          have hbw : ∀ s : State,
              pe'.beliefTCw labs s E = pe'.probOf E hc.1 * (E.endState hc.1) s := by
            intro s; unfold ProbabilisticExecution.beliefTCw; rw [dif_pos hc]
          simp_rw [hbw]
          rw [← decomp_g E hc.1]
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr (fun s => ?_)
          ring
        · have hz : ∀ s : State, pe'.beliefTCw labs s E = 0 := by
            intro s; unfold ProbabilisticExecution.beliefTCw; rw [dif_neg hc]
          rw [dif_neg hc]
          simp only [hz, zero_mul, tsum_zero]
      rw [hLmid, hR]

open Classical in
/-- **Trace-cone invariant (`g = 1` slice).** For each label list `labs`, the
`lower`-witness assigns the same total `probOf`-mass to `sys`-executions with
label list `labs` as `pe'` assigns to `𝒟(sys)`-histories with label list `labs`.
The `g = 1` instance of `lower_labProb_eq_aux`. -/
theorem ProbabilisticExecution.lowerWith_labProb_eq
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys))
    (K : AlterSeq (PMF State) Label → Label → PMF (PMF State) → State → PMF (PMF State))
    (hvalid : LowerKernelValid pe' K) (hdecomp : LowerKernelDecomp pe' K)
    (labs : List Label) :
    (∑' e : AlterSeq State Label,
        dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs)
          (fun h => (pe'.lowerWith K hvalid).probOf e h.1) (fun _ => 0))
    = ∑' E : AlterSeq (PMF State) Label,
        dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
          (fun h => pe'.probOf E h.1) (fun _ => 0) := by
  classical
  have h := pe'.lowerWith_labProb_eq_aux K hvalid hdecomp labs (fun _ => 1)
  simpa only [ProbabilisticExecution.labMass, mul_one, PMF.tsum_coe] using h

/-- **Trace preservation for the witness.** For each trace `τ`,
`sys.traceProb (pe'.lowerWith K hvalid) τ = 𝒟(sys).traceProb pe' τ`. Regroup both `traceProb`s by
label list (`traceProb_eq_labProb_sum`); since `sys` and `𝒟(sys)` share `internal`,
the label-list condition coincides, and per label list the two masses agree by the
trace-cone invariant `lower_labProb_eq`. -/
theorem ProbabilisticExecution.lowerWith_traceProb_eq
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys))
    (K : AlterSeq (PMF State) Label → Label → PMF (PMF State) → State → PMF (PMF State))
    (hvalid : LowerKernelValid pe' K) (hdecomp : LowerKernelDecomp pe' K)
    (τ : Seq Label) :
    sys.traceProb (pe'.lowerWith K hvalid) τ = 𝒟(sys).traceProb pe' τ := by
  classical
  rw [System.traceProb_eq_labProb_sum sys (pe'.lowerWith K hvalid) τ,
      System.traceProb_eq_labProb_sum 𝒟(sys) pe' τ]
  refine tsum_congr fun labs => ?_
  by_cases h : sys.traceTightLabs τ labs
  · have h' : (𝒟(sys)).traceTightLabs τ labs := h
    rw [if_pos h, if_pos h', pe'.lowerWith_labProb_eq K hvalid hdecomp labs]
  · have h' : ¬ (𝒟(sys)).traceTightLabs τ labs := h
    rw [if_neg h, if_neg h']

end PLTS
