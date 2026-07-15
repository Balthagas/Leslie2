/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.DistMonad.DistTraceBelief

/-!
# The distribution-monad lift preserves achievable trace distributions

Final stage: the level-mass append/step recursion (`labMass_append`, `labMass_step`), the
belief-normalisation cancellation, and the resulting trace-probability equality
`ProbabilisticExecution.lower_traceProb_eq`, giving the headline `dist_traceProb_eq`
(`𝒟(sys)` preserves achievable trace distributions). The disintegration kernel and belief/lower
witness construction it builds on live in `DistTraceKernel.lean` and `DistTraceBelief.lean`.
-/

open Stream'

namespace PLTS

variable {α β State State_C State_A Label : Type}

open Classical in
/-- **Append-singleton step of the level-mass recursion** (the `g`-weighted,
generic-system generalisation of `tsum_probOf_labels_append`). Reindex by the
bijection `e = ⟨e'.init, e'.trans.append (cons (l,s') nil)⟩`, using
`endState_append_singleton` (`e.endState = s'`) and `probOf_append_singleton`. -/
theorem ProbabilisticExecution.labMass_append {S : Type} {Sys : System S Label}
    (pe : ProbabilisticExecution Sys) (labs : List Label) (l : Label) (g : S → ENNReal) :
    pe.labMass (labs ++ [l]) g
      = ∑' (e' : AlterSeq S Label) (s' : S),
          dite (e'.trans.Terminates ∧ e'.trans.map Prod.fst = Seq.ofList labs)
            (fun h => pe.probOf e' h.1 * pe.kernel e' (l, s') * g s') (fun _ => 0) := by
  classical
  unfold ProbabilisticExecution.labMass
  rw [← ENNReal.tsum_prod' (f := fun p : AlterSeq S Label × S =>
      dite (p.1.trans.Terminates ∧ Seq.map Prod.fst p.1.trans = (↑labs : Seq Label))
        (fun h => pe.probOf p.1 h.1 * pe.kernel p.1 (l, p.2) * g p.2) (fun _ => 0))]
  -- Abbreviate the two summands.
  set f : AlterSeq S Label → ENNReal := fun e =>
      dite (e.trans.Terminates ∧ Seq.map Prod.fst e.trans = (↑(labs ++ [l]) : Seq Label))
        (fun h => pe.probOf e h.1 * g (e.endState h.1)) (fun _ => 0) with hf_def
  set gg : AlterSeq S Label × S → ENNReal := fun p =>
      dite (p.1.trans.Terminates ∧ Seq.map Prod.fst p.1.trans = (↑labs : Seq Label))
        (fun h => pe.probOf p.1 h.1 * pe.kernel p.1 (l, p.2) * g p.2) (fun _ => 0) with hgg_def
  -- Helper: membership in `support gg` forces the then-branch condition.
  have g_supp_cond : ∀ p : AlterSeq S Label × S, gg p ≠ 0 →
      p.1.trans.Terminates ∧ Seq.map Prod.fst p.1.trans = (↑labs : Seq Label) := by
    intro p hp
    by_contra hcond
    rw [hgg_def] at hp
    simp only at hp
    rw [dif_neg hcond] at hp
    exact hp rfl
  -- Helper: membership in `support f` forces the then-branch condition.
  have f_supp_cond : ∀ e : AlterSeq S Label, f e ≠ 0 →
      e.trans.Terminates ∧ Seq.map Prod.fst e.trans = (↑(labs ++ [l]) : Seq Label) := by
    intro e he
    by_contra hcond
    rw [hf_def] at he
    simp only at he
    rw [dif_neg hcond] at he
    exact he rfl
  -- The forward bijection `(e', s') ↦ ⟨e'.init, e'.trans.append (cons (l,s') nil)⟩`.
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun x => (⟨(x.1).1.init,
        (x.1).1.trans.append (Seq.cons (l, (x.1).2) Seq.nil)⟩ : AlterSeq S Label))
    ?hinj ?hf ?hfg
  case hinj =>
    rintro x y hxy
    have hx := g_supp_cond x.1 x.2
    have hy := g_supp_cond y.1 y.2
    have h_trans := congrArg AlterSeq.trans hxy
    have h_init := congrArg AlterSeq.init hxy
    simp only at h_trans h_init
    have h_last := Stream'.Seq.append_singleton_inj_right
      (x.1).1.trans (y.1).1.trans hx.1 hy.1 _ _ h_trans
    have hs' : (x.1).2 = (y.1).2 := (Prod.mk.inj h_last).2
    have h_prev := Stream'.Seq.append_singleton_inj_left
      (x.1).1.trans (y.1).1.trans hx.1 hy.1 _ _ h_trans
    refine Subtype.ext (Prod.ext ?_ hs')
    exact congrArg₂ AlterSeq.mk h_init h_prev
  case hf =>
    intro e he_mem
    have he := f_supp_cond e (Function.mem_support.mp he_mem)
    -- `e.trans` is nonempty.
    have h_ne : e.trans.toList he.1 ≠ [] := by
      intro hnil
      have h_map_nil : e.trans.map Prod.fst = Stream'.Seq.nil := by
        have : e.trans = Stream'.Seq.nil := by
          rw [← Stream'.Seq.ofList_toList e.trans he.1, hnil, Stream'.Seq.ofList_nil]
        rw [this, Stream'.Seq.map_nil]
      rw [he.2] at h_map_nil
      have h_len := congrArg Stream'.Seq.length' h_map_nil
      rw [Stream'.Seq.length'_nil,
        Stream'.Seq.length'_of_terminates (Stream'.Seq.terminates_ofList _),
        ← Stream'.Seq.length_toList _ (Stream'.Seq.terminates_ofList _),
        Stream'.Seq.toList_ofList] at h_len
      simp only [List.length_append, List.length_singleton, Nat.cast_eq_zero] at h_len
      omega
    -- Split `e.trans = prev.append (cons last nil)`.
    obtain ⟨prev, last, h_prev_term, h_split, _, _⟩ :=
      Stream'.Seq.exists_split_last e.trans he.1 h_ne
    have h_trans_map := he.2
    rw [h_split, Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil] at h_trans_map
    rw [show (↑(labs ++ [l]) : Seq Label)
        = (↑labs : Seq Label).append (Seq.cons l Seq.nil) by
        rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]]
      at h_trans_map
    have h_prev_map_term : (prev.map Prod.fst).Terminates :=
      Stream'.Seq.terminates_map_iff.mpr h_prev_term
    have h_prev_map : prev.map Prod.fst = (↑labs : Seq Label) :=
      Stream'.Seq.append_singleton_inj_left _ _ h_prev_map_term
        (Stream'.Seq.terminates_ofList _) _ _ h_trans_map
    have h_last : last.1 = l :=
      Stream'.Seq.append_singleton_inj_right _ _ h_prev_map_term
        (Stream'.Seq.terminates_ofList _) _ _ h_trans_map
    -- The reassembled history equals `e`.
    have h_app_term : (prev.append (Seq.cons (l, last.2) Seq.nil)).Terminates := by
      rw [show (Seq.cons (l, last.2) Seq.nil) = Seq.cons last Seq.nil by
        rw [← h_last]]
      exact h_split ▸ he.1
    have h_reassemble : (⟨e.init, prev.append (Seq.cons (l, last.2) Seq.nil)⟩
        : AlterSeq S Label) = e := by
      refine congrArg₂ AlterSeq.mk rfl ?_
      rw [show (Seq.cons (l, last.2) Seq.nil) = Seq.cons last Seq.nil by rw [← h_last]]
      exact h_split.symm
    -- The preimage `(⟨e.init, prev⟩, last.2)` lies in `support gg`.
    have hg_pos : gg (⟨e.init, prev⟩, last.2) ≠ 0 := by
      rw [hgg_def]; simp only
      rw [dif_pos ⟨h_prev_term, h_prev_map⟩]
      have h_factor := ProbabilisticExecution.probOf_append_singleton pe
        e.init prev h_prev_term (l, last.2) h_app_term
      have h_probOf_e : pe.probOf e he.1 ≠ 0 := by
        have h_mem := Function.mem_support.mp he_mem
        change f e ≠ 0 at h_mem
        rw [hf_def] at h_mem; simp only at h_mem
        rw [dif_pos he] at h_mem
        exact fun hz => h_mem (by rw [hz, zero_mul])
      -- end-state of the reassembled history is `last.2`.
      have h_end_app : (⟨e.init, prev.append (Seq.cons (l, last.2) Seq.nil)⟩
          : AlterSeq S Label).endState h_app_term = last.2 := by
        have key := AlterSeq.endState_append_singleton
          (⟨e.init, prev⟩ : AlterSeq S Label) h_prev_term l last.2
        -- Both `endState` calls agree by proof irrelevance of the `Terminates` arg.
        exact key
      have h_g_e : g (e.endState he.1) = g last.2 := by
        have key : ∀ (A : AlterSeq S Label) (hA : A.trans.Terminates),
            A = (⟨e.init, prev.append (Seq.cons (l, last.2) Seq.nil)⟩ : AlterSeq S Label) →
            g (A.endState hA)
              = g ((⟨e.init, prev.append (Seq.cons (l, last.2) Seq.nil)⟩
                  : AlterSeq S Label).endState h_app_term) := by
          rintro A hA rfl; rfl
        rw [key e he.1 h_reassemble.symm, h_end_app]
      intro hzero
      apply h_probOf_e
      -- `pe.probOf e * g (e.endState) = (factored) * g last.2 = 0`.
      have key : ∀ (A : AlterSeq S Label) (hA : A.trans.Terminates),
          A = e → pe.probOf A hA = pe.probOf e he.1 := by
        rintro A hA rfl; rfl
      have h_eq : pe.probOf e he.1 * g (e.endState he.1)
          = (pe.probOf ⟨e.init, prev⟩ h_prev_term * pe.kernel ⟨e.init, prev⟩ (l, last.2))
            * g last.2 := by
        rw [h_g_e, ← key _ h_app_term h_reassemble, h_factor]
      have h_prod_zero : pe.probOf e he.1 * g (e.endState he.1) = 0 := by
        rw [h_eq, hzero]
      -- `g (e.endState) ≠ 0` since the `gg`-value is nonzero only if `g last.2 ≠ 0`...
      -- Actually we use that the f-membership product is nonzero.
      have h_f_ne : pe.probOf e he.1 * g (e.endState he.1) ≠ 0 := by
        have h_mem := Function.mem_support.mp he_mem
        change f e ≠ 0 at h_mem
        rw [hf_def] at h_mem; simp only at h_mem
        rwa [dif_pos he] at h_mem
      exact absurd h_prod_zero h_f_ne
    refine ⟨⟨(⟨e.init, prev⟩, last.2), hg_pos⟩, ?_⟩
    simp only
    exact h_reassemble
  case hfg =>
    rintro x
    set e' := (x.1).1 with he'_def
    set s' := (x.1).2 with hs'_def
    have hx := g_supp_cond x.1 x.2
    -- The RHS `gg ↑x` is in its then-branch.
    have h_gg : gg x.1 = pe.probOf e' hx.1 * pe.kernel e' (l, s') * g s' := by
      rw [hgg_def]; simp only; rw [dif_pos hx]
    -- Termination of the appended trans.
    have h_app_term : (e'.trans.append (Seq.cons (l, s') Seq.nil)).Terminates :=
      ⟨_, Stream'.Seq.terminatedAt_append_find hx.1
        (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil).choose_spec⟩
    -- The map of the appended trans is `↑(labs ++ [l])`.
    have h_map : Seq.map Prod.fst (e'.trans.append (Seq.cons (l, s') Seq.nil))
        = (↑(labs ++ [l]) : Seq Label) := by
      rw [Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil, hx.2,
        Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    -- The LHS `f (i x)` is in its then-branch.
    have h_f : f (⟨e'.init, e'.trans.append (Seq.cons (l, s') Seq.nil)⟩
        : AlterSeq S Label)
        = pe.probOf ⟨e'.init, e'.trans.append (Seq.cons (l, s') Seq.nil)⟩ h_app_term
          * g ((⟨e'.init, e'.trans.append (Seq.cons (l, s') Seq.nil)⟩
              : AlterSeq S Label).endState h_app_term) := by
      rw [hf_def]; simp only; rw [dif_pos ⟨h_app_term, h_map⟩]
    -- end-state of the appended history is `s'`.
    have h_end : (⟨e'.init, e'.trans.append (Seq.cons (l, s') Seq.nil)⟩
        : AlterSeq S Label).endState h_app_term = s' := by
      have key := AlterSeq.endState_append_singleton
        (⟨e'.init, e'.trans⟩ : AlterSeq S Label) hx.1 l s'
      -- `⟨e'.init, e'.trans⟩ = e'` definitionally; proof irrelevance on the `Terminates`
      -- argument makes the two `endState` calls equal.
      exact key
    change f (⟨e'.init, e'.trans.append (Seq.cons (l, s') Seq.nil)⟩
        : AlterSeq S Label) = gg x.1
    rw [h_f, h_gg, h_end]
    -- Factor via `probOf_append_singleton`.
    rw [ProbabilisticExecution.probOf_append_singleton pe e'.init e'.trans hx.1 (l, s')
      h_app_term]

open Classical in
/-- **Level-mass recursion**, kernel form: factor the appended-step sum so the
one-step kernel's `g`-expectation sits inside the level-`labs` `dite`. The form
used by both sides of the trace-cone induction. -/
theorem ProbabilisticExecution.labMass_step {S : Type} {Sys : System S Label}
    (pe : ProbabilisticExecution Sys) (labs : List Label) (l : Label) (g : S → ENNReal) :
    pe.labMass (labs ++ [l]) g
      = ∑' e' : AlterSeq S Label,
          dite (e'.trans.Terminates ∧ e'.trans.map Prod.fst = Seq.ofList labs)
            (fun h => pe.probOf e' h.1 * ∑' s' : S, pe.kernel e' (l, s') * g s')
            (fun _ => 0) := by
  classical
  rw [pe.labMass_append labs l g]
  refine tsum_congr (fun e' => ?_)
  by_cases hc : e'.trans.Terminates ∧ e'.trans.map Prod.fst = Seq.ofList labs
  · rw [dif_pos hc, ← ENNReal.tsum_mul_left]
    refine tsum_congr (fun s' => ?_)
    rw [dif_pos hc]; ring
  · rw [dif_neg hc]
    simp only [dif_neg hc, tsum_zero]

open Classical in
/-- **Lowered one-step kernel, integrated against `g`.** For a `sys`-history `e`
with label list `labs` and end-state `s`, the lowered kernel's `g`-expectation
factors through the trace-cone belief and the per-state hyper-kernel `bind id`. -/
theorem ProbabilisticExecution.lower_kernel_g_sum
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys))
    (labs : List Label) (l : Label) (g : State → ENNReal)
    (e : AlterSeq State Label) (h_term : e.trans.Terminates)
    (h_labs : (e.trans.toList h_term).map Prod.fst = labs)
    (s : State) (h_end : e.endState h_term = s) :
    (∑' s' : State, pe'.lower.kernel e (l, s') * g s')
      = ∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
          ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
            (∑' q : State, ((pe'.distHyperKernel E l ω s).bind id) q * g q) := by
  classical
  have key : ∀ ν : PMF State, pe'.lower.scheduler.next e (some (l, ν))
      = ∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
          (∑' ω : PMF (PMF State),
            pe'.scheduler.next E (some (l, ω)) * pe'.distHyperKernel E l ω s ν) := by
    intro ν
    change (if h : e.trans.Terminates then
        (pe'.beliefTC ((e.trans.toList h).map Prod.fst) (e.endState h)).bind (fun E =>
          (pe'.scheduler.next E).bind (fun opt =>
            match opt with
            | none => PMF.pure none
            | some (l, ω) =>
              (pe'.distHyperKernel E l ω (e.endState h)).map (fun μ' => some (l, μ'))))
      else PMF.pure none) (some (l, ν)) = _
    rw [dif_pos h_term, h_labs, h_end]
    rw [PMF.bind_apply]
    refine tsum_congr (fun E => ?_)
    congr 1
    rw [PMF.bind_apply]
    refine tsum_eq_tsum_of_ne_zero_bij
      (i := fun ω : Function.support (fun ω : PMF (PMF State) =>
        pe'.scheduler.next E (some (l, ω)) * pe'.distHyperKernel E l ω s ν) =>
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
            (pe'.distHyperKernel E l₀ ω s)) (some (l, ν)) ≠ 0 := right_ne_zero_of_mul hopt
        rw [PMF.map_apply] at hmap
        have hl : l₀ = l := by
          by_contra hne
          apply hmap
          rw [ENNReal.tsum_eq_zero]
          intro a
          exact if_neg (fun ha => hne (Prod.mk.inj (Option.some.inj ha)).1.symm)
        subst hl
        -- The map factor at `(some (l₀, ν))` evaluates to `dhk E l₀ ω s ν`.
        have hmap_eval : (PMF.map (fun μ' => some (l₀, μ'))
            (pe'.distHyperKernel E l₀ ω s)) (some (l₀, ν)) = pe'.distHyperKernel E l₀ ω s ν := by
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
  -- The `bind id` push-forward abbreviation `C ν = ∑' q, ν q * g q`.
  set C : PMF State → ENNReal := fun ν => ∑' q : State, ν q * g q with hC_def
  -- Common normal form for the RHS.
  have hRHS : (∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
        ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
          (∑' q : State, ((pe'.distHyperKernel E l ω s).bind id) q * g q))
      = ∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
          ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
            (∑' ν : PMF State, pe'.distHyperKernel E l ω s ν * C ν) := by
    refine tsum_congr (fun E => ?_)
    congr 1
    refine tsum_congr (fun ω => ?_)
    congr 1
    -- `∑' q, (∑' ν, dhk ν * ν q) * g q = ∑' ν, dhk ν * C ν`.
    simp only [hC_def, PMF.bind_apply, id_eq]
    rw [show (∑' q : State, (∑' ν : PMF State, pe'.distHyperKernel E l ω s ν * ν q) * g q)
        = ∑' q : State, ∑' ν : PMF State, pe'.distHyperKernel E l ω s ν * (ν q * g q) from
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
        (∑' ν : PMF State, pe'.lower.scheduler.next e (some (l, ν)) * ν s') * g s')
      = ∑' ν : PMF State, pe'.lower.scheduler.next e (some (l, ν)) * C ν from reorg _]
  simp only [key]
  -- Reorganize `∑' ν, (∑' E, bel E * ∑' ω, next * dhk ν) * C ν` to the common form.
  rw [show (∑' ν : PMF State,
        (∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
          ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
            pe'.distHyperKernel E l ω s ν) * C ν)
      = ∑' E : AlterSeq (PMF State) Label, ∑' ν : PMF State,
          (pe'.beliefTC labs s E *
            ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
              pe'.distHyperKernel E l ω s ν) * C ν from by
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun ν => ?_)
    rw [← ENNReal.tsum_mul_right]]
  refine tsum_congr (fun E => ?_)
  -- Pull `beliefTC E` out of the `ν`-sum on the left.
  rw [show (∑' ν : PMF State,
        (pe'.beliefTC labs s E *
          ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
            pe'.distHyperKernel E l ω s ν) * C ν)
      = pe'.beliefTC labs s E * ∑' ν : PMF State,
          (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
            pe'.distHyperKernel E l ω s ν) * C ν from by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr (fun ν => by ring)]
  congr 1
  -- Now `∑' ν, (∑' ω, next * dhk ν) * C ν = ∑' ω, next * ∑' ν, dhk ν * C ν`.
  rw [show (∑' ν : PMF State,
        (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
          pe'.distHyperKernel E l ω s ν) * C ν)
      = ∑' ν : PMF State, ∑' ω : PMF (PMF State),
          pe'.scheduler.next E (some (l, ω)) * (pe'.distHyperKernel E l ω s ν * C ν) from
    tsum_congr (fun ν => by rw [← ENNReal.tsum_mul_right]; exact tsum_congr (fun ω => by ring))]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun ω => ?_)
  rw [ENNReal.tsum_mul_left]

/-- **Trace-cone belief normaliser cancellation.** Multiplying the (possibly
unnormalised) `beliefTC`-expectation by the normaliser recovers the unnormalised
`beliefTCw`-weighted sum; covers the `Z = 0` fallback too. -/
theorem ProbabilisticExecution.beliefTC_normalize_cancel
    {sys : System State Label}
    (pe' : ProbabilisticExecution 𝒟(sys))
    (labs : List Label) (s : State) (w : AlterSeq (PMF State) Label → ENNReal) :
    (∑' E, pe'.beliefTCw labs s E) * (∑' E, pe'.beliefTC labs s E * w E)
      = ∑' E, pe'.beliefTCw labs s E * w E := by
  classical
  by_cases hZ : (∑' E, pe'.beliefTCw labs s E) = 0
  · rw [hZ, zero_mul]
    have hz : ∀ E, pe'.beliefTCw labs s E = 0 := ENNReal.tsum_eq_zero.mp hZ
    exact (ENNReal.tsum_eq_zero.mpr (fun E => by rw [hz E, zero_mul])).symm
  · have hZtop : (∑' E, pe'.beliefTCw labs s E) ≠ ⊤ := pe'.beliefTCw_tsum_ne_top labs s
    have hbel : ∀ E, pe'.beliefTC labs s E
        = pe'.beliefTCw labs s E * (∑' E', pe'.beliefTCw labs s E')⁻¹ := by
      intro E
      unfold ProbabilisticExecution.beliefTC
      rw [dif_pos hZ, PMF.normalize_apply]
    rw [show (∑' E, pe'.beliefTC labs s E * w E)
          = ∑' E, (pe'.beliefTCw labs s E * (∑' E', pe'.beliefTCw labs s E')⁻¹) * w E from
        tsum_congr (fun E => by rw [hbel E]),
      ← ENNReal.tsum_mul_left]
    refine tsum_congr (fun E => ?_)
    rw [show (∑' E', pe'.beliefTCw labs s E') *
          (pe'.beliefTCw labs s E * (∑' E', pe'.beliefTCw labs s E')⁻¹ * w E)
          = ((∑' E', pe'.beliefTCw labs s E') * (∑' E', pe'.beliefTCw labs s E')⁻¹) *
            (pe'.beliefTCw labs s E * w E) by ring,
      ENNReal.mul_inv_cancel hZ hZtop, one_mul]

open Classical in
/-- **Trace-cone invariant (`g`-indexed).** The headline identity `ρ = Ω.bind id`:
the lowered witness's `g`-integrated level mass equals `pe'`'s level mass
integrated against the `bind id` push-forward `μ ↦ ∑' s, μ s · g s`. Proven by
induction on `labs`: the base is `labMass_nil` + `initState.bind id`; the step
chains `labMass_append`, `lower_kernel_g_sum`, the IH, `beliefTC_normalize_cancel`
and `hyperStep_marginal_decomp` (the dhk→ω collapse). -/
theorem ProbabilisticExecution.lower_labProb_eq_aux
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys)) (labs : List Label)
    (g : State → ENNReal) :
    pe'.lower.labMass labs g
      = pe'.labMass labs (fun μ : PMF State => ∑' s : State, μ s * g s) := by
  classical
  revert g
  induction labs using List.reverseRecOn with
  | nil =>
      intro g
      rw [pe'.lower.labMass_nil g, pe'.labMass_nil (fun μ : PMF State => ∑' s, μ s * g s)]
      have hinit : pe'.lower.initState = pe'.initState.bind id := rfl
      rw [hinit]
      simp_rw [PMF.bind_apply, id_eq]
      simp_rw [← ENNReal.tsum_mul_right]
      rw [ENNReal.tsum_comm]
      refine tsum_congr (fun a => ?_)
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr (fun s₀ => by ring)
  | append_singleton labs l ih =>
      intro g
      have hL : pe'.lower.labMass (labs ++ [l]) g
          = pe'.lower.labMass labs (fun s => ∑' E : AlterSeq (PMF State) Label,
              pe'.beliefTC labs s E * (∑' ω : PMF (PMF State),
                pe'.scheduler.next E (some (l, ω)) *
                  (∑' q : State, ((pe'.distHyperKernel E l ω s).bind id) q * g q))) := by
        rw [pe'.lower.labMass_step labs l g]
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
          rw [pe'.lower_kernel_g_sum labs l g e' hc.1 h_labs (e'.endState hc.1) rfl]
        · rw [dif_neg hc, dif_neg hc]
      rw [hL, ih (fun s => ∑' E : AlterSeq (PMF State) Label,
            pe'.beliefTC labs s E * (∑' ω : PMF (PMF State),
              pe'.scheduler.next E (some (l, ω)) *
                (∑' q : State, ((pe'.distHyperKernel E l ω s).bind id) q * g q)))]
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
                (∑' q : State, ((pe'.distHyperKernel E l ω s).bind id) q * g q)))))
          = ∑' E : AlterSeq (PMF State) Label,
              dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
                (fun h => pe'.probOf E h.1 * (∑' ω : PMF (PMF State),
                  pe'.scheduler.next E (some (l, ω)) *
                    (∑' s : State, ((ω.bind id) s) * g s))) (fun _ => 0) := by
        -- Abbreviate the per-state inner factor `H s`.
        set Hfun : State → ENNReal := fun s =>
            ∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
              (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                (∑' q : State, ((pe'.distHyperKernel E l ω s).bind id) q * g q)) with hHfun
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
                  (∑' q : State, ((pe'.distHyperKernel E l ω b).bind id) q * g q)))
            = ∑' E : AlterSeq (PMF State) Label, pe'.beliefTCw labs b E *
                (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                  (∑' q : State, ((pe'.distHyperKernel E l ω b).bind id) q * g q)) := by
          intro b
          exact pe'.beliefTC_normalize_cancel labs b
            (fun E => ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
              (∑' q : State, ((pe'.distHyperKernel E l ω b).bind id) q * g q))
        simp_rw [stepB]
        rw [ENNReal.tsum_comm]
        -- The marginal collapse: per terminating `E`, integrating the per-state
        -- hyper-kernel against the end-state distribution recovers `ω.bind id`.
        have decomp_g : ∀ (E : AlterSeq (PMF State) Label) (hE : E.trans.Terminates),
            (∑' s : State, (E.endState hE) s *
              (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                (∑' q : State, ((pe'.distHyperKernel E l ω s).bind id) q * g q)))
            = ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                (∑' s : State, ((ω.bind id) s) * g s) := by
          intro E hE
          -- Push `(E.endState hE) s` into the ω-sum, swap `s ↔ ω`, pull `next` out.
          have hpush : ∀ s : State, (E.endState hE) s *
              (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                (∑' q : State, ((pe'.distHyperKernel E l ω s).bind id) q * g q))
              = ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                  ((E.endState hE) s * (∑' q : State,
                    ((pe'.distHyperKernel E l ω s).bind id) q * g q)) := by
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
            simp_rw [hyperStep_marginal_decomp pe' hE h_supp]
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
theorem ProbabilisticExecution.lower_labProb_eq
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys)) (labs : List Label) :
    (∑' e : AlterSeq State Label,
        dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs)
          (fun h => pe'.lower.probOf e h.1) (fun _ => 0))
    = ∑' E : AlterSeq (PMF State) Label,
        dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
          (fun h => pe'.probOf E h.1) (fun _ => 0) := by
  classical
  have h := pe'.lower_labProb_eq_aux labs (fun _ => 1)
  simpa only [ProbabilisticExecution.labMass, mul_one, PMF.tsum_coe] using h

/-- **Trace preservation for the witness.** For each trace `τ`,
`sys.traceProb pe'.lower τ = 𝒟(sys).traceProb pe' τ`. Regroup both `traceProb`s by
label list (`traceProb_eq_labProb_sum`); since `sys` and `𝒟(sys)` share `internal`,
the label-list condition coincides, and per label list the two masses agree by the
trace-cone invariant `lower_labProb_eq`. -/
theorem ProbabilisticExecution.lower_traceProb_eq
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys)) (τ : Seq Label) :
    sys.traceProb pe'.lower τ = 𝒟(sys).traceProb pe' τ := by
  classical
  rw [System.traceProb_eq_labProb_sum sys pe'.lower τ,
      System.traceProb_eq_labProb_sum 𝒟(sys) pe' τ]
  refine tsum_congr fun labs => ?_
  by_cases h : sys.traceTightLabs τ labs
  · have h' : (𝒟(sys)).traceTightLabs τ labs := h
    rw [if_pos h, if_pos h', pe'.lower_labProb_eq labs]
  · have h' : ¬ (𝒟(sys)).traceTightLabs τ labs := h
    rw [if_neg h, if_neg h']

/-- **Superset direction.** Every achievable trace distribution of `𝒟(sys)` is
achievable by `sys`, witnessed by `pe'.lower` (the trace-cone construction). -/
theorem dist_traceProb_superset [Silent Label] (sys : System State Label) :
    achievableTraceDists 𝒟(sys) ⊆ achievableTraceDists sys := by
  rintro D ⟨pe', h_init, h_pe'⟩
  refine ⟨pe'.lower, ?_, fun τ => ?_⟩
  · have hD : (𝒟(sys)).init = PMF.pure sys.init := rfl
    change pe'.lower.initState = PMF.pure sys.init
    rw [show pe'.lower.initState = pe'.initState.bind id from rfl, h_init, hD,
      PMF.pure_bind, id_eq]
  · rw [pe'.lower_traceProb_eq τ, h_pe' τ]

/-- **Distribution-monad construction preserves trace distributions.** -/
theorem dist_traceProb_eq [Silent Label] (sys : System State Label) :
    achievableTraceDists sys = achievableTraceDists 𝒟(sys) :=
  Set.Subset.antisymm
    (dist_traceProb_subset sys)
    (dist_traceProb_superset sys)


end PLTS
