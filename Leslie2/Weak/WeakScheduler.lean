/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Systems.Trace

/-!
# Weak-scheduler bind calculus

The `bind` (sequential composition) calculus for schedulers and weak
schedulers: `WeakScheduler` (a scheduler emitting only internal labels), the
halting mass `haltMass`, `Scheduler.bind` / `WeakScheduler.bind`, and the
`bind_haltMass` identity decomposing the halting mass of a bind into a
prefix/suffix sum.

This is layer 2 of the weak-transition development: it sits between the trace
core (`Systems/Trace`) and the weak transitions (`Weak/Step`).
-/

open Stream'

namespace PLTS

-- The canonical-`τ` instance `[Silent Label]` is threaded as a section variable
-- but is only used by the weak-scheduler lemmas, not the pure `Scheduler`
-- combinatorics; silence the resulting over-inclusion linter file-wide.
set_option linter.unusedSectionVars false

variable {α β State State_C State_A Label : Type} [Silent Label]

/-! ### Weak Schedulers -/

/-- A *weak scheduler* for a labelled system: a `Scheduler` whose emissions are
restricted to internal labels. -/
structure WeakScheduler (sys : System State Label)
    extends Scheduler sys where
  internal_only : ∀ (e : AlterSeq State Label) (l : Label) (μ : PMF State),
    some (l, μ) ∈ (next e).support → (l = Silent.τ)

namespace WeakScheduler

variable {sys : System State Label}

/-- The weak scheduler that immediately stops on every prefix: it emits `⊥`
(`none`) everywhere. Used to witness reflexivity of weak transitions — it takes
no τ-steps, so it halts at once with the chain still at its starting state. -/
noncomputable def stop (sys : System State Label) : WeakScheduler sys where
  next _ := PMF.pure none
  valid e _ _ _ _ l μ h := by simp at h
  internal_only e l μ h := by simp at h

/-- **Monotonicity in the step relation.** A weak scheduler for `sys` is reusable *verbatim* as a
weak scheduler for any `sys'` whose `τ`-steps include all of `sys`'s: since a weak scheduler only
ever emits internal (`τ`) steps (`internal_only`), validating those same emissions against `sys'`
needs only that `sys`-`τ`-steps are `sys'`-`τ`-steps. The `next` function is unchanged, so
`haltMass`/`probOf` are definitionally identical. -/
noncomputable def mono {sys' : System State Label} (σ : WeakScheduler sys)
    (hstep : ∀ s μ, sys.step s Silent.τ μ → sys'.step s Silent.τ μ) : WeakScheduler sys' where
  next := σ.next
  valid := fun e n s ht hs l μ hsupp => by
    have hl := σ.internal_only e l μ hsupp
    subst hl
    exact hstep s μ (σ.valid e n s ht hs _ μ hsupp)
  internal_only := σ.internal_only

/-! ### Sequential composition of weak schedulers (`bind`) -/

/-- Dropping a prefix of a terminating execution's transition sequence again
terminates. -/
theorem drop_terminates {e : AlterSeq State Label} (hT : e.trans.Terminates) (j : ℕ) :
    (e.trans.drop j).Terminates := by
  obtain ⟨N, hN⟩ := hT
  exact ⟨N, by
    change (e.trans.drop j).get? N = none
    rw [Stream'.Seq.drop_get?]
    exact Stream'.Seq.terminated_stable e.trans (Nat.le_add_left N j) hN⟩

/-- The state of `e` after `j` transitions (junk default `e.init` outside the
valid range; only used for `j < length`, where `stateAt j` is `some`). -/
noncomputable def stateAfter (e : AlterSeq State Label) (j : ℕ) : State :=
  (e.stateAt j).getD e.init

/-- The end-state of the `j`-suffix `⟨stateAfter e j, e.trans.drop j⟩` equals the
end-state of `e` (both are the final state of `e`), for `j` within range. -/
theorem endState_drop (e : AlterSeq State Label) (hT : e.trans.Terminates) (j : ℕ)
    (hj : j < e.trans.length hT) :
    (⟨stateAfter e j, e.trans.drop j⟩ : AlterSeq State Label).endState (drop_terminates hT j)
      = e.endState hT := by
  classical
  set N := e.trans.length hT with hN
  -- `e`'s canonical end index is `N`.
  have hNe : Nat.find hT = N := rfl
  -- `e` does not terminate before `N`; in particular not at `j` (since `j < N`).
  have h_not_term_lt : ∀ k < N, ¬ e.trans.TerminatedAt k := fun k hk => Nat.find_min hT hk
  -- `e.trans.TerminatedAt N`.
  have hN_term : e.trans.TerminatedAt N := Nat.find_spec hT
  -- The drop's canonical end index is `N - j`.
  set d : AlterSeq State Label := ⟨stateAfter e j, e.trans.drop j⟩ with hd
  have hd_term := drop_terminates hT j
  -- `(e.trans.drop j).TerminatedAt (N - j)`.
  have hdrop_term : (e.trans.drop j).TerminatedAt (N - j) := by
    change (e.trans.drop j).get? (N - j) = none
    rw [Stream'.Seq.drop_get?, show j + (N - j) = N from by omega]
    exact hN_term
  -- `(e.trans.drop j)` does not terminate before `N - j`.
  have hdrop_not : ∀ m < N - j, ¬ (e.trans.drop j).TerminatedAt m := by
    intro m hm hcontra
    apply h_not_term_lt (j + m) (by omega)
    change e.trans.get? (j + m) = none
    rw [← Stream'.Seq.drop_get?]; exact hcontra
  -- Hence `Nat.find hd_term = N - j`.
  have hNd : Nat.find hd_term = N - j := by
    apply le_antisymm (Nat.find_le hdrop_term)
    by_contra hc
    push Not at hc
    exact hdrop_not (Nat.find hd_term) hc (Nat.find_spec hd_term)
  -- `N - j ≥ 1` since `j < N`.
  have hpos : 1 ≤ N - j := by omega
  obtain ⟨m, hm⟩ : ∃ m, N - j = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  -- Reduce to equality of the underlying `stateAt` options.
  have hstate : d.stateAt (Nat.find hd_term) = e.stateAt (Nat.find hT) := by
    rw [hNd, hNe, hm]
    change ((e.trans.drop j).get? m).map Prod.snd = e.stateAt N
    rw [Stream'.Seq.drop_get?]
    have hNeq : N = (j + m) + 1 := by omega
    rw [hNeq]
    rfl
  rw [AlterSeq.stateAt_find_eq_endState d hd_term,
    AlterSeq.stateAt_find_eq_endState e hT] at hstate
  exact (Option.some_inj.mp hstate)

/-! ### `bind_haltMass`: helpers -/

/-- Split an `ENNReal` tsum over `Option γ` into the `none` value plus the tsum
over `some`. -/
private theorem tsum_option_enn {γ : Type} (f : Option γ → ENNReal) :
    (∑' o, f o) = f none + ∑' n, f (some n) := by
  rw [← (Equiv.optionEquivSumPUnit.{0} γ).symm.tsum_eq f,
    Summable.tsum_sum ENNReal.summable ENNReal.summable, add_comm]
  congr 1
  rw [tsum_eq_single PUnit.unit (by rintro ⟨⟩ h; exact absurd rfl h)]
  rfl

/-- `Seq.take` of `Seq.ofList` is `List.take`. -/
theorem take_ofList {γ : Type} (L : List γ) (j : ℕ) :
    Stream'.Seq.take j (Stream'.Seq.ofList L) = L.take j := by
  induction j generalizing L with
  | zero => simp [Stream'.Seq.take]
  | succ n ih =>
    cases L with
    | nil => simp [Stream'.Seq.take]
    | cons a t =>
      rw [Stream'.Seq.ofList_cons, Stream'.Seq.take_succ_cons, List.take_succ_cons, ih]

/-- `Seq.drop` of `Seq.ofList` is `Seq.ofList ∘ List.drop`. -/
theorem drop_ofList {γ : Type} (L : List γ) (j : ℕ) :
    Stream'.Seq.drop (Stream'.Seq.ofList L) j = Stream'.Seq.ofList (L.drop j) := by
  induction j generalizing L with
  | zero => simp
  | succ n ih =>
    cases L with
    | nil => simp [Stream'.Seq.drop_nil]
    | cons a t =>
      rw [Stream'.Seq.ofList_cons, List.drop_succ_cons, Stream'.Seq.drop_succ_cons, ih]

/-- `Seq.ofList` of a list with one element appended is `append` of a singleton `cons`. -/
private theorem ofList_append_singleton {γ : Type} (L : List γ) (x : γ) :
    Stream'.Seq.ofList (L ++ [x])
      = (Stream'.Seq.ofList L).append (Seq.cons x Seq.nil) := by
  induction L with
  | nil => simp [Stream'.Seq.ofList_nil, Stream'.Seq.nil_append, Stream'.Seq.ofList_cons]
  | cons a t ih =>
    rw [List.cons_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_cons,
      Stream'.Seq.cons_append, ih]

/-- `length` of `Seq.ofList` is `List.length`. -/
theorem length_ofList {γ : Type} (L : List γ) :
    (Stream'.Seq.ofList L).length (Stream'.Seq.terminates_ofList L) = L.length := by
  rw [← Stream'.Seq.length_toList, Stream'.Seq.toList_ofList]

/-- `stateAfter ⟨s₀, ofList L⟩` of the empty offset is `s₀`. -/
private theorem stateAfter_ofList_zero (s₀ : State) (L : List (Label × State)) :
    stateAfter ⟨s₀, Stream'.Seq.ofList L⟩ 0 = s₀ := by
  unfold stateAfter
  rfl

/-- `stateAfter ⟨s₀, ofList L⟩ (n+1)` reads the `n`-th list entry's destination. -/
private theorem stateAfter_ofList_succ (s₀ : State) (L : List (Label × State)) (n : ℕ) :
    stateAfter ⟨s₀, Stream'.Seq.ofList L⟩ (n + 1) = ((L[n]?).map Prod.snd).getD s₀ := by
  unfold stateAfter AlterSeq.stateAt
  simp only
  rw [Stream'.Seq.ofList_get?]

/-- `stateAfter` is invariant under appending one transition, for offsets within
the original length. -/
private theorem stateAfter_append_eq (s₀ : State) (L : List (Label × State))
    (x : Label × State) (j : ℕ) (hj : j ≤ L.length) :
    stateAfter ⟨s₀, Stream'.Seq.ofList (L ++ [x])⟩ j
      = stateAfter ⟨s₀, Stream'.Seq.ofList L⟩ j := by
  cases j with
  | zero => rw [stateAfter_ofList_zero, stateAfter_ofList_zero]
  | succ n =>
    rw [stateAfter_ofList_succ, stateAfter_ofList_succ]
    have hn : n < L.length := Nat.lt_of_succ_le hj
    rw [List.getElem?_append_left hn]

/-- `stateAfter e (length e)` is the end-state of the (terminating) execution `e`. -/
theorem stateAfter_length_eq_endState (e : AlterSeq State Label)
    (hT : e.trans.Terminates) :
    stateAfter e (e.trans.length hT) = e.endState hT := by
  unfold stateAfter
  rw [show e.trans.length hT = Nat.find hT from rfl,
    AlterSeq.stateAt_find_eq_endState e hT]
  rfl

/-- `probOf` only depends on the `AlterSeq` (proofs of termination are
irrelevant): equal `AlterSeq`s have equal `probOf`. -/
private theorem probOf_congr_eq {Sys : System State Label}
    (pe : ProbabilisticExecution Sys) {e₁ e₂ : AlterSeq State Label}
    (heq : e₁ = e₂) (h₁ : e₁.trans.Terminates) (h₂ : e₂.trans.Terminates) :
    pe.probOf e₁ h₁ = pe.probOf e₂ h₂ := by
  subst heq; rfl

end WeakScheduler

namespace Scheduler

variable {sys : System State Label}

open WeakScheduler

/-- The **halting mass** of a scheduler `σ` from source `μ_init`, at a
terminating finite execution `e`: the probability of producing the transition
sequence `e` (under the probabilistic execution `⟨μ_init, σ⟩`) and then emitting
`⊥` (halting) at the prefix `e`. This is `probOf e · σ.next e ⊥`. -/
noncomputable def haltMass (σ : Scheduler sys) (μ_init : PMF State)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) : ENNReal :=
  (⟨μ_init, σ⟩ : ProbabilisticExecution sys).probOf e.1 e.2
    * σ.next e.1 none

/-- **`haltMass` is linear in the source distribution** (lifting `probOf_init_mix`,
since the halt probability `σ.next e ⊥` depends only on the scheduler). The
"un-disintegration over the source" used to glue weak-τ phases. -/
theorem haltMass_init_mix (σ : Scheduler sys) (μ_init : PMF State)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) :
    σ.haltMass μ_init e = ∑' s, μ_init s * σ.haltMass (PMF.pure s) e := by
  unfold Scheduler.haltMass
  rw [ProbabilisticExecution.probOf_init_mix σ μ_init e.1 e.2,
    ← ENNReal.tsum_mul_right]
  exact tsum_congr (fun s => by ring)

open Classical in
/-- The (un-normalized) belief weight over the split point of `bind σ k` at a
terminating execution `e`. `none` = σ produced all of `e` (and is still active);
`some j` = σ halted after `j` transitions and `k` produced the rest. Source-
independent: Dirac sources `PMF.pure` are used throughout. -/
noncomputable def bindWeight (σ : Scheduler sys)
    (k : State → Scheduler sys)
    (e : AlterSeq State Label) (hT : e.trans.Terminates) : Option ℕ → ENNReal
  | none => (⟨PMF.pure e.init, σ⟩ : ProbabilisticExecution sys).probOf e hT
  | some j =>
      if _hj : j < e.trans.length hT then
        σ.haltMass (PMF.pure e.init)
            ⟨⟨e.init, Seq.ofList (e.trans.take j)⟩, Stream'.Seq.terminates_ofList _⟩
          * (⟨PMF.pure (stateAfter e j), (k (stateAfter e j))⟩
              : ProbabilisticExecution sys).probOf
              ⟨stateAfter e j, e.trans.drop j⟩ (drop_terminates hT j)
      else 0

/-- The total belief weight is finite: the `some`-part is supported on
`{j | j < length}` and every weight is `≤ 1`. -/
private theorem bindWeight_tsum_ne_top (σ : Scheduler sys)
    (k : State → Scheduler sys)
    (e : AlterSeq State Label) (hT : e.trans.Terminates) :
    (∑' o, bindWeight σ k e hT o) ≠ ⊤ := by
  classical
  -- `probOf` from a Dirac source is `≤ 1`.
  have hprob_le_one : ∀ (sch : Scheduler sys) (e' : AlterSeq State Label)
      (h' : e'.trans.Terminates),
      (⟨PMF.pure e'.init, sch⟩ : ProbabilisticExecution sys).probOf e' h' ≤ 1 := by
    intro sch e' h'
    refine le_trans (ProbabilisticExecution.probOf_le_init _ e' h') ?_
    rw [ProbabilisticExecution.init_eq_initState]
    exact PMF.coe_le_one _ _
  -- Bound each weight by `1`.
  have hbound : ∀ o : Option ℕ, bindWeight σ k e hT o ≤ 1 := by
    intro o
    cases o with
    | none =>
      change (⟨PMF.pure e.init, σ⟩ :
        ProbabilisticExecution sys).probOf e hT ≤ 1
      exact hprob_le_one _ e hT
    | some j =>
      change (if _ : j < e.trans.length hT then _ else 0) ≤ 1
      by_cases hj : j < e.trans.length hT
      · rw [dif_pos hj]
        refine mul_le_one' ?_ (hprob_le_one _ _ _)
        unfold Scheduler.haltMass
        exact mul_le_one' (hprob_le_one _ _ _) (PMF.coe_le_one _ _)
      · rw [dif_neg hj]; exact zero_le_one
  -- The `some`-weights vanish off `Finset.range (length)`.
  set S : Finset (Option ℕ) :=
    insert none ((Finset.range (e.trans.length hT)).image some) with hS
  have hzero : ∀ o ∉ S, bindWeight σ k e hT o = 0 := by
    intro o ho
    cases o with
    | none => exact absurd (Finset.mem_insert_self none _) ho
    | some j =>
      have hj : ¬ j < e.trans.length hT := by
        intro hlt
        exact ho (Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hlt, rfl⟩))
      change (if hj : j < e.trans.length hT then _ else 0) = 0
      rw [dif_neg hj]
  rw [tsum_eq_sum hzero]
  refine ENNReal.sum_ne_top.mpr ?_
  intro o _
  exact ne_top_of_le_ne_top ENNReal.one_ne_top (hbound o)

/-- The first-step action when the belief says "σ stays active to the end":
fold σ's halt into `k`'s first step at the end-state of `e`. -/
private noncomputable def actionBot (σ : Scheduler sys)
    (k : State → Scheduler sys)
    (e : AlterSeq State Label) (hT : e.trans.Terminates) : PMF (Option (Label × PMF State)) :=
  (σ.next e).bind (fun o => match o with
    | none => (k (e.endState hT)).next ⟨e.endState hT, Seq.nil⟩
    | some lμ => PMF.pure (some lμ))

/-- The first-step action when the belief says "σ halted after `j` steps": let
`k` (started at the state after `j`) act on the remaining suffix. -/
private noncomputable def actionK (k : State → Scheduler sys)
    (e : AlterSeq State Label) (j : ℕ) : PMF (Option (Label × PMF State)) :=
  (k (stateAfter e j)).next ⟨stateAfter e j, e.trans.drop j⟩

open Classical in
/-- **Sequential composition** of schedulers: `bind σ k` runs `σ` from the
start and, at `σ`'s almost-sure halt at state `s`, switches to `k s`. The σ→k
boundary is invisible in the concrete history, so the first step is a *belief*
over the split point (`bindWeight`, source-independent), realised by
`PMF.normalize` then `bind` into `actionBot`/`actionK`. -/
noncomputable def bind (σ : Scheduler sys) (k : State → Scheduler sys) :
    Scheduler sys where
  next e :=
    if hT : e.trans.Terminates then
      if h0 : (∑' o, bindWeight σ k e hT o) ≠ 0 then
        (PMF.normalize (bindWeight σ k e hT) h0 (bindWeight_tsum_ne_top σ k e hT)).bind
          (fun o => match o with
            | none => actionBot σ k e hT
            | some j => actionK k e j)
      else PMF.pure none
    else PMF.pure none
  valid := by
    classical
    intro e n s e_term_n e_stateAt_eq l μ h_supp
    have hT : e.trans.Terminates := ⟨n, e_term_n⟩
    -- Identify `s` as `e.endState hT` (`n` is the canonical end index).
    have h_find_le : Nat.find hT ≤ n := Nat.find_le e_term_n
    have h_n_le : n ≤ Nat.find hT := by
      by_contra h_lt
      push Not at h_lt
      rcases n with _ | m
      · exact absurd h_lt (Nat.not_lt_zero _)
      · have hk_ge : Nat.find hT ≤ m := Nat.lt_succ_iff.mp h_lt
        have h_term_k : e.trans.TerminatedAt m :=
          Stream'.Seq.terminated_stable e.trans hk_ge (Nat.find_spec hT)
        have h_state_none : e.stateAt (m + 1) = none := by
          change (e.trans.get? m).map Prod.snd = none
          rw [show e.trans.get? m = none from h_term_k]; rfl
        rw [h_state_none] at e_stateAt_eq
        exact Option.some_ne_none s e_stateAt_eq.symm
    have h_n_eq : n = Nat.find hT := le_antisymm h_n_le h_find_le
    have h_s_eq : s = e.endState hT := by
      have h := AlterSeq.stateAt_find_eq_endState e hT
      rw [← h_n_eq] at h; rw [h] at e_stateAt_eq
      exact (Option.some.inj e_stateAt_eq).symm
    subst h_s_eq
    -- Reduce the support membership to the main branch.
    change some (l, μ) ∈
      (if hT' : e.trans.Terminates then
        if h0 : ∑' (o : Option ℕ), σ.bindWeight k e hT' o ≠ 0 then
          (PMF.normalize (σ.bindWeight k e hT') h0 _).bind fun o =>
            match o with
            | none => σ.actionBot k e hT'
            | some j => actionK k e j
        else PMF.pure none
      else PMF.pure none).support at h_supp
    rw [dif_pos hT] at h_supp
    by_cases h0 : ∑' (o : Option ℕ), σ.bindWeight k e hT o ≠ 0
    · rw [dif_pos h0, PMF.mem_support_bind_iff] at h_supp
      obtain ⟨o, ho_mem, h_supp⟩ := h_supp
      cases o with
      | none =>
        -- `actionBot`: emission comes from σ or from k at the end-state.
        change some (l, μ) ∈ (σ.actionBot k e hT).support at h_supp
        unfold Scheduler.actionBot at h_supp
        rw [PMF.mem_support_bind_iff] at h_supp
        obtain ⟨o', ho'_mem, h_supp⟩ := h_supp
        cases o' with
        | none =>
          -- From `(k (e.endState hT)).next ⟨e.endState hT, nil⟩`.
          change some (l, μ) ∈ ((k (e.endState hT)).next
            ⟨e.endState hT, Seq.nil⟩).support at h_supp
          exact (k (e.endState hT)).valid ⟨e.endState hT, Seq.nil⟩ 0 (e.endState hT)
            (by change (Seq.nil : Seq (Label × State)).get? 0 = none; rfl) rfl l μ h_supp
        | some lμ' =>
          -- From `σ.next e`, via `pure (some lμ')`.
          change some (l, μ) ∈ (PMF.pure (some lμ')).support at h_supp
          rw [PMF.mem_support_pure_iff] at h_supp
          have : lμ' = (l, μ) := (Option.some.inj h_supp).symm
          subst this
          exact σ.valid e n (e.endState hT) e_term_n
            (h_n_eq ▸ AlterSeq.stateAt_find_eq_endState e hT) l μ ho'_mem
      | some j =>
        -- `actionK`: emission from `k (stateAfter e j)` on the suffix.
        change some (l, μ) ∈ (actionK k e j).support at h_supp
        unfold Scheduler.actionK at h_supp
        -- `j < length` from `bindWeight (some j) ≠ 0`.
        rw [PMF.mem_support_normalize_iff] at ho_mem
        have hj : j < e.trans.length hT := by
          by_contra hc
          apply ho_mem
          change (if _ : j < e.trans.length hT then _ else 0) = 0
          rw [dif_neg hc]
        -- Apply `k`'s validity at the canonical end of the suffix (end-state `e.endState hT`).
        set d : AlterSeq State Label := ⟨stateAfter e j, e.trans.drop j⟩ with hd
        have hd_term := drop_terminates hT j
        have hvalid := (k (stateAfter e j)).valid d (Nat.find hd_term) (d.endState hd_term)
          (Nat.find_spec hd_term) (AlterSeq.stateAt_find_eq_endState d hd_term) l μ h_supp
        rw [endState_drop e hT j hj] at hvalid
        exact hvalid
    · rw [dif_neg h0] at h_supp
      change some (l, μ) ∈ (PMF.pure (α := Option (Label × PMF State)) none).support at h_supp
      rw [PMF.mem_support_pure_iff] at h_supp
      exact absurd h_supp (by simp)

open Classical in
/-- **Normalizer-cancellation.** Scaling `(bind σ k).next e` by the total belief
weight `Z(e) := ∑' o, bindWeight σ k e hT o` cancels the `PMF.normalize`, leaving
the raw belief-weighted mixture of `actionBot`/`actionK` (evaluated at any `b`).
Holds in both branches: when `Z(e) = 0` both sides vanish. -/
private theorem bind_next_smul (σ : Scheduler sys) (k : State → Scheduler sys)
    (e : AlterSeq State Label) (hT : e.trans.Terminates) (b : Option (Label × PMF State)) :
    (∑' o, bindWeight σ k e hT o) * (bind σ k).next e b
      = ∑' (i : Option ℕ), bindWeight σ k e hT i
          * (match i with
              | none => actionBot σ k e hT
              | some j => actionK k e j : PMF (Option (Label × PMF State))) b := by
  have hnext : (bind σ k).next e
      = if hT' : e.trans.Terminates then
          if h0 : (∑' o, bindWeight σ k e hT' o) ≠ 0 then
            (PMF.normalize (bindWeight σ k e hT') h0 (bindWeight_tsum_ne_top σ k e hT')).bind
              (fun o => match o with
                | none => actionBot σ k e hT'
                | some j => actionK k e j)
          else PMF.pure none
        else PMF.pure none := rfl
  rw [hnext, dif_pos hT]
  by_cases h0 : (∑' o, bindWeight σ k e hT o) ≠ 0
  · rw [dif_pos h0, PMF.bind_apply, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro i
    rw [PMF.normalize_apply]
    rw [show (∑' o, bindWeight σ k e hT o)
          * (bindWeight σ k e hT i * (∑' x, bindWeight σ k e hT x)⁻¹
              * (match i with
                  | none => actionBot σ k e hT
                  | some j => actionK k e j : PMF (Option (Label × PMF State))) b)
        = (bindWeight σ k e hT i
            * (match i with
                | none => actionBot σ k e hT
                | some j => actionK k e j : PMF (Option (Label × PMF State))) b)
          * ((∑' o, bindWeight σ k e hT o) * (∑' x, bindWeight σ k e hT x)⁻¹) from by ring]
    rw [ENNReal.mul_inv_cancel h0 (bindWeight_tsum_ne_top σ k e hT), mul_one]
  · push Not at h0
    rw [dif_neg (by rw [h0]; simp), h0, zero_mul]
    symm
    rw [ENNReal.tsum_eq_zero] at h0 ⊢
    intro i
    rw [h0 i, zero_mul]

/-- The `(l, s')`-kernel of `actionK k e j`: aggregating `actionK`'s emission over
`ν` with weight `ν s'` is exactly `k (stateAfter e j)`'s one-step kernel on the
remaining suffix `⟨stateAfter e j, e.trans.drop j⟩`. -/
private theorem actionK_kernel (k : State → Scheduler sys)
    (e : AlterSeq State Label) (j : ℕ) (l : Label) (s' : State) :
    (∑' ν, (actionK k e j) (some (l, ν)) * ν s')
      = (⟨PMF.pure (stateAfter e j), (k (stateAfter e j))⟩
          : ProbabilisticExecution sys).kernel
          ⟨stateAfter e j, e.trans.drop j⟩ (l, s') := by
  rfl

/-- The `(l, s')`-kernel of `actionBot σ k e hT`: σ's one-step kernel on `e` plus
σ's halt mass times `k (e.endState)`'s first-step kernel from the end-state. -/
private theorem actionBot_kernel (σ : Scheduler sys) (k : State → Scheduler sys)
    (e : AlterSeq State Label) (hT : e.trans.Terminates) (l : Label) (s' : State) :
    (∑' ν, (actionBot σ k e hT) (some (l, ν)) * ν s')
      = (⟨PMF.pure e.init, σ⟩
          : ProbabilisticExecution sys).kernel e (l, s')
        + σ.next e none
          * (⟨PMF.pure (e.endState hT), (k (e.endState hT))⟩
              : ProbabilisticExecution sys).kernel
              ⟨e.endState hT, Seq.nil⟩ (l, s') := by
  classical
  unfold actionBot
  -- expand the outer bind and the `ν`-sum
  simp only [PMF.bind_apply]
  -- target RHS kernels in tsum form
  rw [show (⟨PMF.pure e.init, σ⟩
        : ProbabilisticExecution sys).kernel e (l, s')
      = ∑' ν, σ.next e (some (l, ν)) * ν s' from rfl]
  rw [show (⟨PMF.pure (e.endState hT), (k (e.endState hT))⟩
        : ProbabilisticExecution sys).kernel ⟨e.endState hT, Seq.nil⟩ (l, s')
      = ∑' ν, (k (e.endState hT)).next ⟨e.endState hT, Seq.nil⟩ (some (l, ν)) * ν s' from rfl]
  rw [show σ.next e none
        * ∑' ν, (k (e.endState hT)).next ⟨e.endState hT, Seq.nil⟩ (some (l, ν)) * ν s'
      = ∑' ν, σ.next e none
          * ((k (e.endState hT)).next ⟨e.endState hT, Seq.nil⟩ (some (l, ν)) * ν s')
      from (ENNReal.tsum_mul_left).symm]
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro ν
  -- LHS at ν: (∑' o, σ.next e o * matchAction o (some (l,ν))) * ν s'
  rw [show (∑' (a : Option (Label × PMF State)),
        σ.next e a * (match a with
          | none => (k (e.endState hT)).next ⟨e.endState hT, Seq.nil⟩
          | some lμ => PMF.pure (some lμ) : PMF (Option (Label × PMF State))) (some (l, ν)))
      = σ.next e none * ((k (e.endState hT)).next ⟨e.endState hT, Seq.nil⟩) (some (l, ν))
        + ∑' lμ : Label × PMF State,
          σ.next e (some lμ) * (PMF.pure (some lμ) : PMF (Option (Label × PMF State))) (some (l, ν))
      from tsum_option_enn _]
  -- collapse the `some` tsum to `σ.next e (some (l,ν))`
  rw [show (∑' lμ : Label × PMF State,
        σ.next e (some lμ) * (PMF.pure (some lμ) : PMF (Option (Label × PMF State))) (some (l, ν)))
      = σ.next e (some (l, ν)) from by
        rw [tsum_eq_single (l, ν) (fun lμ hlμ => by
          rw [PMF.pure_apply, if_neg (by intro h; exact hlμ (Option.some.inj h).symm), mul_zero])]
        rw [PMF.pure_apply, if_pos rfl, mul_one]]
  ring

/-- `haltMass` only depends on the underlying `AlterSeq`. -/
theorem haltMass_congr_eq (σ : Scheduler sys) (μ : PMF State)
    {e₁ e₂ : {e : AlterSeq State Label // e.trans.Terminates}}
    (heq : e₁.1 = e₂.1) :
    σ.haltMass μ e₁ = σ.haltMass μ e₂ := by
  obtain ⟨e₁, h₁⟩ := e₁
  obtain ⟨e₂, h₂⟩ := e₂
  simp only at heq
  subst heq; rfl

/-- The `none`-weight of `e = e' ++ [(l,s')]` is the `none`-weight of `e'` times
σ's one-step kernel. -/
private theorem bindWeight_none_append (σ : Scheduler sys)
    (k : State → Scheduler sys)
    (s₀ : State) (L' : List (Label × State)) (l : Label) (s' : State) :
    bindWeight σ k ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩
        (Stream'.Seq.terminates_ofList _) none
      = bindWeight σ k ⟨s₀, Stream'.Seq.ofList L'⟩ (Stream'.Seq.terminates_ofList _) none
        * (⟨PMF.pure s₀, σ⟩ : ProbabilisticExecution sys).kernel
            ⟨s₀, Stream'.Seq.ofList L'⟩ (l, s') := by
  have heq : (⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩ : AlterSeq State Label)
      = ⟨s₀, (Stream'.Seq.ofList L').append (Seq.cons (l, s') Seq.nil)⟩ := by
    rw [ofList_append_singleton]
  change (⟨PMF.pure s₀, σ⟩ : ProbabilisticExecution sys).probOf
        ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩ _
      = (⟨PMF.pure s₀, σ⟩ : ProbabilisticExecution sys).probOf
          ⟨s₀, Stream'.Seq.ofList L'⟩ _
        * (⟨PMF.pure s₀, σ⟩ : ProbabilisticExecution sys).kernel
            ⟨s₀, Stream'.Seq.ofList L'⟩ (l, s')
  rw [probOf_congr_eq _ heq _ (heq ▸ Stream'.Seq.terminates_ofList (L' ++ [(l, s')]))]
  rw [ProbabilisticExecution.probOf_append_singleton _ s₀ (Stream'.Seq.ofList L')
    (Stream'.Seq.terminates_ofList L') (l, s') _]

/-- The `(some j)`-weight of `e = e' ++ [(l,s')]` for `j < |L'|`: it equals the
`(some j)`-weight of `e'` times `k`'s one-step kernel on the suffix. -/
private theorem bindWeight_some_lt (σ : Scheduler sys) (k : State → Scheduler sys)
    (s₀ : State) (L' : List (Label × State)) (l : Label) (s' : State)
    (j : ℕ) (hj : j < L'.length) :
    bindWeight σ k ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩
        (Stream'.Seq.terminates_ofList _) (some j)
      = bindWeight σ k ⟨s₀, Stream'.Seq.ofList L'⟩ (Stream'.Seq.terminates_ofList _) (some j)
        * (⟨PMF.pure (stateAfter ⟨s₀, Stream'.Seq.ofList L'⟩ j),
              (k (stateAfter ⟨s₀, Stream'.Seq.ofList L'⟩ j))⟩
            : ProbabilisticExecution sys).kernel
            ⟨stateAfter ⟨s₀, Stream'.Seq.ofList L'⟩ j,
              (Stream'.Seq.ofList L').drop j⟩ (l, s') := by
  classical
  -- length facts
  have hlenE : (Stream'.Seq.ofList (L' ++ [(l, s')]) : Seq (Label × State)).length
      (Stream'.Seq.terminates_ofList _) = L'.length + 1 := by
    rw [length_ofList]; simp
  have hlenE' : (Stream'.Seq.ofList L' : Seq (Label × State)).length
      (Stream'.Seq.terminates_ofList _) = L'.length := length_ofList L'
  -- stateAfter invariance
  have hstate : stateAfter ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩ j
      = stateAfter ⟨s₀, Stream'.Seq.ofList L'⟩ j :=
    stateAfter_append_eq s₀ L' (l, s') j (le_of_lt hj)
  -- unfold both `some j` weights
  change (if _hj : j < (Stream'.Seq.ofList (L' ++ [(l, s')])).length
          (Stream'.Seq.terminates_ofList _) then
        σ.haltMass (PMF.pure s₀)
            ⟨⟨s₀, Stream'.Seq.ofList ((Stream'.Seq.ofList (L' ++ [(l, s')])).take j)⟩, _⟩
          * (⟨PMF.pure (stateAfter ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩ j),
                (k (stateAfter ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩ j))⟩
              : ProbabilisticExecution sys).probOf
              ⟨stateAfter ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩ j,
                (Stream'.Seq.ofList (L' ++ [(l, s')])).drop j⟩ _
        else 0)
      = (if _hj : j < (Stream'.Seq.ofList L').length (Stream'.Seq.terminates_ofList _) then
          σ.haltMass (PMF.pure s₀)
              ⟨⟨s₀, Stream'.Seq.ofList ((Stream'.Seq.ofList L').take j)⟩, _⟩
            * (⟨PMF.pure (stateAfter ⟨s₀, Stream'.Seq.ofList L'⟩ j),
                  (k (stateAfter ⟨s₀, Stream'.Seq.ofList L'⟩ j))⟩
                : ProbabilisticExecution sys).probOf
                ⟨stateAfter ⟨s₀, Stream'.Seq.ofList L'⟩ j,
                  (Stream'.Seq.ofList L').drop j⟩ _
          else 0) * _
  rw [dif_pos (show j < (Stream'.Seq.ofList (L' ++ [(l, s')])).length _ by rw [hlenE]; omega),
    dif_pos (show j < (Stream'.Seq.ofList L').length _ by rw [hlenE']; exact hj)]
  -- the take-factor (haltMass) agrees
  have htake : (⟨s₀, Stream'.Seq.ofList ((Stream'.Seq.ofList (L' ++ [(l, s')])).take j)⟩
        : AlterSeq State Label)
      = ⟨s₀, Stream'.Seq.ofList ((Stream'.Seq.ofList L').take j)⟩ := by
    rw [take_ofList, take_ofList, List.take_append_of_le_length (le_of_lt hj)]
  rw [haltMass_congr_eq σ (PMF.pure s₀)
    (e₁ := ⟨⟨s₀, Stream'.Seq.ofList ((Stream'.Seq.ofList (L' ++ [(l, s')])).take j)⟩,
      Stream'.Seq.terminates_ofList _⟩)
    (e₂ := ⟨⟨s₀, Stream'.Seq.ofList ((Stream'.Seq.ofList L').take j)⟩,
      Stream'.Seq.terminates_ofList _⟩) htake]
  rw [mul_assoc]
  congr 1
  -- the probOf factor expands via append-singleton + stateAfter equality
  rw [hstate]
  have heq2 : (⟨stateAfter ⟨s₀, Stream'.Seq.ofList L'⟩ j,
        (Stream'.Seq.ofList (L' ++ [(l, s')])).drop j⟩ : AlterSeq State Label)
      = ⟨stateAfter ⟨s₀, Stream'.Seq.ofList L'⟩ j,
        ((Stream'.Seq.ofList L').drop j).append (Seq.cons (l, s') Seq.nil)⟩ := by
    rw [drop_ofList, drop_ofList, List.drop_append_of_le_length (le_of_lt hj),
      ofList_append_singleton]
  rw [probOf_congr_eq _ heq2 _
    (heq2 ▸ drop_terminates (e := ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩)
      (Stream'.Seq.terminates_ofList _) j)]
  rw [ProbabilisticExecution.probOf_append_singleton _ _ ((Stream'.Seq.ofList L').drop j)
    (drop_terminates (e := ⟨s₀, Stream'.Seq.ofList L'⟩)
      (Stream'.Seq.terminates_ofList L') j) (l, s') _]

/-- The **top-split** `(some |L'|)`-weight of `e = e' ++ [(l,s')]`: σ produced all
of `e'` and halted; `k` produces the single final step. Equals `e'`'s `none`-weight
times σ's halt mass times `k`'s first-step kernel from the end-state. -/
private theorem bindWeight_some_top (σ : Scheduler sys)
    (k : State → Scheduler sys)
    (s₀ : State) (L' : List (Label × State)) (l : Label) (s' : State) :
    bindWeight σ k ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩
        (Stream'.Seq.terminates_ofList _) (some L'.length)
      = bindWeight σ k ⟨s₀, Stream'.Seq.ofList L'⟩ (Stream'.Seq.terminates_ofList _) none
        * (σ.next ⟨s₀, Stream'.Seq.ofList L'⟩ none
          * (⟨PMF.pure ((⟨s₀, Stream'.Seq.ofList L'⟩ : AlterSeq State Label).endState
                  (Stream'.Seq.terminates_ofList _)),
                (k ((⟨s₀, Stream'.Seq.ofList L'⟩ : AlterSeq State Label).endState
                  (Stream'.Seq.terminates_ofList _)))⟩
              : ProbabilisticExecution sys).kernel
              ⟨(⟨s₀, Stream'.Seq.ofList L'⟩ : AlterSeq State Label).endState
                (Stream'.Seq.terminates_ofList _), Seq.nil⟩ (l, s')) := by
  classical
  set e' : AlterSeq State Label := ⟨s₀, Stream'.Seq.ofList L'⟩ with he'
  set send := e'.endState (Stream'.Seq.terminates_ofList L') with hsend
  have hlenE : (Stream'.Seq.ofList (L' ++ [(l, s')]) : Seq (Label × State)).length
      (Stream'.Seq.terminates_ofList _) = L'.length + 1 := by
    rw [length_ofList]; simp
  -- stateAfter at top split = end state of e'
  have hstate : stateAfter ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩ L'.length = send := by
    rw [stateAfter_append_eq s₀ L' (l, s') L'.length (le_refl _)]
    rw [show (L'.length : ℕ) = (Stream'.Seq.ofList L').length (Stream'.Seq.terminates_ofList _) from
      (length_ofList L').symm]
    exact stateAfter_length_eq_endState e' (Stream'.Seq.terminates_ofList L')
  -- unfold the top-split weight
  change (if _hj : L'.length < (Stream'.Seq.ofList (L' ++ [(l, s')])).length
          (Stream'.Seq.terminates_ofList _) then
        σ.haltMass (PMF.pure s₀)
            ⟨⟨s₀, Stream'.Seq.ofList ((Stream'.Seq.ofList (L' ++ [(l, s')])).take L'.length)⟩, _⟩
          * (⟨PMF.pure (stateAfter ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩ L'.length),
                (k (stateAfter ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩ L'.length))⟩
              : ProbabilisticExecution sys).probOf
              ⟨stateAfter ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩ L'.length,
                (Stream'.Seq.ofList (L' ++ [(l, s')])).drop L'.length⟩ _
        else 0) = _
  rw [dif_pos (show L'.length < (Stream'.Seq.ofList (L' ++ [(l, s')])).length _ by
    rw [hlenE]; omega)]
  -- take L'.length = L'
  have htake : (⟨s₀, Stream'.Seq.ofList ((Stream'.Seq.ofList (L' ++ [(l, s')])).take L'.length)⟩
        : AlterSeq State Label) = e' := by
    rw [take_ofList, List.take_left]
  rw [haltMass_congr_eq σ (PMF.pure s₀)
    (e₁ := ⟨⟨s₀, Stream'.Seq.ofList ((Stream'.Seq.ofList (L' ++ [(l, s')])).take L'.length)⟩,
      Stream'.Seq.terminates_ofList _⟩)
    (e₂ := ⟨e', Stream'.Seq.terminates_ofList L'⟩) htake]
  -- σ.haltMass (pure s₀) e' = bindWeight e' none * σ.next e' none
  rw [show σ.haltMass (PMF.pure s₀) ⟨e', Stream'.Seq.terminates_ofList L'⟩
      = bindWeight σ k e' (Stream'.Seq.terminates_ofList _) none * σ.next e' none from rfl]
  rw [hstate]
  -- drop L'.length e.trans = cons (l,s') nil
  have hdrop : (⟨send, (Stream'.Seq.ofList (L' ++ [(l, s')])).drop L'.length⟩
        : AlterSeq State Label)
      = ⟨send, (Seq.nil : Seq (Label × State)).append (Seq.cons (l, s') Seq.nil)⟩ := by
    rw [drop_ofList, List.drop_append_of_le_length (le_refl _), List.drop_length,
      List.nil_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil,
      Stream'.Seq.nil_append]
  rw [probOf_congr_eq _ hdrop _
    (hdrop ▸ drop_terminates (e := ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩)
      (Stream'.Seq.terminates_ofList _) L'.length)]
  rw [ProbabilisticExecution.probOf_append_singleton _ send (Seq.nil : Seq (Label × State))
    Stream'.Seq.terminates_nil (l, s') _]
  rw [ProbabilisticExecution.probOf_nil]
  rw [ProbabilisticExecution.init_eq_initState]
  simp only [PMF.pure_apply_self]
  ring

open Classical in
/-- **Reach step identity.** Scaling the `bind`-kernel one step `(l,s')` from `e'`
by `e'`'s total belief weight gives `e = e' ++ [(l,s')]`'s total belief weight.
The core of the telescoping `reach` lemma. -/
private theorem reach_step (σ : Scheduler sys) (k : State → Scheduler sys)
    (s₀ : State) (L' : List (Label × State)) (l : Label) (s' : State) :
    (∑' o, bindWeight σ k ⟨s₀, Stream'.Seq.ofList L'⟩ (Stream'.Seq.terminates_ofList _) o)
        * (⟨PMF.pure s₀, (bind σ k)⟩
            : ProbabilisticExecution sys).kernel ⟨s₀, Stream'.Seq.ofList L'⟩ (l, s')
      = ∑' o, bindWeight σ k ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩
          (Stream'.Seq.terminates_ofList _) o := by
  classical
  set e' : AlterSeq State Label := ⟨s₀, Stream'.Seq.ofList L'⟩ with he'
  set Z' := ∑' o, bindWeight σ k e' (Stream'.Seq.terminates_ofList L') o with hZ'
  -- Reduce LHS to ∑' i, bindWeight e' i * κ(i).
  have hkernel : (⟨PMF.pure s₀, (bind σ k)⟩
        : ProbabilisticExecution sys).kernel e' (l, s')
      = ∑' ν, (bind σ k).next e' (some (l, ν)) * ν s' := rfl
  rw [hkernel, ← ENNReal.tsum_mul_left]
  -- push Z' into each ν-term and apply bind_next_smul
  rw [show (∑' ν, Z' * ((bind σ k).next e' (some (l, ν)) * ν s'))
      = ∑' ν, (∑' i, bindWeight σ k e' (Stream'.Seq.terminates_ofList L') i
          * (match i with
              | none => actionBot σ k e' (Stream'.Seq.terminates_ofList L')
              | some j => actionK k e' j : PMF (Option (Label × PMF State))) (some (l, ν))) * ν s'
      from by
        apply tsum_congr; intro ν
        rw [← mul_assoc, hZ', bind_next_smul]]
  -- ∑' ν ∑' i ... * ν s'  =  ∑' i ∑' ν ... * ν s'
  rw [show (∑' ν, (∑' i, bindWeight σ k e' (Stream'.Seq.terminates_ofList L') i
          * (match i with
              | none => actionBot σ k e' (Stream'.Seq.terminates_ofList L')
              | some j => actionK k e' j : PMF (Option (Label × PMF State))) (some (l, ν))) * ν s')
      = ∑' i, bindWeight σ k e' (Stream'.Seq.terminates_ofList L') i
          * (∑' ν, (match i with
              | none => actionBot σ k e' (Stream'.Seq.terminates_ofList L')
              | some j => actionK k e' j : PMF (Option (Label × PMF State))) (some (l, ν)) * ν s')
      from by
        rw [show (∑' ν, (∑' i, bindWeight σ k e' (Stream'.Seq.terminates_ofList L') i
              * (match i with
                | none => actionBot σ k e' (Stream'.Seq.terminates_ofList L')
                | some j => actionK k e' j : ) (some (l, ν))) * ν s')
            = ∑' ν, ∑' i, (bindWeight σ k e' (Stream'.Seq.terminates_ofList L') i
              * (match i with
                | none => actionBot σ k e' (Stream'.Seq.terminates_ofList L')
                | some j => actionK k e' j : PMF (Option (Label × PMF State))) (some (l, ν))) * ν s'
            from by
              apply tsum_congr; intro ν; rw [← ENNReal.tsum_mul_right]]
        rw [ENNReal.tsum_comm]
        apply tsum_congr; intro i
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr; intro ν
        ring]
  -- split both sides over `none` / `some j`
  rw [tsum_option_enn (fun i => bindWeight σ k e' (Stream'.Seq.terminates_ofList L') i
        * ∑' ν, (match i with
            | none => actionBot σ k e' (Stream'.Seq.terminates_ofList L')
            | some j => actionK k e' j : PMF (Option (Label × PMF State))) (some (l, ν)) * ν s')]
  rw [tsum_option_enn (fun o => bindWeight σ k ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩
        (Stream'.Seq.terminates_ofList _) o)]
  -- the `none`-term on LHS uses actionBot_kernel
  rw [show (∑' ν, (actionBot σ k e' (Stream'.Seq.terminates_ofList L')) (some (l, ν)) * ν s')
      = (⟨PMF.pure e'.init, σ⟩ : ProbabilisticExecution sys).kernel e' (l, s')
        + σ.next e' none
          * (⟨PMF.pure (e'.endState (Stream'.Seq.terminates_ofList L')),
                (k (e'.endState (Stream'.Seq.terminates_ofList L')))⟩
              : ProbabilisticExecution sys).kernel
              ⟨e'.endState (Stream'.Seq.terminates_ofList L'), Seq.nil⟩ (l, s')
      from actionBot_kernel σ k e' (Stream'.Seq.terminates_ofList L') l s']
  -- expand the `none` LHS term:
  -- bindWeight e' none * (kσ + ...) = bindWeight e none + bindWeight e top
  rw [show bindWeight σ k e' (Stream'.Seq.terminates_ofList L') none *
      ((⟨PMF.pure e'.init, σ⟩ : ProbabilisticExecution sys).kernel e' (l, s')
          + σ.next e' none
            * (⟨PMF.pure (e'.endState (Stream'.Seq.terminates_ofList L')),
                  (k (e'.endState (Stream'.Seq.terminates_ofList L')))⟩
                : ProbabilisticExecution sys).kernel
                ⟨e'.endState (Stream'.Seq.terminates_ofList L'), Seq.nil⟩ (l, s'))
      = bindWeight σ k ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩
          (Stream'.Seq.terminates_ofList _) none
        + bindWeight σ k ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩
            (Stream'.Seq.terminates_ofList _) (some L'.length)
      from by
        rw [mul_add]
        simp only [he']
        rw [← bindWeight_none_append σ k s₀ L' l s', ← bindWeight_some_top σ k s₀ L' l s']]
  -- the `some j` terms:
  -- bindWeight e' (some j) * κ(some j) = bindWeight e (some j) for j<|L'|, 0 else
  rw [show (∑' j, bindWeight σ k e' (Stream'.Seq.terminates_ofList L') (some j)
          * ∑' ν, (actionK k e' j) (some (l, ν)) * ν s')
      = ∑' j, (if j < L'.length then
          bindWeight σ k ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩
            (Stream'.Seq.terminates_ofList _) (some j) else 0)
      from by
        apply tsum_congr; intro j
        rw [actionK_kernel]
        by_cases hj : j < L'.length
        · rw [if_pos hj]
          simp only [he']
          rw [← bindWeight_some_lt σ k s₀ L' l s' j hj]
        · rw [if_neg hj]
          rw [show bindWeight σ k e' (Stream'.Seq.terminates_ofList L') (some j) = 0 from by
            change (if _ : j < (Stream'.Seq.ofList L').length _ then _ else 0) = 0
            rw [dif_neg (by rw [length_ofList]; exact hj)]]
          rw [zero_mul]]
  -- now: (bindWeight e none + bindWeight e top) + ∑' j (filtered)
  --    = bindWeight e none + ∑' j, bindWeight e (some j)
  rw [add_assoc]
  congr 1
  -- ∑' j, bindWeight e (some j) = bindWeight e (some |L'|) + ∑' j (filtered)
  rw [show (∑' j, bindWeight σ k ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩
        (Stream'.Seq.terminates_ofList _) (some j))
      = bindWeight σ k ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩
          (Stream'.Seq.terminates_ofList _) (some L'.length)
        + ∑' j, (if j < L'.length then
            bindWeight σ k ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩
              (Stream'.Seq.terminates_ofList _) (some j) else 0)
      from by
        have hsplit : ∀ j, bindWeight σ k ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩
              (Stream'.Seq.terminates_ofList _) (some j)
            = (if j = L'.length then
                bindWeight σ k ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩
                  (Stream'.Seq.terminates_ofList _) (some L'.length) else 0)
              + (if j < L'.length then
                bindWeight σ k ⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩
                  (Stream'.Seq.terminates_ofList _) (some j) else 0) := by
          intro j
          rcases lt_trichotomy j L'.length with hlt | heq | hgt
          · rw [if_neg (Nat.ne_of_lt hlt), if_pos hlt, zero_add]
          · subst heq; rw [if_pos rfl, if_neg (lt_irrefl _), add_zero]
          · rw [if_neg (Nat.ne_of_gt hgt), if_neg (Nat.not_lt.mpr (le_of_lt hgt)), add_zero]
            -- bindWeight e (some j) = 0 for j > |L'|
            change (if _ : j < (Stream'.Seq.ofList (L' ++ [(l, s')])).length _ then _ else 0) = 0
            rw [dif_neg (by rw [length_ofList]; simp; omega)]
        rw [tsum_congr hsplit, ENNReal.tsum_add]
        congr 1
        rw [tsum_eq_single L'.length (fun j hj => if_neg hj)]
        rw [if_pos rfl]]

open Classical in
/-- **Reach (Lemma A).** Running the `bind σ k` scheduler from `pure s₀` produces
the execution `e` with probability equal to the total belief weight `Z(e)`. Proven
by reverse (cons-end) induction on `L`, with `reach_step` as the inductive step.
(Exposed for the σ\* cylinder-monotonicity route, F5b: it turns the normalized-`next`
path measure into the `n`-monotone *unnormalized* belief-weight sum.) -/
theorem reach (σ : Scheduler sys) (k : State → Scheduler sys)
    (s₀ : State) (L : List (Label × State)) :
    (⟨PMF.pure s₀, (bind σ k)⟩ : ProbabilisticExecution sys).probOf
        ⟨s₀, Stream'.Seq.ofList L⟩ (Stream'.Seq.terminates_ofList L)
      = ∑' o, bindWeight σ k ⟨s₀, Stream'.Seq.ofList L⟩ (Stream'.Seq.terminates_ofList L) o := by
  classical
  induction L using List.reverseRecOn with
  | nil =>
    -- LHS = pure s₀ s₀ = 1; RHS = Z(⟨s₀, nil⟩) = 1
    change (⟨PMF.pure s₀, (bind σ k)⟩ : ProbabilisticExecution sys).probOf
        ⟨s₀, Seq.nil⟩ Stream'.Seq.terminates_nil
      = ∑' o, bindWeight σ k ⟨s₀, Seq.nil⟩ Stream'.Seq.terminates_nil o
    rw [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState,
      PMF.pure_apply_self]
    rw [tsum_option_enn (fun o => bindWeight σ k ⟨s₀, Seq.nil⟩ Stream'.Seq.terminates_nil o)]
    rw [show bindWeight σ k ⟨s₀, Seq.nil⟩ Stream'.Seq.terminates_nil none
        = (⟨PMF.pure s₀, σ⟩ : ProbabilisticExecution sys).probOf
            ⟨s₀, Seq.nil⟩ Stream'.Seq.terminates_nil from rfl]
    rw [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState,
      PMF.pure_apply_self]
    rw [show (∑' n, bindWeight σ k ⟨s₀, Seq.nil⟩ Stream'.Seq.terminates_nil (some n)) = 0 from by
      rw [ENNReal.tsum_eq_zero]
      intro n
      change (if _ : n < (Seq.nil : Seq (Label × State)).length Stream'.Seq.terminates_nil
            then _ else 0) = 0
      rw [dif_neg (by rw [Stream'.Seq.length_nil]; omega)]]
    rw [add_zero]
  | append_singleton L' x ih =>
    obtain ⟨l, s'⟩ := x
    -- e.trans = (ofList L').append (cons (l,s') nil)
    have heq : (⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩ : AlterSeq State Label)
        = ⟨s₀, (Stream'.Seq.ofList L').append (Seq.cons (l, s') Seq.nil)⟩ := by
      rw [ofList_append_singleton]
    rw [probOf_congr_eq _ heq _
      (heq ▸ Stream'.Seq.terminates_ofList (L' ++ [(l, s')]))]
    rw [ProbabilisticExecution.probOf_append_singleton _ s₀ (Stream'.Seq.ofList L')
      (Stream'.Seq.terminates_ofList L') (l, s') _]
    rw [ih, reach_step σ k s₀ L' l s']

/-- `actionBot ... none = σ.next e none * (k's halt-step at the end-state)`. -/
private theorem actionBot_none (σ : Scheduler sys) (k : State → Scheduler sys)
    (e : AlterSeq State Label) (hT : e.trans.Terminates) :
    (actionBot σ k e hT) none
      = σ.next e none * (k (e.endState hT)).next ⟨e.endState hT, Seq.nil⟩ none := by
  classical
  unfold actionBot
  rw [PMF.bind_apply, tsum_option_enn]
  rw [show (∑' lμ : Label × PMF State, σ.next e (some lμ)
        * (PMF.pure (some lμ) : PMF (Option (Label × PMF State))) none) = 0 from by
    apply (ENNReal.tsum_eq_zero).mpr
    intro lμ
    rw [PMF.pure_apply, if_neg (by simp), mul_zero]]
  rw [add_zero]

open Classical in
/-- **Halt-unfold (Lemma B).** Scaling `(bind σ k).next e none` (the halt prob) by
the total belief weight `Z(e)` gives the capped sum (over split points `j`) of the
product `σ.haltMass · k.haltMass`. -/
private theorem halt_unfold (σ : Scheduler sys) (k : State → Scheduler sys)
    (e : AlterSeq State Label) (hT : e.trans.Terminates) :
    (∑' o, bindWeight σ k e hT o) * (bind σ k).next e none
      = ∑ j ∈ Finset.range (e.trans.length hT + 1),
          σ.haltMass (PMF.pure e.init)
            ⟨⟨e.init, Stream'.Seq.ofList (e.trans.take j)⟩, Stream'.Seq.terminates_ofList _⟩
          * (k (stateAfter e j)).haltMass (PMF.pure (stateAfter e j))
              ⟨⟨stateAfter e j, e.trans.drop j⟩, drop_terminates hT j⟩ := by
  classical
  set N := e.trans.length hT with hN
  -- the summand function
  set F : ℕ → ENNReal := fun j =>
    σ.haltMass (PMF.pure e.init)
      ⟨⟨e.init, Stream'.Seq.ofList (e.trans.take j)⟩, Stream'.Seq.terminates_ofList _⟩
    * (k (stateAfter e j)).haltMass (PMF.pure (stateAfter e j))
        ⟨⟨stateAfter e j, e.trans.drop j⟩, drop_terminates hT j⟩ with hF
  rw [bind_next_smul]
  rw [tsum_option_enn (fun i => bindWeight σ k e hT i
      * (match i with
          | none => actionBot σ k e hT
          | some j => actionK k e j : PMF (Option (Label × PMF State))) none)]
  -- the `none` term equals F N
  rw [show bindWeight σ k e hT none
        * (actionBot σ k e hT) none = F N from by
      rw [actionBot_none, hF]
      simp only []
      -- prefix at N is `e` itself; stateAfter N = endState; suffix-trans = nil
      have hstateN : stateAfter e N = e.endState hT := by
        rw [hN]; exact stateAfter_length_eq_endState e hT
      have hprefix : (⟨e.init, Stream'.Seq.ofList (e.trans.take N)⟩) = e := by
        rw [show Stream'.Seq.take N e.trans = e.trans.toList hT from rfl,
          Stream'.Seq.ofList_toList]
      have hdropnil : e.trans.drop N = Seq.nil := by
        apply Stream'.Seq.ext
        intro m
        rw [Stream'.Seq.drop_get?, Stream'.Seq.get?_nil]
        exact Stream'.Seq.terminated_stable e.trans (Nat.le_add_right N m) (Nat.find_spec hT)
      -- rewrite the haltMass factors
      rw [haltMass_congr_eq σ (PMF.pure e.init)
        (e₁ := ⟨⟨e.init, Stream'.Seq.ofList (e.trans.take N)⟩, Stream'.Seq.terminates_ofList _⟩)
        (e₂ := ⟨e, hT⟩) hprefix]
      rw [hstateN]
      -- (k endState).haltMass (pure endState) ⟨⟨endState, nil⟩, _⟩
      rw [haltMass_congr_eq (k (e.endState hT)) (PMF.pure (e.endState hT))
        (e₁ := ⟨⟨e.endState hT, e.trans.drop N⟩, drop_terminates hT N⟩)
        (e₂ := ⟨⟨e.endState hT, Seq.nil⟩, Stream'.Seq.terminates_nil⟩)
        (by simp only; rw [hdropnil])]
      -- expand both haltMass and probOf_nil = 1
      change (⟨PMF.pure e.init, σ⟩ : ProbabilisticExecution sys).probOf e hT
          * (σ.next e none * (k (e.endState hT)).next ⟨e.endState hT, Seq.nil⟩ none)
        = ((⟨PMF.pure e.init, σ⟩ : ProbabilisticExecution sys).probOf e hT
            * σ.next e none)
          * ((⟨PMF.pure (e.endState hT), (k (e.endState hT))⟩
                : ProbabilisticExecution sys).probOf ⟨e.endState hT, Seq.nil⟩
                Stream'.Seq.terminates_nil
              * (k (e.endState hT)).next ⟨e.endState hT, Seq.nil⟩ none)
      rw [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState,
        PMF.pure_apply_self, one_mul]
      ring]
  -- the `some j` terms
  rw [show (∑' j, bindWeight σ k e hT (some j) * (actionK k e j) none)
      = ∑' j, (if j < N then F j else 0) from by
      apply tsum_congr; intro j
      by_cases hj : j < N
      · rw [if_pos hj, hF]
        simp only []
        -- unfold bindWeight (some j) via dif_pos
        rw [show bindWeight σ k e hT (some j)
            = σ.haltMass (PMF.pure e.init)
                ⟨⟨e.init, Stream'.Seq.ofList (e.trans.take j)⟩, Stream'.Seq.terminates_ofList _⟩
              * (⟨PMF.pure (stateAfter e j), (k (stateAfter e j))⟩
                  : ProbabilisticExecution sys).probOf
                  ⟨stateAfter e j, e.trans.drop j⟩ (drop_terminates hT j) from by
          change (if _ : j < e.trans.length hT then _ else 0) = _
          rw [dif_pos (by rw [← hN]; exact hj)]]
        -- actionK none and haltMass of suffix
        change σ.haltMass (PMF.pure e.init)
              ⟨⟨e.init, Stream'.Seq.ofList (e.trans.take j)⟩, Stream'.Seq.terminates_ofList _⟩
            * (⟨PMF.pure (stateAfter e j), (k (stateAfter e j))⟩
                : ProbabilisticExecution sys).probOf
                ⟨stateAfter e j, e.trans.drop j⟩ (drop_terminates hT j)
            * (k (stateAfter e j)).next ⟨stateAfter e j, e.trans.drop j⟩ none
          = σ.haltMass (PMF.pure e.init)
              ⟨⟨e.init, Stream'.Seq.ofList (e.trans.take j)⟩, Stream'.Seq.terminates_ofList _⟩
            * (k (stateAfter e j)).haltMass (PMF.pure (stateAfter e j))
                ⟨⟨stateAfter e j, e.trans.drop j⟩, drop_terminates hT j⟩
        rw [show (k (stateAfter e j)).haltMass (PMF.pure (stateAfter e j))
              ⟨⟨stateAfter e j, e.trans.drop j⟩, drop_terminates hT j⟩
            = (⟨PMF.pure (stateAfter e j), (k (stateAfter e j))⟩
                : ProbabilisticExecution sys).probOf
                ⟨stateAfter e j, e.trans.drop j⟩ (drop_terminates hT j)
              * (k (stateAfter e j)).next ⟨stateAfter e j, e.trans.drop j⟩ none from rfl]
        ring
      · rw [if_neg hj]
        rw [show bindWeight σ k e hT (some j) = 0 from by
          change (if _ : j < e.trans.length hT then _ else 0) = 0
          rw [dif_neg (by rw [← hN]; exact hj)]]
        rw [zero_mul]]
  -- convert tsum to Finset.sum and reassemble
  rw [Finset.sum_range_succ]
  rw [add_comm]
  congr 1
  rw [show (∑' j, (if j < N then F j else 0)) = ∑ j ∈ Finset.range N, F j from by
    rw [tsum_eq_sum (s := Finset.range N) (fun j hj => if_neg (by
      rw [Finset.mem_range] at hj; omega))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [if_pos hj]]

/-- `bindWeight` only depends on the underlying `AlterSeq`. -/
private theorem bindWeight_congr_eq (σ : Scheduler sys)
    (k : State → Scheduler sys)
    {e₁ e₂ : AlterSeq State Label} (heq : e₁ = e₂)
    {h₁ : e₁.trans.Terminates} {h₂ : e₂.trans.Terminates} (o : Option ℕ) :
    bindWeight σ k e₁ h₁ o = bindWeight σ k e₂ h₂ o := by
  subst heq; rfl

/-- `haltMass` factors through the source mass on the start state: `μ_init s₀` times
the Dirac-source halt mass equals the `μ_init`-source halt mass (the source only
enters through the initial state). -/
private theorem haltMass_pure_smul (σ : Scheduler sys) (μ_init : PMF State)
    (s₀ : State) (t : Seq (Label × State)) (h : t.Terminates) :
    μ_init s₀ * σ.haltMass (PMF.pure s₀) ⟨⟨s₀, t⟩, h⟩
      = σ.haltMass μ_init ⟨⟨s₀, t⟩, h⟩ := by
  change μ_init s₀ * ((⟨PMF.pure s₀, σ⟩
        : ProbabilisticExecution sys).probOf ⟨s₀, t⟩ h * σ.next ⟨s₀, t⟩ none)
    = (⟨μ_init, σ⟩ : ProbabilisticExecution sys).probOf ⟨s₀, t⟩ h
      * σ.next ⟨s₀, t⟩ none
  rw [ProbabilisticExecution.probOf_init_factor σ μ_init ⟨s₀, t⟩ h]
  change μ_init s₀ * ((⟨PMF.pure s₀, σ⟩
        : ProbabilisticExecution sys).probOf ⟨s₀, t⟩ h * σ.next ⟨s₀, t⟩ none)
    = μ_init s₀ * (⟨PMF.pure s₀, σ⟩
        : ProbabilisticExecution sys).probOf ⟨s₀, t⟩ h * σ.next ⟨s₀, t⟩ none
  ring

open Classical in
/-- **Correctness of `bind`** (the chain-rule / belief telescoping): the halting
mass of `bind σ k` from `μ_init` is the convolution over the split point: it sums,
over the split point `j` (number of steps before σ hands off to `k`), the product
of σ's halt mass on the `j`-prefix and `k`'s halt mass on the suffix. -/
theorem bind_haltMass (σ : Scheduler sys) (k : State → Scheduler sys)
    (μ_init : PMF State) (e : {e : AlterSeq State Label // e.trans.Terminates}) :
    (bind σ k).haltMass μ_init e
      = ∑ j ∈ Finset.range (e.1.trans.length e.2 + 1),
          σ.haltMass μ_init
            ⟨⟨e.1.init, Seq.ofList (e.1.trans.take j)⟩, Stream'.Seq.terminates_ofList _⟩
          * (k (stateAfter e.1 j)).haltMass (PMF.pure (stateAfter e.1 j))
              ⟨⟨stateAfter e.1 j, e.1.trans.drop j⟩, drop_terminates e.2 j⟩ := by
  classical
  obtain ⟨e, hT⟩ := e
  -- e = ⟨e.init, ofList (toList)⟩
  have heofL : (⟨e.init, Stream'.Seq.ofList (e.trans.toList hT)⟩ : AlterSeq State Label) = e := by
    rw [Stream'.Seq.ofList_toList]
  -- unfold haltMass and factor the source mass
  change (⟨μ_init, (bind σ k)⟩ : ProbabilisticExecution sys).probOf e hT
      * (bind σ k).next e none = _
  rw [ProbabilisticExecution.probOf_init_factor (bind σ k) μ_init e hT]
  -- probOf ⟨pure e.init, bind⟩ e = reach
  rw [show (⟨PMF.pure e.init, (bind σ k)⟩
        : ProbabilisticExecution sys).probOf e hT
      = ∑' o, bindWeight σ k e hT o from by
    rw [probOf_congr_eq (⟨PMF.pure e.init, (bind σ k)⟩
        : ProbabilisticExecution sys) heofL.symm hT
      (Stream'.Seq.terminates_ofList _)]
    rw [reach σ k e.init (e.trans.toList hT)]
    apply tsum_congr
    intro o
    exact bindWeight_congr_eq σ k heofL o]
  -- Z(e) * bind.next e none = capped sum via halt_unfold
  rw [mul_assoc, halt_unfold σ k e hT]
  -- push μ_init e.init into the sum, fold via haltMass_pure_smul
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← mul_assoc]
  rw [haltMass_pure_smul σ μ_init e.init (Stream'.Seq.ofList (e.trans.take j))
    (Stream'.Seq.terminates_ofList _)]

end Scheduler

namespace WeakScheduler

variable {sys : System State Label}

/-- The **halting mass** of a weak scheduler `σ` from source `μ_init`, at a
terminating finite execution `e`: the `Scheduler`-level halting mass of its
underlying scheduler. -/
noncomputable def haltMass (σ : WeakScheduler sys) (μ_init : PMF State)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) : ENNReal :=
  Scheduler.haltMass σ.toScheduler μ_init e

/-- **`haltMass` is linear in the source distribution.** Wrapper over
`Scheduler.haltMass_init_mix`. -/
theorem haltMass_init_mix (σ : WeakScheduler sys) (μ_init : PMF State)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) :
    σ.haltMass μ_init e = ∑' s, μ_init s * σ.haltMass (PMF.pure s) e :=
  Scheduler.haltMass_init_mix σ.toScheduler μ_init e

/-- `haltMass` only depends on the underlying `AlterSeq`. Wrapper over
`Scheduler.haltMass_congr_eq`. -/
theorem haltMass_congr_eq (σ : WeakScheduler sys) (μ : PMF State)
    {e₁ e₂ : {e : AlterSeq State Label // e.trans.Terminates}}
    (heq : e₁.1 = e₂.1) :
    σ.haltMass μ e₁ = σ.haltMass μ e₂ :=
  Scheduler.haltMass_congr_eq σ.toScheduler μ heq

open Classical in
/-- **Sequential composition** of weak schedulers: `bind σ k` runs `σ` from the
start and, at `σ`'s almost-sure halt at state `s`, switches to `k s`. Its
underlying scheduler is `Scheduler.bind`; the extra `internal_only` field records
that every emission is internal (inherited from `σ` and `k`). -/
noncomputable def bind (σ : WeakScheduler sys) (k : State → WeakScheduler sys) :
    WeakScheduler sys where
  toScheduler := Scheduler.bind σ.toScheduler (fun s => (k s).toScheduler)
  internal_only := by
    classical
    intro e l μ h_supp
    set σ' : Scheduler sys := σ.toScheduler with hσ'
    set k' : State → Scheduler sys := fun s => (k s).toScheduler with hk'
    by_cases hT : e.trans.Terminates
    · change some (l, μ) ∈
        (if hT' : e.trans.Terminates then
          if h0 : ∑' (o : Option ℕ), σ'.bindWeight k' e hT' o ≠ 0 then
            (PMF.normalize (σ'.bindWeight k' e hT') h0 _).bind fun o =>
              match o with
              | none => σ'.actionBot k' e hT'
              | some j => Scheduler.actionK k' e j
          else PMF.pure none
        else PMF.pure none).support at h_supp
      rw [dif_pos hT] at h_supp
      by_cases h0 : ∑' (o : Option ℕ), σ'.bindWeight k' e hT o ≠ 0
      · rw [dif_pos h0, PMF.mem_support_bind_iff] at h_supp
        obtain ⟨o, _, h_supp⟩ := h_supp
        cases o with
        | none =>
          change some (l, μ) ∈ (σ'.actionBot k' e hT).support at h_supp
          unfold Scheduler.actionBot at h_supp
          rw [PMF.mem_support_bind_iff] at h_supp
          obtain ⟨o', ho'_mem, h_supp⟩ := h_supp
          cases o' with
          | none =>
            change some (l, μ) ∈ ((k (e.endState hT)).next
              ⟨e.endState hT, Seq.nil⟩).support at h_supp
            exact (k (e.endState hT)).internal_only ⟨e.endState hT, Seq.nil⟩ l μ h_supp
          | some lμ' =>
            change some (l, μ) ∈ (PMF.pure (some lμ')).support at h_supp
            rw [PMF.mem_support_pure_iff] at h_supp
            have : lμ' = (l, μ) := (Option.some.inj h_supp).symm
            subst this
            exact σ.internal_only e l μ ho'_mem
        | some j =>
          change some (l, μ) ∈ (Scheduler.actionK k' e j).support at h_supp
          unfold Scheduler.actionK at h_supp
          exact (k (stateAfter e j)).internal_only ⟨stateAfter e j, e.trans.drop j⟩ l μ h_supp
      · rw [dif_neg h0] at h_supp
        change some (l, μ) ∈ (PMF.pure (α := Option (Label × PMF State)) none).support at h_supp
        rw [PMF.mem_support_pure_iff] at h_supp
        exact absurd h_supp (by simp)
    · change some (l, μ) ∈
        (if hT' : e.trans.Terminates then _ else
          PMF.pure (α := Option (Label × PMF State)) none).support at h_supp
      rw [dif_neg hT] at h_supp
      rw [PMF.mem_support_pure_iff] at h_supp
      exact absurd h_supp (by simp)

/-- **Correctness of `bind`.** Wrapper over `Scheduler.bind_haltMass`. -/
theorem bind_haltMass (σ : WeakScheduler sys) (k : State → WeakScheduler sys)
    (μ_init : PMF State) (e : {e : AlterSeq State Label // e.trans.Terminates}) :
    (bind σ k).haltMass μ_init e
      = ∑ j ∈ Finset.range (e.1.trans.length e.2 + 1),
          σ.haltMass μ_init
            ⟨⟨e.1.init, Seq.ofList (e.1.trans.take j)⟩, Stream'.Seq.terminates_ofList _⟩
          * (k (stateAfter e.1 j)).haltMass (PMF.pure (stateAfter e.1 j))
              ⟨⟨stateAfter e.1 j, e.1.trans.drop j⟩, drop_terminates e.2 j⟩ :=
  Scheduler.bind_haltMass σ.toScheduler (fun s => (k s).toScheduler) μ_init e

end WeakScheduler

end PLTS
