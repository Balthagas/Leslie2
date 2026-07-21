/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Systems.Trace

/-!
# From trace-distribution support to genuine executions

The bridge between `traceProb` positivity and execution-level reasoning, used
to prove safety properties of every trace in the support of an achievable
trace distribution:

* `ProbabilisticExecution.exists_step_of_kernel_ne_zero` — a non-vanishing
  one-step kernel exhibits a scheduler-supported transition.
* `is_exec_of_probOf_ne_zero` — a positive-probability finite execution of a
  Dirac-initialised probabilistic execution is a genuine execution (`is_exec`)
  of the system.
* `exists_exec_of_traceProb_ne_zero` — a trace with positive `traceProb` is
  the trace of a genuine execution `e`, and membership in the trace is fully
  characterised by the labelled events of `e`.
* `is_exec_induction` / `is_exec_induction_labels` — invariant induction along
  genuine executions (state-only, and label-history-aware).
* `is_exec_stable` — a step-stable predicate propagates forward along a
  genuine execution.
* `safety_transfer` — trace-support safety transfers along
  `achievableTraceDists ⊆`.
-/

open Stream'

namespace PLTS

variable {State Label : Type}

/-! ### Prefix-execution glue for `ofList` executions -/

namespace AlterSeq

/-- The end state of the finite transition list `L` started at `s₀`: the second
component of the last transition, or `s₀` if there is none. -/
def endStList (s₀ : State) (L : List (Label × State)) : State :=
  (L.getLast?).elim s₀ Prod.snd

@[simp] theorem endStList_nil (s₀ : State) :
    endStList s₀ ([] : List (Label × State)) = s₀ := rfl

theorem endStList_concat (s₀ : State) (M : List (Label × State)) (a : Label × State) :
    endStList s₀ (M ++ [a]) = a.2 := by
  simp [endStList]

/-- `Seq.ofList L` is terminated at `L.length`. -/
theorem ofList_terminatedAt_length (L : List (Label × State)) :
    (Seq.ofList L).TerminatedAt L.length := by
  show (Seq.ofList L).get? L.length = none
  rw [Seq.ofList_get?]
  simp

/-- The state after all of `⟨s₀, ofList L⟩`'s transitions is `endStList s₀ L`. -/
theorem stateAt_ofList_length (s₀ : State) (L : List (Label × State)) :
    (⟨s₀, Seq.ofList L⟩ : AlterSeq State Label).stateAt L.length
      = some (endStList s₀ L) := by
  rcases List.eq_nil_or_concat L with rfl | ⟨M, a, rfl⟩
  · rfl
  · simp only [List.concat_eq_append]
    have hlen : (M ++ [a]).length = M.length + 1 := by simp
    rw [hlen]
    show ((Seq.ofList (M ++ [a])).get? M.length).map Prod.snd = _
    rw [Seq.ofList_get?]
    simp [endStList_concat]

/-- `stateAt` of an `ofList (M ++ K)` execution agrees with the `ofList M`
execution on positions `≤ M.length`. -/
theorem stateAt_ofList_append_le (s₀ : State) (M K : List (Label × State))
    {n : ℕ} (h : n ≤ M.length) :
    (⟨s₀, Seq.ofList (M ++ K)⟩ : AlterSeq State Label).stateAt n
      = (⟨s₀, Seq.ofList M⟩ : AlterSeq State Label).stateAt n := by
  cases n with
  | zero => rfl
  | succ k =>
    show ((Seq.ofList (M ++ K)).get? k).map Prod.snd
        = ((Seq.ofList M).get? k).map Prod.snd
    rw [Seq.ofList_get?, Seq.ofList_get?, List.getElem?_append_left (by omega)]

end AlterSeq

/-! ### From `probOf` positivity to genuine executions -/

/-- A non-vanishing one-step kernel exhibits a scheduler-supported successor
distribution containing the target state. -/
theorem ProbabilisticExecution.exists_step_of_kernel_ne_zero
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (l : Label) (s' : State)
    (h : pe.kernel e (l, s') ≠ 0) :
    ∃ μ, some (l, μ) ∈ (pe.scheduler.next e).support ∧ s' ∈ μ.support := by
  by_contra hc
  push_neg at hc
  refine h (ENNReal.tsum_eq_zero.mpr fun μ => ?_)
  by_cases hμ : some (l, μ) ∈ (pe.scheduler.next e).support
  · have := hc μ hμ
    rw [PMF.mem_support_iff, not_not] at this
    rw [this, mul_zero]
  · rw [PMF.mem_support_iff, not_not] at hμ
    rw [hμ, zero_mul]

/-- A positive-probability `ofList` execution is a partial execution of the
system: every transition is scheduler-supported, hence (`Scheduler.valid`) a
genuine `sys.step` from the state reached so far. -/
theorem is_partial_exec_of_probOf_ofList_ne_zero
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (s₀ : State) (L : List (Label × State))
    (h : pe.probOf ⟨s₀, Seq.ofList L⟩ (Seq.terminates_ofList L) ≠ 0) :
    is_partial_exec (⟨s₀, Seq.ofList L⟩ : AlterSeq State Label) sys := by
  induction L using List.reverseRecOn with
  | nil =>
    intro n l s' hget
    rw [show (⟨s₀, Seq.ofList []⟩ : AlterSeq State Label).trans = Seq.nil from by
      rw [Seq.ofList_nil]] at hget
    simp [Seq.get?_nil] at hget
  | append_singleton M a ih =>
    -- Split the probability into the `M`-prefix probability and the last kernel.
    have h_split : Seq.ofList (M ++ [a]) =
        (Seq.ofList M).append (Seq.cons a Seq.nil) := by
      rw [Seq.ofList_append, Seq.ofList_cons, Seq.ofList_nil]
    have h_factor := pe.probOf_append_singleton s₀ (Seq.ofList M)
      (Seq.terminates_ofList M) a
      (h_split ▸ Seq.terminates_ofList (M ++ [a]))
    have h_ne : pe.probOf ⟨s₀, Seq.ofList (M ++ [a])⟩ (Seq.terminates_ofList _) ≠ 0 := h
    rw [pe.probOf_congr ⟨s₀, Seq.ofList (M ++ [a])⟩
        ⟨s₀, (Seq.ofList M).append (Seq.cons a Seq.nil)⟩ (by rw [h_split])
        (Seq.terminates_ofList _) (h_split ▸ Seq.terminates_ofList (M ++ [a])),
      h_factor] at h_ne
    have h_pre : pe.probOf ⟨s₀, Seq.ofList M⟩ (Seq.terminates_ofList M) ≠ 0 :=
      fun h0 => h_ne (by rw [h0, zero_mul])
    have h_ker : pe.kernel ⟨s₀, Seq.ofList M⟩ a ≠ 0 :=
      fun h0 => h_ne (by rw [h0, mul_zero])
    have ih' := ih h_pre
    -- The last transition is a genuine step from the end state of the prefix.
    obtain ⟨μ, h_supp, h_s'⟩ :=
      pe.exists_step_of_kernel_ne_zero ⟨s₀, Seq.ofList M⟩ a.1 a.2 (by
        rcases a with ⟨l, s'⟩; exact h_ker)
    have h_step : sys.step (AlterSeq.endStList s₀ M) a.1 μ :=
      pe.scheduler.valid ⟨s₀, Seq.ofList M⟩ M.length (AlterSeq.endStList s₀ M)
        (AlterSeq.ofList_terminatedAt_length M)
        (AlterSeq.stateAt_ofList_length s₀ M) a.1 μ h_supp
    -- Assemble `is_partial_exec` for the extended execution.
    intro n l s' hget
    rw [show (⟨s₀, Seq.ofList (M ++ [a])⟩ : AlterSeq State Label).trans
        = Seq.ofList (M ++ [a]) from rfl, Seq.ofList_get?] at hget
    have h_lt : n < M.length + 1 := by
      by_contra hc
      rw [List.getElem?_eq_none (by simp; omega)] at hget
      exact absurd hget (by simp)
    rcases Nat.lt_succ_iff_lt_or_eq.mp h_lt with h_n | rfl
    · -- Position inside the prefix: reuse `ih'`.
      have hget_M : (⟨s₀, Seq.ofList M⟩ : AlterSeq State Label).trans.get? n
          = some (l, s') := by
        show (Seq.ofList M).get? n = some (l, s')
        rw [Seq.ofList_get?]
        rw [List.getElem?_append_left h_n] at hget
        exact hget
      obtain ⟨s, μ', h_state, h_step', h_supp'⟩ := ih' n l s' hget_M
      exact ⟨s, μ', by
        rw [AlterSeq.stateAt_ofList_append_le s₀ M [a] (by omega)]
        exact h_state, h_step', h_supp'⟩
    · -- The appended position: the step established above.
      rw [List.getElem?_concat_length] at hget
      obtain ⟨rfl, rfl⟩ : a.1 = l ∧ a.2 = s' := by
        have := Option.some.inj hget
        exact ⟨congr_arg Prod.fst this, congr_arg Prod.snd this⟩
      exact ⟨AlterSeq.endStList s₀ M, μ, by
        rw [AlterSeq.stateAt_ofList_append_le s₀ M [a] (le_refl _)]
        exact AlterSeq.stateAt_ofList_length s₀ M, h_step, h_s'⟩

/-- **A positive-probability finite execution of a Dirac-initialised
probabilistic execution is a genuine execution of the system.** -/
theorem is_exec_of_probOf_ne_zero
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (hinit : pe.initState = PMF.pure sys.init)
    (e : AlterSeq State Label) (hFin : e.trans.Terminates)
    (h : pe.probOf e hFin ≠ 0) :
    is_exec e sys := by
  obtain ⟨s₀, tr⟩ := e
  have h_ofList : Seq.ofList (tr.toList hFin) = tr := Seq.ofList_toList tr hFin
  constructor
  · -- partial-execution component, transported from the `ofList` form
    have h_ne : pe.probOf ⟨s₀, Seq.ofList (tr.toList hFin)⟩
        (Seq.terminates_ofList _) ≠ 0 := by
      rw [pe.probOf_congr ⟨s₀, Seq.ofList (tr.toList hFin)⟩ ⟨s₀, tr⟩
        (by rw [h_ofList]) (Seq.terminates_ofList _) hFin]
      exact h
    have := is_partial_exec_of_probOf_ofList_ne_zero pe s₀ (tr.toList hFin) h_ne
    rwa [show (⟨s₀, Seq.ofList (tr.toList hFin)⟩ : AlterSeq State Label)
        = ⟨s₀, tr⟩ from by rw [h_ofList]] at this
  · -- initial-state component: positive mass under a Dirac init pins the start.
    have h_init_ne : pe.init s₀ ≠ 0 := by
      intro h0
      exact h (le_antisymm (h0 ▸ pe.probOf_le_init ⟨s₀, tr⟩ hFin) bot_le)
    rw [pe.init_eq_initState, hinit] at h_init_ne
    by_contra h_ne
    exact h_init_ne (PMF.pure_apply_of_ne _ _ (Ne.symm h_ne))

/-! ### From `traceProb` positivity to executions with a trace-membership
characterisation -/

/-- Membership in `Seq.ofList` is list membership. -/
theorem Seq_mem_ofList {α : Type} {a : α} {L : List α} :
    a ∈ Seq.ofList L ↔ a ∈ L := by
  rw [Seq.mem_iff_exists_get?, List.mem_iff_getElem?]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, by rw [← Seq.ofList_get?]; exact hi.symm⟩
  · rintro ⟨i, hi⟩; exact ⟨i, by rw [Seq.ofList_get?]; exact hi.symm⟩

variable [Silent Label]

open Classical in
/-- **A trace with positive `traceProb` (from a Dirac init) is the trace of a
genuine execution, and its members are exactly the external labels of that
execution's events.** -/
theorem exists_exec_of_traceProb_ne_zero
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (hinit : pe.initState = PMF.pure sys.init)
    (t : Seq Label) (h : sys.traceProb pe t ≠ 0) :
    ∃ e : AlterSeq State Label, is_exec e sys ∧
      (∀ l : Label, l ∈ t ↔ (¬ l = Silent.τ) ∧ ∃ k s', e.trans.get? k = some (l, s')) := by
  -- Regroup by label list and extract a nonzero group.
  rw [sys.traceProb_eq_labProb_sum pe t] at h
  obtain ⟨labs, h_labs⟩ : ∃ labs : List Label, _ ≠ (0 : ENNReal) := by
    by_contra hc
    push_neg at hc
    exact h (ENNReal.tsum_eq_zero.mpr hc)
  have h_tt : sys.traceTightLabs t labs := by
    by_contra hc
    rw [if_neg hc] at h_labs
    exact h_labs rfl
  rw [if_pos h_tt] at h_labs
  obtain ⟨e, h_e⟩ : ∃ e : AlterSeq State Label, _ ≠ (0 : ENNReal) := by
    by_contra hc
    push_neg at hc
    exact h_labs (ENNReal.tsum_eq_zero.mpr hc)
  by_cases h_cond : e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs
  swap
  · rw [dif_neg h_cond] at h_e; exact absurd rfl h_e
  rw [dif_pos h_cond] at h_e
  obtain ⟨hFin, h_map⟩ := h_cond
  refine ⟨e, is_exec_of_probOf_ne_zero pe hinit e hFin h_e, fun l => ?_⟩
  -- The trace is the filtered label list; membership reduces to list membership.
  have h_t := h_tt.1
  rw [Seq.ofList_filter] at h_t
  constructor
  · intro h_mem
    rw [← h_t, Seq_mem_ofList, List.mem_filter] at h_mem
    obtain ⟨h_mem, h_ext⟩ := h_mem
    refine ⟨by simpa using h_ext, ?_⟩
    -- From `l ∈ labs` to an event of `e`.
    rw [List.mem_iff_getElem?] at h_mem
    obtain ⟨k, hk⟩ := h_mem
    have h_get_eq : (e.trans.map Prod.fst).get? k = (Seq.ofList labs).get? k := by
      rw [h_map]
    rw [Seq.map_get?, Seq.ofList_get?, hk] at h_get_eq
    cases hg : e.trans.get? k with
    | none => rw [hg] at h_get_eq; exact absurd h_get_eq (by simp)
    | some p =>
      rw [hg] at h_get_eq
      simp only [Option.map_some, Option.some.injEq] at h_get_eq
      exact ⟨k, p.2, by rw [hg, ← h_get_eq]⟩
  · rintro ⟨h_ext, k, s', h_get⟩
    rw [← h_t, Seq_mem_ofList, List.mem_filter]
    have h_get_eq : (e.trans.map Prod.fst).get? k = (Seq.ofList labs).get? k := by
      rw [h_map]
    rw [Seq.map_get?, Seq.ofList_get?, h_get] at h_get_eq
    refine ⟨List.mem_iff_getElem?.mpr ⟨k, h_get_eq.symm⟩, by simpa using h_ext⟩

/-! ### Invariant induction along genuine executions -/

section Induction

variable {sys : System State Label}

omit [Silent Label] in
/-- **State-invariant induction.** A predicate holding initially and preserved
by every step holds at every reached state of a genuine execution. -/
theorem is_exec_induction (I : State → Prop)
    (hinit : I sys.init)
    (hstep : ∀ s l μ s', I s → sys.step s l μ → s' ∈ μ.support → I s')
    {e : AlterSeq State Label} (he : is_exec e sys) :
    ∀ n s, e.stateAt n = some s → I s := by
  intro n
  induction n with
  | zero =>
    intro s hs
    obtain rfl : e.init = s := Option.some.inj hs
    exact he.2 ▸ hinit
  | succ k ih =>
    intro s hs
    obtain ⟨⟨l, s'⟩, h_get, h_snd⟩ : ∃ p : Label × State,
        e.trans.get? k = some p ∧ p.2 = s := by
      cases hg : e.trans.get? k with
      | none =>
        rw [show e.stateAt (k+1) = (e.trans.get? k).map Prod.snd from rfl, hg] at hs
        exact absurd hs (by simp)
      | some p =>
        rw [show e.stateAt (k+1) = (e.trans.get? k).map Prod.snd from rfl, hg] at hs
        exact ⟨p, rfl, Option.some.inj hs⟩
    obtain ⟨s₀, μ, h_state, h_step, h_supp⟩ := he.1 k l s' h_get
    exact h_snd ▸ hstep s₀ l μ s' (ih s₀ h_state) h_step h_supp

omit [Silent Label] in
/-- **Forward stability.** A step-stable predicate propagates from any reached
state to every later reached state of a genuine execution. -/
theorem is_exec_stable (P : State → Prop)
    (hstep : ∀ s l μ s', P s → sys.step s l μ → s' ∈ μ.support → P s')
    {e : AlterSeq State Label} (he : is_exec e sys) :
    ∀ m n s s', m ≤ n → e.stateAt m = some s → e.stateAt n = some s' →
      P s → P s' := by
  intro m n
  induction n with
  | zero =>
    intro s s' hmn hm hn hP
    obtain rfl : m = 0 := Nat.le_zero.mp hmn
    rw [hm] at hn
    exact (Option.some.inj hn) ▸ hP
  | succ k ih =>
    intro s s' hmn hm hn hP
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with h_lt | rfl
    · -- m ≤ k: step from position k.
      obtain ⟨⟨l, s''⟩, h_get, h_snd⟩ : ∃ p : Label × State,
          e.trans.get? k = some p ∧ p.2 = s' := by
        cases hg : e.trans.get? k with
        | none =>
          rw [show e.stateAt (k+1) = (e.trans.get? k).map Prod.snd from rfl, hg] at hn
          exact absurd hn (by simp)
        | some p =>
          rw [show e.stateAt (k+1) = (e.trans.get? k).map Prod.snd from rfl, hg] at hn
          exact ⟨p, rfl, Option.some.inj hn⟩
      obtain ⟨s₀, μ, h_state, h_step, h_supp⟩ := he.1 k l s'' h_get
      have hPk : P s₀ := ih s s₀ (by omega) hm h_state hP
      exact h_snd ▸ hstep s₀ l μ s'' hPk h_step h_supp
    · rw [hm] at hn
      exact (Option.some.inj hn) ▸ hP

/-- The labels of the first `n` transitions of an execution. -/
def AlterSeq.labelsUpTo (e : AlterSeq State Label) : ℕ → List Label
  | 0 => []
  | n + 1 => e.labelsUpTo n ++ ((e.trans.get? n).map Prod.fst).toList

omit [Silent Label] in
/-- Every label in `labelsUpTo e n` is the label of an event of `e` (before
position `n`). -/
theorem AlterSeq.mem_labelsUpTo {e : AlterSeq State Label} {l : Label} :
    ∀ {n : ℕ}, l ∈ e.labelsUpTo n → ∃ k, k < n ∧ ∃ s', e.trans.get? k = some (l, s') := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (List.not_mem_nil)
  | succ k ih =>
    intro h
    rcases List.mem_append.mp h with h_pre | h_last
    · obtain ⟨k', hk', hs⟩ := ih h_pre
      exact ⟨k', by omega, hs⟩
    · cases hg : e.trans.get? k with
      | none =>
        rw [hg] at h_last
        simp at h_last
      | some p =>
        rw [hg] at h_last
        simp only [Option.map_some, Option.toList_some, List.mem_singleton] at h_last
        exact ⟨k, by omega, p.2, by rw [hg, h_last]⟩

omit [Silent Label] in
/-- **Label-history-aware invariant induction.** An invariant over (seen
labels, current state) holding initially and preserved by every step holds,
at every position `n`, of the labels seen so far and the state reached. -/
theorem is_exec_induction_labels (I : List Label → State → Prop)
    (hinit : I [] sys.init)
    (hstep : ∀ pre s l μ s', I pre s → sys.step s l μ → s' ∈ μ.support →
      I (pre ++ [l]) s')
    {e : AlterSeq State Label} (he : is_exec e sys) :
    ∀ n s, e.stateAt n = some s → I (e.labelsUpTo n) s := by
  intro n
  induction n with
  | zero =>
    intro s hs
    obtain rfl : e.init = s := Option.some.inj hs
    exact he.2 ▸ hinit
  | succ k ih =>
    intro s hs
    obtain ⟨⟨l, s'⟩, h_get, h_snd⟩ : ∃ p : Label × State,
        e.trans.get? k = some p ∧ p.2 = s := by
      cases hg : e.trans.get? k with
      | none =>
        rw [show e.stateAt (k+1) = (e.trans.get? k).map Prod.snd from rfl, hg] at hs
        exact absurd hs (by simp)
      | some p =>
        rw [show e.stateAt (k+1) = (e.trans.get? k).map Prod.snd from rfl, hg] at hs
        exact ⟨p, rfl, Option.some.inj hs⟩
    obtain ⟨s₀, μ, h_state, h_step, h_supp⟩ := he.1 k l s' h_get
    have h_labels : e.labelsUpTo (k + 1) = e.labelsUpTo k ++ [l] := by
      rw [AlterSeq.labelsUpTo, h_get]
      rfl
    rw [h_labels]
    exact h_snd ▸ hstep (e.labelsUpTo k) s₀ l μ s' (ih s₀ h_state) h_step h_supp

end Induction

/-! ### Safety transfer along trace-distribution inclusion -/

/-- **Safety transfer.** If every positive-mass trace of every achievable
trace distribution of `sysA` satisfies `Pr`, and `sysC`'s achievable trace
distributions are included in `sysA`'s, then the same holds for `sysC`. -/
theorem safety_transfer {State_C State_A : Type}
    {sysC : System State_C Label} {sysA : System State_A Label}
    (h : achievableTraceDists sysC ⊆ achievableTraceDists sysA)
    {Pr : Seq Label → Prop}
    (hA : ∀ D ∈ achievableTraceDists sysA, ∀ t, D t ≠ 0 → Pr t) :
    ∀ D ∈ achievableTraceDists sysC, ∀ t, D t ≠ 0 → Pr t :=
  fun D hD => hA D (h hD)

end PLTS
