/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Seq.Defs
import Mathlib.Data.Seq.Basic
import MyMathlibProject.SeqHelper

/-!
# Probabilistic Labelled Transition System (PLTS)

PLTS are the basic model used to represent protocols.
-/

open Stream'

namespace PLTS

structure System (State : Type) (Label : Type) where
  /-- The unique initial state of the system. -/
  init : State
  step : State → Label → PMF State → Prop

/-- An alternating sequence of states and labels: an initial state followed by a
possibly infinite sequence of `(label, next state)` transitions. -/
structure AlterSeq (State : Type) (Label : Type) where
  init : State
  trans : Seq (Label × State)

namespace AlterSeq

variable {State : Type} {Label : Type}

/-- The state reached after `n` transitions: position `0` is the initial state,
position `n + 1` is the destination of the `n`-th transition (or `none` if the
sequence has already terminated). -/
def stateAt (e : AlterSeq State Label) : ℕ → Option State
  | 0     => some e.init
  | n + 1 => (e.trans.get? n).map Prod.snd

/-- At the canonical terminating position `Nat.find h`, the state is defined. -/
lemma stateAt_find_isSome (e : AlterSeq State Label) (h : e.trans.Terminates) :
    (e.stateAt (Nat.find h)).isSome := by
  rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | hpos
  · rw [h0]; rfl
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hNotT : ¬ e.trans.TerminatedAt k :=
      Nat.find_min h (by rw [hk]; exact Nat.lt_succ_self k)
    rw [hk]
    change ((e.trans.get? k).map Prod.snd).isSome
    rw [Option.isSome_map]
    exact Option.isSome_iff_ne_none.mpr hNotT

lemma exists_endpoint (e : AlterSeq State Label) (h : e.trans.Terminates) :
    ∃ n s, e.trans.TerminatedAt n ∧ e.stateAt n = some s :=
  ⟨Nat.find h, (e.stateAt (Nat.find h)).get (stateAt_find_isSome e h),
    Nat.find_spec h, Option.eq_some_of_isSome _⟩

/-- The end-state of a finite alternating sequence: the state reached after
the last transition (or `e.init` if there are no transitions). Defined as
the state at the canonical terminating position `Nat.find h`. -/
noncomputable def endState (e : AlterSeq State Label) (h : e.trans.Terminates) :
    State :=
  (e.stateAt (Nat.find h)).get (stateAt_find_isSome e h)

/-- The end-state is the state at `Nat.find h`. -/
theorem stateAt_find_eq_endState (e : AlterSeq State Label)
    (h : e.trans.Terminates) :
    e.stateAt (Nat.find h) = some (e.endState h) :=
  Option.eq_some_of_isSome _

/-- If `e.trans = Seq.nil`, the `endState` of `e` is its `init`. -/
theorem endState_of_trans_nil
    (e : AlterSeq State Label) (h_nil : e.trans = Seq.nil)
    (h : e.trans.Terminates) :
    e.endState h = e.init := by
  have h_term0 : e.trans.TerminatedAt 0 := by
    rw [h_nil]; rfl
  have h_find : Nat.find h = 0 := (Nat.find_eq_zero h).mpr h_term0
  have h_stateAt := stateAt_find_eq_endState e h
  rw [h_find] at h_stateAt
  have h_zero : e.stateAt 0 = some e.init := rfl
  rw [h_zero] at h_stateAt
  exact (Option.some.inj h_stateAt).symm

/-- The `endState` of an alterSeq extended by appending a single transition
`(l, s)` is `s` (the destination of the appended transition). -/
theorem endState_append_singleton
    (e : AlterSeq State Label) (h : e.trans.Terminates)
    (l : Label) (s : State) :
    (⟨e.init, e.trans.append (Seq.cons (l, s) Seq.nil)⟩ : AlterSeq State Label).endState
      ⟨Nat.find h + 1, Stream'.Seq.terminatedAt_append_find h
        (show (Seq.cons (l, s) Seq.nil).TerminatedAt 1 from rfl)⟩ = s := by
  classical
  set new_e : AlterSeq State Label :=
    ⟨e.init, e.trans.append (Seq.cons (l, s) Seq.nil)⟩
  set new_h : new_e.trans.Terminates :=
    ⟨Nat.find h + 1, Stream'.Seq.terminatedAt_append_find h
      (show (Seq.cons (l, s) Seq.nil).TerminatedAt 1 from rfl)⟩
  -- Step 1: Nat.find new_h = Nat.find h + 1.
  have h_find : Nat.find new_h = Nat.find h + 1 := by
    apply le_antisymm
    · exact Nat.find_le (Stream'.Seq.terminatedAt_append_find h
        (show (Seq.cons (l, s) Seq.nil).TerminatedAt 1 from rfl))
    · -- Show Nat.find h + 1 ≤ Nat.find new_h via contradiction.
      by_contra h_not
      have h_lt_succ : Nat.find new_h < Nat.find h + 1 := Nat.not_le.mp h_not
      have h_le : Nat.find new_h ≤ Nat.find h := Nat.lt_succ_iff.mp h_lt_succ
      have h_term_spec : new_e.trans.TerminatedAt (Nat.find new_h) := Nat.find_spec new_h
      by_cases h_eq : Nat.find new_h = Nat.find h
      · -- Nat.find new_h = Nat.find h: new_e.trans.get? (Nat.find h) = some (l, s).
        have h_get : new_e.trans.get? (Nat.find h) = some (l, s) := by
          change (e.trans.append (Seq.cons (l, s) Seq.nil)).get? (Nat.find h) = _
          have := Stream'.Seq.get?_append_find h (Seq.cons (l, s) Seq.nil) 0
          rw [Nat.add_zero] at this; rw [this]; rfl
        rw [h_eq] at h_term_spec
        change new_e.trans.get? (Nat.find h) = none at h_term_spec
        rw [h_get] at h_term_spec
        exact absurd h_term_spec (by simp)
      · -- Nat.find new_h < Nat.find h: get? value is in e.trans.
        have hk' : Nat.find new_h < Nat.find h := lt_of_le_of_ne h_le h_eq
        have h_not_term_e : ¬ e.trans.TerminatedAt (Nat.find new_h) := Nat.find_min h hk'
        have h_get_eq : new_e.trans.get? (Nat.find new_h) = e.trans.get? (Nat.find new_h) :=
          Stream'.Seq.get?_append_before_length h_not_term_e
        change new_e.trans.get? (Nat.find new_h) = none at h_term_spec
        rw [h_get_eq] at h_term_spec
        exact h_not_term_e h_term_spec
  -- Step 2: new_e.stateAt (Nat.find h + 1) = some s.
  have h_state : new_e.stateAt (Nat.find h + 1) = some s := by
    change (new_e.trans.get? (Nat.find h)).map Prod.snd = some s
    have h_get : new_e.trans.get? (Nat.find h) = some (l, s) := by
      change (e.trans.append (Seq.cons (l, s) Seq.nil)).get? (Nat.find h) = _
      have := Stream'.Seq.get?_append_find h (Seq.cons (l, s) Seq.nil) 0
      rw [Nat.add_zero] at this
      rw [this]
      rfl
    rw [h_get]
    rfl
  -- Combine via stateAt_find_eq_endState.
  have h_stateAt := AlterSeq.stateAt_find_eq_endState new_e new_h
  rw [h_find, h_state] at h_stateAt
  exact (Option.some.inj h_stateAt).symm

/-- The `endState` of the singleton-transition alterSeq `⟨s₀, cons (l₀, s₁) nil⟩`
is `s₁`. Useful for matching constraints involving `endState` against `s₁`. -/
theorem endState_singleton_cons
    (s₀ : State) (l₀ : Label) (s₁ : State) :
    (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
      (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil) = s₁ := by
  set h_hist_term : (Seq.cons (l₀, s₁) Seq.nil : Seq (Label × State)).Terminates :=
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
  have h_find : Nat.find h_hist_term = 1 := by
    apply le_antisymm
    · exact Nat.find_le (show (Seq.cons (l₀, s₁) Seq.nil).TerminatedAt 1 from rfl)
    · rw [Nat.one_le_iff_ne_zero]
      intro h_zero
      exact Stream'.Seq.cons_not_terminatedAt_zero
        (h_zero ▸ Nat.find_spec h_hist_term)
  have h_eq := AlterSeq.stateAt_find_eq_endState
    ({ init := s₀, trans := Seq.cons (l₀, s₁) Seq.nil
      : AlterSeq State Label }) h_hist_term
  rw [h_find] at h_eq
  exact (Option.some.inj h_eq).symm

end AlterSeq

variable {State : Type} {Label : Type}

def is_partial_exec (e : AlterSeq State Label) (sys : System State Label) : Prop :=
  ∀ n l s', e.trans.get? n = some (l, s') →
    ∃ s μ, e.stateAt n = some s ∧ sys.step s l μ ∧ s' ∈ μ.support

def is_exec (e : AlterSeq State Label) (sys : System State Label) : Prop :=
  is_partial_exec e sys ∧ sys.init = e.init

/-- A randomized scheduler for a PLTS `sys`. Given a finite execution prefix it
either returns `none` (the scheduler stops on this prefix, producing no further
step) or `some` distribution over the next step `(label, distribution)` of the
system. The well-formedness condition `valid` requires every step in the support
of a `some` output to be a valid transition of `sys` from the current state. -/
structure Scheduler (sys : System State Label) where
  next : AlterSeq State Label → PMF (Option (Label × PMF State))
  valid : ∀ (e : AlterSeq State Label) (n : ℕ) (s : State),
    e.trans.TerminatedAt n → e.stateAt n = some s →
    ∀ (l : Label) (μ : PMF State),
      some (l, μ) ∈ (next e).support → sys.step s l μ

/-- A probabilistic execution: a unique initial state together with a scheduler
resolving each step of the trace. -/
structure ProbabilisticExecution (sys : System State Label) where
  /-- The unique initial state of this execution. -/
  initState : PMF State
  scheduler : Scheduler sys

namespace ProbabilisticExecution

variable {sys : System State Label}

/-- The initial distribution alias: `pe.init = pe.initState`. The `init`
projection is kept for code that uniformly reads `pe.init` regardless of how
the structure stores the initial distribution. -/
noncomputable def init (pe : ProbabilisticExecution sys) : PMF State :=
  pe.initState

@[simp] theorem init_eq_initState (pe : ProbabilisticExecution sys) :
    pe.init = pe.initState := rfl

/-- The one-step kernel of a probabilistic execution. Given a finite prefix `e`
and a concrete next step `(l, s')`, returns the probability mass that the
scheduler emits `(l, s')` as the next step. With the PMF-out-Option scheduler
shape, this aggregates over all `μ : PMF State` that the scheduler might emit
alongside label `l`, weighted by the emission probability and `μ s'`:

  `kernel pe e (l, s') = ∑' μ, pe.scheduler.next e (some (l, μ)) * μ s'` -/
noncomputable def kernel (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (step : Label × State) : ENNReal :=
  ∑' μ, pe.scheduler.next e (some (step.1, μ)) * μ step.2

/-- The one-step kernel is bounded by `1`. -/
theorem kernel_le_one (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (step : Label × State) :
    pe.kernel e step ≤ 1 := by
  unfold kernel
  calc ∑' μ, pe.scheduler.next e (some (step.1, μ)) * μ step.2
      ≤ ∑' μ, pe.scheduler.next e (some (step.1, μ)) := by
        refine ENNReal.tsum_le_tsum (fun μ => ?_)
        exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
    _ ≤ ∑' (lμ : Label × PMF State), pe.scheduler.next e (some lμ) := by
        exact ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun μ => (step.1, μ))
          (fun μ₁ μ₂ h_eq => (Prod.mk.inj h_eq).2)
          (fun lμ => pe.scheduler.next e (some lμ))
    _ ≤ ∑' opt, pe.scheduler.next e opt := by
        exact ENNReal.tsum_comp_le_tsum_of_injective
          (f := some) (fun _ _ h => Option.some.inj h)
          (fun opt => pe.scheduler.next e opt)
    _ = 1 := (pe.scheduler.next e).tsum_coe

/-- The probability that the probabilistic execution `pe` produces the finite
concrete execution `e`.

Defined recursively from the END of the transition list (cons-end form):
* base (`e.trans = Seq.nil`): the initial mass `pe.init e.init`;
* step (`e.trans = sq.append (Seq.cons (l, s') Seq.nil)`): the probability of
  the truncated execution `⟨e.init, sq⟩` times the one-step kernel
  `pe.kernel ⟨e.init, sq⟩ (l, s')`.

Implementation reduces `e.trans` to a finite list via `Stream'.Seq.toList hFin`
and uses `List.reverseRecOn` (reverse / cons-end induction). The cons-end
factorisation `probOf_append_singleton` is then near-definitional. -/
noncomputable def probOf (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (hFin : e.trans.Terminates) : ENNReal :=
  (e.trans.toList hFin).reverseRecOn
    (motive := fun _ => ENNReal)
    (pe.init e.init)
    (fun rest last ih => ih * pe.kernel ⟨e.init, Seq.ofList rest⟩ last)

/-- `probOf` on an execution with empty trans reduces to the initial mass. -/
@[simp] theorem probOf_nil (pe : ProbabilisticExecution sys) (s₀ : State) :
    pe.probOf ⟨s₀, Seq.nil⟩ Stream'.Seq.terminates_nil = pe.init s₀ := by
  unfold probOf
  simp [Stream'.Seq.toList_nil]

/-- **Cons-end factorisation** (near-definitional from the cons-end recursion):
appending a single transition `last` at the end multiplies `probOf` by the
one-step kernel at the truncated prefix. -/
theorem probOf_append_singleton (pe : ProbabilisticExecution sys)
    (s₀ : State) (sq : Seq (Label × State)) (h_sq : sq.Terminates)
    (last : Label × State)
    (h_app : (sq.append (Seq.cons last Seq.nil)).Terminates) :
    pe.probOf ⟨s₀, sq.append (Seq.cons last Seq.nil)⟩ h_app =
      pe.probOf ⟨s₀, sq⟩ h_sq * pe.kernel ⟨s₀, sq⟩ last := by
  unfold probOf
  have h_singleton_term : (Seq.cons last Seq.nil : Seq (Label × State)).Terminates :=
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
  have h_toList : (sq.append (Seq.cons last Seq.nil)).toList h_app =
      sq.toList h_sq ++ [last] := by
    rw [Stream'.Seq.toList_append sq (Seq.cons last Seq.nil) h_sq h_singleton_term h_app]
    congr 1
    rw [Stream'.Seq.toList_cons]
    simp [Stream'.Seq.toList_nil]
  -- (⟨s₀, sq.append (cons last nil)⟩).trans = sq.append (cons last nil),
  -- so its toList equals sq.toList h_sq ++ [last] by h_toList.
  rw [show (⟨s₀, sq.append (Seq.cons last Seq.nil)⟩ : AlterSeq State Label).trans.toList h_app
        = sq.toList h_sq ++ [last] from h_toList]
  rw [List.reverseRecOn_concat]
  -- Seq.ofList (sq.toList h_sq) = sq.
  rw [Stream'.Seq.ofList_toList sq h_sq]

/-- `probOf e ≤ pe.init e.init`: a finite execution's probability is bounded by
the mass on its starting state. -/
theorem probOf_le_init (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (hFin : e.trans.Terminates) :
    pe.probOf e hFin ≤ pe.init e.init := by
  unfold probOf
  induction e.trans.toList hFin using List.reverseRecOn with
  | nil =>
    rw [List.reverseRecOn_nil]
  | append_singleton rest last _ih =>
    rw [List.reverseRecOn_concat]
    calc rest.reverseRecOn (motive := fun _ => ENNReal) (pe.init e.init) _
            * pe.kernel ⟨e.init, Seq.ofList rest⟩ last
        ≤ pe.init e.init * 1 := by gcongr; exact pe.kernel_le_one _ _
      _ = pe.init e.init := mul_one _

end ProbabilisticExecution

end PLTS
