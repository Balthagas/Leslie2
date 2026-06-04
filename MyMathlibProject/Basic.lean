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
  is_partial_exec e sys ∧ e.init = sys.init

/-- A randomized scheduler for a PLTS `sys`. Given a finite execution prefix it
either returns `none` (the scheduler stops on this prefix, producing no further
step) or `some` distribution over the next step `(label, distribution)` of the
system. The well-formedness condition `valid` requires every step in the support
of a `some` output to be a valid transition of `sys` from the current state. -/
structure Scheduler (sys : System State Label) where
  next : AlterSeq State Label → Option (PMF (Label × PMF State))
  valid : ∀ (e : AlterSeq State Label) (n : ℕ) (s : State),
    e.trans.TerminatedAt n → e.stateAt n = some s →
    ∀ d, next e = some d → ∀ l μ, (l, μ) ∈ d.support → sys.step s l μ

/-- A probabilistic execution: a unique initial state together with a scheduler
resolving each step of the trace. -/
structure ProbabilisticExecution (sys : System State Label) where
  /-- The unique initial state of this execution. -/
  initState : State
  scheduler : Scheduler sys

namespace ProbabilisticExecution

variable {sys : System State Label}

/-- The initial distribution: a Dirac on `initState`. -/
noncomputable def init (pe : ProbabilisticExecution sys) : PMF State :=
  PMF.pure pe.initState

theorem init_apply (pe : ProbabilisticExecution sys) (s : State) :
    pe.init s = (PMF.pure pe.initState) s := rfl

@[simp] theorem init_apply_self (pe : ProbabilisticExecution sys) :
    pe.init pe.initState = 1 := by
  unfold init; exact PMF.pure_apply_self _

theorem init_apply_of_ne (pe : ProbabilisticExecution sys) {s : State}
    (h : s ≠ pe.initState) : pe.init s = 0 := by
  unfold init; exact PMF.pure_apply_of_ne _ _ h

@[simp] theorem init_support (pe : ProbabilisticExecution sys) :
    pe.init.support = {pe.initState} := by
  unfold init; exact PMF.support_pure _

/-- The one-step kernel of a probabilistic execution. Given a finite prefix `e`
and a concrete next step `(l, s')`, returns the probability mass that the
scheduler emits `(l, s')` as the next step. If the scheduler stops on `e`
(i.e. `pe.scheduler.next e = none`), the mass is `0`. Otherwise:

  `kernel pe e (l, s') = ∑_{μ} (pe.scheduler.next e) (l, μ) * μ s'`

i.e. it is `(pe.scheduler.next e).bind (fun (l, μ) => PMF.map (l, ·) μ) (l, s')`. -/
noncomputable def kernel (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (step : Label × State) : ENNReal :=
  (pe.scheduler.next e).elim 0 fun d =>
    (d.bind fun lμ => PMF.map (fun s' => (lμ.1, s')) lμ.2) step

/-- The one-step kernel is bounded by `1`: a coerced PMF mass when the
scheduler is active, `0` otherwise. -/
theorem kernel_le_one (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (step : Label × State) :
    pe.kernel e step ≤ 1 := by
  unfold kernel
  rcases h : pe.scheduler.next e with _ | d
  · simp
  · simp only [Option.elim_some]
    exact PMF.coe_le_one _ _

/-- Probability of taking the remaining transitions of a finite execution,
given the concrete prefix `pre` walked so far. Each step contributes the mass
of `pe.kernel cur_pre` at the corresponding `(label, state)` pair. -/
noncomputable def probOfRemaining (pe : ProbabilisticExecution sys)
    (pre : AlterSeq State Label) (xs : List (Label × State)) : ENNReal :=
  xs.foldl
    (fun (acc : ENNReal × AlterSeq State Label) hd =>
      let (acc_val, cur_pre) := acc
      (acc_val * pe.kernel cur_pre hd,
       ⟨cur_pre.init, cur_pre.trans.append (Seq.cons hd Seq.nil)⟩))
    (1, pre)
    |>.1

/-- The probability that the probabilistic execution `pe` produces the finite
concrete execution `e`.

For `e` with initial state `s₀` and transitions
`[(l₀, s₁), (l₁, s₂), …, (lₙ₋₁, sₙ)]`, this equals

  `pe.init s₀  *  ∏ᵢ pe.kernel e[..i] (lᵢ, sᵢ₊₁)`

where `e[..i]` is the prefix of `e` containing the first `i` transitions. -/
noncomputable def probOf (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (hFin : e.trans.Terminates) : ENNReal :=
  pe.init e.init * pe.probOfRemaining ⟨e.init, Seq.nil⟩ (e.trans.toList hFin)

/-- Auxiliary: the first component of `probOfRemaining`'s `foldl` stays `≤ 1`
when started from any value `≤ 1`. -/
private theorem probOfRemaining_aux_le_one (pe : ProbabilisticExecution sys)
    (xs : List (Label × State)) :
    ∀ acc : ENNReal × AlterSeq State Label, acc.1 ≤ 1 →
    (xs.foldl
      (fun (acc : ENNReal × AlterSeq State Label) hd =>
        (acc.1 * pe.kernel acc.2 hd,
         ⟨acc.2.init, acc.2.trans.append (Seq.cons hd Seq.nil)⟩)) acc).1 ≤ 1 := by
  induction xs with
  | nil => intro acc h_acc; exact h_acc
  | cons hd rest ih =>
    intro acc h_acc
    apply ih
    change acc.1 * pe.kernel acc.2 hd ≤ 1
    calc acc.1 * pe.kernel acc.2 hd
        ≤ 1 * 1 := by
          gcongr
          exact pe.kernel_le_one _ _
      _ = 1 := one_mul 1

/-- `probOfRemaining` is always at most `1` — a product of PMF values each ≤ 1. -/
theorem probOfRemaining_le_one (pe : ProbabilisticExecution sys)
    (pre : AlterSeq State Label) (xs : List (Label × State)) :
    pe.probOfRemaining pre xs ≤ 1 :=
  pe.probOfRemaining_aux_le_one xs (1, pre) (le_refl _)

/-- `probOf e ≤ pe.init e.init`: a finite execution's probability is bounded by
the mass on its starting state. -/
theorem probOf_le_init (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (hFin : e.trans.Terminates) :
    pe.probOf e hFin ≤ pe.init e.init := by
  unfold probOf
  calc pe.init e.init * pe.probOfRemaining ⟨e.init, Seq.nil⟩ (e.trans.toList hFin)
      ≤ pe.init e.init * 1 := by gcongr; exact pe.probOfRemaining_le_one _ _
    _ = pe.init e.init := mul_one _

/-- The initial-accumulator value factors linearly out of `probOfRemaining`'s
internal foldl: scaling the starting `acc.1` by `c` scales the result by `c`. -/
private theorem foldl_acc_linear (pe : ProbabilisticExecution sys) :
    ∀ (xs : List (Label × State)) (c : ENNReal) (pre : AlterSeq State Label),
    (xs.foldl
      (fun (acc : ENNReal × AlterSeq State Label) hd =>
        (acc.1 * pe.kernel acc.2 hd,
         ⟨acc.2.init, acc.2.trans.append (Seq.cons hd Seq.nil)⟩)) (c, pre)).1 =
    c * (xs.foldl
      (fun (acc : ENNReal × AlterSeq State Label) hd =>
        (acc.1 * pe.kernel acc.2 hd,
         ⟨acc.2.init, acc.2.trans.append (Seq.cons hd Seq.nil)⟩)) (1, pre)).1 := by
  intro xs
  induction xs with
  | nil => intro c pre; simp [List.foldl]
  | cons hd rest ih =>
    intro c pre
    simp only [List.foldl]
    rw [ih (c * pe.kernel pre hd) _, ih (1 * pe.kernel pre hd) _]
    ring

/-- `probOfRemaining` decomposes at the head: the first kernel mass multiplied
by the rest's `probOfRemaining` on the prefix extended by `hd`. -/
theorem probOfRemaining_cons (pe : ProbabilisticExecution sys)
    (pre : AlterSeq State Label) (hd : Label × State) (rest : List (Label × State)) :
    pe.probOfRemaining pre (hd :: rest) =
      pe.kernel pre hd *
        pe.probOfRemaining ⟨pre.init, pre.trans.append (Seq.cons hd Seq.nil)⟩ rest := by
  unfold probOfRemaining
  simp only [List.foldl]
  rw [pe.foldl_acc_linear rest (1 * pe.kernel pre hd) _]
  ring

-- The continuationFrom-related lemmas come after the definition.

/-- The probabilistic execution starting at the end-state of `history`, with
its scheduler shifted so it queries `pe.scheduler` on prefixes extended by
`history` on the left. Used to recursively decompose `traceProb`: after pe
takes a first transition, the "remaining" execution is a `continuationFrom`
of the just-emitted history.

The scheduler is conditional on `e'.init = history.endState`: when this
holds, the extended prefix has a consistent state at the join, and validity
transfers from `pe.scheduler.valid`. When it doesn't hold, the scheduler
returns `none` (validity vacuous). -/
noncomputable def continuationFrom (pe : ProbabilisticExecution sys)
    (history : AlterSeq State Label) (h_term : history.trans.Terminates) :
    ProbabilisticExecution sys where
  initState := history.endState h_term
  scheduler :=
    { next := fun e' =>
        open Classical in
        if e'.init = history.endState h_term then
          pe.scheduler.next ⟨history.init, history.trans.append e'.trans⟩
        else
          none
      valid := by
        classical
        intro e' n s h_term_e' h_state_e' d h_some l μ h_supp
        by_cases h_init : e'.init = history.endState h_term
        swap
        · rw [if_neg h_init] at h_some; exact absurd h_some (by simp)
        rw [if_pos h_init] at h_some
        set m := Nat.find h_term with hm_def
        -- Extended prefix: ⟨history.init, history.trans.append e'.trans⟩.
        -- Apply `pe.scheduler.valid` at position `m + n`.
        refine pe.scheduler.valid
          ⟨history.init, history.trans.append e'.trans⟩ (m + n) s ?_ ?_ d h_some l μ h_supp
        · -- TerminatedAt (m + n).
          exact Stream'.Seq.terminatedAt_append_find h_term h_term_e'
        · -- stateAt (m + n) = some s.
          rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
          · subst hn0
            -- s = e'.init = history.endState h_term.
            have h_e'_init : s = e'.init := by
              have : e'.stateAt 0 = some e'.init := rfl
              rw [this] at h_state_e'
              exact (Option.some.inj h_state_e').symm
            have h_s_eq : s = history.endState h_term := by rw [h_e'_init]; exact h_init
            rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
            · -- m = 0: extended.stateAt 0 = some history.init = some endState = some s.
              rw [Nat.add_zero, hm0]
              change some history.init = some s
              have h_endState_eq : history.endState h_term = history.init := by
                have h_eq := history.stateAt_find_eq_endState h_term
                rw [← hm_def, hm0] at h_eq
                have h_zero : history.stateAt 0 = some history.init := rfl
                rw [h_zero] at h_eq
                exact (Option.some.inj h_eq).symm
              rw [h_s_eq, h_endState_eq]
            · -- m ≥ 1: extended.stateAt m = history.stateAt m = some endState = some s.
              obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm_pos.ne'
              have hj' : m = j + 1 := hj
              rw [Nat.add_zero, hj']
              change ((history.trans.append e'.trans).get? j).map Prod.snd = some s
              have h_lt_find : j < Nat.find h_term := by
                rw [← hm_def]; rw [hj']; exact Nat.lt_succ_self j
              have h_before : (history.trans.append e'.trans).get? j = history.trans.get? j :=
                Stream'.Seq.get?_append_before_length (Nat.find_min h_term h_lt_find)
              rw [h_before]
              change history.stateAt (j + 1) = some s
              rw [← hj', hm_def, history.stateAt_find_eq_endState h_term, h_s_eq]
          · -- n ≥ 1: extended.stateAt (m + n) = e'.stateAt n = some s.
            obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn_pos.ne'
            have hk' : n = k + 1 := hk
            rw [hk']
            change ((history.trans.append e'.trans).get? (m + k)).map Prod.snd = some s
            have h_after : (history.trans.append e'.trans).get? (m + k) =
                e'.trans.get? k :=
              Stream'.Seq.get?_append_find h_term e'.trans k
            rw [h_after]
            change e'.stateAt (k + 1) = some s
            rw [← hk']; exact h_state_e' }

/-- The `continuationFrom`'s kernel, evaluated at a local prefix starting at
`history.endState`, equals `pe`'s kernel at the history-extended prefix. -/
theorem kernel_continuationFrom (pe : ProbabilisticExecution sys)
    (history : AlterSeq State Label) (h_term : history.trans.Terminates)
    (extra_trans : Seq (Label × State)) (step : Label × State) :
    (pe.continuationFrom history h_term).kernel
        ⟨history.endState h_term, extra_trans⟩ step =
      pe.kernel ⟨history.init, history.trans.append extra_trans⟩ step := by
  classical
  unfold kernel
  change (((if (⟨history.endState h_term, extra_trans⟩ : AlterSeq State Label).init
        = history.endState h_term then
          pe.scheduler.next ⟨history.init, history.trans.append extra_trans⟩
        else none).elim 0
      (fun d => (d.bind fun lμ => PMF.map (fun s' => (lμ.1, s')) lμ.2) step))) = _
  rw [if_pos rfl]

/-- The `continuationFrom`'s `probOfRemaining`, on a local prefix starting at
`history.endState`, equals `pe`'s `probOfRemaining` from the history-extended
prefix. -/
theorem probOfRemaining_continuationFrom (pe : ProbabilisticExecution sys)
    (history : AlterSeq State Label) (h_term : history.trans.Terminates)
    (xs : List (Label × State)) :
    (pe.continuationFrom history h_term).probOfRemaining
        ⟨history.endState h_term, Seq.nil⟩ xs =
      pe.probOfRemaining ⟨history.init, history.trans⟩ xs := by
  -- Both sides unfold to a foldl. Show by induction on xs that they
  -- agree pointwise, using `kernel_continuationFrom` at each step.
  -- Generalize over the accumulated extra_trans on the continuationFrom side.
  -- For simplicity, prove a more general statement first.
  have h_aux : ∀ (xs : List (Label × State)) (c : ENNReal)
      (extra : Seq (Label × State)),
      (xs.foldl (fun acc hd =>
        (acc.1 * (pe.continuationFrom history h_term).kernel acc.2 hd,
         ⟨acc.2.init, acc.2.trans.append (Seq.cons hd Seq.nil)⟩))
        (c, ⟨history.endState h_term, extra⟩)).1 =
      (xs.foldl (fun acc hd =>
        (acc.1 * pe.kernel acc.2 hd,
         ⟨acc.2.init, acc.2.trans.append (Seq.cons hd Seq.nil)⟩))
        (c, ⟨history.init, history.trans.append extra⟩)).1 := by
    intro xs
    induction xs with
    | nil => intros; rfl
    | cons hd rest ih =>
      intro c extra
      simp only [List.foldl]
      rw [kernel_continuationFrom pe history h_term extra hd]
      -- After the step, the continuationFrom side has extra := extra.append (cons hd nil),
      -- the pe side has trans := history.trans.append extra.append (cons hd nil).
      -- These should agree after rewriting via append_assoc.
      have h_assoc : history.trans.append (extra.append (Seq.cons hd Seq.nil)) =
          (history.trans.append extra).append (Seq.cons hd Seq.nil) :=
        (Stream'.Seq.append_assoc _ _ _).symm
      rw [← h_assoc]
      exact ih _ _
  unfold probOfRemaining
  exact h_aux xs 1 Seq.nil |>.trans (by rw [Stream'.Seq.append_nil])

/-- The `continuationFrom`'s `probOf`, at a local prefix starting at
`history.endState`, equals `pe`'s `probOfRemaining` from `history`'s trans
on the local prefix's transition list. -/
theorem probOf_continuationFrom (pe : ProbabilisticExecution sys)
    (history : AlterSeq State Label) (h_term : history.trans.Terminates)
    (e_local : AlterSeq State Label) (h_e_local : e_local.trans.Terminates)
    (h_init : e_local.init = history.endState h_term) :
    (pe.continuationFrom history h_term).probOf e_local h_e_local =
      pe.probOfRemaining ⟨history.init, history.trans⟩ (e_local.trans.toList h_e_local) := by
  unfold probOf
  have h_pmf : (pe.continuationFrom history h_term).init e_local.init = 1 := by
    change (PMF.pure (history.endState h_term)) e_local.init = 1
    rw [h_init, PMF.pure_apply]
    simp
  rw [h_pmf, one_mul, h_init]
  exact probOfRemaining_continuationFrom pe history h_term _

/-- **Factorization of `probOf` over the first transition.** A finite execution
starting with transition `(l₀, s₁)` factors into:
* the initial mass `pe.init s₀`,
* the first kernel step `pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁)`,
* the conditional `probOf` of the rest, expressed as a `probOf` of a
  `continuationFrom`. -/
theorem probOf_cons (pe : ProbabilisticExecution sys)
    (s₀ : State) (l₀ : Label) (s₁ : State) (e_rest_trans : Seq (Label × State))
    (h_term_full : (Seq.cons (l₀, s₁) e_rest_trans).Terminates) :
    pe.probOf ⟨s₀, Seq.cons (l₀, s₁) e_rest_trans⟩ h_term_full =
      pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
      (pe.continuationFrom ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
          (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
            : (Seq.cons (l₀, s₁) Seq.nil).Terminates)).probOf
        ⟨s₁, e_rest_trans⟩ (Stream'.Seq.terminates_tail_of_cons h_term_full) := by
  -- The history ⟨s₀, cons (l₀, s₁) nil⟩ has endState s₁.
  have h_hist_term : (Seq.cons (l₀, s₁) Seq.nil : Seq (Label × State)).Terminates :=
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
  have h_e_rest_term : e_rest_trans.Terminates :=
    Stream'.Seq.terminates_tail_of_cons h_term_full
  have h_find : Nat.find h_hist_term = 1 := by
    apply le_antisymm
    · exact Nat.find_le (show (Seq.cons (l₀, s₁) Seq.nil).TerminatedAt 1 from rfl)
    · rw [Nat.one_le_iff_ne_zero]
      intro h_zero
      exact Stream'.Seq.cons_not_terminatedAt_zero
        (h_zero ▸ Nat.find_spec h_hist_term)
  have h_endState :
      ({ init := s₀, trans := Seq.cons (l₀, s₁) Seq.nil
        : AlterSeq State Label }).endState h_hist_term = s₁ := by
    have h_eq := AlterSeq.stateAt_find_eq_endState
      ({ init := s₀, trans := Seq.cons (l₀, s₁) Seq.nil
        : AlterSeq State Label }) h_hist_term
    rw [h_find] at h_eq
    exact (Option.some.inj h_eq).symm
  -- LHS: pe.init s₀ * pe.probOfRemaining ⟨s₀, nil⟩ ((l₀, s₁) :: rest_list).
  -- Factor first step via probOfRemaining_cons; the tail prefix becomes
  -- ⟨s₀, nil.append (cons (l₀, s₁) nil)⟩ = ⟨s₀, cons (l₀, s₁) nil⟩.
  have h_lhs : pe.probOf ⟨s₀, Seq.cons (l₀, s₁) e_rest_trans⟩ h_term_full =
      pe.init s₀ * pe.kernel ⟨s₀, Seq.nil⟩ (l₀, s₁) *
      pe.probOfRemaining ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩
        (e_rest_trans.toList h_e_rest_term) := by
    unfold probOf
    rw [Stream'.Seq.toList_cons, probOfRemaining_cons]
    rw [show (⟨s₀, Seq.nil⟩ : AlterSeq State Label).trans.append
      (Seq.cons (l₀, s₁) Seq.nil) = Seq.cons (l₀, s₁) Seq.nil from
      Stream'.Seq.nil_append _]
    ring
  -- RHS: ... * (continuationFrom).probOf ⟨s₁, e_rest_trans⟩ h_e_rest_term.
  -- By probOf_continuationFrom (with init match via h_endState), this equals
  -- ... * pe.probOfRemaining ⟨s₀, cons (l₀, s₁) nil⟩ (e_rest_trans.toList _).
  rw [h_lhs]
  rw [probOf_continuationFrom pe ⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ h_hist_term
    ⟨s₁, e_rest_trans⟩ h_e_rest_term h_endState.symm]

/-- `continuationFrom`'s `probOf` is zero when the local prefix's init
doesn't match `history.endState`: the `init` factor `(PMF.pure
(history.endState)) e_local.init = 0`. -/
theorem probOf_continuationFrom_zero_of_init_ne
    (pe : ProbabilisticExecution sys) (history : AlterSeq State Label)
    (h_term : history.trans.Terminates) (e_local : AlterSeq State Label)
    (h_e_local : e_local.trans.Terminates)
    (h_init_ne : e_local.init ≠ history.endState h_term) :
    (pe.continuationFrom history h_term).probOf e_local h_e_local = 0 := by
  unfold probOf
  have h_pmf : (pe.continuationFrom history h_term).init e_local.init = 0 := by
    change (PMF.pure (history.endState h_term)) e_local.init = 0
    rw [PMF.pure_apply]
    simp [h_init_ne.symm, Ne.symm]
  rw [h_pmf]
  ring

end ProbabilisticExecution

end PLTS
