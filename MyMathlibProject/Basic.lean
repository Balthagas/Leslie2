/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Seq.Defs
import Mathlib.Data.Seq.Basic

/-!
# Probabilistic Labelled Transition System (PLTS)

PLTS are the basic model used to represent protocols.
-/

open Stream'

namespace Stream'.Seq

variable {α : Type*}

/-- For `n` the *exact* length of `s` (i.e. `s.TerminatedAt n` and `s` is not
terminated at any smaller index), positions in `s.append s'` past `n` reduce
to positions in `s'`: `(s.append s').get? (n + k) = s'.get? k`. -/
theorem get?_append_after_length {s s' : Seq α} {n : ℕ}
    (h_min : ∀ k < n, ¬ s.TerminatedAt k)
    (h_done : s.TerminatedAt n) (k : ℕ) :
    (s.append s').get? (n + k) = s'.get? k := by
  induction n generalizing s with
  | zero =>
    rw [terminatedAt_zero_iff] at h_done
    subst h_done
    rw [nil_append, Nat.zero_add]
  | succ j ih =>
    have h_not_term_0 : ¬ s.TerminatedAt 0 := h_min 0 (Nat.zero_lt_succ _)
    cases s with
    | nil => exact absurd terminatedAt_nil h_not_term_0
    | cons a t =>
      rw [cons_append, show j + 1 + k = (j + k) + 1 from by ring, get?_cons_succ]
      apply ih
      · intro k' hk'
        have h_succ_lt : k' + 1 < j + 1 := by omega
        have h_not := h_min (k' + 1) h_succ_lt
        rwa [cons_terminatedAt_succ_iff] at h_not
      · rwa [cons_terminatedAt_succ_iff] at h_done

/-- Specialization: `(s.append s').get? (Nat.find h + k) = s'.get? k`. -/
theorem get?_append_find {s : Seq α} (h : s.Terminates) (s' : Seq α) (k : ℕ) :
    (s.append s').get? (Nat.find h + k) = s'.get? k :=
  get?_append_after_length (fun _ hk => Nat.find_min h hk) (Nat.find_spec h) k

/-- Before `s` terminates at position `k`, append's `get?` agrees with `s`'s. -/
theorem get?_append_before_length {s s' : Seq α} {k : ℕ}
    (h_not_term : ¬ s.TerminatedAt k) :
    (s.append s').get? k = s.get? k := by
  induction k generalizing s with
  | zero =>
    cases s with
    | nil => exact absurd terminatedAt_nil h_not_term
    | cons a t => rw [cons_append]; rfl
  | succ k' ih =>
    cases s with
    | nil => exact absurd terminatedAt_nil h_not_term
    | cons a t =>
      rw [cons_append, get?_cons_succ, get?_cons_succ]
      exact ih (by rwa [← cons_terminatedAt_succ_iff (x := a)])

/-- `(s.append s').TerminatedAt (Nat.find h + n)` when `s'.TerminatedAt n`. -/
theorem terminatedAt_append_find {s : Seq α} (h : s.Terminates) {s' : Seq α}
    {n : ℕ} (h_s' : s'.TerminatedAt n) :
    (s.append s').TerminatedAt (Nat.find h + n) := by
  change (s.append s').get? _ = none
  rw [get?_append_find h s' n]; exact h_s'

end Stream'.Seq

namespace PLTS

structure System (State : Type) (Label : Type) where
  init : State → Prop
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

end AlterSeq

variable {State : Type} {Label : Type}

def is_partial_exec (e : AlterSeq State Label) (sys : System State Label) : Prop :=
  ∀ n l s', e.trans.get? n = some (l, s') →
    ∃ s μ, e.stateAt n = some s ∧ sys.step s l μ ∧ s' ∈ μ.support

def is_exec (e : AlterSeq State Label) (sys : System State Label) : Prop :=
  is_partial_exec e sys ∧ sys.init e.init

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

/-- A probabilistic execution: an initial distribution over states together
with a scheduler resolving each step of the trace. -/
structure ProbabilisticExecution (sys : System State Label) where
  init : PMF State
  scheduler : Scheduler sys

namespace ProbabilisticExecution

variable {sys : System State Label}

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
  init := PMF.pure (history.endState h_term)
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

end ProbabilisticExecution

end PLTS
