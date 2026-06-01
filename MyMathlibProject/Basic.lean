/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Seq.Defs

/-!
# Probabilistic Labelled Transition System (PLTS)

PLTS are the basic model used to represent protocols.
-/

open Stream'

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

/-- For a finite alternating sequence, there is a position `n` and a state `s`
such that the underlying transition sequence terminates at `n` and the state at
position `n` is `s`. The pair `(n, s)` is the length and last state of the
trace. -/
lemma exists_endpoint (e : AlterSeq State Label) (h : e.trans.Terminates) :
    ∃ n s, e.trans.TerminatedAt n ∧ e.stateAt n = some s := by
  refine ⟨Nat.find h, ?_⟩
  have hT : e.trans.TerminatedAt (Nat.find h) := Nat.find_spec h
  rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | hpos
  · exact ⟨e.init, hT, by rw [h0]; rfl⟩
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hNotT : ¬ e.trans.TerminatedAt k :=
      Nat.find_min h (by rw [hk]; exact Nat.lt_succ_self k)
    have hNotNone : e.trans.get? k ≠ none := hNotT
    obtain ⟨⟨l, s⟩, hls⟩ := Option.ne_none_iff_exists'.mp hNotNone
    refine ⟨s, hT, ?_⟩
    rw [hk]
    change (e.trans.get? k).map Prod.snd = some s
    rw [hls]; rfl

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

end ProbabilisticExecution

end PLTS
