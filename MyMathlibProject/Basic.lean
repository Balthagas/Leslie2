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
returns a distribution over the next step `(label, distribution)` of the
system. The well-formedness condition `valid` requires every step in the support
to be a valid transition of `sys` from the current state. -/
structure Scheduler (sys : System State Label) where
  next : AlterSeq State Label → PMF (Label × PMF State)
  valid : ∀ (e : AlterSeq State Label) (n : ℕ) (s : State),
    e.trans.TerminatedAt n → e.stateAt n = some s →
    ∀ l μ, (l, μ) ∈ (next e).support → sys.step s l μ

/-- A probabilistic execution: an initial distribution over states together
with a scheduler resolving each step of the trace. -/
structure ProbabilisticExecution (sys : System State Label) where
  init : PMF State
  scheduler : Scheduler sys

namespace ProbabilisticExecution

variable {sys : System State Label}

/-- The one-step kernel of a probabilistic execution. Given a finite prefix `e`,
returns the distribution over the next concrete `(label, state)` step:
`(l, μ) ~ pe.scheduler.next e` is the next PLTS step, and `s' ~ μ` is the next
concrete state. -/
noncomputable def kernel (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) : PMF (Label × State) :=
  (pe.scheduler.next e).bind fun lμ => PMF.map (fun s' => (lμ.1, s')) lμ.2

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

end ProbabilisticExecution

end PLTS
