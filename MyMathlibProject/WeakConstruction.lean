/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.WeakStep

/-!
# Constructions on PLTSs

This file collects constructions that build new probabilistic labelled
transition systems from existing ones, using the weak-step infrastructure
from `WeakStep.lean`.
-/

open Stream'

namespace PLTS

variable {α β State State_C State_A Label : Type}

/-! ## The weak-closure construction

Keep the state space and the internal-label classification of `sys` but
replace its step relation by *weak transitions*: from a state `s` on label
`l`, a `weak step` is a `weakTau` to `μ` if `l` is internal, or a `weakStep`
from `PMF.pure s` to `μ` if `l` is external. -/

/-- The **weak closure** of a labelled PLTS.

`sys.weakClosure : LabelledSystem State Label` has the same state space,
initial state, and internal-label predicate as `sys`, but its `step` relation
is the case-split weak transition:

* for an *internal* label `l`, `step s l μ := weakTau sys (PMF.pure s) μ`
  — `μ` is reachable by zero-or-more internal hyper-steps from the Dirac at
  `s`;
* for an *external* label `l`, `step s l μ := weakStep sys (PMF.pure s) l μ`
  — `μ` is reachable by a `weakTau ; hyperStep l ; weakTau` chain from the
  Dirac at `s`. -/
def LabelledSystem.weakClosure (sys : LabelledSystem State Label) :
    LabelledSystem State Label where
  init := sys.init
  step s l μ :=
    (sys.internal l ∧ weakTau sys (PMF.pure s) μ) ∨
    (¬ sys.internal l ∧ weakStep sys (PMF.pure s) l μ)
  internal := sys.internal

/-- `sys^w` is sugar for `LabelledSystem.weakClosure sys`, the weak-closure
construction replacing `sys`'s step relation by its case-split weak
transitions. -/
scoped postfix:max "^w" => LabelledSystem.weakClosure

/-! ## Trace-distribution preservation

The weak-closure construction `·^w` is designed to leave the *set of
achievable trace distributions* invariant. The preservation theorem splits
into two set inclusions ("subset" and "superset"). One direction is the
structural lift of `sys`-executions into the construction; the other is the
harder "expand" direction.
-/

/-! ### The weak-closure construction preserves trace distributions

The easy direction is `⊆`: every `pe` over `sys` is still a valid
probabilistic execution over `sys^w` (each strong step is a weak step), and
`traceProb` is unchanged because `sys^w` shares its `internal` predicate with
`sys` (so `trace` and `IsTight` are identical). The reverse direction
requires expanding each weak step in `sys^w` back into a chain of strong
`sys`-steps; that proof is deferred. -/

/-- **Every strong step lifts to a `sys^w` step.** This is the structural
fact that powers the easy direction of `weakClosure_traceProb_eq`. -/
theorem LabelledSystem.step_le_weakClosure_step
    (sys : LabelledSystem State Label)
    {s : State} {l : Label} {μ : PMF State} (h : sys.step s l μ) :
    sys^w.step s l μ := by
  change (sys.internal l ∧ weakTau sys (PMF.pure s) μ) ∨
       (¬ sys.internal l ∧ weakStep sys (PMF.pure s) l μ)
  by_cases h_int : sys.internal l
  · exact Or.inl ⟨h_int, weakTau_of_step h_int h
      (ls := sys) (s := s) (l := l) (μ := μ)⟩
  · exact Or.inr ⟨h_int, weakStep_strong h⟩

/-- **Easy direction of `weakClosure_traceProb_eq`**: every trace distribution
achievable by `sys` is achievable by `sys^w`. The witness `pe'` reuses `pe`'s
scheduler and initial distribution verbatim; only the validity field is
re-derived through `step_le_weakClosure_step`. Since `sys` and `sys^w` share
their internal-label predicate, the `trace` / `IsTight` filters and `probOf`
computation agree definitionally, so `traceProb` is unchanged. -/
theorem weakClosure_traceProb_subset (sys : LabelledSystem State Label) :
    achievableTraceDists sys ⊆ achievableTraceDists sys^w := by
  rintro D ⟨pe, h_init, hpe⟩
  refine ⟨
    { initState := pe.initState
      scheduler :=
        { next := pe.scheduler.next
          valid := fun e n s h_term h_state l μ h_supp =>
            sys.step_le_weakClosure_step
              (pe.scheduler.valid e n s h_term h_state l μ h_supp) } }, ?_, ?_⟩
  · -- `sys^w.init = sys.init`, so the lifted execution starts at the same state.
    exact h_init
  · intro τ
    exact hpe τ

/-- **Hard direction of `weakClosure_traceProb_eq`**: every trace distribution
achievable by `sys^w` is achievable by `sys`, via the algorithmic witness
`pe_of_weak sys pe'`. Reduces to `pe_of_weak_traceProb`. -/
theorem weakClosure_traceProb_superset (sys : LabelledSystem State Label) :
    achievableTraceDists sys^w ⊆ achievableTraceDists sys := by
  sorry

/-- **Weak-closure construction preserves trace distributions.** -/
theorem weakClosure_traceProb_eq (sys : LabelledSystem State Label) :
    achievableTraceDists sys = achievableTraceDists sys^w :=
  Set.Subset.antisymm
    (weakClosure_traceProb_subset sys)
    (weakClosure_traceProb_superset sys)

end PLTS
