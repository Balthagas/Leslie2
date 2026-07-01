/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.WeakStep
import MyMathlibProject.DistConstruction
import MyMathlibProject.TraceMap
import MyMathlibProject.TraceProbBound
import MyMathlibProject.TightTrace

/-!
# Constructions on PLTSs

This file collects constructions that build new probabilistic labelled
transition systems from existing ones, using the weak-step infrastructure
from `WeakStep.lean`.
-/

open Stream'

namespace PLTS

-- The canonical-`τ` instance `[Silent Label]` is threaded as a section variable
-- but is unused by some pure level-mass lemmas; silence the over-inclusion linter.
set_option linter.unusedSectionVars false

variable {α β State State_C State_A Label : Type} [Silent Label]

/-! ## The weak-closure construction

Keep the state space and the internal-label classification of `sys` but
replace its step relation by *weak transitions*: from a state `s` on label
`l`, a `weak step` is a `weakTau` to `μ` if `l` is internal, or a `weakStep`
from `PMF.pure s` to `μ` if `l` is external. -/

/-- The **weak closure** of a labelled PLTS.

`sys.weakClosure : System State Label` has the same state space,
initial state, and internal-label predicate as `sys`, but its `step` relation
is the case-split weak transition:

* for an *internal* label `l`, `step s l μ := weakTau sys (PMF.pure s) μ`
  — `μ` is reachable by zero-or-more internal hyper-steps from the Dirac at
  `s`;
* for an *external* label `l`, `step s l μ := weakStep sys (PMF.pure s) l μ`
  — `μ` is reachable by a `weakTau ; hyperStep l ; weakTau` chain from the
  Dirac at `s`. -/
def System.weakClosure (sys : System State Label) :
    System State Label where
  init := sys.init
  step s l μ :=
    ((l = Silent.τ) ∧ weakTau sys (PMF.pure s) μ) ∨
    (¬ (l = Silent.τ) ∧ weakStep sys (PMF.pure s) l μ)

/-- `sys^w` is sugar for `System.weakClosure sys`, the weak-closure
construction replacing `sys`'s step relation by its case-split weak
transitions. -/
scoped postfix:max "^w" => System.weakClosure

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
theorem System.step_le_weakClosure_step
    (sys : System State Label)
    {s : State} {l : Label} {μ : PMF State} (h : sys.step s l μ) :
    sys^w.step s l μ := by
  change ((l = Silent.τ) ∧ weakTau sys (PMF.pure s) μ) ∨
       (¬ (l = Silent.τ) ∧ weakStep sys (PMF.pure s) l μ)
  by_cases h_int : (l = Silent.τ)
  · exact Or.inl ⟨h_int, weakTau_of_step h_int h
      (ls := sys) (s := s) (l := l) (μ := μ)⟩
  · exact Or.inr ⟨h_int, weakStep_strong h⟩

/-- **Easy direction of `weakClosure_traceProb_eq`**: every trace distribution
achievable by `sys` is achievable by `sys^w`. The witness `pe'` reuses `pe`'s
scheduler and initial distribution verbatim; only the validity field is
re-derived through `step_le_weakClosure_step`. Since `sys` and `sys^w` share
their internal-label predicate, the `trace` / `IsTight` filters and `probOf`
computation agree definitionally, so `traceProb` is unchanged. -/
theorem weakClosure_traceProb_subset (sys : System State Label) :
    achievableTraceDists sys ⊆ achievableTraceDists sys^w :=
  achievableTraceDists_map (sys_X := sys) (sys_Y := sys^w) (f := id) rfl
    (fun s l μ h => by rw [PMF.map_id]; exact sys.step_le_weakClosure_step h)


/-! ### The hard direction `weakClosure_traceProb_superset` (proved downstream)

`weakClosure_traceProb_superset` — every trace distribution achievable by
`sys^w` is achievable by `sys` — and the resulting equality
`weakClosure_traceProb_eq` are proved in `ExpandTraceProb.lean`. Their proof
unfolds each `sys^w` weak step `τ*·l·τ*` into a concrete `sys`-path (the
"unfold a `sys^w`-scheduler" algorithm of `blueprint/src/content.tex`), which
lives in `Expand`/`ExpandTrace`/`ExpandProbOf`/`ExpandSched` — all of which
import this file, so the theorem cannot be stated here without an import cycle. -/

end PLTS
