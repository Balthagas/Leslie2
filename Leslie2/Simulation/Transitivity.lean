/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Simulation.Defs

/-!
# Weak-transition lifting for transitivity of forward simulation

Support for `ProbabilisticForwardSimulation.trans` (in `Results.lean`): the label-indexed
packaging `weakTransition` of the internal/external weak-transition split, and the crux lemma
`weakTransition_lift` (currently `sorry`) that transports a weak transition on the (concrete)
`sys_B` side through a forward simulation to a weak transition on the (abstract) `sys_A` side.

The composite relation `compRel` and the distribution-level relation `Simulates` these are stated
with live in `Simulation/Defs.lean`.
-/

namespace PLTS

variable {State_B State_A Label : Type} [Silent Label]

/-- The label-indexed weak transition packaged from the internal/external split used throughout
the simulation definitions: a `weakTau` on the silent label `τ`, a `weakStep` otherwise. This is
exactly the disjunction appearing in the `step` field of `ProbabilisticForwardSimulation`. -/
def weakTransition {S : Type} (sys : System S Label)
    (μ : PMF S) (l : Label) (ν : PMF S) : Prop :=
  ((l = Silent.τ) ∧ weakTau sys μ ν) ∨ (¬ (l = Silent.τ) ∧ weakStep sys μ l ν)

variable {sys_B : System State_B Label} {sys_A : System State_A Label}
  {R_AB : State_B → PMF State_A → Prop}

/-- **Weak-transition lifting through a forward simulation (the crux).**

If `μ_A` simulates `μ_B` (`Simulates R_AB μ_B μ_A`) and `μ_B` performs a weak `l`-transition to
`ν_B` in `sys_B`, then `μ_A` performs a weak `l`-transition to some `ν_A` in `sys_A` that simulates
`ν_B`.

Stated at the level of *distributions* `μ_B, ν_B` (rather than a single `State_B` state): this is
exactly the granularity the transitivity `step` obligation feeds in, since the concrete step is
matched on the `sys_B` side by a weak transition out of the whole distribution `μ_B`. The
single-state statement is the special case `μ_B = PMF.pure q_B`.

*Left as `sorry` for now.* -/
theorem weakTransition_lift
    (sim_AB : ProbabilisticForwardSimulation sys_B sys_A R_AB)
    {μ_B ν_B : PMF State_B} {μ_A : PMF State_A} {l : Label}
    (hsim : Simulates R_AB μ_B μ_A)
    (hweak : weakTransition sys_B μ_B l ν_B) :
    ∃ ν_A, weakTransition sys_A μ_A l ν_A ∧ Simulates R_AB ν_B ν_A := by
  sorry

end PLTS
