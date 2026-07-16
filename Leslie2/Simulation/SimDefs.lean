/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Weak.WeakTransition

/-!
# Simulation definitions

The three notions of probabilistic simulation used in this development —
`StrongProbabilisticSimulation`, `WeakProbabilisticSimulation`, and
`ProbabilisticForwardSimulation` — together with `PMFRel`, the lifting of a
state relation to a coupling of PMFs. The characterizations tying weak/forward
simulation to strong simulation into a transformed system live in
`Simulation/Equivalences.lean` (their supporting lemmas in
`Weak/WeakChar.lean`).
-/

open Stream'

namespace PLTS

variable {α β State State_C State_A State_B Label : Type} [Silent Label]

/-- Lifting of a state relation `R : α → β → Prop` to a relation on PMFs.
`PMFRel R μ₁ μ₂` holds iff there is a joint PMF `ω` on `α × β` whose first
marginal is `μ₁`, second marginal is `μ₂`, and whose support is contained
in `R`. -/
def PMFRel (R : α → β → Prop) (μ₁ : PMF α) (μ₂ : PMF β) : Prop :=
  ∃ ω : PMF (α × β),
    PMF.map Prod.fst ω = μ₁ ∧
    PMF.map Prod.snd ω = μ₂ ∧
    ∀ p ∈ ω.support, R p.1 p.2

/-- **Forward (Kleisli) lift of a state-to-distribution relation to distributions.**
`Simulates R μ ν` — read "`ν` simulates `μ`" — holds iff `ν` is a bind `μ.bind f` where
every `s ∈ μ.support` is `R`-matched by `f s`. This is the distribution-level form of the
relation `R` carried by a `ProbabilisticForwardSimulation`. -/
def Simulates {S T : Type} (R : S → PMF T → Prop) (μ : PMF S) (ν : PMF T) : Prop :=
  ∃ f : S → PMF T, ν = μ.bind f ∧ ∀ s ∈ μ.support, R s (f s)

/-- **Composite simulation relation.** `compRel R_BC R_AB` relates a concrete `State_C`
state `s_C` to an abstract distribution `μ_A` iff some `μ_B` with `R_BC s_C μ_B` is
`Simulates R_AB`-related to `μ_A`. It is the relation along which forward simulation
composes (`ProbabilisticForwardSimulation.trans`). -/
def compRel (R_BC : State_C → PMF State_B → Prop)
    (R_AB : State_B → PMF State_A → Prop) : State_C → PMF State_A → Prop :=
  fun s_C μ_A => ∃ μ_B, R_BC s_C μ_B ∧ Simulates R_AB μ_B μ_A

/-- A *strong* probabilistic forward simulation from `sys_C` to `sys_A` along
the state relation `R : State_C → State_A → Prop`:

* `init`: every initial concrete state is matched by some initial abstract
  state with which it is `R`-related;
* `step`: every concrete transition `s_C -[l]→ μ_C` from an `R`-related pair
  `(s_C, s_A)` can be matched by an abstract *strong* transition
  `s_A -[l]→ μ_A` such that `μ_C` and `μ_A` are related by the PMF-lifting of
  `R`. -/
structure StrongProbabilisticSimulation
    (sys_C : System State_C Label) (sys_A : System State_A Label)
    (R : State_C → State_A → Prop) where
  init : R sys_C.init sys_A.init
  step : ∀ s_C s_A, R s_C s_A →
    ∀ l μ_C, sys_C.step s_C l μ_C →
    ∃ μ_A, sys_A.step s_A l μ_A ∧ PMFRel R μ_C μ_A

/-- A *probabilistic* forward simulation from `sys_C` to `sys_A`, parameterised
by a relation `R : State_C → PMF State_A → Prop` linking each concrete state to
a *distribution* over abstract states (rather than to a single abstract state
as in `WeakProbabilisticSimulation`).

* `init`: every initial concrete state is matched by some abstract distribution
  supported on initial abstract states;
* `step`: from an `R`-related pair `(s_C, μ_A)` with `μ_A : PMF State_A`, every
  concrete transition `s_C -[l]→ μ_C` is matched on the abstract side by a
  weak transition from `μ_A` to `ω.bind id`, where `ω : PMF (PMF State_A)` is
  a coupling of `μ_C` with `R`-related abstract distributions (i.e.
  `PMFRel R μ_C ω`). The choice between `weakTau` and `weakStep` depends, as
  in `WeakProbabilisticSimulation`, on whether `l` is internal in `sys_C`.

Modulo the typing of `R` (`State_C → PMF State_A → Prop` here vs.
`State_C → State_A → Prop` there), the matching pattern is exactly the same as
in `WeakProbabilisticSimulation`: `PMFRel R` couples the concrete outcome with
the abstract outcome, and the case split on `(l = Silent.τ)` picks between
the τ-only and the external weak transition. The notion is equivalent to
`WeakProbabilisticSimulation` (the latter is the special case where each `μ_A`
is concentrated on a single abstract state). -/
structure ProbabilisticForwardSimulation
    (sys_C : System State_C Label) (sys_A : System State_A Label)
    (R : State_C → PMF State_A → Prop) where
  init : ∃ μ_A, (∀ s_A ∈ μ_A.support, s_A = sys_A.init) ∧ R sys_C.init μ_A
  step : ∀ s_C μ_A, R s_C μ_A →
    ∀ l μ_C, sys_C.step s_C l μ_C →
    ∃ ω : PMF (PMF State_A),
      PMFRel R μ_C ω ∧
      (((l = Silent.τ) ∧ weakTau sys_A μ_A (ω.bind id)) ∨
       (¬ (l = Silent.τ) ∧ weakStep sys_A μ_A l (ω.bind id)))

end PLTS
