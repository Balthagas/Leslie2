/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.WeakStep

/-!
# Simulations
-/

open Stream'

namespace PLTS

variable {α β State State_C State_A Label : Type}

/-- Lifting of a state relation `R : α → β → Prop` to a relation on PMFs.
`PMFRel R μ₁ μ₂` holds iff there is a joint PMF `ω` on `α × β` whose first
marginal is `μ₁`, second marginal is `μ₂`, and whose support is contained
in `R`. -/
def PMFRel (R : α → β → Prop) (μ₁ : PMF α) (μ₂ : PMF β) : Prop :=
  ∃ ω : PMF (α × β),
    PMF.map Prod.fst ω = μ₁ ∧
    PMF.map Prod.snd ω = μ₂ ∧
    ∀ p ∈ ω.support, R p.1 p.2

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

/-- A *weak* probabilistic forward simulation from `sys_C` to `sys_A` along the
state relation `R : State_C → State_A → Prop`. Both systems carry an
internal/external label partition.

* `init`: every initial concrete state is matched by some initial abstract
  state with which it is `R`-related;
* `step`: every concrete transition `s_C -[l]→ μ_C` from an `R`-related pair
  `(s_C, s_A)` is matched on the abstract side by:
  - a `weakTau` (a τ-closure from `PMF.pure s_A`) when `l` is *internal* in
    `sys_C` — the concrete invisible step is matched by zero-or-more invisible
    abstract steps;
  - a `weakStep` with the same label `l` from `PMF.pure s_A` when `l` is
    *external* in `sys_C` — the concrete visible step is matched by
    τ-closure + one strong `l`-step + τ-closure on the abstract side;

  in both cases the resulting abstract distribution `μ_A` must be related to
  `μ_C` by `PMFRel R`. -/
structure WeakProbabilisticSimulation
    (sys_C : LabelledSystem State_C Label) (sys_A : LabelledSystem State_A Label)
    (R : State_C → State_A → Prop) where
  init : R sys_C.init sys_A.init
  step : ∀ s_C s_A, R s_C s_A →
    ∀ l μ_C, sys_C.step s_C l μ_C →
    ∃ μ_A : PMF State_A,
      ((sys_C.internal l ∧ weakTau sys_A (PMF.pure s_A) μ_A) ∨
       (¬ sys_C.internal l ∧ weakStep sys_A (PMF.pure s_A) l μ_A)) ∧
      PMFRel R μ_C μ_A

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
the abstract outcome, and the case split on `sys_C.internal l` picks between
the τ-only and the external weak transition. The notion is equivalent to
`WeakProbabilisticSimulation` (the latter is the special case where each `μ_A`
is concentrated on a single abstract state). -/
structure ProbabilisticForwardSimulation
    (sys_C : LabelledSystem State_C Label) (sys_A : LabelledSystem State_A Label)
    (R : State_C → PMF State_A → Prop) where
  init : ∃ μ_A, (∀ s_A ∈ μ_A.support, s_A = sys_A.init) ∧ R sys_C.init μ_A
  step : ∀ s_C μ_A, R s_C μ_A →
    ∀ l μ_C, sys_C.step s_C l μ_C →
    ∃ ω : PMF (PMF State_A),
      PMFRel R μ_C ω ∧
      ((sys_C.internal l ∧ weakTau sys_A μ_A (ω.bind id)) ∨
       (¬ sys_C.internal l ∧ weakStep sys_A μ_A l (ω.bind id)))



end PLTS
