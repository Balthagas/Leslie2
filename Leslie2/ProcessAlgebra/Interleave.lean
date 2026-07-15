/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.ProcessAlgebra.Composition
import Leslie2.Simulation.Defs

/-!
# Simulation-congruence machinery for `interleave`

Support lemmas for the precongruence `ProbabilisticForwardSimulation.interleave` (in
`Results.lean`): the composite relation `interleaveRel`, its `PMFRel` coupling
(`pmfRel_interleave`), and the two
**weak-transition lift lemmas** (currently `sorry`) that transport a single component's weak
transition into the fully-asynchronous product:

* `weakTau_interleave` — a `sysA i` τ-closure ⟹ an interleave τ-closure;
* `weakStep_interleave` — a `sysA i` weak `l`-step ⟹ an interleave weak `l`-step (still interleaved,
  never synchronised).

The `piPMF`/`Function.update` algebra these build on lives in `ProcessAlgebra/Composition.lean`.
-/

open scoped BigOperators

namespace PLTS

section Interleave

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {State_C State_A : ι → Type} {Label : Type} [Silent Label]
  {sysC : ∀ i, System (State_C i) Label} {sysA : ∀ i, System (State_A i) Label}
  {R : ∀ i, State_C i → PMF (State_A i) → Prop}

/-- The composite relation for the interleave precongruence: the abstract distribution is the
independent product `piPMF μ_` of per-component beliefs, each `R`-related to the concrete state. -/
def interleaveRel (R : ∀ i, State_C i → PMF (State_A i) → Prop) :
    (∀ i, State_C i) → PMF (∀ i, State_A i) → Prop :=
  fun s ν => ∃ μ_ : ∀ i, PMF (State_A i), (∀ i, R i (s i) (μ_ i)) ∧ ν = piPMF μ_

/-- Lift a component `PMFRel (R i)` coupling to an `interleaveRel R` coupling, holding the other
components at their beliefs `μ_ j` (which are `R j`-related to `s j` by `hR`). -/
theorem pmfRel_interleave (i : ι) (s : ∀ j, State_C j) (μ_ : ∀ j, PMF (State_A j))
    (hR : ∀ j, R j (s j) (μ_ j)) {μ_Ci : PMF (State_C i)} {ω_Ai : PMF (PMF (State_A i))}
    (h : PMFRel (R i) μ_Ci ω_Ai) :
    PMFRel (interleaveRel R) (piPMF (Function.update (fun j => PMF.pure (s j)) i μ_Ci))
      (ω_Ai.map (fun ρ => piPMF (Function.update μ_ i ρ))) := by
  obtain ⟨Ω_Ai, hfst, hsnd, hsupp⟩ := h
  refine ⟨Ω_Ai.map (fun q => (Function.update s i q.1, piPMF (Function.update μ_ i q.2))),
    ?_, ?_, ?_⟩
  · rw [PMF.map_comp, piPMF_update_pure, ← hfst, PMF.map_comp]; rfl
  · rw [PMF.map_comp, ← hsnd, PMF.map_comp]; rfl
  · intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨Function.update μ_ i q.2, ?_, rfl⟩
    intro j
    dsimp only
    by_cases hj : j = i
    · subst hj; rw [Function.update_self, Function.update_self]; exact hsupp q hq
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]; exact hR j

/-! ### The two weak-transition lift lemmas (the crux, left as `sorry`) -/

/-- A `sysA i` τ-closure lifts to an interleave τ-closure, holding all the other components at their
beliefs `μ_ j`. -/
theorem weakTau_interleave (i : ι) (μ_ : ∀ j, PMF (State_A j)) {ν : PMF (State_A i)}
    (h : weakTau (sysA i) (μ_ i) ν) :
    weakTau (System.interleave sysA) (piPMF μ_) (piPMF (Function.update μ_ i ν)) := by
  sorry

/-- A `sysA i` weak `l`-step lifts to an interleave weak `l`-step (still interleaved: the other
components are held), holding all the other components at their beliefs `μ_ j`. -/
theorem weakStep_interleave (i : ι) (l : Label) (μ_ : ∀ j, PMF (State_A j))
    {ν : PMF (State_A i)} (h : weakStep (sysA i) (μ_ i) l ν) :
    weakStep (System.interleave sysA) (piPMF μ_) l (piPMF (Function.update μ_ i ν)) := by
  sorry

end Interleave

end PLTS
