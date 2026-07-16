/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.ProcessAlgebra.Composition
import Leslie2.Simulation.SimDefs

/-!
# Simulation-congruence machinery for binary parallel composition

Support lemmas for the precongruence `ProbabilisticForwardSimulation.parallel_right` (in
`Results.lean`): the composite relation `parallelRel`, its `PMFRel` couplings
(`pmfRel_parallel_left/right/sync`), and the three **weak-transition lift lemmas** (currently
`sorry`) that transport a component's weak transition into the product:

* `weakTau_parallel_left` — a `sys_A` τ-closure becomes a τ-left interleaving (B held);
* `weakTau_parallel_right` — a `sys_B` τ-closure becomes a τ-right interleaving (A held);
* `weakStep_parallel_sync` — a `sys_A` weak `l`-step synchronised with a single `sys_B` `l`-step.

The `prodPMF` algebra these build on lives in `ProcessAlgebra/Composition.lean`.
-/

open scoped BigOperators

namespace PLTS

variable {State_C State_A State_B Label : Type} [Silent Label]
  {sys_C : System State_C Label} {sys_A : System State_A Label}
  {R : State_C → PMF State_A → Prop}

/-! ### The composite relation and its `PMFRel` couplings -/

/-- The composite simulation relation for `parallel_right`: the abstract distribution keeps the
`sys_B` coordinate deterministic at `p.2` (a Dirac) and is `R`-related on the `sys_A` coordinate. -/
def parallelRel (R : State_C → PMF State_A → Prop) :
    State_C × State_B → PMF (State_A × State_B) → Prop :=
  fun p ν => ∃ μ_A, R p.1 μ_A ∧ ν = prodPMF μ_A (PMF.pure p.2)

/-- Lift a `PMFRel R` coupling to a `parallelRel R` coupling, holding the `sys_B` state `b`. -/
theorem pmfRel_parallel_left (b : State_B) {μ_C : PMF State_C} {ω_A : PMF (PMF State_A)}
    (h : PMFRel R μ_C ω_A) :
    PMFRel (parallelRel R) (prodPMF μ_C (PMF.pure b))
      (ω_A.map (fun ρ => prodPMF ρ (PMF.pure b))) := by
  obtain ⟨Ω_A, hfst, hsnd, hsupp⟩ := h
  refine ⟨Ω_A.map (fun q => ((q.1, b), prodPMF q.2 (PMF.pure b))), ?_, ?_, ?_⟩
  · rw [PMF.map_comp, prodPMF_pure_right, ← hfst, PMF.map_comp]; rfl
  · rw [PMF.map_comp, ← hsnd, PMF.map_comp]; rfl
  · intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact ⟨q.2, hsupp q hq, rfl⟩

/-- Lift the identity coupling on `sys_B` to a `parallelRel R` coupling, holding the `sys_A`
belief `μ_A`. -/
theorem pmfRel_parallel_right {c : State_C} {μ_A : PMF State_A} (μ_B : PMF State_B)
    (h : R c μ_A) :
    PMFRel (parallelRel R) (prodPMF (PMF.pure c) μ_B)
      (μ_B.map (fun b => prodPMF μ_A (PMF.pure b))) := by
  refine ⟨μ_B.map (fun b => ((c, b), prodPMF μ_A (PMF.pure b))), ?_, ?_, ?_⟩
  · rw [PMF.map_comp, prodPMF_pure_left]; rfl
  · rw [PMF.map_comp]; rfl
  · intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨b, hb, rfl⟩ := hp
    exact ⟨μ_A, h, rfl⟩

/-- Lift a `PMFRel R` coupling to a `parallelRel R` coupling for a synchronised step, pairing with
the `sys_B` outcome `μ_B`. -/
theorem pmfRel_parallel_sync {μ_C : PMF State_C} {ω_A : PMF (PMF State_A)} (μ_B : PMF State_B)
    (h : PMFRel R μ_C ω_A) :
    PMFRel (parallelRel R) (prodPMF μ_C μ_B)
      ((prodPMF ω_A μ_B).map (fun p => prodPMF p.1 (PMF.pure p.2))) := by
  obtain ⟨Ω_A, hfst, hsnd, hsupp⟩ := h
  refine ⟨(prodPMF Ω_A μ_B).map (fun q => ((q.1.1, q.2), prodPMF q.1.2 (PMF.pure q.2))),
    ?_, ?_, ?_⟩
  · rw [PMF.map_comp]
    change (prodPMF Ω_A μ_B).map (fun q => (Prod.fst q.1, id q.2)) = prodPMF μ_C μ_B
    rw [prodPMF_map, hfst, PMF.map_id]
  · rw [PMF.map_comp]
    change (prodPMF Ω_A μ_B).map
        ((fun p => prodPMF p.1 (PMF.pure p.2)) ∘ (fun q => (Prod.snd q.1, id q.2)))
      = (prodPMF ω_A μ_B).map (fun p => prodPMF p.1 (PMF.pure p.2))
    rw [← PMF.map_comp, prodPMF_map, hsnd, PMF.map_id]
  · intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact ⟨q.1.2, hsupp q.1 (mem_support_prodPMF.mp hq).1, rfl⟩

/-! ### The three weak-transition lift lemmas (the crux, left as `sorry`) -/

/-- A `sys_A` τ-closure lifts to a τ-left interleaving of the product, the `sys_B` side held at
any distribution `ρ`. -/
theorem weakTau_parallel_left (sys_A : System State_A Label) (sys_B : System State_B Label)
    {μ_A ν_A : PMF State_A} (ρ : PMF State_B) (h : weakTau sys_A μ_A ν_A) :
    weakTau (sys_A.parallel sys_B) (prodPMF μ_A ρ) (prodPMF ν_A ρ) := by
  sorry

/-- A `sys_B` τ-closure lifts to a τ-right interleaving of the product, the `sys_A` side held at
any distribution `ρ`. -/
theorem weakTau_parallel_right (sys_A : System State_A Label) (sys_B : System State_B Label)
    {μ_B ν_B : PMF State_B} (ρ : PMF State_A) (h : weakTau sys_B μ_B ν_B) :
    weakTau (sys_A.parallel sys_B) (prodPMF ρ μ_B) (prodPMF ρ ν_B) := by
  sorry

/-- A `sys_A` weak `l`-step (with `l` visible) synchronised with a single `sys_B` `l`-step lifts to
a weak `l`-step of the product. -/
theorem weakStep_parallel_sync (sys_A : System State_A Label) (sys_B : System State_B Label)
    {μ_A ν_A : PMF State_A} {l : Label} {s_B : State_B} {μ_B : PMF State_B}
    (hl : l ≠ Silent.τ) (hA : weakStep sys_A μ_A l ν_A) (hB : sys_B.step s_B l μ_B) :
    weakStep (sys_A.parallel sys_B) (prodPMF μ_A (PMF.pure s_B)) l (prodPMF ν_A μ_B) := by
  sorry

end PLTS
