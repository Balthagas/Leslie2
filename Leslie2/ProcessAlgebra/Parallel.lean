/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.ProcessAlgebra.Composition
import Leslie2.Simulation.SimDefs
import Leslie2.Weak.Embed

/-!
# Simulation-congruence machinery for binary parallel composition

Support lemmas for the precongruence `ProbabilisticForwardSimulation.parallel_right` (in
`Results.lean`): the composite relation `parallelRel`, its `PMFRel` couplings
(`pmfRel_parallel_left/right/sync`), and the three **weak-transition lift lemmas** that transport a
component's weak transition into the product:

* `weakTau_parallel_left` — a `sys_A` τ-closure becomes a τ-left interleaving (B held), via the
  scheduler-map primitive `weakTau_embed`;
* `weakTau_parallel_right` — a single `sys_B` τ-step becomes a τ-right interleaving (A held);
  matched one-to-one, so just a τ-`hyperStep` collapsed by `weakTau_of_hyperStep` (no embed);
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

/-! ### The three weak-transition lift lemmas (the crux) -/

/-- A `sys_A` τ-closure lifts to a τ-left interleaving of the product, the `sys_B` side held at the
state `s_B`. The abstract (moving) side is a genuine τ-closure, so this is a direct application of
the scheduler-map primitive `weakTau_embed` along the injective embedding `a ↦ (a, s_B)` (every
`sys_A` τ-step becomes a left-interleaved product τ-step). -/
theorem weakTau_parallel_left (sys_A : System State_A Label) (sys_B : System State_B Label)
    {μ_A ν_A : PMF State_A} (s_B : State_B) (h : weakTau sys_A μ_A ν_A) :
    weakTau (sys_A.parallel sys_B) (prodPMF μ_A (PMF.pure s_B)) (prodPMF ν_A (PMF.pure s_B)) := by
  have hι : Function.Injective (fun a : State_A => (a, s_B)) := fun a a' hh => congrArg Prod.fst hh
  have hstep : ∀ a μ, sys_A.step a Silent.τ μ →
      (sys_A.parallel sys_B).step (a, s_B) Silent.τ (μ.map (fun a => (a, s_B))) :=
    fun a μ hA => Or.inr (Or.inl ⟨rfl, μ, hA, (prodPMF_pure_right μ s_B).symm⟩)
  rw [prodPMF_pure_right, prodPMF_pure_right]
  exact weakTau_embed (fun a : State_A => (a, s_B)) hι hstep h

/-- A single `sys_B` τ-step lifts to a τ-right interleaving of the product, the `sys_A` side held at
any distribution `ρ`. Since the precongruence keeps `sys_B` identical on both sides, the moving
(right) component is matched *one-to-one* by that same step — so this is a single τ-`hyperStep` of
the product (each point `(a, s_B)` steps right, `a` held), collapsed by `weakTau_of_hyperStep`; no
scheduler transport is needed. -/
theorem weakTau_parallel_right (sys_A : System State_A Label) (sys_B : System State_B Label)
    (ρ : PMF State_A) {s_B : State_B} {μ_B : PMF State_B} (hB : sys_B.step s_B Silent.τ μ_B) :
    weakTau (sys_A.parallel sys_B) (prodPMF ρ (PMF.pure s_B)) (prodPMF ρ μ_B) := by
  apply weakTau_of_hyperStep
  refine ⟨fun p => PMF.pure (prodPMF (PMF.pure p.1) μ_B), ?_, ?_⟩
  · intro p hp μ hμ
    rw [PMF.mem_support_pure_iff] at hμ; subst hμ
    obtain ⟨-, hp2⟩ := mem_support_prodPMF.mp hp
    rw [PMF.mem_support_pure_iff] at hp2
    exact Or.inr (Or.inr ⟨rfl, μ_B, by rw [hp2]; exact hB, rfl⟩)
  · simp only [PMF.pure_bind, id_eq, prodPMF, PMF.bind_bind]

/-- Binding over the `sys_B` coordinate reassembles a product: `κ.bind (b ↦ ρ ⊗ δ_b) = ρ ⊗ κ`. -/
private theorem bind_prodPMF_pure_right (ρ : PMF State_A) (κ : PMF State_B) :
    κ.bind (fun b => prodPMF ρ (PMF.pure b)) = prodPMF ρ κ := by
  simp only [prodPMF, PMF.pure_bind]; rw [PMF.bind_comm]

/-- A `sys_A` weak `l`-step (with `l` visible) synchronised with a single `sys_B` `l`-step lifts to
a weak `l`-step of the product. Three layers: the pre-τ-closure holds `sys_B` at `s_B`
(`weakTau_parallel_left`); the middle synchronises `sys_A`'s `l`-hyper-step with `sys_B`'s single
`l`-step into a product `l`-hyper-step; the post-τ-closure holds `sys_B` at the *distribution* `μ_B`
so it mixes the Dirac-held `weakTau_parallel_left` over `μ_B` (`weakTau_mix`). -/
theorem weakStep_parallel_sync (sys_A : System State_A Label) (sys_B : System State_B Label)
    {μ_A ν_A : PMF State_A} {l : Label} {s_B : State_B} {μ_B : PMF State_B}
    (hl : l ≠ Silent.τ) (hA : weakStep sys_A μ_A l ν_A) (hB : sys_B.step s_B l μ_B) :
    weakStep (sys_A.parallel sys_B) (prodPMF μ_A (PMF.pure s_B)) l (prodPMF ν_A μ_B) := by
  obtain ⟨m, m', h1, h2, h3⟩ := hA
  refine ⟨prodPMF m (PMF.pure s_B), prodPMF m' μ_B, ?_, ?_, ?_⟩
  · exact weakTau_parallel_left sys_A sys_B s_B h1
  · obtain ⟨p, hp, hm'eq⟩ := h2
    refine ⟨fun q => (p q.1).map (fun ζ => prodPMF ζ μ_B), ?_, ?_⟩
    · intro q hq ω hω
      rw [mem_support_prodPMF] at hq
      obtain ⟨hq1, hq2⟩ := hq
      rw [PMF.mem_support_pure_iff] at hq2
      rw [PMF.mem_support_map_iff] at hω
      obtain ⟨ζ, hζ, rfl⟩ := hω
      exact Or.inl ⟨hl, ζ, μ_B, hp q.1 hq1 ζ hζ, by rw [hq2]; exact hB, rfl⟩
    · rw [hm'eq]
      simp only [prodPMF, PMF.bind_map, PMF.bind_bind, PMF.pure_bind, id_eq, Function.comp_def]
  · rw [← bind_prodPMF_pure_right m' μ_B, ← bind_prodPMF_pure_right ν_A μ_B]
    exact weakTau_mix μ_B (fun b => prodPMF m' (PMF.pure b)) (fun b => prodPMF ν_A (PMF.pure b))
      (fun b _ => weakTau_parallel_left sys_A sys_B b h3)

end PLTS
