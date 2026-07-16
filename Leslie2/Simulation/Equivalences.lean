/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Simulation.SimDefs
import Leslie2.WeakClosure.WeakClosure
import Leslie2.Weak.WeakChar
import Leslie2.DistMonad.DistMonad

/-!
# Simulation equivalences

Two definitional correspondences identifying the weak / forward probabilistic
simulations with *strong* simulations into a transformed abstract system:

* `weakProbabilisticSimulation_iff_strong_weakClosure` — a weak simulation of
  `sys` by `sys'` is the same data as a strong simulation of `sys` by `sys'^w`;
* `probabilisticForwardSimulation_iff_strong_dist_weakClosure` — a forward
  simulation of `sys` by `sys'` is the same data as a strong simulation of
  `sys` by `𝒟(sys'^w)`.

The forward equivalence rests on the weak-transition characterizations in
`Weak/WeakChar.lean`; the weak equivalence holds by unfolding.
-/

open Stream'

namespace PLTS

variable {α β State State_C State_A Label : Type} [Silent Label]

/-- **(A1).** A `weakTau` from a distribution `μ` is a `hyperStep` over the weak
closure `sys^w`. -/
theorem hyperStep_weakClosure_of_weakTau {sys : System State Label}
    {μ ν : PMF State} {l : Label} (hl : (l = Silent.τ)) (h : weakTau sys μ ν) :
    hyperStep sys^w μ l ν := by
  obtain ⟨ρ, hρ, hν⟩ := weakTau_exists_pointwise h
  refine ⟨fun s => PMF.pure (ρ s), ?_, ?_⟩
  · intro s hs τ hτ
    rw [PMF.mem_support_pure_iff] at hτ; subst hτ
    exact Or.inl ⟨hl, hρ s hs⟩
  · rw [hν]; simp only [PMF.pure_bind, id_eq]

/-- **(A2).** A `hyperStep` over `sys^w` at an internal label collapses to a
single `weakTau` from the distribution. -/
theorem weakTau_of_hyperStep_weakClosure {sys : System State Label}
    {μ ν : PMF State} {l : Label} (hl : (l = Silent.τ)) (h : hyperStep sys^w μ l ν) :
    weakTau sys μ ν := by
  obtain ⟨p, hp, hν⟩ := h
  have hpt : ∀ s ∈ μ.support, weakTau sys (PMF.pure s) ((p s).bind id) := by
    intro s hs
    refine weakTau_bind ?_
    intro τ hτ
    rcases hp s hs τ hτ with ⟨_, hwt⟩ | ⟨hi, _⟩
    · exact hwt
    · exact absurd hl hi
  rw [hν]
  exact weakTau_of_pointwise _ hpt

/-- **(B1).** A `weakStep` from a distribution `μ` is a `hyperStep` over the weak
closure `sys^w`. -/
theorem hyperStep_weakClosure_of_weakStep {sys : System State Label}
    {μ ν : PMF State} {l : Label} (hl : ¬ (l = Silent.τ)) (h : weakStep sys μ l ν) :
    hyperStep sys^w μ l ν := by
  obtain ⟨ρ, hρ, hν⟩ := weakStep_exists_pointwise h
  refine ⟨fun s => PMF.pure (ρ s), ?_, ?_⟩
  · intro s hs τ hτ
    rw [PMF.mem_support_pure_iff] at hτ; subst hτ
    exact Or.inr ⟨hl, hρ s hs⟩
  · rw [hν]; simp only [PMF.pure_bind, id_eq]

/-- **(B2).** A `hyperStep` over `sys^w` at an external label collapses to a
single `weakStep` from the distribution. -/
theorem weakStep_of_hyperStep_weakClosure {sys : System State Label}
    {μ ν : PMF State} {l : Label} (hl : ¬ (l = Silent.τ)) (h : hyperStep sys^w μ l ν) :
    weakStep sys μ l ν := by
  obtain ⟨p, hp, hν⟩ := h
  have hpt : ∀ s ∈ μ.support, weakStep sys (PMF.pure s) l ((p s).bind id) := by
    intro s hs
    refine weakStep_bind ?_
    intro τ hτ
    rcases hp s hs τ hτ with ⟨hi, _⟩ | ⟨_, hws⟩
    · exact absurd hi hl
    · exact hws
  rw [hν]
  exact weakStep_of_pointwise _ hpt

/-! ### Forward simulation = strong simulation into `𝒟(·^w)`

The next block proves that a `ProbabilisticForwardSimulation` of `sys` by `sys'`
is the same data as a `StrongProbabilisticSimulation` of `sys` by `𝒟(sys'^w)`,
the distribution-monad lift of the weak closure of the abstract system.

Both notions carry the *same* relation `R : State_C → PMF State_A → Prop`
(`𝒟(sys'^w)`'s state type is `PMF State_A`, exactly the forward simulation's
abstract-distribution type). After lining up `init` and the (canonical)
internal/external split, the entire content is the transition-level correspondence

  `hyperStep sys'^w μ l ν  ↔  weakTau sys' μ ν` (internal `l`) /
                              `weakStep sys' μ l ν` (external `l`),

i.e. a weak transition from a distribution `μ` is exactly a convex combination
(`hyperStep` over `sys'^w`) of per-point weak transitions of `sys'`. The four
lemmas below are that correspondence; the `of_weak*` directions are
source-decomposition, the `weak*_of` directions need source-mixing plus the
target-convexity of `weakTau`/`weakStep` (closure under mixing schedulers from a
single point). -/


/-- **Probabilistic forward simulation = strong simulation into `𝒟(·^w)`.**
A `ProbabilisticForwardSimulation` of `sys` by `sys'` is the same data as a
`StrongProbabilisticSimulation` of `sys` by `𝒟(sys'^w)`. The two systems agree
on which labels are internal automatically, since the internal/external
classification is canonical (the silent label `τ`). -/
theorem probabilisticForwardSimulation_iff_strong_dist_weakClosure
    (sys : System State_C Label) (sys' : System State_A Label)
    (R : State_C → PMF State_A → Prop) :
    ProbabilisticForwardSimulation sys sys' R ↔
      StrongProbabilisticSimulation sys (𝒟(sys'^w)) R := by
  constructor
  · intro h
    refine ⟨?_, fun s_C μ_A hR l μ_C hstep => ?_⟩
    · -- init: the forward simulation's initial distribution is `pure sys'.init`.
      obtain ⟨μ_init, hsupp, hR⟩ := h.init
      have hμ : μ_init = PMF.pure sys'.init := by
        refine PMF.ext fun x => ?_
        by_cases hx : x = sys'.init
        · subst hx
          rw [PMF.pure_apply, if_pos rfl,
            ← μ_init.tsum_coe, tsum_eq_single sys'.init]
          intro b hb
          by_contra hbne
          exact hb (hsupp b hbne)
        · rw [PMF.pure_apply, if_neg hx]
          by_contra hbne
          exact hx (hsupp x hbne)
      rw [hμ] at hR
      exact hR
    · -- step: convert the forward weak transition into a `𝒟(sys'^w)` strong step.
      obtain ⟨ω, hPMFRel, hdisj⟩ := h.step s_C μ_A hR l μ_C hstep
      refine ⟨ω, ?_, hPMFRel⟩
      change hyperStep sys'^w μ_A l (ω.bind id)
      rcases hdisj with ⟨hi, hwt⟩ | ⟨hi, hws⟩
      · exact hyperStep_weakClosure_of_weakTau hi hwt
      · exact hyperStep_weakClosure_of_weakStep hi hws
  · intro h
    refine ⟨⟨PMF.pure sys'.init, ?_, h.init⟩, fun s_C μ_A hR l μ_C hstep => ?_⟩
    · intro s hs
      rwa [PMF.mem_support_pure_iff] at hs
    · -- step: convert the `𝒟(sys'^w)` strong step into a forward weak transition.
      obtain ⟨ω, hhyper, hPMFRel⟩ := h.step s_C μ_A hR l μ_C hstep
      refine ⟨ω, hPMFRel, ?_⟩
      change hyperStep sys'^w μ_A l (ω.bind id) at hhyper
      by_cases hil : (l = Silent.τ)
      · exact Or.inl ⟨hil, weakTau_of_hyperStep_weakClosure hil hhyper⟩
      · exact Or.inr ⟨hil, weakStep_of_hyperStep_weakClosure hil hhyper⟩


end PLTS
