/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Simulation.Defs
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

/-- **Weak simulation = strong simulation into the weak closure of the abstract
system.** A `WeakProbabilisticSimulation` of `sys` by `sys'` is the *same data*
as a `StrongProbabilisticSimulation` of `sys` by `sys'^w` (the weak closure of
the abstract system). The two systems agree on which labels are internal
automatically — the silent label `τ` is canonical (from `Silent Label`).

The reason this is purely definitional — with no weak-transition transfer
argument — is that *both* notions match a **strong** concrete step
`sys.step s_C l μ_C`: the concrete system is left unclosed. A weak simulation
matches such a step by a `weakTau`/`weakStep` from `PMF.pure s_A`, which is
exactly a strong step of `sys'^w`. The only bookkeeping is that
`WeakProbabilisticSimulation` keys its `weakTau`/`weakStep` case split on
`sys.internal` whereas `sys'^w` keys it on `sys'.internal`; these coincide
because the internal/external classification is canonical (the silent label
`τ`). -/
theorem weakProbabilisticSimulation_iff_strong_weakClosure
    (sys : System State_C Label) (sys' : System State_A Label)
    (R : State_C → State_A → Prop) :
    WeakProbabilisticSimulation sys sys' R ↔
      StrongProbabilisticSimulation sys (sys'^w) R := by
  constructor
  · intro h
    refine ⟨h.init, fun s_C s_A hR l μ_C hstep => ?_⟩
    obtain ⟨μ_A, hdisj, hrel⟩ := h.step s_C s_A hR l μ_C hstep
    refine ⟨μ_A, ?_, hrel⟩
    change ((l = Silent.τ) ∧ weakTau sys' (PMF.pure s_A) μ_A) ∨
         (¬ (l = Silent.τ) ∧ weakStep sys' (PMF.pure s_A) l μ_A)
    rcases hdisj with ⟨hi, hw⟩ | ⟨hi, hw⟩
    · exact Or.inl ⟨hi, hw⟩
    · exact Or.inr ⟨hi, hw⟩
  · intro h
    refine ⟨h.init, fun s_C s_A hR l μ_C hstep => ?_⟩
    obtain ⟨μ_A, hdisj, hrel⟩ := h.step s_C s_A hR l μ_C hstep
    refine ⟨μ_A, ?_, hrel⟩
    rcases hdisj with ⟨hi, hw⟩ | ⟨hi, hw⟩
    · exact Or.inl ⟨hi, hw⟩
    · exact Or.inr ⟨hi, hw⟩

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
