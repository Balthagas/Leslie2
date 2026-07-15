/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Simulation.Soundness
import Leslie2.Simulation.Transitivity
import Leslie2.DistMonad.DistTrace
import Leslie2.ProcessAlgebra.Parallel
import Leslie2.ProcessAlgebra.Interleave
import Leslie2.ProcessAlgebra.Abstract

/-!
# The five main results

This file collects the five headline theorems about **probabilistic forward simulation**; all of
their supporting machinery lives under the themed sub-folders (`Systems/`, `Weak/`, `DistMonad/`,
`WeakClosure/`, `Simulation/`, `ProcessAlgebra/`).

1. `ProbabilisticForwardSimulation.achievableTraceDists_subset` — **soundness**: a forward
   simulation of `sys_C` by `sys_A` makes every trace distribution of `sys_C` reproducible by
   `sys_A`.
2. `ProbabilisticForwardSimulation.trans` — **transitivity**: forward simulation composes, along
   the composite relation `compRel`.
3. `ProbabilisticForwardSimulation.parallel_right` — **precongruence for `parallel`**.
4. `ProbabilisticForwardSimulation.interleave` — **precongruence for `interleave`**.
5. `ProbabilisticForwardSimulation.abstract` — **precongruence for `abstract`**.

The non-headline strong- and weak-simulation soundness results are in
`Simulation/Soundness.lean`.
-/

open Stream'
open scoped BigOperators

namespace PLTS

/-! ## 1. Soundness -/

section Soundness

variable {State_C State_A Label : Type} [Silent Label]

/-- **Probabilistic forward simulation preserves achievable trace distributions** (soundness): if
`sys_C` is forward-simulated by `sys_A`, then every trace distribution achievable by `sys_C` is
achievable by `sys_A`. -/
theorem ProbabilisticForwardSimulation.achievableTraceDists_subset
    {sys_C : System State_C Label} {sys_A : System State_A Label}
    {R : State_C → PMF State_A → Prop}
    (sim : ProbabilisticForwardSimulation sys_C sys_A R) :
    achievableTraceDists sys_C ⊆ achievableTraceDists sys_A := by
  -- A forward simulation is a strong simulation into `𝒟(sys_A^w)`; both `·^w` and `𝒟(·)`
  -- preserve traces.
  rw [weakClosure_traceProb_eq sys_A, dist_traceProb_eq (sys_A^w)]
  exact ((probabilisticForwardSimulation_iff_strong_dist_weakClosure sys_C sys_A R).mp
    sim).achievableTraceDists_subset

end Soundness

/-! ## 2. Transitivity -/

section Transitivity

variable {State_C State_B State_A Label : Type} [Silent Label]
  {sys_C : System State_C Label} {sys_B : System State_B Label}
  {sys_A : System State_A Label}
  {R_BC : State_C → PMF State_B → Prop} {R_AB : State_B → PMF State_A → Prop}

/-- **Transitivity of probabilistic forward simulation.** If `sys_B` simulates `sys_C` and `sys_A`
simulates `sys_B`, then `sys_A` simulates `sys_C` along the composite relation `compRel R_BC R_AB`.
Proven from `weakTransition_lift`. -/
theorem ProbabilisticForwardSimulation.trans
    (sim_BC : ProbabilisticForwardSimulation sys_C sys_B R_BC)
    (sim_AB : ProbabilisticForwardSimulation sys_B sys_A R_AB) :
    ProbabilisticForwardSimulation sys_C sys_A (compRel R_BC R_AB) := by
  refine ⟨?_, ?_⟩
  · -- init: bind the concrete initial distribution against the constant abstract one.
    obtain ⟨μ_B, hμ_B_supp, hR_BC⟩ := sim_BC.init
    obtain ⟨μ_A0, hμ_A0_supp, hR_AB⟩ := sim_AB.init
    refine ⟨μ_B.bind (fun _ => μ_A0), ?_, μ_B, hR_BC, fun _ => μ_A0, rfl, ?_⟩
    · intro s_A hs
      rw [PMF.mem_support_bind_iff] at hs
      obtain ⟨_, _, hs2⟩ := hs
      exact hμ_A0_supp s_A hs2
    · intro q_B hq
      rw [hμ_B_supp q_B hq]
      exact hR_AB
  · -- step
    intro s_C μ_A hR l μ_C hstep
    obtain ⟨μ_B, hR_BC, hsimBA⟩ := hR
    -- Match the concrete `sys_C`-step on the `sys_B` side (a weak transition out of `μ_B`).
    obtain ⟨ω_B, hPMFRel_B, hweakB_raw⟩ := sim_BC.step s_C μ_B hR_BC l μ_C hstep
    have hweakB : weakTransition sys_B μ_B l (ω_B.bind id) := hweakB_raw
    -- Lift that `sys_B` weak transition to a `sys_A` weak transition (the crux).
    obtain ⟨ν_A, hweakA, g, hνA, hg_supp⟩ := weakTransition_lift sim_AB hsimBA hweakB
    obtain ⟨Ω_B, hfst_B, hsnd_B, hsupp_B⟩ := hPMFRel_B
    -- Push each `sys_B`-coupled distribution forward through `g` to an `sys_A` one.
    refine ⟨ω_B.map (fun ρ => ρ.bind g), ?_, ?_⟩
    · -- `PMFRel (compRel R_BC R_AB) μ_C (ω_B.map (·.bind g))`, witnessed by pushing `Ω_B`.
      refine ⟨Ω_B.map (fun p => (p.1, p.2.bind g)), ?_, ?_, ?_⟩
      · rw [PMF.map_comp]; exact hfst_B
      · rw [← hsnd_B, PMF.map_comp, PMF.map_comp]; rfl
      · intro p hp
        rw [PMF.mem_support_map_iff] at hp
        obtain ⟨p', hp', rfl⟩ := hp
        refine ⟨p'.2, hsupp_B p' hp', g, rfl, ?_⟩
        intro s hs
        apply hg_supp
        rw [PMF.mem_support_bind_iff]
        refine ⟨p'.2, ?_, hs⟩
        rw [← hsnd_B, PMF.mem_support_map_iff]
        exact ⟨p', hp', rfl⟩
    · -- the weak `sys_A`-transition, after identifying `(ω_B.map (·.bind g)).bind id = ν_A`.
      have hbind : (ω_B.map (fun ρ => ρ.bind g)).bind id = ν_A := by
        rw [hνA, PMF.bind_map, PMF.bind_bind]; rfl
      rw [hbind]
      exact hweakA

end Transitivity

/-! ## 3. Precongruence for parallel composition -/

section Parallel

variable {State_C State_A State_B Label : Type} [Silent Label]
  {sys_C : System State_C Label} {sys_A : System State_A Label}
  {R : State_C → PMF State_A → Prop}

/-- **Precongruence (right).** If `sys_A` simulates `sys_C`, then `sys_A ∥ sys_B` simulates
`sys_C ∥ sys_B` for every `sys_B`, along `parallelRel R`. Proven from the three lift lemmas. -/
theorem ProbabilisticForwardSimulation.parallel_right
    (sim : ProbabilisticForwardSimulation sys_C sys_A R) (sys_B : System State_B Label) :
    ProbabilisticForwardSimulation (sys_C.parallel sys_B) (sys_A.parallel sys_B)
      (parallelRel R) := by
  refine ⟨?_, ?_⟩
  · -- init
    obtain ⟨μ_A0, hsupp, hR0⟩ := sim.init
    refine ⟨prodPMF μ_A0 (PMF.pure sys_B.init), ?_, μ_A0, hR0, rfl⟩
    intro x hx
    rw [prodPMF_pure_right, PMF.mem_support_map_iff] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hsupp a ha]; rfl
  · -- step
    rintro ⟨s_C, s_B⟩ ν ⟨μ_A, hR, rfl⟩ l μ_CB hstep
    rw [System.parallel_step] at hstep
    rcases hstep with ⟨hl, μ_C, μ_B, hC, hB, rfl⟩ | ⟨hl, μ_C, hC, rfl⟩ | ⟨hl, μ_B, hB, rfl⟩
    · -- synchronised visible step
      obtain ⟨ω_A, hPMFRelA, hdisj⟩ := sim.step s_C μ_A hR l μ_C hC
      rcases hdisj with ⟨hτ, _⟩ | ⟨_, hstepA⟩
      · exact absurd hτ hl
      refine ⟨(prodPMF ω_A μ_B).map (fun p => prodPMF p.1 (PMF.pure p.2)), ?_, ?_⟩
      · exact pmfRel_parallel_sync μ_B hPMFRelA
      · rw [bindId_sync]
        exact Or.inr ⟨hl, weakStep_parallel_sync sys_A sys_B hl hstepA hB⟩
    · -- τ-left interleaving (sys_C moves)
      obtain ⟨ω_A, hPMFRelA, hdisj⟩ := sim.step s_C μ_A hR l μ_C hC
      rcases hdisj with ⟨_, htauA⟩ | ⟨hτ, _⟩
      · refine ⟨ω_A.map (fun ρ => prodPMF ρ (PMF.pure s_B)), ?_, ?_⟩
        · exact pmfRel_parallel_left s_B hPMFRelA
        · rw [bindId_left]
          exact Or.inl ⟨hl, weakTau_parallel_left sys_A sys_B (PMF.pure s_B) htauA⟩
      · exact absurd hl hτ
    · -- τ-right interleaving (sys_B moves)
      refine ⟨μ_B.map (fun b => prodPMF μ_A (PMF.pure b)), ?_, ?_⟩
      · exact pmfRel_parallel_right μ_B hR
      · rw [bindId_right]
        exact Or.inl ⟨hl, weakTau_parallel_right sys_A sys_B μ_A (weakTau_of_step hl hB)⟩

end Parallel

/-! ## 4. Precongruence for `interleave` -/

section Interleave

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {State_C State_A : ι → Type} {Label : Type} [Silent Label]
  {sysC : ∀ i, System (State_C i) Label} {sysA : ∀ i, System (State_A i) Label}
  {R : ∀ i, State_C i → PMF (State_A i) → Prop}

/-- **Precongruence for `interleave`.** If `sysA i` simulates `sysC i` for every component `i`, then
`interleave sysA` simulates `interleave sysC`, along `interleaveRel R`. Proven from the two lift
lemmas. -/
theorem ProbabilisticForwardSimulation.interleave
    (sim : ∀ i, ProbabilisticForwardSimulation (sysC i) (sysA i) (R i)) :
    ProbabilisticForwardSimulation (System.interleave sysC) (System.interleave sysA)
      (interleaveRel R) := by
  refine ⟨?_, ?_⟩
  · -- init
    choose μ_0 hsupp0 hR0 using fun i => (sim i).init
    refine ⟨piPMF μ_0, ?_, μ_0, hR0, rfl⟩
    intro f hf
    rw [mem_support_piPMF] at hf
    funext i
    exact hsupp0 i (f i) (hf i)
  · -- step
    rintro s ν ⟨μ_, hR, rfl⟩ l μ_CB hstep
    rw [System.interleave_step] at hstep
    obtain ⟨i, μ_Ci, hCi, rfl⟩ := hstep
    obtain ⟨ω_Ai, hPMFReli, hdisj⟩ := (sim i).step (s i) (μ_ i) (hR i) l μ_Ci hCi
    refine ⟨ω_Ai.map (fun ρ => piPMF (Function.update μ_ i ρ)), ?_, ?_⟩
    · exact pmfRel_interleave i s μ_ hR hPMFReli
    · rw [bindId_update]
      rcases hdisj with ⟨hτ, htau⟩ | ⟨hτ, hstepw⟩
      · exact Or.inl ⟨hτ, weakTau_interleave i μ_ htau⟩
      · exact Or.inr ⟨hτ, weakStep_interleave i l μ_ hstepw⟩

end Interleave

/-! ## 5. Precongruence for abstraction -/

section Abstract

variable {State_C State_A Label : Type} [Silent Label]
  {sys_C : System State_C Label} {sys_A : System State_A Label}
  {R : State_C → PMF State_A → Prop}

/-- **Precongruence for abstraction.** If `sys_A` simulates `sys_C`, then `sys_A.abstract L`
simulates `sys_C.abstract L` along the same relation `R`. Proven from the three lift lemmas. -/
theorem ProbabilisticForwardSimulation.abstract
    (sim : ProbabilisticForwardSimulation sys_C sys_A R) (L : Set Label) :
    ProbabilisticForwardSimulation (sys_C.abstract L) (sys_A.abstract L) R := by
  refine ⟨sim.init, ?_⟩
  rintro s_C μ_A hR l' μ_C hstep
  rw [System.abstract_step] at hstep
  rcases hstep with ⟨hl'τ, l, hlL, hstep⟩ | ⟨hl'L, hstep⟩
  · -- the concrete label `l ∈ L` is hidden, so `l' = τ`
    obtain ⟨ω, hPMFRel, hdisj⟩ := sim.step s_C μ_A hR l μ_C hstep
    refine ⟨ω, hPMFRel, Or.inl ⟨hl'τ, ?_⟩⟩
    rcases hdisj with ⟨_, wtau⟩ | ⟨_, wstep⟩
    · exact weakTau_abstract sys_A L wtau
    · exact weakTau_of_weakStep_mem sys_A L hlL wstep
  · -- the concrete label `l' ∉ L` is unchanged
    obtain ⟨ω, hPMFRel, hdisj⟩ := sim.step s_C μ_A hR l' μ_C hstep
    rcases hdisj with ⟨hl'τ, wtau⟩ | ⟨hl'τ, wstep⟩
    · exact ⟨ω, hPMFRel, Or.inl ⟨hl'τ, weakTau_abstract sys_A L wtau⟩⟩
    · exact ⟨ω, hPMFRel, Or.inr ⟨hl'τ, weakStep_abstract sys_A L hl'L wstep⟩⟩

end Abstract

end PLTS
