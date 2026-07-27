/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Simulation.SimDefs
import Leslie2.Weak.WeakChar
import Leslie2.Simulation.Equivalences
import Leslie2.Simulation.WeakTauLift
import Leslie2.Simulation.DistCollapse
import Leslie2.WeakClosure.HaltMass

/-!
# Weak-transition lifting for transitivity of forward simulation

Support for `ProbabilisticForwardSimulation.trans` (in `Results.lean`): the label-indexed
packaging `weakTransition` of the internal/external weak-transition split, and the crux lemma
`weakTransition_lift` that transports a weak transition on the (concrete) `sys_B` side through a
forward simulation to a weak transition on the (abstract) `sys_A` side.

## Reduction to a simulation-free weak-closure collapse

`weakTransition_lift` is reduced here through `weakTau_lift_pure` (lift a `weakTau` out of a single
concrete state `PMF.pure q_B`) to the single *simulation-free* lemma

  `weakClosure_weakTau_collapse` (`WeakClosure/HaltMass.lean`) — a run-to-halt internal weak
  transition of the weak closure `sys^w` collapses to one of the base `sys`,

whose genuine analytic crux (a.s.-halting *convergence* of the unfolded scheduler, phrased as the
`g`-integrated halt-mass conservation `expandSched_haltMass_g_eq`) is the last `sorry` in the
development. `weakTau_lift_pure` itself is discharged by the strong-simulation route
(`probabilisticForwardSimulation_iff_strong_dist_weakClosure` →
`StrongProbabilisticSimulation.weakTau_lift` → `weakTau_dist_collapse` → the collapse above), so the
simulation is fully handled off and only the closure-idempotence content remains. Everything else is
*coupling algebra*:

* `simulates_bind_mix` — `Simulates` is closed under mixing sources (posterior/Bayesian mixing of
  the per-source kernels), the convex-closure property the coupling form of `Simulates` was chosen
  for. `simulates_of_pmfRel` is the corollary turning a `sim.step` coupling into a `Simulates`.
* `weakStep_mix` — `weakStep` is closed under mixing sources (layerwise via `weakTau_mix` /
  `hyperStep_mix`).
* `weakTau_lift` — the *distribution* `weakTau` lift, from `weakTau_lift_pure` by decomposing the
  concrete source pointwise (`weakTau_exists_pointwise`) and re-mixing (`weakTau_mix`,
  `simulates_bind_mix`).
* `hyperStep_lift` — the external one-step layer, lifted directly through `sim.step`.
* `weakStep_lift` / `weakTransition_lift` — the external label and the internal/external split,
  by composing the three `weakStep` layers (`weakTau_trans`).

The composite relation `compRel` and the distribution-level relation `Simulates` live in
`Simulation/SimDefs.lean`; `Simulates` is the **coupling lifting** in disintegrated form, which is
what makes the mixing lemmas below hold for a non-convex `R`.
-/

namespace PLTS

variable {State_B State_A Label : Type} [Silent Label]

/-- The label-indexed weak transition packaged from the internal/external split used throughout
the simulation definitions: a `weakTau` on the silent label `τ`, a `weakStep` otherwise. This is
exactly the disjunction appearing in the `step` field of `ProbabilisticForwardSimulation`. -/
def weakTransition {S : Type} (sys : System S Label)
    (μ : PMF S) (l : Label) (ν : PMF S) : Prop :=
  ((l = Silent.τ) ∧ weakTau sys μ ν) ∨ (¬ (l = Silent.τ) ∧ weakStep sys μ l ν)

/-! ### Coupling / mixing algebra -/

/-- Binding against two kernels that agree on the source's support gives equal mixtures. -/
private theorem bind_eq_of_support {W α : Type} {μ : PMF W} {f g : W → PMF α}
    (h : ∀ w ∈ μ.support, f w = g w) : μ.bind f = μ.bind g := by
  refine PMF.ext (fun a => ?_)
  simp only [PMF.bind_apply]
  refine tsum_congr (fun w => ?_)
  by_cases hw : w ∈ μ.support
  · rw [h w hw]
  · rw [PMF.mem_support_iff, not_not] at hw
    rw [hw, zero_mul, zero_mul]

/-- Binding a constant kernel is the constant. -/
private theorem bind_const {W α : Type} (μ : PMF W) (ν : PMF α) :
    (μ.bind fun _ => ν) = ν := by
  refine PMF.ext (fun a => ?_)
  rw [PMF.bind_apply, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

/-- **Mixing for `Simulates`.** A `W`-indexed family of simulations `Simulates R (m w) (n w)`
combines into a single simulation from the mixed source `Ω.bind m` to the mixed target `Ω.bind n`,
via Bayesian-posterior mixing of the per-source mixture kernels. This is the convex-closure
property that the *coupling* form of `Simulates` enjoys (and the functional form does not). -/
theorem simulates_bind_mix {W S T : Type} {R : S → PMF T → Prop}
    (Ω : PMF W) (m : W → PMF S) (n : W → PMF T)
    (h : ∀ w ∈ Ω.support, Simulates R (m w) (n w)) :
    Simulates R (Ω.bind m) (Ω.bind n) := by
  classical
  -- per-source mixture kernel witnessing each `Simulates R (m w) (n w)`
  set Kw : W → S → PMF (PMF T) :=
    fun w => if hw : w ∈ Ω.support then (h w hw).choose else fun _ => PMF.pure (n w) with hKw
  have hKw_spec : ∀ w (hw : w ∈ Ω.support),
      n w = (m w).bind (fun s => (Kw w s).bind id) ∧
        ∀ s ∈ (m w).support, ∀ ρ ∈ (Kw w s).support, R s ρ := by
    intro w hw
    have hc := (h w hw).choose_spec
    have he : Kw w = (h w hw).choose := by rw [hKw]; exact dif_pos hw
    rw [he]; exact hc
  set num : S → W → ENNReal := fun s w => Ω w * (m w) s with hnum
  have hnumsum : ∀ s, (∑' w, num s w) = (Ω.bind m) s := by
    intro s; rw [hnum, PMF.bind_apply]
  set post : (s : S) → (Ω.bind m) s ≠ 0 → PMF W :=
    fun s hs => PMF.normalize (num s) (by rw [hnumsum]; exact hs)
      (by rw [hnumsum]; exact (Ω.bind m).apply_ne_top s) with hpost
  have hZ : ∀ s (hs : (Ω.bind m) s ≠ 0) w, (Ω.bind m) s * (post s hs) w = num s w := by
    intro s hs w
    rw [hpost, PMF.normalize_apply, hnumsum, ← mul_assoc, mul_comm ((Ω.bind m) s) (num s w),
      mul_assoc, ENNReal.mul_inv_cancel hs ((Ω.bind m).apply_ne_top s), mul_one]
  set K : S → PMF (PMF T) :=
    fun s => if hs : (Ω.bind m) s = 0 then PMF.pure (Ω.bind n)
      else (post s hs).bind (fun w => Kw w s) with hK
  have hnum_supp : ∀ s w, num s w ≠ 0 → w ∈ Ω.support ∧ s ∈ (m w).support := by
    intro s w hne
    rw [hnum, mul_ne_zero_iff] at hne
    exact ⟨(PMF.mem_support_iff Ω w).mpr hne.1, (PMF.mem_support_iff (m w) s).mpr hne.2⟩
  refine ⟨K, ?_, ?_⟩
  · -- `Ω.bind n = (Ω.bind m).bind (fun s => (K s).bind id)`
    refine PMF.ext (fun y => ?_)
    have hterm : ∀ s, (Ω.bind m) s * ((K s).bind id) y
        = ∑' w, num s w * ((Kw w s).bind id) y := by
      intro s
      by_cases hs : (Ω.bind m) s = 0
      · rw [hs, zero_mul]
        refine (ENNReal.tsum_eq_zero.mpr (fun w => ?_)).symm
        have hz : (∑' w, num s w) = 0 := by rw [hnumsum]; exact hs
        rw [ENNReal.tsum_eq_zero] at hz
        rw [hz w, zero_mul]
      · have hKs : K s = (post s hs).bind (fun w => Kw w s) := by rw [hK]; exact dif_neg hs
        rw [hKs, PMF.bind_bind, PMF.bind_apply (post s hs), ← ENNReal.tsum_mul_left]
        refine tsum_congr (fun w => ?_)
        rw [← mul_assoc, hZ s hs w]
    have hRHS : ((Ω.bind m).bind (fun s => (K s).bind id)) y
        = ∑' s, ∑' w, num s w * ((Kw w s).bind id) y := by
      rw [PMF.bind_apply]; exact tsum_congr hterm
    have hLHS : (Ω.bind n) y = ∑' w, ∑' s, num s w * ((Kw w s).bind id) y := by
      rw [PMF.bind_apply]
      refine tsum_congr (fun w => ?_)
      by_cases hw : w ∈ Ω.support
      · rw [(hKw_spec w hw).1, PMF.bind_apply, ← ENNReal.tsum_mul_left]
        refine tsum_congr (fun s => ?_)
        simp only [hnum]; ring
      · rw [PMF.mem_support_iff, not_not] at hw
        rw [hw, zero_mul]
        refine (ENNReal.tsum_eq_zero.mpr (fun s => ?_)).symm
        simp only [hnum, hw, zero_mul]
    rw [hLHS, hRHS, ENNReal.tsum_comm]
  · -- support in `R`
    intro s hs ρ hρ
    rw [PMF.mem_support_iff] at hs
    rw [hK] at hρ; simp only [dif_neg hs] at hρ
    rw [PMF.mem_support_bind_iff] at hρ
    obtain ⟨w, hw_post, hρ⟩ := hρ
    have hnumne : num s w ≠ 0 := by
      rw [hpost, PMF.mem_support_normalize_iff] at hw_post; exact hw_post
    obtain ⟨hwΩ, hsm⟩ := hnum_supp s w hnumne
    exact (hKw_spec w hwΩ).2 s hsm ρ hρ

/-- A `sim.step`-style coupling `PMFRel R μ ω` yields a `Simulates R μ (ω.bind id)`. -/
theorem simulates_of_pmfRel {S T : Type} {R : S → PMF T → Prop}
    {μ : PMF S} {ω : PMF (PMF T)} (h : PMFRel R μ ω) :
    Simulates R μ (ω.bind id) := by
  obtain ⟨Ω, hfst, hsnd, hsupp⟩ := h
  have key : Simulates R (Ω.bind (fun p => PMF.pure p.1)) (Ω.bind (fun p => p.2)) := by
    refine simulates_bind_mix Ω (fun p => PMF.pure p.1) (fun p => p.2) (fun p hp => ?_)
    refine ⟨fun _ => PMF.pure p.2, ?_, ?_⟩
    · simp only [PMF.pure_bind, id_eq]
    · intro s hs ρ hρ
      rw [PMF.mem_support_pure_iff] at hs hρ
      subst hs; subst hρ
      exact hsupp p hp
  have h1 : Ω.bind (fun p => PMF.pure p.1) = μ := by
    rw [← hfst]
    refine PMF.ext (fun a => ?_)
    rw [PMF.bind_apply, PMF.map_apply]
    refine tsum_congr (fun p => ?_)
    by_cases hpa : a = p.1
    · rw [PMF.pure_apply, if_pos hpa, if_pos hpa, mul_one]
    · rw [PMF.pure_apply, if_neg hpa, if_neg hpa, mul_zero]
  have h2 : Ω.bind (fun p => p.2) = ω.bind id := by rw [← hsnd, PMF.bind_map]; rfl
  rw [h1, h2] at key; exact key

/-- **Mixing for `weakStep`.** A `W`-indexed family of weak steps combines into one weak step from
the mixed source to the mixed target, layerwise via `weakTau_mix` and `hyperStep_mix`. -/
theorem weakStep_mix {S W : Type} {sys : System S Label} {l : Label}
    (q : PMF W) (m ν : W → PMF S)
    (H : ∀ w ∈ q.support, weakStep sys (m w) l (ν w)) :
    weakStep sys (q.bind m) l (q.bind ν) := by
  classical
  set pre : W → PMF S :=
    fun w => if hw : w ∈ q.support then (H w hw).choose else m w with hpre
  set post : W → PMF S :=
    fun w => if hw : w ∈ q.support then (H w hw).choose_spec.choose else m w with hpost
  have hspec : ∀ w (hw : w ∈ q.support),
      weakTau sys (m w) (pre w) ∧ hyperStep sys (pre w) l (post w)
        ∧ weakTau sys (post w) (ν w) := by
    intro w hw
    have hc := (H w hw).choose_spec.choose_spec
    have h1 : pre w = (H w hw).choose := by rw [hpre]; exact dif_pos hw
    have h2 : post w = (H w hw).choose_spec.choose := by rw [hpost]; exact dif_pos hw
    rw [h1, h2]; exact hc
  exact ⟨q.bind pre, q.bind post,
    weakTau_mix q m pre (fun w hw => (hspec w hw).1),
    hyperStep_mix q pre post (fun w hw => (hspec w hw).2.1),
    weakTau_mix q post ν (fun w hw => (hspec w hw).2.2)⟩

/-! ### The lift, reduced to a single-state `weakTau` -/

variable {sys_B : System State_B Label} {sys_A : System State_A Label}
  {R_AB : State_B → PMF State_A → Prop}

/-! ### The weak-closure `weakTau` collapse (the convergence crux, `G1`)

The single remaining analytic content is isolated as the *simulation-free* lemma
`weakClosure_weakTau_collapse` (`weakTau sys^w μ ν → weakTau sys μ ν`) in
`WeakClosure/HaltMass.lean`: a run-to-halt internal weak transition of the weak closure `sys^w`
collapses to one of the base `sys`. That file reduces it (via the `expandSched` unfolding, slicing
`expandSched_haltMass_g_eq` at `g = 1` and `g = [· = x]`, and the `{sys with init := s}`
relabeling) to one analytic `sorry`: the a.s.-halting conservation `expandSched_haltMass_g_eq`. -/

/-- **Single-state `weakTau` lift (reduced).**

If the concrete state `q_B` is related to the abstract distribution `μ_A` (`R_AB q_B μ_A`), and
`PMF.pure q_B` performs an internal weak transition to `ν_B` in `sys_B`, then `μ_A` performs an
internal weak transition to some `ν_A` in `sys_A` that simulates `ν_B`.

Reduced to the *simulation-free* `weakClosure_weakTau_collapse` (`G1`) by the strong-simulation
route: a forward simulation is a strong simulation into `𝒟(sys_A^w)`
(`probabilisticForwardSimulation_iff_strong_dist_weakClosure`); lift the single-state `weakTau`
through it (`StrongProbabilisticSimulation.weakTau_lift`, matching end-states by a `PMFRel`
coupling); collapse `𝒟(sys_A^w) → sys_A^w` (`weakTau_dist_collapse`) and then `sys_A^w → sys_A`
(`G1`). The `Simulates` conclusion is the coupling read through `simulates_of_pmfRel`. -/
theorem weakTau_lift_pure
    (sim : ProbabilisticForwardSimulation sys_B sys_A R_AB)
    {q_B : State_B} {ν_B : PMF State_B} {μ_A : PMF State_A}
    (hR : R_AB q_B μ_A)
    (hweak : weakTau sys_B (PMF.pure q_B) ν_B) :
    ∃ ν_A, weakTau sys_A μ_A ν_A ∧ Simulates R_AB ν_B ν_A := by
  -- forward simulation ⟺ strong simulation into `𝒟(sys_A^w)`
  have sim' : StrongProbabilisticSimulation sys_B (𝒟(sys_A^w)) R_AB :=
    (probabilisticForwardSimulation_iff_strong_dist_weakClosure sys_B sys_A R_AB).mp sim
  -- lift the single-state `weakTau` through the strong simulation (end-states coupled by `PMFRel`)
  obtain ⟨Ν, hwtD, hcoup⟩ := sim'.weakTau_lift hR hweak
  -- collapse `𝒟(sys_A^w)` → `sys_A^w` (`weakTau_dist_collapse`), then `sys_A^w` → `sys_A` (`G1`)
  refine ⟨Ν.bind id, weakClosure_weakTau_collapse (weakTau_dist_collapse hwtD), ?_⟩
  exact simulates_of_pmfRel hcoup

/-- Extract the pointwise membership from the standard `(K0)`-joint `Ω`. -/
private theorem mem_bindMap_support {μ_B : PMF State_B} {K0 : State_B → PMF (PMF State_A)}
    {p : State_B × PMF State_A}
    (hp : p ∈ (μ_B.bind (fun s => (K0 s).map (Prod.mk s))).support) :
    p.1 ∈ μ_B.support ∧ p.2 ∈ (K0 p.1).support := by
  rw [PMF.mem_support_bind_iff] at hp
  obtain ⟨s, hs, hp⟩ := hp
  rw [PMF.mem_support_map_iff] at hp
  obtain ⟨ρ, hρ, rfl⟩ := hp
  exact ⟨hs, hρ⟩

/-- **Distribution `weakTau` lift.** The distribution-level internal case, reduced to
`weakTau_lift_pure` by decomposing the concrete source pointwise and re-mixing. -/
theorem weakTau_lift
    (sim : ProbabilisticForwardSimulation sys_B sys_A R_AB)
    {μ_B ν_B : PMF State_B} {μ_A : PMF State_A}
    (hsim : Simulates R_AB μ_B μ_A)
    (hweak : weakTau sys_B μ_B ν_B) :
    ∃ ν_A, weakTau sys_A μ_A ν_A ∧ Simulates R_AB ν_B ν_A := by
  classical
  obtain ⟨K0, hμA, hK0⟩ := hsim
  obtain ⟨ρ_B, hρB, hνB⟩ := weakTau_exists_pointwise hweak
  set Ω : PMF (State_B × PMF State_A) :=
    μ_B.bind (fun s => (K0 s).map (Prod.mk s)) with hΩ
  have hμA' : μ_A = Ω.bind (fun p => p.2) := by
    rw [hμA, hΩ, PMF.bind_bind]
    refine bind_eq_of_support (fun s _ => ?_)
    rw [PMF.bind_map]; rfl
  have hνB' : ν_B = Ω.bind (fun p => ρ_B p.1) := by
    rw [hνB, hΩ, PMF.bind_bind]
    refine bind_eq_of_support (fun s _ => ?_)
    rw [PMF.bind_map]
    change ρ_B s = (K0 s).bind (fun _ => ρ_B s)
    rw [bind_const]
  have hpt : ∀ p ∈ Ω.support,
      ∃ w, weakTau sys_A p.2 w ∧ Simulates R_AB (ρ_B p.1) w := by
    intro p hp
    obtain ⟨hs, hρ⟩ := mem_bindMap_support (hΩ ▸ hp)
    exact weakTau_lift_pure sim (hK0 p.1 hs p.2 hρ) (hρB p.1 hs)
  set νA : (State_B × PMF State_A) → PMF State_A :=
    fun p => if hp : p ∈ Ω.support then (hpt p hp).choose else PMF.pure sys_A.init with hνAdef
  have hνA_eq : ∀ p (hp : p ∈ Ω.support), νA p = (hpt p hp).choose :=
    fun p hp => by rw [hνAdef]; exact dif_pos hp
  refine ⟨Ω.bind νA, ?_, ?_⟩
  · rw [hμA']
    exact weakTau_mix Ω (fun p => p.2) νA
      (fun p hp => by rw [hνA_eq p hp]; exact (hpt p hp).choose_spec.1)
  · rw [hνB']
    exact simulates_bind_mix Ω (fun p => ρ_B p.1) νA
      (fun p hp => by rw [hνA_eq p hp]; exact (hpt p hp).choose_spec.2)

/-- **External one-step lift.** A `hyperStep` at an external label, lifted through a forward
simulation: it becomes a `weakStep` on the abstract side, matched by `sim.step` per source point
(no run-to-halt involved). -/
theorem hyperStep_lift
    (sim : ProbabilisticForwardSimulation sys_B sys_A R_AB)
    {m m' : PMF State_B} {n : PMF State_A} {l : Label} (hl : ¬ (l = Silent.τ))
    (hsim : Simulates R_AB m n)
    (hhyper : hyperStep sys_B m l m') :
    ∃ n', weakStep sys_A n l n' ∧ Simulates R_AB m' n' := by
  classical
  obtain ⟨K0, hn, hK0⟩ := hsim
  obtain ⟨p, hp_step, hm'⟩ := hhyper
  set Ω : PMF (State_B × PMF State_A) :=
    m.bind (fun s => (K0 s).map (Prod.mk s)) with hΩ
  have hn' : n = Ω.bind (fun q => q.2) := by
    rw [hn, hΩ, PMF.bind_bind]
    refine bind_eq_of_support (fun s _ => ?_)
    rw [PMF.bind_map]; rfl
  have hm'' : m' = Ω.bind (fun q => (p q.1).bind id) := by
    rw [hm', hΩ, PMF.bind_bind]
    refine bind_eq_of_support (fun s _ => ?_)
    rw [PMF.bind_map]
    change (p s).bind id = (K0 s).bind (fun _ => (p s).bind id)
    rw [bind_const]
  have hpt : ∀ q ∈ Ω.support,
      ∃ t, weakStep sys_A q.2 l t ∧ Simulates R_AB ((p q.1).bind id) t := by
    intro q hq
    obtain ⟨hs, hd⟩ := mem_bindMap_support (hΩ ▸ hq)
    have hinner : ∀ μ ∈ (p q.1).support,
        ∃ u, weakStep sys_A q.2 l u ∧ Simulates R_AB μ u := by
      intro μ hμ
      obtain ⟨ω', hPMFRel', hdisj⟩ :=
        sim.step q.1 q.2 (hK0 q.1 hs q.2 hd) l μ (hp_step q.1 hs μ hμ)
      rcases hdisj with ⟨hτ, _⟩ | ⟨_, hws⟩
      · exact absurd hτ hl
      · exact ⟨ω'.bind id, hws, simulates_of_pmfRel hPMFRel'⟩
    set uu : PMF State_B → PMF State_A :=
      fun μ => if hμ : μ ∈ (p q.1).support then (hinner μ hμ).choose else PMF.pure sys_A.init
      with huudef
    have huu_eq : ∀ μ (hμ : μ ∈ (p q.1).support), uu μ = (hinner μ hμ).choose :=
      fun μ hμ => by rw [huudef]; exact dif_pos hμ
    refine ⟨(p q.1).bind uu, ?_, ?_⟩
    · have hmix := weakStep_mix (p q.1) (fun _ => q.2) uu
        (fun μ hμ => by rw [huu_eq μ hμ]; exact (hinner μ hμ).choose_spec.1)
      rwa [bind_const] at hmix
    · exact simulates_bind_mix (p q.1) id uu
        (fun μ hμ => by rw [huu_eq μ hμ]; exact (hinner μ hμ).choose_spec.2)
  set tt : (State_B × PMF State_A) → PMF State_A :=
    fun q => if hq : q ∈ Ω.support then (hpt q hq).choose else PMF.pure sys_A.init with httdef
  have htt_eq : ∀ q (hq : q ∈ Ω.support), tt q = (hpt q hq).choose :=
    fun q hq => by rw [httdef]; exact dif_pos hq
  refine ⟨Ω.bind tt, ?_, ?_⟩
  · rw [hn']
    exact weakStep_mix Ω (fun q => q.2) tt
      (fun q hq => by rw [htt_eq q hq]; exact (hpt q hq).choose_spec.1)
  · rw [hm'']
    exact simulates_bind_mix Ω (fun q => (p q.1).bind id) tt
      (fun q hq => by rw [htt_eq q hq]; exact (hpt q hq).choose_spec.2)

/-- **External `weakStep` lift.** Compose the three layers `τ-closure → hyper-step → τ-closure`,
lifting each and stitching with `weakTau_trans`. -/
theorem weakStep_lift
    (sim : ProbabilisticForwardSimulation sys_B sys_A R_AB)
    {μ_B ν_B : PMF State_B} {μ_A : PMF State_A} {l : Label} (hl : ¬ (l = Silent.τ))
    (hsim : Simulates R_AB μ_B μ_A)
    (hweak : weakStep sys_B μ_B l ν_B) :
    ∃ ν_A, weakStep sys_A μ_A l ν_A ∧ Simulates R_AB ν_B ν_A := by
  obtain ⟨m1, m1', hpre, hmid, hpost⟩ := hweak
  obtain ⟨n1, hwt1, hsim1⟩ := weakTau_lift sim hsim hpre
  obtain ⟨n1', hws, hsim2⟩ := hyperStep_lift sim hl hsim1 hmid
  obtain ⟨ν_A, hwt2, hsim3⟩ := weakTau_lift sim hsim2 hpost
  obtain ⟨a, a', hpreA, hmidA, hpostA⟩ := hws
  exact ⟨ν_A, ⟨a, a', weakTau_trans hwt1 hpreA, hmidA, weakTau_trans hpostA hwt2⟩, hsim3⟩

/-- **Weak-transition lifting through a forward simulation (the crux, reduced).**

If `μ_A` simulates `μ_B` and `μ_B` performs a weak `l`-transition to `ν_B` in `sys_B`, then `μ_A`
performs a weak `l`-transition to some `ν_A` in `sys_A` that simulates `ν_B`. The internal case is
`weakTau_lift`; the external case is `weakStep_lift`. Both bottom out at `weakTau_lift_pure`. -/
theorem weakTransition_lift
    (sim_AB : ProbabilisticForwardSimulation sys_B sys_A R_AB)
    {μ_B ν_B : PMF State_B} {μ_A : PMF State_A} {l : Label}
    (hsim : Simulates R_AB μ_B μ_A)
    (hweak : weakTransition sys_B μ_B l ν_B) :
    ∃ ν_A, weakTransition sys_A μ_A l ν_A ∧ Simulates R_AB ν_B ν_A := by
  rcases hweak with ⟨hτ, hwt⟩ | ⟨hτ, hws⟩
  · obtain ⟨ν_A, hwtA, hsimA⟩ := weakTau_lift sim_AB hsim hwt
    exact ⟨ν_A, Or.inl ⟨hτ, hwtA⟩, hsimA⟩
  · obtain ⟨ν_A, hwsA, hsimA⟩ := weakStep_lift sim_AB hτ hsim hws
    exact ⟨ν_A, Or.inr ⟨hτ, hwsA⟩, hsimA⟩

end PLTS
