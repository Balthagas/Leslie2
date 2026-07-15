/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2Extra.Fairness.Construction.DistFairHalt

/-!
# Barycenter normalisation of abstract witnesses into `𝒟f(sys, F)`

When a fair strong probabilistic simulation targets the belief system `sys_A = 𝒟f(sys, F)`, a
concrete transition `μ_C` is matched (via `PMFRel R`) by an abstract transition
`μ_A = ω.map Prod.snd`, whose support — a set of *beliefs* — may be infinite. Since the abstract
states are beliefs and hence a convex space, we can **re-choose** `μ_A` for its finite-support
**barycenter**: group the abstract successors by which concrete successor they simulate (finitely
many when `sys_C` is finitely-branching), and replace each group by its coupling-average
`E[ν ∣ s'_C]`.

This file prototypes that re-choice and isolates *exactly* what it demands. The barycenter transition
`baryTrans ω μ_C`
* has **finite support** `≤ |μ_C.support|` (`baryTrans_support_finite`), and
* has the **same flattened target** as `μ_A` (`baryTrans_bind_id`), so it preserves `hyperStep` and
  the `F.dist`-fairness *status* of the transition.

`baryTrans_valid` shows it is again a valid, `R`-coupled `𝒟f`-transition — **conditional on the two
things the construction rests on**:
* **(1)** `R` is closed under the barycenter (`hR`) — makes the coupling legal (`PMFRel`);
* **(2)** the barycenters are `Resolvable` (`hRes`) — makes it a legal `𝒟f`-step (clustering
  restriction).

These are conditions on the simulation relation `R` (and how it reflects fairness), *not* free from
`sys_C.ImageFinite`; the point of the prototype is to make them explicit. The downstream goal (a full
`FairStrong…` normalisation, giving `SchedFinBranch` for the resulting `abstractMarginal` scheduler)
builds on this lemma.
-/

open Stream'
open scoped Classical

namespace PLTS

variable {State State_C Label : Type} [Silent Label] {sys : System State Label}

/-- The **unnormalised barycenter numerator** at a concrete successor `s'_C`: the coupling `ω`
conditioned (unnormalised) on first coordinate `s'_C`, flattened — `x ↦ ∑' ν, ω (s'_C, ν) · ν x`. -/
noncomputable def baryNum (ω : PMF (State_C × PMF State)) (s'_C : State_C) (x : State) : ENNReal :=
  ∑' ν : PMF State, ω (s'_C, ν) * ν x

/-- The first-marginal mass `(ω.map Prod.fst) s'_C` is the sum of `ω (s'_C, ν)` over all beliefs
`ν` (the fibre of the first coordinate over `s'_C`). -/
private theorem map_fst_tsum (ω : PMF (State_C × PMF State)) (s'_C : State_C) :
    (ω.map Prod.fst) s'_C = ∑' ν : PMF State, ω (s'_C, ν) := by
  rw [PMF.map_apply, ENNReal.tsum_prod', tsum_eq_single s'_C]
  · exact tsum_congr fun ν => by simp
  · intro a ha; simp [Ne.symm ha]

/-- The total mass of `baryNum ω s'_C` is the first-marginal mass `(ω.map Prod.fst) s'_C`
(sum over `x` of each belief `ν` is `1`). -/
theorem baryNum_tsum (ω : PMF (State_C × PMF State)) (s'_C : State_C) :
    (∑' x, baryNum ω s'_C x) = (ω.map Prod.fst) s'_C := by
  unfold baryNum
  rw [ENNReal.tsum_comm, map_fst_tsum]
  exact tsum_congr fun ν => by rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

/-- The **barycenter belief** `E[ν ∣ s'_C]`: the coupling `ω` conditioned on its first coordinate
being `s'_C`, flattened to a single belief. Junk (`δ_{sys.init}`) off the first-marginal support —
never used, since it is weighted by `μ_C s'_C = 0` there. -/
noncomputable def baryBelief (ω : PMF (State_C × PMF State)) (s'_C : State_C) : PMF State :=
  if h : (ω.map Prod.fst) s'_C = 0 then ω.bind Prod.snd  -- junk (off the first marginal's support)
  else PMF.normalize (baryNum ω s'_C) (by rw [baryNum_tsum]; exact h)
        (by rw [baryNum_tsum]; exact PMF.apply_ne_top _ _)

/-- The **barycenter transition**: push `μ_C` forward along the barycenter-belief map. Support is
`≤ |μ_C.support|`; flattened target agrees with `ω.map Prod.snd`. -/
noncomputable def baryTrans (ω : PMF (State_C × PMF State)) (μ_C : PMF State_C) : PMF (PMF State) :=
  μ_C.map (baryBelief ω)

/-- **Finite support** of the barycenter transition — the whole point of the re-choice. -/
theorem baryTrans_support_finite (ω : PMF (State_C × PMF State)) (μ_C : PMF State_C)
    (hfin : μ_C.support.Finite) : (baryTrans ω μ_C).support.Finite := by
  rw [baryTrans, PMF.support_map]
  exact hfin.image _

/-- **Flattened target preserved.** `(baryTrans ω μ_C).bind id = (ω.map Prod.snd).bind id` when `ω`'s
first marginal is `μ_C`: in the bind, the `μ_C s'_C` weight cancels the conditional normaliser, so
`baryTrans.bind id = ω.bind Prod.snd = (ω.map Prod.snd).bind id`. This is why the re-choice preserves
`hyperStep` and the `F.dist`-fairness status. -/
theorem baryTrans_bind_id (ω : PMF (State_C × PMF State)) (μ_C : PMF State_C)
    (hmar : ω.map Prod.fst = μ_C) :
    (baryTrans ω μ_C).bind id = (ω.map Prod.snd).bind id := by
  -- Termwise cancellation: `μ_C s'_C` weight cancels the conditional normaliser.
  have key : ∀ (s'_C : State_C) (x : State),
      μ_C s'_C * baryBelief ω s'_C x = baryNum ω s'_C x := by
    intro s'_C x
    by_cases h0 : μ_C s'_C = 0
    · rw [h0, zero_mul]
      have hsum : (∑' x, baryNum ω s'_C x) = 0 := by rw [baryNum_tsum, hmar, h0]
      rw [ENNReal.tsum_eq_zero.mp hsum x]
    · have hne : (ω.map Prod.fst) s'_C ≠ 0 := by rw [hmar]; exact h0
      rw [baryBelief, dif_neg hne, PMF.normalize_apply, baryNum_tsum, hmar,
        ← mul_assoc, mul_comm (μ_C s'_C), mul_assoc,
        ENNReal.mul_inv_cancel h0 (PMF.apply_ne_top _ _), mul_one]
  rw [baryTrans, PMF.bind_map, PMF.bind_map]
  ext x
  rw [PMF.bind_apply, PMF.bind_apply]
  simp only [Function.comp_apply, id_eq]
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun s'_C => ?_
  rw [key s'_C x]
  rfl

/-- **Barycenter witness validity.** If `μ_A = ω.map Prod.snd` is a valid `𝒟f`-transition coupled to
`μ_C` by `R` (i.e. `ω` witnesses `PMFRel R μ_C μ_A` and `hstepA` holds), then its finite-support
barycenter `baryTrans ω μ_C` is *again* a valid `R`-coupled `𝒟f`-transition — **provided**:

* **(1)** `hR` — `R` is closed under the barycenter (each `E[ν ∣ s'_C]` still simulates `s'_C`); this
  is what makes the coupling `PMFRel R μ_C (baryTrans ω μ_C)` legal;
* **(2)** `hRes` — the barycenters are `Resolvable`; this is what makes `baryTrans ω μ_C` a legal
  `𝒟f`-step (the clustering restriction on successors).

Exactly these two, and nothing more — the flattened target (hence `hyperStep`) comes for free from
`baryTrans_bind_id`. -/
theorem baryTrans_valid (F : Fairness sys) {R : State_C → PMF State → Prop}
    (ω : PMF (State_C × PMF State)) (μ_C : PMF State_C) (l : Label) (s_A : PMF State)
    (hmar : ω.map Prod.fst = μ_C)
    (hstepA : (sys.distF F).step s_A l (ω.map Prod.snd))
    (hR : ∀ s'_C ∈ μ_C.support, R s'_C (baryBelief ω s'_C))
    (hRes : ∀ s'_C ∈ μ_C.support, F.Resolvable (baryBelief ω s'_C)) :
    (sys.distF F).step s_A l (baryTrans ω μ_C) ∧ PMFRel R μ_C (baryTrans ω μ_C) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- hyperStep: same flattened target as `ω.map Prod.snd`, so reuse `hstepA.1`.
    rw [baryTrans_bind_id ω μ_C hmar]
    exact hstepA.1
  · -- successors are `Resolvable` — each is a barycenter over `μ_C.support`.
    intro ν hν
    rw [baryTrans, PMF.mem_support_map_iff] at hν
    obtain ⟨s'_C, hs'_C, rfl⟩ := hν
    exact hRes s'_C hs'_C
  · -- coupling: `μ_C.map (fun s'_C => (s'_C, baryBelief ω s'_C))`.
    refine ⟨μ_C.map (fun s'_C => (s'_C, baryBelief ω s'_C)), ?_, ?_, ?_⟩
    · rw [PMF.map_comp]
      have : (Prod.fst ∘ fun s'_C => (s'_C, baryBelief ω s'_C)) = id := by ext s; rfl
      rw [this, PMF.map_id]
    · rw [PMF.map_comp]; rfl
    · intro p hp
      rw [PMF.mem_support_map_iff] at hp
      obtain ⟨s'_C, hs'_C, rfl⟩ := hp
      exact hR s'_C hs'_C

/-- **Fairness status preserved.** `F.dist.fair` depends on a transition only through its flattened
target and the `Resolvable`-ility of its successors, both of which the barycenter shares with
`μ_A = ω.map Prod.snd`. Hence the `¬ F.dist.fair → descent` rank clause of a fair strong simulation
transfers *verbatim* to the barycenter witness — no extra condition on `R`. -/
theorem baryTrans_fair_iff (F : Fairness sys) (ω : PMF (State_C × PMF State)) (μ_C : PMF State_C)
    (l : Label) (s_A : PMF State) (hmar : ω.map Prod.fst = μ_C)
    (hRes : ∀ s'_C ∈ μ_C.support, F.Resolvable (baryBelief ω s'_C))
    (hResA : ∀ ν ∈ (ω.map Prod.snd).support, F.Resolvable ν) :
    F.dist.fair s_A l (baryTrans ω μ_C) ↔ F.dist.fair s_A l (ω.map Prod.snd) := by
  have hbind : (baryTrans ω μ_C).bind id = (ω.map Prod.snd).bind id :=
    baryTrans_bind_id ω μ_C hmar
  -- Resolvable clauses for each transition's successors.
  have hResBary : ∀ ν ∈ (baryTrans ω μ_C).support, F.Resolvable ν := by
    intro ν hν
    rw [baryTrans, PMF.mem_support_map_iff] at hν
    obtain ⟨s'_C, hs'_C, rfl⟩ := hν
    exact hRes s'_C hs'_C
  constructor
  · rintro ⟨⟨hyper, _⟩, p, hp, hpbind⟩
    -- transfer hyperStep and the flattened-target identity through `hbind`.
    rw [hbind] at hyper hpbind
    exact ⟨⟨hyper, hResA⟩, p, hp, hpbind⟩
  · rintro ⟨⟨hyper, _⟩, p, hp, hpbind⟩
    rw [← hbind] at hyper hpbind
    exact ⟨⟨hyper, hResBary⟩, p, hp, hpbind⟩

end PLTS
