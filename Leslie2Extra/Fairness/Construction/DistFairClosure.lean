/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2Extra.Fairness.Construction.DistFairBarycenter

/-!
# The fair-label-refined right-convex closure of a simulation into `𝒟f(sys, F)`

To normalise a fair strong probabilistic simulation `R` into `𝒟f(sys, F)` to finite-support
witnesses, we re-choose each abstract transition for a finite family of **barycenters** of its
successors, grouped by the concrete successor they simulate *and* by a common fair label
(`DistFairBarycenter.lean` proved the single-barycenter re-choice valid). This file records the
foundational objects for that development:

* `FairLabels F s` — the enabled fair labels of a base state;
* `commonFairLabels F ν` — the fair labels shared by every state of a belief;
* `FinFairLabelSets F` — **the new assumption**: finitely many distinct enabled-fair-label sets in
  the abstract system (strictly weaker than "finitely many fair labels");
* `rightConvexClosure R` — the plain barycenter closure (may leave `𝒟f`: barycenters need not be
  `Resolvable`);
* `refinedClosure F R` — the closure restricted to `Resolvable` barycenters, which is exactly the
  fairness-homogeneous re-choice.

Built on these: the refined barycenter transition `refinedTrans` (finite support under
`FinFairLabelSets`) and the capstone `refinedClosure_isFairSim` — `refinedClosure F R` is again a
`FairStrongProbabilisticSimulation` into `𝒟f(sys, F)`, now with a **finite-support** witness
(`refinedTrans`) for every concrete transition.

### On discharging `SchedFinBranch` (deferred by design)

The intended payoff is that the scheduler `abstractMarginal (simJointExecR pe_C ·)` induced by the
refined simulation is `SchedFinBranch` (its H2 = each emitted `ω` finite-support), which is exactly
the hypothesis `DistFairHalt.fairAchievableTraceDists_distF_subset` takes on the lowered execution.
`refinedClosure_isFairSim` supplies the finite witness, but it is **not** enough to discharge H2
mechanically: the emission read off the joint scheduler is `(simCoupleF …).map Prod.snd`, which
`simCoupleF_map_snd` equates to `(sim.step …).choose`. As an `Exists.choose`, it is proof-irrelevant
— it depends only on the *proposition* `∃ μ_A, 𝒟f-step ∧ PMFRel (refinedClosure F R) μ_C μ_A`,
not on the finite `refinedTrans` witness we hand `refinedClosure_step`. That proposition does not
force finiteness (a `PMFRel`-coupling to a finite `μ_C` can still have infinite second marginal), so
`Classical.choice` may re-select an infinite witness. Forcing finiteness through `.choose` would
require moving it into the step-*property* — e.g. retargeting the closure into a finite-branching
`𝒟f` (plus a `sys.ImageFinite` fairness/deadlock bridge), or a data-carrying abstract scheduler that
bypasses `simCoupleF`. Both are larger refactors; `SchedFinBranch` is therefore kept a hypothesis,
with `refinedClosure_isFairSim` standing as the evidence that it is satisfiable.
-/

namespace PLTS

variable {State State_C Label : Type} [Silent Label] {sys : System State Label}

/-- **Enabled fair labels** of a base state `s` of the abstract system `sys`: the labels at which
`s` has an `F`-fair transition. -/
def FairLabels (F : Fairness sys) (s : State) : Set Label := {l | ∃ μ : PMF State, F.fair s l μ}

/-- **Common fair labels** of a belief `ν`: the labels fair at *every* state of `ν.support` (the
intersection of the support states' `FairLabels`). `ν` is `F.CommonFairLabel` exactly when this set
is nonempty, and any element of it witnesses `CommonFairLabel`. -/
def commonFairLabels (F : Fairness sys) (ν : PMF State) : Set Label :=
  ⋂ s ∈ ν.support, FairLabels F s

/-- **The finiteness assumption on the abstract system.** Only finitely many *distinct*
enabled-fair-label sets occur among the base states. This is strictly weaker than "finitely many
fair labels" — it is insensitive to label multiplicity within a shared set (e.g. every state fair
on the same infinite label set gives a *single* distinct set). It is precisely what bounds the
number of
fairness-homogeneous barycenter groups — hence the branching of the induced scheduler — in the
refined closure. -/
def FinFairLabelSets (F : Fairness sys) : Prop := (Set.range (FairLabels F)).Finite

/-- The **right-convex closure** of a concrete-to-belief relation `R`: relate `q_C` to every
barycenter `κ.bind id` of a family `κ` of beliefs all `R`-related to `q_C`. This closure may leave
`𝒟f`, since a barycenter of `Resolvable` beliefs need not be `Resolvable`. -/
def rightConvexClosure (R : State_C → PMF State → Prop) : State_C → PMF State → Prop :=
  fun q_C q_A => ∃ κ : PMF (PMF State), (∀ ν ∈ κ.support, R q_C ν) ∧ q_A = κ.bind id

/-- The **fair-label-refined right-convex closure**: the barycenters of `R` that stay inside `𝒟f`,
i.e. are `Resolvable`. Requiring the barycenter `κ.bind id` to be `Resolvable` is *exactly* the
fairness-homogeneity of the family:
`F.CommonFairLabel (κ.bind id)` ⟺ a common fair label across all constituents (their
`commonFairLabels` intersect), and `F.AllFairDeadlock (κ.bind id)` ⟺ all constituents are
all-deadlock — because `(κ.bind id).support = ⋃ ν ∈ κ.support, ν.support`. Under `FinFairLabelSets`,
the beliefs coupled to a fixed concrete successor fall into finitely many such Resolvable
barycenter groups. -/
def refinedClosure (F : Fairness sys) (R : State_C → PMF State → Prop) :
    State_C → PMF State → Prop :=
  fun q_C q_A => rightConvexClosure R q_C q_A ∧ F.Resolvable q_A

/-- **The finiteness the assumption buys.** Under `FinFairLabelSets`, only finitely many distinct
`commonFairLabels` values occur across all beliefs: `commonFairLabels F ν = ⋂₀ (FairLabels F ''
ν.support)` is the intersection of a subfamily of the finite family `Set.range (FairLabels F)`, so
it ranges over `≤ 2^m` values. This bounds the number of fairness-homogeneous barycenter groups
(hence the branching of the refined-closure scheduler): group coupled beliefs by their
`commonFairLabels` value, and there are finitely many such groups. -/
theorem commonFairLabels_range_finite (F : Fairness sys) (h : FinFairLabelSets F) :
    (Set.range (commonFairLabels F)).Finite := by
  refine Set.Finite.subset (h.finite_subsets.image Set.sInter) ?_
  rintro _ ⟨ν, rfl⟩
  refine ⟨FairLabels F '' ν.support, Set.image_subset_range _ _, ?_⟩
  rw [commonFairLabels, ← Set.sInter_image]

/-! ### The refined barycenter transition

To refine an abstract witness `μ_A = ω.map Prod.snd` (coupled to `μ_C` by `PMFRel R` via `ω`) to a
finite-support, `Resolvable`-successored transition, we **re-index the concrete coordinate by the
fair
label class**: replace `State_C` by `State_C × Set Label`, tagging each coupled belief `ν` with its
`commonFairLabels F ν`. The refined transition is then just `baryTrans` at that refined type — so
its
flattened target and coupling come for free from `baryTrans`/`baryTrans_bind_id`, and the group
barycenters are `Resolvable` because each group is fairness-homogeneous. -/

/-- The **fair-label-refined coupling**: tag each coupled pair `(s'_C, ν)` with `ν`'s
common-fair-label
class, refining the concrete coordinate to `State_C × Set Label`. -/
noncomputable def reindexCoupling (F : Fairness sys) (ω : PMF (State_C × PMF State)) :
    PMF ((State_C × Set Label) × PMF State) :=
  ω.map (fun p => ((p.1, commonFairLabels F p.2), p.2))

/-- The **refined barycenter transition**: `baryTrans` over the refined coupling — one group
barycenter per `(concrete successor, common-fair-label class)`. -/
noncomputable def refinedTrans (F : Fairness sys) (ω : PMF (State_C × PMF State)) :
    PMF (PMF State) :=
  baryTrans (reindexCoupling F ω) ((reindexCoupling F ω).map Prod.fst)

/-- Re-indexing doesn't touch the belief coordinate: the second marginal is unchanged. -/
theorem reindexCoupling_map_snd (F : Fairness sys) (ω : PMF (State_C × PMF State)) :
    (reindexCoupling F ω).map Prod.snd = ω.map Prod.snd := by
  rw [reindexCoupling, PMF.map_comp]; rfl

/-- **Flattened target preserved.** The refined transition has the same flattened target as the
original abstract witness `ω.map Prod.snd` — immediate from `baryTrans_bind_id` (the refined
marginal
is the first marginal of `reindexCoupling F ω` by definition) and `reindexCoupling_map_snd`. -/
theorem refinedTrans_bind_id (F : Fairness sys) (ω : PMF (State_C × PMF State)) :
    (refinedTrans F ω).bind id = (ω.map Prod.snd).bind id := by
  rw [refinedTrans, baryTrans_bind_id _ _ rfl, reindexCoupling_map_snd]

/-- The first-marginal mass `(ω.map Prod.fst) s'_C` is the sum of `ω (s'_C, ν)` over all beliefs
`ν` (local copy of the `private` `DistFairBarycenter.map_fst_tsum`). -/
private theorem map_fst_tsum' (ω : PMF (State_C × PMF State)) (s'_C : State_C) :
    (ω.map Prod.fst) s'_C = ∑' ν : PMF State, ω (s'_C, ν) := by
  rw [PMF.map_apply, ENNReal.tsum_prod', tsum_eq_single s'_C]
  · exact tsum_congr fun ν => by simp
  · intro a ha; simp [Ne.symm ha]

/-- `commonFairLabels` is nonempty exactly when the belief has a common fair label. -/
theorem commonFairLabels_nonempty_iff (F : Fairness sys) (ν : PMF State) :
    (commonFairLabels F ν).Nonempty ↔ F.CommonFairLabel ν := by
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨l, ?_⟩
    intro s hs
    exact Set.mem_iInter₂.mp hl s hs
  · rintro ⟨l, hl⟩
    refine ⟨l, ?_⟩
    rw [commonFairLabels, Set.mem_iInter₂]
    intro s hs
    exact hl s hs

/-- **Support of a barycenter belief.** Off the junk branch, a state is in the barycenter's support
iff some belief the coupling puts on `s'_C` carries it. Proof: `baryBelief = PMF.normalize (baryNum
…)`, so `x ∈ support ↔ baryNum ω s'_C x ≠ 0 ↔ ∑' ν, ω (s'_C, ν) · ν x ≠ 0 ↔ ∃ ν, ω (s'_C, ν) ≠ 0 ∧
ν x ≠ 0`. -/
theorem baryBelief_mem_support (ω : PMF (State_C × PMF State)) (s'_C : State_C)
    (h : (ω.map Prod.fst) s'_C ≠ 0) (x : State) :
    x ∈ (baryBelief ω s'_C).support ↔ ∃ ν : PMF State, ω (s'_C, ν) ≠ 0 ∧ x ∈ ν.support := by
  unfold baryBelief
  rw [dif_neg h, PMF.mem_support_iff, PMF.normalize_apply]
  have hinv : (∑' x, baryNum ω s'_C x)⁻¹ ≠ 0 := by
    rw [baryNum_tsum]
    exact ENNReal.inv_ne_zero.mpr (PMF.apply_ne_top _ _)
  rw [mul_ne_zero_iff, and_iff_left hinv]
  unfold baryNum
  rw [Ne, ENNReal.tsum_eq_zero, not_forall]
  constructor
  · rintro ⟨ν, hν⟩
    exact ⟨ν, (mul_ne_zero_iff.mp hν).1, (PMF.mem_support_iff _ _).mpr (mul_ne_zero_iff.mp hν).2⟩
  · rintro ⟨ν, h1, h2⟩
    exact ⟨ν, mul_ne_zero h1 ((PMF.mem_support_iff _ _).mp h2)⟩

/-- **The barycenter belief lies in the right-convex closure.** It is `κ.bind id` for the
belief-level
conditional `κ = PMF.normalize (fun ν => ω (s'_C, ν)) …`, whose support consists of `R`-related
beliefs. (`baryBelief ω s'_C = κ.bind id` because both equal `x ↦ baryNum ω s'_C x · ((ω.map fst)
s'_C)⁻¹`; use `PMF.normalize_apply`, `baryNum_tsum`, and `∑' ν, ω (s'_C, ν) = (ω.map fst) s'_C`.) -/
theorem baryBelief_mem_rightConvexClosure (ω : PMF (State_C × PMF State)) (s'_C : State_C)
    {R : State_C → PMF State → Prop} (hR : ∀ ν, ω (s'_C, ν) ≠ 0 → R s'_C ν)
    (h : (ω.map Prod.fst) s'_C ≠ 0) :
    rightConvexClosure R s'_C (baryBelief ω s'_C) := by
  have hsum : (∑' ν : PMF State, ω (s'_C, ν)) = (ω.map Prod.fst) s'_C :=
    (map_fst_tsum' ω s'_C).symm
  have h0 : (∑' ν : PMF State, ω (s'_C, ν)) ≠ 0 := by rw [hsum]; exact h
  have htop : (∑' ν : PMF State, ω (s'_C, ν)) ≠ ⊤ := by rw [hsum]; exact PMF.apply_ne_top _ _
  refine ⟨PMF.normalize (fun ν => ω (s'_C, ν)) h0 htop, ?_, ?_⟩
  · -- support of `κ` sits inside the `R`-related beliefs
    intro ν hν
    rw [PMF.mem_support_normalize_iff] at hν
    exact hR ν hν
  · -- `baryBelief ω s'_C = κ.bind id`, both being `x ↦ baryNum ω s'_C x · ((ω.map fst) s'_C)⁻¹`
    ext x
    rw [PMF.bind_apply]
    have hκ : ∀ ν : PMF State,
        (PMF.normalize (fun ν => ω (s'_C, ν)) h0 htop) ν * (id ν) x
          = ω (s'_C, ν) * ν x * ((ω.map Prod.fst) s'_C)⁻¹ := by
      intro ν
      rw [PMF.normalize_apply, hsum]
      simp only [id_eq]
      ring
    rw [tsum_congr hκ, ENNReal.tsum_mul_right]
    rw [baryBelief, dif_neg h, PMF.normalize_apply, baryNum_tsum]
    rfl

/-- **Finite support of the refined transition** (H2). Under `FinFairLabelSets` and a finite
concrete
marginal, `refinedTrans` has finitely many successor beliefs. Via `baryTrans_support_finite`: the
refined marginal `(reindexCoupling F ω).map Prod.fst` has support inside
`(ω.map Prod.fst).support ×ˢ Set.range (commonFairLabels F)` — finite by `hCfin` and
`commonFairLabels_range_finite h`. -/
theorem refinedTrans_support_finite (F : Fairness sys) (h : FinFairLabelSets F)
    (ω : PMF (State_C × PMF State)) (hCfin : (ω.map Prod.fst).support.Finite) :
    (refinedTrans F ω).support.Finite := by
  rw [refinedTrans]
  apply baryTrans_support_finite
  -- the refined marginal's support sits inside a finite product
  refine Set.Finite.subset (hCfin.prod (commonFairLabels_range_finite F h)) ?_
  rintro ⟨s, I⟩ hk
  rw [reindexCoupling, PMF.map_comp, PMF.mem_support_map_iff] at hk
  obtain ⟨p, hp, hpk⟩ := hk
  simp only [Function.comp_apply, Prod.mk.injEq] at hpk
  refine ⟨?_, ?_⟩
  · rw [PMF.mem_support_map_iff]
    exact ⟨p, hp, hpk.1⟩
  · exact ⟨p.2, hpk.2⟩

/-- A nonzero refined-coupling weight `reindexCoupling F ω ((s'_C, I), ρ) ≠ 0` comes from an
original coupled pair `(s'_C, ρ) ∈ ω.support` whose belief `ρ` has `commonFairLabels F ρ = I`. -/
private theorem reindexCoupling_apply_ne_zero (F : Fairness sys) (ω : PMF (State_C × PMF State))
    (s'_C : State_C) (I : Set Label) (ρ : PMF State)
    (hne : reindexCoupling F ω ((s'_C, I), ρ) ≠ 0) :
    (s'_C, ρ) ∈ ω.support ∧ commonFairLabels F ρ = I := by
  rw [reindexCoupling, ← PMF.mem_support_iff, PMF.mem_support_map_iff] at hne
  obtain ⟨p, hp, hpk⟩ := hne
  simp only [Prod.mk.injEq] at hpk
  obtain ⟨⟨h1, h2⟩, h3⟩ := hpk
  subst h1; subst h3
  exact ⟨hp, h2⟩

/-- **Every successor of the refined transition is `Resolvable`** — the fairness-homogeneity payoff.
Each successor is `baryBelief (reindexCoupling F ω) (s'_C, I)`, a barycenter of beliefs all coupled
to
`s'_C` with `commonFairLabels = I`. If `I ≠ ∅`, pick `l ∈ I`: every state of every such belief has a
fair `l`-transition (`l ∈ commonFairLabels ν = ⋂ FairLabels`), so the barycenter's support
(`baryBelief_mem_support`, the union of those supports) is `CommonFairLabel l`. If `I = ∅`, each
such
belief is `Resolvable` (`hResA`) with empty `commonFairLabels`, hence `AllFairDeadlock`
(`commonFairLabels_nonempty_iff`), so the barycenter is `AllFairDeadlock`. Either way `Resolvable`.
-/
theorem refinedTrans_resolvable (F : Fairness sys) (ω : PMF (State_C × PMF State))
    (hResA : ∀ ν ∈ (ω.map Prod.snd).support, F.Resolvable ν)
    (β : PMF State) (hβ : β ∈ (refinedTrans F ω).support) :
    F.Resolvable β := by
  -- Peel off the barycenter: `β = baryBelief (reindexCoupling F ω) k` for some `k = (s'_C, I)`.
  rw [refinedTrans, baryTrans, PMF.mem_support_map_iff] at hβ
  obtain ⟨k, hk, rfl⟩ := hβ
  obtain ⟨s'_C, I⟩ := k
  -- `k ∈ μ'.support` gives the nonvanishing first-marginal mass needed by `baryBelief_mem_support`.
  have hkne : ((reindexCoupling F ω).map Prod.fst) (s'_C, I) ≠ 0 := by
    rwa [← PMF.mem_support_iff]
  -- Every state of the barycenter's support comes from some coupled belief `ρ` with `cFL ρ = I`.
  have hsupp : ∀ x ∈ (baryBelief (reindexCoupling F ω) (s'_C, I)).support,
      ∃ ρ : PMF State, commonFairLabels F ρ = I ∧
        (s'_C, ρ) ∈ ω.support ∧ x ∈ ρ.support := by
    intro x hx
    rw [baryBelief_mem_support _ _ hkne] at hx
    obtain ⟨ρ, hρne, hxρ⟩ := hx
    obtain ⟨hρω, hρI⟩ := reindexCoupling_apply_ne_zero F ω s'_C I ρ hρne
    exact ⟨ρ, hρI, hρω, hxρ⟩
  by_cases hI : (I : Set Label).Nonempty
  · -- Common fair label branch: any `l ∈ I` is fair at every state of the barycenter.
    obtain ⟨l, hl⟩ := hI
    refine Or.inl ⟨l, fun x hx => ?_⟩
    obtain ⟨ρ, hρI, _, hxρ⟩ := hsupp x hx
    -- `l ∈ I = commonFairLabels F ρ`, so `l` is fair at `x ∈ ρ.support`.
    have : l ∈ commonFairLabels F ρ := hρI ▸ hl
    rw [commonFairLabels, Set.mem_iInter₂] at this
    exact this x hxρ
  · -- All-fair-deadlock branch: each carrier belief `ρ` is resolvable with empty `cFL`, so dead.
    refine Or.inr (fun x hx => ?_)
    obtain ⟨ρ, hρI, hρω, hxρ⟩ := hsupp x hx
    have hρres : F.Resolvable ρ := by
      apply hResA
      rw [PMF.mem_support_map_iff]
      exact ⟨(s'_C, ρ), hρω, rfl⟩
    have hnotcfl : ¬ F.CommonFairLabel ρ := by
      rw [← commonFairLabels_nonempty_iff]
      rw [hρI]; exact hI
    rcases hρres with hc | hd
    · exact absurd hc hnotcfl
    · exact hd x hxρ

/-- **Summed validity of the refined transition** — the generalisation of `baryTrans_valid` to the
finite label-indexed family. If `ω` witnesses `PMFRel R μ_C (ω.map Prod.snd)` and `hstepA` holds,
then
the refined transition is a valid `𝒟f`-step coupled to `μ_C` by the *refined closure*:

* the **step** is `hyperStep` (same flattened target, `refinedTrans_bind_id` + `hstepA.1`) with
  `Resolvable` successors (`refinedTrans_resolvable`, fed `hstepA.2`);
* the **`PMFRel (refinedClosure F R)`** coupling pairs each successor barycenter with its concrete
  successor `s'_C` (project the label tag away): the coupling
  `((reindexCoupling F ω).map Prod.fst).map (fun k => (k.1, baryBelief (reindexCoupling F ω) k))`
  has
  first marginal `μ_C` (via `hmar`), second marginal `refinedTrans`, and support inside
  `refinedClosure F R` — each successor is in `rightConvexClosure`
  (`baryBelief_mem_rightConvexClosure`,
  since coupled beliefs are `R`-related via `hR`) and `Resolvable` (`refinedTrans_resolvable`). -/
theorem refinedTrans_valid (F : Fairness sys) {R : State_C → PMF State → Prop}
    (ω : PMF (State_C × PMF State)) (μ_C : PMF State_C) (l : Label) (s_A : PMF State)
    (hmar : ω.map Prod.fst = μ_C)
    (hstepA : (sys.distF F).step s_A l (ω.map Prod.snd))
    (hR : ∀ p ∈ ω.support, R p.1 p.2) :
    (sys.distF F).step s_A l (refinedTrans F ω) ∧
      PMFRel (refinedClosure F R) μ_C (refinedTrans F ω) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- hyperStep: same flattened target as `ω.map Prod.snd`.
    rw [refinedTrans_bind_id]
    exact hstepA.1
  · -- successors are `Resolvable`.
    intro ν hν
    exact refinedTrans_resolvable F ω hstepA.2 ν hν
  · -- coupling: pair each successor barycenter with its concrete successor `k.1`.
    set μ' := (reindexCoupling F ω).map Prod.fst with hμ'
    refine ⟨μ'.map (fun k => (k.1, baryBelief (reindexCoupling F ω) k)), ?_, ?_, ?_⟩
    · -- first marginal is `μ_C`
      rw [PMF.map_comp, hμ', reindexCoupling, PMF.map_comp, PMF.map_comp, ← hmar]
      rfl
    · -- second marginal is `refinedTrans F ω`
      rw [PMF.map_comp]
      rfl
    · -- support ⊆ `refinedClosure F R`
      intro p hp
      rw [PMF.mem_support_map_iff] at hp
      obtain ⟨k, hk, rfl⟩ := hp
      obtain ⟨s'_C, I⟩ := k
      have hkne : ((reindexCoupling F ω).map Prod.fst) (s'_C, I) ≠ 0 := by
        rw [hμ'] at hk; rwa [← PMF.mem_support_iff]
      simp only []
      refine ⟨?_, ?_⟩
      · -- rightConvexClosure via `baryBelief_mem_rightConvexClosure` (label tag ignored in `R'`)
        exact baryBelief_mem_rightConvexClosure (reindexCoupling F ω) (s'_C, I)
          (R := fun _ ρ => R s'_C ρ)
          (fun ρ hρne => hR (s'_C, ρ) (reindexCoupling_apply_ne_zero F ω s'_C I ρ hρne).1)
          hkne
      · -- Resolvable via `refinedTrans_resolvable`
        apply refinedTrans_resolvable F ω hstepA.2
        rw [refinedTrans, baryTrans, PMF.mem_support_map_iff]
        exact ⟨(s'_C, I), by rw [hμ'] at hk; exact hk, rfl⟩

/-! ### Convexity of `hyperStep` and `F.dist`-fairness under barycentric mixing

The refined closure steps out of a barycenter `κ.bind id` by *mixing* the constituent beliefs'
steps. The reusable core is the **posterior-mixed kernel** `kernelMix κ K`: to step out of state `s`
of the flattened belief `κ.bind id`, sample the belief `ν` from the posterior `∝ κ ν · ν s` and draw
from that belief's kernel `K ν s`. Its flattened bind **telescopes** (`kernelMix_bind_id`) — the
posterior normaliser cancels the `(κ.bind id) s` weight, as in `baryTrans_bind_id`. This yields:

* `hyperStep_bind` — a `κ`-mixture of `hyperStep`s from the `ν` is a `hyperStep` from `κ.bind id`;
* `distF_step_bind` — the same for full `𝒟f`-steps (adds the `Resolvable`-successors clause);
* `distFair_bind` — the same for `F.dist`-fair transitions (mixes the fair kernels), which is what
  transfers the rank clause of the refined simulation.
-/

/-- The **posterior-mixed kernel**. Given a distribution `κ` over beliefs and a total per-belief
kernel `K`, the combined kernel out of state `s` samples `ν` from the posterior given `s`
(`∝ κ ν · ν s`, with normaliser `(κ.bind id) s`) and then draws from `K ν s`. Junk off the support
of `κ.bind id` (never reached: it carries weight `0`). -/
noncomputable def kernelMix (κ : PMF (PMF State)) (K : PMF State → State → PMF (PMF State))
    (s : State) : PMF (PMF State) :=
  if h : (κ.bind id) s = 0 then PMF.pure (κ.bind id)
  else
    (PMF.normalize (fun ν => κ ν * ν s)
        (by simpa only [PMF.bind_apply, id_eq] using h)
        (by simpa only [PMF.bind_apply, id_eq] using PMF.apply_ne_top (κ.bind id) s)).bind
      (fun ν => K ν s)

/-- **Support of the posterior mix.** Every belief in `(kernelMix κ K s).support` (for `s` in the
support of `κ.bind id`) comes from some `K ν s` with a positive posterior weight `κ ν · ν s`. -/
theorem kernelMix_mem_support {κ : PMF (PMF State)} {K : PMF State → State → PMF (PMF State)}
    {s : State} (h : (κ.bind id) s ≠ 0) {μ : PMF State} (hμ : μ ∈ (kernelMix κ K s).support) :
    ∃ ν, κ ν ≠ 0 ∧ ν s ≠ 0 ∧ μ ∈ (K ν s).support := by
  -- Strategy: `kernelMix`, `dif_neg h`; `PMF.mem_support_bind_iff` splits off the posterior sample
  -- `ν`; `PMF.normalize_apply` + `ENNReal.mul_ne_zero`/`mul_ne_zero_iff` turn the posterior support
  -- `ν ∈ (normalize …).support` into `κ ν * ν s ≠ 0`, hence `κ ν ≠ 0 ∧ ν s ≠ 0`. The `(∑')⁻¹`
  -- factor is nonzero since the total (`= (κ.bind id) s ≠ ⊤`) is not `⊤`.
  rw [kernelMix, dif_neg h, PMF.mem_support_bind_iff] at hμ
  obtain ⟨ν, hν_norm, hμν⟩ := hμ
  rw [PMF.mem_support_iff, PMF.normalize_apply] at hν_norm
  obtain ⟨hκ, hνs⟩ := mul_ne_zero_iff.mp (left_ne_zero_of_mul hν_norm)
  exact ⟨ν, hκ, hνs, hμν⟩

/-- **Telescoping bind — the crux.** Flattening the posterior mix reproduces the plain mixture of
the per-belief flattened kernels: the posterior normaliser cancels the `(κ.bind id) s` weight. Like
the `baryTrans_bind_id` cancellation, with one extra `tsum_comm` layer over the beliefs. -/
theorem kernelMix_bind_id (κ : PMF (PMF State)) (K : PMF State → State → PMF (PMF State)) :
    (κ.bind id).bind (fun s => (kernelMix κ K s).bind id)
      = κ.bind (fun ν => ν.bind (fun s => (K ν s).bind id)) := by
  -- Strategy: `ext x`; expand both sides with `PMF.bind_apply`.
  --   RHS x = ∑' ν, κ ν * ∑' s, ν s * ((K ν s).bind id) x.
  --   LHS x = ∑' s, (κ.bind id) s * ((kernelMix κ K s).bind id) x.
  -- For `s` with `(κ.bind id) s ≠ 0`: `dif_neg`, `PMF.bind_apply`, `PMF.normalize_apply`; factor
  -- `(κ.bind id) s * (κ ν * ν s * ((κ.bind id) s)⁻¹) = κ ν * ν s` cancels (`mul_inv_cancel`, as in
  -- `baryTrans_bind_id`), giving the `s`-term `∑' ν, κ ν * ν s * ((K ν s).bind id) x`. For
  -- `(κ.bind id) s = 0` the LHS term is `0`, and on the right `∑' ν, κ ν * ν s = 0` forces each
  -- `κ ν * ν s = 0` (`ENNReal.tsum_eq_zero`), so the same `s`-term is `0` — hence
  --   LHS x = ∑' s, ∑' ν, κ ν * ν s * ((K ν s).bind id) x
  -- for *all* `s`. Finish with `ENNReal.tsum_comm` and `ENNReal.tsum_mul_left`/`mul_assoc`.
  ext x
  -- The per-`s` termwise identity: the posterior normaliser cancels the `(κ.bind id) s` weight.
  have hflat : ∀ s, (κ.bind id) s = ∑' ν, κ ν * ν s := by
    intro s; simp only [PMF.bind_apply, id_eq]
  have key : ∀ s, (κ.bind id) s * ((kernelMix κ K s).bind id) x
      = ∑' ν, κ ν * ν s * ((K ν s).bind id) x := by
    intro s
    by_cases h0 : (κ.bind id) s = 0
    · rw [h0, zero_mul]
      have hsum : (∑' ν, κ ν * ν s) = 0 := by rw [← hflat s]; exact h0
      refine (ENNReal.tsum_eq_zero.mpr fun ν => ?_).symm
      rw [ENNReal.tsum_eq_zero.mp hsum ν, zero_mul]
    · have hT : (∑' ν, κ ν * ν s) ≠ 0 := by rw [← hflat s]; exact h0
      have hTtop : (∑' ν, κ ν * ν s) ≠ ⊤ := by
        rw [← hflat s]; exact PMF.apply_ne_top _ _
      rw [hflat s, kernelMix, dif_neg h0, PMF.bind_bind, PMF.bind_apply, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun ν => ?_
      rw [PMF.normalize_apply, ← mul_assoc, mul_comm ((∑' ν, κ ν * ν s))
          (κ ν * ν s * (∑' ν, κ ν * ν s)⁻¹), mul_assoc (κ ν * ν s), mul_assoc (κ ν * ν s),
        ENNReal.inv_mul_cancel hT hTtop, one_mul]
  rw [PMF.bind_apply]
  simp only [key]
  rw [ENNReal.tsum_comm, PMF.bind_apply]
  refine tsum_congr fun ν => ?_
  rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun s => ?_
  rw [mul_assoc]

omit [Silent Label] in
/-- **Convexity of `hyperStep`.** A `κ`-mixture of hypersteps out of the beliefs `ν` (each to `g ν`)
is a single hyperstep out of the barycenter `κ.bind id` to the mixed target `κ.bind g`. Witnessed by
the posterior-mixed kernel of the per-`ν` extracted kernels. -/
theorem hyperStep_bind (κ : PMF (PMF State)) (l : Label) (g : PMF State → PMF State)
    (hg : ∀ ν ∈ κ.support, hyperStep sys ν l (g ν)) :
    hyperStep sys (κ.bind id) l (κ.bind g) := by
  classical
  set K : PMF State → State → PMF (PMF State) :=
    fun ν => if hν : ν ∈ κ.support then (hg ν hν).kernel else fun _ => PMF.pure (g ν) with hK
  have hKspec : ∀ (ν) (hν : ν ∈ κ.support), K ν = (hg ν hν).kernel := by
    intro ν hν; rw [hK]; exact dif_pos hν
  refine ⟨kernelMix κ K, ?_, ?_⟩
  · -- validity of the mixed kernel
    intro s hs μ hμ
    obtain ⟨ν, hκν, hνs, hμν⟩ :=
      kernelMix_mem_support (by rwa [PMF.mem_support_iff] at hs) hμ
    have hν : ν ∈ κ.support := (PMF.mem_support_iff _ _).mpr hκν
    rw [hKspec ν hν] at hμν
    exact (hg ν hν).kernel_step s ((PMF.mem_support_iff _ _).mpr hνs) μ hμν
  · -- flattened target: `kernelMix_bind_id` then `post_eq_bind` per belief
    rw [kernelMix_bind_id]
    ext x
    rw [PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun ν => ?_
    by_cases hν : ν ∈ κ.support
    · rw [hKspec ν hν, ← (hg ν hν).post_eq_bind]
    · have hκ0 : κ ν = 0 := by simpa only [PMF.mem_support_iff, not_not] using hν
      simp [hκ0]

/-- **Convexity of `𝒟f`-steps.** A `κ`-mixture of `𝒟f(sys, F)`-steps out of the beliefs `ν` is a
`𝒟f`-step out of the barycenter `κ.bind id` to `κ.bind g`: the `hyperStep` part is `hyperStep_bind`,
and the `Resolvable`-successors clause is inherited pointwise. -/
theorem distF_step_bind (F : Fairness sys) (κ : PMF (PMF State)) (l : Label)
    (g : PMF State → PMF (PMF State))
    (hstep : ∀ ν ∈ κ.support, (sys.distF F).step ν l (g ν)) :
    (sys.distF F).step (κ.bind id) l (κ.bind g) := by
  refine ⟨?_, ?_⟩
  · have h := hyperStep_bind κ l (fun ν => (g ν).bind id) (fun ν hν => (hstep ν hν).1)
    rwa [PMF.bind_bind]
  · intro ν' hν'
    rw [PMF.mem_support_bind_iff] at hν'
    obtain ⟨ν, hν, hν'g⟩ := hν'
    exact (hstep ν hν).2 ν' hν'g

/-- **Convexity of `F.dist`-fairness.** A `κ`-mixture of `F.dist`-fair transitions out of the
beliefs `ν` is `F.dist`-fair out of the barycenter `κ.bind id`. Combines the `𝒟f`-step part
(`distF_step_bind`) with the posterior mix of the all-`F`-fair kernels — this is what carries the
rank clause of the refined simulation across the barycentric re-choice. -/
theorem distFair_bind (F : Fairness sys) (κ : PMF (PMF State)) (l : Label)
    (g : PMF State → PMF (PMF State))
    (hf : ∀ ν ∈ κ.support, F.dist.fair ν l (g ν)) :
    F.dist.fair (κ.bind id) l (κ.bind g) := by
  classical
  refine ⟨distF_step_bind F κ l g (fun ν hν => (hf ν hν).1), ?_⟩
  set K : PMF State → State → PMF (PMF State) :=
    fun ν => if hν : ν ∈ κ.support then (hf ν hν).2.choose else fun _ => PMF.pure (κ.bind id)
    with hK
  have hKspec : ∀ (ν) (hν : ν ∈ κ.support), K ν = (hf ν hν).2.choose := by
    intro ν hν; rw [hK]; exact dif_pos hν
  refine ⟨kernelMix κ K, ?_, ?_⟩
  · -- validity: each sampled `μ'` is `F`-fair via the belief `ν`'s fair kernel
    intro s hs μ' hμ'
    obtain ⟨ν, hκν, hνs, hμν⟩ :=
      kernelMix_mem_support (by rwa [PMF.mem_support_iff] at hs) hμ'
    have hν : ν ∈ κ.support := (PMF.mem_support_iff _ _).mpr hκν
    rw [hKspec ν hν] at hμν
    exact (hf ν hν).2.choose_spec.1 s ((PMF.mem_support_iff _ _).mpr hνs) μ' hμν
  · -- flattened target via `kernelMix_bind_id` then the per-belief fair-kernel identity
    rw [kernelMix_bind_id, PMF.bind_bind]
    ext x
    rw [PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun ν => ?_
    by_cases hν : ν ∈ κ.support
    · rw [hKspec ν hν, ← (hf ν hν).2.choose_spec.2]
    · have hκ0 : κ ν = 0 := by simpa only [PMF.mem_support_iff, not_not] using hν
      simp [hκ0]

/-! ### Fair-enabledness of a belief, and deadlock reflection through the barycenter -/

/-- **Fair-enabledness of a belief is exactly a common fair label.** A belief `ν` can take an
`F.dist`-fair `𝒟f`-step iff every state of `ν.support` enables an `F`-fair transition at one common
label. The forward direction reads the fair kernel; the backward direction clusters the fair
successors to **Diracs** (always `Resolvable`), decoupling the transition's successor beliefs from
the fair kernel's (arbitrary) outputs. -/
theorem dist_fairEnabled_iff_commonFairLabel (F : Fairness sys) (ν : PMF State) :
    F.dist.FairEnabled ν ↔ F.CommonFairLabel ν := by
  classical
  constructor
  · rintro ⟨l, ω, _, p, hp, _⟩
    refine ⟨l, fun s hs => ?_⟩
    obtain ⟨μ', hμ'⟩ := (p s).support_nonempty
    exact ⟨μ', hp s hs μ' hμ'⟩
  · rintro ⟨l, hl⟩
    set μf : State → PMF State :=
      fun s => if hs : s ∈ ν.support then (hl s hs).choose else PMF.pure sys.init with hμf
    have hμf_fair : ∀ s ∈ ν.support, F.fair s l (μf s) := by
      intro s hs; rw [hμf]; simp only [dif_pos hs]; exact (hl s hs).choose_spec
    have hM : (((ν.bind μf).map PMF.pure).bind id) = ν.bind μf := by
      rw [PMF.bind_map]; simp [PMF.bind_pure]
    refine ⟨l, (ν.bind μf).map PMF.pure, ⟨?_, ?_⟩, fun s => PMF.pure (μf s), ?_, ?_⟩
    · rw [hM]
      exact ⟨fun s => PMF.pure (μf s), fun s hs μ hμ => by
          rw [PMF.mem_support_pure_iff] at hμ; subst hμ
          exact F.step_of_fair s l (μf s) (hμf_fair s hs),
        by simp [PMF.pure_bind]⟩
    · intro σ hσ
      rw [PMF.mem_support_map_iff] at hσ
      obtain ⟨x, _, rfl⟩ := hσ
      exact F.resolvable_pure x
    · intro s hs μ' hμ'
      rw [PMF.mem_support_pure_iff] at hμ'; subst hμ'
      exact hμf_fair s hs
    · rw [hM]; simp [PMF.pure_bind]

/-- A common fair label of a barycenter `κ.bind id` restricts to each constituent belief `ν` of the
mix — its support states are a subset of the barycenter's. -/
theorem commonFairLabel_of_bind_mem (F : Fairness sys) (κ : PMF (PMF State)) {ν : PMF State}
    (hν : ν ∈ κ.support) (h : F.CommonFairLabel (κ.bind id)) : F.CommonFairLabel ν := by
  obtain ⟨l, hl⟩ := h
  refine ⟨l, fun s hs => hl s ?_⟩
  rw [PMF.mem_support_bind_iff]
  exact ⟨ν, hν, hs⟩

/-- **Fairness status of the refined transition.** `F.dist.fair` sees the refined transition and the
original abstract witness `ω.map Prod.snd` alike — they share flattened target and `Resolvable`
successors (`refinedTrans` is a `baryTrans` over the re-indexed coupling). Transfers the rank clause
across the re-choice. -/
theorem refinedTrans_fair_iff (F : Fairness sys) (ω : PMF (State_C × PMF State)) (l : Label)
    (s_A : PMF State) (hResA : ∀ ν ∈ (ω.map Prod.snd).support, F.Resolvable ν) :
    F.dist.fair s_A l (refinedTrans F ω) ↔ F.dist.fair s_A l (ω.map Prod.snd) := by
  have hRes' : ∀ s' ∈ ((reindexCoupling F ω).map Prod.fst).support,
      F.Resolvable (baryBelief (reindexCoupling F ω) s') := by
    intro s' hs'
    refine refinedTrans_resolvable F ω hResA _ ?_
    rw [refinedTrans, baryTrans, PMF.mem_support_map_iff]
    exact ⟨s', hs', rfl⟩
  have hResA' : ∀ ν ∈ ((reindexCoupling F ω).map Prod.snd).support, F.Resolvable ν := by
    rw [reindexCoupling_map_snd]; exact hResA
  rw [refinedTrans,
    baryTrans_fair_iff F (reindexCoupling F ω) _ l s_A rfl hRes' hResA',
    reindexCoupling_map_snd]

/-! ### `refinedClosure F R` is a fair strong probabilistic simulation

The `step` field is the content: match a concrete transition out of `s_C` uniformly across the
constituents `ν` of the barycenter `s_A = κ.bind id`, mix the abstract witnesses
(`distF_step_bind`), and re-choose the mix for finite support (`refinedTrans_valid`). The rank
clause transfers because `distFair_bind` is contrapositive-tight: if the *refined* mix is unfair
then (via `refinedTrans_fair_iff` and `distFair_bind`) some constituent's witness is unfair, and
that constituent's own rank clause — speaking only of the concrete side — delivers the descent. -/

/-- **The step field of the refined closure.** Every concrete transition out of `s_C` is matched by
a finite-support `𝒟f`-transition out of a barycenter `s_A` refining-closure-related to `s_C`,
coupled by `refinedClosure F R`, with the rank clause inherited from the constituent simulations. -/
theorem refinedClosure_step {sys_C : System State_C Label} (F_C : Fairness sys_C) (F : Fairness sys)
    {R : State_C → PMF State → Prop} (sim : FairStrongProbabilisticSimulation F_C F.dist R)
    {s_C : State_C} {s_A : PMF State} (hrel : refinedClosure F R s_C s_A)
    {l : Label} {μ_C : PMF State_C} (hstep : sys_C.step s_C l μ_C) :
    ∃ μ_A, (sys.distF F).step s_A l μ_A ∧ PMFRel (refinedClosure F R) μ_C μ_A ∧
      (¬ F.dist.fair s_A l μ_A →
        (F_C.fair s_C l μ_C → ∀ s'_C ∈ μ_C.support, sim.le s'_C s_C ∧ ¬ sim.le s_C s'_C) ∧
        (¬ F_C.fair s_C l μ_C → ∀ s'_C ∈ μ_C.support, sim.le s'_C s_C)) := by
  classical
  obtain ⟨⟨κ, hκR, rfl⟩, -⟩ := hrel
  -- local `bind` congruences over `κ`'s support
  have hbind_eq : ∀ {β : Type} (h : PMF State → PMF β) (q : PMF β),
      (∀ ν ∈ κ.support, h ν = q) → κ.bind h = q := by
    intro β h q hh
    ext b
    rw [PMF.bind_apply]
    have hpt : ∀ ν, κ ν * h ν b = κ ν * q b := by
      intro ν
      by_cases hν : ν ∈ κ.support
      · rw [hh ν hν]
      · have : κ ν = 0 := by simpa [PMF.mem_support_iff] using hν
        rw [this, zero_mul, zero_mul]
    rw [tsum_congr hpt, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hbind_congr : ∀ {β : Type} (h₁ h₂ : PMF State → PMF β),
      (∀ ν ∈ κ.support, h₁ ν = h₂ ν) → κ.bind h₁ = κ.bind h₂ := by
    intro β h₁ h₂ hh
    ext b
    rw [PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun ν => ?_
    by_cases hν : ν ∈ κ.support
    · rw [hh ν hν]
    · have : κ ν = 0 := by simpa [PMF.mem_support_iff] using hν
      rw [this, zero_mul, zero_mul]
  -- per-constituent abstract witnesses from the original simulation
  have hstepν : ∀ ν, ν ∈ κ.support →
      ∃ μ_Aν, (sys.distF F).step ν l μ_Aν ∧ PMFRel R μ_C μ_Aν ∧
        (¬ F.dist.fair ν l μ_Aν →
          (F_C.fair s_C l μ_C → ∀ s'_C ∈ μ_C.support, sim.le s'_C s_C ∧ ¬ sim.le s_C s'_C) ∧
          (¬ F_C.fair s_C l μ_C → ∀ s'_C ∈ μ_C.support, sim.le s'_C s_C)) :=
    fun ν hν => sim.step s_C ν (hκR ν hν) l μ_C hstep
  set g : PMF State → PMF (PMF State) :=
    fun ν => if hν : ν ∈ κ.support then (hstepν ν hν).choose else PMF.pure ν with hg
  have hg_eq : ∀ (ν) (hν : ν ∈ κ.support), g ν = (hstepν ν hν).choose := by
    intro ν hν; rw [hg]; exact dif_pos hν
  have hg_step : ∀ (ν) (hν : ν ∈ κ.support), (sys.distF F).step ν l (g ν) := by
    intro ν hν; rw [hg_eq ν hν]; exact (hstepν ν hν).choose_spec.1
  have hg_rel : ∀ (ν) (hν : ν ∈ κ.support), PMFRel R μ_C (g ν) := by
    intro ν hν; rw [hg_eq ν hν]; exact (hstepν ν hν).choose_spec.2.1
  have hg_rank : ∀ (ν) (hν : ν ∈ κ.support), ¬ F.dist.fair ν l (g ν) →
      (F_C.fair s_C l μ_C → ∀ s'_C ∈ μ_C.support, sim.le s'_C s_C ∧ ¬ sim.le s_C s'_C) ∧
      (¬ F_C.fair s_C l μ_C → ∀ s'_C ∈ μ_C.support, sim.le s'_C s_C) := by
    intro ν hν; rw [hg_eq ν hν]; exact (hstepν ν hν).choose_spec.2.2
  -- combined coupling: mix the per-constituent couplings by `κ`
  set cpl : PMF State → PMF (State_C × PMF State) :=
    fun ν => if hν : ν ∈ κ.support then (hg_rel ν hν).choose else PMF.pure (s_C, ν) with hcpl
  have hcpl_eq : ∀ (ν) (hν : ν ∈ κ.support), cpl ν = (hg_rel ν hν).choose := by
    intro ν hν; rw [hcpl]; exact dif_pos hν
  have hcpl_fst : ∀ (ν) (hν : ν ∈ κ.support), (cpl ν).map Prod.fst = μ_C := by
    intro ν hν; rw [hcpl_eq ν hν]; exact (hg_rel ν hν).choose_spec.1
  have hcpl_snd : ∀ (ν) (hν : ν ∈ κ.support), (cpl ν).map Prod.snd = g ν := by
    intro ν hν; rw [hcpl_eq ν hν]; exact (hg_rel ν hν).choose_spec.2.1
  have hcpl_R : ∀ (ν) (hν : ν ∈ κ.support), ∀ p ∈ (cpl ν).support, R p.1 p.2 := by
    intro ν hν; rw [hcpl_eq ν hν]; exact (hg_rel ν hν).choose_spec.2.2
  set ω : PMF (State_C × PMF State) := κ.bind cpl with hω
  have hωfst : ω.map Prod.fst = μ_C := by
    rw [hω, PMF.map_bind]; exact hbind_eq _ _ (fun ν hν => hcpl_fst ν hν)
  have hωsnd : ω.map Prod.snd = κ.bind g := by
    rw [hω, PMF.map_bind]; exact hbind_congr _ _ (fun ν hν => hcpl_snd ν hν)
  have hRω : ∀ p ∈ ω.support, R p.1 p.2 := by
    intro p hp
    rw [hω, PMF.mem_support_bind_iff] at hp
    obtain ⟨ν, hν, hpν⟩ := hp
    exact hcpl_R ν hν p hpν
  have hResA_ω : ∀ ν ∈ (ω.map Prod.snd).support, F.Resolvable ν := by
    rw [hωsnd]
    intro ν hν
    rw [PMF.mem_support_bind_iff] at hν
    obtain ⟨ν', hν', hνg⟩ := hν
    exact (hg_step ν' hν').2 ν hνg
  have hstepA : (sys.distF F).step (κ.bind id) l (ω.map Prod.snd) := by
    rw [hωsnd]; exact distF_step_bind F κ l g hg_step
  obtain ⟨hstepR, hcplR⟩ := refinedTrans_valid F ω μ_C l (κ.bind id) hωfst hstepA hRω
  refine ⟨refinedTrans F ω, hstepR, hcplR, fun hnf => ?_⟩
  -- rank clause: the refined mix being unfair forces some constituent unfair
  have hnf' : ¬ F.dist.fair (κ.bind id) l (κ.bind g) := by
    rw [← hωsnd]
    exact fun h => hnf ((refinedTrans_fair_iff F ω l (κ.bind id) hResA_ω).mpr h)
  have hex : ∃ ν ∈ κ.support, ¬ F.dist.fair ν l (g ν) := by
    by_contra hc
    push Not at hc
    exact hnf' (distFair_bind F κ l g hc)
  obtain ⟨ν, hν, hnfν⟩ := hex
  exact hg_rank ν hν hnfν

/-- **The refined closure is again a fair strong probabilistic simulation.** Ranks, the initial
match, and fair-deadlock reflection all transfer from `sim`; the `step` field is
`refinedClosure_step` (barycentric mixing + finite-support re-choice). This is the normalisation
step: `refinedClosure F R` matches every concrete transition by a **finite-support** `𝒟f`-witness,
which is what makes the induced abstract scheduler finitely branching. -/
noncomputable def refinedClosure_isFairSim {sys_C : System State_C Label} (F_C : Fairness sys_C)
    (F : Fairness sys) {R : State_C → PMF State → Prop}
    (sim : FairStrongProbabilisticSimulation F_C F.dist R) :
    FairStrongProbabilisticSimulation F_C F.dist (refinedClosure F R) where
  init := ⟨⟨PMF.pure (PMF.pure sys.init),
      fun ν hν => by rw [PMF.mem_support_pure_iff] at hν; subst hν; exact sim.init,
      by rw [PMF.pure_bind]; rfl⟩,
    F.resolvable_pure sys.init⟩
  le := sim.le
  le_refl := sim.le_refl
  le_trans := sim.le_trans
  lt_wf := sim.lt_wf
  step := fun _ _ hrel _ _ hstep => refinedClosure_step F_C F sim hrel hstep
  fair_deadlock := by
    intro s_C s_A hrel hFD
    obtain ⟨⟨κ, hκR, rfl⟩, -⟩ := hrel
    intro hEn
    rw [dist_fairEnabled_iff_commonFairLabel] at hEn
    obtain ⟨ν₀, hν₀⟩ := κ.support_nonempty
    have hEnν₀ : F.dist.FairEnabled ν₀ :=
      (dist_fairEnabled_iff_commonFairLabel F ν₀).mpr (commonFairLabel_of_bind_mem F κ hν₀ hEn)
    exact sim.fair_deadlock s_C ν₀ (hκR ν₀ hν₀) hFD hEnν₀

end PLTS
