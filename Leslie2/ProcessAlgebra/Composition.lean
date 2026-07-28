/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Systems.Trace

/-!
# Parallel composition of PLTS

Two parallel-composition operators over a common label alphabet `Label`, together with the
independent finite product of PMFs (`piPMF`) that the asynchronous product distributions
are built from.

* `System.parallel sys₁ sys₂ : System (State₁ × State₂) Label` — **binary** composition.
  The silent label `τ` is *interleaved* (asynchronous): a single component performs the
  internal step, the other holds its state (a Dirac). Every other (visible) label is
  *synchronised*: both components step simultaneously on the same label, and the joint
  distribution is the independent product `prodPMF`.

* `System.interleave sys : System (∀ i, State i) Label` — **fully-asynchronous**
  composition of an indexed family `sys i : System (State i) Label` over any index
  with `[DecidableEq ι]` (finite *or* infinite — e.g. `ℕ`). On *every* label
  (silent or not) exactly one component steps and all the others hold their state; the
  joint next-state distribution is the single-coordinate pushforward
  `μ_i.map (Function.update s i)`. There is no synchronisation at all. When `ι` is
  finite this equals the independent product `piPMF (Function.update (Dirac) i μ_i)`
  (lemma `interleave_step`, via `piPMF_update_pure`); the pushforward form is the
  primitive because it needs no finite product and so is well-defined over infinite `ι`.

The two independent products of PMFs used as joint next-state distributions — `prodPMF`
(binary) and `piPMF` (finite family) — are built here; Mathlib has no such constructions.
`piPMF`'s mass function is `f ↦ ∏ i, μ i (f i)`, with total-mass-one proof `tsum_pi_prod`.
-/

open scoped BigOperators

namespace PLTS

/-! ### The independent finite product of PMFs -/

/-- The mass of the independent product `∏ i, μ i (f i)` sums to `1` over the product
space `∀ i, α i`. Proven by `Fintype`-induction on the index, splitting one coordinate
per step with `ENNReal.tsum_prod'`. -/
theorem tsum_pi_prod {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, PMF (α i)) :
    (∑' f : ∀ i, α i, ∏ i, (μ i) (f i)) = 1 := by
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ (α : ι → Type _) (μ : ∀ i, PMF (α i)),
      (∑' f : ∀ i, α i, ∏ i, (μ i) (f i)) = 1)
    ?_ ?_ ?_ ι α μ
  · -- transport along an index equivalence `e : γ ≃ δ`
    intro γ δ _ e ih α μ
    letI : Fintype γ := Fintype.ofEquiv δ e.symm
    rw [← Equiv.tsum_eq (Equiv.piCongrLeft α e) (fun f => ∏ d, μ d (f d))]
    have hval : ∀ g : (∀ c, α (e c)),
        (∏ d, μ d ((Equiv.piCongrLeft α e) g d)) = ∏ c, μ (e c) (g c) := by
      intro g
      rw [← Equiv.prod_comp e (fun d => μ d ((Equiv.piCongrLeft α e) g d))]
      exact Finset.prod_congr rfl (fun c _ => by rw [Equiv.piCongrLeft_apply_apply])
    rw [tsum_congr hval]
    exact ih (fun c => α (e c)) (fun c => μ (e c))
  · -- empty index: the product space is a singleton and the product is empty
    intro α μ; simp
  · -- `Option`-step: peel off the `none` coordinate
    intro γ _ ih α μ
    rw [← Equiv.tsum_eq (Equiv.piOptionEquivProd (β := α)).symm (fun f => ∏ i, μ i (f i))]
    have hval : ∀ (p : α none × ∀ c, α (some c)),
        (∏ i, μ i ((Equiv.piOptionEquivProd (β := α)).symm p i))
          = μ none p.1 * ∏ c, μ (some c) (p.2 c) := by
      intro p
      rw [Fintype.prod_option]; rfl
    rw [tsum_congr hval, ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [tsum_congr (fun a => by
      rw [ih (fun c => α (some c)) (fun c => μ (some c)), mul_one])]
    exact (μ none).tsum_coe

/-- The **independent finite product** of a family of PMFs: the distribution on the
product space `∀ i, α i` whose mass at `f` is `∏ i, μ i (f i)`. The coordinates are
sampled independently, each `i` from `μ i`. -/
noncomputable def piPMF {ι : Type*} [Fintype ι] {α : ι → Type*} (μ : ∀ i, PMF (α i)) :
    PMF (∀ i, α i) :=
  ⟨fun f => ∏ i, μ i (f i), by rw [← tsum_pi_prod μ]; exact ENNReal.summable.hasSum⟩

@[simp] theorem piPMF_apply {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, PMF (α i)) (f : ∀ i, α i) : piPMF μ f = ∏ i, μ i (f i) := rfl

/-- The **independent product of two PMFs**: the joint distribution on `α × β` that
samples the two coordinates independently, the first from `μ₁` and the second from `μ₂`. -/
noncomputable def prodPMF {α β : Type*} (μ₁ : PMF α) (μ₂ : PMF β) : PMF (α × β) :=
  μ₁.bind fun a => μ₂.bind fun b => PMF.pure (a, b)

/-! ### `prodPMF` algebra -/

section ProdPMFAlgebra

variable {α α' β β' : Type*}

theorem prodPMF_pure_right (μ : PMF α) (b : β) :
    prodPMF μ (PMF.pure b) = μ.map (fun a => (a, b)) := by
  simp only [prodPMF, PMF.pure_bind]; rfl

theorem prodPMF_pure_left (a : α) (μ : PMF β) :
    prodPMF (PMF.pure a) μ = μ.map (fun b => (a, b)) := by
  simp only [prodPMF, PMF.pure_bind]; rfl

theorem prodPMF_map (f : α → α') (g : β → β') (μ₁ : PMF α) (μ₂ : PMF β) :
    (prodPMF μ₁ μ₂).map (fun p => (f p.1, g p.2)) = prodPMF (μ₁.map f) (μ₂.map g) := by
  simp only [prodPMF, PMF.map_bind, PMF.pure_map, PMF.bind_map, Function.comp_def]

theorem mem_support_prodPMF {μ₁ : PMF α} {μ₂ : PMF β} {p : α × β} :
    p ∈ (prodPMF μ₁ μ₂).support ↔ p.1 ∈ μ₁.support ∧ p.2 ∈ μ₂.support := by
  simp only [prodPMF, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨ha, hb⟩
  · rintro ⟨h1, h2⟩; exact ⟨p.1, h1, p.2, h2, rfl⟩

/-- Flattening the family `ρ ↦ ρ ⊗ ρ'` reached from `ω` back to a single product. -/
theorem bindId_left (ω : PMF (PMF α)) (ρ' : PMF β) :
    (ω.map (fun ρ => prodPMF ρ ρ')).bind id = prodPMF (ω.bind id) ρ' := by
  rw [PMF.bind_map, Function.id_comp]
  simp only [prodPMF, PMF.bind_bind, id_eq]

/-- Flattening the family `b ↦ ρ ⊗ δ_b` reached from `μ_B` back to a single product. -/
theorem bindId_right (ρ : PMF α) (μ_B : PMF β) :
    (μ_B.map (fun b => prodPMF ρ (PMF.pure b))).bind id = prodPMF ρ μ_B := by
  rw [PMF.bind_map, Function.id_comp]
  simp only [prodPMF, PMF.pure_bind]
  conv_rhs => rw [PMF.bind_comm]

/-- Flattening the family `(ρ,b) ↦ ρ ⊗ δ_b` reached from `ω ⊗ μ_B` back to a single product. -/
theorem bindId_sync (ω : PMF (PMF α)) (μ_B : PMF β) :
    ((prodPMF ω μ_B).map (fun p => prodPMF p.1 (PMF.pure p.2))).bind id
      = prodPMF (ω.bind id) μ_B := by
  rw [PMF.bind_map, Function.id_comp]
  simp only [prodPMF, PMF.bind_bind, PMF.pure_bind, id_eq]
  refine congrArg (fun h => ω.bind h) (funext fun ρ => ?_)
  rw [PMF.bind_comm]

end ProdPMFAlgebra

/-! ### `piPMF` / `Function.update` algebra -/

section PiPMFAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type}

/-- The mass of `piPMF (update μ_ i ρ)` at `f` factors the moved coordinate `i` (mass `ρ (f i)`)
out of the product of the held coordinates. -/
theorem piPMF_update_apply (i : ι) (μ_ : ∀ j, PMF (α j)) (ρ : PMF (α i)) (f : ∀ j, α j) :
    (piPMF (Function.update μ_ i ρ)) f = ρ (f i) * ∏ x ∈ Finset.univ.erase i, μ_ x (f x) := by
  rw [piPMF_apply, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    Function.update_self]
  exact congrArg _ (Finset.prod_congr rfl
    (fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]))

omit [DecidableEq ι] in
theorem mem_support_piPMF {μ : ∀ i, PMF (α i)} {f : ∀ i, α i} :
    f ∈ (piPMF μ).support ↔ ∀ i, f i ∈ (μ i).support := by
  rw [PMF.mem_support_iff, piPMF_apply, Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ, forall_true_left, PMF.mem_support_iff]

/-- A `piPMF` with a single non-Dirac coordinate `i` is the pushforward of that coordinate into the
product (the analog of `prodPMF_pure_right`). -/
theorem piPMF_update_pure (s : ∀ i, α i) (i : ι) (μ : PMF (α i)) :
    piPMF (Function.update (fun j => PMF.pure (s j)) i μ)
      = μ.map (fun c => Function.update s i c) := by
  ext f
  rw [piPMF_update_apply, PMF.map_apply]
  simp only [PMF.pure_apply]
  by_cases hC : ∀ x ∈ Finset.univ.erase i, f x = s x
  · have hpos : f = Function.update s i (f i) := by
      funext x
      by_cases hx : x = i
      · subst hx; rw [Function.update_self]
      · rw [Function.update_of_ne hx]
        exact hC x (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩)
    rw [Finset.prod_eq_one (fun x hx => if_pos (hC x hx)), mul_one,
      tsum_eq_single (f i) ?_, if_pos hpos]
    intro c hc
    apply if_neg
    intro heq
    apply hc
    have h := congrFun heq i
    rw [Function.update_self] at h
    exact h.symm
  · push Not at hC
    obtain ⟨x, hx, hne⟩ := hC
    rw [Finset.prod_eq_zero hx (if_neg hne), mul_zero]
    symm
    refine ENNReal.tsum_eq_zero.mpr (fun c => if_neg ?_)
    intro heq
    apply hne
    have h := congrFun heq x
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)] at h
    exact h

/-- Flattening the family `ρ ↦ piPMF (update μ_ i ρ)` reached from `ω` back to a single product
(the analog of `bindId_left`). -/
theorem bindId_update (i : ι) (μ_ : ∀ j, PMF (α j)) (ω : PMF (PMF (α i))) :
    (ω.map (fun ρ => piPMF (Function.update μ_ i ρ))).bind id
      = piPMF (Function.update μ_ i (ω.bind id)) := by
  rw [PMF.bind_map, Function.id_comp]
  ext f
  rw [PMF.bind_apply]
  simp only [piPMF_update_apply]
  rw [PMF.bind_apply]
  simp only [id_eq]
  rw [← ENNReal.tsum_mul_right]
  exact tsum_congr (fun a => by ring)

end PiPMFAlgebra

/-! ### Cofinitely-Dirac families

An independent product of PMFs over an *infinite* index is a `PMF` only when cofinitely many
factors are Dirac (else the mass function is identically `0`). `CofinPMF` records such a family
**as data** — a finite `active` set of (possibly) non-Dirac coordinates, plus a Dirac `base` for
the rest — so the product `toPMF` is total and needs no side-condition, and single-coordinate
updates keep the family cofinitely Dirac by construction (`active` only grows). This is the
belief carrier for the infinite-index interleave precongruence. -/

section CofinDirac

variable {ι : Type} [DecidableEq ι] {α : ι → Type}

/-- A **cofinitely-Dirac family** of PMFs, as data: outside the finite set `active` every
coordinate is the point mass `pure (base i)`; on `active`, coordinate `i` is distributed as
`law i` (the value of `law` off `active` is irrelevant). Finiteness of the non-Dirac support is
the field `active`, so forming the product `toPMF` never needs a side-condition and stays a
genuine `PMF` over an arbitrary (e.g. infinite) index. -/
structure CofinPMF (α : ι → Type) where
  /-- The Dirac value of every coordinate outside `active`. -/
  base : ∀ i, α i
  /-- The finite set of (possibly) non-Dirac coordinates. -/
  active : Finset ι
  /-- The law of each active coordinate (its value off `active` is irrelevant). -/
  law : ∀ i, PMF (α i)

namespace CofinPMF

/-- The effective per-coordinate law: `law i` on `active`, the Dirac base off it. This is the
`i`-th marginal of `toPMF`, and what the interleave coupling relates to the concrete state. -/
noncomputable def coord (c : CofinPMF α) (i : ι) : PMF (α i) :=
  if i ∈ c.active then c.law i else PMF.pure (c.base i)

/-- Fill a partial assignment on `active` to a total one, using the base off `active`. -/
def fill (c : CofinPMF α) (g : ∀ i : c.active, α i) : ∀ i, α i :=
  fun i => if h : i ∈ c.active then g ⟨i, h⟩ else c.base i

/-- The independent product distribution: sample each active coordinate from its law, fill the
rest from the base. Reduces to the finite `piPMF` on the `Fintype` subtype `↥active`, so its
mass-one proof is inherited (`tsum_pi_prod`), not reproved. -/
noncomputable def toPMF (c : CofinPMF α) : PMF (∀ i, α i) :=
  (piPMF (fun i : c.active => c.law i)).map c.fill

noncomputable instance : CoeHead (CofinPMF α) (PMF (∀ i, α i)) := ⟨toPMF⟩

/-- The all-Dirac family concentrated at `s` (empty active set). -/
noncomputable def dirac (s : ∀ i, α i) : CofinPMF α where
  base := s
  active := ∅
  law := fun i => PMF.pure (s i)

/-- Re-law coordinate `i` to `ρ`, marking it active. `active` only ever grows, so iterating
keeps the family cofinitely Dirac by construction. -/
noncomputable def update (c : CofinPMF α) (i : ι) (ρ : PMF (α i)) : CofinPMF α where
  base := c.base
  active := insert i c.active
  law := Function.update c.law i ρ

@[simp] theorem coord_update_self (c : CofinPMF α) (i : ι) (ρ : PMF (α i)) :
    (c.update i ρ).coord i = ρ := by
  simp [coord, update]

theorem coord_update_ne (c : CofinPMF α) (i : ι) (ρ : PMF (α i)) {j : ι} (h : j ≠ i) :
    (c.update i ρ).coord j = c.coord j := by
  show (if j ∈ insert i c.active then Function.update c.law i ρ j else PMF.pure (c.base j))
      = if j ∈ c.active then c.law j else PMF.pure (c.base j)
  simp only [Finset.mem_insert, h, false_or, Function.update_of_ne h]

/-- The mass of `toPMF` at a point `f` that matches the base off `active`: the finite product of
the active laws. -/
theorem toPMF_apply (c : CofinPMF α) (f : ∀ i, α i)
    (hf : ∀ i, i ∉ c.active → f i = c.base i) :
    c.toPMF f = ∏ i ∈ c.active, c.law i (f i) := by
  rw [toPMF, PMF.map_apply]
  rw [tsum_eq_single (fun i : c.active => f ↑i)]
  · rw [if_pos, piPMF_apply, Finset.prod_coe_sort c.active (fun i => c.law i (f i))]
    funext i
    by_cases hi : i ∈ c.active
    · simp only [fill, dif_pos hi]
    · simp only [fill, dif_neg hi, hf i hi]
  · intro g hg
    rw [if_neg]
    intro hcontra
    apply hg
    funext i
    have := congrFun hcontra ↑i
    rw [fill, dif_pos i.2] at this
    exact this.symm

/-- `toPMF` vanishes at any point that disagrees with the base somewhere off `active`. -/
theorem toPMF_apply_of_not (c : CofinPMF α) (f : ∀ i, α i)
    (hf : ¬ ∀ i, i ∉ c.active → f i = c.base i) :
    c.toPMF f = 0 := by
  rw [toPMF, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro g
  rw [if_neg]
  intro hcontra
  apply hf
  intro i hi
  have := congrFun hcontra i
  rw [fill, dif_neg hi] at this
  exact this

/-- **The step-collapse identity.** Mixing a belief-of-laws `ω` into coordinate `i` and
flattening equals re-lawing `i` by `ω.bind id`. The infinite-index analogue of `bindId_update`;
coordinate `i` is singled out by construction, so no product reindexing is needed. -/
theorem bind_toPMF_update (c : CofinPMF α) (i : ι) (ω : PMF (PMF (α i))) :
    (ω.map (fun ρ => (c.update i ρ).toPMF)).bind id = (c.update i (ω.bind id)).toPMF := by
  rw [PMF.bind_map, Function.id_comp]
  ext f
  rw [PMF.bind_apply]
  by_cases hf : ∀ j, j ∉ insert i c.active → f j = c.base j
  · set P := ∏ j ∈ (insert i c.active).erase i, c.law j (f j) with hP
    have hsplit : ∀ ρ : PMF (α i),
        (∏ j ∈ insert i c.active, (Function.update c.law i ρ) j (f j)) = ρ (f i) * P := by
      intro ρ
      rw [← Finset.mul_prod_erase (insert i c.active)
        (fun j => (Function.update c.law i ρ) j (f j)) (Finset.mem_insert_self i c.active),
        Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have hpos : ∀ a : PMF (α i), (c.update i a).toPMF f = a (f i) * P := by
      intro a
      rw [(c.update i a).toPMF_apply f hf]
      exact hsplit a
    rw [hpos (ω.bind id)]
    have hbind : (ω.bind id) (f i) = ∑' a, ω a * a (f i) := by
      rw [PMF.bind_apply]; exact tsum_congr (fun a => by rw [id_eq])
    rw [hbind, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro a
    rw [hpos a, mul_assoc]
  · rw [(c.update i (ω.bind id)).toPMF_apply_of_not f hf]
    apply ENNReal.tsum_eq_zero.mpr
    intro a
    rw [(c.update i a).toPMF_apply_of_not f hf, mul_zero]

@[simp] theorem toPMF_dirac (s : ∀ i, α i) : (dirac s : CofinPMF α).toPMF = PMF.pure s := by
  have hfill : (dirac s).fill = fun _ => s := by
    funext g; funext i; simp [fill, dirac]
  unfold toPMF
  rw [hfill]
  simp only [PMF.map, Function.comp_def]
  exact PMF.bind_const _ _

/-- Re-lawing coordinate `i` to its own current marginal `coord i` leaves the product unchanged. -/
theorem toPMF_update_coord_self (c : CofinPMF α) (i : ι) :
    (c.update i (c.coord i)).toPMF = c.toPMF := by
  by_cases hi : i ∈ c.active
  · -- `i` already active: `update i (coord i)` is the same data as `c`.
    have hupd : c.update i (c.coord i) = c := by
      cases c with | mk base active law =>
      simp only [update, coord] at *
      rw [Finset.insert_eq_self.mpr hi, if_pos hi, Function.update_eq_self]
    rw [hupd]
  · -- `i` off active: `coord i = pure (base i)`; compare masses pointwise.
    have hcoord : c.coord i = PMF.pure (c.base i) := by rw [coord, if_neg hi]
    refine PMF.ext fun f => ?_
    -- On `active`, the updated law agrees with `c.law` (the moved coordinate `i` is off `active`).
    have htail : (∏ j ∈ c.active, (Function.update c.law i (c.coord i)) j (f j))
        = ∏ j ∈ c.active, c.law j (f j) :=
      Finset.prod_congr rfl fun j hj => by
        have hne : j ≠ i := fun h => hi (h ▸ hj)
        rw [Function.update_of_ne hne]
    by_cases hm : ∀ j, j ∉ c.active → f j = c.base j
    · -- RHS support predicate holds; LHS predicate follows since `active ⊆ insert i active`.
      have hm' : ∀ j, j ∉ insert i c.active → f j = c.base j := fun j hj =>
        hm j (fun hj' => hj (Finset.mem_insert_of_mem hj'))
      rw [(c.update i (c.coord i)).toPMF_apply f hm', c.toPMF_apply f hm]
      change (∏ j ∈ insert i c.active, (Function.update c.law i (c.coord i)) j (f j))
        = ∏ j ∈ c.active, c.law j (f j)
      rw [← Finset.mul_prod_erase (insert i c.active)
        (fun j => (Function.update c.law i (c.coord i)) j (f j))
        (Finset.mem_insert_self i c.active), Function.update_self,
        Finset.erase_insert hi, htail, hcoord]
      have hone : (PMF.pure (c.base i)) (f i) = 1 := by
        rw [PMF.pure_apply, if_pos (hm i hi)]
      rw [hone, one_mul]
    · -- RHS support predicate fails, so RHS = 0. For LHS, split on its own predicate.
      rw [c.toPMF_apply_of_not f hm]
      by_cases hm' : ∀ j, j ∉ insert i c.active → f j = c.base j
      · -- LHS predicate holds, so the disagreement forcing `hm` false must be at `i` itself,
        -- and the moved coordinate is Dirac at `base i`, giving mass `0`.
        have hfi : f i ≠ c.base i := by
          intro heq
          exact hm fun j hj => by
            rcases eq_or_ne j i with rfl | hne
            · exact heq
            · exact hm' j (fun hj'' => hj (Finset.mem_of_mem_insert_of_ne hj'' hne))
        rw [(c.update i (c.coord i)).toPMF_apply f hm']
        change (∏ j ∈ insert i c.active, (Function.update c.law i (c.coord i)) j (f j)) = 0
        rw [← Finset.mul_prod_erase (insert i c.active)
          (fun j => (Function.update c.law i (c.coord i)) j (f j))
          (Finset.mem_insert_self i c.active), Function.update_self, hcoord]
        rw [PMF.pure_apply, if_neg hfi, zero_mul]
      · rw [(c.update i (c.coord i)).toPMF_apply_of_not f hm']

/-- **Resample identity.** The updated product is: draw the whole state from the *current*
product, then overwrite coordinate `i` by an independent draw from `ν`. This is the bundled
replacement for `piPMF μ = (piPMF μ).bind (fun s => (μ i).map (update s i))`, and drives the lift
lemmas. -/
theorem toPMF_update_eq_bind (c : CofinPMF α) (i : ι) (ν : PMF (α i)) :
    (c.update i ν).toPMF = c.toPMF.bind (fun s => ν.map (Function.update s i)) := by
  classical
  refine PMF.ext fun f => ?_
  set Q := ∀ j, j ∉ c.active → j ≠ i → f j = c.base j with hQdef
  set P := ∏ j ∈ c.active.erase i, c.law j (f j) with hPdef
  set M := ∑' y : α i, c.toPMF (Function.update f i y) with hMdef
  -- The marginal `M` (integrating out coordinate `i`) equals `if Q then P else 0`.
  have hM : M = (if Q then P else 0) := by
    rw [hMdef, hPdef]
    by_cases hQ : Q
    · rw [if_pos hQ]
      by_cases hi : i ∈ c.active
      · have hne : ∀ j, j ∉ c.active → j ≠ i := fun j hj h => hj (h ▸ hi)
        have hval : ∀ y, c.toPMF (Function.update f i y)
            = c.law i y * ∏ j ∈ c.active.erase i, c.law j (f j) := by
          intro y
          have hpred : ∀ j, j ∉ c.active → (Function.update f i y) j = c.base j := by
            intro j hj
            rw [Function.update_of_ne (hne j hj)]
            exact hQ j hj (hne j hj)
          rw [c.toPMF_apply _ hpred,
            ← Finset.mul_prod_erase c.active (fun j => c.law j ((Function.update f i y) j)) hi,
            Function.update_self]
          congr 1
          apply Finset.prod_congr rfl
          intro j hj
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        simp_rw [hval]
        rw [ENNReal.tsum_mul_right, (c.law i).tsum_coe, one_mul]
      · rw [Finset.erase_eq_of_notMem hi, tsum_eq_single (c.base i)]
        · have hpred : ∀ j, j ∉ c.active → (Function.update f i (c.base i)) j = c.base j := by
            intro j hj
            by_cases hj2 : j = i
            · subst hj2; rw [Function.update_self]
            · rw [Function.update_of_ne hj2]; exact hQ j hj hj2
          rw [c.toPMF_apply _ hpred]
          apply Finset.prod_congr rfl
          intro j hj
          have hji : j ≠ i := by rintro rfl; exact hi hj
          rw [Function.update_of_ne hji]
        · intro y hy
          apply c.toPMF_apply_of_not
          intro hcon
          apply hy
          have := hcon i hi
          rw [Function.update_self] at this
          exact this
    · rw [if_neg hQ]
      apply ENNReal.tsum_eq_zero.mpr
      intro y
      apply c.toPMF_apply_of_not
      intro hcon
      apply hQ
      intro j hj hji
      have := hcon j hj
      rw [Function.update_of_ne hji] at this
      exact this
  -- The LHS mass factors the moved coordinate `ν (f i)` out of `if Q then P else 0`.
  have hLHS : (c.update i ν).toPMF f = ν (f i) * (if Q then P else 0) := by
    rw [hPdef]
    have hQiff : (∀ j, j ∉ insert i c.active → f j = c.base j) ↔ Q := by
      rw [hQdef]
      constructor
      · intro h j hj hji
        exact h j (fun hh => (Finset.mem_insert.mp hh).elim (fun e => hji e) (fun e => hj e))
      · intro h j hj
        exact h j (fun hh => hj (Finset.mem_insert_of_mem hh))
          (fun e => hj (e ▸ Finset.mem_insert_self i c.active))
    by_cases hQ : Q
    · rw [if_pos hQ]
      have hpred : ∀ j, j ∉ insert i c.active → f j = c.base j := hQiff.mpr hQ
      rw [(c.update i ν).toPMF_apply f hpred]
      change (∏ j ∈ insert i c.active, (Function.update c.law i ν) j (f j))
        = ν (f i) * ∏ j ∈ c.active.erase i, c.law j (f j)
      rw [← Finset.mul_prod_erase (insert i c.active)
        (fun j => (Function.update c.law i ν) j (f j)) (Finset.mem_insert_self i c.active),
        Function.update_self]
      congr 1
      rw [Finset.erase_insert_eq_erase]
      apply Finset.prod_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    · rw [if_neg hQ, mul_zero]
      apply (c.update i ν).toPMF_apply_of_not
      intro h
      exact hQ (hQiff.mp h)
  -- The RHS mass: bind unfolds, the inner pushforward collapses to `ν (f i)` on the agreeing
  -- states, and the restricted sum is the marginal `M`.
  have hRHS : (c.toPMF.bind (fun s => ν.map (Function.update s i))) f = ν (f i) * M := by
    rw [PMF.bind_apply]
    have hinner : ∀ s : ∀ j, α j,
        (ν.map (Function.update s i)) f
          = (if (∀ j, j ≠ i → f j = s j) then ν (f i) else 0) := by
      intro s
      rw [PMF.map_apply]
      by_cases hc : ∀ j, j ≠ i → f j = s j
      · rw [if_pos hc, tsum_eq_single (f i)]
        · rw [if_pos]
          ext j
          by_cases hj : j = i
          · subst hj; rw [Function.update_self]
          · rw [Function.update_of_ne hj]; exact hc j hj
        · intro x hx
          rw [if_neg]
          intro heq
          apply hx
          have := congrFun heq i
          rw [Function.update_self] at this
          exact this.symm
      · rw [if_neg hc]
        apply ENNReal.tsum_eq_zero.mpr
        intro x
        rw [if_neg]
        intro heq
        apply hc
        intro j hj
        have := congrFun heq j
        rw [Function.update_of_ne hj] at this
        exact this
    simp_rw [hinner]
    have hstep : ∀ s : ∀ j, α j,
        c.toPMF s * (if (∀ j, j ≠ i → f j = s j) then ν (f i) else 0)
          = ν (f i) * (c.toPMF s * (if (∀ j, j ≠ i → f j = s j) then 1 else 0)) := by
      intro s
      by_cases hc : ∀ j, j ≠ i → f j = s j
      · rw [if_pos hc, if_pos hc]; ring
      · rw [if_neg hc, if_neg hc, mul_zero, mul_zero]
    simp_rw [hstep]
    rw [ENNReal.tsum_mul_left]
    congr 1
    rw [hMdef]
    symm
    refine tsum_eq_tsum_of_ne_zero_bij
      (fun (s : Function.support (fun s => c.toPMF s * (if (∀ j, j ≠ i → f j = s j)
          then (1 : ENNReal) else 0))) => (s : ∀ j, α j) i) ?_ ?_ ?_
    · rintro ⟨s, hs⟩ ⟨t, ht⟩ hst
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hs ht
      simp only at hst
      have hcs : (∀ j, j ≠ i → f j = s j) := by by_contra h; simp [h] at hs
      have hct : (∀ j, j ≠ i → f j = t j) := by by_contra h; simp [h] at ht
      refine Subtype.ext ?_
      change s = t
      ext j
      by_cases hj : j = i
      · subst hj; exact hst
      · rw [← hcs j hj, ← hct j hj]
    · intro y hy
      simp only [Function.mem_support, ne_eq] at hy
      have hcond : (∀ j, j ≠ i → f j = Function.update f i y j) := by
        intro j hj; rw [Function.update_of_ne hj]
      rw [Set.mem_range]
      refine ⟨⟨Function.update f i y, ?_⟩, ?_⟩
      · simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or]
        exact ⟨hy, by rw [if_pos hcond]; exact one_ne_zero⟩
      · change Function.update f i y i = y
        rw [Function.update_self]
    · rintro ⟨s, hs⟩
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hs
      have hcs : (∀ j, j ≠ i → f j = s j) := by by_contra h; simp [h] at hs
      simp only
      rw [if_pos hcs, mul_one]
      congr 1
      change Function.update f i (s i) = s
      ext j
      by_cases hj : j = i
      · subst hj; rw [Function.update_self]
      · rw [Function.update_of_ne hj, hcs j hj]
  rw [hLHS, hRHS, hM]

/-- Resampling coordinate `i` from its own marginal `coord i`, holding the rest, is the identity
on the product. The `ν := coord i` specialisation of `toPMF_update_eq_bind`. -/
theorem toPMF_self_bind (c : CofinPMF α) (i : ι) :
    c.toPMF = c.toPMF.bind (fun s => (c.coord i).map (Function.update s i)) := by
  conv_lhs => rw [← toPMF_update_coord_self c i]
  rw [toPMF_update_eq_bind]

end CofinPMF

end CofinDirac

/-! ### Binary composition: `τ` interleaved, visible labels synchronised -/

section Binary

variable {State₁ State₂ Label : Type} [Silent Label]

namespace System

/-- **Binary parallel composition** over a common label alphabet. On a visible label
`l ≠ τ` both components must step simultaneously (synchronisation), yielding the
independent product `prodPMF`; on the silent label `τ` exactly one component steps and
the other holds its state (interleaving). -/
def parallel (sys₁ : System State₁ Label) (sys₂ : System State₂ Label) :
    System (State₁ × State₂) Label where
  init := (sys₁.init, sys₂.init)
  step p l μ :=
    -- Synchronised visible step: `l ≠ τ` and both components step.
    (l ≠ Silent.τ ∧
      ∃ μ₁ μ₂, sys₁.step p.1 l μ₁ ∧ sys₂.step p.2 l μ₂ ∧ μ = prodPMF μ₁ μ₂) ∨
    -- Left interleaved `τ`-step: only `sys₁` steps.
    (l = Silent.τ ∧ ∃ μ₁, sys₁.step p.1 l μ₁ ∧ μ = prodPMF μ₁ (PMF.pure p.2)) ∨
    -- Right interleaved `τ`-step: only `sys₂` steps.
    (l = Silent.τ ∧ ∃ μ₂, sys₂.step p.2 l μ₂ ∧ μ = prodPMF (PMF.pure p.1) μ₂)

@[simp] theorem parallel_init (sys₁ : System State₁ Label) (sys₂ : System State₂ Label) :
    (parallel sys₁ sys₂).init = (sys₁.init, sys₂.init) := rfl

theorem parallel_step (sys₁ : System State₁ Label) (sys₂ : System State₂ Label)
    (p : State₁ × State₂) (l : Label) (μ : PMF (State₁ × State₂)) :
    (parallel sys₁ sys₂).step p l μ ↔
      (l ≠ Silent.τ ∧
        ∃ μ₁ μ₂, sys₁.step p.1 l μ₁ ∧ sys₂.step p.2 l μ₂ ∧ μ = prodPMF μ₁ μ₂) ∨
      (l = Silent.τ ∧ ∃ μ₁, sys₁.step p.1 l μ₁ ∧ μ = prodPMF μ₁ (PMF.pure p.2)) ∨
      (l = Silent.τ ∧ ∃ μ₂, sys₂.step p.2 l μ₂ ∧ μ = prodPMF (PMF.pure p.1) μ₂) :=
  Iff.rfl

end System

end Binary

/-! ### Fully-asynchronous composition of an indexed family -/

section Family

variable {ι : Type} [DecidableEq ι] {State : ι → Type} {Label : Type}

namespace System

/-- **Fully-asynchronous (interleaving) parallel composition** of an indexed family of PLTS,
over any index type with `[DecidableEq ι]` (finite *or* infinite, e.g. `ℕ`).
On *every* label, exactly one component `i` steps `sys i (s i) l μ_i` while all the other
components hold their current state; the joint next-state distribution is the single-coordinate
pushforward `μ_i.map (Function.update s i)`. No label is ever synchronised.

The pushforward form is the primitive (rather than the independent product
`piPMF (Function.update (Dirac) i μ_i)`) because it needs no finite product, so it is
well-defined for infinite `ι`; the two agree when `ι` is finite (`interleave_step`). -/
def interleave (sys : ∀ i, System (State i) Label) :
    System (∀ i, State i) Label where
  init := fun i => (sys i).init
  step s l μ := ∃ (i : ι) (μ_i : PMF (State i)), (sys i).step (s i) l μ_i ∧
    μ = μ_i.map (Function.update s i)

@[simp] theorem interleave_init (sys : ∀ i, System (State i) Label) :
    (interleave sys).init = fun i => (sys i).init := rfl

/-- The step relation of `interleave`, in the primitive single-coordinate pushforward form
(no finiteness needed). -/
theorem interleave_step_map (sys : ∀ i, System (State i) Label)
    (s : ∀ i, State i) (l : Label) (μ : PMF (∀ i, State i)) :
    (interleave sys).step s l μ ↔
      ∃ (i : ι) (μ_i : PMF (State i)), (sys i).step (s i) l μ_i ∧
        μ = μ_i.map (Function.update s i) :=
  Iff.rfl

/-- The step relation of `interleave` in independent-product (`piPMF`) form. Available only
for finite `ι`, where the single-coordinate pushforward and the finite product coincide
(`piPMF_update_pure`). Provided for backward compatibility with the finite-family metatheory
(`ProcessAlgebra/Interleave.lean`, `Results.lean`). -/
theorem interleave_step [Fintype ι] (sys : ∀ i, System (State i) Label)
    (s : ∀ i, State i) (l : Label) (μ : PMF (∀ i, State i)) :
    (interleave sys).step s l μ ↔
      ∃ (i : ι) (μ_i : PMF (State i)), (sys i).step (s i) l μ_i ∧
        μ = piPMF (Function.update (fun j => PMF.pure (s j)) i μ_i) := by
  simp only [interleave_step_map, piPMF_update_pure]

end System

end Family

end PLTS
