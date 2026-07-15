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
  composition of a finite family `sys i : System (State i) Label`. On *every* label
  (silent or not) exactly one component steps and all the others hold their state; the
  joint next-state distribution is the independent product `piPMF` of the moving
  component's distribution with the Diracs of the others (`Function.update` of the
  all-Dirac family). There is no synchronisation at all.

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
  · push_neg at hC
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

/-! ### Fully-asynchronous composition of a finite family -/

section Family

variable {ι : Type} [Fintype ι] [DecidableEq ι] {State : ι → Type} {Label : Type}

namespace System

/-- **Fully-asynchronous (interleaving) parallel composition** of a finite family of PLTS.
On *every* label, exactly one component `i` steps `sys i (s i) l μ_i` while all the other
components hold their current state; the joint next-state distribution is the independent
product `piPMF` where coordinate `i` is `μ_i` and every other coordinate is the Dirac
`PMF.pure (s j)` (i.e. `Function.update` of the all-Dirac family at `i`). No label is ever
synchronised. -/
def interleave (sys : ∀ i, System (State i) Label) :
    System (∀ i, State i) Label where
  init := fun i => (sys i).init
  step s l μ := ∃ (i : ι) (μ_i : PMF (State i)), (sys i).step (s i) l μ_i ∧
    μ = piPMF (Function.update (fun j => PMF.pure (s j)) i μ_i)

@[simp] theorem interleave_init (sys : ∀ i, System (State i) Label) :
    (interleave sys).init = fun i => (sys i).init := rfl

theorem interleave_step (sys : ∀ i, System (State i) Label)
    (s : ∀ i, State i) (l : Label) (μ : PMF (∀ i, State i)) :
    (interleave sys).step s l μ ↔
      ∃ (i : ι) (μ_i : PMF (State i)), (sys i).step (s i) l μ_i ∧
        μ = piPMF (Function.update (fun j => PMF.pure (s j)) i μ_i) :=
  Iff.rfl

end System

end Family

/-! ### Abstraction: hiding a set of labels as `τ` -/

section Abstraction

variable {State Label : Type} [Silent Label]

namespace System

/-- **Abstraction.** `sys.abstract L` relabels every `L`-labelled transition of `sys` to `τ`,
leaving labels outside `L` (and original `τ`-transitions) untouched. On the silent label the
outgoing transitions are the original `τ`-steps *together with* every `L`-labelled step; on a
label `l' ∉ L` they are exactly the original `l'`-steps. -/
def abstract (sys : System State Label) (L : Set Label) : System State Label where
  init := sys.init
  step s l' μ :=
    (l' = Silent.τ ∧ ∃ l ∈ L, sys.step s l μ) ∨ (l' ∉ L ∧ sys.step s l' μ)

@[simp] theorem abstract_init (sys : System State Label) (L : Set Label) :
    (sys.abstract L).init = sys.init := rfl

theorem abstract_step (sys : System State Label) (L : Set Label)
    (s : State) (l' : Label) (μ : PMF State) :
    (sys.abstract L).step s l' μ ↔
      (l' = Silent.τ ∧ ∃ l ∈ L, sys.step s l μ) ∨ (l' ∉ L ∧ sys.step s l' μ) :=
  Iff.rfl

end System

end Abstraction

end PLTS
