/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2.ProcessAlgebra.Composition
import Leslie2.Systems.LTS

/-!
# Full-synchronisation product of a finite family

`System.syncProduct sys` composes a finite family `sys i : System (State i) Label`
over one shared alphabet under **full synchronisation**: on every visible label
*all* components step simultaneously on that label, and the joint next-state
distribution is the independent product `piPMF`. The silent label `τ` is the sole
exception — it is interleaved, exactly one component moving while the others hold
their state, as in `System.parallel`.

This is the dual of `System.interleave` (in `ProcessAlgebra/Composition.lean`),
which synchronises nothing; the sync-set composition `∥_S` sits between the two
and is recovered from `syncProduct` by the **rendezvous idiom**:

* every component carries idle self-loops (`System.withIdle`, in
  `Framework/IdleFamily.lean`) on the labels it does not own, so a component that
  is not a participant answers a foreign handshake by standing still;
* a label owned by exactly two components is then a communication: it moves those
  two and leaves every other component where it is;
* a label owned by no component is blocked — no component offers it, so the
  conjunction over all components is unsatisfiable and the product has no such
  transition.

Ownership is thus expressed on the components, not on the product operator, which
keeps the operator itself uniform: a single conjunction over the whole family.

Full synchronisation preserves `System.IsLTS` (`System.syncProduct_isLTS`): a
product of Diracs is the Dirac on the tuple of their points (`piPMF_pure`), and a
single-coordinate update of an all-Dirac family is a Dirac too
(`piPMF_update_pure`).
-/

namespace PLTS

/-! ### Products of Diracs -/

section PiPMFPure

variable {ι : Type} [Fintype ι] {α : ι → Type}

/-- The independent product of Diracs is the Dirac on the tuple of their points. -/
theorem piPMF_pure (x : ∀ i, α i) : piPMF (fun i => PMF.pure (x i)) = PMF.pure x := by
  classical
  ext f
  simp only [piPMF_apply, PMF.pure_apply]
  by_cases hf : f = x
  · subst hf; simp
  · rw [if_neg hf]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hf
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

end PiPMFPure

/-! ### The full-synchronisation product -/

section Family

variable {ι : Type} [Fintype ι] [DecidableEq ι] {State : ι → Type} {Label : Type} [Silent Label]

namespace System

/-- **Full-synchronisation composition** of a finite family of PLTS over a common
label alphabet. On a visible label `l ≠ τ` *every* component steps simultaneously
on `l`, and the joint next-state distribution is the independent product `piPMF`
of the per-component distributions; on the silent label `τ` exactly one component
steps and all the others hold their state (the `Function.update` of the all-Dirac
family used by `System.interleave`). -/
def syncProduct (sys : ∀ i, System (State i) Label) :
    System (∀ i, State i) Label where
  init := fun i => (sys i).init
  step s l μ :=
    -- Synchronised visible step: `l ≠ τ` and every component steps on `l`.
    (l ≠ Silent.τ ∧ ∃ μ_ : ∀ i, PMF (State i),
      (∀ i, (sys i).step (s i) l (μ_ i)) ∧ μ = piPMF μ_) ∨
    -- Interleaved `τ`-step: one component steps, the others hold their state.
    (l = Silent.τ ∧ ∃ (i : ι) (μ_i : PMF (State i)),
      (sys i).step (s i) Silent.τ μ_i ∧
      μ = piPMF (Function.update (fun j => PMF.pure (s j)) i μ_i))

@[simp] theorem syncProduct_init (sys : ∀ i, System (State i) Label) :
    (syncProduct sys).init = fun i => (sys i).init := rfl

@[simp] theorem syncProduct_step (sys : ∀ i, System (State i) Label)
    (s : ∀ i, State i) (l : Label) (μ : PMF (∀ i, State i)) :
    (syncProduct sys).step s l μ ↔
      (l ≠ Silent.τ ∧ ∃ μ_ : ∀ i, PMF (State i),
        (∀ i, (sys i).step (s i) l (μ_ i)) ∧ μ = piPMF μ_) ∨
      (l = Silent.τ ∧ ∃ (i : ι) (μ_i : PMF (State i)),
        (sys i).step (s i) Silent.τ μ_i ∧
        μ = piPMF (Function.update (fun j => PMF.pure (s j)) i μ_i)) :=
  Iff.rfl

/-- A full-synchronisation product of LTS components is an LTS: the synchronised
distribution is a product of Diracs, and the interleaved one a single-coordinate
update of an all-Dirac family. -/
theorem syncProduct_isLTS {sys : ∀ i, System (State i) Label}
    (h : ∀ i, (sys i).IsLTS) : (syncProduct sys).IsLTS := by
  classical
  rintro s l μ (⟨-, μ_, hstep, rfl⟩ | ⟨-, i, μ_i, hstep, rfl⟩)
  · choose x hx using fun i => h i (s i) l (μ_ i) (hstep i)
    exact ⟨x, by rw [funext hx]; exact piPMF_pure x⟩
  · obtain ⟨x, rfl⟩ := h i (s i) Silent.τ μ_i hstep
    exact ⟨Function.update s i x, by rw [piPMF_update_pure, PMF.pure_map]⟩

end System

end Family

end PLTS
