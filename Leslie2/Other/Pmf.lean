/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# PMF utility lemmas

Small helpers about `PMF.pure` and `PMF.map` not present in Mathlib.
-/

namespace PMF

variable {α β : Type*}

/-- `PMF.pure` is injective: two Diracs are equal only on equal points. -/
theorem pure_injective : Function.Injective (@PMF.pure α) := by
  intro a b h
  by_contra hne
  simpa [PMF.pure_apply, hne] using DFunLike.congr_fun h a

/-- `PMF.map f` is injective whenever `f` is. -/
theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (PMF.map f) := by
  intro p q h
  ext a
  have h1 : (p.map f) (f a) = (q.map f) (f a) := by rw [h]
  rw [PMF.map_apply, PMF.map_apply] at h1
  rw [tsum_eq_single a (fun b hb => if_neg (fun heq => hb (hf heq).symm))] at h1
  rw [tsum_eq_single a (fun b hb => if_neg (fun heq => hb (hf heq).symm))] at h1
  rwa [if_pos rfl, if_pos rfl] at h1

end PMF
