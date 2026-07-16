/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace PLTS

variable {α β : Type}

/-- **`tsum` over an `Option` type splits** as the value at `none` plus the `tsum`
over the `some`-fibres. (Local `ENNReal` specialisation; no such `tsum_option`
exists in this Mathlib revision, and every `ENNReal` family is summable.) -/
theorem ENNReal.tsum_option' {β : Type*} (f : Option β → ENNReal) :
    (∑' x, f x) = f none + ∑' y, f (some y) := by
  rw [_root_.ENNReal.tsum_eq_add_tsum_ite none]
  congr 1
  rw [tsum_eq_tsum_of_ne_zero_bij (i := fun y : {y : β // f (some y) ≠ 0} => some y.1)]
  · intro a b hab; exact Subtype.ext (Option.some_injective β hab)
  · intro x hx
    cases hx2 : (x : Option β) with
    | none => simp [Function.mem_support, hx2] at hx
    | some y =>
      refine ⟨⟨y, ?_⟩, ?_⟩
      · simp only [Function.mem_support] at hx ⊢
        rw [hx2] at hx; simpa using hx
      · simp
  · intro y; simp

end PLTS
