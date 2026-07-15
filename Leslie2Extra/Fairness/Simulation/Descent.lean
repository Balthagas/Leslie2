/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Systems.System

/-!
# Well-founded descent (the order-theoretic core of fair simulation soundness)

The self-contained order-theoretic heart of fair-trace soundness for
`FairStrongProbabilisticSimulation` (`Simulation/Fair/Defs.lean`): `no_infinite_descending`
(a well-founded relation has no infinite descending chain) and `descent_of_infinitely_often`
(a rank sequence that is non-increasing in a pre-order `le` and strictly decreasing in a compatible
well-founded companion `lt` at infinitely many positions cannot exist). This is exactly what turns
"the abstract run stalls on unfair `τ`-steps forever while the concrete run fires fairly infinitely
often" into a contradiction, and it needs no finiteness assumption. Kept generic (over an arbitrary
`γ`) and free of the simulation machinery so it can be reused.
-/

open Stream'

namespace PLTS

/-! ### Well-founded descent (the fairness core)

The self-contained order-theoretic heart of fair soundness: a rank sequence that is non-increasing
in a pre-order `le` and strictly decreasing in a compatible well-founded companion `lt` at
infinitely many positions cannot exist. This is exactly what turns "the abstract run stalls on
unfair `τ`-steps forever while the concrete run fires fairly infinitely often" into a contradiction,
and it needs no finiteness assumption. -/

/-- A well-founded relation admits no infinite descending chain. -/
theorem no_infinite_descending {γ : Type*} {r : γ → γ → Prop} (hwf : WellFounded r)
    (f : ℕ → γ) (hf : ∀ n, r (f (n + 1)) (f n)) : False := by
  suffices H : ∀ a : γ, ∀ k : ℕ, f k = a → False from H (f 0) 0 rfl
  intro a
  induction a using hwf.induction with
  | _ x ih => intro k hk; exact ih (f (k + 1)) (hk ▸ hf k) (k + 1) rfl

/-- **Well-founded descent for a run.** If a rank sequence `g : ℕ → γ` is non-increasing in a
pre-order `le` (`hle`), strictly decreasing in a compatible well-founded companion `lt` at every
position satisfying `P` (`hlt`), and `P` holds infinitely often (`hinf`), then `False`. Instantiated
in fair soundness with `g n =` the concrete rank at step `n`, `P n =` "step `n` is a fair concrete
step", on the tail where every matched abstract step is unfair. -/
theorem descent_of_infinitely_often {γ : Type*} {le lt : γ → γ → Prop}
    (hwf : WellFounded lt)
    (hrefl : ∀ a, le a a)
    (htrans : ∀ {a b c}, le a b → le b c → le a c)
    (hcompat : ∀ {a b c}, le a b → lt b c → lt a c)
    (g : ℕ → γ) (hle : ∀ n, le (g (n + 1)) (g n))
    (P : ℕ → Prop) (hlt : ∀ n, P n → lt (g (n + 1)) (g n))
    (hinf : ∀ N : ℕ, ∃ n, N ≤ n ∧ P n) : False := by
  -- `g` is `le`-monotone (non-increasing): `m ≤ n → le (g n) (g m)`.
  have hmono : ∀ m n, m ≤ n → le (g n) (g m) := by
    intro m n hmn
    induction n with
    | zero => obtain rfl : m = 0 := Nat.le_zero.mp hmn; exact hrefl _
    | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hlt' | hge
      · exact htrans (hle k) (ih (Nat.lt_succ_iff.mp hlt'))
      · obtain rfl : m = k + 1 := Nat.le_antisymm hmn hge; exact hrefl _
  -- at a `P`-position `n`, any later index `m ≥ n + 1` has `lt (g m) (g n)`.
  have hdrop : ∀ n, P n → ∀ m, n + 1 ≤ m → lt (g m) (g n) :=
    fun n hn m hm => hcompat (hmono (n + 1) m hm) (hlt n hn)
  -- choose an increasing sequence of `P`-positions.
  let pos : ℕ → ℕ := fun k => Nat.rec (hinf 0).choose (fun _ p => (hinf (p + 1)).choose) k
  have hposP : ∀ k, P (pos k) := by
    intro k; cases k with
    | zero => exact (hinf 0).choose_spec.2
    | succ j => exact (hinf (pos j + 1)).choose_spec.2
  have hposlt : ∀ k, pos k + 1 ≤ pos (k + 1) := fun k => (hinf (pos k + 1)).choose_spec.1
  -- `k ↦ g (pos k)` is an infinite `lt`-descending chain.
  exact no_infinite_descending hwf (fun k => g (pos k))
    (fun k => hdrop (pos k) (hposP k) (pos (k + 1)) (hposlt k))

end PLTS
