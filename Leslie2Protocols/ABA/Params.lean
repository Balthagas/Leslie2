/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Systems.Trace

/-!
# Parameters of the ABA development

The protocol parameters shared by every system in the ABA case study:

* `ABA.Params` — the number of processes `n`, the corruption budget `f` (with
  `3 * f < n`), and the coin goodness `ε` (with `2 * ε ≤ 1`).
* `ABA.Params.coinPMF` — the outcome distribution of one weak-common-coin
  resolution: `some b` with probability `ε` for each bit `b` (all correct
  processes get `b`), and `none` (the adversary-controlled outcome `⊤`) with
  the remaining probability `1 - 2 * ε`.

Both `WCC.Spec`'s coin-resolution transition and `ABA.Spec`'s coin transition
are `coinPMF.map` into their respective state updates, so the simulation
couples the two flips outcome-to-outcome through the *same* PMF.
-/

namespace PLTS
namespace ABA

/-- The global parameters of the ABA development: `n` processes of which at
most `f` may be corrupted (`3 * f < n`), and an `ε`-good weak common coin
(`2 * ε ≤ 1`, so that the three coin outcomes have total mass one). -/
structure Params where
  /-- Number of processes. -/
  n : ℕ
  /-- Corruption budget. -/
  f : ℕ
  /-- Optimal-resilience bound `3f < n`. -/
  hf : 3 * f < n
  /-- Coin goodness. -/
  ε : ENNReal
  /-- The two good outcomes fit inside a probability: `2ε ≤ 1`. -/
  hε : 2 * ε ≤ 1

namespace Params

/-- Total mass of the three coin outcomes is one: `(1 - 2ε) + (ε + ε) = 1`. -/
private theorem coin_mass (P : Params) :
    (∑ o : Option Bool, o.elim (1 - 2 * P.ε) (fun _ => P.ε)) = 1 := by
  rw [Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some]
  rw [Fintype.sum_bool, ← two_mul]
  rw [tsub_add_cancel_of_le P.hε]

/-- The outcome distribution of one coin resolution: each bit with probability
`ε`, and the adversarial outcome `none` (`⊤` in the blueprint) otherwise. -/
noncomputable def coinPMF (P : Params) : PMF (Option Bool) :=
  PMF.ofFintype (fun o => o.elim (1 - 2 * P.ε) (fun _ => P.ε)) P.coin_mass

@[simp] theorem coinPMF_apply_some (P : Params) (b : Bool) :
    P.coinPMF (some b) = P.ε := by
  simp [coinPMF]

@[simp] theorem coinPMF_apply_none (P : Params) :
    P.coinPMF none = 1 - 2 * P.ε := by
  simp [coinPMF]

/-- `n` is positive (from `3f < n`). -/
theorem n_pos (P : Params) : 0 < P.n := lt_of_le_of_lt (Nat.zero_le _) P.hf

/-- The quorum size `n - f` exceeds `f`: any `n - f` processes contain a
correct one even after removing `f` corrupted ones. -/
theorem f_lt_n_sub_f (P : Params) : P.f < P.n - P.f := by
  have := P.hf; omega

end Params

end ABA
end PLTS
