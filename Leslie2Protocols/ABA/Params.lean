/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2.Systems.Trace

/-!
# Parameters of the ABA development

The protocol parameters shared by every system in the ABA case study:

* `ABA.Params` — the number of processes `n`, the corruption budget `f` (with
  `3 * f < n`), the coin goodness `ε` and the coin failure probability `δ`
  (with `2 * ε + δ ≤ 1`).
* `ABA.Params.coinPMF` — the outcome distribution used by `ABA.Spec`'s coin
  transition: `some b` with probability `ε` for each bit `b` (all correct
  processes get `b`), and `none` (the adversary-controlled outcome `⊤`) with
  the remaining probability `1 - 2 * ε`. Delivery always happens.
* `ABA.Params.wccPMF` — the outcome distribution used by `WCC.Spec`'s coin
  resolution, over `ABA.CoinOutcome`: `bit b` with probability `ε` for each
  bit `b`, `adv` (the adversary-controlled outcome `⊤`) with probability
  `1 - (2 * ε + δ)`, and `dead` — the coin fails and never delivers — with
  probability `δ`.

Both transitions are a `PMF.map` of their distribution into the respective
state update.
-/

namespace PLTS
namespace ABA

/-- The global parameters of the ABA development: `n` processes of which at
most `f` may be corrupted (`3 * f < n`), and an `ε`-good, `δ`-failing weak
common coin (`2 * ε + δ ≤ 1`, so that the four coin outcomes have total mass
one). -/
structure Params where
  /-- Number of processes. -/
  n : ℕ
  /-- Corruption budget. -/
  f : ℕ
  /-- Optimal-resilience bound `3f < n`. -/
  hf : 3 * f < n
  /-- Coin goodness. -/
  ε : ENNReal
  /-- Coin failure probability: the mass on which the coin never delivers. -/
  δ : ENNReal
  /-- The two good outcomes and the failure outcome fit inside a probability:
  `2ε + δ ≤ 1`. -/
  hδ : 2 * ε + δ ≤ 1

/-- The outcome of one weak-common-coin resolution: the common bit `b`, the
adversary-controlled outcome `⊤` (delivery happens, but the adversary picks
each process's returned bit), or delivery failure (the coin never delivers, so
no process ever returns). -/
inductive CoinOutcome : Type
  /-- The common bit `b`: every correct process receives `b`. -/
  | bit (b : Bool)
  /-- The adversary-controlled outcome `⊤`. -/
  | adv
  /-- Delivery failure: the resolution never delivers. -/
  | dead
  deriving DecidableEq, Repr

instance : Fintype CoinOutcome where
  elems := {.bit false, .bit true, .adv, .dead}
  complete := by
    intro o
    cases o with
    | bit b => cases b <;> decide
    | adv => decide
    | dead => decide

namespace Params

/-- The two good outcomes alone fit inside a probability: `2ε ≤ 1`. -/
theorem hε (P : Params) : 2 * P.ε ≤ 1 := le_trans le_self_add P.hδ

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

/-- The mass function of `wccPMF`: `ε` on each bit, `1 - (2ε + δ)` on the
adversarial outcome, `δ` on delivery failure. -/
noncomputable def wccMass (P : Params) : CoinOutcome → ENNReal
  | .bit _ => P.ε
  | .adv => 1 - (2 * P.ε + P.δ)
  | .dead => P.δ

/-- Total mass of the four coin outcomes is one:
`(ε + ε) + (1 - (2ε + δ)) + δ = 1`. -/
private theorem wcc_mass (P : Params) : (∑ o : CoinOutcome, P.wccMass o) = 1 := by
  rw [show (Finset.univ : Finset CoinOutcome)
      = {.bit false, .bit true, .adv, .dead} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have key : ∀ x : ENNReal, P.ε + (P.ε + (x + P.δ)) = 2 * P.ε + P.δ + x := by
    intro x; rw [two_mul]; ring
  rw [wccMass, wccMass, wccMass, wccMass, key, add_tsub_cancel_of_le P.hδ]

/-- The outcome distribution of one weak-common-coin resolution: each bit with
probability `ε`, delivery failure with probability `δ`, and the adversarial
outcome `adv` (`⊤` in the blueprint) with the remaining mass. -/
noncomputable def wccPMF (P : Params) : PMF CoinOutcome :=
  PMF.ofFintype P.wccMass P.wcc_mass

@[simp] theorem wccPMF_apply_bit (P : Params) (b : Bool) :
    P.wccPMF (.bit b) = P.ε := by
  simp [wccPMF, wccMass]

@[simp] theorem wccPMF_apply_adv (P : Params) :
    P.wccPMF .adv = 1 - (2 * P.ε + P.δ) := by
  simp [wccPMF, wccMass]

@[simp] theorem wccPMF_apply_dead (P : Params) :
    P.wccPMF .dead = P.δ := by
  simp [wccPMF, wccMass]

/-- `n` is positive (from `3f < n`). -/
theorem n_pos (P : Params) : 0 < P.n := lt_of_le_of_lt (Nat.zero_le _) P.hf

/-- The quorum size `n - f` exceeds `f`: any `n - f` processes contain a
correct one even after removing `f` corrupted ones. -/
theorem f_lt_n_sub_f (P : Params) : P.f < P.n - P.f := by
  have := P.hf; omega

end Params

end ABA
end PLTS
