/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Systems.System
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Trajectory coordinates for the Ionescu–Tulcea measure

To turn a `ProbabilisticExecution` into a genuine probability measure we present
its runs as points of an infinite product `Π n, TrajCoord State Label n`, so that
Mathlib's Ionescu–Tulcea construction (`ProbabilityTheory.Kernel.trajMeasure`)
applies. Coordinate `0` holds the initial state; each later coordinate holds one
transition `(l, s')`, or `none` meaning "already halted".

`State` and `Label` are assumed `Countable`, so every coordinate is a *discrete*
measurable space (`⊤`); this makes every measurability side-condition vanish and
keeps the whole development elementary.

This file only sets up the coordinate family and the dictionary between I–T's
dependent history tuples `(i : Iic n) → TrajCoord State Label i` and the existing
`AlterSeq` histories: `coord`/`tup` (execution → tuple) and
`initCoord`/`stepCoord`/`recon`/`halted` (tuple → execution). The measure itself
is built in `Measure/Trajectory.lean`.
-/

open MeasureTheory ProbabilityTheory Finset Stream'

namespace PLTS

variable {State Label : Type}

/-- Trajectory coordinate family: position `0` is the initial state, each later
position `k+1` is one transition `(l, s')` or `none` (halted). -/
def TrajCoord (State Label : Type) : ℕ → Type
  | 0 => State
  | _ + 1 => Option (Label × State)

instance (n : ℕ) : MeasurableSpace (TrajCoord State Label n) := ⊤

instance (n : ℕ) : MeasurableSingletonClass (TrajCoord State Label n) := ⟨fun _ => trivial⟩

instance (n : ℕ) [Countable State] [Countable Label] :
    Countable (TrajCoord State Label n) := by
  cases n with
  | zero => change Countable State; infer_instance
  | succ k => change Countable (Option (Label × State)); infer_instance

/-! ### Execution → history tuple -/

/-- The coordinate values of a finite execution `e`. -/
def coord (e : AlterSeq State Label) : (n : ℕ) → TrajCoord State Label n
  | 0 => e.init
  | k + 1 => e.trans.get? k

/-- The history tuple over `Iic n` realising execution `e` (`n` = number of
transitions read). -/
def tup (e : AlterSeq State Label) (n : ℕ) : (i : Finset.Iic n) → TrajCoord State Label i :=
  fun i => coord e i

/-! ### History tuple → execution -/

/-- The initial state read off a history tuple. -/
def initCoord {n : ℕ} (x : (i : Finset.Iic n) → TrajCoord State Label i) : State :=
  x ⟨0, mem_Iic.mpr (Nat.zero_le n)⟩

/-- The transition (or `none`) at position `k+1` of a history tuple; `none` past
the end. -/
def stepCoord {n : ℕ} (x : (i : Finset.Iic n) → TrajCoord State Label i) (k : ℕ) :
    Option (Label × State) :=
  if h : k + 1 ≤ n then x ⟨k + 1, mem_Iic.mpr h⟩ else none

/-- The transition list of the live prefix of a history tuple (stop at the first
`none`). -/
def reconTransList {n : ℕ} (x : (i : Finset.Iic n) → TrajCoord State Label i) :
    List (Label × State) :=
  (((List.range n).map (stepCoord x)).takeWhile Option.isSome).filterMap id

/-- The `AlterSeq` reconstructed from a history tuple: initial state plus the live
`some`-prefix of transitions. -/
def recon {n : ℕ} (x : (i : Finset.Iic n) → TrajCoord State Label i) : AlterSeq State Label :=
  ⟨initCoord x, Seq.ofList (reconTransList x)⟩

/-- A history tuple is *halted* if some live position already holds `none`. -/
def halted {n : ℕ} (x : (i : Finset.Iic n) → TrajCoord State Label i) : Prop :=
  ∃ k, k < n ∧ stepCoord x k = none

/-! ### Dictionary lemmas -/

@[simp] theorem initCoord_tup (e : AlterSeq State Label) (n : ℕ) :
    initCoord (tup e n) = e.init := rfl

theorem stepCoord_tup (e : AlterSeq State Label) (n k : ℕ) (h : k + 1 ≤ n) :
    stepCoord (tup e n) k = e.trans.get? k := by
  rw [stepCoord, dif_pos h]; rfl

/-- **A3.** Reconstructing the tuple of an execution recovers the execution. -/
theorem recon_tup (e : AlterSeq State Label) (hFin : e.trans.Terminates) :
    recon (tup e (e.trans.length hFin)) = e := by
  have hLlen : (e.trans.toList hFin).length = e.trans.length hFin := Seq.length_toList _ _
  -- The mapped-coordinate list is exactly `toList` wrapped in `some`.
  have key : (List.range (e.trans.length hFin)).map (stepCoord (tup e (e.trans.length hFin)))
      = (e.trans.toList hFin).map some := by
    apply List.ext_getElem
    · simp [hLlen]
    · intro k h₁ _
      have hk : k < e.trans.length hFin := by simpa using h₁
      rw [List.getElem_map, List.getElem_range, List.getElem_map,
        stepCoord_tup e _ k (by omega), ← Seq.getElem?_toList e.trans hFin k,
        List.getElem?_eq_getElem (by rw [hLlen]; exact hk)]
  have hlist : reconTransList (tup e (e.trans.length hFin)) = e.trans.toList hFin := by
    rw [reconTransList, key]
    generalize e.trans.toList hFin = l
    induction l with
    | nil => rfl
    | cons a l ih => simpa using ih
  change (⟨initCoord (tup e (e.trans.length hFin)),
      Seq.ofList (reconTransList (tup e (e.trans.length hFin)))⟩ : AlterSeq State Label) = e
  rw [initCoord_tup, hlist, Seq.ofList_toList]

/-- **A4.** The tuple of an execution is never halted. -/
theorem not_halted_tup (e : AlterSeq State Label) (hFin : e.trans.Terminates) :
    ¬ halted (tup e (e.trans.length hFin)) := by
  rintro ⟨k, hk, hnone⟩
  rw [stepCoord_tup e _ k (by omega)] at hnone
  have : e.trans.length hFin ≤ k := Seq.length_le_iff.mpr hnone
  omega

end PLTS
