/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Spec
import Leslie2Protocols.Framework.IdleFamily

/-!
# The GBCA specification instance (blueprint Transition System 2)

The round-`r` instance of the Graded Binding Crusader Agreement specification.
Binding is *linearised*: an internal τ-transition fixes the bound value once a
quorum has spoken with an honest witness, and every return label carries the
bound value (`retG r id out bound`), so Binding becomes a per-label property.

Grades: `A b` (decide `b`), `B b` (adopt `b`), `C` (no output; adopt the
coin). The `grade` field (`some true` ≈ grade `1`/A-side, `some false` ≈
grade `0`/C-side) enforces the A/C exclusivity of Graded Agreement: once an
`A`-return happened no `C`-return can, and vice versa. `B`- and `C`-returns
additionally require an honest dissenting input (`call id' = 1 − bind`).

Every transition is Dirac, so the instance is an LTS and the `ForwardLTS`
bridge applies. `fail` is the determinised D1 `corrupt`; the family
(`GBCA.specFamily`) broadcasts it to all rounds.
-/

namespace PLTS
namespace ABA
namespace GBCA

/-- The state of one GBCA specification instance. -/
structure SpecState (n : ℕ) where
  /-- Pending inputs: `call id = some b` when `id` has input `b`. -/
  call : Fin n → Option Bool
  /-- Which processes have received their return. -/
  ret : Fin n → Bool
  /-- The bound value (fixed by the internal binding transition). -/
  bind : Option Bool
  /-- The grade lock: `some true` after an `A`-return, `some false` after a
  `C`-return (`⊥` before either). -/
  grade : Option Bool
  /-- The corrupted set (local copy, kept in lockstep by `fail` broadcast). -/
  F : Finset (Fin n)
  deriving DecidableEq

namespace SpecState

variable {n : ℕ}

/-- The initial GBCA instance state. -/
def initial (n : ℕ) : SpecState n where
  call := fun _ => none
  ret := fun _ => false
  bind := none
  grade := none
  F := ∅

/-- The quorum guard `|{id ∉ F | call[id] ≠ ⊥} ∪ F| ≥ n − f`. -/
def quorum (P : Params) (s : SpecState P.n) : Prop :=
  P.n - P.f ≤ ((Finset.univ.filter (fun id => id ∉ s.F ∧ s.call id ≠ none)) ∪ s.F).card

/-- Corruption (deviation D1): total, Dirac, monotone in `F`. -/
def corrupt (P : Params) (id : Fin P.n) (s : SpecState P.n) : SpecState P.n :=
  if id ∉ s.F ∧ s.F.card < P.f then { s with F := insert id s.F } else s

end SpecState

/-- The step relation of the round-`r` GBCA specification instance
(blueprint Transition System 2). -/
inductive Step (P : Params) (r : ℕ) :
    SpecState P.n → Lab P.n → PMF (SpecState P.n) → Prop
  /-- A process inputs its bit. -/
  | call (s : SpecState P.n) (id : Fin P.n) (b : Bool) (h : s.call id = none) :
      Step P r s (.callG r id b)
        (PMF.pure { s with call := Function.update s.call id (some b) })
  /-- Input-enabledness loop for `call`. -/
  | callLoop (s : SpecState P.n) (id : Fin P.n) (b : Bool) :
      Step P r s (.callG r id b) (PMF.pure s)
  /-- Binding: a quorum has spoken and an honest process input `b`;
  fix the bound value. -/
  | bindSet (s : SpecState P.n) (b : Bool)
      (hq : s.quorum P) (hw : ∃ id, id ∉ s.F ∧ s.call id = some b)
      (hb : s.bind = none) :
      Step P r s .tau (PMF.pure { s with bind := some b })
  /-- `B`-return: adopt the bound value (an honest dissent exists). -/
  | retB (s : SpecState P.n) (id : Fin P.n) (v : Bool)
      (hb : s.bind = some v)
      (hw : ∃ id', id' ∉ s.F ∧ s.call id' = some (!v))
      (hr : s.ret id = false) :
      Step P r s (.retG r id (.B v) v)
        (PMF.pure { s with ret := Function.update s.ret id true })
  /-- `A`-return: decide the bound value (locks the grade to the A-side). -/
  | retA (s : SpecState P.n) (id : Fin P.n) (v : Bool)
      (hb : s.bind = some v)
      (hg : s.grade = none ∨ s.grade = some true)
      (hr : s.ret id = false) :
      Step P r s (.retG r id (.A v) v)
        (PMF.pure { s with grade := some true, ret := Function.update s.ret id true })
  /-- `C`-return: no output (locks the grade to the C-side; honest dissent
  exists). -/
  | retC (s : SpecState P.n) (id : Fin P.n) (v : Bool)
      (hb : s.bind = some v)
      (hw : ∃ id', id' ∉ s.F ∧ s.call id' = some (!v))
      (hg : s.grade = none ∨ s.grade = some false)
      (hr : s.ret id = false) :
      Step P r s (.retG r id .C v)
        (PMF.pure { s with grade := some false, ret := Function.update s.ret id true })
  /-- Corruption (deviation D1). -/
  | fail (s : SpecState P.n) (id : Fin P.n) :
      Step P r s (.fail id) (PMF.pure (s.corrupt P id))

/-- The round-`r` GBCA specification instance. -/
noncomputable def specInst (P : Params) (r : ℕ) : System (SpecState P.n) (Lab P.n) where
  init := SpecState.initial P.n
  step := Step P r

@[simp] theorem specInst_init (P : Params) (r : ℕ) :
    (specInst P r).init = SpecState.initial P.n := rfl

@[simp] theorem specInst_step (P : Params) (r : ℕ) (s : SpecState P.n)
    (l : Lab P.n) (μ : PMF (SpecState P.n)) :
    (specInst P r).step s l μ ↔ Step P r s l μ := Iff.rfl

/-- Every GBCA spec transition is Dirac: the instance is an LTS. -/
theorem specInst_isLTS (P : Params) (r : ℕ) : (specInst P r).IsLTS := by
  rintro s l μ hstep
  cases hstep <;> exact ⟨_, rfl⟩

/-- The broadcast transform of the GBCA family: corruption on `fail id`,
identity on every other label. -/
def failAct (P : Params) : Lab P.n → SpecState P.n → SpecState P.n
  | .fail id, s => s.corrupt P id
  | _, s => s

/-- The ℕ-indexed family of GBCA specification instances. -/
noncomputable def specFamily (P : Params) :
    System (ℕ → SpecState P.n) (Lab P.n) :=
  System.family (specInst P) Lab.gbcaRound Lab.isFail (failAct P)

/-- The GBCA spec family is an LTS. -/
theorem specFamily_isLTS (P : Params) : (specFamily P).IsLTS :=
  System.family_isLTS (specInst_isLTS P) _ _ _

end GBCA
end ABA
end PLTS
