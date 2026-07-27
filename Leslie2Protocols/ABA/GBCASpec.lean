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
Binding is internal specification state: the τ-transition `bindSet` fixes the
`bind` field once a quorum has spoken and `f + 1` F-blind supporters back the
bit. The `A`- and `B`-returns hand out that bound value, and the bit they hand
out is the one their graded outcome names (`A v`, `B v`); the `C`-return hands
out no bit, so its label is the bare `C`.

Grades: `A b` (decide `b`), `B b` (adopt `b`), `C` (no output; adopt the
coin). The `grade` field (`some true` ≈ grade `1`/A-side, `some false` ≈
grade `0`/C-side) enforces the A/C exclusivity of Graded Agreement: once an
`A`-return happened no `C`-return can, and vice versa. A `B`-return
additionally requires `f + 1` callers supporting the dissenting bit
(`call id' = 1 − bind`); a `C`-return requires `f + 1` callers supporting
`true` and `f + 1` supporting `false`, which is what certifies that no single
bit can be handed out.

* **D14 (repair, load-bearing).** The blueprint's TS 2 certifies `bindSet`
  by a *single* honest witness (`∃ id ∉ F, call id = b`), and `B`/`C`
  dissent likewise by a single honest dissenter. That singular witness is
  the same provenance loss as the pre-D13 top-level spec, one level down: the witness
  may be corrupted later in the trace, after which nothing attributes the
  bound value to a never-corrupted input — and `hybridSpec` built on this
  TS 2 provably violates the papers' Validity (deterministic witness at
  `n = 4, f = 1`, inputs `1,0,0,0`: `bindSet 1` off the sole `1`-holder,
  `retB`-adopt everywhere, round-1 unanimity decides `1`, `fail 0`,
  `retABA 1 1` — never-corrupted processes all input `0`). ABDY22's
  implementation carries the `f + 1` via Valid-set relay thresholds; TS 2
  abstracted it to one witness. Repair (D15): `bindSet`'s witness, the
  `retB` dissent guard and each of the `retC` guards is a count
  `f + 1 ≤ #{id | call id = some b ∨ id ∈ F}` at the relevant bit — exactly
  TS 1's `SuppOK` shape (D13), directly `F`-blind: the count is monotone
  in `F` and in `call`, so it is immune to later `fail`s. Provenance
  survives verbatim: `F` is monotone with `|F_final| ≤ f`, so among `f + 1`
  distinct supporters some member is outside the *final* `F`, hence outside
  the current `F`, hence a never-corrupted genuine caller — corrupt
  supporters are paid for by the `F` budget itself, with no phantom-call
  bookkeeping.

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
  /-- Binding: a quorum has spoken and `f + 1` processes support `b`
  (D15, SuppOK form: caller or `F`-member); fix the bound value. -/
  | bindSet (s : SpecState P.n) (b : Bool)
      (hq : s.quorum P)
      (hw : P.f + 1 ≤ (Finset.univ.filter
        (fun id => s.call id = some b ∨ id ∈ s.F)).card)
      (hb : s.bind = none) :
      Step P r s .tau (PMF.pure { s with bind := some b })
  /-- `B`-return: adopt the bound value (`f + 1` dissenting supporters,
  D15). -/
  | retB (s : SpecState P.n) (id : Fin P.n) (v : Bool)
      (hb : s.bind = some v)
      (hw : P.f + 1 ≤ (Finset.univ.filter
        (fun id' => s.call id' = some (!v) ∨ id' ∈ s.F)).card)
      (hr : s.ret id = false) :
      Step P r s (.retG r id (.B v))
        (PMF.pure { s with ret := Function.update s.ret id true })
  /-- `A`-return: decide the bound value (locks the grade to the A-side). -/
  | retA (s : SpecState P.n) (id : Fin P.n) (v : Bool)
      (hb : s.bind = some v)
      (hg : s.grade = none ∨ s.grade = some true)
      (hr : s.ret id = false) :
      Step P r s (.retG r id (.A v))
        (PMF.pure { s with grade := some true, ret := Function.update s.ret id true })
  /-- `C`-return: no output. Both bits carry `f + 1` F-blind support (D15),
  which is what makes handing out no bit the right answer; the grade is
  locked to the C-side. -/
  | retC (s : SpecState P.n) (id : Fin P.n)
      (hwT : P.f + 1 ≤ (Finset.univ.filter
        (fun id' => s.call id' = some true ∨ id' ∈ s.F)).card)
      (hwF : P.f + 1 ≤ (Finset.univ.filter
        (fun id' => s.call id' = some false ∨ id' ∈ s.F)).card)
      (hg : s.grade = none ∨ s.grade = some false)
      (hr : s.ret id = false) :
      Step P r s (.retG r id .C)
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
