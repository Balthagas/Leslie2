/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Labels
import Leslie2Protocols.Framework.IdleFamily

/-!
# The GBCA specification instance (blueprint Transition System 2)

The round-`r` instance of the Graded Binding Crusader Agreement specification.

Binding is *negative* information. The state field `dead : Finset Bool` is the
set of bits the instance can no longer hand out; it starts empty. The internal
τ-transition `bindUnset b` kills one bit — `dead := insert b dead` — once a
quorum has spoken and `f + 1` F-blind supporters back the *surviving* bit `!b`.
No rule removes a bit and `bindUnset` requires `dead = ∅`, so `dead` is written
at most once per instance — the kill commits the round — and is monotone along
every execution; `corrupt` leaves it alone. The once-only guard is what makes
every fair round completable: a second kill after an `A`-return would strand
the processes yet to return, the value-bearing returns needing a live bit and
`retC` being blocked by the A-latch. Every property below is a consequence of
that monotonicity plus the membership guards on the return rules, with no
auxiliary invariant.

Grades: `A b` (decide `b`), `B b` (adopt `b`), `C` (no output; adopt the coin).
The `grade` field (`some true` ≈ grade `1`/A-side, `some false` ≈ grade
`0`/C-side) enforces the A/C exclusivity of Graded Agreement: once an
`A`-return happened no `C`-return can, and vice versa.

## Graded agreement is the guard pair

Both value-bearing returns carry the guard pair `v ∉ dead ∧ (!v) ∈ dead`: the
bit handed out is alive, and the other bit is already dead. That pair *is*
graded agreement, with no supporting argument. A return of `v` pins `!v` into
`dead`; monotonicity carries `!v ∈ dead` to every later state of the run; a
later return of `w` needs `w ∉ dead`, so `w ≠ !v`, so `w = v`. Two returns in
one execution therefore name the same bit whatever their grades, and a single
bit — the unique survivor once any value-bearing return has fired — is the only
bit any extension can ever hand out.

## `retC` and Graded Binding

The `C`-return's guard `1 ≤ dead.card` is ABDY22's Graded Binding clause read
on this state: *there is a bit `b` such that no non-faulty party decides `1 − b`
at grade `≥ 1` in any extension*. A member of `dead` is exactly such a `1 − b`
— the witness `b` is its complement, the surviving bit — because the
value-bearing returns refuse a dead bit, and `dead` only grows, so the witness
is valid in every extension of the run and not merely at the moment of the
return. A `C`-return thus commits the instance: from that point on at most
one bit is alive anywhere in the future, which is what makes handing out no bit
the right answer. `retC` additionally requires `f + 1` F-blind support for each
bit (D15), which is what certifies that neither bit was forced.

## The all-⊥ run

In a round where neither bit is decidable the specification still commits
internally to a single killed bit, and the run ends with `C`-returns alone.
That commitment is sound because the `C`-return's label carries no bit: the
instance never announces which bit it killed, so no process is answered with
the internal choice. `retC`'s guard `1 ≤ dead.card` is the binding witness
either way — a bit that no extension can hand out — whether the round goes on
to hand out its complement or hands out nothing at all.

## Provenance (D14/D15)

* **D14 (repair, load-bearing).** The source blueprint's TS 2 certifies binding
  by a *single* honest witness (`∃ id ∉ F, call id = b`), and `B`/`C` dissent
  likewise by a single honest dissenter. That singular witness is the same
  provenance loss the D13 repair removes from Transition System 1, one level
  down: the witness may
  be corrupted later in the trace, after which nothing attributes the outcome to
  a never-corrupted input — and `hybrid` built on this TS 2 provably violates
  the papers' Validity (deterministic witness at `n = 4, f = 1`, inputs
  `1,0,0,0`: bind at `1` off the sole `1`-holder, `retB`-adopt everywhere,
  round-1 unanimity decides `1`, `fail 0`, `retABA 1 1` — never-corrupted
  processes all input `0`). ABDY22's implementation carries the `f + 1` via
  Valid-set relay thresholds; TS 2 abstracted it to one witness.
* **D15 (the repair).** Every certificate is a count
  `f + 1 ≤ #{id | call id = some b ∨ id ∈ F}` at the relevant bit — exactly
  TS 1's `SuppOK` shape (D13), directly `F`-blind: the count is monotone in `F`
  and in `call`, so it is immune to later `fail`s. On the exclusion set the
  counts sit at three places. `bindUnset b` counts support for the bit it
  *spares*, `!b`; the `retB` dissent guard counts support for the bit it does
  *not* hand out, `!v`; `retC` counts support for both bits. Provenance survives
  verbatim: `F` is monotone with `|F_final| ≤ f`, so among `f + 1` distinct
  supporters some member is outside the *final* `F`, hence outside the current
  `F`, hence a never-corrupted genuine caller — corrupt supporters are paid for
  by the `F` budget itself, with no phantom-call bookkeeping. Chaining the two:
  a bit `v` handed out at grade `≥ 1` requires `(!v) ∈ dead`, and the
  `bindUnset (!v)` that put it there certified `f + 1` F-blind supporters of
  `!(!v) = v`; the budget pigeonhole then recovers a never-corrupted genuine
  caller of `v` behind every value-bearing return.

* **D19 (the state shape).** The source blueprint's TS 2 carries a bound value
  `bind ∈ {0, 1, ⊥}`. The exclusion set is the killed-bit reading of that
  value: `dead ∈ {∅, {b}}`, embedding `bind = ⊥ ↦ dead = ∅` and
  `bind = b ↦ dead = {!b}`. The two states therefore differ in the guards, not
  in the cardinality. The blueprint's `bind = some v` guard on the
  value-bearing returns becomes the pair `v ∉ dead ∧ (!v) ∈ dead`, its
  `bind = none` guard on binding becomes `dead = ∅`, and the `C`-return's
  binding obligation `bind ≠ ⊥` — which in the source also puts the bound
  value on the label — becomes `1 ≤ dead.card`, read off a label that names no
  bit.

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
  /-- The exclusion set: the bits the instance can no longer hand out.
  Monotone, written at most once, by `bindUnset`. -/
  dead : Finset Bool
  /-- The grade lock: `some true` after an `A`-return, `some false` after a
  `C`-return (`⊥` before either). -/
  grade : Option Bool
  /-- The corrupted set (local copy, kept in lockstep by `fail` broadcast). -/
  F : Finset (Fin n)
  deriving DecidableEq

namespace SpecState

variable {n : ℕ}

/-- The initial GBCA instance state: no bit is dead yet. -/
def initial (n : ℕ) : SpecState n where
  call := fun _ => none
  ret := fun _ => false
  dead := ∅
  grade := none
  F := ∅

/-- The quorum guard `|{id ∉ F | call[id] ≠ ⊥} ∪ F| ≥ n − f`. -/
def quorum (P : Params) (s : SpecState P.n) : Prop :=
  P.n - P.f ≤ ((Finset.univ.filter (fun id => id ∉ s.F ∧ s.call id ≠ none)) ∪ s.F).card

/-- Corruption (deviation D1): total, Dirac, monotone in `F`, and blind to
`dead`. -/
def corrupt (P : Params) (id : Fin P.n) (s : SpecState P.n) : SpecState P.n :=
  if id ∉ s.F ∧ s.F.card < P.f then { s with F := insert id s.F } else s

end SpecState

/-! ### Corruption frame lemmas

`SpecState.corrupt` writes `F` and nothing else, so every other projection
passes through it untouched. These four `@[simp]` lemmas are the canonical
statements of that fact; the refinement, safety and core-simulation files all
read them from here rather than reproving them locally. -/

@[simp] theorem corrupt_call (P : Params) (s : SpecState P.n) (id : Fin P.n) :
    (s.corrupt P id).call = s.call := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_ret (P : Params) (s : SpecState P.n) (id : Fin P.n) :
    (s.corrupt P id).ret = s.ret := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_dead (P : Params) (s : SpecState P.n) (id : Fin P.n) :
    (s.corrupt P id).dead = s.dead := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_grade (P : Params) (s : SpecState P.n) (id : Fin P.n) :
    (s.corrupt P id).grade = s.grade := by
  unfold SpecState.corrupt; split <;> rfl

/-- The step relation of the round-`r` GBCA specification instance
(blueprint Transition System 2, deviation D19). -/
inductive Step (P : Params) (r : ℕ) :
    SpecState P.n → Lab P.n → PMF (SpecState P.n) → Prop
  /-- A process inputs its bit. -/
  | call (s : SpecState P.n) (id : Fin P.n) (b : Bool) (h : s.call id = none) :
      Step P r s (.callG r id b)
        (PMF.pure { s with call := Function.update s.call id (some b) })
  /-- Input-enabledness loop for `call`. -/
  | callLoop (s : SpecState P.n) (id : Fin P.n) (b : Bool) :
      Step P r s (.callG r id b) (PMF.pure s)
  /-- Binding: a quorum has spoken and `f + 1` processes support the surviving
  bit `!b` (D15, SuppOK form: caller or `F`-member); kill `b`. Fires at most
  once per instance — the guard is `dead = ∅` — and `dead` never shrinks. -/
  | bindUnset (s : SpecState P.n) (b : Bool)
      (hq : s.quorum P)
      (hw : P.f + 1 ≤ (Finset.univ.filter
        (fun id => s.call id = some (!b) ∨ id ∈ s.F)).card)
      (hd0 : s.dead = ∅) :
      Step P r s .tau (PMF.pure { s with dead := insert b s.dead })
  /-- `B`-return: adopt the surviving bit `v` (`f + 1` dissenting supporters,
  D15). The guard pair `v ∉ dead`, `(!v) ∈ dead` is graded agreement. -/
  | retB (s : SpecState P.n) (id : Fin P.n) (v : Bool)
      (hlive : v ∉ s.dead) (hdead : (!v) ∈ s.dead)
      (hw : P.f + 1 ≤ (Finset.univ.filter
        (fun id' => s.call id' = some (!v) ∨ id' ∈ s.F)).card)
      (hr : s.ret id = false) :
      Step P r s (.retG r id (.B v))
        (PMF.pure { s with ret := Function.update s.ret id true })
  /-- `A`-return: decide the surviving bit `v` (locks the grade to the A-side).
  Same guard pair as `retB`. -/
  | retA (s : SpecState P.n) (id : Fin P.n) (v : Bool)
      (hlive : v ∉ s.dead) (hdead : (!v) ∈ s.dead)
      (hg : s.grade = none ∨ s.grade = some true)
      (hr : s.ret id = false) :
      Step P r s (.retG r id (.A v))
        (PMF.pure { s with grade := some true, ret := Function.update s.ret id true })
  /-- `C`-return: no output. Some bit is already dead — the Graded Binding
  witness, valid in every extension because `dead` only grows — and both bits
  carry `f + 1` F-blind support (D15), which is what makes handing out no bit
  the right answer; the grade is locked to the C-side. -/
  | retC (s : SpecState P.n) (id : Fin P.n)
      (hd : 1 ≤ s.dead.card)
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
