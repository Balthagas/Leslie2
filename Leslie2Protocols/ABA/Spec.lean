/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Labels

/-!
# The ABA specification (blueprint Transition System 1, repaired)

The PLTS encoding of Asynchronous Byzantine Agreement, transcribed from the
blueprint's Transition System 1 with four deviations:

* **D13 (repair, load-bearing).** The blueprint's TS 1 fails the papers'
  Validity (see `ABA/AUDIT.md` §2.1): rule 7's free re-propose while
  `val = ⊥` and rule 4's free mixed bind lose input provenance, so a bit
  input only by a process corrupted *later in the same trace* can win
  (achievable at `n = 4, f = 1` with inputs `1,0,0,0`: bind `1`, `fail` the
  sole `1`-holder, re-propose `1` everywhere, decide `1`). The repair
  principle: a value may circulate only with `f + 1` distinct supporters —
  at most `f` processes are *ever* corrupted, so `f + 1` supporters always
  include a never-corrupted one, and provenance survives dynamic corruption
  with no future-peeking guard (`3f < n` supplies `n − 2f ≥ f + 1`). The
  deltas: a ghost map `input` records genuine `callABA` events (rule 1
  unconditionally, rule 2 first-write-wins); rule 4 requires `f + 1` callers
  of the bound bit (`hs`); rule 7 re-proposes only a recorded own input, the
  bound value, or the decision value (coin values are deliberately *not*
  licensed — they would resurrect the audit trace through a probability-`ε`
  flip); the new τ-rule `callByzFill` lets a corrupted process fill an empty
  call slot with **no** ghost record — the Byzantine phantom-call channel of
  the concrete adversary's hidden byz `callG` drivers. All support counts
  are `F`-blind (immune to later `fail`s); corrupt callers are paid for by
  the `id ∈ F` disjunct of the provenance invariant (`SpecSafety.SpecInv`),
  i.e. by the `F` budget, not the ghost.
* **D3 (repair, load-bearing).** The blueprint's re-propose transition
  (`call[id] = ⊥ ∧ bind ≠ coin →τ→ call[id] = b`, `b` arbitrary) admits an
  Agreement-violating trace: after a unanimous-`v` round sets `val := v` and
  some process returns `v`, arbitrary re-proposal of `1−v` lets the unanimity
  rule overwrite `val := 1−v` and a second process return `1−v`. The real
  protocol excludes this via grades. We guard re-proposal with
  `val = ⊥ ∨ b = val` (once the decision value is fixed, honest re-inputs
  equal it) — see the annotation in the blueprint source.
* **D1 (determinised `fail`).** Corruption is the total function
  `corrupt id` (adds `id` to `F` when `id ∉ F ∧ |F| < f`, else identity),
  merging the blueprint's guarded transition and its input-enabledness loop.
  This keeps the `F`-copies of all composed components in lockstep.
* The blueprint's `Initial` clause mentions an undeclared `out`; omitted.

The coin domain `{0,1,⊥,⊤}` is `TVal`; `bind, val ∈ {0,1,⊥}` are
`Option Bool`. All transitions are Dirac except the coin flip, which is
`coinPMF.map` into the state update.
-/

namespace PLTS
namespace ABA

/-- A `⊤`-completed value: `⊥`, `⊤`, or a bit. The domain of the spec's `coin`
field (and of `WCC.Spec`'s `val` field). -/
inductive TVal : Type
  /-- Unresolved (`⊥`). -/
  | bot
  /-- Adversarial outcome (`⊤`): every process may receive either bit. -/
  | top
  /-- The common bit `b`. -/
  | bit (b : Bool)
  deriving DecidableEq, Repr

/-- `agrees o t`: the blueprint's cross-domain equality `bind = coin` between
`bind ∈ {0,1,⊥}` and `coin ∈ {0,1,⊥,⊤}` — `⊥ = ⊥` or `b = b`; `⊤` agrees with
nothing. -/
def TVal.agrees : Option Bool → TVal → Prop
  | none, .bot => True
  | some b, .bit b' => b = b'
  | _, _ => False

instance : ∀ o t, Decidable (TVal.agrees o t) := fun o t => by
  cases o <;> cases t <;> simp only [TVal.agrees] <;> infer_instance

/-- The state of the ABA specification (Transition System 1). -/
structure SpecState (n : ℕ) where
  /-- Pending round inputs: `call id = some b` when `id`'s current-round input
  is `b`, `none` when unset. -/
  call : Fin n → Option Bool
  /-- Which processes have returned. -/
  ret : Fin n → Bool
  /-- The bound value (write-target of the unanimity/mixed rules). -/
  bind : Option Bool
  /-- The decision value: once `some v`, every return carries `v`. -/
  val : Option Bool
  /-- The current coin outcome. -/
  coin : TVal
  /-- The corrupted set. -/
  F : Finset (Fin n)
  /-- Ghost input record (D13): `input id = some b` when a genuine
  `callABA id b` event was recorded for `id` (rules 1 and 2; never written
  by Byzantine fills). -/
  input : Fin n → Option Bool
  deriving DecidableEq

namespace SpecState

variable {n : ℕ}

/-- The initial spec state: everything unset, nobody corrupted. -/
def initial (n : ℕ) : SpecState n where
  call := fun _ => none
  ret := fun _ => false
  bind := none
  val := none
  coin := .bot
  F := ∅
  input := fun _ => none

/-- The blueprint's quorum guard `|{id ∉ F | call[id] ≠ ⊥} ∪ F| ≥ n − f`. -/
def quorum (P : Params) (s : SpecState P.n) : Prop :=
  P.n - P.f ≤ ((Finset.univ.filter (fun id => id ∉ s.F ∧ s.call id ≠ none)) ∪ s.F).card

instance (P : Params) (s : SpecState P.n) : Decidable (s.quorum P) := by
  unfold quorum; infer_instance

/-- Corruption of `id` (deviation D1): total, Dirac, monotone in `F`. -/
def corrupt (P : Params) (id : Fin P.n) (s : SpecState P.n) : SpecState P.n :=
  if id ∉ s.F ∧ s.F.card < P.f then { s with F := insert id s.F } else s

end SpecState

/-- The step relation of the ABA specification: one constructor per blueprint
rule (rule 7 carries the D3 repair guard; `fail` is the determinised D1 form). -/
inductive SpecStep (P : Params) :
    SpecState P.n → Lab P.n → PMF (SpecState P.n) → Prop
  /-- Rule 1: an environment call sets a pending input (only while `bind = ⊥`);
  the ghost `input` records it (D13). -/
  | callSet (s : SpecState P.n) (id : Fin P.n) (b : Bool)
      (h₁ : s.call id = none) (h₂ : s.bind = none) :
      SpecStep P s (.callABA id b)
        (PMF.pure { s with call := Function.update s.call id (some b),
                           input := Function.update s.input id (some b) })
  /-- Rule 2: input-enabledness loop for `call`; the ghost `input` records the
  event first-write-wins (D13): a genuine `callABA` event may bank an input
  even when the `call` slot is occupied or the round is bound. -/
  | callLoop (s : SpecState P.n) (id : Fin P.n) (b : Bool) :
      SpecStep P s (.callABA id b)
        (PMF.pure { s with input := if s.input id = none
                             then Function.update s.input id (some b)
                             else s.input })
  /-- Rule 3 (unanimity): a quorum has spoken and no honest input is `b`;
  bind and decide `!b`, reset the round. -/
  | unanim (s : SpecState P.n) (b : Bool)
      (hq : s.quorum P) (hb : ∀ id, id ∉ s.F → s.call id ≠ some b) :
      SpecStep P s .tau
        (PMF.pure { s with call := fun _ => none, bind := some (!b),
                           val := some (!b), coin := .bot })
  /-- Rule 4 (mixed, **with the D13 support guard**): a quorum has spoken with
  both bits present among honest inputs; bind a bit `b` carrying `f + 1`
  callers (`hs`, F-blind — corrupt callers count, paid for by the `F`
  budget), reset the round (`val` untouched). -/
  | mixed (s : SpecState P.n) (b : Bool)
      (hq : s.quorum P)
      (h1 : ∃ id, id ∉ s.F ∧ s.call id = some true)
      (h0 : ∃ id, id ∉ s.F ∧ s.call id = some false)
      (hs : P.f + 1 ≤ (Finset.univ.filter (fun id => s.call id = some b)).card) :
      SpecStep P s .tau
        (PMF.pure { s with call := fun _ => none, bind := some b, coin := .bot })
  /-- Rule 5 (coin flip): the round is reset and bound; resolve the coin. The
  only non-Dirac transition. -/
  | coinFlip (s : SpecState P.n)
      (hcall : ∀ id, s.call id = none) (hbind : s.bind ≠ none) :
      SpecStep P s .tau
        (P.coinPMF.map (fun o => { s with coin := o.elim TVal.top TVal.bit }))
  /-- Rule 6 (adopt): when `bind = coin`, a process adopts the bound value as
  its next-round input. -/
  | adopt (s : SpecState P.n) (id : Fin P.n)
      (h₁ : s.call id = none) (h₂ : TVal.agrees s.bind s.coin) :
      SpecStep P s .tau
        (PMF.pure { s with call := Function.update s.call id s.bind })
  /-- Rule 7 (re-propose, **with the D3 + D13 repair guards**): when
  `bind ≠ coin`, a process re-proposes a bit `b` — while `val = ⊥`, only a
  recorded own input or the bound value (D13: provenance); once the decision
  value is fixed, `b = val` (D3). -/
  | repropose (s : SpecState P.n) (id : Fin P.n) (b : Bool)
      (h₁ : s.call id = none) (h₂ : ¬ TVal.agrees s.bind s.coin)
      (h₃ : (s.val = none ∧ (s.input id = some b ∨ s.bind = some b)) ∨
        s.val = some b) :
      SpecStep P s .tau
        (PMF.pure { s with call := Function.update s.call id (some b) })
  /-- Byzantine phantom call (D13, τ): a corrupted process fills an empty
  call slot with an arbitrary bit, with **no** ghost record — the abstract
  counterpart of the concrete adversary's hidden byz `callG` drivers. -/
  | callByzFill (s : SpecState P.n) (id : Fin P.n) (b : Bool)
      (hF : id ∈ s.F) (h : s.call id = none) :
      SpecStep P s .tau
        (PMF.pure { s with call := Function.update s.call id (some b) })
  /-- Rule 8 (return): a process returns the decision value. -/
  | ret (s : SpecState P.n) (id : Fin P.n) (b : Bool)
      (h₁ : s.val = some b) (h₂ : s.ret id = false) :
      SpecStep P s (.retABA id b)
        (PMF.pure { s with ret := Function.update s.ret id true })
  /-- Rule 9 (corruption, deviation D1): total and Dirac. -/
  | fail (s : SpecState P.n) (id : Fin P.n) :
      SpecStep P s (.fail id) (PMF.pure (s.corrupt P id))

/-- **Audit-trace check (D13).** The AUDIT §2.1 trace dies exactly at
`mixed (b := 1)`: with inputs `1,0,0,0` (`n = 4`, `f = 1`) only id `0` calls
`1`, so the new support guard `hs` — demanding `f + 1 = 2` callers of `1` —
fails. (The rule-7 detour is also dead: only id `0` may re-propose `1`, and
a `val := 1` unanimity can never reach quorum from `|{0} ∪ F| ≤ 1 + f <
n − f`.) -/
example :
    let call : Fin 4 → Option Bool := fun i => if i = 0 then some true else some false
    ¬ (1 + 1 ≤ (Finset.univ.filter (fun id => call id = some true)).card) := by
  decide

/-- The ABA specification system (blueprint Transition System 1, repaired). -/
noncomputable def spec (P : Params) : System (SpecState P.n) (Lab P.n) where
  init := SpecState.initial P.n
  step := SpecStep P

@[simp] theorem spec_init (P : Params) : (spec P).init = SpecState.initial P.n := rfl

@[simp] theorem spec_step (P : Params) (s : SpecState P.n) (l : Lab P.n)
    (μ : PMF (SpecState P.n)) : (spec P).step s l μ ↔ SpecStep P s l μ := Iff.rfl

end ABA
end PLTS
