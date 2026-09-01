/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Labels

/-!
# The ABA specification (blueprint Transition System 1)

This module is the account of record for what the ABA development specifies.

The state is the record `SpecState`: a ghost record `input` of genuine
`callABA` events (D13), the flags `ret` of the processes that have returned,
the corrupted set `F`, the decision value `val`, and a control mode
`mode ∈ {idle, locked, dead}` (D21). Six rules act on it. `SpecStep.callSet`
and `SpecStep.callLoop` carry the interface call, `SpecStep.coinFlip` is the
mode loop, `SpecStep.decide` writes the decision value, `SpecStep.ret` carries
the interface return, and `SpecStep.fail` is corruption (D1). Every transition
is Dirac except `SpecStep.coinFlip`.

The mode loop is the specification's liveness reading. From `Mode.idle` a
flip locks with probability `ε`, kills with probability `δ`, and releases back
to `Mode.idle` with the remaining mass. At `Mode.locked` the decision is the
only `τ`-rule the mode can enable, so a lock is never discarded; `Mode.dead`
enables no `τ`-rule at all (D17). The flip names no coin bit. Reading `lock` as the coin
agreeing with a round's reference value is an outcome coupling of a
refinement, not a component of this system.

Provenance rests on the ghost record and the support guard `SuppOK` (D13).
`SpecStep.decide` is the sole writer of `val`. Its guards are `val = ⊥`,
`SuppOK b` and `mode ≠ dead`, and the support guard is the entire constraint
on the value decided. The rule is therefore enabled whenever some bit carries
`f + 1` recorded-or-corrupt supporters and the mode is not `Mode.dead`; no
count of participating processes is read anywhere in the system.
`SpecStep.callSet` overwrites the ghost record while nothing is decided, so
the record holds the bit of the last such call (D16); `SpecStep.callLoop` is
the input-enabledness loop and records first-write-wins.
-/

namespace PLTS
namespace ABA

/-- The control mode of the specification: waiting to flip, holding a lock, or
frozen by a failed flip. -/
inductive Mode : Type
  /-- The flip is enabled and no lock is held. -/
  | idle
  /-- A lock is held: the decision is the only enabled `τ`-rule. -/
  | locked
  /-- The flip failed to deliver (D17): no `τ`-rule is enabled. -/
  | dead
  deriving DecidableEq, Repr

/-- The state of the ABA specification (Transition System 1). -/
structure SpecState (n : ℕ) where
  /-- Ghost input record (D13): `input id = some b` when a genuine
  `callABA id b` event was recorded for `id`. -/
  input : Fin n → Option Bool
  /-- Which processes have returned. -/
  ret : Fin n → Bool
  /-- The corrupted set. -/
  F : Finset (Fin n)
  /-- The decision value: once `some v`, every return carries `v`. -/
  val : Option Bool
  /-- The control mode. -/
  mode : Mode
  deriving DecidableEq

namespace SpecState

variable {n : ℕ}

/-- The initial spec state: nothing recorded, nobody returned, nobody
corrupted, nothing decided, and the flip enabled. -/
def initial (n : ℕ) : SpecState n where
  input := fun _ => none
  ret := fun _ => false
  F := ∅
  val := none
  mode := .idle

/-- Corruption of `id` (deviation D1): total, Dirac, monotone in `F`. -/
def corrupt (P : Params) (id : Fin P.n) (s : SpecState P.n) : SpecState P.n :=
  if id ∉ s.F ∧ s.F.card < P.f then { s with F := insert id s.F } else s

end SpecState

/-- D13 support for `v`: `f + 1` ids, each either ghost-recorded as inputting
`v` or corrupted. The count is `F`-blind (D15), hence immune to later
corruptions. -/
def SuppOK (P : Params) (s : SpecState P.n) (v : Bool) : Prop :=
  P.f + 1 ≤ (Finset.univ.filter (fun id => s.input id = some v ∨ id ∈ s.F)).card

theorem SuppOK.mono {P : Params} {s s' : SpecState P.n} {v : Bool}
    (h : SuppOK P s v) (hin : ∀ id, s.input id = some v → s'.input id = some v)
    (hF : s.F ⊆ s'.F) : SuppOK P s' v := by
  refine le_trans h (Finset.card_le_card ?_)
  intro id hid
  rw [Finset.mem_filter] at hid ⊢
  exact ⟨hid.1, hid.2.imp (hin id) (fun hm => hF hm)⟩

/-- The outcome of one flip: it locks, releases, or kills. No coin bit is
named. -/
inductive FlipOutcome : Type
  /-- The flip locks: the mode becomes `Mode.locked`. -/
  | lock
  /-- The flip releases: the mode stays `Mode.idle`. -/
  | release
  /-- The flip kills: the mode becomes `Mode.dead` (D17). -/
  | kill
  deriving DecidableEq, Repr

/-- The flip distribution: mass `ε` on `lock`, `1 − ε − δ` on `release` and
`δ` on `kill`. It is the image of the development's single coin distribution
`Params.wccPMF` under a map that forgets the bit, one bit going to `lock` and
the other, together with the adversarial outcome, to `release`. The three
masses are all the rules read; no rule names a coin bit. -/
noncomputable def flipPMF (P : Params) : PMF FlipOutcome :=
  P.wccPMF.map (fun o => match o with
    | .bit true => .lock
    | .bit false => .release
    | .adv => .release
    | .dead => .kill)

/-- The step relation of the ABA specification. -/
inductive SpecStep (P : Params) :
    SpecState P.n → Lab P.n → PMF (SpecState P.n) → Prop
  /-- Rule 1: an environment call records its bit in the ghost record. The
  write is an overwrite (D13, D16): while nothing is decided the record is
  revisable, so it holds the bit of the last such call. -/
  | callSet (s : SpecState P.n) (id : Fin P.n) (b : Bool) (hv : s.val = none) :
      SpecStep P s (.callABA id b)
        (PMF.pure { s with input := Function.update s.input id (some b) })
  /-- Rule 2: the input-enabledness loop for `callABA`. The label is enabled in
  every state; the ghost record takes the bit first-write-wins (D13). -/
  | callLoop (s : SpecState P.n) (id : Fin P.n) (b : Bool) :
      SpecStep P s (.callABA id b)
        (PMF.pure { s with input := if s.input id = none
                             then Function.update s.input id (some b)
                             else s.input })
  /-- Rule 3 (the flip): the only non-Dirac rule of the system. From
  `Mode.idle`, with nothing decided, one flip resolves by `flipPMF` into
  `Mode.locked` with probability `ε`, back into `Mode.idle` with probability
  `1 − ε − δ`, and into `Mode.dead` with probability `δ` (D17). It is
  one-shot: the three outcomes are the three modes, and the rule names no coin
  bit. -/
  | coinFlip (s : SpecState P.n) (hm : s.mode = .idle) (hv : s.val = none) :
      SpecStep P s .tau
        ((flipPMF P).map (fun o => match o with
          | .lock => { s with mode := .locked }
          | .release => s
          | .kill => { s with mode := .dead }))
  /-- Rule 4 (decide): the sole writer of `val`. Its guards are `val = ⊥`
  (`hv`), `SuppOK b` (`hs`) and `mode ≠ dead` (`hm`), and the support guard is
  the entire constraint on the decided value: the bit `b` carries `f + 1`
  recorded-or-corrupt supporters (D13). A killed flip disables the rule (D17);
  at `Mode.locked` it is the only enabled `τ`-rule, and it is enabled there
  whenever some bit carries `f + 1` support. The mode returns to `Mode.idle`. -/
  | decide (s : SpecState P.n) (b : Bool) (hv : s.val = none) (hs : SuppOK P s b)
      (hm : s.mode ≠ .dead) :
      SpecStep P s .tau
        (PMF.pure { s with val := some b, mode := .idle })
  /-- Rule 5 (return): a process returns the decision value. -/
  | ret (s : SpecState P.n) (id : Fin P.n) (b : Bool)
      (h₁ : s.val = some b) (h₂ : s.ret id = false) :
      SpecStep P s (.retABA id b)
        (PMF.pure { s with ret := Function.update s.ret id true })
  /-- Rule 6 (corruption, deviation D1): total and Dirac. -/
  | fail (s : SpecState P.n) (id : Fin P.n) :
      SpecStep P s (.fail id) (PMF.pure (s.corrupt P id))

/-- **Counterexample check (D13).** The Validity-violating trace dies at
`SpecStep.decide (b := true)`: with the inputs `1,0,0,0` recorded at
`n = 4, f = 1` and the sole `1`-inputter corrupted, the supporters of `1` are
that one process alone, so the guard `hs`, demanding `f + 1 = 2` of them,
fails. -/
example :
    let input : Fin 4 → Option Bool := fun i => if i = 0 then some true else some false
    let F : Finset (Fin 4) := {0}
    ¬ (1 + 1 ≤ (Finset.univ.filter (fun id => input id = some true ∨ id ∈ F)).card) := by
  decide

/-- The ABA specification system (blueprint Transition System 1). -/
noncomputable def spec (P : Params) : System (SpecState P.n) (Lab P.n) where
  init := SpecState.initial P.n
  step := SpecStep P

@[simp] theorem spec_init (P : Params) : (spec P).init = SpecState.initial P.n := rfl

@[simp] theorem spec_step (P : Params) (s : SpecState P.n) (l : Lab P.n)
    (μ : PMF (SpecState P.n)) : (spec P).step s l μ ↔ SpecStep P s l μ := Iff.rfl

end ABA
end PLTS
