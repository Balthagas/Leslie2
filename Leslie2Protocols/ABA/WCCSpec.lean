/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Spec
import Leslie2Protocols.Framework.IdleFamily

/-!
# The WCC specification instance (blueprint Transition System 3)

The round-`r` instance of the Weak Common Coin specification. The coin
resolution is the only probabilistic transition of the whole development
besides `ABA.Spec`'s: once more than `f` processes (counting corrupted ones)
have called, `val` resolves by `wccPMF` — each bit with probability `ε` (all
correct processes receive that bit), the failure outcome with probability `δ`,
and `⊤` with the remaining mass (the adversary controls per-process return
values).

Deviations: the `guess` label is omitted (D4 — it exists solely for the
out-of-scope Unpredictability property), and `fail` is the determinised
`corrupt` (D1).

* **D17 (δ-mass failure outcome).** The coin implementation the source builds
  on is an `ε`-correct verifiable secret sharing scheme, whose delivery
  guarantee holds only up to a failure probability `δ`; the specification
  inherits that failure as an outcome of its own. `wccPMF` therefore carries a
  fourth outcome `dead` of mass `δ`, pushed into `val := TVal.dead`. A `dead`
  round enables no `ret`: the return rule's guard is positive
  (`val = ⊤ ∨ val = bit b`), so a failed resolution silently delivers nothing
  and the round's callers wait forever. This is distinct from `⊤`, where
  delivery does happen and the adversary merely picks each process's returned
  bit.

The instance only steps on its own round-`r` API labels, `fail`, and `τ`; the
family combinator (`System.family`) supplies idle self-loops on every other
label.
-/

namespace PLTS
namespace ABA

/-- The `TVal` recorded by a coin resolution with the given outcome: the common
bit, `⊤` for the adversarial outcome, and `dead` for delivery failure. -/
def CoinOutcome.toTVal : CoinOutcome → TVal
  | .bit b => .bit b
  | .adv => .top
  | .dead => .dead

/-- `toTVal` is injective: the four coin outcomes land on four distinct
`TVal`s. -/
theorem CoinOutcome.toTVal_injective : Function.Injective CoinOutcome.toTVal := by
  intro a b h; cases a <;> cases b <;> simp_all [CoinOutcome.toTVal]

namespace WCC

/-- The state of one WCC specification instance. -/
structure SpecState (n : ℕ) where
  /-- Which processes have called this instance. -/
  called : Fin n → Bool
  /-- Which processes have received their return. -/
  ret : Fin n → Bool
  /-- The coin outcome (`⊥` until resolved). -/
  val : TVal
  /-- The corrupted set (local copy, kept in lockstep by `fail` broadcast). -/
  F : Finset (Fin n)
  deriving DecidableEq

namespace SpecState

variable {n : ℕ}

/-- The initial WCC instance state. -/
def initial (n : ℕ) : SpecState n where
  called := fun _ => false
  ret := fun _ => false
  val := .bot
  F := ∅

/-- The resolution threshold `|{id ∉ F | called id} ∪ F| > f`. -/
def threshold (P : Params) (s : SpecState P.n) : Prop :=
  P.f < ((Finset.univ.filter (fun id => id ∉ s.F ∧ s.called id)) ∪ s.F).card

/-- Corruption (deviation D1): total, Dirac, monotone in `F`. -/
def corrupt (P : Params) (id : Fin P.n) (s : SpecState P.n) : SpecState P.n :=
  if id ∉ s.F ∧ s.F.card < P.f then { s with F := insert id s.F } else s

end SpecState

/-- The step relation of the round-`r` WCC specification instance. -/
inductive Step (P : Params) (r : ℕ) :
    SpecState P.n → Lab P.n → PMF (SpecState P.n) → Prop
  /-- A process calls the coin. -/
  | call (s : SpecState P.n) (id : Fin P.n) (h : s.called id = false) :
      Step P r s (.callW r id)
        (PMF.pure { s with called := Function.update s.called id true })
  /-- Input-enabledness loop for `call`. -/
  | callLoop (s : SpecState P.n) (id : Fin P.n) :
      Step P r s (.callW r id) (PMF.pure s)
  /-- Coin resolution: the only probabilistic transition. Outcome `dead`
  (mass `δ`, deviation D17) resolves the coin without delivering. -/
  | flip (s : SpecState P.n) (hq : s.threshold P) (hv : s.val = .bot) :
      Step P r s .tau
        (P.wccPMF.map (fun o => { s with val := o.toTVal }))
  /-- A process receives its return: the common bit if `val = bit b`, an
  adversary-chosen bit if `val = ⊤`. The guard is positive, so a `dead`
  resolution (D17) enables no return at all. -/
  | ret (s : SpecState P.n) (id : Fin P.n) (b : Bool)
      (h₁ : s.val = .top ∨ s.val = .bit b) (h₂ : s.ret id = false) :
      Step P r s (.retW r id b)
        (PMF.pure { s with ret := Function.update s.ret id true })
  /-- Corruption (deviation D1). -/
  | fail (s : SpecState P.n) (id : Fin P.n) :
      Step P r s (.fail id) (PMF.pure (s.corrupt P id))

/-- The round-`r` WCC specification instance. -/
noncomputable def specInst (P : Params) (r : ℕ) : System (SpecState P.n) (Lab P.n) where
  init := SpecState.initial P.n
  step := Step P r

@[simp] theorem specInst_init (P : Params) (r : ℕ) :
    (specInst P r).init = SpecState.initial P.n := rfl

@[simp] theorem specInst_step (P : Params) (r : ℕ) (s : SpecState P.n)
    (l : Lab P.n) (μ : PMF (SpecState P.n)) :
    (specInst P r).step s l μ ↔ Step P r s l μ := Iff.rfl

/-- The broadcast transform of the WCC family: corruption on `fail id`,
identity on every other label. -/
def failAct (P : Params) : Lab P.n → SpecState P.n → SpecState P.n
  | .fail id, s => s.corrupt P id
  | _, s => s

/-- The ℕ-indexed family of WCC specification instances: one instance per
round, `fail` broadcast to all of them, idle on foreign labels. -/
noncomputable def specFamily (P : Params) :
    System (ℕ → SpecState P.n) (Lab P.n) :=
  System.family (specInst P) Lab.wccRound Lab.isFail (failAct P)

end WCC
end ABA
end PLTS
