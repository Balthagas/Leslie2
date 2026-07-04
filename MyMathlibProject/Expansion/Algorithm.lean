/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Construction.WeakClosure

/-!
# Unfolding a `sys^w`-scheduler: the reaching probability

This file formalises the algorithm (see `blueprint/src/content.tex`) that unfolds
the execution of a scheduler `ws` on `sys^w` into a concrete `sys`-execution. The
algorithm is deterministic in control flow but makes probabilistic draws, so each
reachable **configuration** is reached with a well-defined probability,
`reachProb`.

A configuration is the pair `(we, e)` of the algorithm's outer loop:
* `we : List (Label × State)` — the abstract `sys^w`-execution built so far
  (the transition list of `⟨sys.init, we⟩`), one entry per completed weak step;
* `e : AlterSeq State Label` — the concrete `sys`-execution built so far.

One outer iteration draws a weak transition `wt = (l, μ)` from `ws(we)`, takes the
witness scheduler `s` inducing `wt` (`s ← wt.choose`), runs it from `last(e)` to
produce a concrete segment `e'` (the `τ*·l·τ*` unfolding), and sets
`e ← e ⌢ e'`, `we ← we ++ [(l, last(e))]`.
-/

open Stream'

namespace PLTS

variable {State Label : Type} [Silent Label] {sys : System State Label}

/-! ### The witness scheduler `s` of a weak transition (`s ← wt.choose`) -/

open Classical in
/-- A `sys`-scheduler `σ` **realises** the `sys^w` weak transition `s ⤳[l] μ`: run
from the Dirac `pure s` it halts almost surely, the distribution of its halting
end-state is exactly `μ`, and every halting trajectory has external trace `[l]`
(when `l ≠ τ`) or `[]` (when `l = τ`). That is, `σ` unfolds the single weak step
into a concrete `τ*·l·τ*` (or `τ*`) `sys`-path. -/
def Realises (σ : Scheduler sys) (s : State) (l : Label) (μ : PMF State) : Prop :=
  (∑' e : {e : AlterSeq State Label // e.trans.Terminates}, σ.haltMass (PMF.pure s) e) = 1 ∧
  (∀ x, μ x = ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
      σ.haltMass (PMF.pure s) e * (if WeakScheduler.stateAfter e.1 (e.1.trans.length e.2) = x
        then 1 else 0)) ∧
  (∀ e : {e : AlterSeq State Label // e.trans.Terminates}, σ.haltMass (PMF.pure s) e ≠ 0 →
      sys.trace e.1 = if l = Silent.τ then Seq.nil else Seq.cons l Seq.nil)

/-- The **immediate-halt** `sys`-scheduler: it emits `⊥` (no transition) at every
history. Used as the canonical value of the witness field `s` at halt configurations
(`wt = none`), and as `schedOf`'s junk fallback. -/
noncomputable def Scheduler.halt (sys : System State Label) : Scheduler sys :=
  ⟨fun _ => PMF.pure none, fun _ _ _ _ _ _ _ hmem => by simp at hmem⟩

open Classical in
/-- The witness scheduler `s` **inducing** the weak transition `wt = (l, μ)` from
state `x` — the algorithm's `s ← wt.choose`. Some scheduler realising the
`sys^w`-step `x ⤳[l] μ` (one exists exactly when `sys^w.step x l μ` holds); the
immediate-halt scheduler `Scheduler.halt` as junk otherwise. -/
noncomputable def schedOf (sys : System State Label) (x : State) (l : Label) (μ : PMF State) :
    Scheduler sys :=
  if h : ∃ σ : Scheduler sys, Realises σ x l μ then h.choose
  else Scheduler.halt sys

/-! ### Configurations and the reaching probability -/

/-- A **configuration** of the unfolding algorithm: the full state of all its
variables at a point during execution (matching the pseudocode in
`blueprint/src/content.tex`). -/
structure Config (sys : System State Label) where
  /-- `we` — the abstract `sys^w`-execution built so far. -/
  we : AlterSeq State Label
  /-- `e` — the concrete `sys`-execution built so far. -/
  e  : AlterSeq State Label
  /-- `wt` — the current weak transition `ws(we)` of `sys^w` (`none` is `⊥`, the
  outer-loop halt signal). -/
  wt : Option (Label × PMF State)
  /-- `s` — the witness `sys`-scheduler inducing `wt` (`s ← wt.choose`): it unfolds
  the weak step `wt` into a concrete `τ*·l·τ*` `sys`-segment. -/
  s  : Scheduler sys
  /-- `e'` — the in-progress inner `sys`-execution (the current segment, started
  from `last(e)`). -/
  e' : AlterSeq State Label
  /-- `t` — the current inner transition `s(e')` of `sys` (`none` is `⊥`, the
  inner-loop halt signal). -/
  t  : Option (Label × PMF State)

open Classical in
/-- The final state of a (finite) execution `e` — its `endState`, or `e.init` as
junk when `e.trans` is infinite (which never happens for the algorithm's reachable
configurations). The algorithm's `last(e)`. -/
noncomputable def lastOf (e : AlterSeq State Label) : State :=
  if h : e.trans.Terminates then e.endState h else e.init

open Classical in
/-- **One probabilistic instruction** of the algorithm, as a transition weight
`c → c'` (a sub-probability kernel on configurations). The two probabilistic
instructions are `t ← s(e')` (inner) and `wt ← ws(we)` (outer):

* `c.t = some (l', μ')` — **inner instruction** `t ← s(e')`: sample `s' ∼ μ'`,
  extend `e' ← e'.lbl(t).out(t)` by `(l', s')`, and draw the next `t` from `s`.
  Weight `μ' s' * c.s.next e'_new c'.t`. (`we, e, wt, s` are unchanged.)
* `c.t = none` — **outer instruction** `wt ← ws(we)`: commit `e ← e ⌢ e'` and
  `we ← we ++ [(lbl wt, last e)]`, draw `wt' = c'.wt` from `ws(we)`, take its
  witness `s' = schedOf wt'`, reset `e' ← last(e)`, and draw the first `t` from
  `s'`. Weight `ws.next we_new c'.wt * c'.s.next e'_new c'.t`.
* `c.wt = none` — halted: no outgoing transition. -/
noncomputable def step (ws : Scheduler sys^w) (c c' : Config sys) : ENNReal :=
  match c.wt, c.t with
  | none, _ => 0
  | some _, some (l', μ') =>
      if c'.we = c.we ∧ c'.e = c.e ∧ c'.wt = c.wt ∧ c'.s = c.s ∧
         c'.e'.init = c.e'.init ∧
         c'.e'.trans = c.e'.trans.append (Seq.cons (l', lastOf c'.e') Seq.nil)
      then μ' (lastOf c'.e') * c.s.next c'.e' c'.t
      else 0
  | some (lw, _), none =>
      let eN : AlterSeq State Label := ⟨c.e.init, c.e.trans.append c.e'.trans⟩
      let weN : AlterSeq State Label :=
        ⟨c.we.init, c.we.trans.append (Seq.cons (lw, lastOf eN) Seq.nil)⟩
      if c'.e = eN ∧ c'.we = weN ∧ c'.e' = ⟨lastOf eN, Seq.nil⟩ ∧
         (∀ p, c'.wt = some p → c'.s = schedOf sys (lastOf eN) p.1 p.2) ∧
         (c'.wt = none → c'.s = Scheduler.halt sys)
      then ws.next weN c'.wt *
        (match c'.wt with
         | none => if c'.t = none then 1 else 0
         | some _ => c'.s.next c'.e' c'.t)
      else 0

open Classical in
/-- The configuration distribution after `n` probabilistic instructions. The base
case (`n = 0`) is the algorithm's start: draw the first `wt ← ws(sys.init)` and
(if `wt ≠ ⊥`) the first inner `t ← s(e')`, with `we = e = e' = ⟨sys.init, nil⟩`. -/
noncomputable def reachAfter (ws : Scheduler sys^w) : ℕ → Config sys → ENNReal
  | 0, c =>
      if c.we = ⟨sys.init, Seq.nil⟩ ∧ c.e = ⟨sys.init, Seq.nil⟩ ∧
         c.e' = ⟨sys.init, Seq.nil⟩ ∧
         (∀ p, c.wt = some p → c.s = schedOf sys sys.init p.1 p.2) ∧
         (c.wt = none → c.s = Scheduler.halt sys)
      then ws.next ⟨sys.init, Seq.nil⟩ c.wt *
        (match c.wt with
         | none => if c.t = none then 1 else 0
         | some _ => c.s.next c.e' c.t)
      else 0
  | n + 1, c => ∑' c₀ : Config sys, reachAfter ws n c₀ * step ws c₀ c

/-- **The reaching probability** of a configuration `c`: the total probability,
over every instruction count, of the algorithm's state being exactly `c`. -/
noncomputable def reachProb (ws : Scheduler sys^w) (c : Config sys) : ENNReal :=
  ∑' n, reachAfter ws n c

end PLTS
