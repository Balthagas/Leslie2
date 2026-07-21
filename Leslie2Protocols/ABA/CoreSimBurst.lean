/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2Protocols.ABA.CoreSimRel
import Leslie2.Weak.WeakTransition

/-!
# Abstract-twin burst machinery (M6-E1)

Pure `ABA.spec`-side weak-τ chain lemmas, with no hybrid/`Inv`/`Abs` reasoning: given an
abstract `SpecState`, these package the internal `SpecStep` rules (`Spec.lean`) into the
`weakTau`/`weakStep` chains (`WeakTransition.lean`) that the coupling tranche (next) will need
to drive the abstract twin through a τ-burst. Every lemma here is standalone and never mentions
`Inv`/`Abs`/the concrete `(g, c, w)` state.

* `fill_chain` (B1): fills an all-`none` `call` row to an arbitrary D3-legal target, one
  `adopt`/`repropose` step per process.
* `rebind_mixed` / `rebind_unanim` (B2): the single-step quorum rules (4/3) that clear a filled
  `call` row and rebind.
* `val_force` (B3): composes `fill_chain` with `rebind_unanim` to force `val`/`bind` to a chosen
  bit from any pre-existing `bind`.
* `coin_reset_flip`: exposes the `coinFlip` rule's exact resolution `PMF`.
* `weakStep_of_burst_then_step`: a `weakTau` burst followed by a genuine visible step is a
  `weakStep`.
-/

namespace PLTS
namespace ABA

variable {P : Params}

/-! ### B1: filling an empty `call` row -/

/-- `fillState a t l`: `a` with `call` set to `t` off the (finite) list `l` and to `none` on
`l` — the state reached after filling every process outside `l`. Only `call` varies; every
other field of `fillState a t l` is definitionally `a`'s. -/
private def fillState (a : SpecState P.n) (t : Fin P.n → Option Bool) (l : List (Fin P.n)) :
    SpecState P.n :=
  { a with call := fun id => if id ∈ l then none else t id }

private theorem fillState_call (a : SpecState P.n) (t : Fin P.n → Option Bool)
    (l : List (Fin P.n)) (id : Fin P.n) :
    (fillState a t l).call id = if id ∈ l then none else t id := rfl

/-- Filling every `some`-entry of a D3-legal target `t` from an all-`none` `call` row, one
`adopt`/`repropose` step per process (`fillState`-indexed induction on the remaining-ids list).
-/
theorem fill_chain {a : SpecState P.n} {vb : Bool} (hbind : a.bind = some vb)
    {t : Fin P.n → Option Bool}
    (hlegal : ∀ id b, t id = some b → a.val = none ∨ a.val = some b)
    (havail : TVal.agrees a.bind a.coin → ∀ id b, t id = some b → b = vb)
    (hempty : ∀ id, a.call id = none) :
    weakTau (spec P) (PMF.pure a) (PMF.pure { a with call := t }) := by
  suffices h : ∀ l : List (Fin P.n), l.Nodup → ∀ cur : Fin P.n → Option Bool,
      (∀ id, id ∈ l → cur id = none) → (∀ id, id ∉ l → cur id = t id) →
      weakTau (spec P) (PMF.pure { a with call := cur }) (PMF.pure { a with call := t }) by
    have hres := h (List.finRange P.n) (List.nodup_finRange P.n) a.call
      (fun id _ => hempty id) (fun id hid => absurd (List.mem_finRange id) hid)
    simpa using hres
  intro l
  induction l with
  | nil =>
    intro _ cur _ hout
    have hceq : cur = t := funext (fun id => hout id List.not_mem_nil)
    rw [hceq]; exact weakTau_refl _ _
  | cons id l' ih =>
    intro hnodup cur hin hout
    have hidnl' : id ∉ l' := (List.nodup_cons.mp hnodup).1
    have hnodup' : l'.Nodup := (List.nodup_cons.mp hnodup).2
    have hcurid : cur id = none := hin id List.mem_cons_self
    rcases hc : t id with _ | b
    · -- `t id = none`: nothing to fill at `id`, reindex to `l'`.
      refine ih hnodup' cur ?_ ?_
      · intro id' hid'; exact hin id' (List.mem_cons_of_mem id hid')
      · intro id' hid'
        by_cases heq : id' = id
        · rw [heq, hcurid, hc]
        · exact hout id' (by simp [List.mem_cons, heq, hid'])
    · -- `t id = some b`: a single `adopt`/`repropose` step, then the `l'`-indexed IH.
      have hcont : ∀ cur' : Fin P.n → Option Bool, cur' = Function.update cur id (some b) →
          weakTau (spec P) (PMF.pure { a with call := cur })
            (PMF.pure { a with call := t }) := by
        intro cur' hcur'eq
        have hchain : weakTau (spec P) (PMF.pure { a with call := cur' })
            (PMF.pure { a with call := t }) := by
          refine ih hnodup' cur' ?_ ?_
          · intro id' hid'
            rw [hcur'eq, Function.update_of_ne (ne_of_mem_of_not_mem hid' hidnl')]
            exact hin id' (List.mem_cons_of_mem id hid')
          · intro id' hid'
            by_cases heq : id' = id
            · rw [heq, hcur'eq, Function.update_self, hc]
            · rw [hcur'eq, Function.update_of_ne heq]
              exact hout id' (by simp [List.mem_cons, heq, hid'])
        refine weakTau_trans (weakTau_of_step rfl ?_) hchain
        rw [hcur'eq]
        by_cases hagree : TVal.agrees a.bind a.coin
        · have hbeq : b = vb := havail hagree id b hc
          have hstep := SpecStep.adopt (P := P) { a with call := cur } id hcurid hagree
          have hupdate : Function.update cur id a.bind = Function.update cur id (some b) := by
            rw [hbind, ← hbeq]
          rwa [hupdate] at hstep
        · exact SpecStep.repropose (P := P) { a with call := cur } id b hcurid hagree
            (hlegal id b hc)
      exact hcont _ rfl

/-! ### B2: quorum rebind rules -/

/-- Rule 4 (mixed): both bits present among honest calls, a quorum has spoken — a single τ step
clears `call` and rebinds to any chosen `b'` (`val`/`ret`/`F` untouched, `coin` reset to `⊥`). -/
theorem rebind_mixed {a : SpecState P.n} (hq : a.quorum P)
    (h1 : ∃ id, id ∉ a.F ∧ a.call id = some true) (h0 : ∃ id, id ∉ a.F ∧ a.call id = some false)
    (b' : Bool) :
    weakTau (spec P) (PMF.pure a)
      (PMF.pure { a with call := fun _ => none, bind := some b', coin := .bot }) :=
  weakTau_of_step rfl (SpecStep.mixed a b' hq h1 h0)

/-- Rule 3 (unanimity): every honest call avoids `b`, a quorum has spoken — a single τ step
clears `call` and decides `!b` (`ret`/`F` untouched, `coin` reset to `⊥`). -/
theorem rebind_unanim {a : SpecState P.n} {b : Bool} (hq : a.quorum P)
    (hb : ∀ id, id ∉ a.F → a.call id ≠ some b) :
    weakTau (spec P) (PMF.pure a)
      (PMF.pure { a with
        call := fun _ => none, bind := some (!b), val := some (!b), coin := .bot }) :=
  weakTau_of_step rfl (SpecStep.unanim a b hq hb)

/-- The full-`call` row always meets the quorum guard (every `id` is counted, corrupted or
not). -/
private theorem quorum_of_full_call {s : SpecState P.n} (hcall : ∀ id, s.call id ≠ none) :
    s.quorum P := by
  have heq : (Finset.univ.filter (fun id => id ∉ s.F ∧ s.call id ≠ none)) ∪ s.F
      = (Finset.univ : Finset (Fin P.n)) := by
    ext id
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : id ∈ s.F
    · simp [h]
    · simp [h, hcall id]
  unfold SpecState.quorum
  rw [heq, Finset.card_univ, Fintype.card_fin]
  omega

/-! ### B3: forcing `val` from a pre-existing `bind` -/

/-- From `bind = some b`, an empty `call` row, and `val` either unset or already `b`: fill every
process with `b` (`fill_chain`, D3-legal since `val ∈ {⊥, some b}`), then unanimously rebind
away from `!b` (every filled call is `b ≠ !b`) — landing on `val = bind = some b`, `coin` reset,
`call` cleared, `ret`/`F` untouched. -/
theorem val_force {a : SpecState P.n} {b : Bool} (hbind : a.bind = some b)
    (hcall : ∀ id, a.call id = none) (hval : a.val = none ∨ a.val = some b) :
    ∃ a' : SpecState P.n, weakTau (spec P) (PMF.pure a) (PMF.pure a') ∧
      a'.val = some b ∧ a'.bind = some b ∧ a'.call = (fun _ => none) ∧
      a'.ret = a.ret ∧ a'.F = a.F ∧ a'.coin = .bot := by
  set a1 : SpecState P.n := { a with call := fun _ => some b } with ha1def
  have hfill : weakTau (spec P) (PMF.pure a) (PMF.pure a1) := by
    refine fill_chain hbind (t := fun _ => some b) ?_ ?_ hcall
    · intro id b' hb'
      have hbb' : b = b' := Option.some_inj.mp hb'
      rw [← hbb']
      exact hval
    · intro _ id b' hb'; exact (Option.some_inj.mp hb').symm
  have ha1quorum : a1.quorum P := quorum_of_full_call (s := a1) (fun id => by simp [ha1def])
  have ha1avoid : ∀ id, id ∉ a1.F → a1.call id ≠ some (!b) := by
    intro id _
    simp only [ha1def]
    intro hcontra
    exact absurd (Option.some_inj.mp hcontra) (by cases b <;> simp)
  have hreb := rebind_unanim (a := a1) (b := !b) ha1quorum ha1avoid
  rw [Bool.not_not] at hreb
  exact ⟨_, weakTau_trans hfill hreb, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Coin resolution -/

/-- Rule 5 (coin flip): with `call` empty and `bind` already resolved, the coin-flip step is
available with exactly this resolution `PMF` (exposed unpackaged for the ε-coupling, which needs
to see the `PMF.map` shape, not just its existence). -/
theorem coin_reset_flip {a : SpecState P.n} (hcall : ∀ id, a.call id = none)
    (hbind : a.bind ≠ none) :
    SpecStep P a .tau (P.coinPMF.map (fun o => { a with coin := o.elim TVal.top TVal.bit })) :=
  SpecStep.coinFlip a hcall hbind

/-! ### Convenience: closing a burst with a visible step -/

/-- A `weakTau` burst followed by a genuine (possibly visible) single step is a `weakStep`: the
burst is the leading τ-closure, the step is the middle hyper-step (`hyperStep_pure_of_step`), and
the trailing τ-closure is the trivial reflexivity at the final state. -/
theorem weakStep_of_burst_then_step {a a' a'' : SpecState P.n} {l : Lab P.n}
    (hburst : weakTau (spec P) (PMF.pure a) (PMF.pure a'))
    (hstep : SpecStep P a' l (PMF.pure a'')) :
    weakStep (spec P) (PMF.pure a) l (PMF.pure a'') :=
  ⟨PMF.pure a', PMF.pure a'', hburst, hyperStep_pure_of_step hstep, weakTau_refl _ _⟩

end ABA
end PLTS
