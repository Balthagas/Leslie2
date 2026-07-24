/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.CoreSimRel
import Leslie2.Weak.WeakTransition

/-!
# Abstract-twin burst machinery

Pure `ABA.spec`-side weak-τ chain lemmas, with no hybrid/`Inv`/`Abs` reasoning: given an
abstract `SpecState`, these package the internal `SpecStep` rules (`Spec.lean`) into the
`weakTau`/`weakStep` chains (`WeakTransition.lean`) that the simulation rows (`CoreSim.lean`) consume
to drive the abstract twin through a τ-burst. Every lemma here is standalone and never mentions
`Inv`/`Abs`/the concrete `(g, c, w)` state.

* `fill_chain` (B1): fills an all-`none` `call` row to an arbitrary D3-legal target, one
  `adopt`/`repropose` step per process.
* `rebind_mixed` / `rebind_unanim` (B2): the single-step quorum rules (4/3) that clear a filled
  `call` row and rebind.
* `weakStep_of_burst_then_step`: a `weakTau` burst followed by a genuine visible step is a
  `weakStep`.
-/

namespace PLTS
namespace ABA

variable {P : Params}

/-! ### B1: filling an empty `call` row -/

/-- Filling every `some`-entry of a D3-legal target `t` from an all-`none` `call` row, one
`adopt`/`repropose` step per process (induction on the remaining-ids list).
-/
theorem fill_chain {a : SpecState P.n} {vb : Bool} (hbind : a.bind = some vb)
    {t : Fin P.n → Option Bool}
    (hlegal : ∀ id b, t id = some b →
      ((a.val = none ∧ (a.input id = some b ∨ a.bind = some b)) ∨ a.val = some b) ∨
        id ∈ a.F)
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
        rcases hlegal id b hc with hlic | hidF
        · by_cases hagree : TVal.agrees a.bind a.coin
          · have hbeq : b = vb := havail hagree id b hc
            have hstep := SpecStep.adopt (P := P) { a with call := cur } id hcurid hagree
            have hupdate : Function.update cur id a.bind = Function.update cur id (some b) := by
              rw [hbind, ← hbeq]
            rwa [hupdate] at hstep
          · exact SpecStep.repropose (P := P) { a with call := cur } id b hcurid hagree hlic
        · exact SpecStep.callByzFill (P := P) { a with call := cur } id b hidF hcurid
      exact hcont _ rfl

/-- Byzantine fill chain (D13): a τ-chain of `callByzFill`s reaching any target
that agrees with the current `call` row except on empty `F`-slots. Unlike `fill_chain`
it needs no `bind`/`coin` side conditions (`callByzFill` is unguarded beyond `id ∈ F`
and slot emptiness), so it also serves *pre-bind* bursts. -/
theorem byz_fill_chain {a : SpecState P.n} {t : Fin P.n → Option Bool}
    (ht : ∀ id, t id = a.call id ∨ (a.call id = none ∧ id ∈ a.F)) :
    weakTau (spec P) (PMF.pure a) (PMF.pure { a with call := t }) := by
  suffices h : ∀ l : List (Fin P.n), l.Nodup → ∀ cur : Fin P.n → Option Bool,
      (∀ id, id ∈ l → cur id = a.call id) → (∀ id, id ∉ l → cur id = t id) →
      weakTau (spec P) (PMF.pure { a with call := cur }) (PMF.pure { a with call := t }) by
    have hres := h (List.finRange P.n) (List.nodup_finRange P.n) a.call
      (fun _ _ => rfl) (fun id hid => absurd (List.mem_finRange id) hid)
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
    have hcurid : cur id = a.call id := hin id List.mem_cons_self
    by_cases hskip : t id = a.call id
    · -- nothing to fill at `id`: reindex to `l'`
      refine ih hnodup' cur ?_ ?_
      · intro id' hid'; exact hin id' (List.mem_cons_of_mem id hid')
      · intro id' hid'
        by_cases heq : id' = id
        · rw [heq, hcurid, hskip]
        · exact hout id' (by simp [List.mem_cons, heq, hid'])
    · rcases ht id with heq | ⟨hnone, hidF⟩
      · exact absurd heq hskip
      rcases hc : t id with _ | b
      · exact absurd (hc.trans hnone.symm) hskip
      have hchain : weakTau (spec P) (PMF.pure { a with call := Function.update cur id (some b) })
          (PMF.pure { a with call := t }) := by
        refine ih hnodup' _ ?_ ?_
        · intro id' hid'
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hid' hidnl')]
          exact hin id' (List.mem_cons_of_mem id hid')
        · intro id' hid'
          by_cases heq : id' = id
          · rw [heq, Function.update_self, hc]
          · rw [Function.update_of_ne heq]
            exact hout id' (by simp [List.mem_cons, heq, hid'])
      refine weakTau_trans (weakTau_of_step rfl ?_) hchain
      exact SpecStep.callByzFill (P := P) { a with call := cur } id b hidF
        (hcurid.trans hnone)

/-! ### B2: quorum rebind rules -/

/-- Rule 4 (mixed, D13): both bits present among honest calls, a quorum has spoken, and the
chosen `b'` carries `f + 1` callers (`hs`, F-blind) — a single τ step clears `call` and rebinds
to `b'` (`val`/`ret`/`F` untouched, `coin` reset to `⊥`). -/
theorem rebind_mixed {a : SpecState P.n} (hq : a.quorum P)
    (h1 : ∃ id, id ∉ a.F ∧ a.call id = some true) (h0 : ∃ id, id ∉ a.F ∧ a.call id = some false)
    (b' : Bool)
    (hs : P.f + 1 ≤ (Finset.univ.filter (fun id => a.call id = some b')).card) :
    weakTau (spec P) (PMF.pure a)
      (PMF.pure { a with call := fun _ => none, bind := some b', coin := .bot }) :=
  weakTau_of_step rfl (SpecStep.mixed a b' hq h1 h0 hs)

/-- Rule 3 (unanimity): every honest call avoids `b`, a quorum has spoken — a single τ step
clears `call` and decides `!b` (`ret`/`F` untouched, `coin` reset to `⊥`). -/
theorem rebind_unanim {a : SpecState P.n} {b : Bool} (hq : a.quorum P)
    (hb : ∀ id, id ∉ a.F → a.call id ≠ some b) :
    weakTau (spec P) (PMF.pure a)
      (PMF.pure { a with
        call := fun _ => none, bind := some (!b), val := some (!b), coin := .bot }) :=
  weakTau_of_step rfl (SpecStep.unanim a b hq hb)

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
