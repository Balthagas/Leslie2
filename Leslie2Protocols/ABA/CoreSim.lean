/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.CoreSimAbs
import Leslie2Protocols.ABA.CoreSimBurst

/-!
# The core simulation `hybridSpec ⊑ ABA.spec`

Assembles the invariant/relation of the `CoreSimRel`/`CoreSimInv`/`CoreSimAbs` chain and
`CoreSimBurst`'s burst kit into the theorem
`coreSim`, the probabilistic forward simulation `hybridSpec P ⊑ spec P` along `coreRel P`.
-/

namespace PLTS
namespace ABA

variable {P : Params}

/-- The core simulation relation, `Dirac`-lifted: every concrete state relates to the point
mass on its (unique) abstract twin. -/
def coreRel (P : Params) : HState P → PMF (SpecState P.n) → Prop :=
  diracRel (coreR P)

/-- **Stutter-row packaging.** If every post-state `s'` in the support of a concrete τ-step's
outcome `μ_C` relates to the *same* abstract state `a` (via `coreR`), the abstract twin can
answer with the trivial `weakTau_refl` stutter: the coupling `Ω := μ_C.map (fun s' => (s', pure
a))` has first marginal `μ_C` and second marginal the constant `pure (pure a)` (`PMF.map_const`),
so `ω := pure (pure a)` and `ω.bind id = pure a` (`PMF.pure_bind`). Reused by every hidden
handshake / internal row and by the unanimous `bindUnset` / stale coin-flip cases. -/
private theorem stutter_step {P : Params} (μ_C : PMF (HState P)) (a : SpecState P.n)
    (hA : ∀ s' ∈ μ_C.support, coreR P s' a) :
    ∃ ω : PMF (PMF (SpecState P.n)),
      PMFRel (coreRel P) μ_C ω ∧ weakTau (spec P) (PMF.pure a) (ω.bind id) := by
  set Ω : PMF (HState P × PMF (SpecState P.n)) := μ_C.map (fun s' => (s', PMF.pure a)) with hΩdef
  have hFst : Ω.map Prod.fst = μ_C := by
    rw [hΩdef, PMF.map_comp]
    have hcomp : (Prod.fst ∘ fun s' => (s', PMF.pure a)) = (id : HState P → HState P) := rfl
    rw [hcomp, PMF.map_id]
  have hSnd : Ω.map Prod.snd = PMF.pure (PMF.pure a) := by
    rw [hΩdef, PMF.map_comp]
    have hcomp : (Prod.snd ∘ fun s' => (s', PMF.pure a)) =
        (Function.const (HState P) (PMF.pure a)) := rfl
    rw [hcomp, PMF.map_const]
  refine ⟨PMF.pure (PMF.pure a), ⟨Ω, hFst, hSnd, ?_⟩, ?_⟩
  · intro p hp
    rw [hΩdef, PMF.mem_support_map_iff] at hp
    obtain ⟨s', hs', hp'⟩ := hp
    rw [← hp']
    exact ⟨a, rfl, hA s' hs'⟩
  · rw [PMF.pure_bind]
    exact weakTau_refl _ _

/-- Abstract-side corruption (deviation D1) only ever touches `F`. -/
theorem SpecState.corrupt_ret {P : Params} (id : Fin P.n) (s : SpecState P.n) :
    (s.corrupt P id).ret = s.ret := by unfold SpecState.corrupt; split <;> rfl

theorem SpecState.corrupt_call {P : Params} (id : Fin P.n) (s : SpecState P.n) :
    (s.corrupt P id).call = s.call := by unfold SpecState.corrupt; split <;> rfl

theorem SpecState.corrupt_bind {P : Params} (id : Fin P.n) (s : SpecState P.n) :
    (s.corrupt P id).bind = s.bind := by unfold SpecState.corrupt; split <;> rfl

theorem SpecState.corrupt_val {P : Params} (id : Fin P.n) (s : SpecState P.n) :
    (s.corrupt P id).val = s.val := by unfold SpecState.corrupt; split <;> rfl

theorem SpecState.corrupt_coin {P : Params} (id : Fin P.n) (s : SpecState P.n) :
    (s.corrupt P id).coin = s.coin := by unfold SpecState.corrupt; split <;> rfl

/-- Corruption of `F` is monotone (`fail`'s guard only ever inserts). -/
theorem CoreState.corrupt_F_subset {P : Params} (c : CoreState P.n) (id : Fin P.n) :
    c.F ⊆ (c.corrupt P id).F := by
  unfold CoreState.corrupt; split_ifs with hcond
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

theorem SpecState.corrupt_input {P : Params} (id : Fin P.n) (s : SpecState P.n) :
    (s.corrupt P id).input = s.input := by unfold SpecState.corrupt; split <;> rfl

/-- A triple product of Dirac PMFs collapses to a single Dirac (used to normalise the concrete
outcome of every visible row, `prodPMF (pure g) (prodPMF (pure c) (pure w))`, into `dirac_step`'s
expected `PMF.pure` shape). -/
private theorem prodPMF_pure_pure_pure {α β γ : Type*} (x : α) (y : β) (z : γ) :
    prodPMF (PMF.pure x) (prodPMF (PMF.pure y) (PMF.pure z)) = PMF.pure (x, (y, z)) := by
  simp [prodPMF, PMF.pure_bind]

/-- The full-`call` row always meets the quorum guard (re-derived locally: `CoreSimBurst`'s copy
is `private`). -/
private theorem quorum_of_full_call' {P : Params} {s : SpecState P.n}
    (hcall : ∀ id, s.call id ≠ none) : s.quorum P := by
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

/-- Force `val`/`bind` to a chosen bit, decoupled from the pre-existing bind value: since the
abstract twin never fires rule 5 (`coin_bot`), `TVal.agrees` is always `False`, so the
bind-branch of rule 7's repaired `h₃` licenses an all-`b` fill only when `a.bind = some b` —
which is exactly how it is invoked (post-rebind-to-`b`). -/
private theorem val_force' {P : Params} {a : SpecState P.n} {b : Bool}
    (hbind : a.bind = some b) (hcall : ∀ id, a.call id = none) (hcoin : a.coin = .bot)
    (hval : a.val = none ∨ a.val = some b) :
    ∃ a' : SpecState P.n, weakTau (spec P) (PMF.pure a) (PMF.pure a') ∧
      a'.val = some b ∧ a'.bind = some b ∧ a'.call = (fun _ => none) ∧
      a'.ret = a.ret ∧ a'.F = a.F ∧ a'.coin = .bot := by
  set a1 : SpecState P.n := { a with call := fun _ => some b } with ha1def
  have hfill : weakTau (spec P) (PMF.pure a) (PMF.pure a1) := by
    refine fill_chain hbind (t := fun _ => some b) ?_ ?_ hcall (by simp [hcoin])
    · intro id b' hb'
      have hbeq : b = b' := Option.some_inj.mp hb'
      rw [← hbeq]
      rcases hval with h | h
      · exact Or.inl (Or.inl ⟨h, Or.inr hbind⟩)
      · exact Or.inl (Or.inr h)
    · intro hagree
      exfalso; rw [hbind, hcoin] at hagree
      cases b <;> simp [TVal.agrees] at hagree
  have ha1quorum : a1.quorum P := quorum_of_full_call' (s := a1) (fun id => by simp [ha1def])
  have ha1avoid : ∀ id, id ∉ a1.F → a1.call id ≠ some (!b) := by
    intro id _
    simp only [ha1def]
    intro hcontra
    exact absurd (Option.some_inj.mp hcontra) (by cases b <;> simp)
  have hreb := rebind_unanim (a := a1) (b := !b) ha1quorum ha1avoid
  rw [Bool.not_not] at hreb
  exact ⟨_, weakTau_trans hfill hreb, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The abstract quorum is monotone under call growth (fills never empty a slot). -/
private theorem quorum_mono' {P : Params} {s s' : SpecState P.n} (hF : s'.F = s.F)
    (hcall : ∀ id, s.call id ≠ none → s'.call id ≠ none) (h : s.quorum P) : s'.quorum P := by
  refine le_trans h (Finset.card_le_card ?_)
  intro x hx
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, hF] at hx ⊢
  rcases hx with ⟨hxF, hxc⟩ | hxF
  · exact Or.inl ⟨hxF, hcall x hxc⟩
  · exact Or.inr hxF

/-- One honest caller of each bit, given an honest `b`-caller and an honest `!b`-caller. -/
private theorem pair_of_dissent {P : Params} {s : SpecState P.n} {b : Bool}
    (h1 : ∃ i, i ∉ s.F ∧ s.call i = some b) (h0 : ∃ i, i ∉ s.F ∧ s.call i = some (!b)) :
    (∃ i, i ∉ s.F ∧ s.call i = some true) ∧ (∃ i, i ∉ s.F ∧ s.call i = some false) := by
  cases b
  · exact ⟨by simpa using h0, by simpa using h1⟩
  · exact ⟨by simpa using h1, by simpa using h0⟩

/-- **The phase-1 decide burst (D16).** From an unbound, undecided twin with `coin ⊥`,
a quorum on the standing calls, and `f + 1` call-and-ghost-or-`F` material for `b`, a
τ-chain reaches `bind = val = some b` with the board clear and `ret`/`F` untouched.
Route: if no honest call dissents from `b`, one rule-3 step decides outright; otherwise
byz-fill the empty `F`-slots with the majority bit `v'` (the quorum pigeonholes its
`n − f ≥ 2f + 1` callers-or-`F` onto the two bits), rule-4 rebind to `v'` — *clearing
the board*, which is what makes every `F`-slot fillable-with-`b` afterwards — then fill
the material with `b` (ghost/byz branches) and everything else with `v'` (bind branch),
rule-4 rebind to `b` (rule 3 directly if everything is material), and close with the
all-`b` fill + rule 3 (`val_force'`). -/
private theorem decide_burst {P : Params} {a : SpecState P.n} {b : Bool}
    (hval : a.val = none)
    (hq : a.quorum P) (hFcard : a.F.card ≤ P.f)
    (hmat : P.f + 1 ≤ (Finset.univ.filter
      (fun id => (a.call id = some b ∧ a.input id = some b) ∨ id ∈ a.F)).card) :
    ∃ a' : SpecState P.n, weakTau (spec P) (PMF.pure a) (PMF.pure a') ∧
      a'.val = some b ∧ a'.bind = some b ∧ a'.ret = a.ret ∧ a'.F = a.F ∧
      a'.call = (fun _ => none) ∧ a'.coin = .bot := by
  by_cases hdis : ∃ id, id ∉ a.F ∧ a.call id = some (!b)
  case neg =>
    have havoid : ∀ id, id ∉ a.F → a.call id ≠ some (!b) :=
      fun id hidF hc => hdis ⟨id, hidF, hc⟩
    have hreb := rebind_unanim (a := a) (b := !b) hq havoid
    rw [Bool.not_not] at hreb
    exact ⟨_, hreb, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨idd, hiddF, hiddc⟩ := hdis
  have hmatH : ∃ id, id ∉ a.F ∧ a.call id = some b ∧ a.input id = some b := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ.filter
        (fun id => (a.call id = some b ∧ a.input id = some b) ∨ id ∈ a.F)) ⊆ a.F := by
      intro id hid
      rw [Finset.mem_filter] at hid
      rcases hid.2 with ⟨h1, h2⟩ | h
      · by_contra hne; exact hcon id hne h1 h2
      · exact h
    have := Finset.card_le_card hsub
    omega
  obtain ⟨idb, hidbF, hidbc, hidbg⟩ := hmatH
  -- the majority bit `v'` off the quorum pigeonhole
  have hpick : ∃ v', P.f + 1 ≤ (Finset.univ.filter
      (fun id => a.call id = some v' ∨ (id ∈ a.F ∧ a.call id = none))).card := by
    set At := Finset.univ.filter
      (fun id => a.call id = some true ∨ (id ∈ a.F ∧ a.call id = none)) with hAt
    set Af := Finset.univ.filter
      (fun id => a.call id = some false ∨ (id ∈ a.F ∧ a.call id = none)) with hAf
    have hcover : (Finset.univ.filter (fun id => id ∉ a.F ∧ a.call id ≠ none)) ∪ a.F
        ⊆ At ∪ Af := by
      intro x hx
      simp only [hAt, hAf, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and] at hx ⊢
      rcases hx with ⟨hxF, hxc⟩ | hxF
      · rcases hcv : a.call x with _ | bx
        · exact absurd hcv hxc
        · cases bx
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl (Or.inl rfl)
      · rcases hcv : a.call x with _ | bx
        · exact Or.inl (Or.inr ⟨hxF, rfl⟩)
        · cases bx
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl (Or.inl rfl)
    have hsum : P.n - P.f ≤ At.card + Af.card :=
      le_trans hq (le_trans (Finset.card_le_card hcover) (Finset.card_union_le At Af))
    have hnf : 2 * P.f + 1 ≤ P.n - P.f := by have := P.hf; omega
    by_cases ht : P.f + 1 ≤ At.card
    · exact ⟨true, ht⟩
    · refine ⟨false, ?_⟩
      show P.f + 1 ≤ Af.card
      omega
  obtain ⟨v', hv'⟩ := hpick
  -- Stage 1: byz-fill the empty `F`-slots with `v'`, then rule-4 rebind to `v'`
  set t₁ : Fin P.n → Option Bool :=
    fun id => if a.call id = none ∧ id ∈ a.F then some v' else a.call id with ht₁
  have ht₁eval : ∀ id, t₁ id =
      if a.call id = none ∧ id ∈ a.F then some v' else a.call id := fun _ => rfl
  have hfill1 : weakTau (spec P) (PMF.pure a) (PMF.pure { a with call := t₁ }) :=
    byz_fill_chain (fun id => by
      rw [ht₁eval id]
      by_cases h : a.call id = none ∧ id ∈ a.F
      · rw [if_pos h]; exact Or.inr h
      · rw [if_neg h]; exact Or.inl rfl)
  have ht₁H : ∀ id, id ∉ a.F → t₁ id = a.call id := by
    intro id h; rw [ht₁eval id, if_neg (fun hc => h hc.2)]
  have hq1 : SpecState.quorum P { a with call := t₁ } := by
    refine quorum_mono' (s := a) (s' := { a with call := t₁ }) rfl (fun id hne => ?_) hq
    show t₁ id ≠ none
    rw [ht₁eval id]
    by_cases h : a.call id = none ∧ id ∈ a.F
    · rw [if_pos h]; simp
    · rw [if_neg h]; exact hne
  have hs1 : P.f + 1 ≤ (Finset.univ.filter
      (fun id => ({ a with call := t₁ } : SpecState P.n).call id = some v')).card := by
    refine le_trans hv' (Finset.card_le_card ?_)
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    show t₁ x = some v'
    rw [ht₁eval x]
    rcases hx with hc | ⟨hF, hc⟩
    · rw [if_neg (fun h => by rw [h.1] at hc; exact absurd hc (by simp))]; exact hc
    · rw [if_pos ⟨hc, hF⟩]
  have hpair1 := pair_of_dissent (s := { a with call := t₁ })
    ⟨idb, hidbF, by show t₁ idb = some b; rw [ht₁H idb hidbF]; exact hidbc⟩
    ⟨idd, hiddF, by show t₁ idd = some (!b); rw [ht₁H idd hiddF]; exact hiddc⟩
  have hreb1 := rebind_mixed (a := { a with call := t₁ }) hq1 hpair1.1 hpair1.2 v' hs1
  set a2 : SpecState P.n :=
    { a with call := fun _ => none, bind := some v', coin := .bot } with ha2
  have hchain1 : weakTau (spec P) (PMF.pure a) (PMF.pure a2) :=
    weakTau_trans hfill1 hreb1
  clear hfill1 hreb1 hq1 hs1 hpair1 hq
  -- Stage 2: from the cleared `v'`-bound board, reach `bind = some b` with `val` untouched
  have hstage2 : ∃ a3 : SpecState P.n,
      weakTau (spec P) (PMF.pure a2) (PMF.pure a3) ∧ a3.val = some b ∧ a3.bind = some b ∧
      a3.ret = a.ret ∧ a3.F = a.F ∧ a3.call = (fun _ => none) ∧ a3.coin = .bot := by
    by_cases hvb : v' = b
    · subst hvb
      obtain ⟨a4, hw4, h1, h2, h3, h4, h5, h6⟩ :=
        val_force' (a := a2) (b := v') rfl (fun _ => rfl) rfl (Or.inl hval)
      exact ⟨a4, hw4, h1, h2, h4, h5, h3, h6⟩
    · have hv'b : v' = !b := Bool.eq_not_iff.mpr hvb
      set t₂ : Fin P.n → Option Bool :=
        fun id => if a.input id = some b ∨ id ∈ a.F then some b else some v' with ht₂
      have ht₂eval : ∀ id, t₂ id =
          if a.input id = some b ∨ id ∈ a.F then some b else some v' := fun _ => rfl
      have hfill2 : weakTau (spec P) (PMF.pure a2) (PMF.pure { a2 with call := t₂ }) := by
        refine fill_chain (vb := v') rfl (t := t₂) ?_ ?_ (fun _ => rfl) (by simp [ha2])
        · intro id b' hb'
          rw [ht₂eval id] at hb'
          by_cases h : a.input id = some b ∨ id ∈ a.F
          · rw [if_pos h, Option.some_inj] at hb'
            subst hb'
            rcases h with hg | hF
            · exact Or.inl (Or.inl ⟨hval, Or.inl hg⟩)
            · exact Or.inr hF
          · rw [if_neg h, Option.some_inj] at hb'
            subst hb'
            exact Or.inl (Or.inl ⟨hval, Or.inr rfl⟩)
        · intro hagree
          exfalso
          have : TVal.agrees (some v') .bot := hagree
          simp [TVal.agrees] at this
      have hfull : ∀ id, t₂ id ≠ none := by
        intro id; rw [ht₂eval id]
        by_cases h : a.input id = some b ∨ id ∈ a.F
        · rw [if_pos h]; simp
        · rw [if_neg h]; simp
      have hq2 : SpecState.quorum P { a2 with call := t₂ } :=
        quorum_of_full_call' (fun id => hfull id)
      by_cases hall : ∀ id, a.input id = some b ∨ id ∈ a.F
      · -- everything is material: the filled board is all-`b`, rule 3 decides
        have havoid : ∀ id, id ∉ ({ a2 with call := t₂ } : SpecState P.n).F →
            ({ a2 with call := t₂ } : SpecState P.n).call id ≠ some (!b) := by
          intro id _
          show t₂ id ≠ some (!b)
          rw [ht₂eval id, if_pos (hall id)]
          simp only [Ne, Option.some_inj]
          intro h; exact absurd h.symm (by cases b <;> simp)
        have hreb := rebind_unanim (a := { a2 with call := t₂ }) (b := !b) hq2 havoid
        rw [Bool.not_not] at hreb
        exact ⟨_, weakTau_trans hfill2 hreb, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · push Not at hall
        obtain ⟨idn, hidng, hidnF⟩ := hall
        have hpair2 := pair_of_dissent (s := { a2 with call := t₂ }) (b := b)
          ⟨idb, hidbF, by show t₂ idb = some b; rw [ht₂eval idb, if_pos (Or.inl hidbg)]⟩
          ⟨idn, hidnF, by
            show t₂ idn = some (!b)
            rw [ht₂eval idn, if_neg (by rintro (h | h); exacts [hidng h, hidnF h]), hv'b]⟩
        have hs2 : P.f + 1 ≤ (Finset.univ.filter
            (fun id => ({ a2 with call := t₂ } : SpecState P.n).call id = some b)).card := by
          refine le_trans hmat (Finset.card_le_card ?_)
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          show t₂ x = some b
          rw [ht₂eval x]
          rcases hx with ⟨-, hg⟩ | hF
          · rw [if_pos (Or.inl hg)]
          · rw [if_pos (Or.inr hF)]
        have hreb2 := rebind_mixed (a := { a2 with call := t₂ }) hq2 hpair2.1 hpair2.2 b hs2
        obtain ⟨a4, hw4, h1, h2, h3, h4, h5, h6⟩ := val_force'
          (a := { a2 with call := fun _ => none, bind := some b, coin := .bot })
          (b := b) rfl (fun _ => rfl) rfl (Or.inl hval)
        exact ⟨a4, weakTau_trans hfill2 (weakTau_trans hreb2 hw4), h1, h2, h4, h5, h3, h6⟩
  obtain ⟨a3, hw3, h1, h2, h3, h4, h5, h6⟩ := hstage2
  exact ⟨a3, weakTau_trans hchain1 hw3, h1, h2, h3, h4, h5, h6⟩

/-- **Visible-row packaging.** A single concrete Dirac outcome `s_C'` matched by a single
abstract state `a'` (`coreR`-related) closes the `weakStep` disjunct of the simulation clause:
the coupling is the Dirac-of-Dirac `ω := pure (pure a')`, whose `bind id` collapses back to
`pure a'` (`PMF.pure_bind`), so any `weakStep (spec P) (pure a) l (pure a')` transfers directly. -/
private theorem dirac_step {P : Params} (s_C' : HState P) (a' : SpecState P.n)
    (hcoreR : coreR P s_C' a') :
    ∃ ω : PMF (PMF (SpecState P.n)),
      PMFRel (coreRel P) (PMF.pure s_C') ω ∧ ω.bind id = PMF.pure a' := by
  refine ⟨PMF.pure (PMF.pure a'), ⟨PMF.pure (s_C', PMF.pure a'), ?_, ?_, ?_⟩, ?_⟩
  · rw [PMF.pure_map]
  · rw [PMF.pure_map]
  · intro p hp; rw [PMF.mem_support_pure_iff] at hp; subst hp; exact ⟨a', rfl, hcoreR⟩
  · rw [PMF.pure_bind]; rfl

/-- A hidden-API label can never be visible at the `hybridSpec` level (it is always relabeled to
`τ` by `.abstract`), so any purported `hybridSpec`-step carrying one is vacuous. -/
private theorem hidden_label_impossible {P : Params} {s_C : HState P} {l : Lab P.n}
    {μ_C : PMF (HState P)} (hmem : l ∈ Lab.hiddenAPI P.n) (hne : l ≠ Silent.τ)
    (hstep : (hybridSpec P).step s_C l μ_C) : False := by
  unfold hybridSpec at hstep
  rw [System.abstract_step] at hstep
  rcases hstep with ⟨h, -⟩ | ⟨h, -⟩
  · exact hne h
  · exact h hmem

/-- **The core simulation.** `hybridSpec P` is a probabilistic forward simulation of `spec P`
along `coreRel P` (the never-flipping abstract twin). -/
theorem coreSim (P : Params) :
    ProbabilisticForwardSimulation (hybridSpec P) (spec P) (coreRel P) := by
  refine ⟨⟨PMF.pure (SpecState.initial P.n), ?_, SpecState.initial P.n, rfl, Inv.initial P,
    Abs.initial P⟩, ?_⟩
  · intro s_A hs_A; rw [PMF.mem_support_pure_iff] at hs_A; exact hs_A
  · intro s_C μ_A hR l μ_C hstep
    obtain ⟨g, c, w⟩ := s_C
    obtain ⟨a, rfl, hI, hAbs⟩ := hR
    dsimp only at hI hAbs
    cases l with
    | tau =>
      rcases hybrid_step_tau P g c w μ_C hstep with
        ⟨r, μr, hstepG, rfl⟩ | ⟨μc, hstepC, rfl⟩ | ⟨r, μw', hstepW, rfl⟩ |
        ⟨r, id, b, μr, μc, hstepG, hstepC, rfl⟩ |
        ⟨r, id, out, μr, μc, hstepG, hstepC, rfl⟩ |
        ⟨r, id, μw', μc, hstepW, hstepC, rfl⟩ | ⟨r, id, b, μw', μc, hstepW, hstepC, rfl⟩
      · -- row 3: `bindUnset` (`gbcaTau`) — the ultra-lazy twin (D16) always stutters
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', c', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF] at hs'
          obtain ⟨hh1, hh2⟩ := hs'
          rw [PMF.mem_support_map_iff] at hh1; rw [PMF.mem_support_pure_iff] at hh2
          obtain ⟨gr', hgr', heq⟩ := hh1
          have hc : c' = c := congrArg Prod.fst hh2
          have hw : w' = w := congrArg Prod.snd hh2
          exact ⟨hI', by rw [← heq, hc, hw]; exact hAbs.step_gbcaTau hI r hstepG hgr'⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
      · -- rows 2/8: core τ (DECIDED delivery/echo/byz)
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', c', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hs'
          obtain ⟨h1, h2, h3⟩ := hs'
          exact ⟨hI', by rw [h1, h3]; exact hAbs.step_coreTau hI hstepC h2⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
      · -- row 6: WCC flip — always a constant-coupled stutter (`coin_bot`: `Abs` never
        -- reads `w`, so every outcome of the coin lands on the same abstract twin `a`)
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', c', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hs'
          obtain ⟨h1, h2, _⟩ := hs'
          exact ⟨hI', by rw [h1, h2]; exact hAbs.w_swap⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
      · -- row: callG handshake
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', c', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF, PMF.mem_support_pure_iff,
            PMF.mem_support_map_iff] at hs'
          obtain ⟨⟨gr', hgr', heq⟩, h2, h3⟩ := hs'
          exact ⟨hI', by rw [← heq, h3]; exact hAbs.step_callG hI r id b hstepG hstepC hgr' h2⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
      · -- row: retG handshake
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', c', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF, PMF.mem_support_pure_iff,
            PMF.mem_support_map_iff] at hs'
          obtain ⟨⟨gr', hgr', heq⟩, h2, h3⟩ := hs'
          exact ⟨hI', by
            rw [← heq, h3]; exact hAbs.step_retG hI r id out hstepG hstepC hgr' h2⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
      · -- row: callW handshake
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', c', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF, PMF.mem_support_pure_iff,
            PMF.mem_support_map_iff] at hs'
          obtain ⟨h1, h2, ⟨wr', hwr', heq⟩⟩ := hs'
          exact ⟨hI', by rw [h1, ← heq]; exact hAbs.step_callW hI r id hstepW hstepC hwr' h2⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
      · -- row: retW handshake
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', c', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF, PMF.mem_support_pure_iff,
            PMF.mem_support_map_iff] at hs'
          obtain ⟨h1, h2, ⟨wr', hwr', heq⟩⟩ := hs'
          exact ⟨hI', by rw [h1, ← heq]; exact hAbs.step_retW hI r id b hstepW hstepC hwr' h2⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
    | callABA id b =>
      rw [hybrid_step_callABA] at hstep
      obtain ⟨μc, hstepC, rfl⟩ := hstep
      have hdisj := (coreStep_callABA_iff P c id b μc).mp hstepC
      rcases hdisj with ⟨hin, rfl⟩ | rfl
      · -- genuine fresh input: rule 1 in phase 1 (banks call + ghost, overwriting any
        -- self-loop-banked junk), rule 2 in phase 2 (first-write-wins ghost)
        set c' := c.setProc id { c.procs id with
          input := some b, est := some b, round := 0, phase := .toCallG } with hc'def
        have hc'mem : c' ∈ (PMF.pure c').support := by rw [PMF.mem_support_pure_iff]
        have hIAF := Inv.step_callABA hI id b hstepC hc'mem
        have hIA' : Inv P g c' w := hIAF.1
        have hCF : c'.F = c.F := CoreState.setProc_F _ _ _
        have hSelf : c'.procs id = { c.procs id with
            input := some b, est := some b, round := 0, phase := .toCallG } := by
          rw [hc'def]; exact CoreState.setProc_procs_self _ _ _
        have hNe : ∀ id', id' ≠ id → c'.procs id' = c.procs id' := by
          intro id' h; rw [hc'def]; exact CoreState.setProc_procs_ne _ _ _ h
        rcases hAbs.phase with ⟨hb, hv, hcall, hghost⟩ |
          ⟨v, hb2, hv2, hcall2, ⟨r0, hcv0⟩, hpin⟩
        · -- phase 1: rule 1
          have hcallnone : a.call id = none := by rw [hcall id, hin]
          set a' : SpecState P.n := { a with
            call := Function.update a.call id (some b)
            input := Function.update a.input id (some b) } with ha'def
          have hAbs' : Abs P g c' w a' := by
            refine ⟨by rw [hCF]; exact hAbs.F_eq, fun id' => ?_, hAbs.coin_bot,
              Or.inl ⟨hb, hv, ?_, ?_⟩⟩
            · show a.ret id' = (c'.procs id').returned
              by_cases h : id' = id
              · rw [h, hSelf]; exact hAbs.ret_eq id
              · rw [hNe id' h]; exact hAbs.ret_eq id'
            · intro id'
              show Function.update a.call id (some b) id' = (c'.procs id').input
              by_cases h : id' = id
              · rw [h, Function.update_self, hSelf]
              · rw [Function.update_of_ne h, hNe id' h]; exact hcall id'
            · intro id' b' hb'
              show Function.update a.input id (some b) id' = some b'
              by_cases h : id' = id
              · rw [h, Function.update_self]
                rw [h, hSelf] at hb'
                exact hb'
              · rw [Function.update_of_ne h]
                rw [hNe id' h] at hb'
                exact hghost id' b' hb'
          rw [prodPMF_pure_pure_pure]
          obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, c', w) a' ⟨hIA', hAbs'⟩
          refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
          rw [hbid]
          exact weakStep_strong (SpecStep.callSet a id b hcallnone hb)
        · -- phase 2: rule 2
          set a' : SpecState P.n := { a with
            input := if a.input id = none then Function.update a.input id (some b)
              else a.input } with ha'def
          have hAbs' : Abs P g c' w a' := by
            refine ⟨by rw [hCF]; exact hAbs.F_eq, fun id' => ?_, hAbs.coin_bot,
              Or.inr ⟨v, hb2, hv2, hcall2, hIAF.2.1 r0 v hcv0, hIAF.2.2 v ⟨r0, hcv0⟩ hpin⟩⟩
            show a.ret id' = (c'.procs id').returned
            by_cases h : id' = id
            · rw [h, hSelf]; exact hAbs.ret_eq id
            · rw [hNe id' h]; exact hAbs.ret_eq id'
          rw [prodPMF_pure_pure_pure]
          obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, c', w) a' ⟨hIA', hAbs'⟩
          refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
          rw [hbid]
          exact weakStep_strong (SpecStep.callLoop a id b)
      · -- concrete self-loop: rule 2 in either phase (a junk ghost may bank; phase 1's
        -- sync clause only tracks committed concrete inputs, which are untouched here)
        set a' : SpecState P.n := { a with
          input := if a.input id = none then Function.update a.input id (some b)
            else a.input } with ha'def
        have hAbs' : Abs P g c w a' := by
          refine ⟨hAbs.F_eq, hAbs.ret_eq, hAbs.coin_bot, ?_⟩
          rcases hAbs.phase with ⟨hb, hv, hcall, hghost⟩ | hph2
          · refine Or.inl ⟨hb, hv, hcall, ?_⟩
            intro id' b' hin'
            have hgin : a.input id' = some b' := hghost id' b' hin'
            show (if a.input id = none then Function.update a.input id (some b)
              else a.input) id' = some b'
            by_cases h : id' = id
            · rw [if_neg (by rw [← h, hgin]; simp)]
              exact hgin
            · by_cases hcond : a.input id = none
              · rw [if_pos hcond, Function.update_of_ne h]; exact hgin
              · rw [if_neg hcond]; exact hgin
          · exact Or.inr hph2
        rw [prodPMF_pure_pure_pure]
        obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, c, w) a' ⟨hI, hAbs'⟩
        refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
        rw [hbid]
        exact weakStep_strong (SpecStep.callLoop a id b)
    | retABA id b =>
      rw [hybrid_step_retABA] at hstep
      obtain ⟨μc, hstepC, rfl⟩ := hstep
      rw [coreStep_retABA_iff] at hstepC
      obtain ⟨hcnt, hs, hret, rfl⟩ := hstepC
      set c' := c.setProc id { c.procs id with returned := true } with hc'def
      have hc'mem : c' ∈ (PMF.pure c').support := by rw [PMF.mem_support_pure_iff]
      have hIAF := Inv.step_retABA hI id b (by
        rw [coreStep_retABA_iff]; exact ⟨hcnt, hs, hret, rfl⟩) hc'mem
      have hIA' : Inv P g c' w := hIAF.1
      -- Honest DECIDED-sender pigeonhole: `n − f` distinct senders of `b` delivered to `id`,
      -- only `f` corrupted — equivocating byzantine senders may count toward the tally, but
      -- at least one counted sender is never-corrupted (D12′).
      have hex : ∃ j, j ∉ c.F ∧ b ∈ c.decidedRecv id j := by
        by_contra hcon; push Not at hcon
        have hsub : (Finset.univ.filter (fun j => b ∈ c.decidedRecv id j)) ⊆ c.F := by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          by_contra hnf; exact hcon j hnf hj
        have hcard := Finset.card_le_card hsub
        have hfc := hI.F_card
        have hf3 := P.hf
        unfold CoreState.decidedCount at hcnt
        omega
      obtain ⟨j, hjF, hjrecv⟩ := hex
      have hjsent : b ∈ c.decidedSent j := hI.recv_sound id j b hjrecv
      obtain ⟨rA, hrA_cert⟩ := hI.decided_src j b hjF hjsent
      -- the twin-level holder pin for `b`: every honest `A`-decision holder agrees with the
      -- harvested sender's pooled bit (I30)
      have hpinb : ∀ j0 b0', j0 ∉ c.F → AHolder P c j0 b0' → b0' = b :=
        fun j0 b0' hj0 hh0 => hI.alock_agree j0 j b0' b hj0 hjF hh0 (Or.inr hjsent)
      have hretfalse : a.ret id = false := by rw [hAbs.ret_eq id]; exact hret
      have hCF : c'.F = c.F := CoreState.setProc_F _ _ _
      rcases hAbs.phase with ⟨hb, hv, hcall, hghost⟩ |
        ⟨v, hb2, hv2, hcall2, ⟨r0, hcv0⟩, hpin⟩
      · -- phase 1: the decide burst (D16), then rule 8
        have hq : a.quorum P := abstract_quorum_of_call (aF := a.F) (aCall := a.call) hI
          hAbs.F_eq (fun id0 _ hin0 => by rw [hcall id0]; exact hin0) (r := rA)
          (fun hemp => absurd (hemp ▸ hrA_cert.2.1) (Finset.notMem_empty _))
        have hmat : P.f + 1 ≤ (Finset.univ.filter
            (fun id0 => (a.call id0 = some b ∧ a.input id0 = some b) ∨ id0 ∈ a.F)).card := by
          refine le_trans (hI.bind_supp rA b hrA_cert.2.1) (Finset.card_le_card ?_)
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          rcases hx with hin0 | hF0
          · exact Or.inl ⟨by rw [hcall x]; exact hin0, hghost x b hin0⟩
          · exact Or.inr (by rw [hAbs.F_eq]; exact hF0)
        have hFcard : a.F.card ≤ P.f := by rw [hAbs.F_eq]; exact hI.F_card
        obtain ⟨a1, hburst, hval1, hbind1, hret1, hF1, hcall1, hcoin1⟩ :=
          decide_burst hv hq hFcard hmat
        have hretid : a1.ret id = false := by rw [hret1]; exact hretfalse
        set a'' : SpecState P.n := { a1 with ret := Function.update a1.ret id true } with ha''def
        have hAbs'' : Abs P g c' w a'' := by
          refine ⟨?_, ?_, ?_, Or.inr ⟨b, ?_, ?_, ?_, hIAF.2.1 rA b hrA_cert,
            hIAF.2.2 b ⟨rA, hrA_cert⟩ hpinb⟩⟩
          · show a1.F = c'.F
            rw [hF1, hAbs.F_eq, hCF]
          · intro id'
            show Function.update a1.ret id true id' = (c'.procs id').returned
            by_cases h : id' = id
            · rw [h, Function.update_self, hc'def, CoreState.setProc_procs_self]
            · rw [Function.update_of_ne h, hret1, hc'def, CoreState.setProc_procs_ne _ _ _ h]
              exact hAbs.ret_eq id'
          · show a1.coin = .bot
            exact hcoin1
          · show a1.bind = some b
            exact hbind1
          · show a1.val = some b
            exact hval1
          · intro id0
            show a1.call id0 = none
            rw [hcall1]
        rw [prodPMF_pure_pure_pure]
        obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, c', w) a'' ⟨hIA', hAbs''⟩
        refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
        rw [hbid]
        exact weakStep_of_burst_then_step hburst (SpecStep.ret a1 id b hval1 hretid)
      · -- phase 2: `b` agrees with the certified value through the twin's holder pin
        -- (I30 pins the harvested sender's pooled `b` against every honest holder, and the
        -- twin's pin names `v`; rule 8 fires directly)
        have hD3 : v = b := (hpin j b hjF (Or.inr hjsent)).symm
        have hvalb : a.val = some b := by rw [hv2, hD3]
        set a'' : SpecState P.n := { a with ret := Function.update a.ret id true } with ha''def
        have hAbs'' : Abs P g c' w a'' := by
          refine ⟨?_, ?_, hAbs.coin_bot, Or.inr ⟨v, hb2, hv2, hcall2, hIAF.2.1 r0 v hcv0,
            hIAF.2.2 v ⟨r0, hcv0⟩ hpin⟩⟩
          · show a.F = c'.F
            rw [hAbs.F_eq, hCF]
          · intro id'
            show Function.update a.ret id true id' = (c'.procs id').returned
            by_cases h : id' = id
            · rw [h, Function.update_self, hc'def, CoreState.setProc_procs_self]
            · rw [Function.update_of_ne h, hc'def, CoreState.setProc_procs_ne _ _ _ h]
              exact hAbs.ret_eq id'
        rw [prodPMF_pure_pure_pure]
        obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, c', w) a'' ⟨hIA', hAbs''⟩
        refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
        rw [hbid]
        exact weakStep_strong (SpecStep.ret a id b hvalb hretfalse)
    | callG r id b => exact (hidden_label_impossible (by simp) (by simp) hstep).elim
    | retG r id out => exact (hidden_label_impossible (by simp) (by simp) hstep).elim
    | callW r id => exact (hidden_label_impossible (by simp) (by simp) hstep).elim
    | retW r id b => exact (hidden_label_impossible (by simp) (by simp) hstep).elim
    | fail id =>
      rw [hybrid_step_fail] at hstep
      subst hstep
      have hEq : prodPMF (PMF.pure (fun r => (g r).corrupt P id))
          (prodPMF (PMF.pure (c.corrupt P id)) (PMF.pure (fun r => (w r).corrupt P id))) =
          PMF.pure (fun r => (g r).corrupt P id, (c.corrupt P id, fun r => (w r).corrupt P id)) := by
        simp [prodPMF, PMF.pure_bind]
      rw [hEq]
      have hFsub := CoreState.corrupt_F_subset c id
      have hAbs' : Abs P (fun r => (g r).corrupt P id) (c.corrupt P id)
          (fun r => (w r).corrupt P id) (a.corrupt P id) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · show (a.corrupt P id).F = (c.corrupt P id).F
          unfold SpecState.corrupt CoreState.corrupt
          rw [hAbs.F_eq]; split_ifs <;> simp [hAbs.F_eq]
        · intro id'
          rw [SpecState.corrupt_ret, CoreState.corrupt_procs]; exact hAbs.ret_eq id'
        · rw [SpecState.corrupt_coin]; exact hAbs.coin_bot
        · rcases hAbs.phase with ⟨hb, hv, hcall, hghost⟩ |
            ⟨v, hb, hv, hcall, ⟨r0, hcv0⟩, hpin⟩
          · refine Or.inl ⟨?_, ?_, ?_, ?_⟩
            · rw [SpecState.corrupt_bind]; exact hb
            · rw [SpecState.corrupt_val]; exact hv
            · intro id'
              rw [SpecState.corrupt_call, CoreState.corrupt_procs]; exact hcall id'
            · intro id' b' h
              rw [CoreState.corrupt_procs] at h
              rw [SpecState.corrupt_input]; exact hghost id' b' h
          · refine Or.inr ⟨v, ?_, ?_, ?_, (hI.step_fail id).2.1 r0 v hcv0,
              (hI.step_fail id).2.2 v ⟨r0, hcv0⟩ hpin⟩
            · rw [SpecState.corrupt_bind]; exact hb
            · rw [SpecState.corrupt_val]; exact hv
            · intro id'; rw [SpecState.corrupt_call]; exact hcall id'
      have hIA' : Inv P (fun r => (g r).corrupt P id) (c.corrupt P id)
          (fun r => (w r).corrupt P id) := (hI.step_fail id).1
      refine ⟨PMF.pure (PMF.pure (a.corrupt P id)), ⟨PMF.pure
        ((fun r => (g r).corrupt P id, (c.corrupt P id, fun r => (w r).corrupt P id)),
          PMF.pure (a.corrupt P id)), ?_, ?_, ?_⟩, Or.inr ⟨by simp, ?_⟩⟩
      · rw [PMF.pure_map]
      · rw [PMF.pure_map]
      · intro p hp
        rw [PMF.mem_support_pure_iff] at hp
        subst hp
        exact ⟨a.corrupt P id, rfl, hIA', hAbs'⟩
      · rw [PMF.pure_bind]
        exact weakStep_strong (SpecStep.fail a id)

end ABA
end PLTS
