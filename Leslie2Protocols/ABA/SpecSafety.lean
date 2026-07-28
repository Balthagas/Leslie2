/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Spec
import Leslie2Protocols.Framework.TraceSupport

/-!
# Safety of the ABA specification

Validity and Agreement, stated as predicates on traces and proven for every
trace in the support of every achievable trace distribution of `ABA.spec`
(`ABA.spec_safe`). This validates the D3 and D13 repairs: Agreement is
*false* for the blueprint's unrepaired Transition System 1, and the papers'
Validity is false for the D3-only repair (a later-corrupted caller's input can win).

The proof is invariant reasoning along genuine executions (via
`TraceSupport`):

* `SpecInv` — the state invariant: `|F| ≤ f`; once `val = some v` the bound
  value equals `val` and every honest pending input is `⊥` or `val`; and the
  D13 provenance conjuncts V-P0–V-P3: while unbound every pending input is
  ghost-recorded or corrupt (`call_prov`), bound and decided values carry
  `f + 1` supporters (`bind_supp`, `val_supp`), and while bound every
  pending input is recorded, the bound value, or corrupt (`bound_prov`).
* `SpecInv.val_stable` — the decision value is write-once: the unanimity rule
  can only rewrite `val` to itself (the quorum argument, using `f < n − f`).
* `ValInv` — the label-history-aware invariant: ghost-recorded inputs are
  attributed to `callABA` events in the history (`input_src`), and the
  corrupted set is exactly the fold of D1-`corrupt` over the labels seen so
  far (`F_eq`).

`AgreementTrace` requires *any* two returns (honest or not) to agree —
stronger than the blueprint's correct-process phrasing, since `ABA.spec`'s
return rule does not inspect `F`. `ValidityTrace` is the paper-form
statement (D13): every return of `b` is *preceded* (positionally) by a
`callABA _ b` event whose caller is never corrupted anywhere along the
trace (`NeverCorrupted`, via the trace-level corruption fold `failSet`) —
returner-unconditional, hence stronger than the papers on the returns axis
and faithful on the witness axis: the witnessing caller must be never
corrupted, not merely a member of some support set that a later `fail`
could taint.

The Validity endgame is a budget pigeonhole: at any return, `val_supp`
yields `f + 1` supporters of the returned bit; every supporter is either
ghost-recorded (hence a genuine preceding `callABA`, by `input_src`) or
ever-corrupted, and at most `f` ids are *ever* corrupted (`failSet` never
exceeds the budget) — so some recorded supporter is never corrupted.
-/

open Stream'

namespace PLTS
namespace ABA

variable {P : Params}

/-! ### The trace-level corruption fold -/

/-- One D1-`corrupt` on a bare corrupted set: insert when the budget allows. -/
def corruptF (P : Params) (id : Fin P.n) (F : Finset (Fin P.n)) : Finset (Fin P.n) :=
  if id ∉ F ∧ F.card < P.f then insert id F else F

/-- Fold one label into the corrupted set: `corruptF` on `fail id`, identity
on every other label. -/
def failStep (P : Params) (F : Finset (Fin P.n)) : Lab P.n → Finset (Fin P.n)
  | .fail id => corruptF P id F
  | _ => F

/-- The corrupted set determined by a label list: the fold of D1-`corrupt`
over its `fail` labels. -/
def failSetL (P : Params) (L : List (Lab P.n)) : Finset (Fin P.n) :=
  L.foldl (failStep P) ∅

/-- The corrupted set after the first `k` labels of a trace. -/
def failSet (P : Params) (t : Seq (Lab P.n)) : ℕ → Finset (Fin P.n)
  | 0 => ∅
  | k + 1 =>
    match t.get? k with
    | some l => failStep P (failSet P t k) l
    | none => failSet P t k

/-- `id` is never corrupted along the trace `t`. -/
def NeverCorrupted (P : Params) (t : Seq (Lab P.n)) (id : Fin P.n) : Prop :=
  ∀ k, id ∉ failSet P t k

/-! ### The trace-level safety predicates -/

/-- **Validity** (paper form, D13): every return of `b` (at any trace
position `m`) is preceded by a `callABA id' b` event whose caller `id'` is
never corrupted anywhere along the trace. Returner-unconditional: the
returning process is not required to be honest. -/
def ValidityTrace (P : Params) (t : Seq (Lab P.n)) : Prop :=
  ∀ m id b, t.get? m = some (Lab.retABA id b) →
    ∃ k, k < m ∧ ∃ id', t.get? k = some (Lab.callABA id' b) ∧
      NeverCorrupted P t id'

/-- **Agreement** (trace form): any two returns carry the same bit. -/
def AgreementTrace {n : ℕ} (t : Seq (Lab n)) : Prop :=
  ∀ id b id' b', Lab.retABA id b ∈ t → Lab.retABA id' b' ∈ t → b = b'

/-! ### Budget and monotonicity of the corruption fold -/

@[simp] theorem failSet_zero (t : Seq (Lab P.n)) : failSet P t 0 = ∅ := rfl

theorem failSet_succ (t : Seq (Lab P.n)) (k : ℕ) :
    failSet P t (k + 1) =
      match t.get? k with
      | some l => failStep P (failSet P t k) l
      | none => failSet P t k := rfl

theorem subset_failStep (F : Finset (Fin P.n)) (l : Lab P.n) :
    F ⊆ failStep P F l := by
  cases l <;> try exact fun _ h => h
  case fail id =>
    change F ⊆ corruptF P id F
    unfold corruptF
    split
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _

theorem failStep_card_le {F : Finset (Fin P.n)} (h : F.card ≤ P.f)
    (l : Lab P.n) : (failStep P F l).card ≤ P.f := by
  cases l <;> try exact h
  case fail id =>
    change (corruptF P id F).card ≤ P.f
    unfold corruptF
    split
    · next hc =>
      have h1 := Finset.card_insert_le id F
      have h2 := hc.2
      omega
    · exact h

theorem failSet_card_le (t : Seq (Lab P.n)) :
    ∀ k, (failSet P t k).card ≤ P.f := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [failSet_succ]
    cases hg : t.get? k with
    | some l => exact failStep_card_le ih l
    | none => exact ih

theorem failSet_mono (t : Seq (Lab P.n)) {k k' : ℕ} (h : k ≤ k') :
    failSet P t k ⊆ failSet P t k' := by
  induction k' with
  | zero =>
    obtain rfl : k = 0 := Nat.le_zero.mp h
    exact Finset.Subset.refl _
  | succ m ih =>
    by_cases hk : k = m + 1
    · subst hk; exact Finset.Subset.refl _
    · refine (ih (by omega)).trans ?_
      rw [failSet_succ]
      cases hg : t.get? m with
      | some l => exact subset_failStep _ l
      | none => exact fun _ hx => hx

theorem failSetL_append (L : List (Lab P.n)) (l : Lab P.n) :
    failSetL P (L ++ [l]) = failStep P (failSetL P L) l := by
  unfold failSetL
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Folding over a filtered list agrees with folding over the original when
the filter keeps every `fail` label. -/
theorem foldl_failStep_filter {p : Lab P.n → Bool}
    (hp : ∀ id : Fin P.n, p (.fail id) = true) :
    ∀ (L : List (Lab P.n)) (F : Finset (Fin P.n)),
      (L.filter p).foldl (failStep P) F = L.foldl (failStep P) F := by
  intro L
  induction L with
  | nil => intro F; rfl
  | cons l L ih =>
    intro F
    by_cases hl : p l = true
    · rw [List.filter_cons_of_pos hl, List.foldl_cons, List.foldl_cons]
      exact ih _
    · have hstep : failStep P F l = F := by
        cases l <;> first | rfl | exact absurd (hp _) hl
      rw [List.filter_cons_of_neg (by simpa using hl), List.foldl_cons, hstep]
      exact ih F

/-- `failSetL` ignores filtering that keeps every `fail` label. -/
theorem failSetL_filter {p : Lab P.n → Bool}
    (hp : ∀ id : Fin P.n, p (.fail id) = true) (L : List (Lab P.n)) :
    failSetL P (L.filter p) = failSetL P L :=
  foldl_failStep_filter hp L ∅

/-- The trace-level fold over `Seq.ofList` is the list-level fold of the
`take`-prefix. -/
theorem failSet_ofList (L : List (Lab P.n)) :
    ∀ k, failSet P (Seq.ofList L) k = failSetL P (L.take k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [failSet_succ]
    cases hg : (Seq.ofList L).get? k with
    | some l =>
      change failStep P (failSet P (Seq.ofList L) k) l = _
      rw [Seq.ofList_get?] at hg
      rw [ih, List.take_add_one, hg, Option.toList_some, failSetL_append]
    | none =>
      change failSet P (Seq.ofList L) k = _
      rw [Seq.ofList_get?] at hg
      rw [ih, List.take_add_one, hg, Option.toList_none, List.append_nil]

/-- A finite set each of whose members is eventually corrupted is corrupted
at a single uniform stage (`failSet` is monotone in the stage). -/
theorem exists_uniform_stage (t : Seq (Lab P.n)) (S : Finset (Fin P.n)) :
    (∀ id ∈ S, ∃ k, id ∈ failSet P t k) →
    ∃ K, ∀ id ∈ S, id ∈ failSet P t K := by
  classical
  induction S using Finset.induction_on with
  | empty => exact fun _ => ⟨0, fun id h => absurd h (Finset.notMem_empty id)⟩
  | insert a S ha ih =>
    intro h
    obtain ⟨ka, hka⟩ := h a (Finset.mem_insert_self a S)
    obtain ⟨K, hK⟩ := ih fun id hid => h id (Finset.mem_insert_of_mem hid)
    refine ⟨max ka K, fun id hid => ?_⟩
    rcases Finset.mem_insert.mp hid with rfl | hid
    · exact failSet_mono t (le_max_left ka K) hka
    · exact failSet_mono t (le_max_right ka K) (hK id hid)

/-! ### `f + 1`-support -/

/-- D13 support for `v`: `f + 1` ids, each either ghost-recorded as
inputting `v` or corrupted. Monotone in `input` and `F`, hence stable under
`fail` and banking. -/
def SuppOK (P : Params) (s : SpecState P.n) (v : Bool) : Prop :=
  P.f + 1 ≤ (Finset.univ.filter (fun id => s.input id = some v ∨ id ∈ s.F)).card

theorem SuppOK.mono {s s' : SpecState P.n} {v : Bool} (h : SuppOK P s v)
    (hin : ∀ id, s.input id = some v → s'.input id = some v)
    (hF : s.F ⊆ s'.F) : SuppOK P s' v := by
  refine le_trans h (Finset.card_le_card ?_)
  intro id hid
  rw [Finset.mem_filter] at hid ⊢
  exact ⟨hid.1, hid.2.imp (hin id) (fun hm => hF hm)⟩

/-! ### The state invariant -/

/-- The core state invariant of `ABA.spec`: the corrupted set respects the
budget; once the decision value is fixed it agrees with the bound value and
dominates every honest pending input; and the D13 provenance conjuncts
V-P0–V-P3 (`call_prov`, `bind_supp`, `val_supp`, `bound_prov`). -/
structure SpecInv (P : Params) (s : SpecState P.n) : Prop where
  F_le : s.F.card ≤ P.f
  bind_val : s.val ≠ none → s.bind = s.val
  call_val : ∀ id, id ∉ s.F → s.val ≠ none →
    s.call id = none ∨ s.call id = s.val
  /-- V-P0: while unbound, every pending input is ghost-recorded or corrupt. -/
  call_prov : s.bind = none → ∀ id b, s.call id = some b →
    s.input id = some b ∨ id ∈ s.F
  /-- V-P1: the bound value has `f + 1` supporters. -/
  bind_supp : ∀ v, s.bind = some v → SuppOK P s v
  /-- V-P2: the decision value has `f + 1` supporters. -/
  val_supp : ∀ v, s.val = some v → SuppOK P s v
  /-- V-P3: while bound, every pending input is ghost-recorded, the bound
  value, or corrupt (post-`val`, `bind_val` collapses rule 7's `val`-branch
  writes into the middle disjunct). -/
  bound_prov : ∀ v, s.bind = some v → ∀ id b, s.call id = some b →
    s.input id = some b ∨ b = v ∨ id ∈ s.F

theorem SpecInv.initial (P : Params) : SpecInv P (SpecState.initial P.n) where
  F_le := by simp [SpecState.initial]
  bind_val := fun h => absurd rfl h
  call_val := fun _ _ h => absurd rfl h
  call_prov := fun _ _ _ h => absurd h (by simp [SpecState.initial])
  bind_supp := fun _ h => absurd h (by simp [SpecState.initial])
  val_supp := fun _ h => absurd h (by simp [SpecState.initial])
  bound_prov := fun _ h => absurd h (by simp [SpecState.initial])

/-! Field stability of `corrupt`. -/

section Corrupt

variable (s : SpecState P.n) (id : Fin P.n)

@[simp] theorem corrupt_call : (s.corrupt P id).call = s.call := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_ret : (s.corrupt P id).ret = s.ret := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_bind : (s.corrupt P id).bind = s.bind := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_val : (s.corrupt P id).val = s.val := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_coin : (s.corrupt P id).coin = s.coin := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_input : (s.corrupt P id).input = s.input := by
  unfold SpecState.corrupt; split <;> rfl

/-- `corrupt` acts on `F` exactly as the bare-set fold step `corruptF`. -/
theorem corrupt_F : (s.corrupt P id).F = corruptF P id s.F := by
  unfold SpecState.corrupt corruptF
  split <;> rfl

theorem corrupt_F_subset : s.F ⊆ (s.corrupt P id).F := by
  unfold SpecState.corrupt
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

theorem corrupt_card_le (hF : s.F.card ≤ P.f) : (s.corrupt P id).F.card ≤ P.f := by
  unfold SpecState.corrupt
  split
  · next hc =>
    show (insert id s.F).card ≤ P.f
    have h2 := hc.2
    have h3 := Finset.card_insert_le id s.F
    omega
  · exact hF

end Corrupt

/-- A quorum with a bounded corrupted set contains an honest pending input. -/
theorem exists_honest_call {s : SpecState P.n}
    (hq : s.quorum P) (hF : s.F.card ≤ P.f) :
    ∃ id, id ∉ s.F ∧ s.call id ≠ none := by
  by_contra hc
  push_neg at hc
  have h_empty : Finset.univ.filter (fun id => id ∉ s.F ∧ s.call id ≠ none) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    rintro id - ⟨h1, h2⟩
    exact h2 (hc id h1)
  unfold SpecState.quorum at hq
  rw [h_empty, Finset.empty_union] at hq
  have := P.f_lt_n_sub_f
  omega

/-- A quorum with a bounded corrupted set has `f + 1` *honest* callers
(`n − 2f ≥ f + 1` from `3f < n`). -/
theorem honest_callers_ge {s : SpecState P.n}
    (hq : s.quorum P) (hF : s.F.card ≤ P.f) :
    P.f + 1 ≤ (Finset.univ.filter (fun id => id ∉ s.F ∧ s.call id ≠ none)).card := by
  unfold SpecState.quorum at hq
  have hu := Finset.card_union_le
    (Finset.univ.filter (fun id => id ∉ s.F ∧ s.call id ≠ none)) s.F
  have hn := P.hf
  omega

/-- Harvest for the unanimity rule: its `f + 1` honest callers all carry
`!b`, and each is a recorded supporter — or the bound value equals `!b` and
V-P1 closes directly. -/
theorem unanim_suppOK {s : SpecState P.n} {b : Bool} (hI : SpecInv P s)
    (hq : s.quorum P) (hb : ∀ id, id ∉ s.F → s.call id ≠ some b) :
    SuppOK P s (!b) := by
  -- every honest caller calls `!b`
  have hcall : ∀ id, id ∉ s.F → s.call id ≠ none → s.call id = some (!b) := by
    intro id hid hne
    obtain ⟨c, hc⟩ : ∃ c, s.call id = some c := by
      cases h : s.call id with
      | none => exact absurd h hne
      | some c => exact ⟨c, rfl⟩
    have hcb : c ≠ b := fun h => hb id hid (h ▸ hc)
    rw [hc]
    cases c <;> cases b <;> simp_all
  cases hbind : s.bind with
  | some v =>
    by_cases hveq : v = !b
    · exact hveq ▸ hI.bind_supp v hbind
    · refine le_trans (honest_callers_ge hq hI.F_le) (Finset.card_le_card ?_)
      intro id hid
      rw [Finset.mem_filter] at hid ⊢
      obtain ⟨-, hnF, hne⟩ := hid
      rcases hI.bound_prov v hbind id (!b) (hcall id hnF hne) with h | h | h
      · exact ⟨Finset.mem_univ id, Or.inl h⟩
      · exact absurd h.symm hveq
      · exact absurd h hnF
  | none =>
    refine le_trans (honest_callers_ge hq hI.F_le) (Finset.card_le_card ?_)
    intro id hid
    rw [Finset.mem_filter] at hid ⊢
    obtain ⟨-, hnF, hne⟩ := hid
    rcases hI.call_prov hbind id (!b) (hcall id hnF hne) with h | h
    · exact ⟨Finset.mem_univ id, Or.inl h⟩
    · exact absurd h hnF

/-- Harvest for the mixed rule: its `f + 1` callers of `b` are supporters
through V-P0/V-P3 — or the bound value equals `b` and V-P1 closes. -/
theorem mixed_suppOK {s : SpecState P.n} {b : Bool} (hI : SpecInv P s)
    (hs : P.f + 1 ≤ (Finset.univ.filter (fun id => s.call id = some b)).card) :
    SuppOK P s b := by
  cases hbind : s.bind with
  | some v =>
    by_cases hveq : b = v
    · exact hveq.symm ▸ hI.bind_supp v hbind
    · refine le_trans hs (Finset.card_le_card ?_)
      intro id hid
      rw [Finset.mem_filter] at hid ⊢
      rcases hI.bound_prov v hbind id b hid.2 with h | h | h
      · exact ⟨hid.1, Or.inl h⟩
      · exact absurd h hveq
      · exact ⟨hid.1, Or.inr h⟩
  | none =>
    refine le_trans hs (Finset.card_le_card ?_)
    intro id hid
    rw [Finset.mem_filter] at hid ⊢
    exact ⟨hid.1, hI.call_prov hbind id b hid.2⟩

/-- If the unanimity rule fires while `val = some v` (under the invariant),
the value it writes is again `v`. -/
theorem unanim_rewrites_val {s : SpecState P.n} {b' v : Bool}
    (hI : SpecInv P s) (hv : s.val = some v)
    (hq : s.quorum P) (hb : ∀ id, id ∉ s.F → s.call id ≠ some b') :
    (!b') = v := by
  obtain ⟨id, h_hon, h_ne⟩ := exists_honest_call hq hI.F_le
  rcases hI.call_val id h_hon (by rw [hv]; simp) with h0 | h0
  · exact absurd h0 h_ne
  · have h_call : s.call id = some v := by rw [h0, hv]
    have h_neq : v ≠ b' := fun h => hb id h_hon (h ▸ h_call)
    cases v <;> cases b' <;> simp_all

/-- **Invariant preservation.** `SpecInv` is preserved by every step. -/
theorem SpecInv.step {s : SpecState P.n} {l : Lab P.n} {μ : PMF (SpecState P.n)}
    {s' : SpecState P.n} (hI : SpecInv P s)
    (hstep : SpecStep P s l μ) (hs' : s' ∈ μ.support) : SpecInv P s' := by
  cases hstep with
  | callSet id b h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    have hval : s.val = none := by
      by_contra hv
      have := hI.bind_val hv
      rw [h₂] at this
      exact hv this.symm
    refine ⟨hI.F_le, fun h => absurd hval h, fun id' _ h => absurd hval h,
      ?_, ?_, ?_, ?_⟩
    · -- call_prov: the fresh caller is freshly recorded
      intro _ id' b' h_call
      replace h_call : Function.update s.call id (some b) id' = some b' := h_call
      by_cases h_eq : id' = id
      · subst h_eq
        rw [Function.update_self] at h_call
        refine Or.inl ?_
        change Function.update s.input id' (some b) id' = some b'
        rw [Function.update_self]
        exact h_call
      · rw [Function.update_of_ne h_eq] at h_call
        refine (hI.call_prov h₂ id' b' h_call).imp (fun h => ?_) (fun h => h)
        change Function.update s.input id (some b) id' = some b'
        rw [Function.update_of_ne h_eq]
        exact h
    · intro v hv
      exact absurd (show s.bind = some v from hv) (by rw [h₂]; simp)
    · intro v hv
      exact absurd (show s.val = some v from hv) (by rw [hval]; simp)
    · intro v hv
      exact absurd (show s.bind = some v from hv) (by rw [h₂]; simp)
  | callLoop id b =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    have hnew : ∀ id' v, s.input id' = some v →
        (if s.input id = none then Function.update s.input id (some b)
          else s.input) id' = some v := by
      intro id' v hv
      by_cases hcond : s.input id = none
      · rw [if_pos hcond]
        by_cases h_eq : id' = id
        · subst h_eq; rw [hv] at hcond; exact absurd hcond (by simp)
        · rw [Function.update_of_ne h_eq]; exact hv
      · rw [if_neg hcond]; exact hv
    refine ⟨hI.F_le, hI.bind_val, hI.call_val, ?_, ?_, ?_, ?_⟩
    · intro hb id' b' h_call
      exact (hI.call_prov hb id' b' h_call).imp (hnew id' b') (fun h => h)
    · intro v hv
      exact (hI.bind_supp v hv).mono (fun i => hnew i v) (Finset.Subset.refl _)
    · intro v hv
      exact (hI.val_supp v hv).mono (fun i => hnew i v) (Finset.Subset.refl _)
    · intro v hv id' b' h_call
      rcases hI.bound_prov v hv id' b' h_call with h | h | h
      · exact Or.inl (hnew id' b' h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  | unanim b hq hb =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨hI.F_le, fun _ => rfl, fun id' _ _ => Or.inl rfl, ?_, ?_, ?_, ?_⟩
    · intro hbind
      exact absurd (show (some (!b) : Option Bool) = none from hbind) (by simp)
    · intro v hv
      have hbv : (some (!b) : Option Bool) = some v := hv
      obtain rfl : (!b) = v := Option.some.inj hbv
      exact unanim_suppOK (s := s) hI hq hb
    · intro v hv
      have hbv : (some (!b) : Option Bool) = some v := hv
      obtain rfl : (!b) = v := Option.some.inj hbv
      exact unanim_suppOK (s := s) hI hq hb
    · intro v hv id' b' h_call
      exact absurd (show (none : Option Bool) = some b' from h_call) (by simp)
  | mixed b hq h1 h0 hs =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    have hval : s.val = none := by
      by_contra hv
      obtain ⟨i, hi, hci⟩ := h1
      obtain ⟨j, hj, hcj⟩ := h0
      rcases hI.call_val i hi hv with h | h
      · rw [h] at hci; exact absurd hci (by simp)
      · rcases hI.call_val j hj hv with h' | h'
        · rw [h'] at hcj; exact absurd hcj (by simp)
        · rw [h] at hci; rw [h'] at hcj; rw [hci] at hcj
          exact absurd (Option.some.inj hcj) (by simp)
    refine ⟨hI.F_le, fun h => absurd hval h, fun id' _ h => absurd hval h,
      ?_, ?_, ?_, ?_⟩
    · intro hbind
      exact absurd (show (some b : Option Bool) = none from hbind) (by simp)
    · intro v hv
      have hbv : (some b : Option Bool) = some v := hv
      obtain rfl : b = v := Option.some.inj hbv
      exact mixed_suppOK (s := s) hI hs
    · intro v hv
      exact absurd (show s.val = some v from hv) (by rw [hval]; simp)
    · intro v hv id' b' h_call
      exact absurd (show (none : Option Bool) = some b' from h_call) (by simp)
  | coinFlip hcall hbind =>
    rw [PMF.mem_support_map_iff] at hs'
    obtain ⟨o, -, rfl⟩ := hs'
    exact ⟨hI.F_le, hI.bind_val, hI.call_val, hI.call_prov, hI.bind_supp,
      hI.val_supp, hI.bound_prov⟩
  | adopt id h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨hI.F_le, hI.bind_val, ?_, ?_, hI.bind_supp, hI.val_supp, ?_⟩
    · intro id' h_hon hv
      by_cases h_eq : id' = id
      · subst h_eq
        simp only [Function.update_self]
        exact Or.inr (hI.bind_val hv)
      · simp only [Function.update_of_ne h_eq]
        exact hI.call_val id' h_hon hv
    · intro hb id' b' h_call
      replace h_call : Function.update s.call id s.bind id' = some b' := h_call
      by_cases h_eq : id' = id
      · subst h_eq
        rw [Function.update_self, hb] at h_call
        exact absurd h_call (by simp)
      · rw [Function.update_of_ne h_eq] at h_call
        exact hI.call_prov hb id' b' h_call
    · intro v hv id' b' h_call
      replace h_call : Function.update s.call id s.bind id' = some b' := h_call
      by_cases h_eq : id' = id
      · subst h_eq
        rw [Function.update_self, show s.bind = some v from hv] at h_call
        exact Or.inr (Or.inl (Option.some.inj h_call).symm)
      · rw [Function.update_of_ne h_eq] at h_call
        exact hI.bound_prov v hv id' b' h_call
  | repropose id b h₁ h₂ hd h₃ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨hI.F_le, hI.bind_val, ?_, ?_, hI.bind_supp, hI.val_supp, ?_⟩
    · intro id' h_hon hv
      by_cases h_eq : id' = id
      · subst h_eq
        simp only [Function.update_self]
        rcases h₃ with ⟨hvn, -⟩ | h
        · exact absurd hvn hv
        · exact Or.inr h.symm
      · simp only [Function.update_of_ne h_eq]
        exact hI.call_val id' h_hon hv
    · intro hb id' b' h_call
      replace h_call : Function.update s.call id (some b) id' = some b' := h_call
      by_cases h_eq : id' = id
      · subst h_eq
        rw [Function.update_self] at h_call
        obtain rfl := Option.some.inj h_call
        rcases h₃ with ⟨hvn, hin | hbind⟩ | hval
        · exact Or.inl hin
        · exact absurd hbind (by rw [hb]; simp)
        · have hbv := hI.bind_val (by rw [hval]; simp)
          rw [hb, hval] at hbv
          exact absurd hbv (by simp)
      · rw [Function.update_of_ne h_eq] at h_call
        exact hI.call_prov hb id' b' h_call
    · intro v hv id' b' h_call
      replace h_call : Function.update s.call id (some b) id' = some b' := h_call
      by_cases h_eq : id' = id
      · subst h_eq
        rw [Function.update_self] at h_call
        obtain rfl := Option.some.inj h_call
        rcases h₃ with ⟨hvn, hin | hbind⟩ | hval
        · exact Or.inl hin
        · rw [show s.bind = some v from hv] at hbind
          exact Or.inr (Or.inl (Option.some.inj hbind).symm)
        · have hbv := hI.bind_val (by rw [hval]; simp)
          rw [show s.bind = some v from hv, hval] at hbv
          exact Or.inr (Or.inl (Option.some.inj hbv).symm)
      · rw [Function.update_of_ne h_eq] at h_call
        exact hI.bound_prov v hv id' b' h_call
  | callByzFill id b hF h =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨hI.F_le, hI.bind_val, ?_, ?_, hI.bind_supp, hI.val_supp, ?_⟩
    · intro id' h_hon hv
      by_cases h_eq : id' = id
      · subst h_eq
        exact absurd hF h_hon
      · simp only [Function.update_of_ne h_eq]
        exact hI.call_val id' h_hon hv
    · intro hb id' b' h_call
      by_cases h_eq : id' = id
      · subst h_eq
        exact Or.inr hF
      · replace h_call : Function.update s.call id (some b) id' = some b' := h_call
        rw [Function.update_of_ne h_eq] at h_call
        exact hI.call_prov hb id' b' h_call
    · intro v hv id' b' h_call
      by_cases h_eq : id' = id
      · subst h_eq
        exact Or.inr (Or.inr hF)
      · replace h_call : Function.update s.call id (some b) id' = some b' := h_call
        rw [Function.update_of_ne h_eq] at h_call
        exact hI.bound_prov v hv id' b' h_call
  | ret id b h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    exact ⟨hI.F_le, hI.bind_val, hI.call_val, hI.call_prov, hI.bind_supp,
      hI.val_supp, hI.bound_prov⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨corrupt_card_le s id hI.F_le, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [corrupt_bind, corrupt_val]; exact hI.bind_val
    · intro id' h_hon hv
      rw [corrupt_call, corrupt_val]
      rw [corrupt_val] at hv
      exact hI.call_val id' (fun hm => h_hon (corrupt_F_subset s id hm)) hv
    · rw [corrupt_bind]
      intro hb id' b' h_call
      rw [corrupt_call] at h_call
      rw [corrupt_input]
      exact (hI.call_prov hb id' b' h_call).imp (fun hh => hh)
        (fun hh => corrupt_F_subset s id hh)
    · intro v hv
      rw [corrupt_bind] at hv
      exact (hI.bind_supp v hv).mono
        (fun i hh => by rw [corrupt_input]; exact hh) (corrupt_F_subset s id)
    · intro v hv
      rw [corrupt_val] at hv
      exact (hI.val_supp v hv).mono
        (fun i hh => by rw [corrupt_input]; exact hh) (corrupt_F_subset s id)
    · intro v hv id' b' h_call
      rw [corrupt_bind] at hv
      rw [corrupt_call] at h_call
      rw [corrupt_input]
      rcases hI.bound_prov v hv id' b' h_call with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr (corrupt_F_subset s id hh))


/-- **Write-once decision.** Under the invariant, `val = some b` is preserved
by every step (the unanimity rule can only rewrite `val` to itself). -/
theorem SpecInv.val_stable {s : SpecState P.n} {l : Lab P.n}
    {μ : PMF (SpecState P.n)} {s' : SpecState P.n} {b : Bool}
    (hI : SpecInv P s) (hv : s.val = some b)
    (hstep : SpecStep P s l μ) (hs' : s' ∈ μ.support) : s'.val = some b := by
  cases hstep with
  | callSet id b' h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | callLoop id b' =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | unanim b' hq hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    show some (!b') = some b
    rw [unanim_rewrites_val hI hv hq hb]
  | mixed b' hq h1 h0 hs =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | coinFlip hcall hbind =>
    rw [PMF.mem_support_map_iff] at hs'
    obtain ⟨o, _, rfl⟩ := hs'
    exact hv
  | adopt id h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | repropose id b' h₁ h₂ hd h₃ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | callByzFill id b' hF h =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | ret id b' h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    rw [corrupt_val]; exact hv

/-! ### The label-history-aware invariant (for Validity) -/

/-- The history-aware invariant: ghost-recorded inputs are attributed to
`callABA` events in the label history, and the corrupted set is exactly the
fold of D1-`corrupt` over the labels seen so far. Byzantine `call` fills
have no event — which is why attribution rides the ghost `input` (never
Byzantine-written), not `call`. -/
structure ValInv (P : Params) (pre : List (Lab P.n)) (s : SpecState P.n) : Prop where
  inv : SpecInv P s
  input_src : ∀ id b, s.input id = some b → Lab.callABA id b ∈ pre
  F_eq : s.F = failSetL P pre

theorem ValInv.initial (P : Params) : ValInv P [] (SpecState.initial P.n) where
  inv := SpecInv.initial P
  input_src := fun _ _ h => absurd h (by simp [SpecState.initial])
  F_eq := rfl

/-- **History-invariant preservation.** -/
theorem ValInv.step {pre : List (Lab P.n)} {s : SpecState P.n} {l : Lab P.n}
    {μ : PMF (SpecState P.n)} {s' : SpecState P.n}
    (hI : ValInv P pre s) (hstep : SpecStep P s l μ) (hs' : s' ∈ μ.support) :
    ValInv P (pre ++ [l]) s' := by
  have mono : ∀ {l' : Lab P.n}, l' ∈ pre → l' ∈ pre ++ [l] :=
    fun h => List.mem_append_left _ h
  have h_inv' := hI.inv.step hstep hs'
  cases hstep with
  | callSet id b h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨h_inv', ?_, ?_⟩
    · intro id' b' h_in
      replace h_in : Function.update s.input id (some b) id' = some b' := h_in
      by_cases h_eq : id' = id
      · subst h_eq
        rw [Function.update_self] at h_in
        obtain rfl := Option.some.inj h_in
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      · rw [Function.update_of_ne h_eq] at h_in
        exact mono (hI.input_src id' b' h_in)
    · change s.F = failSetL P (pre ++ [Lab.callABA id b])
      rw [failSetL_append]
      exact hI.F_eq
  | callLoop id b =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨h_inv', ?_, ?_⟩
    · intro id' b' h_in
      replace h_in : (if s.input id = none then Function.update s.input id (some b)
          else s.input) id' = some b' := h_in
      by_cases hcond : s.input id = none
      · rw [if_pos hcond] at h_in
        by_cases h_eq : id' = id
        · subst h_eq
          rw [Function.update_self] at h_in
          obtain rfl := Option.some.inj h_in
          exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
        · rw [Function.update_of_ne h_eq] at h_in
          exact mono (hI.input_src id' b' h_in)
      · rw [if_neg hcond] at h_in
        exact mono (hI.input_src id' b' h_in)
    · change s.F = failSetL P (pre ++ [Lab.callABA id b])
      rw [failSetL_append]
      exact hI.F_eq
  | unanim b hq hb =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨h_inv', fun id' b' h_in => mono (hI.input_src id' b' h_in), ?_⟩
    change s.F = failSetL P (pre ++ [Lab.tau])
    rw [failSetL_append]
    exact hI.F_eq
  | mixed b hq h1 h0 hs =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨h_inv', fun id' b' h_in => mono (hI.input_src id' b' h_in), ?_⟩
    change s.F = failSetL P (pre ++ [Lab.tau])
    rw [failSetL_append]
    exact hI.F_eq
  | coinFlip hcall hbind =>
    rw [PMF.mem_support_map_iff] at hs'
    obtain ⟨o, -, rfl⟩ := hs'
    refine ⟨h_inv', fun id' b' h_in => mono (hI.input_src id' b' h_in), ?_⟩
    change s.F = failSetL P (pre ++ [Lab.tau])
    rw [failSetL_append]
    exact hI.F_eq
  | adopt id h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨h_inv', fun id' b' h_in => mono (hI.input_src id' b' h_in), ?_⟩
    change s.F = failSetL P (pre ++ [Lab.tau])
    rw [failSetL_append]
    exact hI.F_eq
  | repropose id b h₁ h₂ hd h₃ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨h_inv', fun id' b' h_in => mono (hI.input_src id' b' h_in), ?_⟩
    change s.F = failSetL P (pre ++ [Lab.tau])
    rw [failSetL_append]
    exact hI.F_eq
  | callByzFill id b hF h =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨h_inv', fun id' b' h_in => mono (hI.input_src id' b' h_in), ?_⟩
    change s.F = failSetL P (pre ++ [Lab.tau])
    rw [failSetL_append]
    exact hI.F_eq
  | ret id b h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨h_inv', fun id' b' h_in => mono (hI.input_src id' b' h_in), ?_⟩
    change s.F = failSetL P (pre ++ [Lab.retABA id b])
    rw [failSetL_append]
    exact hI.F_eq
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨h_inv', ?_, ?_⟩
    · intro id' b' h_in
      rw [corrupt_input] at h_in
      exact mono (hI.input_src id' b' h_in)
    · rw [failSetL_append, corrupt_F, hI.F_eq]
      rfl


/-! ### The safety theorem -/

/-- Inverting a `retABA` event: the pre-state's decision value is the
returned bit. -/
private theorem retABA_inv {s : SpecState P.n} {id : Fin P.n} {b : Bool}
    {μ : PMF (SpecState P.n)} (hstep : SpecStep P s (.retABA id b) μ) :
    s.val = some b :=
  match hstep with
  | .ret _ _ _ h₁ _ => h₁

/-- Two decision values read along one genuine execution agree
(`k₁ ≤ k₂` case). -/
private theorem val_agree_le {e : AlterSeq (SpecState P.n) (Lab P.n)}
    (he : is_exec e (spec P)) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    {s₁ s₂ : SpecState P.n} {b b' : Bool}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hv₁ : s₁.val = some b) (hv₂ : s₂.val = some b') : b = b' := by
  have h_inv := is_exec_induction (sys := spec P) (SpecInv P) (SpecInv.initial P)
    (fun s l μ s' hI hstep hs' => hI.step hstep hs') he k₁ s₁ hst₁
  have h_stable := is_exec_stable (sys := spec P)
    (fun s => SpecInv P s ∧ s.val = some b)
    (fun s l μ s' ⟨hI, hv⟩ hstep hs' =>
      ⟨hI.step hstep hs', hI.val_stable hv hstep hs'⟩)
    he k₁ k₂ s₁ s₂ hk hst₁ hst₂ ⟨h_inv, hv₁⟩
  rw [h_stable.2] at hv₂
  exact Option.some.inj hv₂

/-- The budget pigeonhole: `f + 1` supporters minus at most `f`
ever-corrupted ids leave a never-corrupted recorded inputter. -/
theorem exists_neverCorrupted_supporter {t : Seq (Lab P.n)} {s : SpecState P.n}
    {v : Bool} {m : ℕ} (hsupp : SuppOK P s v) (hF : s.F = failSet P t m) :
    ∃ id, s.input id = some v ∧ NeverCorrupted P t id := by
  by_contra hc
  push_neg at hc
  have hall : ∀ id ∈ Finset.univ.filter
      (fun id => s.input id = some v ∨ id ∈ s.F), ∃ k, id ∈ failSet P t k := by
    intro id hid
    rcases (Finset.mem_filter.mp hid).2 with hin | hmem
    · have h1 := hc id hin
      unfold NeverCorrupted at h1
      push_neg at h1
      exact h1
    · exact ⟨m, hF ▸ hmem⟩
  obtain ⟨K, hK⟩ := exists_uniform_stage t _ hall
  have h1 := Finset.card_le_card
    (show Finset.univ.filter (fun id => s.input id = some v ∨ id ∈ s.F)
        ⊆ failSet P t K from fun id hid => hK id hid)
  have h2 := failSet_card_le t K
  have h3 := hsupp
  unfold SuppOK at h3
  omega

/-- **Safety of the ABA specification**: every trace in the support of every
achievable trace distribution of `ABA.spec` satisfies Validity (paper form,
ordered, with a never-corrupted witness) and Agreement. -/
theorem spec_safe (P : Params) :
    ∀ D ∈ achievableTraceDists (spec P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace t := by
  rintro D ⟨pe, h_init, h_D⟩ t h_ne
  rw [← h_D t] at h_ne
  constructor
  · -- Validity
    obtain ⟨e, labs, h_exec, h_map, h_t⟩ :=
      exists_exec_of_traceProb_ne_zero_ord pe h_init t h_ne
    rw [Seq.ofList_filter] at h_t
    -- generalise the external-label filter to an opaque Boolean predicate
    obtain ⟨p, hpfail, hpcall, h_t⟩ : ∃ p : Lab P.n → Bool,
        (∀ id : Fin P.n, p (.fail id) = true) ∧
        (∀ (id : Fin P.n) (b : Bool), p (.callABA id b) = true) ∧
        Seq.ofList (labs.filter p) = t :=
      ⟨_, fun id => by simp, fun id b => by simp, h_t⟩
    intro m id b h_ret
    -- trace position `m` pulls back to an execution event `j`
    rw [← h_t, Seq.ofList_get?] at h_ret
    obtain ⟨j, hj, hlen⟩ := filter_getElem?_pullback p labs m _ h_ret
    obtain ⟨s'', h_get⟩ : ∃ s'', e.trans.get? j = some (Lab.retABA id b, s'') := by
      have hk : (e.trans.get? j).map Prod.fst = labs[j]? := by
        rw [← Seq.map_get?, h_map, Seq.ofList_get?]
      rw [hj] at hk
      cases hg : e.trans.get? j with
      | none => rw [hg] at hk; exact absurd hk (by simp)
      | some q =>
        rw [hg] at hk
        simp only [Option.map_some, Option.some.injEq] at hk
        exact ⟨q.2, by rw [← hk]⟩
    obtain ⟨s, μ, h_state, h_step, -⟩ := h_exec.1 j _ _ h_get
    have h_val : s.val = some b := retABA_inv h_step
    have h_VI := is_exec_induction_labels (sys := spec P)
      (fun pre s => ValInv P pre s) (ValInv.initial P)
      (fun pre s l μ s' hI hstep hs' => hI.step hstep hs') h_exec j s h_state
    rw [AlterSeq.labelsUpTo_eq_take h_map j] at h_VI
    -- the trace-prefix bridge: `s.F` is the trace-level fold at position `m`
    have h_take : (labs.take j).filter p = (labs.filter p).take m :=
      take_filter_eq_take p labs hlen
    have h_bridge : s.F = failSet P t m := by
      rw [h_VI.F_eq, ← failSetL_filter hpfail (labs.take j), h_take,
        ← failSet_ofList, h_t]
    -- the pigeonhole witness, pushed back to a preceding trace position
    obtain ⟨id', h_in, h_nc⟩ :=
      exists_neverCorrupted_supporter (h_VI.inv.val_supp b h_val) h_bridge
    have h_memf : Lab.callABA id' b ∈ (labs.filter p).take m := by
      rw [← h_take]
      exact List.mem_filter.mpr ⟨h_VI.input_src id' b h_in, hpcall id' b⟩
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp h_memf
    have hk_lt : k < m := by
      have h1 := (List.getElem?_eq_some_iff.mp hk).1
      have h2 : ((labs.filter p).take m).length ≤ m := by
        rw [List.length_take]; omega
      omega
    rw [List.getElem?_take_of_lt hk_lt] at hk
    refine ⟨k, hk_lt, id', ?_, h_nc⟩
    rw [← h_t, Seq.ofList_get?]
    exact hk
  · -- Agreement
    obtain ⟨e, h_exec, h_char⟩ :=
      exists_exec_of_traceProb_ne_zero pe h_init t h_ne
    intro id b id' b' h₁ h₂
    obtain ⟨-, k₁, s₁', hg₁⟩ := (h_char _).mp h₁
    obtain ⟨-, k₂, s₂', hg₂⟩ := (h_char _).mp h₂
    obtain ⟨s₁, μ₁, hst₁, hstep₁, -⟩ := h_exec.1 k₁ _ _ hg₁
    obtain ⟨s₂, μ₂, hst₂, hstep₂, -⟩ := h_exec.1 k₂ _ _ hg₂
    have hv₁ : s₁.val = some b := retABA_inv hstep₁
    have hv₂ : s₂.val = some b' := retABA_inv hstep₂
    rcases le_total k₁ k₂ with h | h
    · exact val_agree_le h_exec h hst₁ hst₂ hv₁ hv₂
    · exact (val_agree_le h_exec h hst₂ hst₁ hv₂ hv₁).symm


end ABA
end PLTS
