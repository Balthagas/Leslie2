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
(`ABA.spec_safe`).

`AgreementTrace` requires *any* two returns (honest or not) to agree —
stronger than the blueprint's correct-process phrasing, since `ABA.spec`'s
return rule does not inspect `F`. `ValidityTrace` is the paper-form statement
(D13): every return of `b` is *preceded* (positionally) by a `callABA _ b`
event whose caller is never corrupted anywhere along the trace
(`NeverCorrupted`, via the trace-level corruption fold `failSet`) —
returner-unconditional, hence stronger than the papers on the returns axis and
faithful on the witness axis: the witnessing caller must be never corrupted,
not merely a member of some support set that a later `fail` could taint.

The proof is invariant reasoning along genuine executions (via
`TraceSupport`), on two invariants:

* `SpecInv` — the state invariant, in two clauses: the corrupted set respects
  the budget (`F_le`), and the decision value carries `f + 1` F-blind
  supporters (`val_supp`). The second clause is `SpecStep.decide`'s own guard
  at the one rule that writes `val`, and every other rule carries it by
  `SuppOK.mono`, the ghost record and the corrupted set being monotone.
* `ValInv` — the label-history-aware invariant: ghost-recorded inputs are
  attributed to `callABA` events in the history (`input_src`), and the
  corrupted set is exactly the fold of D1-`corrupt` over the labels seen so
  far (`F_eq`). The `callABA` rules record the bit their own label carries,
  which is what restores `input_src` under the D16 overwrite.

Agreement rests on `SpecInv.val_stable`: `SpecStep.decide` is the sole writer
of `val` and fires only from `val = ⊥`, so the decision value never changes
once written and two returns read the same one.

Validity is a budget pigeonhole at the return. `retABA_inv` reads the returned
bit off the pre-state's decision value and `SpecInv.val_supp` yields `f + 1`
supporters of that bit. Every supporter is either ghost-recorded — hence a
genuine preceding `callABA`, by `ValInv.input_src` — or ever-corrupted, and at
most `f` ids are ever corrupted (`failSet` never exceeds the budget), so some
recorded supporter is never corrupted (`exists_neverCorrupted_supporter`).
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

/-! ### The state invariant -/

/-- The state invariant of `ABA.spec`: the corrupted set respects the budget,
and the decision value carries `f + 1` F-blind supporters (D13). -/
structure SpecInv (P : Params) (s : SpecState P.n) : Prop where
  /-- The corrupted set stays inside the budget. -/
  F_le : s.F.card ≤ P.f
  /-- The decision value has `f + 1` supporters. -/
  val_supp : ∀ v, s.val = some v → SuppOK P s v

theorem SpecInv.initial (P : Params) : SpecInv P (SpecState.initial P.n) where
  F_le := by simp [SpecState.initial]
  val_supp := fun _ h => absurd h (by simp [SpecState.initial])

/-! Field stability of `corrupt`. -/

section Corrupt

variable (s : SpecState P.n) (id : Fin P.n)

@[simp] theorem corrupt_input : (s.corrupt P id).input = s.input := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_ret : (s.corrupt P id).ret = s.ret := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_val : (s.corrupt P id).val = s.val := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_mode : (s.corrupt P id).mode = s.mode := by
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

/-- **Invariant preservation.** `SpecInv` is preserved by every step. -/
theorem SpecInv.step {s : SpecState P.n} {l : Lab P.n} {μ : PMF (SpecState P.n)}
    {s' : SpecState P.n} (hI : SpecInv P s)
    (hstep : SpecStep P s l μ) (hs' : s' ∈ μ.support) : SpecInv P s' := by
  cases hstep with
  | callSet id b hv =>
    -- `val` stays `⊥`, so `val_supp` has nothing to prove
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    exact ⟨hI.F_le, fun v hvv => absurd (show s.val = some v from hvv) (by rw [hv]; simp)⟩
  | callLoop id b =>
    -- the ghost record only grows, so `SuppOK.mono` carries the support
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
    exact ⟨hI.F_le, fun v hv =>
      (hI.val_supp v hv).mono (fun i => hnew i v) (Finset.Subset.refl _)⟩
  | coinFlip hm hv hq =>
    -- every branch writes `mode` alone
    rw [PMF.mem_support_map_iff] at hs'
    obtain ⟨o, -, rfl⟩ := hs'
    cases o <;> exact ⟨hI.F_le, hI.val_supp⟩
  | decide b hv hs hm hq =>
    -- the guard `hs` is the conclusion
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨hI.F_le, fun v hvv => ?_⟩
    obtain rfl : b = v := Option.some.inj (show (some b : Option Bool) = some v from hvv)
    exact hs
  | ret id b h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    exact ⟨hI.F_le, hI.val_supp⟩
  | fail id =>
    -- `F` grows inside the budget, and `SuppOK` is monotone in it
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨corrupt_card_le s id hI.F_le, fun v hv => ?_⟩
    rw [corrupt_val] at hv
    exact (hI.val_supp v hv).mono
      (fun i hh => by rw [corrupt_input]; exact hh) (corrupt_F_subset s id)

/-- **Write-once decision.** `SpecStep.decide` is the sole writer of `val` and
fires only from `val = ⊥`, so `val = some b` is preserved by every step. -/
theorem SpecInv.val_stable {s : SpecState P.n} {l : Lab P.n}
    {μ : PMF (SpecState P.n)} {s' : SpecState P.n} {b : Bool}
    (hv : s.val = some b) (hstep : SpecStep P s l μ) (hs' : s' ∈ μ.support) :
    s'.val = some b := by
  cases hstep with
  | callSet id b' hv' =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | callLoop id b' =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | coinFlip hm hv' hq =>
    rw [PMF.mem_support_map_iff] at hs'
    obtain ⟨o, -, rfl⟩ := hs'
    cases o <;> exact hv
  | decide b' hv' hs hm hq =>
    exact absurd hv (by rw [hv']; simp)
  | ret id b' h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    rw [corrupt_val]; exact hv

/-! ### The label-history-aware invariant (for Validity) -/

/-- The history-aware invariant: ghost-recorded inputs are attributed to
`callABA` events in the label history, and the corrupted set is exactly the
fold of D1-`corrupt` over the labels seen so far. -/
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
  | callSet id b hv =>
    -- the overwritten bit is the label's own bit
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
  | coinFlip hm hv hq =>
    rw [PMF.mem_support_map_iff] at hs'
    obtain ⟨o, -, rfl⟩ := hs'
    have hFeq : s.F = failSetL P (pre ++ [Lab.tau]) := by
      rw [failSetL_append]; exact hI.F_eq
    cases o <;>
      exact ⟨h_inv', fun id' b' h_in => mono (hI.input_src id' b' h_in), hFeq⟩
  | decide b hv hs hm hq =>
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
  have h_stable := is_exec_stable (sys := spec P) (fun s => s.val = some b)
    (fun s l μ s' hv hstep hs' => SpecInv.val_stable hv hstep hs')
    he k₁ k₂ s₁ s₂ hk hst₁ hst₂ hv₁
  rw [h_stable] at hv₂
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
