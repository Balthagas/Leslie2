/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2Protocols.ABA.Spec
import Leslie2Protocols.Framework.TraceSupport

/-!
# Safety of the ABA specification

Validity and Agreement, stated as predicates on traces and proven for every
trace in the support of every achievable trace distribution of `ABA.spec`
(`ABA.spec_safe`). This validates the D3 repair: Agreement is *false* for the
blueprint's unrepaired Transition System 1.

The proof is invariant reasoning along genuine executions (via
`TraceSupport`):

* `SpecInv` — the state invariant: `|F| ≤ f`, and once `val = some v` the
  bound value equals `val` and every honest pending input is `⊥` or `val`.
* `SpecInv.val_stable` — the decision value is write-once: the unanimity rule
  can only rewrite `val` to itself (the quorum argument, using `f < n − f`).
* `ValInv` — the label-history-aware invariant attributing pending inputs and
  the decision value to `callABA` events in the history.

`AgreementTrace` requires *any* two returns (honest or not) to agree, and
`ValidityTrace` attributes the returned bit to some `callABA` event — both
slightly stronger than the blueprint's correct-process phrasing, since
`ABA.spec`'s return rule does not inspect `F`. Validity is membership-based
(the witnessing call necessarily precedes the return in the underlying
execution, but the trace-level statement does not order them).
-/

open Stream'

namespace PLTS
namespace ABA

variable {P : Params}

/-! ### The trace-level safety predicates -/

/-- **Validity** (trace form): every returned bit was some process's input. -/
def ValidityTrace {n : ℕ} (t : Seq (Lab n)) : Prop :=
  ∀ id b, Lab.retABA id b ∈ t → ∃ id', Lab.callABA id' b ∈ t

/-- **Agreement** (trace form): any two returns carry the same bit. -/
def AgreementTrace {n : ℕ} (t : Seq (Lab n)) : Prop :=
  ∀ id b id' b', Lab.retABA id b ∈ t → Lab.retABA id' b' ∈ t → b = b'

/-! ### The state invariant -/

/-- The core state invariant of `ABA.spec`: the corrupted set respects the
budget, and once the decision value is fixed it agrees with the bound value
and dominates every honest pending input. -/
structure SpecInv (P : Params) (s : SpecState P.n) : Prop where
  F_le : s.F.card ≤ P.f
  bind_val : s.val ≠ none → s.bind = s.val
  call_val : ∀ id, id ∉ s.F → s.val ≠ none →
    s.call id = none ∨ s.call id = s.val

theorem SpecInv.initial (P : Params) : SpecInv P (SpecState.initial P.n) where
  F_le := by simp [SpecState.initial]
  bind_val := fun h => absurd rfl h
  call_val := fun _ _ h => absurd rfl h

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
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hval : s.val = none := by
      by_contra hv
      have := hI.bind_val hv
      rw [h₂] at this
      exact hv this.symm
    exact ⟨hI.F_le, fun h => absurd hval h, fun id' _ h => absurd hval h⟩
  | callLoop id b =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hI
  | unanim b hq hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨hI.F_le, fun _ => rfl, fun id' _ _ => Or.inl rfl⟩
  | mixed b hq h1 h0 =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
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
    exact ⟨hI.F_le, fun h => absurd hval h, fun id' _ h => absurd hval h⟩
  | coinFlip hcall hbind =>
    rw [PMF.mem_support_map_iff] at hs'
    obtain ⟨o, _, rfl⟩ := hs'
    exact ⟨hI.F_le, hI.bind_val, hI.call_val⟩
  | adopt id h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_le, hI.bind_val, fun id' h_hon hv => ?_⟩
    by_cases h_eq : id' = id
    · subst h_eq
      simp only [Function.update_self]
      exact Or.inr (hI.bind_val hv)
    · simp only [Function.update_of_ne h_eq]
      exact hI.call_val id' h_hon hv
  | repropose id b h₁ h₂ h₃ =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_le, hI.bind_val, fun id' h_hon hv => ?_⟩
    by_cases h_eq : id' = id
    · subst h_eq
      simp only [Function.update_self]
      rcases h₃ with h | h
      · exact absurd h hv
      · exact Or.inr h.symm
    · simp only [Function.update_of_ne h_eq]
      exact hI.call_val id' h_hon hv
  | ret id b h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨hI.F_le, hI.bind_val, hI.call_val⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨corrupt_card_le s id hI.F_le, ?_, ?_⟩
    · rw [corrupt_bind, corrupt_val]; exact hI.bind_val
    · intro id' h_hon hv
      rw [corrupt_call, corrupt_val]
      rw [corrupt_val] at hv
      exact hI.call_val id' (fun h => h_hon (corrupt_F_subset s id h)) hv

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
  | mixed b' hq h1 h0 =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | coinFlip hcall hbind =>
    rw [PMF.mem_support_map_iff] at hs'
    obtain ⟨o, _, rfl⟩ := hs'
    exact hv
  | adopt id h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | repropose id b' h₁ h₂ h₃ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | ret id b' h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    rw [corrupt_val]; exact hv

/-! ### The label-history-aware invariant (for Validity) -/

/-- The history-aware invariant: pending inputs (while unbound) and the
decision value are attributed to `callABA` events in the label history. -/
structure ValInv (P : Params) (pre : List (Lab P.n)) (s : SpecState P.n) : Prop where
  inv : SpecInv P s
  coin_bot : s.bind = none → s.coin = .bot
  call_src : s.bind = none → ∀ id b, s.call id = some b → Lab.callABA id b ∈ pre
  val_src : ∀ b, s.val = some b →
    (∃ id, Lab.callABA id b ∈ pre) ∨
    ((∃ id, Lab.callABA id true ∈ pre) ∧ (∃ id, Lab.callABA id false ∈ pre))
  mix_src : s.bind ≠ none → s.val = none →
    (∃ id, Lab.callABA id true ∈ pre) ∧ (∃ id, Lab.callABA id false ∈ pre)

theorem ValInv.initial (P : Params) : ValInv P [] (SpecState.initial P.n) where
  inv := SpecInv.initial P
  coin_bot := fun _ => rfl
  call_src := fun _ _ _ h => absurd h (by simp [SpecState.initial])
  val_src := fun _ h => absurd h (by simp [SpecState.initial])
  mix_src := fun h _ => absurd rfl h

/-- **History-invariant preservation.** -/
theorem ValInv.step {pre : List (Lab P.n)} {s : SpecState P.n} {l : Lab P.n}
    {μ : PMF (SpecState P.n)} {s' : SpecState P.n}
    (hI : ValInv P pre s) (hstep : SpecStep P s l μ) (hs' : s' ∈ μ.support) :
    ValInv P (pre ++ [l]) s' := by
  have mono : ∀ {l' : Lab P.n}, l' ∈ pre → l' ∈ pre ++ [l] :=
    fun h => List.mem_append_left _ h
  have mono₁ : ∀ {b : Bool}, (∃ id, Lab.callABA id b ∈ pre) →
      ∃ id, Lab.callABA id b ∈ pre ++ [l] :=
    fun ⟨id, h⟩ => ⟨id, mono h⟩
  have h_inv' := hI.inv.step hstep hs'
  cases hstep with
  | callSet id b h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have h_self : Lab.callABA id b ∈ pre ++ [Lab.callABA id b] :=
      List.mem_append_right _ (List.mem_singleton.mpr rfl)
    refine ⟨h_inv', hI.coin_bot, ?_, ?_, ?_⟩
    · intro hb id' b' h_call
      replace h_call : Function.update s.call id (some b) id' = some b' := h_call
      by_cases h_eq : id' = id
      · subst h_eq
        rw [Function.update_self] at h_call
        obtain rfl := Option.some.inj h_call
        exact h_self
      · rw [Function.update_of_ne h_eq] at h_call
        exact mono (hI.call_src h₂ id' b' h_call)
    · intro b' hb'
      rcases hI.val_src b' hb' with h | ⟨ht, hf⟩
      · exact Or.inl (mono₁ h)
      · exact Or.inr ⟨mono₁ ht, mono₁ hf⟩
    · intro hbind hval
      obtain ⟨ht, hf⟩ := hI.mix_src hbind hval
      exact ⟨mono₁ ht, mono₁ hf⟩
  | callLoop id b =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨h_inv', hI.coin_bot, ?_, ?_, ?_⟩
    · intro hb id' b' h_call
      exact mono (hI.call_src hb id' b' h_call)
    · intro b' hb'
      rcases hI.val_src b' hb' with h | ⟨ht, hf⟩
      · exact Or.inl (mono₁ h)
      · exact Or.inr ⟨mono₁ ht, mono₁ hf⟩
    · intro hbind hval
      obtain ⟨ht, hf⟩ := hI.mix_src hbind hval
      exact ⟨mono₁ ht, mono₁ hf⟩
  | unanim b hq hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨h_inv', fun h => absurd h (by simp), fun h => absurd h (by simp),
      ?_, fun _ h => absurd h (by simp)⟩
    -- attribute the freshly written decision value `!b`
    intro b' hb'
    have hb'_eq : b' = !b := by
      have h2 : some (!b) = some b' := hb'
      exact (Option.some.inj h2).symm
    subst hb'_eq
    -- a quorum member witnesses `!b`
    obtain ⟨id, h_hon, h_ne⟩ := exists_honest_call hq hI.inv.F_le
    obtain ⟨c, h_call⟩ : ∃ c, s.call id = some c := by
      cases h : s.call id with
      | none => exact absurd h h_ne
      | some c => exact ⟨c, rfl⟩
    have h_c : c = !b := by
      have := hb id h_hon
      rw [h_call] at this
      have h_ne_b : c ≠ b := fun h => this (h ▸ rfl)
      cases c <;> cases b <;> simp_all
    subst h_c
    by_cases hbind : s.bind = none
    · -- while unbound, the witnessing input is attributed directly
      exact Or.inl ⟨id, mono (hI.call_src hbind id _ h_call)⟩
    · by_cases hval : s.val = none
      · -- rule-4 provenance: both bits were input
        obtain ⟨ht, hf⟩ := hI.mix_src hbind hval
        exact Or.inr ⟨mono₁ ht, mono₁ hf⟩
      · -- val was already fixed: the write is idempotent, reuse `val_src`
        obtain ⟨v, hv⟩ : ∃ v, s.val = some v := by
          cases h : s.val with
          | none => exact absurd h hval
          | some v => exact ⟨v, rfl⟩
        have h_veq : (!b) = v := by
          rcases hI.inv.call_val id h_hon (by rw [hv]; simp) with h | h
          · exact absurd h h_ne
          · rw [h_call, hv] at h
            exact Option.some.inj h
        rw [h_veq]
        rcases hI.val_src v hv with h | ⟨ht, hf⟩
        · exact Or.inl (mono₁ h)
        · exact Or.inr ⟨mono₁ ht, mono₁ hf⟩
  | mixed b hq h1 h0 =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hval : s.val = none := by
      by_contra hv
      obtain ⟨i, hi, hci⟩ := h1
      obtain ⟨j, hj, hcj⟩ := h0
      rcases hI.inv.call_val i hi hv with h | h
      · rw [h] at hci; exact absurd hci (by simp)
      · rcases hI.inv.call_val j hj hv with h' | h'
        · rw [h'] at hcj; exact absurd hcj (by simp)
        · rw [h] at hci; rw [h'] at hcj; rw [hci] at hcj
          exact absurd (Option.some.inj hcj) (by simp)
    have h_both : (∃ id, Lab.callABA id true ∈ pre) ∧
        (∃ id, Lab.callABA id false ∈ pre) := by
      by_cases hbind : s.bind = none
      · obtain ⟨i, hi, hci⟩ := h1
        obtain ⟨j, hj, hcj⟩ := h0
        exact ⟨⟨i, hI.call_src hbind i true hci⟩, ⟨j, hI.call_src hbind j false hcj⟩⟩
      · exact hI.mix_src hbind hval
    refine ⟨h_inv', fun h => absurd h (by simp), fun h => absurd h (by simp),
      ?_, ?_⟩
    · intro b' hb'
      exact absurd (hval ▸ hb') (by simp)
    · intro _ _
      exact ⟨mono₁ h_both.1, mono₁ h_both.2⟩
  | coinFlip hcall hbind =>
    rw [PMF.mem_support_map_iff] at hs'
    obtain ⟨o, _, rfl⟩ := hs'
    refine ⟨h_inv', fun h => absurd h hbind, fun h => absurd h hbind, ?_, ?_⟩
    · intro b' hb'
      rcases hI.val_src b' hb' with h | ⟨ht, hf⟩
      · exact Or.inl (mono₁ h)
      · exact Or.inr ⟨mono₁ ht, mono₁ hf⟩
    · intro _ hval
      obtain ⟨ht, hf⟩ := hI.mix_src hbind hval
      exact ⟨mono₁ ht, mono₁ hf⟩
  | adopt id h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨h_inv', hI.coin_bot, ?_, ?_, ?_⟩
    · intro hb id' b' h_call
      replace h_call : Function.update s.call id s.bind id' = some b' := h_call
      by_cases h_eq : id' = id
      · subst h_eq
        rw [Function.update_self, hb] at h_call
        exact absurd h_call (by simp)
      · rw [Function.update_of_ne h_eq] at h_call
        exact mono (hI.call_src hb id' b' h_call)
    · intro b' hb'
      rcases hI.val_src b' hb' with h | ⟨ht, hf⟩
      · exact Or.inl (mono₁ h)
      · exact Or.inr ⟨mono₁ ht, mono₁ hf⟩
    · intro hbind hval
      obtain ⟨ht, hf⟩ := hI.mix_src hbind hval
      exact ⟨mono₁ ht, mono₁ hf⟩
  | repropose id b h₁ h₂ h₃ =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hbind : s.bind ≠ none := by
      intro h0
      refine h₂ ?_
      rw [h0, hI.coin_bot h0]
      trivial
    refine ⟨h_inv', hI.coin_bot, fun hb => absurd hb hbind, ?_, ?_⟩
    · intro b' hb'
      rcases hI.val_src b' hb' with h | ⟨ht, hf⟩
      · exact Or.inl (mono₁ h)
      · exact Or.inr ⟨mono₁ ht, mono₁ hf⟩
    · intro _ hval
      obtain ⟨ht, hf⟩ := hI.mix_src hbind hval
      exact ⟨mono₁ ht, mono₁ hf⟩
  | ret id b h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨h_inv', hI.coin_bot, ?_, ?_, ?_⟩
    · intro hb id' b' h_call
      exact mono (hI.call_src hb id' b' h_call)
    · intro b' hb'
      rcases hI.val_src b' hb' with h | ⟨ht, hf⟩
      · exact Or.inl (mono₁ h)
      · exact Or.inr ⟨mono₁ ht, mono₁ hf⟩
    · intro hbind hval
      obtain ⟨ht, hf⟩ := hI.mix_src hbind hval
      exact ⟨mono₁ ht, mono₁ hf⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨h_inv', ?_, ?_, ?_, ?_⟩
    · rw [corrupt_bind, corrupt_coin]; exact hI.coin_bot
    · rw [corrupt_bind, corrupt_call]
      intro hb id' b' h_call
      exact mono (hI.call_src hb id' b' h_call)
    · rw [corrupt_val]
      intro b' hb'
      rcases hI.val_src b' hb' with h | ⟨ht, hf⟩
      · exact Or.inl (mono₁ h)
      · exact Or.inr ⟨mono₁ ht, mono₁ hf⟩
    · rw [corrupt_bind, corrupt_val]
      intro hbind hval
      obtain ⟨ht, hf⟩ := hI.mix_src hbind hval
      exact ⟨mono₁ ht, mono₁ hf⟩

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

/-- **Safety of the ABA specification**: every trace in the support of every
achievable trace distribution of `ABA.spec` satisfies Validity and
Agreement. -/
theorem spec_safe (P : Params) :
    ∀ D ∈ achievableTraceDists (spec P), ∀ t, D t ≠ 0 →
      ValidityTrace t ∧ AgreementTrace t := by
  rintro D ⟨pe, h_init, h_D⟩ t h_ne
  rw [← h_D t] at h_ne
  obtain ⟨e, h_exec, h_char⟩ :=
    exists_exec_of_traceProb_ne_zero pe h_init t h_ne
  constructor
  · -- Validity
    intro id b h_ret
    obtain ⟨-, k, s', h_get⟩ := (h_char _).mp h_ret
    obtain ⟨s, μ, h_state, h_step, -⟩ := h_exec.1 k _ s' h_get
    have h_val : s.val = some b := retABA_inv h_step
    have h_VI := is_exec_induction_labels (sys := spec P)
      (fun pre s => ValInv P pre s) (ValInv.initial P)
      (fun pre s l μ s' hI hstep hs' => hI.step hstep hs') h_exec k s h_state
    obtain ⟨id', h_mem⟩ : ∃ id', Lab.callABA id' b ∈ e.labelsUpTo k := by
      rcases h_VI.val_src b h_val with ⟨id', h⟩ | ⟨⟨i_t, h_t⟩, ⟨i_f, h_f⟩⟩
      · exact ⟨id', h⟩
      · cases b
        · exact ⟨i_f, h_f⟩
        · exact ⟨i_t, h_t⟩
    obtain ⟨k', -, s'', h_get'⟩ := AlterSeq.mem_labelsUpTo h_mem
    exact ⟨id', (h_char _).mpr ⟨by simp, k', s'', h_get'⟩⟩
  · -- Agreement
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
