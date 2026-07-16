/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Mathlib.Tactic.Ring
import Mathlib.Data.List.Basic
import Mathlib.Data.Seq.Defs
import Mathlib.Data.Seq.Basic

/-!
# `Stream'.Seq` helpers

Pure helper lemmas and definitions about possibly-infinite sequences
(`Stream'.Seq`) that are independent of the PLTS development: facts about
`append`, a noncomputable `filter`, and basic `toList`/splitting lemmas.
-/

open Stream'

namespace Stream'.Seq

variable {α : Type*}

/-- For `n` the *exact* length of `s` (i.e. `s.TerminatedAt n` and `s` is not
terminated at any smaller index), positions in `s.append s'` past `n` reduce
to positions in `s'`: `(s.append s').get? (n + k) = s'.get? k`. -/
theorem get?_append_after_length {s s' : Seq α} {n : ℕ}
    (h_min : ∀ k < n, ¬ s.TerminatedAt k)
    (h_done : s.TerminatedAt n) (k : ℕ) :
    (s.append s').get? (n + k) = s'.get? k := by
  induction n generalizing s with
  | zero =>
    rw [terminatedAt_zero_iff] at h_done
    subst h_done
    rw [nil_append, Nat.zero_add]
  | succ j ih =>
    have h_not_term_0 : ¬ s.TerminatedAt 0 := h_min 0 (Nat.zero_lt_succ _)
    cases s with
    | nil => exact absurd terminatedAt_nil h_not_term_0
    | cons a t =>
      rw [cons_append, show j + 1 + k = (j + k) + 1 from by ring, get?_cons_succ]
      apply ih
      · intro k' hk'
        have h_succ_lt : k' + 1 < j + 1 := by omega
        have h_not := h_min (k' + 1) h_succ_lt
        rwa [cons_terminatedAt_succ_iff] at h_not
      · rwa [cons_terminatedAt_succ_iff] at h_done

/-- Specialization: `(s.append s').get? (Nat.find h + k) = s'.get? k`. -/
theorem get?_append_find {s : Seq α} (h : s.Terminates) (s' : Seq α) (k : ℕ) :
    (s.append s').get? (Nat.find h + k) = s'.get? k :=
  get?_append_after_length (fun _ hk => Nat.find_min h hk) (Nat.find_spec h) k

/-- Before `s` terminates at position `k`, append's `get?` agrees with `s`'s. -/
theorem get?_append_before_length {s s' : Seq α} {k : ℕ}
    (h_not_term : ¬ s.TerminatedAt k) :
    (s.append s').get? k = s.get? k := by
  induction k generalizing s with
  | zero =>
    cases s with
    | nil => exact absurd terminatedAt_nil h_not_term
    | cons a t => rw [cons_append]; rfl
  | succ k' ih =>
    cases s with
    | nil => exact absurd terminatedAt_nil h_not_term
    | cons a t =>
      rw [cons_append, get?_cons_succ, get?_cons_succ]
      exact ih (by rwa [← cons_terminatedAt_succ_iff (x := a)])

/-- `(s.append s').TerminatedAt (Nat.find h + n)` when `s'.TerminatedAt n`. -/
theorem terminatedAt_append_find {s : Seq α} (h : s.Terminates) {s' : Seq α}
    {n : ℕ} (h_s' : s'.TerminatedAt n) :
    (s.append s').TerminatedAt (Nat.find h + n) := by
  change (s.append s').get? _ = none
  rw [get?_append_find h s' n]; exact h_s'

/-- `Terminates` transfers from a cons to its tail. -/
theorem terminates_tail_of_cons {a : α} {s : Seq α}
    (h : (cons a s).Terminates) : s.Terminates :=
  terminates_cons_iff.mp h

/-- `toList` of a cons. -/
theorem toList_cons {a : α} {s : Seq α} (h : (cons a s).Terminates) :
    (cons a s).toList h = a :: s.toList (terminates_tail_of_cons h) := by
  unfold toList
  have h' : s.Terminates := terminates_tail_of_cons h
  rw [show (cons a s).length h = s.length h' + 1 from length_cons h']
  exact take_succ_cons

/-- Filter a (possibly infinite) sequence by a predicate, keeping only the
elements that satisfy it. Noncomputable: locating the next satisfying element
requires non-constructively inspecting arbitrarily many positions when the
predicate fails on a long run. -/
noncomputable def filter (p : α → Prop) (s : Seq α) : Seq α :=
  open Classical in
  Seq.corec (fun cur : Seq α =>
    if h : ∃ n, ∃ a, cur.get? n = some a ∧ p a then
      some ((Nat.find_spec h).choose, cur.drop (Nat.find h + 1))
    else none) s

/-- Filtering the empty sequence yields the empty sequence. -/
@[simp] theorem filter_nil (p : α → Prop) : (nil : Seq α).filter p = nil := by
  classical
  unfold filter
  apply corec_nil
  show (if _ : ∃ n, ∃ a, (nil : Seq α).get? n = some a ∧ p a then _ else none) = none
  rw [dif_neg]
  rintro ⟨n, a, h_eq, _⟩
  simp at h_eq

/-- Filtering `cons a s` by a predicate that holds at `a`: the result is
`cons a (s.filter p)`. -/
theorem filter_cons_pos {p : α → Prop} (a : α) (s : Seq α) (h : p a) :
    (cons a s).filter p = cons a (s.filter p) := by
  classical
  unfold filter
  apply corec_cons
  have h_ex : ∃ n, ∃ a', (cons a s).get? n = some a' ∧ p a' :=
    ⟨0, a, by simp, h⟩
  have h_find_zero : Nat.find h_ex = 0 :=
    (Nat.find_eq_zero h_ex).mpr ⟨a, by simp, h⟩
  change (if h' : ∃ n, ∃ a', (cons a s).get? n = some a' ∧ p a' then
         some ((Nat.find_spec h').choose, (cons a s).drop (Nat.find h' + 1))
       else none) = some (a, s)
  rw [dif_pos h_ex]
  have h_choose_eq : (Nat.find_spec h_ex).choose = a := by
    have h_spec_get : (cons a s).get? (Nat.find h_ex) =
        some (Nat.find_spec h_ex).choose := (Nat.find_spec h_ex).choose_spec.1
    have h_at_zero : (cons a s).get? (Nat.find h_ex) = some a := by
      rw [h_find_zero]; simp
    have : some a = some (Nat.find_spec h_ex).choose := h_at_zero.symm.trans h_spec_get
    exact (Option.some_inj.mp this).symm
  rw [h_choose_eq, h_find_zero]
  rfl

/-- `(cons a s).drop (n + 1) = s.drop n`: dropping one more from `cons a s` is
the same as dropping one from `s`. -/
private theorem drop_cons_succ (a : α) (s : Seq α) (n : ℕ) :
    (cons a s).drop (n + 1) = s.drop n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change tail ((cons a s).drop (k + 1)) = tail (s.drop k)
    rw [ih]

/-- Filtering `cons a s` by a predicate that fails at `a`: the result equals
`s.filter p`. -/
theorem filter_cons_neg {p : α → Prop} (a : α) (s : Seq α) (h : ¬ p a) :
    (cons a s).filter p = s.filter p := by
  classical
  apply Seq.eq_of_bisim
    (R := fun t₁ t₂ =>
      t₁ = t₂ ∨ ∃ a' s', ¬ p a' ∧ t₁ = (cons a' s').filter p ∧ t₂ = s'.filter p)
  · -- IsBisimulation
    have bisim_refl : ∀ x, BisimO
        (fun t₁ t₂ => t₁ = t₂ ∨ ∃ a' s', ¬ p a' ∧
          t₁ = (cons a' s').filter p ∧ t₂ = s'.filter p) x x := by
      intro x
      cases x with
      | none => trivial
      | some pr =>
        obtain ⟨v, t'⟩ := pr
        exact ⟨rfl, Or.inl rfl⟩
    rintro t₁ t₂ (rfl | ⟨a', s', h', rfl, rfl⟩)
    · exact bisim_refl _
    · -- Show: destruct ((cons a' s').filter p) = destruct (s'.filter p),
      -- then BisimO follows by reflexivity.
      suffices h_de : destruct ((cons a' s').filter p) = destruct (s'.filter p) by
        rw [h_de]; exact bisim_refl _
      unfold filter
      rw [corec_eq, corec_eq]
      -- Goal: omap _ (body (cons a' s')) = omap _ (body s')
      congr 1
      -- Goal: body (cons a' s') = body s', by case analysis.
      by_cases h_s_ex : ∃ m, ∃ a'', s'.get? m = some a'' ∧ p a''
      · -- Case A: `s'` has a `p`-satisfying element.
        have h_cons_ex : ∃ n, ∃ a'', (cons a' s').get? n = some a'' ∧ p a'' := by
          obtain ⟨m, a'', h_get, h_p⟩ := h_s_ex
          exact ⟨m + 1, a'', by simp [h_get], h_p⟩
        -- `Nat.find h_cons_ex = Nat.find h_s_ex + 1`.
        have h_find_eq : Nat.find h_cons_ex = Nat.find h_s_ex + 1 := by
          apply le_antisymm
          · apply Nat.find_min' h_cons_ex
            obtain ⟨a'', h_get, h_p⟩ := Nat.find_spec h_s_ex
            exact ⟨a'', by simp [h_get], h_p⟩
          · -- Extract a witness `a''` at `Nat.find h_cons_ex` in `cons a' s'`,
            -- then split that position as `m + 1` (it's positive since `¬ p a'`).
            obtain ⟨a'', h_get, h_p⟩ := Nat.find_spec h_cons_ex
            -- `Nat.find h_cons_ex ≥ 1`.
            have h_pos : 1 ≤ Nat.find h_cons_ex := by
              rcases Nat.eq_zero_or_pos (Nat.find h_cons_ex) with h_zero | h_pos
              · exfalso
                rw [h_zero] at h_get
                have h_eq : a' = a'' := by simpa using h_get
                subst h_eq
                exact h' h_p
              · exact h_pos
            obtain ⟨m, hm⟩ : ∃ m, Nat.find h_cons_ex = m + 1 :=
              Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp h_pos)
            rw [hm]
            apply Nat.succ_le_succ
            apply Nat.find_min' h_s_ex
            rw [hm] at h_get
            exact ⟨a'', by simpa using h_get, h_p⟩
        change (if h : ∃ n, ∃ a'', (cons a' s').get? n = some a'' ∧ p a'' then
                  some ((Nat.find_spec h).choose, (cons a' s').drop (Nat.find h + 1))
                else none) =
               (if h : ∃ n, ∃ a'', s'.get? n = some a'' ∧ p a'' then
                  some ((Nat.find_spec h).choose, s'.drop (Nat.find h + 1))
                else none)
        rw [dif_pos h_cons_ex, dif_pos h_s_ex]
        -- Drop equality.
        have h_drop_eq : (cons a' s').drop (Nat.find h_cons_ex + 1) =
            s'.drop (Nat.find h_s_ex + 1) := by
          rw [h_find_eq]
          exact drop_cons_succ a' s' (Nat.find h_s_ex + 1)
        -- Choose equality.
        have h_choose_eq : (Nat.find_spec h_cons_ex).choose =
            (Nat.find_spec h_s_ex).choose := by
          have h_cons_at_succ : (cons a' s').get? (Nat.find h_s_ex + 1) =
              some (Nat.find_spec h_cons_ex).choose := by
            rw [← h_find_eq]; exact (Nat.find_spec h_cons_ex).choose_spec.1
          have h_shift : (cons a' s').get? (Nat.find h_s_ex + 1) =
              s'.get? (Nat.find h_s_ex) := by simp
          have h_s_via : s'.get? (Nat.find h_s_ex) =
              some (Nat.find_spec h_cons_ex).choose := h_shift ▸ h_cons_at_succ
          have h_s_get : s'.get? (Nat.find h_s_ex) =
              some (Nat.find_spec h_s_ex).choose :=
            (Nat.find_spec h_s_ex).choose_spec.1
          exact Option.some_inj.mp (h_s_via.symm.trans h_s_get)
        rw [h_choose_eq, h_drop_eq]
      · -- Case B: neither `s'` nor `cons a' s'` has a `p`-satisfying element.
        have h_cons_neg :
            ¬ ∃ n, ∃ a'', (cons a' s').get? n = some a'' ∧ p a'' := by
          rintro ⟨n, a'', h_get, h_p⟩
          cases n with
          | zero =>
            have h_eq : a' = a'' := by simpa using h_get
            subst h_eq
            exact h' h_p
          | succ k =>
            exact h_s_ex ⟨k, a'', by simpa using h_get, h_p⟩
        change (if h : ∃ n, ∃ a'', (cons a' s').get? n = some a'' ∧ p a'' then
                  some ((Nat.find_spec h).choose, (cons a' s').drop (Nat.find h + 1))
                else none) =
               (if h : ∃ n, ∃ a'', s'.get? n = some a'' ∧ p a'' then
                  some ((Nat.find_spec h).choose, s'.drop (Nat.find h + 1))
                else none)
        rw [dif_neg h_cons_neg, dif_neg h_s_ex]
  · right
    exact ⟨a, s, h, rfl, rfl⟩

/-- `toList` of an `append` is the list-level concatenation of the two
constituent `toList`s. -/
theorem toList_append {α : Type*} (s s' : Seq α) (h_s : s.Terminates)
    (h_s' : s'.Terminates) (h_combined : (s.append s').Terminates) :
    (s.append s').toList h_combined = s.toList h_s ++ s'.toList h_s' := by
  -- Induct on s.length h_s, with s, h_s, h_combined universally quantified.
  suffices h_aux : ∀ (n : ℕ) (s : Seq α) (h_s : s.Terminates),
      s.length h_s = n → ∀ (h_combined : (s.append s').Terminates),
      (s.append s').toList h_combined = s.toList h_s ++ s'.toList h_s' from
    h_aux (s.length h_s) s h_s rfl h_combined
  intro n
  induction n with
  | zero =>
    intro s h_s h_len h_combined
    have h_s_nil : s = Seq.nil := length_eq_zero.mp h_len
    subst h_s_nil
    -- Goal: (nil.append s').toList h_combined = nil.toList h_s ++ s'.toList h_s'.
    -- nil.toList = []. (nil.append s') = s'. Goal reduces to s'.toList = s'.toList.
    have h_nil_toList : (Seq.nil : Seq α).toList h_s = [] := toList_nil
    rw [h_nil_toList, List.nil_append]
    -- Goal: (nil.append s').toList h_combined = s'.toList h_s'.
    -- Use proof irrelevance + nil_append.
    congr 1
    exact nil_append s'
  | succ n ih =>
    intro s h_s h_len h_combined
    have h_ne : s ≠ Seq.nil := by
      intro h_nil
      subst h_nil
      rw [length_nil] at h_len
      exact Nat.succ_ne_zero n h_len.symm
    cases s with
    | nil =>
      exact absurd rfl h_ne
    | cons a t =>
      have h_t_term : t.Terminates := terminates_tail_of_cons h_s
      have h_t_len : t.length h_t_term = n := by
        have : (cons a t).length h_s = t.length h_t_term + 1 := length_cons h_t_term
        rw [this] at h_len
        omega
      -- (cons a t).append s' = cons a (t.append s') (cons_append).
      have h_cons_app : (cons a t).append s' = cons a (t.append s') := cons_append a t s'
      -- Use this to compute both sides.
      -- LHS: (cons a t).append s'.toList h_combined.
      -- By proof irrelevance, this equals (cons a (t.append s')).toList h_combined'
      -- where h_combined' is the corresponding Terminates proof.
      have h_tail_combined : (t.append s').Terminates := by
        have : ((cons a t).append s').Terminates := h_combined
        rw [h_cons_app] at this
        exact terminates_tail_of_cons this
      have h_cons_tail_combined : (cons a (t.append s')).Terminates := by
        rw [← h_cons_app]; exact h_combined
      -- LHS: rewrite via the seq equality, then apply toList_cons.
      have h_LHS : ((cons a t).append s').toList h_combined =
          a :: (t.append s').toList h_tail_combined := by
        rw [show ((cons a t).append s').toList h_combined =
              (cons a (t.append s')).toList h_cons_tail_combined from by
          congr 1]
        exact toList_cons h_cons_tail_combined
      rw [h_LHS]
      rw [toList_cons h_s]
      rw [ih t h_t_term h_t_len h_tail_combined]
      rfl

/-- **Seq-splitting helper**: any terminating `Seq` whose `toList` is
non-empty can be expressed as `previous.append (cons last nil)` for some
terminating `previous` and last element `last`. Used for induction on
`AlterSeq` length: lets us peel off the most recent transition.

The construction takes `previous := ofList (toList.dropLast)` and `last :=
toList.getLast h_nonempty`; correctness follows from `dropLast ++ [getLast]
= toList`, `ofList_append`, and `ofList_toList`. -/
theorem exists_split_last
    {α : Type} (s : Seq α) (h_term : s.Terminates)
    (h_nonempty : s.toList h_term ≠ []) :
    ∃ (previous : Seq α) (last : α) (h_prev : previous.Terminates),
      s = previous.append (Seq.cons last Seq.nil) ∧
      previous.toList h_prev = (s.toList h_term).dropLast ∧
      last = (s.toList h_term).getLast h_nonempty := by
  let toL := s.toList h_term
  let lst := toL.getLast h_nonempty
  let prevList := toL.dropLast
  let previous : Seq α := Stream'.Seq.ofList prevList
  have h_prev : previous.Terminates := Stream'.Seq.terminates_ofList prevList
  have h_split : toL = prevList ++ [lst] :=
    (List.dropLast_append_getLast h_nonempty).symm
  refine ⟨previous, lst, h_prev, ?_, ?_, rfl⟩
  · -- s = previous.append (cons lst nil)
    -- s = ofList (toList s h_term) = ofList (prevList ++ [lst])
    --   = (ofList prevList).append (ofList [lst])
    --   = previous.append (cons lst (ofList []))
    --   = previous.append (cons lst nil)
    have h_s_eq : s = Stream'.Seq.ofList toL := (Stream'.Seq.ofList_toList s h_term).symm
    rw [h_s_eq, h_split, Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons,
        Stream'.Seq.ofList_nil]
  · -- previous.toList h_prev = prevList = dropLast (toL).
    exact Stream'.Seq.toList_ofList prevList

/-- `Seq.filter` distributes over `append` when the left sequence terminates.
Proved by induction on the underlying list of the left sequence. -/
theorem filter_append (p : α → Prop) (s t : Seq α)
    (h_s : s.Terminates) :
    (s.append t).filter p = (s.filter p).append (t.filter p) := by
  classical
  obtain ⟨l, hl⟩ : ∃ l : List α, s = Seq.ofList l :=
    ⟨s.toList h_s, (Seq.ofList_toList _ _).symm⟩
  subst hl
  clear h_s
  induction l with
  | nil =>
    rw [Seq.ofList_nil, Seq.nil_append, Seq.filter_nil, Seq.nil_append]
  | cons a t' ih =>
    rw [Seq.ofList_cons, Seq.cons_append]
    by_cases h_p : p a
    · rw [Seq.filter_cons_pos a _ h_p, Seq.filter_cons_pos a _ h_p, Seq.cons_append, ih]
    · rw [Seq.filter_cons_neg a _ h_p, Seq.filter_cons_neg a _ h_p, ih]

/-- Right-cancellation for append-of-singleton on terminating sequences: if
`A ++ [x] = B ++ [y]` with both `A`, `B` terminating, then `x = y`. -/
theorem append_singleton_inj_right
    (A B : Seq α) (h_A : A.Terminates) (h_B : B.Terminates) (x y : α)
    (h : A.append (Seq.cons x Seq.nil) = B.append (Seq.cons y Seq.nil)) :
    x = y := by
  classical
  have h_x_term : (Seq.cons x Seq.nil).Terminates :=
    Seq.terminates_cons_iff.mpr Seq.terminates_nil
  have h_y_term : (Seq.cons y Seq.nil).Terminates :=
    Seq.terminates_cons_iff.mpr Seq.terminates_nil
  have h_AX_term : (A.append (Seq.cons x Seq.nil)).Terminates :=
    ⟨_, Seq.terminatedAt_append_find h_A h_x_term.choose_spec⟩
  have h_BY_term : (B.append (Seq.cons y Seq.nil)).Terminates :=
    ⟨_, Seq.terminatedAt_append_find h_B h_y_term.choose_spec⟩
  have h_toL : (A.append (Seq.cons x Seq.nil)).toList h_AX_term
              = (B.append (Seq.cons y Seq.nil)).toList h_BY_term := by congr 1
  rw [Seq.toList_append A _ h_A h_x_term h_AX_term,
      Seq.toList_append B _ h_B h_y_term h_BY_term] at h_toL
  have h_x_toL : (Seq.cons x Seq.nil).toList h_x_term = [x] := by
    rw [Seq.toList_cons h_x_term]; congr 1; exact Seq.toList_nil
  have h_y_toL : (Seq.cons y Seq.nil).toList h_y_term = [y] := by
    rw [Seq.toList_cons h_y_term]; congr 1; exact Seq.toList_nil
  rw [h_x_toL, h_y_toL] at h_toL
  have h_last := congrArg List.getLast? h_toL
  rw [List.getLast?_concat, List.getLast?_concat] at h_last
  exact Option.some_inj.mp h_last

/-- Left-cancellation for append-of-singleton on terminating sequences: if
`A ++ [x] = B ++ [y]` with both `A`, `B` terminating, then `A = B`. -/
theorem append_singleton_inj_left
    (A B : Seq α) (h_A : A.Terminates) (h_B : B.Terminates) (x y : α)
    (h : A.append (Seq.cons x Seq.nil) = B.append (Seq.cons y Seq.nil)) :
    A = B := by
  classical
  have h_x_term : (Seq.cons x Seq.nil).Terminates :=
    Seq.terminates_cons_iff.mpr Seq.terminates_nil
  have h_y_term : (Seq.cons y Seq.nil).Terminates :=
    Seq.terminates_cons_iff.mpr Seq.terminates_nil
  have h_AX_term : (A.append (Seq.cons x Seq.nil)).Terminates :=
    ⟨_, Seq.terminatedAt_append_find h_A h_x_term.choose_spec⟩
  have h_BY_term : (B.append (Seq.cons y Seq.nil)).Terminates :=
    ⟨_, Seq.terminatedAt_append_find h_B h_y_term.choose_spec⟩
  have h_toL : (A.append (Seq.cons x Seq.nil)).toList h_AX_term
              = (B.append (Seq.cons y Seq.nil)).toList h_BY_term := by congr 1
  rw [Seq.toList_append A _ h_A h_x_term h_AX_term,
      Seq.toList_append B _ h_B h_y_term h_BY_term] at h_toL
  have h_x_toL : (Seq.cons x Seq.nil).toList h_x_term = [x] := by
    rw [Seq.toList_cons h_x_term]; congr 1; exact Seq.toList_nil
  have h_y_toL : (Seq.cons y Seq.nil).toList h_y_term = [y] := by
    rw [Seq.toList_cons h_y_term]; congr 1; exact Seq.toList_nil
  rw [h_x_toL, h_y_toL] at h_toL
  have h_dropLast := congrArg List.dropLast h_toL
  rw [List.dropLast_concat, List.dropLast_concat] at h_dropLast
  have h_A_toL_eq : A = Seq.ofList (A.toList h_A) :=
    (Seq.ofList_toList _ _).symm
  have h_B_toL_eq : B = Seq.ofList (B.toList h_B) :=
    (Seq.ofList_toList _ _).symm
  rw [h_A_toL_eq, h_B_toL_eq, h_dropLast]

/-- `map` and `drop` commute: dropping `n` elements from `s.map f` is the
same as mapping `f` over `s.drop n`. -/
theorem map_drop {β : Type*} (f : α → β) (s : Seq α) (n : ℕ) :
    (s.map f).drop n = (s.drop n).map f := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih =>
    change tail ((s.map f).drop k) = tail ((s.drop k).map f)
    rw [ih]

/-- Filter-map interchange: filtering after mapping equals mapping after
filtering by the precomposed predicate. Proved by bisimulation with case
analysis on whether `s` contains an element satisfying `p ∘ f`. -/
theorem filter_map {β : Type*} (f : α → β) (p : β → Prop) (s : Seq α) :
    (s.map f).filter p = (s.filter (p ∘ f)).map f := by
  classical
  apply Seq.eq_of_bisim
    (R := fun t₁ t₂ => ∃ s : Seq α,
      t₁ = (s.map f).filter p ∧ t₂ = (s.filter (p ∘ f)).map f)
  · rintro t₁ t₂ ⟨s, rfl, rfl⟩
    have h_ex_iff : (∃ n, ∃ b, (s.map f).get? n = some b ∧ p b)
        ↔ (∃ n, ∃ a, s.get? n = some a ∧ (p ∘ f) a) := by
      constructor
      · rintro ⟨n, b, h_get, h_p⟩
        rw [map_get?] at h_get
        rcases h_s : s.get? n with - | a
        · rw [h_s] at h_get; simp at h_get
        · rw [h_s] at h_get
          simp only [Option.map_some, Option.some_inj] at h_get
          refine ⟨n, a, h_s, ?_⟩
          change p (f a); rw [h_get]; exact h_p
      · rintro ⟨n, a, h_get, h_p⟩
        refine ⟨n, f a, ?_, h_p⟩
        rw [map_get?, h_get]; rfl
    by_cases h_ex : ∃ n, ∃ a, s.get? n = some a ∧ (p ∘ f) a
    · have h_ex' : ∃ n, ∃ b, (s.map f).get? n = some b ∧ p b := h_ex_iff.mpr h_ex
      have h_find_eq : Nat.find h_ex' = Nat.find h_ex := by
        apply le_antisymm
        · obtain ⟨a, h_get, h_p⟩ := Nat.find_spec h_ex
          apply Nat.find_min' h_ex'
          exact ⟨f a, by rw [map_get?, h_get]; rfl, h_p⟩
        · obtain ⟨b, h_get, h_p⟩ := Nat.find_spec h_ex'
          apply Nat.find_min' h_ex
          rw [map_get?] at h_get
          rcases h_s : s.get? (Nat.find h_ex') with - | a
          · rw [h_s] at h_get; simp at h_get
          · rw [h_s] at h_get
            simp only [Option.map_some, Option.some_inj] at h_get
            exact ⟨a, rfl, by change p (f a); rw [h_get]; exact h_p⟩
      set cL := (Nat.find_spec h_ex').choose
      set cR := (Nat.find_spec h_ex).choose
      have h1 : (s.map f).get? (Nat.find h_ex') = some cL :=
        (Nat.find_spec h_ex').choose_spec.1
      have h2 : s.get? (Nat.find h_ex) = some cR :=
        (Nat.find_spec h_ex).choose_spec.1
      have h_LHS_destruct :
          destruct ((s.map f).filter p) = some
            (cL, ((s.map f).drop (Nat.find h_ex' + 1)).filter p) := by
        unfold filter
        rw [corec_eq, dif_pos h_ex']
        rfl
      have h_inner_destruct :
          destruct (s.filter (p ∘ f)) = some
            (cR, (s.drop (Nat.find h_ex + 1)).filter (p ∘ f)) := by
        unfold filter
        rw [corec_eq, dif_pos h_ex]
        rfl
      have h_inner_cons : s.filter (p ∘ f) = cons cR
          ((s.drop (Nat.find h_ex + 1)).filter (p ∘ f)) :=
        destruct_eq_cons h_inner_destruct
      rw [h_inner_cons, map_cons, destruct_cons, h_LHS_destruct]
      refine ⟨?_, ?_⟩
      · have h3 : (s.map f).get? (Nat.find h_ex') = some (f cR) := by
          rw [map_get?, h_find_eq, h2]; rfl
        exact Option.some_inj.mp (h1.symm.trans h3)
      · refine ⟨s.drop (Nat.find h_ex + 1), ?_, rfl⟩
        rw [h_find_eq, map_drop]
    · have h_ex_neg' : ¬ ∃ n, ∃ b, (s.map f).get? n = some b ∧ p b :=
        fun h => h_ex (h_ex_iff.mp h)
      have h_inner_nil : s.filter (p ∘ f) = nil := by
        unfold filter
        apply corec_nil
        rw [dif_neg h_ex]
      have h_LHS_nil : (s.map f).filter p = nil := by
        unfold filter
        apply corec_nil
        rw [dif_neg h_ex_neg']
      rw [h_inner_nil, h_LHS_nil, map_nil]
      trivial
  · exact ⟨s, rfl, rfl⟩

/-- Filter preserves termination: a filter of a terminating sequence
is itself terminating. -/
theorem terminates_filter (p : α → Prop) (s : Seq α)
    (h : s.Terminates) : (s.filter p).Terminates := by
  classical
  obtain ⟨l, rfl⟩ : ∃ l : List α, s = Seq.ofList l :=
    ⟨s.toList h, (Seq.ofList_toList _ _).symm⟩
  have h_t : ∀ t : List α, ((↑t : Seq α).filter p).Terminates := by
    intro t
    induction t with
    | nil =>
      change ((Seq.nil : Seq α).filter p).Terminates
      rw [Stream'.Seq.filter_nil]
      exact Seq.terminates_nil
    | cons a t ih =>
      rw [Stream'.Seq.ofList_cons]
      by_cases h_p : p a
      · rw [Stream'.Seq.filter_cons_pos a _ h_p]
        rcases ih with ⟨m, hm⟩
        refine ⟨m + 1, ?_⟩
        change (Seq.cons a ((Seq.ofList t).filter p)).get? (m + 1) = none
        rw [Seq.get?_cons_succ]
        exact hm
      · rw [Stream'.Seq.filter_cons_neg a _ h_p]
        exact ih
  exact h_t l

/-- `toList` is invariant under equality of the underlying `Seq` (the termination
proofs are irrelevant). -/
theorem toList_congr_pub {γ : Type} {s t : Seq γ} (heq : s = t)
    (hs : s.Terminates) (ht : t.Terminates) : s.toList hs = t.toList ht := by subst heq; rfl

/-- Public version of `System.map_ofList`: `Seq.map f (ofList L) = ofList (L.map f)`. -/
theorem map_ofList_pub {α β : Type} (f : α → β) (L : List α) :
    (Seq.ofList L).map f = Seq.ofList (L.map f) := by
  induction L with
  | nil => rw [Stream'.Seq.ofList_nil, Stream'.Seq.map_nil, List.map_nil, Stream'.Seq.ofList_nil]
  | cons a L ih =>
    rw [Stream'.Seq.ofList_cons, Stream'.Seq.map_cons, List.map_cons, Stream'.Seq.ofList_cons, ih]

/-- The length of `(ofList rest).append (cons x nil)` is `rest.length + 1`. -/
theorem append_singleton_length' {γ : Type} (rest : List γ) (x : γ) :
    ((Seq.ofList rest).append (Seq.cons x Seq.nil) : Seq γ).length' = rest.length + 1 := by
  have hcons : (Seq.cons x Seq.nil : Seq γ).Terminates :=
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
  have hfin : ((Seq.ofList rest).append (Seq.cons x Seq.nil) : Seq γ).Terminates :=
    ⟨_, Stream'.Seq.terminatedAt_append_find (Stream'.Seq.terminates_ofList rest)
      (show (Seq.cons x Seq.nil).TerminatedAt 1 from rfl)⟩
  rw [Stream'.Seq.length'_of_terminates hfin]
  have h_eq := Stream'.Seq.length_toList ((Seq.ofList rest).append (Seq.cons x Seq.nil)) hfin
  rw [Stream'.Seq.toList_append (Seq.ofList rest) (Seq.cons x Seq.nil)
    (Stream'.Seq.terminates_ofList rest) hcons hfin,
    Stream'.Seq.toList_ofList, List.length_append, Stream'.Seq.toList_cons,
    Stream'.Seq.toList_nil] at h_eq
  rw [← h_eq]; simp

open Classical in
/-- `Seq.filter` of an `ofList` is the `ofList` of the corresponding `List.filter`. -/
theorem ofList_filter {α : Type} (p : α → Prop) (l : List α) :
    (Seq.ofList l).filter p = Seq.ofList (l.filter (fun a => decide (p a))) := by
  induction l with
  | nil =>
    rw [Stream'.Seq.ofList_nil, Stream'.Seq.filter_nil, List.filter_nil, Stream'.Seq.ofList_nil]
  | cons a t ih =>
    rw [Stream'.Seq.ofList_cons]
    by_cases h : p a
    · rw [Stream'.Seq.filter_cons_pos a _ h, ih, List.filter_cons_of_pos (by simpa using h),
        Stream'.Seq.ofList_cons]
    · rw [Stream'.Seq.filter_cons_neg a _ h, ih, List.filter_cons_of_neg (by simpa using h)]

end Stream'.Seq
