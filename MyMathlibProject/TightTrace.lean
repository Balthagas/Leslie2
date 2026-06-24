/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.TraceProbBound

/-!
# Tight-trace & execution-structure helpers

Generic execution-structure machinery, factored out of `WeakConstruction`: pure
`Seq`/`AlterSeq`/`List` helpers (`drop`/`takeWhile`/`filter` lemmas, `endState`
under suffixing and appends), the maximal all-internal tail `internalSuffix`, and
the structural lemmas about *tight* executions (`trace_append`, `isTight_append`,
`tight_getLast_external`, the filter-split lemmas, and the `internalSuffix`
characterisations on tight / segment-extended histories). None of this depends on
the weak-closure or `expand` constructions, so it lives upstream of
`WeakConstruction`.
-/

open Stream'

namespace PLTS

variable {α β State State_C State_A Label : Type}

/-! ### Pure `Seq` / `AlterSeq` / `List` helpers -/

/-- `endState` depends only on the underlying `AlterSeq` (termination proofs are
irrelevant). -/
theorem AlterSeq.endState_congr_pub {e₁ e₂ : AlterSeq State Label}
    (heq : e₁ = e₂) (h₁ : e₁.trans.Terminates) (h₂ : e₂.trans.Terminates) :
    e₁.endState h₁ = e₂.endState h₂ := by subst heq; rfl

/-- Dropping a prefix of a terminating `Seq` again terminates. -/
theorem Stream'.Seq.drop_terminates_pub {α : Type} {s : Seq α} (hT : s.Terminates) (j : ℕ) :
    (s.drop j).Terminates := by
  obtain ⟨N, hN⟩ := hT
  exact ⟨N, by
    change (s.drop j).get? N = none
    rw [Stream'.Seq.drop_get?]; exact Stream'.Seq.terminated_stable s (Nat.le_add_left N j) hN⟩

/-- `Seq.drop` of `Seq.ofList` is `Seq.ofList ∘ List.drop`. -/
theorem Stream'.Seq.drop_ofList_pub {γ : Type} (L : List γ) (j : ℕ) :
    Stream'.Seq.drop (Stream'.Seq.ofList L) j = Stream'.Seq.ofList (L.drop j) := by
  apply Stream'.Seq.ext; intro n
  rw [Stream'.Seq.drop_get?, Stream'.Seq.ofList_get?, Stream'.Seq.ofList_get?, List.getElem?_drop]

/-- `(s.drop j).toList` is the `List.drop j` of `s.toList`. -/
theorem Stream'.Seq.drop_toList_eq_pub {γ : Type} (s : Seq γ) (h : s.Terminates) (j : ℕ)
    (hd : (s.drop j).Terminates) : (s.drop j).toList hd = (s.toList h).drop j := by
  have key : s.drop j = Seq.ofList ((s.toList h).drop j) := by
    conv_lhs => rw [← Stream'.Seq.ofList_toList s h]; rw [Stream'.Seq.drop_ofList_pub]
  rw [Stream'.Seq.toList_congr_pub key hd (Stream'.Seq.terminates_ofList _),
    Stream'.Seq.toList_ofList]

/-- `endState e` is the `.2` of the last transition of `e` (or `e.init` if there
are none), read off `e.trans.toList`. -/
theorem AlterSeq.endState_eq_getLast? (e : AlterSeq State Label) (h : e.trans.Terminates) :
    e.endState h = ((e.trans.toList h).getLast?).elim e.init Prod.snd := by
  classical
  rcases Nat.eq_zero_or_pos (e.trans.length h) with hl | hl
  · have htoNil : e.trans.toList h = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Stream'.Seq.length_toList]; exact hl
    have hnil : e.trans = Seq.nil := by
      have := Stream'.Seq.ofList_toList e.trans h
      rw [htoNil] at this; rw [← this]; rfl
    rw [AlterSeq.endState_of_trans_nil e hnil h, htoNil]; rfl
  · have hgl : (e.trans.toList h).getLast? = e.trans.get? (e.trans.length h - 1) :=
      Stream'.Seq.getLast?_toList e.trans h
    have hfind : Nat.find h = e.trans.length h := rfl
    have hes := AlterSeq.stateAt_find_eq_endState e h
    rw [hfind] at hes
    obtain ⟨m, hm⟩ : ∃ m, e.trans.length h = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
    rw [hm] at hes
    change (e.trans.get? m).map Prod.snd = some (e.endState h) at hes
    rw [hgl, hm, Nat.add_sub_cancel]
    cases hg : e.trans.get? m with
    | none => rw [hg] at hes; simp at hes
    | some p =>
      rw [hg] at hes; simp only [Option.map_some, Option.some.injEq] at hes; simp [hes]

/-- The end-state of the `m`-suffix `⟨(stateAt m).getD init, trans.drop m⟩` equals
the end-state of `e`, for any split `m ≤ length` (both are `e`'s final state). -/
theorem AlterSeq.endState_drop_suffix (e : AlterSeq State Label) (h : e.trans.Terminates)
    (m : ℕ) (hm : m ≤ e.trans.length h) :
    (⟨(e.stateAt m).getD e.init, e.trans.drop m⟩ : AlterSeq State Label).endState
        (Stream'.Seq.drop_terminates_pub h m) = e.endState h := by
  classical
  rw [AlterSeq.endState_eq_getLast? _ (Stream'.Seq.drop_terminates_pub h m),
      AlterSeq.endState_eq_getLast? e h]
  have hdl : (⟨(e.stateAt m).getD e.init, e.trans.drop m⟩
        : AlterSeq State Label).trans.toList (Stream'.Seq.drop_terminates_pub h m)
      = (e.trans.toList h).drop m :=
    Stream'.Seq.drop_toList_eq_pub e.trans h m (Stream'.Seq.drop_terminates_pub h m)
  rw [hdl, List.getLast?_drop]
  have hlen : (e.trans.toList h).length = e.trans.length h := Stream'.Seq.length_toList e.trans h
  by_cases hlt : e.trans.length h ≤ m
  · have heq : m = e.trans.length h := le_antisymm hm hlt
    have hcond : (e.trans.toList h).length ≤ m := by rw [hlen]; omega
    rw [if_pos hcond]
    have hst : e.stateAt m = some (e.endState h) := by
      rw [heq]; have := AlterSeq.stateAt_find_eq_endState e h
      rwa [show Nat.find h = e.trans.length h from rfl] at this
    simp only [hst, Option.getD_some]
    exact AlterSeq.endState_eq_getLast? e h
  · have hcond : ¬ (e.trans.toList h).length ≤ m := by rw [hlen]; omega
    rw [if_neg hcond]
    cases hgl : (e.trans.toList h).getLast? with
    | none => rw [List.getLast?_eq_none_iff] at hgl; rw [hgl] at hcond; simp at hcond
    | some p => rfl

/-- **The end-state of an append is the end-state of its (nonempty) suffix.** -/
theorem AlterSeq.endState_append
    (s s' : State) (A B : Seq (Label × State)) (hA : A.Terminates) (hB : B.Terminates)
    (hB_ne : B.toList hB ≠ []) (hAB : (A.append B).Terminates) :
    (⟨s, A.append B⟩ : AlterSeq State Label).endState hAB
      = (⟨s', B⟩ : AlterSeq State Label).endState hB := by
  rw [AlterSeq.endState_eq_getLast? _ hAB, AlterSeq.endState_eq_getLast? _ hB]
  have hAB_list : (⟨s, A.append B⟩ : AlterSeq State Label).trans.toList hAB
      = A.toList hA ++ B.toList hB := Stream'.Seq.toList_append A B hA hB hAB
  rw [hAB_list, List.getLast?_append_of_ne_nil _ hB_ne]
  -- `B`'s last is `some bl`, so the `.elim … init …` default (differing `init`s) is unused.
  obtain ⟨bl, hbl⟩ : ∃ bl, (B.toList hB).getLast? = some bl := by
    cases hb : (B.toList hB).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hb) hB_ne
    | some bl => exact ⟨bl, rfl⟩
  rw [hbl]; rfl

/-- `Seq.filter` of `Seq.ofList` is `Seq.ofList` of the `List.filter`. -/
theorem Stream'.Seq.filter_ofList_pub {α : Type} (p : α → Prop) [DecidablePred p]
    (L : List α) :
    (Seq.ofList L).filter p = Seq.ofList (L.filter (fun a => decide (p a))) := by
  induction L with
  | nil => rw [Seq.ofList_nil, Seq.filter_nil, List.filter_nil, Seq.ofList_nil]
  | cons a t ih =>
    rw [Seq.ofList_cons, List.filter_cons]
    by_cases hp : p a
    · rw [Seq.filter_cons_pos a _ hp, if_pos (by simpa using hp), Seq.ofList_cons, ih]
    · rw [Seq.filter_cons_neg a _ hp, if_neg (by simpa using hp), ih]

/-- **`takeWhile` of an append whose prefix all satisfies `P` and suffix-head fails `P`.** -/
theorem List.takeWhile_append_of_all {α : Type} (a b : List α) (P : α → Bool)
    (ha : ∀ x ∈ a, P x) (hb : ∀ x, b.head? = some x → ¬ P x) :
    (a ++ b).takeWhile P = a := by
  induction a with
  | nil =>
    simp only [List.nil_append]
    cases hbb : b with
    | nil => simp
    | cons x t => rw [List.takeWhile_cons, if_neg (hb x (by rw [hbb]; rfl))]
  | cons y t ih =>
    rw [List.cons_append, List.takeWhile_cons, if_pos (ha y (by simp)),
      ih (fun x hx => ha x (List.mem_cons_of_mem y hx))]

/-- **List filter-split into a tight prefix.** If `L.filter P = a ++ b` with `b` nonempty,
then `L` splits as `L1 ++ L2` with `L1.filter P = a`, `L2.filter P = b`, and `L1` "tight"
(empty or ending with a `P`-element). `L1` is the shortest prefix with filter `a`: it ends
right after the `|a|`-th `P`-element, so any trailing non-`P` run is pushed into `L2`. -/
theorem List.exists_filter_split_tight {α : Type} (P : α → Bool) :
    ∀ (L : List α) (a b : List α), b ≠ [] → L.filter P = a ++ b →
      ∃ L1 L2, L = L1 ++ L2 ∧ L1.filter P = a ∧ L2.filter P = b ∧
        (∀ y, L1.getLast? = some y → P y) := by
  intro L
  induction L with
  | nil =>
    intro a b hb h
    rw [List.filter_nil] at h
    exact absurd (List.append_eq_nil_iff.mp h.symm).2 hb
  | cons x t ih =>
    intro a b hb h
    cases a with
    | nil =>
      refine ⟨[], x :: t, rfl, by simp, ?_, by simp⟩
      rw [List.nil_append] at h; exact h
    | cons a0 a' =>
      rw [List.filter_cons] at h
      by_cases hx : P x
      · rw [if_pos hx, List.cons_append] at h
        obtain ⟨hx_eq, ht⟩ := List.cons.inj h
        obtain ⟨L1, L2, hL, hL1, hL2, htight⟩ := ih a' b hb ht
        refine ⟨x :: L1, L2, by rw [hL, List.cons_append], ?_, hL2, ?_⟩
        · rw [List.filter_cons, if_pos hx, hL1, hx_eq]
        · intro y hy
          cases hL1' : L1.getLast? with
          | none =>
            have hL1nil : L1 = [] := List.getLast?_eq_none_iff.mp hL1'
            subst hL1nil
            rw [List.getLast?_singleton] at hy
            rw [← Option.some.inj hy, hx_eq]; rw [hx_eq] at hx; exact hx
          | some z =>
            rw [List.getLast?_cons, hL1'] at hy
            exact htight y (by rw [hL1']; exact hy)
      · rw [if_neg hx] at h
        obtain ⟨L1, L2, hL, hL1, hL2, htight⟩ := ih (a0 :: a') b hb h
        have hL1ne : L1 ≠ [] := by
          intro hc; rw [hc, List.filter_nil] at hL1; exact absurd hL1.symm (by simp)
        refine ⟨x :: L1, L2, by rw [hL, List.cons_append], ?_, hL2, ?_⟩
        · rw [List.filter_cons, if_neg hx, hL1]
        · intro y hy
          have hrw : (x :: L1).getLast? = L1.getLast? := by
            rw [List.getLast?_cons]
            cases hL1'' : L1.getLast? with
            | none => exact absurd (List.getLast?_eq_none_iff.mp hL1'') hL1ne
            | some _ => rfl
          rw [hrw] at hy
          exact htight y hy

/-- **Uniqueness of the filter-tight split.** If `A ++ B = C ++ D` with `A.filter P = C.filter P`
and both `A`, `C` empty-or-ending in a `P`-element, then `A = C` (and hence `B = D`). The longer
prefix's surplus has empty `P`-filter (all `¬P`), but it would carry that prefix's external last
element, contradicting it ending in a `P`-element — so the prefixes coincide. -/
theorem List.filter_tight_split_unique {α : Type} (P : α → Bool) :
    ∀ A B C D : List α, A ++ B = C ++ D → A.filter P = C.filter P →
      (∀ y, A.getLast? = some y → P y) → (∀ y, C.getLast? = some y → P y) → A = C := by
  -- WLOG handle the case where one is a prefix of the other.
  have key : ∀ A C M : List α, C = A ++ M → A.filter P = C.filter P →
      (∀ y, C.getLast? = some y → P y) → M = [] := by
    intro A C M hC hfilt hClast
    rw [hC, List.filter_append] at hfilt
    have hMfilt : M.filter P = [] := by
      have : A.filter P ++ M.filter P = A.filter P ++ [] := by
        rw [List.append_nil]; exact hfilt.symm
      exact List.append_cancel_left this
    by_contra hMne
    -- `M`'s last element fails `P` (its filter is empty), but it is `C`'s last (so passes `P`).
    obtain ⟨ml, hml⟩ : ∃ ml, M.getLast? = some ml := by
      cases hm : M.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hm) hMne
      | some ml => exact ⟨ml, rfl⟩
    have hml_mem : ml ∈ M := List.mem_of_getLast? hml
    have hml_notP : ¬ P ml := by
      intro hP
      have : ml ∈ M.filter P := List.mem_filter.mpr ⟨hml_mem, hP⟩
      rw [hMfilt] at this; exact absurd this (List.not_mem_nil)
    have hClast_eq : C.getLast? = some ml := by
      rw [hC, List.getLast?_append_of_ne_nil _ hMne, hml]
    exact hml_notP (hClast ml hClast_eq)
  intro A B C D hABCD hfilt hAlast hClast
  rcases List.append_eq_append_iff.mp hABCD with ⟨M, hC, _⟩ | ⟨M, hA, _⟩
  · -- `C = A ++ M`.
    rw [hC, key A C M hC hfilt hClast, List.append_nil]
  · -- `A = C ++ M`.
    rw [hA, key C A M hA hfilt.symm hAlast, List.append_nil]

/-- **Trace of an append** (the trace ignores states; it depends only on the transition
sequence). -/
theorem LabelledSystem.trace_append (sys : LabelledSystem State Label)
    (s s' : State) (A B : Seq (Label × State)) (hA : A.Terminates) :
    sys.trace ⟨s, A.append B⟩ = (sys.trace ⟨s, A⟩).append (sys.trace ⟨s', B⟩) := by
  unfold LabelledSystem.trace
  rw [Stream'.Seq.filter_append _ _ _ hA, Stream'.Seq.map_append]

/-- **A tight execution ends with an external transition.** (`IsTight`'s content via
`tight_iff`.) Supplies the `hpre_ext` hypothesis of `expand_probOf_append_factor`. -/
theorem LabelledSystem.tight_getLast_external (sys : LabelledSystem State Label)
    (e : AlterSeq State Label) (h : e.trans.Terminates) (htight : sys.IsTight e)
    (p : Label × State) (hp : (e.trans.toList h).getLast? = some p) :
    ¬ sys.internal p.1 := by
  have htt := ((sys.tight_iff (sys.trace e) e h).mp ⟨rfl, htight⟩).2
  exact htt p.1 (by rw [List.getLast?_map, hp]; rfl)

/-- **`IsTight` depends only on the transition sequence**, not on the initial state. -/
theorem LabelledSystem.isTight_init_irrel (sys : LabelledSystem State Label)
    (s s' : State) (B : Seq (Label × State)) (h : sys.IsTight ⟨s, B⟩) :
    sys.IsTight ⟨s', B⟩ := by
  unfold LabelledSystem.IsTight at h ⊢
  exact h

/-- **A tight trace-`[l]` segment has a nonempty transition list.** Its external trace is
the single label `l`, so it must contain at least one transition. -/
theorem LabelledSystem.tight_singleton_trans_nonempty (sys : LabelledSystem State Label)
    (seg : AlterSeq State Label) (h : seg.trans.Terminates) (l : Label)
    (htrace : sys.trace seg = Seq.ofList [l]) :
    seg.trans.toList h ≠ [] := by
  intro hnil
  -- `seg.trans = nil`, so `trace seg = nil ≠ ofList [l]`.
  have htrans_nil : seg.trans = Seq.nil := by
    have := congrArg Stream'.Seq.ofList hnil
    rwa [Stream'.Seq.ofList_toList seg.trans h, Stream'.Seq.ofList_nil] at this
  have : sys.trace seg = Seq.nil := by
    obtain ⟨si, st⟩ := seg
    simp only at htrans_nil
    subst htrans_nil
    exact sys.trace_init si
  rw [this, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil] at htrace
  exact absurd htrace.symm (by simp [Stream'.Seq.cons_ne_nil])

/-- **A tight trace-`[l]` execution has all-internal transitions except its last.** Its
transition label list contains exactly one external label, which (by tightness) is the
last; so every position strictly before the end is internal. For any `pref ++ [step] <+:
seg.trans.toList`, all of `pref` is internal — exactly the `hseg_int` hypothesis of
`expand_probOf_append_factor`. -/
theorem LabelledSystem.tight_singleton_prefix_internal (sys : LabelledSystem State Label)
    (seg : AlterSeq State Label) (h : seg.trans.Terminates) (l : Label)
    (htrace : sys.trace seg = Seq.ofList [l]) (htight : sys.IsTight seg)
    (pref : List (Label × State)) (step : Label × State)
    (hpf : pref ++ [step] <+: seg.trans.toList h) (q : Label × State) (hq : q ∈ pref) :
    sys.internal q.1 := by
  classical
  set Ltr := seg.trans.toList h with hLtr
  set L := Ltr.map Prod.fst with hL
  -- `L.filter (¬internal) = [l]` (exactly one external), from `traceTightLabs`.
  have htt1 : (Seq.ofList L).filter (fun a => ¬ sys.internal a) = Seq.ofList [l] :=
    ((sys.tight_iff (Seq.ofList [l]) seg h).mp ⟨htrace, htight⟩).1
  have hfilt : L.filter (fun a => decide (¬ sys.internal a)) = [l] := by
    rw [Stream'.Seq.filter_ofList_pub] at htt1
    exact Stream'.Seq.ofList_injective htt1
  -- The last element of `Ltr` is external (tightness).
  by_contra hext
  -- `pref.map fst ++ [step.1]` is a prefix of `L`, with an external in `pref`.
  have hpfL : (pref.map Prod.fst) ++ [step.1] <+: L := by
    rw [hL]
    have := List.IsPrefix.map (f := Prod.fst) hpf
    rwa [List.map_append, List.map_singleton] at this
  obtain ⟨rest', hrest'⟩ := hpfL
  -- `L = pref.map fst ++ [step.1] ++ rest'`.
  have hLsplit : L = (pref.map Prod.fst) ++ ([step.1] ++ rest') := by
    rw [← hrest', List.append_assoc]
  -- The filter splits; `pref.map fst` contributes ≥ 1 external (`q.1`), the tail ≥ 1
  -- (the external last element of `L`). So total length ≥ 2, contradicting `= [l]`.
  have hlen1 : (L.filter (fun a => decide (¬ sys.internal a))).length = 1 := by
    rw [hfilt]; rfl
  rw [hLsplit, List.filter_append, List.length_append] at hlen1
  -- `pref.map fst` has at least one external (`q.1`).
  have hq1 : q.1 ∈ pref.map Prod.fst := List.mem_map_of_mem hq
  have hpref_ge : 1 ≤ ((pref.map Prod.fst).filter (fun a => decide (¬ sys.internal a))).length := by
    refine List.length_pos_iff.mpr ?_
    intro hnil
    have : q.1 ∉ (pref.map Prod.fst).filter (fun a => decide (¬ sys.internal a)) := by
      rw [hnil]; exact List.not_mem_nil
    exact this (List.mem_filter.mpr ⟨hq1, by simpa using hext⟩)
  -- The tail `[step.1] ++ rest'` has at least one external: the last element of `L`.
  have hnonempty : L ≠ [] := by
    rw [hLsplit]; intro hc
    exact absurd (List.append_eq_nil_iff.mp hc).2 (by simp)
  have hLlast : ∃ ll, L.getLast? = some ll ∧ ¬ sys.internal ll := by
    refine ⟨L.getLast hnonempty, List.getLast?_eq_some_getLast hnonempty, ?_⟩
    have htt2 := ((sys.tight_iff (sys.trace seg) seg h).mp ⟨rfl, htight⟩).2
    exact htt2 (L.getLast hnonempty) (List.getLast?_eq_some_getLast hnonempty)
  obtain ⟨ll, hll_last, hll_ext⟩ := hLlast
  -- `ll` is in the tail `[step.1] ++ rest'` (it's the last element of the nonempty tail).
  have htail_ge : 1 ≤ (([step.1] ++ rest').filter (fun a => decide (¬ sys.internal a))).length := by
    refine List.length_pos_iff.mpr ?_
    intro hnil
    have hll_mem : ll ∈ ([step.1] ++ rest') := by
      have htail_last : ([step.1] ++ rest').getLast? = some ll := by
        have : L.getLast? = ([step.1] ++ rest').getLast? := by
          rw [hLsplit, List.getLast?_append_of_ne_nil _ (by simp)]
        rw [← this, hll_last]
      exact List.mem_of_getLast? htail_last
    have : ll ∉ ([step.1] ++ rest').filter (fun a => decide (¬ sys.internal a)) := by
      rw [hnil]; exact List.not_mem_nil
    exact this (List.mem_filter.mpr ⟨hll_mem, by simpa using hll_ext⟩)
  omega

/-- **The concatenation of two tight executions, the second nonempty and tight, is tight.**
The last transition of `⟨s, A.append B⟩` is `B`'s last, external by `B`'s tightness. -/
theorem LabelledSystem.isTight_append (sys : LabelledSystem State Label)
    (s : State) (A B : Seq (Label × State)) (hA : A.Terminates) (hB : B.Terminates)
    (hB_ne : B.toList hB ≠ []) (hB_tight : sys.IsTight ⟨s, B⟩) :
    sys.IsTight ⟨s, A.append B⟩ := by
  classical
  have hAB : (A.append B).Terminates :=
    ⟨Nat.find hA + Nat.find hB, Stream'.Seq.terminatedAt_append_find hA (Nat.find_spec hB)⟩
  have hAB_list : (⟨s, A.append B⟩ : AlterSeq State Label).trans.toList hAB
      = A.toList hA ++ B.toList hB := Stream'.Seq.toList_append A B hA hB hAB
  obtain ⟨bl, hbl⟩ : ∃ bl, (B.toList hB).getLast? = some bl := by
    cases hb : (B.toList hB).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hb) hB_ne
    | some bl => exact ⟨bl, rfl⟩
  have hbl_ext : ¬ sys.internal bl.1 :=
    sys.tight_getLast_external ⟨s, B⟩ hB hB_tight bl hbl
  have key := sys.tight_iff (sys.trace ⟨s, A.append B⟩) ⟨s, A.append B⟩ hAB
  refine (key.mpr ⟨?_, ?_⟩).2
  · show Seq.filter _ (↑(((⟨s, A.append B⟩ : AlterSeq State Label).trans.toList hAB).map Prod.fst))
        = sys.trace ⟨s, A.append B⟩
    rw [← Seq.map_ofList_pub, Stream'.Seq.ofList_toList]
    unfold LabelledSystem.trace
    rw [Stream'.Seq.filter_map]
    rfl
  · intro lab hlab
    rw [hAB_list, List.getLast?_map, List.getLast?_append_of_ne_nil _ hB_ne, hbl] at hlab
    rw [← Option.some.inj hlab]; exact hbl_ext

/-! ### `internalSuffix`: the maximal all-internal tail of an execution -/

open Classical in
/-- The maximal all-internal tail of `e`: the sub-execution starting right after
`e`'s last *external* transition (or all of `e` if there is none). With `m` the
number of transitions up to and including the last external one (`0` if none),
`internalSuffix e = ⟨e.stateAt m |>.getD e.init, e.trans.drop m⟩`. The split index
`m = length - (trailing all-internal count)` is read off `e.trans.toList`. -/
noncomputable def LabelledSystem.internalSuffix (ls : LabelledSystem State Label)
    (e : AlterSeq State Label) : AlterSeq State Label :=
  if h : e.trans.Terminates then
    let L := e.trans.toList h
    let m := L.length - (L.reverse.takeWhile (fun p => decide (ls.internal p.1))).length
    ⟨(e.stateAt m).getD e.init, e.trans.drop m⟩
  else e

/-- `internalSuffix` preserves the end state (it's a suffix of `e`). -/
theorem LabelledSystem.internalSuffix_endState (ls : LabelledSystem State Label)
    (e : AlterSeq State Label) (h : e.trans.Terminates)
    (h' : (ls.internalSuffix e).trans.Terminates) :
    (ls.internalSuffix e).endState h' = e.endState h := by
  classical
  set m := (e.trans.toList h).length
      - ((e.trans.toList h).reverse.takeWhile (fun p => decide (ls.internal p.1))).length with hm
  have hsuf : ls.internalSuffix e = ⟨(e.stateAt m).getD e.init, e.trans.drop m⟩ := by
    rw [LabelledSystem.internalSuffix, dif_pos h]
  have hmle : m ≤ e.trans.length h := by
    rw [hm, ← Stream'.Seq.length_toList e.trans h]; exact Nat.sub_le _ _
  rw [AlterSeq.endState_congr_pub hsuf h' (Stream'.Seq.drop_terminates_pub h m)]
  exact AlterSeq.endState_drop_suffix e h m hmle

/-! ### `internalSuffix` of tight / segment-extended histories -/

/-- **`internalSuffix` of a segment-extended history (within a segment).** Suppose `preList`
ends with an external transition (`hpre_ext`) and `pref₀` is all-internal (`hpref_int`). Then
the maximal trailing internal run of `⟨init, ofList (preList ++ pref₀)⟩` is exactly `pref₀`, so
the internal suffix starts right after `preList`'s last (external) transition, at the
end-state `ν'` of the `preList` prefix, with transition list `ofList pref₀`. (PEEL step 1a,
within-segment case: `internalSuffix.init = ν'`, `internalSuffix.trans = ofList pref₀`.) -/
theorem LabelledSystem.internalSuffix_append_internal (sys : LabelledSystem State Label)
    (init : State) (preList pref₀ : List (Label × State))
    (hpre_ext : ∀ x, preList.getLast? = some x → ¬ sys.internal x.1)
    (hpref_int : ∀ p ∈ pref₀, sys.internal p.1) :
    sys.internalSuffix ⟨init, Seq.ofList (preList ++ pref₀)⟩
      = ⟨(⟨init, Seq.ofList preList⟩ : AlterSeq State Label).endState
            (Stream'.Seq.terminates_ofList _), Seq.ofList pref₀⟩ := by
  classical
  set full := preList ++ pref₀ with hfull
  have hT : (Seq.ofList full : Seq (Label × State)).Terminates := Stream'.Seq.terminates_ofList _
  have hLtr : (⟨init, Seq.ofList full⟩ : AlterSeq State Label).trans.toList hT = full := by
    change (Seq.ofList full).toList hT = full
    rw [Stream'.Seq.toList_ofList]
  have htw : (full.reverse.takeWhile (fun p => decide (sys.internal p.1))) = pref₀.reverse := by
    rw [hfull, List.reverse_append]
    apply List.takeWhile_append_of_all
    · intro x hx; rw [List.mem_reverse] at hx; simpa using hpref_int x hx
    · intro x hx; rw [List.head?_reverse] at hx; simpa using hpre_ext x hx
  have hm : full.length - (full.reverse.takeWhile (fun p => decide (sys.internal p.1))).length
      = preList.length := by
    rw [htw, List.length_reverse, hfull, List.length_append]; omega
  rw [LabelledSystem.internalSuffix, dif_pos hT]
  simp only [hLtr, hm]
  congr 1
  · rw [AlterSeq.endState_eq_getLast? _ (Stream'.Seq.terminates_ofList _),
      Stream'.Seq.toList_ofList]
    cases hpl : preList with
    | nil =>
      simp only [List.length_nil, AlterSeq.stateAt, Option.getD_some, List.getLast?_nil,
        Option.elim_none]
    | cons hd tl =>
      rw [← hpl]
      have hlen_pos : preList.length = (preList.length - 1) + 1 := by rw [hpl]; simp
      rw [hlen_pos]
      change Option.getD (Option.map Prod.snd
        ((Seq.ofList full).get? (preList.length - 1))) init = _
      rw [Stream'.Seq.ofList_get?, hfull, List.getElem?_append_left (by rw [hpl]; simp),
        ← List.getLast?_eq_getElem?]
      cases hgl : preList.getLast? with
      | none => rw [List.getLast?_eq_none_iff] at hgl; rw [hgl] at hpl; simp at hpl
      | some p => simp [Option.elim]
  · show (Seq.ofList full).drop preList.length = Seq.ofList pref₀
    rw [Stream'.Seq.drop_ofList_pub, hfull, List.drop_left]

end PLTS
