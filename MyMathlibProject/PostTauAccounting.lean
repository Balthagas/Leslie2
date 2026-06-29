/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.TraceProbBound

/-!
# Post-τ accounting

The general lemma `LabelledSystem.traceProb_eq_one_of_asHalt`: if a process almost
surely halts and every halting execution has the same trace `τ`, then
`traceProb τ = 1`. Its bridge `Scheduler.haltMass_le_traceProb` is a reusable
post-τ-accounting bound (halt mass on trace-`τ` executions ≤ `traceProb τ`), built
on a Kraft-style "total halt mass from a prefix ≤ probOf(prefix)" bound. Generic in
the system; lives upstream of `WeakConstruction`.
-/

open Stream'

namespace PLTS

variable {α β State State_C State_A Label : Type}

/-! ## Post-τ-accounting: trailing internal transitions don't affect the trace
probability of an a.s.-halting process.

This section builds the GENERAL lemma `traceProb_eq_one_of_asHalt`: if a process
almost surely halts (`∑ haltMass = 1`) and every halting execution has the same
trace `τ`, then `traceProb τ = 1`. The proof rests on the bridge
`haltMass_le_traceProb` — the *reusable post-τ accounting* — which bounds the
halt-mass on trace-`τ` executions by `traceProb τ`. The crux is a Kraft-style
"total halt mass from a prefix ≤ probOf(prefix)" bound. -/

/-- **Splitting off the trailing `p`-run of a list.** With `m = |L| - |trailing
p-run|`, the prefix `L.take m` is empty or ends with a `¬p` element, while the
suffix `L.drop m` consists entirely of `p`-elements. -/
private theorem split_trailing_run {α : Type} (p : α → Bool) (L : List α) :
    let m := L.length - (L.reverse.takeWhile p).length
    L.take m = (L.reverse.dropWhile p).reverse ∧
    L.drop m = (L.reverse.takeWhile p).reverse ∧
    (∀ x ∈ L.drop m, p x) ∧
    (∀ y, (L.take m).getLast? = some y → ¬ p y) := by
  intro m
  have hrev : L.reverse.takeWhile p ++ L.reverse.dropWhile p = L.reverse :=
    List.takeWhile_append_dropWhile
  have hlen_dw : (L.reverse.dropWhile p).length = m := by
    have h1 : (L.reverse.takeWhile p).length + (L.reverse.dropWhile p).length = L.length := by
      have := congrArg List.length hrev
      rw [List.length_append, List.length_reverse] at this
      omega
    omega
  have hLsplit : L = (L.reverse.dropWhile p).reverse ++ (L.reverse.takeWhile p).reverse := by
    have := congrArg List.reverse hrev
    rw [List.reverse_reverse, List.reverse_append] at this
    exact this.symm
  have hlenrev : (L.reverse.dropWhile p).reverse.length = m := by
    rw [List.length_reverse, hlen_dw]
  have htake : L.take m = (L.reverse.dropWhile p).reverse := by
    conv_lhs => rw [hLsplit]
    rw [← hlenrev, List.take_left]
  have hdrop : L.drop m = (L.reverse.takeWhile p).reverse := by
    conv_lhs => rw [hLsplit]
    rw [← hlenrev, List.drop_left]
  refine ⟨htake, hdrop, ?_, ?_⟩
  · intro x hx
    rw [hdrop, List.mem_reverse] at hx
    have himp : ∀ {l : List α} {y : α}, y ∈ l.takeWhile p → p y := by
      intro l
      induction l with
      | nil => intro y hy; simp [List.takeWhile] at hy
      | cons hd tl IH =>
        intro y hy
        cases hp : p hd
        · simp [List.takeWhile, hp] at hy
        · simp only [List.takeWhile, hp, List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact hp
          · exact IH hy
    exact himp hx
  · intro y hy
    rw [htake, List.getLast?_reverse] at hy
    cases hd : (L.reverse.dropWhile p).head? with
    | none => rw [hd] at hy; simp at hy
    | some z =>
      rw [hd] at hy
      obtain rfl : z = y := Option.some.inj hy
      have := List.head?_dropWhile_not p L.reverse
      rw [hd] at this
      simpa using this

open Classical in
/-- The **tight-prefix transition list** of a terminating execution `e`: `e`'s
transition list with its trailing all-internal run removed (the truncation right
after the last external transition). -/
noncomputable def LabelledSystem.tightPrefixList (sys : LabelledSystem State Label)
    (e : AlterSeq State Label) (h : e.trans.Terminates) : List (Label × State) :=
  let L := e.trans.toList h
  L.take (L.length - (L.reverse.takeWhile (fun p => decide (sys.internal p.1))).length)

/-- **Tight-prefix decomposition of a terminating execution.** Every terminating
execution `e` splits as its tight prefix `tightPrefixList` (the truncation right
after its last external transition) extended by an all-internal tail. The tail is
all-internal, and the prefix `⟨e.init, ofList (tightPrefixList e)⟩` is terminating,
*tight*, with the *same trace* as `e`, and the full list factors as `prefix ++ tail`. -/
theorem LabelledSystem.tightPrefixList_spec (sys : LabelledSystem State Label)
    (e : AlterSeq State Label) (h : e.trans.Terminates) :
    ∃ tailList : List (Label × State),
      e.trans.toList h = sys.tightPrefixList e h ++ tailList ∧
      (∀ x ∈ tailList, sys.internal x.1) ∧
      sys.IsTight ⟨e.init, Seq.ofList (sys.tightPrefixList e h)⟩ ∧
      sys.trace ⟨e.init, Seq.ofList (sys.tightPrefixList e h)⟩ = sys.trace e := by
  classical
  set P : Label × State → Bool := fun p => decide (sys.internal p.1) with hP
  set L := e.trans.toList h with hL
  set m := L.length - (L.reverse.takeWhile P).length with hm
  have hpfx : sys.tightPrefixList e h = L.take m := rfl
  obtain ⟨_htake, _hdrop, hdrop_int, htake_ext⟩ := split_trailing_run P L
  rw [hpfx]
  refine ⟨L.drop m, (List.take_append_drop m L).symm, ?_, ?_, ?_⟩
  · -- the tail is all-internal
    intro x hx
    have := hdrop_int x hx
    simpa [hP] using this
  · -- the prefix is tight
    -- tightness via `tight_iff`: prove `traceTightLabs (trace pref) (label list of pref)`.
    have hpref_term : (Seq.ofList (L.take m) : Seq (Label × State)).Terminates :=
      Stream'.Seq.terminates_ofList _
    set pref : AlterSeq State Label := ⟨e.init, Seq.ofList (L.take m)⟩ with hpref
    have htoList : pref.trans.toList hpref_term = L.take m := by
      change (Seq.ofList (L.take m)).toList hpref_term = L.take m
      rw [Stream'.Seq.toList_ofList]
    refine ((sys.tight_iff (sys.trace pref) pref hpref_term).mpr ⟨?_, ?_⟩).2
    · -- part 1 of `traceTightLabs`: filter of the label list equals the trace.
      rw [htoList]
      show Seq.filter (fun l => ¬ sys.internal l) (Seq.ofList ((L.take m).map Prod.fst))
          = sys.trace pref
      rw [hpref]
      unfold LabelledSystem.trace
      change Seq.filter (fun l => ¬ sys.internal l) (Seq.ofList ((L.take m).map Prod.fst))
          = Seq.map Prod.fst
            (Seq.filter (fun p => ¬ sys.internal p.1) (Seq.ofList (L.take m)))
      rw [← Seq.map_ofList_pub, Stream'.Seq.filter_map Prod.fst (fun l => ¬ sys.internal l)]
      rfl
    · -- part 2: the prefix's last label (if any) is external.
      rw [htoList, List.getLast?_map]
      intro lab hlab
      cases hgl : (L.take m).getLast? with
      | none => rw [hgl] at hlab; simp at hlab
      | some y =>
        rw [hgl] at hlab
        obtain rfl : lab = y.1 := (Option.some.inj hlab).symm
        have := htake_ext y hgl
        simpa [hP] using this
  · -- same trace: the all-internal tail does not affect the trace
    have hsplit : e.trans.toList h = L.take m ++ L.drop m := (List.take_append_drop m L).symm
    have hetrans : e.trans = Seq.ofList (L.take m ++ L.drop m) := by
      have hofl : (Seq.ofList (e.trans.toList h) : Seq (Label × State)) = e.trans :=
        Stream'.Seq.ofList_toList e.trans h
      rw [hsplit] at hofl; exact hofl.symm
    have htrace_e : sys.trace e = sys.trace ⟨e.init, Seq.ofList (L.take m ++ L.drop m)⟩ := by
      cases e; simp only at hetrans ⊢; rw [hetrans]
    rw [htrace_e]
    exact (sys.trace_append_internal e.init (L.take m) (L.drop m)
      (fun x hx => by have := hdrop_int x hx; simpa [hP] using this)).symm

open Classical in
/-- **Tightness from a scheduler that is silent past a nonempty trace.** If a scheduler `σ`
emits nothing (`next e' (some _) = 0`) at every history `e'` whose external trace is already
nonempty, then any positive-probability execution `e` with nonempty external trace is tight: it
cannot have a trailing internal transition, since that transition would sit at a history with
the same (nonempty) trace where `σ` emits nothing, forcing the corresponding kernel — hence the
whole `probOf` — to vanish. This is the H1-tightness discharge for `expandCont` (silent via L5).
-/
theorem LabelledSystem.isTight_of_silent_past_trace {State Label : Type}
    (sys : LabelledSystem State Label) (σ : Scheduler sys.toSystem) (μ_init : PMF State)
    (hsilent : ∀ (e' : AlterSeq State Label), e'.trans.Terminates → sys.trace e' ≠ Seq.nil →
      ∀ a : Label × PMF State, σ.next e' (some a) = 0)
    (e : AlterSeq State Label) (h : e.trans.Terminates) (htr_ne : sys.trace e ≠ Seq.nil)
    (hprob : (⟨μ_init, σ⟩ : ProbabilisticExecution sys.toSystem).probOf e h ≠ 0) :
    sys.IsTight e := by
  classical
  obtain ⟨tailList, hsplit, htail_int, hpref_tight, hpref_tr⟩ :=
    sys.tightPrefixList_spec e h
  set preList := sys.tightPrefixList e h with hpre
  -- `probOf e = init · pathWeight (toList)`, with `toList = preList ++ tailList`.
  have hpe : (⟨μ_init, σ⟩ : ProbabilisticExecution sys.toSystem).probOf e h
      = (⟨μ_init, σ⟩ : ProbabilisticExecution sys.toSystem).probOf
          ⟨e.init, Seq.ofList (e.trans.toList h)⟩ (by rw [Stream'.Seq.ofList_toList]; exact h) := by
    refine (⟨μ_init, σ⟩ : ProbabilisticExecution sys.toSystem).probOf_congr e
      ⟨e.init, Seq.ofList (e.trans.toList h)⟩ ?_ h (by rw [Stream'.Seq.ofList_toList]; exact h)
    cases e with
    | mk ei et => simp only; rw [Stream'.Seq.ofList_toList]
  rw [ProbabilisticExecution.probOf_eq_pathWeight (⟨μ_init, σ⟩
      : ProbabilisticExecution sys.toSystem) e.init (e.trans.toList h)
    (by rw [Stream'.Seq.ofList_toList]; exact h)] at hpe
  -- It suffices that the tail is empty (then `e = prefix`, which is tight).
  cases htailList : tailList with
  | nil =>
    -- empty tail: `e.trans = ofList preList`, so `e` is the (tight) prefix.
    have he_eq : e = ⟨e.init, Seq.ofList preList⟩ := by
      have htoL : e.trans.toList h = preList := by rw [hsplit, htailList, List.append_nil]
      cases e with
      | mk ei et =>
        simp only at htoL ⊢
        rw [← htoL, Stream'.Seq.ofList_toList]
    rw [he_eq]; exact hpref_tight
  | cons lst rest =>
    -- nonempty tail: front-peel its first transition `lst`, whose boundary kernel vanishes.
    exfalso
    rw [hsplit, htailList,
      ProbabilisticExecution.pathWeight_append (⟨μ_init, σ⟩
          : ProbabilisticExecution sys.toSystem) e.init preList _,
      ProbabilisticExecution.pathWeight_cons (⟨μ_init, σ⟩
          : ProbabilisticExecution sys.toSystem) ⟨e.init, Seq.ofList preList⟩ lst.1 lst.2 _] at hpe
    have hker0 : (⟨μ_init, σ⟩ : ProbabilisticExecution sys.toSystem).kernel
        ⟨e.init, Seq.ofList preList⟩ (lst.1, lst.2) = 0 := by
      unfold ProbabilisticExecution.kernel
      refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
      have htr_pref : sys.trace (⟨e.init, Seq.ofList preList⟩ : AlterSeq State Label)
          ≠ Seq.nil := by
        rw [hpref_tr]; exact htr_ne
      change σ.next ⟨e.init, Seq.ofList preList⟩ (some (lst.1, μ)) * μ lst.2 = 0
      rw [hsilent ⟨e.init, Seq.ofList preList⟩ (Stream'.Seq.terminates_ofList _) htr_pref
        (lst.1, μ), zero_mul]
    rw [hker0] at hpe
    apply hprob
    rw [hpe]; ring


end PLTS
