/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Other.Ennreal
import Leslie2.Weak.WeakTransition

/-!
# Kraft-style halt-mass bounds

Generic machinery (over an arbitrary `System`, no `Silent` instance needed) bounding
`ProbabilisticExecution` masses by `1`: the finite-antichain Kraft bounds
`pathWeight_antichain`/`probOf_antichain` (used by `achievableTraceDists_map`), the halting bound
`WeakScheduler.haltMass_tsum_le_one`, the generic `traceProb_le_one`, and the tight-prefix lower
bound `haltMass_trace_le_traceProb`. The limit-free halt-below identity built on top lives in
`Weak/Bounds.lean`.
-/

open Stream'

namespace PLTS

variable {α β State State_C State_A Label : Type} [Silent Label]

open Classical in
/-- **Halting-mass Kraft bound (path-weight level).** For *any* finite set `F` of
transition lists (no prefix-freeness needed — the per-list halting factor
`next ⟨base.init, base.trans ++ ofList t⟩ none` absorbs overlaps), the total
`pathWeight`-times-halt mass from any base is `≤ 1`. Mirrors
`pathWeight_antichain` (induction on the length bound, grouped by `head?`), but
the inductive bound is the *full* one-step mass `b` (kernel on `some`, halt on
`none`), which sums to exactly `1`. -/
theorem ProbabilisticExecution.pathWeight_halt_le_one {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (base : AlterSeq State Label) (F : Finset (List (Label × State))) :
    (∑ t ∈ F, pe.pathWeight base t *
        pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList t)⟩ none) ≤ 1 := by
  classical
  suffices aux : ∀ (N : ℕ) (base : AlterSeq State Label)
      (F : Finset (List (Label × State))),
      (∀ t ∈ F, t.length ≤ N) →
      (∑ t ∈ F, pe.pathWeight base t *
          pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList t)⟩ none) ≤ 1 by
    exact aux (F.sup List.length) base F (fun t ht => Finset.le_sup ht)
  intro N
  induction N with
  | zero =>
    intro base F hlen
    have hsub : F ⊆ {([] : List (Label × State))} := by
      intro t ht
      have : t = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (hlen t ht))
      simp [this]
    calc (∑ t ∈ F, pe.pathWeight base t *
            pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList t)⟩ none)
        ≤ ∑ t ∈ ({([] : List (Label × State))} : Finset _),
            pe.pathWeight base t *
              pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList t)⟩ none :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => bot_le)
      _ = pe.pathWeight base [] *
            pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList [])⟩ none :=
          Finset.sum_singleton _ _
      _ ≤ 1 := by
          rw [show pe.pathWeight base [] = 1 from by
                unfold ProbabilisticExecution.pathWeight; rw [List.reverseRecOn_nil], one_mul,
              Stream'.Seq.ofList_nil, Stream'.Seq.append_nil]
          exact PMF.coe_le_one _ _
  | succ N ih =>
    intro base F hlen
    set T : Finset (Option (Label × State)) := F.image List.head? with hT
    have hmaps : ∀ t ∈ F, t.head? ∈ T := fun t ht => Finset.mem_image_of_mem _ ht
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun t => pe.pathWeight base t *
        pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList t)⟩ none)]
    set b : Option (Label × State) → ENNReal :=
      fun o => o.elim (pe.scheduler.next base none) (fun p => pe.kernel base p) with hb
    have hfib : ∀ j ∈ T, (∑ i ∈ F with i.head? = j,
        pe.pathWeight base i *
          pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList i)⟩ none) ≤ b j := by
      intro j hj
      cases j with
      | none =>
        have hsubn : (F.filter (fun i => i.head? = none)) ⊆ {([] : List (Label × State))} := by
          intro t ht
          rw [Finset.mem_filter] at ht
          have : t = [] := List.head?_eq_none_iff.mp ht.2
          simp [this]
        calc (∑ i ∈ F with i.head? = none,
              pe.pathWeight base i *
                pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList i)⟩ none)
            ≤ ∑ i ∈ ({([] : List (Label × State))} : Finset _),
                pe.pathWeight base i *
                  pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList i)⟩ none :=
              Finset.sum_le_sum_of_subset_of_nonneg hsubn (fun _ _ _ => bot_le)
          _ = pe.pathWeight base [] *
                pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList [])⟩ none :=
              Finset.sum_singleton _ _
          _ = b none := by
              rw [show pe.pathWeight base [] = 1 from by
                    unfold ProbabilisticExecution.pathWeight; rw [List.reverseRecOn_nil], one_mul,
                  Stream'.Seq.ofList_nil, Stream'.Seq.append_nil]
              rfl
      | some p =>
        obtain ⟨l, s'⟩ := p
        set base' : AlterSeq State Label :=
          ⟨base.init, base.trans.append (Seq.cons (l, s') Seq.nil)⟩ with hbase'
        have hfiber_cons : ∀ t ∈ F.filter (fun i => i.head? = some (l, s')),
            t = (l, s') :: t.tail := by
          intro t ht
          rw [Finset.mem_filter] at ht
          exact (List.cons_head?_tail (a := (l, s')) ht.2).symm
        set Ft : Finset (List (Label × State)) := F.filter (fun i => i.head? = some (l, s'))
          with hFt
        have hstep : (∑ i ∈ Ft,
              pe.pathWeight base i *
                pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList i)⟩ none)
            = ∑ i ∈ Ft, pe.kernel base (l, s') *
                (pe.pathWeight base' i.tail *
                  pe.scheduler.next ⟨base'.init, base'.trans.append (Seq.ofList i.tail)⟩ none) := by
          refine Finset.sum_congr rfl fun t ht => ?_
          conv_lhs => rw [hfiber_cons t ht]
          rw [pe.pathWeight_cons base l s' t.tail]
          have hhist : base.trans.append (Seq.ofList ((l, s') :: t.tail))
              = (base.trans.append (Seq.cons (l, s') Seq.nil)).append (Seq.ofList t.tail) := by
            rw [Stream'.Seq.ofList_cons, Stream'.Seq.append_assoc, Stream'.Seq.cons_append,
              Stream'.Seq.nil_append]
          rw [hhist]
          ring
        rw [hstep, ← Finset.mul_sum]
        set Gt : Finset (List (Label × State)) := Ft.image List.tail with hGt
        have hinj : Set.InjOn List.tail (Ft : Set (List (Label × State))) := by
          intro a ha b hb hab
          have ea := hfiber_cons a ha
          have eb := hfiber_cons b hb
          rw [ea, eb, hab]
        have hreindex : (∑ i ∈ Ft, pe.pathWeight base' i.tail *
              pe.scheduler.next ⟨base'.init, base'.trans.append (Seq.ofList i.tail)⟩ none)
            = ∑ u ∈ Gt, pe.pathWeight base' u *
              pe.scheduler.next ⟨base'.init, base'.trans.append (Seq.ofList u)⟩ none := by
          rw [hGt, Finset.sum_image hinj]
        rw [hreindex]
        have hbound : (∑ u ∈ Gt, pe.pathWeight base' u *
            pe.scheduler.next ⟨base'.init, base'.trans.append (Seq.ofList u)⟩ none) ≤ 1 := by
          apply ih base' Gt
          intro u hu
          rw [hGt, Finset.mem_image] at hu
          obtain ⟨t, ht, rfl⟩ := hu
          have htF : t ∈ F := (Finset.mem_filter.mp (hFt ▸ ht)).1
          have htne : t = (l, s') :: t.tail := hfiber_cons t ht
          have hlent : t.length = t.tail.length + 1 := by
            conv_lhs => rw [htne]
            simp
          have hle := hlen t htF
          omega
        calc pe.kernel base (l, s') *
              ∑ u ∈ Gt, pe.pathWeight base' u *
                pe.scheduler.next ⟨base'.init, base'.trans.append (Seq.ofList u)⟩ none
            ≤ pe.kernel base (l, s') * 1 := by gcongr
          _ = b (some (l, s')) := by rw [mul_one, hb]; rfl
    calc (∑ j ∈ T, ∑ i ∈ F with i.head? = j,
            pe.pathWeight base i *
              pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList i)⟩ none)
        ≤ ∑ j ∈ T, b j := Finset.sum_le_sum hfib
      _ ≤ ∑' j : Option (Label × State), b j := ENNReal.sum_le_tsum T
      _ = 1 := by
          rw [ENNReal.tsum_option' b]
          have hkereq : (∑' p : Label × State, pe.kernel base p)
              = ∑' lμ : Label × PMF State, pe.scheduler.next base (some lμ) := by
            calc (∑' p : Label × State, pe.kernel base p)
                = ∑' (l : Label) (s' : State), pe.kernel base (l, s') := by rw [ENNReal.tsum_prod']
              _ = ∑' (l : Label) (s' : State) (μ : PMF State),
                    pe.scheduler.next base (some (l, μ)) * μ s' := by rfl
              _ = ∑' (l : Label) (μ : PMF State) (s' : State),
                    pe.scheduler.next base (some (l, μ)) * μ s' := by
                  refine tsum_congr fun l => ?_; exact ENNReal.tsum_comm
              _ = ∑' (l : Label) (μ : PMF State), pe.scheduler.next base (some (l, μ)) := by
                  refine tsum_congr fun l => tsum_congr fun μ => ?_
                  rw [ENNReal.tsum_mul_left, μ.tsum_coe, mul_one]
              _ = ∑' lμ : Label × PMF State, pe.scheduler.next base (some lμ) := by
                  rw [ENNReal.tsum_prod']
          have hsome : (∑' p : Label × State, b (some p))
              = ∑' lμ : Label × PMF State, pe.scheduler.next base (some lμ) := by
            rw [show (∑' p : Label × State, b (some p))
                  = ∑' p : Label × State, pe.kernel base p from rfl, hkereq]
          rw [hsome, show b none = pe.scheduler.next base none from rfl,
            ← ENNReal.tsum_option' (fun opt => pe.scheduler.next base opt)]
          exact (pe.scheduler.next base).tsum_coe

open Classical in
/-- **Halting-mass Kraft bound (execution level).** For *any* finite set `F` of
terminating executions (no prefix-freeness needed — the per-execution halting
factor `next e.1 none` absorbs overlaps), the total `probOf`-times-halt mass is
`≤ 1`. Mirrors `probOf_antichain` (group by the initial state, reindex onto the
transition lists), bounding each group by `pathWeight_halt_le_one`, then summing
`∑ initState ≤ 1`. -/
theorem ProbabilisticExecution.probOf_halt_le_one {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (F : Finset {e : AlterSeq State Label // e.trans.Terminates}) :
    (∑ e ∈ F, pe.probOf e.1 e.2 * pe.scheduler.next e.1 none) ≤ 1 := by
  classical
  -- Per-element factorisation of `probOf` through `pathWeight`.
  have hfactor : ∀ (s₀ : State) (sq : Seq (Label × State)) (h : sq.Terminates),
      pe.probOf ⟨s₀, sq⟩ h
        = pe.init s₀ * pe.pathWeight ⟨s₀, Seq.nil⟩ (sq.toList h) := by
    intro s₀ sq h
    have heq : (Seq.ofList (sq.toList h) : Seq (Label × State)) = sq :=
      Stream'.Seq.ofList_toList sq h
    generalize hL : sq.toList h = L
    rw [hL] at heq
    subst heq
    exact pe.probOf_eq_pathWeight s₀ L h
  -- The per-element body, in `pathWeight`-times-halt form with base `⟨init, nil⟩`.
  set body : {e : AlterSeq State Label // e.trans.Terminates} → ENNReal :=
    fun e => pe.init (e.1).init
      * (pe.pathWeight ⟨(e.1).init, Seq.nil⟩ ((e.1).trans.toList e.2)
        * pe.scheduler.next ⟨(e.1).init,
            (Seq.nil : Seq (Label × State)).append (Seq.ofList ((e.1).trans.toList e.2))⟩ none)
    with hbody
  have hrw : (∑ e ∈ F, pe.probOf e.1 e.2 * pe.scheduler.next e.1 none) = ∑ e ∈ F, body e := by
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hbody]; simp only
    rw [hfactor (e.1).init (e.1).trans e.2]
    have hhalt : pe.scheduler.next e.1 none
        = pe.scheduler.next ⟨(e.1).init,
            (Seq.nil : Seq (Label × State)).append (Seq.ofList ((e.1).trans.toList e.2))⟩ none := by
      congr 1
      simp only [Stream'.Seq.nil_append]
      rw [Stream'.Seq.ofList_toList]
    rw [hhalt]; ring
  rw [hrw]
  -- Group by the initial state.
  set g : {e // e ∈ F} → State := fun e => (e.1.1).init with hg
  have hmaps : ∀ e ∈ F.attach, g e ∈ F.attach.image g :=
    fun e he => Finset.mem_image_of_mem g he
  rw [← Finset.sum_attach F body]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun e => body e.1)]
  -- Per-fiber bound: the `s₀`-fiber sum is `≤ pe.init s₀`.
  have hfib : ∀ s₀ ∈ F.attach.image g,
      (∑ i ∈ F.attach with g i = s₀, body i.1) ≤ pe.init s₀ := by
    intro s₀ _
    set Fs : Finset {e // e ∈ F} := F.attach.filter (fun i => g i = s₀) with hFs
    have hinit : ∀ i ∈ Fs, (i.1.1).init = s₀ := by
      intro i hi
      rw [hFs, Finset.mem_filter] at hi
      exact hi.2
    set tl : {e // e ∈ F} → List (Label × State) :=
      fun i => (i.1.1).trans.toList i.1.2 with htl
    -- Halt-factor base, abbreviated to keep lines short.
    set hbase : List (Label × State) → AlterSeq State Label :=
      fun u => ⟨s₀, (Seq.nil : Seq (Label × State)).append (Seq.ofList u)⟩ with hhbase
    have hsum_eq : (∑ i ∈ Fs, body i.1)
        = pe.init s₀ * ∑ i ∈ Fs,
            (pe.pathWeight ⟨s₀, Seq.nil⟩ (tl i)
              * pe.scheduler.next (hbase (tl i)) none) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hbody]; simp only
      rw [hinit i hi]
    rw [hsum_eq]
    set Ts : Finset (List (Label × State)) := Fs.image tl with hTs
    have hinj : Set.InjOn tl (Fs : Set {e // e ∈ F}) := by
      intro a ha b hb hab
      apply Subtype.ext
      apply Subtype.ext
      have hia := hinit a ha
      have hib := hinit b hb
      have htrans : a.1.1.trans = b.1.1.trans := by
        have := congrArg Stream'.Seq.ofList hab
        rw [htl] at this
        rw [Stream'.Seq.ofList_toList, Stream'.Seq.ofList_toList] at this
        exact this
      have hi2 : a.1.1.init = b.1.1.init := by rw [hia, hib]
      cases h1 : a.1.1; cases h2 : b.1.1
      simp only [AlterSeq.mk.injEq]
      rw [h1, h2] at hi2 htrans
      exact ⟨hi2, htrans⟩
    have hreindex : (∑ i ∈ Fs,
          (pe.pathWeight ⟨s₀, Seq.nil⟩ (tl i) * pe.scheduler.next (hbase (tl i)) none))
        = ∑ u ∈ Ts, (pe.pathWeight ⟨s₀, Seq.nil⟩ u * pe.scheduler.next (hbase u) none) := by
      rw [hTs, Finset.sum_image hinj]
    rw [hreindex]
    have hbound : (∑ u ∈ Ts,
        (pe.pathWeight ⟨s₀, Seq.nil⟩ u * pe.scheduler.next (hbase u) none)) ≤ 1 := by
      have := pe.pathWeight_halt_le_one ⟨s₀, Seq.nil⟩ Ts
      simpa [hhbase] using this
    calc pe.init s₀ * ∑ u ∈ Ts,
          (pe.pathWeight ⟨s₀, Seq.nil⟩ u * pe.scheduler.next (hbase u) none)
        ≤ pe.init s₀ * 1 := by gcongr
      _ = pe.init s₀ := mul_one _
  calc (∑ j ∈ F.attach.image g, ∑ i ∈ F.attach with g i = j, body i.1)
      ≤ ∑ j ∈ F.attach.image g, pe.init j := Finset.sum_le_sum hfib
    _ ≤ ∑' s₀ : State, pe.init s₀ := ENNReal.sum_le_tsum _
    _ = 1 := by rw [pe.init_eq_initState]; exact pe.initState.tsum_coe

/-- **Total halting mass is `≤ 1`.** -/
theorem WeakScheduler.haltMass_tsum_le_one {sys : System State Label}
    (σ : WeakScheduler sys) (μ : PMF State) :
    (∑' e, σ.haltMass μ e) ≤ 1 := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  rw [show (∑ e ∈ F, σ.haltMass μ e)
      = ∑ e ∈ F, (⟨μ, σ.toScheduler⟩ : ProbabilisticExecution sys).probOf e.1 e.2
          * (⟨μ, σ.toScheduler⟩ : ProbabilisticExecution sys).scheduler.next e.1 none
        from Finset.sum_congr rfl fun e _ => rfl]
  exact (⟨μ, σ.toScheduler⟩ : ProbabilisticExecution sys).probOf_halt_le_one F

/-! ### Tight-prefix split of a transition list

`splitTight L = (L', G)` peels off the maximal trailing run `G` of internal
(τ-labelled) transitions, leaving the *tight* prefix `L'` (empty or ending with
an external transition). Used for the halting/trace lower bound: every halting
run decomposes at its unique tight prefix. -/

open Classical in
/-- One `foldr` step of `splitTight`: prepend `p` to the current split. If the
prefix is still empty we are inside the trailing internal run unless `p` is
external. -/
noncomputable def splitTightStep {State Label : Type} [Silent Label]
    (p : Label × State) (acc : List (Label × State) × List (Label × State)) :
    List (Label × State) × List (Label × State) :=
  if acc.1 = [] then
    (if p.1 = Silent.τ then ([], p :: acc.2) else ([p], acc.2))
  else (p :: acc.1, acc.2)

/-- Split a transition list into its tight prefix and trailing internal run. -/
noncomputable def splitTight {State Label : Type} [Silent Label]
    (L : List (Label × State)) : List (Label × State) × List (Label × State) :=
  L.foldr splitTightStep ([], [])

theorem splitTight_cons {State Label : Type} [Silent Label]
    (p : Label × State) (L : List (Label × State)) :
    splitTight (p :: L) = splitTightStep p (splitTight L) := rfl

open Classical in
/-- **Specification of `splitTight`.** The two parts concatenate to `L`, the
trailing part is all-internal, and the prefix is empty or ends externally. -/
theorem splitTight_spec {State Label : Type} [Silent Label]
    (L : List (Label × State)) :
    (splitTight L).1 ++ (splitTight L).2 = L
      ∧ (∀ p ∈ (splitTight L).2, p.1 = Silent.τ)
      ∧ (∀ q, (splitTight L).1.getLast? = some q → q.1 ≠ Silent.τ) := by
  induction L with
  | nil =>
    refine ⟨rfl, ?_, ?_⟩
    · intro p hp; simp [splitTight] at hp
    · intro q hq; simp [splitTight] at hq
  | cons p L ih =>
    obtain ⟨hrec, hint, hlast⟩ := ih
    rw [splitTight_cons, splitTightStep]
    rcases hsplit : splitTight L with ⟨L', G⟩
    rw [hsplit] at hrec hint hlast
    simp only
    cases L' with
    | nil =>
      rw [if_pos rfl]
      by_cases hp : p.1 = Silent.τ
      · rw [if_pos hp]
        refine ⟨?_, ?_, ?_⟩
        · rw [List.nil_append] at hrec; simpa using hrec
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq'
          · exact hp
          · exact hint q hq'
        · intro q hq; simp at hq
      · rw [if_neg hp]
        refine ⟨?_, hint, ?_⟩
        · rw [List.nil_append] at hrec; simpa using hrec
        · intro q hq
          rw [List.getLast?_singleton] at hq
          obtain rfl : q = p := (Option.some_inj.mp hq).symm
          exact hp
    | cons q L'' =>
      rw [if_neg (by simp)]
      refine ⟨?_, hint, ?_⟩
      · rw [List.cons_append, hrec]
      · intro r hr
        rw [List.getLast?_cons_cons] at hr
        exact hlast r hr

/-! ### Generic trace-probability bound `traceProb_le_one`

The trace probability of any execution is `≤ 1` (a Kraft bound): distinct tight
executions of the same trace are prefix-free, so `probOf_antichain` applies. The
prefix-freeness reduces to a label-list fact (`traceTightLabs_prefix`). -/

open Classical in
/-- **Tight label lists of a fixed trace are prefix-free.** If `a` and `b` are both
tight label lists for the same external trace `τ` and `a` is a prefix of `b`, then
`a = b`: the extra tail `c` has empty external sublist (all internal), so if nonempty
it would make `b` end internally, contradicting tightness. -/
theorem System.traceTightLabs_prefix {S L : Type} [Silent L] (ls : System S L)
    (τ : Seq L) (a b : List L)
    (ha : ls.traceTightLabs τ a) (hb : ls.traceTightLabs τ b) (hpre : a <+: b) :
    a = b := by
  obtain ⟨c, rfl⟩ := hpre
  obtain ⟨hfa, _hla⟩ := ha
  obtain ⟨hfb, hlb⟩ := hb
  -- list-level filter equalities (avoid naming the predicate to dodge binder mismatch)
  rw [Stream'.Seq.ofList_filter] at hfa hfb
  rw [List.filter_append, ← hfa] at hfb
  have hcnil := List.append_right_eq_self.mp (Stream'.Seq.ofList_injective hfb)
  -- every element of `c` is internal
  have hcint : ∀ x ∈ c, x = Silent.τ := by
    intro x hx
    have hf := List.filter_eq_nil_iff.mp hcnil x hx
    by_contra hne
    exact hf (by simp [hne])
  -- conclude c = []
  rcases List.eq_nil_or_concat c with rfl | ⟨ys, y, rfl⟩
  · simp
  · exfalso
    have hgl : (a ++ ys.concat y).getLast? = some y := by
      rw [List.concat_eq_append, List.getLast?_append_of_ne_nil _ (by simp)]
      simp
    have hyint : y = Silent.τ := hcint y (by simp)
    exact hlb y hgl (by rw [hyint])

open Classical in
/-- **Generic Kraft trace bound.** The trace probability of any execution is `≤ 1`. -/
theorem System.traceProb_le_one {S L : Type} [Silent L] (ls : System S L)
    (pe : ProbabilisticExecution ls) (τ : Seq L) :
    ls.traceProb pe τ ≤ 1 := by
  classical
  unfold System.traceProb
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  set g : AlterSeq S L → ENNReal :=
    fun E => if h : E.trans.Terminates then pe.probOf E h else 0 with hg
  set F : Finset (AlterSeq S L) := s.image Subtype.val with hF
  have hterm : ∀ E ∈ F, E.trans.Terminates := by
    intro E hE
    rw [hF, Finset.mem_image] at hE
    obtain ⟨e, _, rfl⟩ := hE
    exact e.2.1
  have hpf : ∀ e (he : e ∈ F) e' (he' : e' ∈ F), e.init = e'.init →
      e.trans.toList (hterm e he) <+: e'.trans.toList (hterm e' he') → e = e' := by
    intro e he e' he' hinit hpre
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp (hF ▸ he)
    obtain ⟨c', _, rfl⟩ := Finset.mem_image.mp (hF ▸ he')
    have htt := (ls.tight_iff τ c.1 (hterm c.1 he)).mp ⟨c.2.2.1, c.2.2.2⟩
    have htt' := (ls.tight_iff τ c'.1 (hterm c'.1 he')).mp ⟨c'.2.2.1, c'.2.2.2⟩
    have hlabpre : (c.1.trans.toList (hterm c.1 he)).map Prod.fst
        <+: (c'.1.trans.toList (hterm c'.1 he')).map Prod.fst := hpre.map Prod.fst
    have hlabeq := ls.traceTightLabs_prefix τ _ _ htt htt' hlabpre
    have hlen : (c.1.trans.toList (hterm c.1 he)).length
        = (c'.1.trans.toList (hterm c'.1 he')).length := by
      have := congrArg List.length hlabeq; simpa using this
    have htl := hpre.eq_of_length hlen
    have htrans : c.1.trans = c'.1.trans := by
      rw [← Stream'.Seq.ofList_toList c.1.trans (hterm c.1 he),
        ← Stream'.Seq.ofList_toList c'.1.trans (hterm c'.1 he'), htl]
    change c.1 = c'.1
    have hmk : c.1 = (⟨c'.1.init, c'.1.trans⟩ : AlterSeq S L) := by rw [← hinit, ← htrans]
    rw [hmk]
  have key := pe.probOf_antichain F hterm hpf
  have e1 : (∑ E ∈ F, g E) = ∑ e ∈ s, pe.probOf e.1 e.2.1 := by
    rw [hF, Finset.sum_image (fun x _ y _ h => Subtype.ext h)]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    show g e.1 = pe.probOf e.1 e.2.1
    simp only [hg, dif_pos e.2.1]
  have e2 : (∑ E ∈ F.attach, pe.probOf E.1 (hterm E.1 E.2)) = ∑ E ∈ F, g E := by
    rw [← Finset.sum_attach F g]
    refine Finset.sum_congr rfl (fun E _ => ?_)
    show pe.probOf E.1 (hterm E.1 E.2) = g E.1
    simp only [hg, dif_pos (hterm E.1 E.2)]
  rw [← e1, ← e2]; exact key

/-! ### Tight-prefix lower bound `haltMass_trace_le_traceProb`

The total halting mass over terminating runs of a fixed trace `τ` is bounded by
the trace probability: every halting run decomposes at its unique tight prefix
(`splitTight`), and the halting mass below a tight prefix `y` is `≤ probOf y`
(`pathWeight_halt_tsum_le_one`). -/

/-- `tsum` version of the relative halting Kraft bound. -/
theorem ProbabilisticExecution.pathWeight_halt_tsum_le_one {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (base : AlterSeq State Label) :
    (∑' t : List (Label × State), pe.pathWeight base t *
        pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList t)⟩ none) ≤ 1 := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun F => pe.pathWeight_halt_le_one base F

open Classical in
/-- **Relative `probOf` factorisation.** Producing `base` then a continuation `G`
factors as `probOf base` times the conditional path weight of `G` from `base`. -/
theorem ProbabilisticExecution.probOf_append_ofList {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (base : AlterSeq State Label) (hb : base.trans.Terminates)
    (G : List (Label × State))
    (hterm : (base.trans.append (Seq.ofList G)).Terminates) :
    pe.probOf ⟨base.init, base.trans.append (Seq.ofList G)⟩ hterm
      = pe.probOf base hb * pe.pathWeight base G := by
  have hM : base.trans = Seq.ofList (base.trans.toList hb) :=
    (Stream'.Seq.ofList_toList base.trans hb).symm
  set M := base.trans.toList hb with hMdef
  have happ : base.trans.append (Seq.ofList G) = Seq.ofList (M ++ G) := by
    rw [Stream'.Seq.ofList_append, ← hM]
  rw [pe.probOf_congr ⟨base.init, base.trans.append (Seq.ofList G)⟩
      ⟨base.init, Seq.ofList (M ++ G)⟩ (by rw [happ]) hterm (happ ▸ hterm)]
  rw [pe.probOf_eq_pathWeight base.init (M ++ G) (happ ▸ hterm),
    pe.pathWeight_append ⟨base.init, Seq.nil⟩ M G]
  have hpw : pe.pathWeight ⟨base.init, (Seq.nil : Seq (Label × State)).append (Seq.ofList M)⟩ G
      = pe.pathWeight base G := by
    rw [Stream'.Seq.nil_append]
    congr 1
    rw [← hM]
  rw [hpw]
  have hpb : pe.probOf base hb = pe.init base.init * pe.pathWeight ⟨base.init, Seq.nil⟩ M := by
    rw [pe.probOf_congr base ⟨base.init, Seq.ofList M⟩ (by rw [← hM]) hb
        (Stream'.Seq.terminates_ofList M),
      pe.probOf_eq_pathWeight base.init M (Stream'.Seq.terminates_ofList M)]
  rw [hpb]; ring

/-- An all-internal label list filters to the empty trace. -/
private theorem ofList_filter_internal_nil {L : Type} [Silent L] (ls : List L)
    (h : ∀ x ∈ ls, x = Silent.τ) :
    (Seq.ofList ls).filter (fun l => ¬ l = Silent.τ) = Seq.nil := by
  rw [Stream'.Seq.ofList_filter, ← Stream'.Seq.ofList_nil]
  congr 1
  rw [List.filter_eq_nil_iff]
  intro x hx; simp [h x hx]

/-- The trace of a terminating execution is the filtered `ofList` of its label list. -/
private theorem trace_eq_extLabs {S L : Type} [Silent L] (ls : System S L)
    (e : AlterSeq S L) (h : e.trans.Terminates) :
    ls.trace e
      = (Seq.ofList ((e.trans.toList h).map Prod.fst)).filter (fun l => ¬ l = Silent.τ) := by
  have h1 : (Seq.ofList ((e.trans.toList h).map Prod.fst) : Seq L) = e.trans.map Prod.fst := by
    rw [← Seq.map_ofList_pub, Stream'.Seq.ofList_toList]
  rw [h1]
  unfold System.trace
  rw [Stream'.Seq.filter_map Prod.fst (fun l => ¬ (l = Silent.τ))]
  rfl

/-- The tight prefix of a terminating, trace-`τ` execution's label list is tight for `τ`. -/
private theorem splitTight_traceTightLabs {S L : Type} [Silent L] (ls : System S L)
    (e : AlterSeq S L) (h : e.trans.Terminates) :
    ls.traceTightLabs (ls.trace e) ((splitTight (e.trans.toList h)).1.map Prod.fst) := by
  obtain ⟨hrec, hint, hlast⟩ := splitTight_spec (e.trans.toList h)
  set L₀ := e.trans.toList h with hL₀
  set L' := (splitTight L₀).1 with hL'
  set G := (splitTight L₀).2 with hG
  refine ⟨?_, ?_⟩
  · rw [trace_eq_extLabs ls e h, ← hL₀]
    have hLmap : L₀.map Prod.fst = L'.map Prod.fst ++ G.map Prod.fst := by
      rw [← List.map_append, hrec]
    rw [hLmap, Stream'.Seq.ofList_append,
      Stream'.Seq.filter_append (fun l => ¬ l = Silent.τ) _ _ (Stream'.Seq.terminates_ofList _),
      ofList_filter_internal_nil (G.map Prod.fst) (by
        intro x hx; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact hint p hp),
      Stream'.Seq.append_nil]
  · intro l hl
    rw [List.getLast?_map] at hl
    cases hq : L'.getLast? with
    | none => rw [hq] at hl; simp at hl
    | some q =>
      rw [hq] at hl
      obtain rfl : q.1 = l := Option.some_inj.mp hl
      exact hlast q hq

open Classical in
/-- **Trace halting lower bound.** The total halting mass over terminating runs
of a fixed trace `τ` is bounded by the trace probability `traceProb τ`: each such
run decomposes at its unique tight prefix `y`, and the halting mass below `y` is
`≤ probOf y` (`pathWeight_halt_tsum_le_one`). -/
theorem ProbabilisticExecution.haltMass_trace_le_traceProb {State Label : Type} [Silent Label]
    {sys : System State Label} (pe : ProbabilisticExecution sys) (τ : Seq Label) :
    (∑' e : {e : AlterSeq State Label // e.trans.Terminates ∧ sys.trace e = τ},
       pe.probOf e.1 e.2.1 * pe.scheduler.next e.1 none) ≤ sys.traceProb pe τ := by
  set A := {e : AlterSeq State Label // e.trans.Terminates ∧ sys.trace e = τ} with hA
  set g : A → ENNReal := fun e => pe.probOf e.1 e.2.1 * pe.scheduler.next e.1 none with hg
  -- the tight prefix as an `IsTight`, trace-`τ` execution
  have hφ_spec : ∀ (E : AlterSeq State Label) (hEt : E.trans.Terminates) (hEtr : sys.trace E = τ),
      sys.trace ⟨E.init, Seq.ofList (splitTight (E.trans.toList hEt)).1⟩ = τ
        ∧ sys.IsTight ⟨E.init, Seq.ofList (splitTight (E.trans.toList hEt)).1⟩ := by
    intro E hEt hEtr
    refine (sys.tight_iff τ ⟨E.init, Seq.ofList (splitTight (E.trans.toList hEt)).1⟩
      (Stream'.Seq.terminates_ofList _)).mpr ?_
    rw [Stream'.Seq.toList_ofList]
    have h2 := splitTight_traceTightLabs sys E hEt
    rw [hEtr] at h2
    exact h2
  set φ : A → {e : AlterSeq State Label //
      e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e} := fun e =>
    ⟨⟨e.1.init, Seq.ofList (splitTight (e.1.trans.toList e.2.1)).1⟩,
      Stream'.Seq.terminates_ofList _, (hφ_spec e.1 e.2.1 e.2.2).1, (hφ_spec e.1 e.2.1 e.2.2).2⟩
    with hφ
  -- transition-list decomposition `e.trans = ofList L' ++ ofList G`
  have hdecomp : ∀ e : A, e.1.trans
      = (Seq.ofList (splitTight (e.1.trans.toList e.2.1)).1).append
          (Seq.ofList (splitTight (e.1.trans.toList e.2.1)).2) := by
    intro e
    obtain ⟨hrec, _, _⟩ := splitTight_spec (e.1.trans.toList e.2.1)
    rw [← Stream'.Seq.ofList_append, hrec, Stream'.Seq.ofList_toList]
  -- per-fiber bound
  have hfiber : ∀ y, (∑' e : {e : A // φ e = y}, g e.1) ≤ pe.probOf y.1 y.2.1 := by
    intro y
    set f : List (Label × State) → ENNReal :=
      fun G₀ => pe.probOf y.1 y.2.1 * pe.pathWeight y.1 G₀ *
        pe.scheduler.next ⟨y.1.init, y.1.trans.append (Seq.ofList G₀)⟩ none with hf
    have he1 : ∀ e : {e : A // φ e = y}, e.1.1
        = ⟨y.1.init, y.1.trans.append
            (Seq.ofList (splitTight (e.1.1.trans.toList e.1.2.1)).2)⟩ := by
      intro e
      have hcfg : (φ e.1).1 = y.1 := by rw [e.2]
      have hinit : e.1.1.init = y.1.init := by
        have := congrArg AlterSeq.init hcfg; simpa [hφ] using this
      have htrans : Seq.ofList (splitTight (e.1.1.trans.toList e.1.2.1)).1 = y.1.trans := by
        have := congrArg AlterSeq.trans hcfg; simpa [hφ] using this
      have hd := hdecomp e.1
      rw [htrans] at hd
      refine (Eq.symm ?_)
      rw [← hinit, ← hd]
    have htail_eq : ∀ e : {e : A // φ e = y},
        g e.1 = f (splitTight (e.1.1.trans.toList e.1.2.1)).2 := by
      intro e
      set G₀ := (splitTight (e.1.1.trans.toList e.1.2.1)).2 with hG₀
      have htr_e : e.1.1.trans = y.1.trans.append (Seq.ofList G₀) :=
        congrArg AlterSeq.trans (he1 e)
      simp only [hg]
      rw [pe.probOf_congr e.1.1 ⟨y.1.init, y.1.trans.append (Seq.ofList G₀)⟩ (he1 e) e.1.2.1
          (htr_e ▸ e.1.2.1),
        show pe.scheduler.next e.1.1 none
          = pe.scheduler.next ⟨y.1.init, y.1.trans.append (Seq.ofList G₀)⟩ none from by rw [he1 e],
        pe.probOf_append_ofList y.1 y.2.1 G₀ (htr_e ▸ e.1.2.1)]
    have hinj : Function.Injective
        (fun e : {e : A // φ e = y} => (splitTight (e.1.1.trans.toList e.1.2.1)).2) := by
      intro e e' heq
      apply Subtype.ext
      apply Subtype.ext
      rw [he1 e, he1 e']
      have heq' : (splitTight (e.1.1.trans.toList e.1.2.1)).2
          = (splitTight (e'.1.1.trans.toList e'.1.2.1)).2 := heq
      rw [heq']
    calc (∑' e : {e : A // φ e = y}, g e.1)
        = ∑' e : {e : A // φ e = y}, f ((splitTight (e.1.1.trans.toList e.1.2.1)).2) :=
          tsum_congr htail_eq
      _ ≤ ∑' G₀ : List (Label × State), f G₀ :=
          ENNReal.tsum_comp_le_tsum_of_injective hinj f
      _ = pe.probOf y.1 y.2.1 * ∑' G₀ : List (Label × State),
            (pe.pathWeight y.1 G₀ *
              pe.scheduler.next ⟨y.1.init, y.1.trans.append (Seq.ofList G₀)⟩ none) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr (fun G₀ => ?_)
          rw [hf]; ring
      _ ≤ pe.probOf y.1 y.2.1 * 1 := by
          gcongr; exact pe.pathWeight_halt_tsum_le_one y.1
      _ = pe.probOf y.1 y.2.1 := mul_one _
  -- assemble via the fibre partition of the tight-prefix map
  calc (∑' e : A, g e)
      = ∑' p : (Σ y, {e : A // φ e = y}), g (Equiv.sigmaFiberEquiv φ p) :=
        (Equiv.tsum_eq (Equiv.sigmaFiberEquiv φ) g).symm
    _ = ∑' y, ∑' e : {e : A // φ e = y}, g e.1 := by rw [ENNReal.tsum_sigma']; rfl
    _ ≤ ∑' y, pe.probOf y.1 y.2.1 := ENNReal.tsum_le_tsum hfiber
    _ = sys.traceProb pe τ := rfl

end PLTS
