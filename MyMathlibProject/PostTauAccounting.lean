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

/-- **Halt-augmented kernel bound.** The halt mass `next e none` plus the total
one-step kernel mass is `≤ 1` (they are disjoint sub-events of the single PMF
`next e`). -/
theorem ProbabilisticExecution.next_none_add_kernel_tsum_le_one {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) :
    pe.scheduler.next e none + (∑' p : Label × State, pe.kernel e p) ≤ 1 := by
  -- `∑ kernel = ∑_{l,μ} next (some (l, μ)) = ∑_{lμ} next (some lμ)`.
  have hkernel : (∑' p : Label × State, pe.kernel e p)
      = ∑' lμ : Label × PMF State, pe.scheduler.next e (some lμ) := by
    rw [ENNReal.tsum_prod' (f := fun lμ : Label × PMF State => pe.scheduler.next e (some lμ))]
    rw [ENNReal.tsum_prod']
    refine tsum_congr fun l => ?_
    calc (∑' s' : State, pe.kernel e (l, s'))
        = ∑' (s' : State) (μ : PMF State),
            pe.scheduler.next e (some (l, μ)) * μ s' := by rfl
      _ = ∑' (μ : PMF State) (s' : State),
            pe.scheduler.next e (some (l, μ)) * μ s' := ENNReal.tsum_comm
      _ = ∑' (μ : PMF State), pe.scheduler.next e (some (l, μ)) := by
            refine tsum_congr fun μ => ?_
            rw [ENNReal.tsum_mul_left, μ.tsum_coe, mul_one]
  rw [hkernel]
  -- `∑_o next o = next none + (≠ none part)`, and the `≠ none part` reindexes to `∑_{lμ}`.
  have hsplit := ENNReal.tsum_eq_add_tsum_ite (f := fun o => pe.scheduler.next e o)
    (none : Option (Label × PMF State))
  refine le_of_eq_of_le ?_ (le_of_eq (pe.scheduler.next e).tsum_coe)
  rw [hsplit]
  have hreindex : (∑' lμ : Label × PMF State, pe.scheduler.next e (some lμ))
      = ∑' o : Option (Label × PMF State),
          (if o = none then 0 else pe.scheduler.next e o) := by
    refine Eq.trans ?_ (Function.Injective.tsum_eq (g := (Option.some : (Label × PMF State) → _))
      (f := fun o => if o = none then 0 else pe.scheduler.next e o)
      (fun _ _ h => Option.some.inj h) ?_)
    · refine tsum_congr fun lμ => ?_
      simp
    · intro o ho
      cases o with
      | none => simp [Function.mem_support] at ho
      | some lμ => exact ⟨lμ, rfl⟩
  rw [hreindex]
  congr 1
  refine tsum_congr fun o => ?_
  congr 1

/-- **Total halt mass from a base is `≤ 1` (path-weight form, Kraft-style).** For
any base and *any* finite set `F` of transition tails, the sum over `F` of the
path weight of `t` times the halt probability at the end of `t` is `≤ 1`. No
prefix-freeness is required: the halt events are disjoint sub-events of the
branching tree. Proven by induction on the maximum tail length, grouping by the
first transition (mirroring `pathWeight_antichain`, with the halt factor). -/
theorem ProbabilisticExecution.pathWeight_halt_le_one {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (base : AlterSeq State Label) (F : Finset (List (Label × State))) :
    (∑ t ∈ F, pe.pathWeight base t
        * pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList t)⟩ none) ≤ 1 := by
  classical
  suffices aux : ∀ (N : ℕ) (base : AlterSeq State Label)
      (F : Finset (List (Label × State))),
      (∀ t ∈ F, t.length ≤ N) →
      (∑ t ∈ F, pe.pathWeight base t
          * pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList t)⟩ none) ≤ 1 by
    exact aux (F.sup List.length) base F (fun t ht => Finset.le_sup ht)
  intro N
  induction N with
  | zero =>
    intro base F hlen
    -- every t ∈ F has length ≤ 0, so t = []; hence F ⊆ {[]}
    have hsub : F ⊆ {([] : List (Label × State))} := by
      intro t ht
      have : t = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (hlen t ht))
      simp [this]
    calc (∑ t ∈ F, pe.pathWeight base t
            * pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList t)⟩ none)
        ≤ ∑ t ∈ ({([] : List (Label × State))} : Finset _),
            pe.pathWeight base t
              * pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList t)⟩ none :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => bot_le)
      _ = pe.pathWeight base []
            * pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList [])⟩ none :=
          Finset.sum_singleton _ _
      _ ≤ 1 := by
          rw [show pe.pathWeight base [] = 1 by
                unfold ProbabilisticExecution.pathWeight; rw [List.reverseRecOn_nil], one_mul,
              Stream'.Seq.ofList_nil, Stream'.Seq.append_nil]
          exact le_trans (le_add_right le_rfl)
            (pe.next_none_add_kernel_tsum_le_one ⟨base.init, base.trans⟩)
  | succ N ih =>
    intro base F hlen
    -- Group by the head (as `Option`, so no `Inhabited` is needed).
    set T : Finset (Option (Label × State)) := F.image List.head? with hT
    have hmaps : ∀ t ∈ F, t.head? ∈ T := fun t ht => Finset.mem_image_of_mem _ ht
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun t => pe.pathWeight base t
        * pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList t)⟩ none)]
    -- per-fiber bound `b`: halt mass on `none` (empty tail), kernel mass on `some p`.
    set b : Option (Label × State) → ENNReal :=
      fun o => o.elim (pe.scheduler.next ⟨base.init, base.trans⟩ none)
        (fun p => pe.kernel base p) with hb
    have hfib : ∀ j ∈ T, (∑ i ∈ F with i.head? = j,
        pe.pathWeight base i
          * pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList i)⟩ none) ≤ b j := by
      intro j _hj
      cases j with
      | none =>
        -- the fiber over `none` is `{[]}` (or empty): `t.head? = none ↔ t = []`.
        have hsub : (F.filter (fun i => i.head? = none)) ⊆ {([] : List (Label × State))} := by
          intro t ht
          rw [Finset.mem_filter, List.head?_eq_none_iff] at ht
          simp [ht.2]
        calc (∑ i ∈ F with i.head? = none,
                pe.pathWeight base i
                  * pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList i)⟩ none)
            ≤ ∑ i ∈ ({([] : List (Label × State))} : Finset _),
                pe.pathWeight base i
                  * pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList i)⟩ none :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => bot_le)
          _ = b none := by
              rw [Finset.sum_singleton,
                show pe.pathWeight base [] = 1 by
                  unfold ProbabilisticExecution.pathWeight; rw [List.reverseRecOn_nil], one_mul,
                Stream'.Seq.ofList_nil, Stream'.Seq.append_nil]
              rfl
      | some p =>
        obtain ⟨l, s'⟩ := p
        set base' : AlterSeq State Label :=
          ⟨base.init, base.trans.append (Seq.cons (l, s') Seq.nil)⟩ with hbase'
        set Ft : Finset (List (Label × State)) := F.filter (fun i => i.head? = some (l, s'))
          with hFt
        have hfiber_cons : ∀ t ∈ Ft, t = (l, s') :: t.tail := by
          intro t ht
          rw [hFt, Finset.mem_filter] at ht
          exact (List.cons_head?_tail (a := (l, s')) ht.2).symm
        -- history identity: appending `(l,s') :: t.tail` from `base` is appending
        -- `t.tail` from `base'`.
        have hhist : ∀ tl : List (Label × State),
            base.trans.append (Seq.ofList ((l, s') :: tl))
              = base'.trans.append (Seq.ofList tl) := by
          intro tl
          rw [hbase', Stream'.Seq.ofList_cons, Stream'.Seq.append_assoc, Stream'.Seq.cons_append,
            Stream'.Seq.nil_append]
        -- step 1: rewrite each fiber summand via `pathWeight_cons` and `hhist`.
        have hstep : (∑ i ∈ Ft,
            pe.pathWeight base i
              * pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList i)⟩ none)
            = ∑ i ∈ Ft, pe.kernel base (l, s')
                * (pe.pathWeight base' i.tail
                    * pe.scheduler.next ⟨base'.init, base'.trans.append (Seq.ofList i.tail)⟩
                        none) := by
          refine Finset.sum_congr rfl fun t ht => ?_
          conv_lhs => rw [hfiber_cons t ht]
          rw [pe.pathWeight_cons base l s' t.tail]
          rw [hhist t.tail]
          rw [show base.init = base'.init from rfl]
          ring
        rw [hstep, ← Finset.mul_sum]
        -- step 2: reindex the tail sum onto `Gt := Ft.image List.tail`.
        set Gt : Finset (List (Label × State)) := Ft.image List.tail with hGt
        have hinj : Set.InjOn List.tail (Ft : Set (List (Label × State))) := by
          intro a ha b hb hab
          rw [hfiber_cons a ha, hfiber_cons b hb, hab]
        have hreindex : (∑ i ∈ Ft, pe.pathWeight base' i.tail
              * pe.scheduler.next ⟨base'.init, base'.trans.append (Seq.ofList i.tail)⟩ none)
            = ∑ u ∈ Gt, pe.pathWeight base' u
              * pe.scheduler.next ⟨base'.init, base'.trans.append (Seq.ofList u)⟩ none := by
          rw [hGt, Finset.sum_image hinj]
        rw [hreindex]
        -- step 3: bound the tail sum by `1` via `ih base' Gt`.
        have hbound : (∑ u ∈ Gt, pe.pathWeight base' u
            * pe.scheduler.next ⟨base'.init, base'.trans.append (Seq.ofList u)⟩ none) ≤ 1 := by
          apply ih base' Gt
          intro u hu
          rw [hGt, Finset.mem_image] at hu
          obtain ⟨t, ht, rfl⟩ := hu
          have htF : t ∈ F := (Finset.mem_filter.mp (hFt ▸ ht)).1
          have htne : t = (l, s') :: t.tail := hfiber_cons t ht
          have hlent : t.length = t.tail.length + 1 := by
            conv_lhs => rw [htne]
            rw [List.length_cons]
          have hle := hlen t htF
          omega
        calc pe.kernel base (l, s')
              * ∑ u ∈ Gt, pe.pathWeight base' u
                * pe.scheduler.next ⟨base'.init, base'.trans.append (Seq.ofList u)⟩ none
            ≤ pe.kernel base (l, s') * 1 := by gcongr
          _ = b (some (l, s')) := by rw [mul_one, hb]; rfl
    calc (∑ j ∈ T, ∑ i ∈ F with i.head? = j,
            pe.pathWeight base i
              * pe.scheduler.next ⟨base.init, base.trans.append (Seq.ofList i)⟩ none)
        ≤ ∑ j ∈ T, b j := Finset.sum_le_sum hfib
      _ ≤ ∑' j : Option (Label × State), b j := ENNReal.sum_le_tsum T
      _ = pe.scheduler.next ⟨base.init, base.trans⟩ none
            + ∑' p : Label × State, pe.kernel base p := by
          rw [ENNReal.tsum_eq_add_tsum_ite (f := b) (none : Option (Label × State))]
          have hbn : b none = pe.scheduler.next ⟨base.init, base.trans⟩ none := rfl
          rw [hbn]
          congr 1
          refine (Function.Injective.tsum_eq (g := (Option.some : (Label × State) → _))
            (fun _ _ h => Option.some.inj h) ?_).symm.trans ?_
          · intro o ho
            cases o with
            | none => simp [hb] at ho
            | some p => exact ⟨p, rfl⟩
          · refine tsum_congr fun p => ?_
            simp [hb]
      _ ≤ 1 := pe.next_none_add_kernel_tsum_le_one ⟨base.init, base.trans⟩

/-- **Total halt mass over internal extensions of a fixed prefix is `≤ probOf(prefix)`.**
For a scheduler `σ` from a Dirac source `PMF.pure s₀`, a fixed prefix `preList`, and *any*
finite set `F` of tails, the sum of `σ.haltMass` over the executions `⟨s₀, preList ++ tail⟩`
(`tail ∈ F`) is `≤ probOf ⟨s₀, ofList preList⟩`. The halt events at the various tails are
disjoint, so the total halt sub-probability from the prefix is `≤ 1`; scaling by the prefix
probability gives the bound. Built on `pathWeight_halt_le_one`. -/
theorem Scheduler.haltMass_prefix_fiber_le {State Label : Type}
    (sys : LabelledSystem State Label) (σ : Scheduler sys.toSystem) (s₀ : State)
    (preList : List (Label × State)) (F : Finset (List (Label × State))) :
    (∑ t ∈ F, σ.haltMass (PMF.pure s₀)
        ⟨⟨s₀, Seq.ofList (preList ++ t)⟩, Stream'.Seq.terminates_ofList _⟩)
      ≤ (⟨PMF.pure s₀, σ⟩ : ProbabilisticExecution sys.toSystem).probOf
          ⟨s₀, Seq.ofList preList⟩ (Stream'.Seq.terminates_ofList _) := by
  classical
  set pe : ProbabilisticExecution sys.toSystem := ⟨PMF.pure s₀, σ⟩ with hpe
  set base' : AlterSeq State Label := ⟨s₀, Seq.ofList preList⟩ with hbase'
  -- Each summand factors as `probOf(prefix) * pathWeight(base', tail) * next(end, none)`.
  have hsummand : ∀ t : List (Label × State),
      σ.haltMass (PMF.pure s₀)
          ⟨⟨s₀, Seq.ofList (preList ++ t)⟩, Stream'.Seq.terminates_ofList _⟩
        = pe.probOf base' (Stream'.Seq.terminates_ofList _)
          * (pe.pathWeight base' t
              * pe.scheduler.next ⟨base'.init, base'.trans.append (Seq.ofList t)⟩ none) := by
    intro t
    have hAS : (⟨s₀, Seq.ofList (preList ++ t)⟩ : AlterSeq State Label)
        = ⟨base'.init, base'.trans.append (Seq.ofList t)⟩ := by
      rw [hbase']; congr 1; rw [Stream'.Seq.ofList_append]
    -- `haltMass = probOf * next none`; `next` only sees the AlterSeq value.
    have hhalt : σ.haltMass (PMF.pure s₀)
          ⟨⟨s₀, Seq.ofList (preList ++ t)⟩, Stream'.Seq.terminates_ofList _⟩
        = pe.probOf ⟨s₀, Seq.ofList (preList ++ t)⟩ (Stream'.Seq.terminates_ofList _)
          * pe.scheduler.next ⟨base'.init, base'.trans.append (Seq.ofList t)⟩ none := by
      unfold Scheduler.haltMass
      rw [← hpe]
      exact congrArg (fun e => pe.probOf ⟨s₀, Seq.ofList (preList ++ t)⟩ _ * σ.next e none) hAS
    rw [hhalt]
    -- `probOf ⟨s₀, ofList (preList ++ t)⟩ = init s₀ * pathWeight nil (preList ++ t)`.
    rw [pe.probOf_eq_pathWeight s₀ (preList ++ t) (Stream'.Seq.terminates_ofList _),
      pe.pathWeight_append s₀ preList t]
    -- `probOf base' = init s₀ * pathWeight nil preList`.
    rw [pe.probOf_eq_pathWeight s₀ preList (Stream'.Seq.terminates_ofList _)]
    ring
  rw [Finset.sum_congr rfl (fun t _ => hsummand t)]
  rw [← Finset.mul_sum]
  calc pe.probOf base' (Stream'.Seq.terminates_ofList _)
        * ∑ t ∈ F, (pe.pathWeight base' t
            * pe.scheduler.next ⟨base'.init, base'.trans.append (Seq.ofList t)⟩ none)
      ≤ pe.probOf base' (Stream'.Seq.terminates_ofList _) * 1 := by
        gcongr
        exact pe.pathWeight_halt_le_one base' F
    _ = pe.probOf base' (Stream'.Seq.terminates_ofList _) := mul_one _

/-- **`haltMass` factors through the Dirac source.** `haltMass ν e = ν(e.init) * haltMass
(pure e.init) e`: the halt mass scales by the initial mass on `e`'s start state. -/
theorem Scheduler.haltMass_init_factor {State Label : Type}
    (sys : LabelledSystem State Label) (σ : Scheduler sys.toSystem) (ν : PMF State)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) :
    σ.haltMass ν e = ν e.1.init * σ.haltMass (PMF.pure e.1.init) e := by
  unfold Scheduler.haltMass
  rw [ProbabilisticExecution.probOf_init_factor σ ν e.1 e.2]
  ring

/-- **`ν`-source version of `haltMass_prefix_fiber_le`.** The total halt mass from a
mixture source `ν` over the internal extensions of a fixed prefix `⟨s₀, ofList preList⟩`
is `≤ probOf ⟨ν, σ⟩ ⟨s₀, ofList preList⟩`. Reduces to the Dirac case by factoring out
`ν s₀`. -/
theorem Scheduler.haltMass_prefix_fiber_le' {State Label : Type}
    (sys : LabelledSystem State Label) (σ : Scheduler sys.toSystem) (ν : PMF State)
    (s₀ : State) (preList : List (Label × State)) (F : Finset (List (Label × State))) :
    (∑ t ∈ F, σ.haltMass ν
        ⟨⟨s₀, Seq.ofList (preList ++ t)⟩, Stream'.Seq.terminates_ofList _⟩)
      ≤ (⟨ν, σ⟩ : ProbabilisticExecution sys.toSystem).probOf
          ⟨s₀, Seq.ofList preList⟩ (Stream'.Seq.terminates_ofList _) := by
  classical
  -- Factor out `ν s₀` from each summand (each extension shares the init `s₀`).
  have hfac : ∀ t : List (Label × State),
      σ.haltMass ν ⟨⟨s₀, Seq.ofList (preList ++ t)⟩, Stream'.Seq.terminates_ofList _⟩
        = ν s₀ * σ.haltMass (PMF.pure s₀)
            ⟨⟨s₀, Seq.ofList (preList ++ t)⟩, Stream'.Seq.terminates_ofList _⟩ := by
    intro t
    exact Scheduler.haltMass_init_factor sys σ ν
      ⟨⟨s₀, Seq.ofList (preList ++ t)⟩, Stream'.Seq.terminates_ofList _⟩
  rw [Finset.sum_congr rfl (fun t _ => hfac t), ← Finset.mul_sum]
  rw [ProbabilisticExecution.probOf_init_factor σ ν ⟨s₀, Seq.ofList preList⟩
    (Stream'.Seq.terminates_ofList _)]
  gcongr
  exact Scheduler.haltMass_prefix_fiber_le sys σ s₀ preList F

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

open Classical in
/-- **The actual post-τ accounting (bridge lemma).** The halt-mass carried by the
trace-`τ` halting executions is bounded by the trace probability of `τ`. Each halting
trace-`τ` execution is mapped to its *tight prefix* (`tightPrefixList`, the truncation
right after the last external transition), a tight trace-`τ` execution; the fiber of
executions over a fixed tight prefix differ only by an all-internal tail, and their total
halt mass is `≤ probOf(prefix)` (`haltMass_prefix_fiber_le'`, the per-prefix Kraft bound);
summing over the distinct tight prefixes recovers a sub-sum of `traceProb τ`. -/
theorem Scheduler.haltMass_le_traceProb {State Label : Type}
    (ls : LabelledSystem State Label) (σ : Scheduler ls.toSystem) (ν : PMF State) (τ : Seq Label) :
    (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        (if ls.trace e.1 = τ then σ.haltMass ν e else 0))
      ≤ ls.traceProb ⟨ν, σ⟩ τ := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le (fun S => ?_)
  -- Restrict to the trace-`τ` part of `S`.
  set S' : Finset {e : AlterSeq State Label // e.trans.Terminates} :=
    S.filter (fun e => ls.trace e.1 = τ) with hS'
  have hSS' : (∑ e ∈ S, (if ls.trace e.1 = τ then σ.haltMass ν e else 0))
      = ∑ e ∈ S', σ.haltMass ν e := by
    rw [hS', Finset.sum_filter]
  rw [hSS']
  -- The tight-prefix map: each terminating exec ↦ its tight prefix (an `AlterSeq`).
  set tp : {e : AlterSeq State Label // e.trans.Terminates} → AlterSeq State Label :=
    fun e => ⟨e.1.init, Seq.ofList (ls.tightPrefixList e.1 e.2)⟩ with htp
  -- `pf e'`: the membership-free `probOf` of `e'` (0 on non-terminating).
  set pf : AlterSeq State Label → ENNReal :=
    fun e' => if h : e'.trans.Terminates then
      (⟨ν, σ⟩ : ProbabilisticExecution ls.toSystem).probOf e' h else 0 with hpf
  -- Group `S'` by `tp`, then bound each fiber by `pf(tight prefix)`.
  set Q : Finset (AlterSeq State Label) := S'.image tp with hQ
  have hmaps : ∀ e ∈ S', tp e ∈ Q := fun e he => Finset.mem_image_of_mem tp he
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun e => σ.haltMass ν e)]
  -- The tail list of a terminating execution: its transitions after the tight prefix.
  set tsl : {e : AlterSeq State Label // e.trans.Terminates} → List (Label × State) :=
    fun e => (e.1.trans.toList e.2).drop (ls.tightPrefixList e.1 e.2).length with htsl
  -- Per-fiber bound: ∑_{e ∈ S', tp e = e'} haltMass ≤ pf(e').
  have hfib : ∀ e' ∈ Q, (∑ e ∈ S' with tp e = e', σ.haltMass ν e) ≤ pf e' := by
    intro e' he'
    set Fib : Finset {e : AlterSeq State Label // e.trans.Terminates} :=
      S'.filter (fun e => tp e = e') with hFib
    -- Common prefix list and init for the whole fiber.
    set preList : List (Label × State) := e'.trans.toList
      (by rw [hQ, Finset.mem_image] at he'; obtain ⟨e, _, rfl⟩ := he'
          exact Stream'.Seq.terminates_ofList _) with hpreList
    have hpre_term : e'.trans.Terminates := by
      rw [hQ, Finset.mem_image] at he'; obtain ⟨e, _, rfl⟩ := he'
      exact Stream'.Seq.terminates_ofList _
    -- For each `e` in the fiber: `e.1 = ⟨e'.init, ofList (preList ++ tsl e)⟩`.
    have hfiber_form : ∀ e ∈ Fib,
        e.1 = ⟨e'.init, Seq.ofList (preList ++ tsl e)⟩ := by
      rintro ⟨ev, eh⟩ he
      rw [hFib, Finset.mem_filter] at he
      have htpe : tp ⟨ev, eh⟩ = e' := he.2
      rw [htp] at htpe
      simp only at htpe
      have hinit : ev.init = e'.init := congrArg (·.init) htpe
      have h1 : (Seq.ofList (ls.tightPrefixList ev eh) : Seq (Label × State)) = e'.trans :=
        congrArg (·.trans) htpe
      have hpl : ls.tightPrefixList ev eh = preList := by
        rw [hpreList, show e'.trans.toList hpre_term
            = (Seq.ofList (ls.tightPrefixList ev eh)).toList (h1 ▸ hpre_term) from
          (Stream'.Seq.toList_congr_pub h1.symm hpre_term (h1 ▸ hpre_term)),
          Stream'.Seq.toList_ofList]
      obtain ⟨tailList, hfull, _, _, _⟩ := ls.tightPrefixList_spec ev eh
      have htail : tsl ⟨ev, eh⟩ = tailList := by
        rw [htsl]; change (ev.trans.toList eh).drop _ = tailList
        rw [hfull, List.drop_left]
      change ev = ⟨e'.init, Seq.ofList (preList ++ tsl ⟨ev, eh⟩)⟩
      rw [htail]
      have hev : ev = ⟨ev.init, Seq.ofList (ev.trans.toList eh)⟩ := by
        obtain ⟨ei, et⟩ := ev; congr 1; exact (Stream'.Seq.ofList_toList _ _).symm
      rw [hev, hinit, hfull, hpl]
    -- Reindex the fiber sum onto the tail set `F`, then apply the per-prefix bound.
    set F : Finset (List (Label × State)) := Fib.image tsl with hF
    have hinjF : Set.InjOn tsl (Fib : Set {e : AlterSeq State Label // e.trans.Terminates}) := by
      intro a ha b hb hab
      apply Subtype.ext
      rw [hfiber_form a ha, hfiber_form b hb, hab]
    have hreindex : (∑ e ∈ Fib, σ.haltMass ν e)
        = ∑ t ∈ F, σ.haltMass ν
            ⟨⟨e'.init, Seq.ofList (preList ++ t)⟩, Stream'.Seq.terminates_ofList _⟩ := by
      rw [hF, Finset.sum_image (fun a ha b hb => hinjF ha hb)]
      refine Finset.sum_congr rfl fun e he => ?_
      congr 1
      exact Subtype.ext (hfiber_form e he)
    rw [show (∑ e ∈ S' with tp e = e', σ.haltMass ν e)
          = ∑ e ∈ Fib, σ.haltMass ν e from by rw [hFib], hreindex]
    -- Apply the per-prefix Kraft bound; rewrite `⟨e'.init, ofList preList⟩ = e'`.
    have he'_eq : (⟨e'.init, Seq.ofList preList⟩ : AlterSeq State Label) = e' := by
      obtain ⟨ei, et⟩ := e'; congr 1; exact Stream'.Seq.ofList_toList _ _
    change (∑ t ∈ F, σ.haltMass ν
        ⟨⟨e'.init, Seq.ofList (preList ++ t)⟩, Stream'.Seq.terminates_ofList _⟩)
      ≤ pf e'
    rw [hpf]
    change (∑ t ∈ F, σ.haltMass ν
        ⟨⟨e'.init, Seq.ofList (preList ++ t)⟩, Stream'.Seq.terminates_ofList _⟩)
      ≤ if h : e'.trans.Terminates then
          (⟨ν, σ⟩ : ProbabilisticExecution ls.toSystem).probOf e' h else 0
    rw [dif_pos hpre_term]
    calc (∑ t ∈ F, σ.haltMass ν
            ⟨⟨e'.init, Seq.ofList (preList ++ t)⟩, Stream'.Seq.terminates_ofList _⟩)
        ≤ (⟨ν, σ⟩ : ProbabilisticExecution ls.toSystem).probOf
            ⟨e'.init, Seq.ofList preList⟩ (Stream'.Seq.terminates_ofList _) :=
          Scheduler.haltMass_prefix_fiber_le' ls σ ν e'.init preList F
      _ = (⟨ν, σ⟩ : ProbabilisticExecution ls.toSystem).probOf e' hpre_term :=
          ProbabilisticExecution.probOf_congr _ _ _ he'_eq _ _
  -- Each `e' ∈ Q` is a tight trace-`τ` (terminating) execution.
  have hQtight : ∀ e' ∈ Q, e'.trans.Terminates ∧ ls.trace e' = τ ∧ ls.IsTight e' := by
    intro e' he'
    rw [hQ, Finset.mem_image] at he'
    obtain ⟨e, heS', rfl⟩ := he'
    obtain ⟨tailList, _hfull, _htail, htight, htrace⟩ := ls.tightPrefixList_spec e.1 e.2
    have hτ : ls.trace e.1 = τ := by
      rw [hS', Finset.mem_filter] at heS'; exact heS'.2
    refine ⟨Stream'.Seq.terminates_ofList _, ?_, ?_⟩
    · rw [htp]; rw [htrace]; exact hτ
    · rw [htp]; exact htight
  calc (∑ e' ∈ Q, ∑ e ∈ S' with tp e = e', σ.haltMass ν e)
      ≤ ∑ e' ∈ Q, pf e' := Finset.sum_le_sum hfib
    _ ≤ ls.traceProb ⟨ν, σ⟩ τ := by
        -- Embed `Q` into the tight trace-`τ` subtype `T`, then `sum ≤ tsum`.
        unfold LabelledSystem.traceProb
        set T := {e : AlterSeq State Label // e.trans.Terminates ∧ ls.trace e = τ ∧ ls.IsTight e}
          with hT
        -- The image of `Q.attach` inside `T`.
        set embedQ : {x // x ∈ Q} → T :=
          fun x => ⟨x.1, hQtight x.1 x.2⟩ with hembedQ
        have hinj : Function.Injective embedQ := by
          intro a b hab
          have : a.1 = b.1 := congrArg (fun (t : T) => t.1) hab
          exact Subtype.ext this
        set QT : Finset T := Q.attach.image embedQ with hQT
        -- `∑_{e' ∈ Q} pf e' = ∑_{x ∈ QT} probOf x.1 x.2.1`.
        have hsum_eq : (∑ e' ∈ Q, pf e')
            = ∑ x ∈ QT, (⟨ν, σ⟩ : ProbabilisticExecution ls.toSystem).probOf x.1 x.2.1 := by
          rw [hQT, Finset.sum_image (fun a _ b _ hab => hinj hab)]
          rw [← Finset.sum_attach Q pf]
          refine Finset.sum_congr rfl fun x _ => ?_
          change pf x.1 = (⟨ν, σ⟩ : ProbabilisticExecution ls.toSystem).probOf x.1 _
          rw [hpf]
          exact dif_pos (hQtight x.1 x.2).1
        rw [hsum_eq]
        exact ENNReal.sum_le_tsum QT

/-- **Trailing internal transitions don't affect the trace probability of an
a.s.-halting process.** If the process `⟨ν, σ⟩` almost surely halts (total halt
mass `1`) and every halting execution has trace `τ`, then `traceProb τ = 1`. The
proof is the squeeze `1 = ∑ haltMass ≤ traceProb τ ≤ 1`: the upper bound is the
Kraft bound `traceProb_le_one`; the lower bound is the post-τ accounting bridge
`haltMass_le_traceProb` (all halting mass lives on trace-`τ` executions, whose
total halt mass is bounded by `traceProb τ`). -/
theorem LabelledSystem.traceProb_eq_one_of_asHalt {State Label : Type}
    (ls : LabelledSystem State Label) (σ : Scheduler ls.toSystem) (ν : PMF State) (τ : Seq Label)
    (h_halt : (∑' e : {e : AlterSeq State Label // e.trans.Terminates}, σ.haltMass ν e) = 1)
    (h_trace : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
        σ.haltMass ν e ≠ 0 → ls.trace e.1 = τ) :
    ls.traceProb ⟨ν, σ⟩ τ = 1 := by
  classical
  refine le_antisymm (ls.traceProb_le_one ⟨ν, σ⟩ τ) ?_
  -- `1 = ∑ haltMass = ∑ (if trace = τ then haltMass else 0) ≤ traceProb τ`.
  rw [← h_halt]
  -- Every nonzero halting execution has trace `τ`, so the `if`-filter is the identity.
  have hfilter : (∑' e : {e : AlterSeq State Label // e.trans.Terminates}, σ.haltMass ν e)
      = ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          (if ls.trace e.1 = τ then σ.haltMass ν e else 0) := by
    refine tsum_congr fun e => ?_
    by_cases hz : σ.haltMass ν e = 0
    · rw [hz]; split <;> rfl
    · rw [if_pos (h_trace e hz)]
  rw [hfilter]
  exact σ.haltMass_le_traceProb ls ν τ

end PLTS
