/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.WeakStep

/-!
# Kraft-style trace-probability bound

Generic machinery (over an arbitrary `System`, needing no `Silent` instance) for
bounding `ProbabilisticExecution` masses by `1`. We bound the total one-step
kernel mass by `1`, factor `probOf` as the initial mass times a *conditional path
weight* `pathWeight`, prove the front-peel recursion on `pathWeight`, and assemble
the finite-antichain Kraft bound `pathWeight_antichain`/`probOf_antichain` (used by
`achievableTraceDists_map`) and the halting bound `WeakScheduler.haltMass_tsum_le_one`
(used by `Simulation`). None of this depends on the weak-closure or expansion
constructions, so it lives upstream of `WeakConstruction`.
-/

open Stream'

namespace PLTS

variable {α β State State_C State_A Label : Type} [Silent Label]

/-! ### Kraft-bound infrastructure: front-peel of `probOf`

Generic machinery over an arbitrary `System`,
preparing an upcoming Kraft-style bound. We bound the total one-step kernel
mass by `1`, factor `probOf` as the initial mass times a *conditional path
weight* `pathWeight`, and prove the key front-peel recursion on `pathWeight`. -/

/-- The total one-step kernel mass over all next steps is `≤ 1`. -/
theorem ProbabilisticExecution.kernel_tsum_le_one {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) :
    (∑' p : Label × State, pe.kernel e p) ≤ 1 := by
  calc (∑' p : Label × State, pe.kernel e p)
      = ∑' (l : Label) (s' : State), pe.kernel e (l, s') := by
        rw [ENNReal.tsum_prod']
    _ = ∑' (l : Label) (s' : State) (μ : PMF State),
          pe.scheduler.next e (some (l, μ)) * μ s' := by rfl
    _ = ∑' (l : Label) (μ : PMF State) (s' : State),
          pe.scheduler.next e (some (l, μ)) * μ s' := by
        refine tsum_congr fun l => ?_
        exact ENNReal.tsum_comm
    _ = ∑' (l : Label) (μ : PMF State), pe.scheduler.next e (some (l, μ)) := by
        refine tsum_congr fun l => tsum_congr fun μ => ?_
        rw [ENNReal.tsum_mul_left, μ.tsum_coe, mul_one]
    _ = ∑' lμ : Label × PMF State, pe.scheduler.next e (some lμ) := by
        rw [ENNReal.tsum_prod']
    _ ≤ ∑' opt, pe.scheduler.next e opt :=
        ENNReal.tsum_comp_le_tsum_of_injective (f := fun lμ : Label × PMF State => some lμ)
          (fun _ _ h => Option.some.inj h) _
    _ = 1 := (pe.scheduler.next e).tsum_coe

/-- The conditional path weight of a transition list `trans` given a base
history `base`: the product of one-step kernels along `trans`, each evaluated at
`base` extended by the already-consumed prefix. End-recursive, mirroring `probOf`. -/
noncomputable def ProbabilisticExecution.pathWeight {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (base : AlterSeq State Label) (trans : List (Label × State)) : ENNReal :=
  trans.reverseRecOn (motive := fun _ => ENNReal) 1
    (fun rest last ih => ih * pe.kernel ⟨base.init, base.trans.append (Seq.ofList rest)⟩ last)

/-- `probOf` factors as the initial mass times the conditional path weight from
the empty base. -/
theorem ProbabilisticExecution.probOf_eq_pathWeight {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (s₀ : State) (trans : List (Label × State))
    (hFin : (Seq.ofList trans : Seq (Label × State)).Terminates) :
    pe.probOf ⟨s₀, Seq.ofList trans⟩ hFin
      = pe.init s₀ * pe.pathWeight ⟨s₀, Seq.nil⟩ trans := by
  induction trans using List.reverseRecOn with
  | nil =>
    unfold ProbabilisticExecution.probOf ProbabilisticExecution.pathWeight
    rw [Stream'.Seq.toList_ofList, List.reverseRecOn_nil, List.reverseRecOn_nil, mul_one]
  | append_singleton rest last ih =>
    have hL : pe.probOf { init := s₀, trans := ↑(rest ++ [last]) } hFin
        = pe.init s₀ * pe.pathWeight { init := s₀, trans := Seq.nil } rest
          * pe.kernel { init := s₀, trans := ↑rest } last := by
      unfold ProbabilisticExecution.probOf
      rw [Stream'.Seq.toList_ofList, List.reverseRecOn_concat]
      rw [← ih (Stream'.Seq.terminates_ofList rest)]
      unfold ProbabilisticExecution.probOf
      rw [Stream'.Seq.toList_ofList]
    rw [hL]
    unfold ProbabilisticExecution.pathWeight
    rw [List.reverseRecOn_concat]
    simp only [Stream'.Seq.nil_append]
    ring

/-- Front-peel: the path weight of `(l, s') :: rest` is the first kernel step times
the path weight of `rest` from the base extended by `(l, s')`. -/
theorem ProbabilisticExecution.pathWeight_cons {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (base : AlterSeq State Label) (l : Label) (s' : State)
    (rest : List (Label × State)) :
    pe.pathWeight base ((l, s') :: rest)
      = pe.kernel base (l, s')
        * pe.pathWeight ⟨base.init, base.trans.append (Seq.cons (l, s') Seq.nil)⟩ rest := by
  induction rest using List.reverseRecOn with
  | nil =>
    unfold ProbabilisticExecution.pathWeight
    rw [show ((l, s') :: [] : List (Label × State)) = [] ++ [(l, s')] from rfl]
    rw [List.reverseRecOn_concat, List.reverseRecOn_nil, List.reverseRecOn_nil]
    simp only [Stream'.Seq.ofList_nil, Stream'.Seq.append_nil, one_mul, mul_one]
  | append_singleton rest' last ih =>
    have hhist : base.trans.append (Seq.ofList ((l, s') :: rest'))
        = (base.trans.append (Seq.cons (l, s') Seq.nil)).append (Seq.ofList rest') := by
      rw [Stream'.Seq.ofList_cons, Stream'.Seq.append_assoc, Stream'.Seq.cons_append,
        Stream'.Seq.nil_append]
    have hcons : ((l, s') :: (rest' ++ [last]) : List (Label × State))
        = ((l, s') :: rest') ++ [last] := rfl
    rw [hcons]
    unfold ProbabilisticExecution.pathWeight
    rw [List.reverseRecOn_concat, List.reverseRecOn_concat]
    have ih' := ih
    unfold ProbabilisticExecution.pathWeight at ih'
    rw [ih', hhist]
    ring

/-- **Finite-antichain Kraft bound.** For a prefix-free finite set `F` of
transition lists, the total `pathWeight` from any base is `≤ 1`. (Distinct tight
trace-cone executions are prefix-free, so this bounds the trace probability.) -/
theorem ProbabilisticExecution.pathWeight_antichain {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (base : AlterSeq State Label) (F : Finset (List (Label × State)))
    (hpf : ∀ t ∈ F, ∀ t' ∈ F, t <+: t' → t = t') :
    (∑ t ∈ F, pe.pathWeight base t) ≤ 1 := by
  classical
  suffices aux : ∀ (N : ℕ) (base : AlterSeq State Label)
      (F : Finset (List (Label × State))),
      (∀ t ∈ F, t.length ≤ N) →
      (∀ t ∈ F, ∀ t' ∈ F, t <+: t' → t = t') →
      (∑ t ∈ F, pe.pathWeight base t) ≤ 1 by
    exact aux (F.sup List.length) base F (fun t ht => Finset.le_sup ht) hpf
  intro N
  induction N with
  | zero =>
    intro base F hlen hpf
    -- every t ∈ F has length ≤ 0, so t = []; hence F ⊆ {[]}
    have hsub : F ⊆ {([] : List (Label × State))} := by
      intro t ht
      have : t = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (hlen t ht))
      simp [this]
    calc (∑ t ∈ F, pe.pathWeight base t)
        ≤ ∑ t ∈ ({([] : List (Label × State))} : Finset _), pe.pathWeight base t :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => bot_le)
      _ = pe.pathWeight base [] := Finset.sum_singleton _ _
      _ = 1 := by unfold ProbabilisticExecution.pathWeight; rw [List.reverseRecOn_nil]
  | succ N ih =>
    intro base F hlen hpf
    by_cases hnil : ([] : List (Label × State)) ∈ F
    · -- `[] ∈ F`: prefix-freeness forces every member to equal `[]`.
      have hsub : F ⊆ {([] : List (Label × State))} := by
        intro t ht
        have : ([] : List (Label × State)) = t := hpf [] hnil t ht List.nil_prefix
        simp [← this]
      calc (∑ t ∈ F, pe.pathWeight base t)
          ≤ ∑ t ∈ ({([] : List (Label × State))} : Finset _), pe.pathWeight base t :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => bot_le)
        _ = pe.pathWeight base [] := Finset.sum_singleton _ _
        _ = 1 := by unfold ProbabilisticExecution.pathWeight; rw [List.reverseRecOn_nil]
    · -- `[] ∉ F`: every member is nonempty; group by first element.
      -- group by the head (as an `Option`, so no `Inhabited` is needed)
      set T : Finset (Option (Label × State)) := F.image List.head? with hT
      have hmaps : ∀ t ∈ F, t.head? ∈ T := fun t ht => Finset.mem_image_of_mem _ ht
      rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun t => pe.pathWeight base t)]
      -- now: ∑ o ∈ T, ∑ t ∈ F with t.head? = o, pathWeight base t ≤ 1
      -- per-fiber bound `b`: kernel mass on `some p`, `0` on `none`.
      set b : Option (Label × State) → ENNReal :=
        fun o => o.elim 0 (fun p => pe.kernel base p) with hb
      have hfib : ∀ j ∈ T, (∑ i ∈ F with i.head? = j, pe.pathWeight base i) ≤ b j := by
        intro j hj
        cases j with
        | none =>
          -- the fiber over `none` is empty: `t.head? = none ↔ t = []`, and `[] ∉ F`.
          have hempty : (F.filter (fun i => i.head? = none)) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro t ht
            rw [List.head?_eq_none_iff]
            intro hnull
            exact hnil (hnull ▸ ht)
          rw [hempty, Finset.sum_empty]
          exact bot_le
        | some p =>
          obtain ⟨l, s'⟩ := p
          set base' : AlterSeq State Label :=
            ⟨base.init, base.trans.append (Seq.cons (l, s') Seq.nil)⟩ with hbase'
          -- every `t` in the fiber is `(l, s') :: t.tail`
          have hfiber_cons : ∀ t ∈ F.filter (fun i => i.head? = some (l, s')),
              t = (l, s') :: t.tail := by
            intro t ht
            rw [Finset.mem_filter] at ht
            exact (List.cons_head?_tail (a := (l, s')) ht.2).symm
          set Ft : Finset (List (Label × State)) := F.filter (fun i => i.head? = some (l, s'))
            with hFt
          -- step 1: rewrite each fiber summand via `pathWeight_cons`
          have hstep : (∑ i ∈ Ft, pe.pathWeight base i)
              = ∑ i ∈ Ft, pe.kernel base (l, s') * pe.pathWeight base' i.tail := by
            refine Finset.sum_congr rfl fun t ht => ?_
            conv_lhs => rw [hfiber_cons t ht]
            rw [pe.pathWeight_cons base l s' t.tail]
          rw [hstep, ← Finset.mul_sum]
          -- step 2: reindex the tail sum onto `Gt := Ft.image List.tail`
          set Gt : Finset (List (Label × State)) := Ft.image List.tail with hGt
          have hinj : Set.InjOn List.tail (Ft : Set (List (Label × State))) := by
            intro a ha b hb hab
            have ea := hfiber_cons a ha
            have eb := hfiber_cons b hb
            rw [ea, eb, hab]
          have hreindex : (∑ i ∈ Ft, pe.pathWeight base' i.tail)
              = ∑ u ∈ Gt, pe.pathWeight base' u := by
            rw [hGt, Finset.sum_image hinj]
          rw [hreindex]
          -- step 3: bound the tail sum by `1` via `ih base' Gt`
          have hbound : (∑ u ∈ Gt, pe.pathWeight base' u) ≤ 1 := by
            apply ih base' Gt
            · -- length bound: tails have length ≤ N
              intro u hu
              rw [hGt, Finset.mem_image] at hu
              obtain ⟨t, ht, rfl⟩ := hu
              have htF : t ∈ F := (Finset.mem_filter.mp (hFt ▸ ht)).1
              have htne : t = (l, s') :: t.tail := hfiber_cons t ht
              have : t.length = t.tail.length + 1 := by
                conv_lhs => rw [htne]
                simp
              have hle := hlen t htF
              omega
            · -- prefix-free of `Gt`
              intro u₁ hu₁ u₂ hu₂ hpre
              rw [hGt, Finset.mem_image] at hu₁ hu₂
              obtain ⟨t₁, ht₁, rfl⟩ := hu₁
              obtain ⟨t₂, ht₂, rfl⟩ := hu₂
              have e₁ : t₁ = (l, s') :: t₁.tail := hfiber_cons t₁ ht₁
              have e₂ : t₂ = (l, s') :: t₂.tail := hfiber_cons t₂ ht₂
              have ht₁F : t₁ ∈ F := (Finset.mem_filter.mp (hFt ▸ ht₁)).1
              have ht₂F : t₂ ∈ F := (Finset.mem_filter.mp (hFt ▸ ht₂)).1
              have hpre' : t₁ <+: t₂ := by
                rw [e₁, e₂]
                exact (List.cons_prefix_cons).mpr ⟨rfl, hpre⟩
              have := hpf t₁ ht₁F t₂ ht₂F hpre'
              -- t₁ = t₂ ⟹ tails equal
              rw [e₁, e₂] at this
              exact List.cons.inj this |>.2
          -- conclude
          calc pe.kernel base (l, s') * ∑ u ∈ Gt, pe.pathWeight base' u
              ≤ pe.kernel base (l, s') * 1 := by gcongr
            _ = b (some (l, s')) := by rw [mul_one, hb]; rfl
      calc (∑ j ∈ T, ∑ i ∈ F with i.head? = j, pe.pathWeight base i)
          ≤ ∑ j ∈ T, b j := Finset.sum_le_sum hfib
        _ ≤ ∑' j : Option (Label × State), b j := ENNReal.sum_le_tsum T
        _ = ∑' p : Label × State, pe.kernel base p := by
            have hsupp : Function.support b ⊆ Set.range (Option.some : (Label × State) → _) := by
              intro j hj
              cases j with
              | none => simp [hb, Function.mem_support] at hj
              | some p => exact ⟨p, rfl⟩
            have := (Option.some_injective (Label × State)).tsum_eq (f := b) hsupp
            simpa [hb] using this.symm
        _ ≤ 1 := pe.kernel_tsum_le_one base

/-- **Execution-level antichain Kraft bound.** For a finite set `F` of terminating
executions that is prefix-free among executions sharing an initial state, the total
`probOf` is `≤ 1`. Proven by grouping on the initial state and applying
`pathWeight_antichain` to each group, then `∑ initState ≤ 1`. -/
theorem ProbabilisticExecution.probOf_antichain {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (F : Finset (AlterSeq State Label))
    (hterm : ∀ e ∈ F, e.trans.Terminates)
    (hpf : ∀ e (he : e ∈ F) e' (he' : e' ∈ F), e.init = e'.init →
        e.trans.toList (hterm e he) <+: e'.trans.toList (hterm e' he') → e = e') :
    (∑ e ∈ F.attach, pe.probOf e.1 (hterm e.1 e.2)) ≤ 1 := by
  classical
  -- Per-element factorisation of `probOf` through `pathWeight`.
  -- Generic factorisation through `pathWeight`, for any execution and any
  -- termination proof. Stated over fields so the dependent proof can be
  -- generalised cleanly.
  have hfactor : ∀ (s₀ : State) (sq : Seq (Label × State)) (h : sq.Terminates),
      pe.probOf ⟨s₀, sq⟩ h
        = pe.init s₀ * pe.pathWeight ⟨s₀, Seq.nil⟩ (sq.toList h) := by
    intro s₀ sq h
    have heq : (Seq.ofList (sq.toList h) : Seq (Label × State)) = sq :=
      Stream'.Seq.ofList_toList sq h
    -- Move to the `ofList` form, generalising `h` so the rewrite is valid.
    generalize hL : sq.toList h = L
    rw [hL] at heq
    subst heq
    exact pe.probOf_eq_pathWeight s₀ L h
  -- Rewrite each summand via `hfactor`.
  have hrw : (∑ e ∈ F.attach, pe.probOf e.1 (hterm e.1 e.2))
      = ∑ e ∈ F.attach,
          pe.init (e.1).init
            * pe.pathWeight ⟨(e.1).init, Seq.nil⟩ ((e.1).trans.toList (hterm e.1 e.2)) := by
    refine Finset.sum_congr rfl fun e _ => ?_
    exact hfactor (e.1).init (e.1).trans (hterm e.1 e.2)
  rw [hrw]
  -- Group by initial state.
  set g : {x // x ∈ F} → State := fun e => (e.1).init with hg
  have hmaps : ∀ e ∈ F.attach, g e ∈ F.attach.image g :=
    fun e he => Finset.mem_image_of_mem g he
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun e => pe.init (e.1).init
      * pe.pathWeight ⟨(e.1).init, Seq.nil⟩ ((e.1).trans.toList (hterm e.1 e.2)))]
  -- Per-fiber bound: the `s₀`-fiber sum is `≤ pe.init s₀`.
  have hfib : ∀ s₀ ∈ F.attach.image g,
      (∑ i ∈ F.attach with g i = s₀,
        pe.init (i.1).init
          * pe.pathWeight ⟨(i.1).init, Seq.nil⟩ ((i.1).trans.toList (hterm i.1 i.2)))
        ≤ pe.init s₀ := by
    intro s₀ _
    set Fs : Finset {x // x ∈ F} := F.attach.filter (fun i => g i = s₀) with hFs
    -- On `Fs`, every `i` has `(↑i).init = s₀`.
    have hinit : ∀ i ∈ Fs, (i.1).init = s₀ := by
      intro i hi
      rw [hFs, Finset.mem_filter] at hi
      exact hi.2
    -- Rewrite each fiber summand to `pe.init s₀ * pathWeight ⟨s₀, nil⟩ (toList i)`.
    have hsum_eq : (∑ i ∈ Fs,
          pe.init (i.1).init
            * pe.pathWeight ⟨(i.1).init, Seq.nil⟩ ((i.1).trans.toList (hterm i.1 i.2)))
        = pe.init s₀
          * ∑ i ∈ Fs, pe.pathWeight ⟨s₀, Seq.nil⟩ ((i.1).trans.toList (hterm i.1 i.2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hinit i hi]
    rw [hsum_eq]
    -- Reindex the pathWeight sum onto the image of `toList`.
    set tl : {x // x ∈ F} → List (Label × State) :=
      fun i => (i.1).trans.toList (hterm i.1 i.2) with htl
    set Ts : Finset (List (Label × State)) := Fs.image tl with hTs
    have hinj : Set.InjOn tl (Fs : Set {x // x ∈ F}) := by
      intro a ha b hb hab
      apply Subtype.ext
      refine hpf a.1 a.2 b.1 b.2 ?_ ?_
      · rw [hinit a ha, hinit b hb]
      · rw [show a.1.trans.toList (hterm a.1 a.2) = tl a from rfl,
          show b.1.trans.toList (hterm b.1 b.2) = tl b from rfl, hab]
    have hreindex : (∑ i ∈ Fs, pe.pathWeight ⟨s₀, Seq.nil⟩ (tl i))
        = ∑ u ∈ Ts, pe.pathWeight ⟨s₀, Seq.nil⟩ u := by
      rw [hTs, Finset.sum_image hinj]
    rw [show (∑ i ∈ Fs, pe.pathWeight ⟨s₀, Seq.nil⟩ ((i.1).trans.toList (hterm i.1 i.2)))
        = ∑ i ∈ Fs, pe.pathWeight ⟨s₀, Seq.nil⟩ (tl i) from rfl, hreindex]
    -- `Ts` is prefix-free, so `pathWeight_antichain` bounds the sum by `1`.
    have hpf' : ∀ t ∈ Ts, ∀ t' ∈ Ts, t <+: t' → t = t' := by
      intro t ht t' ht' hpre
      rw [hTs, Finset.mem_image] at ht ht'
      obtain ⟨a, ha, rfl⟩ := ht
      obtain ⟨b, hb, rfl⟩ := ht'
      have : a = b := by
        apply Subtype.ext
        refine hpf a.1 a.2 b.1 b.2 ?_ ?_
        · rw [hinit a ha, hinit b hb]
        · exact hpre
      rw [this]
    have hbound : (∑ u ∈ Ts, pe.pathWeight ⟨s₀, Seq.nil⟩ u) ≤ 1 :=
      pe.pathWeight_antichain ⟨s₀, Seq.nil⟩ Ts hpf'
    calc pe.init s₀ * ∑ u ∈ Ts, pe.pathWeight ⟨s₀, Seq.nil⟩ u
        ≤ pe.init s₀ * 1 := by gcongr
      _ = pe.init s₀ := mul_one _
  calc (∑ j ∈ F.attach.image g,
          ∑ i ∈ F.attach with g i = j,
            pe.init (i.1).init
              * pe.pathWeight ⟨(i.1).init, Seq.nil⟩ ((i.1).trans.toList (hterm i.1 i.2)))
      ≤ ∑ j ∈ F.attach.image g, pe.init j := Finset.sum_le_sum hfib
    _ ≤ ∑' s₀ : State, pe.init s₀ := ENNReal.sum_le_tsum _
    _ = 1 := by rw [pe.init_eq_initState]; exact pe.initState.tsum_coe

/-- **`tsum` over an `Option` type splits** as the value at `none` plus the `tsum`
over the `some`-fibres. (Local `ENNReal` specialisation; no such `tsum_option`
exists in this Mathlib revision, and every `ENNReal` family is summable.) -/
theorem ENNReal.tsum_option' {β : Type*} (f : Option β → ENNReal) :
    (∑' x, f x) = f none + ∑' y, f (some y) := by
  rw [_root_.ENNReal.tsum_eq_add_tsum_ite none]
  congr 1
  rw [tsum_eq_tsum_of_ne_zero_bij (i := fun y : {y : β // f (some y) ≠ 0} => some y.1)]
  · intro a b hab; exact Subtype.ext (Option.some_injective β hab)
  · intro x hx
    cases hx2 : (x : Option β) with
    | none => simp [Function.mem_support, hx2] at hx
    | some y =>
      refine ⟨⟨y, ?_⟩, ?_⟩
      · simp only [Function.mem_support] at hx ⊢
        rw [hx2] at hx; simpa using hx
      · simp
  · intro y; simp

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

/-! ### Generic trace-probability bound `traceProb_le_one`

The trace probability of any execution is `≤ 1` (a Kraft bound): distinct tight
executions of the same trace are prefix-free, so `probOf_antichain` applies. The
prefix-freeness reduces to a label-list fact (`traceTightLabs_prefix`). -/

open Classical in
/-- `Seq.filter` of an `ofList` is the `ofList` of the corresponding `List.filter`. -/
theorem Stream'.Seq.ofList_filter {α : Type} (p : α → Prop) (l : List α) :
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

/-! ### Generic `Seq` / trace helpers (shared upstream)

Small generic lemmas used downstream (by `TraceMap` / `SimulationTrace`). -/

/-- `toList` is invariant under equality of the underlying `Seq` (the termination
proofs are irrelevant). -/
theorem Stream'.Seq.toList_congr_pub {γ : Type} {s t : Seq γ} (heq : s = t)
    (hs : s.Terminates) (ht : t.Terminates) : s.toList hs = t.toList ht := by subst heq; rfl

/-- Public version of `System.map_ofList`: `Seq.map f (ofList L) = ofList (L.map f)`. -/
theorem Seq.map_ofList_pub {α β : Type} (f : α → β) (L : List α) :
    (Seq.ofList L).map f = Seq.ofList (L.map f) := by
  induction L with
  | nil => rw [Stream'.Seq.ofList_nil, Stream'.Seq.map_nil, List.map_nil, Stream'.Seq.ofList_nil]
  | cons a L ih =>
    rw [Stream'.Seq.ofList_cons, Stream'.Seq.map_cons, List.map_cons, Stream'.Seq.ofList_cons, ih]

end PLTS
