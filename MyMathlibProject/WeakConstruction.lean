/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.WeakStep
import MyMathlibProject.DistConstruction

/-!
# Constructions on PLTSs

This file collects constructions that build new probabilistic labelled
transition systems from existing ones, using the weak-step infrastructure
from `WeakStep.lean`.
-/

open Stream'

namespace PLTS

variable {α β State State_C State_A Label : Type}

/-! ## The weak-closure construction

Keep the state space and the internal-label classification of `sys` but
replace its step relation by *weak transitions*: from a state `s` on label
`l`, a `weak step` is a `weakTau` to `μ` if `l` is internal, or a `weakStep`
from `PMF.pure s` to `μ` if `l` is external. -/

/-- The **weak closure** of a labelled PLTS.

`sys.weakClosure : LabelledSystem State Label` has the same state space,
initial state, and internal-label predicate as `sys`, but its `step` relation
is the case-split weak transition:

* for an *internal* label `l`, `step s l μ := weakTau sys (PMF.pure s) μ`
  — `μ` is reachable by zero-or-more internal hyper-steps from the Dirac at
  `s`;
* for an *external* label `l`, `step s l μ := weakStep sys (PMF.pure s) l μ`
  — `μ` is reachable by a `weakTau ; hyperStep l ; weakTau` chain from the
  Dirac at `s`. -/
def LabelledSystem.weakClosure (sys : LabelledSystem State Label) :
    LabelledSystem State Label where
  init := sys.init
  step s l μ :=
    (sys.internal l ∧ weakTau sys (PMF.pure s) μ) ∨
    (¬ sys.internal l ∧ weakStep sys (PMF.pure s) l μ)
  internal := sys.internal

/-- `sys^w` is sugar for `LabelledSystem.weakClosure sys`, the weak-closure
construction replacing `sys`'s step relation by its case-split weak
transitions. -/
scoped postfix:max "^w" => LabelledSystem.weakClosure

/-! ## Trace-distribution preservation

The weak-closure construction `·^w` is designed to leave the *set of
achievable trace distributions* invariant. The preservation theorem splits
into two set inclusions ("subset" and "superset"). One direction is the
structural lift of `sys`-executions into the construction; the other is the
harder "expand" direction.
-/

/-! ### The weak-closure construction preserves trace distributions

The easy direction is `⊆`: every `pe` over `sys` is still a valid
probabilistic execution over `sys^w` (each strong step is a weak step), and
`traceProb` is unchanged because `sys^w` shares its `internal` predicate with
`sys` (so `trace` and `IsTight` are identical). The reverse direction
requires expanding each weak step in `sys^w` back into a chain of strong
`sys`-steps; that proof is deferred. -/

/-- **Every strong step lifts to a `sys^w` step.** This is the structural
fact that powers the easy direction of `weakClosure_traceProb_eq`. -/
theorem LabelledSystem.step_le_weakClosure_step
    (sys : LabelledSystem State Label)
    {s : State} {l : Label} {μ : PMF State} (h : sys.step s l μ) :
    sys^w.step s l μ := by
  change (sys.internal l ∧ weakTau sys (PMF.pure s) μ) ∨
       (¬ sys.internal l ∧ weakStep sys (PMF.pure s) l μ)
  by_cases h_int : sys.internal l
  · exact Or.inl ⟨h_int, weakTau_of_step h_int h
      (ls := sys) (s := s) (l := l) (μ := μ)⟩
  · exact Or.inr ⟨h_int, weakStep_strong h⟩

/-- **Easy direction of `weakClosure_traceProb_eq`**: every trace distribution
achievable by `sys` is achievable by `sys^w`. The witness `pe'` reuses `pe`'s
scheduler and initial distribution verbatim; only the validity field is
re-derived through `step_le_weakClosure_step`. Since `sys` and `sys^w` share
their internal-label predicate, the `trace` / `IsTight` filters and `probOf`
computation agree definitionally, so `traceProb` is unchanged. -/
theorem weakClosure_traceProb_subset (sys : LabelledSystem State Label) :
    achievableTraceDists sys ⊆ achievableTraceDists sys^w := by
  rintro D ⟨pe, h_init, hpe⟩
  refine ⟨
    { initState := pe.initState
      scheduler :=
        { next := pe.scheduler.next
          valid := fun e n s h_term h_state l μ h_supp =>
            sys.step_le_weakClosure_step
              (pe.scheduler.valid e n s h_term h_state l μ h_supp) } }, ?_, ?_⟩
  · -- `sys^w.init = sys.init`, so the lifted execution starts at the same state.
    exact h_init
  · intro τ
    exact hpe τ

/-! ### External-trace level mass

The external-trace analogue of `ProbabilisticExecution.labMass`: the total
`probOf`-mass (g-integrated over end-states) of *tight* executions whose
external trace is `extLabs`, obtained by summing `labMass` over the label lists
`labs` that refine `extLabs` (`traceTightLabs`). The `g = 1` slice is `traceProb`
at `Seq.ofList extLabs`. -/
open Classical in
noncomputable def LabelledSystem.extLabMass (ls : LabelledSystem State Label)
    (pe : ProbabilisticExecution ls.toSystem) (extLabs : List Label)
    (g : State → ENNReal) : ENNReal :=
  ∑' labs : List Label,
    if ls.traceTightLabs (Seq.ofList extLabs) labs then pe.labMass labs g else 0

/-- The `g = 1` slice of `extLabMass` is exactly `traceProb` at `Seq.ofList extLabs`. -/
theorem LabelledSystem.traceProb_eq_extLabMass (ls : LabelledSystem State Label)
    (pe : ProbabilisticExecution ls.toSystem) (extLabs : List Label) :
    ls.traceProb pe (Seq.ofList extLabs) = ls.extLabMass pe extLabs (fun _ => 1) := by
  classical
  rw [ls.traceProb_eq_labProb_sum pe (Seq.ofList extLabs)]
  unfold LabelledSystem.extLabMass
  refine tsum_congr fun labs => ?_
  by_cases hc : ls.traceTightLabs (Seq.ofList extLabs) labs
  · simp only [if_pos hc]
    unfold ProbabilisticExecution.labMass
    simp only [mul_one]
  · simp only [if_neg hc]

/-- **Base of the external level-mass recursion.** The only tight execution with
empty external trace is `⟨s₀, nil⟩` (no transitions), so `extLabMass [] g` is the
initial `g`-expectation. -/
theorem LabelledSystem.extLabMass_nil (ls : LabelledSystem State Label)
    (pe : ProbabilisticExecution ls.toSystem) (g : State → ENNReal) :
    ls.extLabMass pe [] g = ∑' s₀ : State, pe.initState s₀ * g s₀ := by
  classical
  unfold LabelledSystem.extLabMass
  have h_iff : ∀ labs : List Label,
      ls.traceTightLabs (Seq.ofList ([] : List Label)) labs ↔ labs = [] := by
    intro labs
    unfold LabelledSystem.traceTightLabs
    rw [Stream'.Seq.ofList_nil]
    constructor
    · rintro ⟨h_filter, h_last⟩
      by_contra h_ne
      obtain ⟨last, h_gl⟩ : ∃ last, labs.getLast? = some last := by
        rcases h_last_opt : labs.getLast? with _ | last
        · exact absurd (List.getLast?_eq_none_iff.mp h_last_opt) h_ne
        · exact ⟨last, rfl⟩
      obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp h_gl
      have h_ext : ¬ ls.internal last := h_last last h_gl
      rw [Stream'.Seq.ofList_append, Stream'.Seq.filter_append _ _ _
        (Stream'.Seq.terminates_ofList ys)] at h_filter
      rw [Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil,
        Stream'.Seq.filter_cons_pos last _ h_ext] at h_filter
      have h_term : (Stream'.Seq.filter (fun l => ¬ ls.internal l) (Seq.ofList ys)).Terminates :=
        Stream'.Seq.terminates_filter _ _ (Stream'.Seq.terminates_ofList ys)
      have h_get := Stream'.Seq.get?_append_find h_term
        (Seq.cons last (Stream'.Seq.filter (fun l => ¬ ls.internal l) Seq.nil)) 0
      rw [h_filter] at h_get
      simp only [Stream'.Seq.get?_nil, Stream'.Seq.get?_cons_zero] at h_get
      cases h_get
    · rintro rfl
      refine ⟨?_, ?_⟩
      · rw [Stream'.Seq.ofList_nil, Stream'.Seq.filter_nil]
      · intro l hl; simp at hl
  simp_rw [h_iff]
  rw [tsum_eq_single [] (fun b hb => if_neg hb), if_pos rfl, pe.labMass_nil g]

/-! ### Kraft-bound infrastructure: front-peel of `probOf`

Generic machinery over an arbitrary `System` (not just `LabelledSystem`),
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

/-- `Seq.filter` of an `ofList` is the `ofList` of the corresponding `List.filter`. -/
private theorem ofList_filter_helper {α : Type} (p : α → Prop) [DecidablePred p]
    (l : List α) :
    (Seq.ofList l).filter p = Seq.ofList (l.filter (fun a => decide (p a))) := by
  induction l with
  | nil => rw [Seq.ofList_nil, Seq.filter_nil, List.filter_nil, Seq.ofList_nil]
  | cons a l ih =>
    rw [Seq.ofList_cons, List.filter_cons]
    by_cases h : p a
    · rw [Seq.filter_cons_pos a _ h, if_pos (by simpa using h), Seq.ofList_cons, ih]
    · rw [Seq.filter_cons_neg a _ h, if_neg (by simpa using h), ih]

open Classical in
/-- The label lists witnessing a fixed external trace `τ` (with the tightness
"ends external" condition) are prefix-free. -/
theorem LabelledSystem.traceTightLabs_prefixFree {S L : Type} (ls : LabelledSystem S L)
    (τ : Seq L) (a b : List L)
    (ha : ls.traceTightLabs τ a) (hb : ls.traceTightLabs τ b) (hab : a <+: b) :
    a = b := by
  classical
  obtain ⟨c, rfl⟩ := hab
  unfold LabelledSystem.traceTightLabs at ha hb
  -- Move both filter conditions to the list level via `ofList_filter_helper`.
  rw [ofList_filter_helper] at ha hb
  rw [List.filter_append] at hb
  -- `ofList` is injective, so the filtered label lists of `a` and `a ++ c` agree.
  have hkey : a.filter (fun l => decide (¬ ls.internal l))
      ++ c.filter (fun l => decide (¬ ls.internal l))
      = a.filter (fun l => decide (¬ ls.internal l)) := by
    apply Stream'.Seq.ofList_injective
    rw [ha.1, hb.1]
  have hcfil : c.filter (fun l => decide (¬ ls.internal l)) = [] :=
    List.append_right_eq_self.mp hkey
  -- Hence every label in `c` is internal.
  have hint : ∀ x ∈ c, ls.internal x := by
    intro x hx
    have := (List.filter_eq_nil_iff.mp hcfil) x hx
    simpa using this
  -- But the last label of `a ++ c` is external when `c ≠ []`, a contradiction.
  suffices hc : c = [] by rw [hc, List.append_nil]
  rcases List.eq_nil_or_concat c with hc | ⟨c', last, rfl⟩
  · exact hc
  · exfalso
    have hgl : (a ++ c'.concat last).getLast? = some last := by
      rw [List.concat_eq_append, List.getLast?_append, List.getLast?_append]; rfl
    have hext : ¬ ls.internal last := hb.2 last hgl
    have hmem : last ∈ c'.concat last := by
      rw [List.concat_eq_append]; exact List.mem_append_right _ (by simp)
    exact hext (hint last hmem)

/-- Distinct tight executions with the same external trace and same initial state
are prefix-incomparable: if one's transition list is a prefix of the other's, they
are equal. -/
theorem tight_trace_prefix_eq {State Label : Type} (ls : LabelledSystem State Label)
    {e e' : AlterSeq State Label} {τ : Seq Label}
    (he_term : e.trans.Terminates) (he'_term : e'.trans.Terminates)
    (he : ls.trace e = τ ∧ ls.IsTight e) (he' : ls.trace e' = τ ∧ ls.IsTight e')
    (h_init : e.init = e'.init)
    (h_pre : e.trans.toList he_term <+: e'.trans.toList he'_term) :
    e = e' := by
  classical
  set labs := (e.trans.toList he_term).map Prod.fst with hlabs
  set labs' := (e'.trans.toList he'_term).map Prod.fst with hlabs'
  have htt : ls.traceTightLabs τ labs := (ls.tight_iff τ e he_term).mp he
  have htt' : ls.traceTightLabs τ labs' := (ls.tight_iff τ e' he'_term).mp he'
  have hpre_labs : labs <+: labs' := List.IsPrefix.map Prod.fst h_pre
  have heqlabs : labs = labs' :=
    ls.traceTightLabs_prefixFree τ labs labs' htt htt' hpre_labs
  -- Equal label lists force equal transition-list lengths.
  have hlen : (e.trans.toList he_term).length = (e'.trans.toList he'_term).length := by
    have := congrArg List.length heqlabs
    rwa [hlabs, hlabs', List.length_map, List.length_map] at this
  -- A prefix of equal length is the whole list.
  have htl_eq : e.trans.toList he_term = e'.trans.toList he'_term := by
    obtain ⟨c, hc⟩ := h_pre
    have hcnil : c = [] := by
      have h2 := hlen
      rw [← hc, List.length_append] at h2
      have : c.length = 0 := by omega
      exact List.length_eq_zero_iff.mp this
    rw [← hc, hcnil, List.append_nil]
  -- Equal transition lists give equal `trans` sequences (apply `ofList`).
  have htrans : e.trans = e'.trans := by
    have := congrArg Stream'.Seq.ofList htl_eq
    rwa [Stream'.Seq.ofList_toList, Stream'.Seq.ofList_toList] at this
  cases e; cases e'
  simp only [AlterSeq.mk.injEq]
  exact ⟨h_init, htrans⟩

/-- **The trace probability is `≤ 1`** (Kraft bound). The tight trace-`τ`
executions have prefix-incomparable transition lists (within each initial state),
so their `probOf`-cylinders are disjoint sub-events; the partial sums are bounded by
`probOf_antichain`. -/
theorem LabelledSystem.traceProb_le_one {State Label : Type}
    (ls : LabelledSystem State Label)
    (pe : ProbabilisticExecution ls.toSystem) (τ : Seq Label) :
    ls.traceProb pe τ ≤ 1 := by
  classical
  unfold LabelledSystem.traceProb
  set T := {e : AlterSeq State Label // e.trans.Terminates ∧ ls.trace e = τ ∧ ls.IsTight e}
    with hT
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le (fun S => ?_)
  -- The finite support `S` projects to a finite set of executions `F`.
  set F : Finset (AlterSeq State Label) := S.image (fun x => x.1) with hF
  have hterm : ∀ a ∈ F, a.trans.Terminates := by
    intro a ha
    rw [hF, Finset.mem_image] at ha
    obtain ⟨x, _, rfl⟩ := ha
    exact x.2.1
  -- `F` is prefix-free by `tight_trace_prefix_eq`.
  have hpf : ∀ e (he : e ∈ F) e' (he' : e' ∈ F), e.init = e'.init →
      e.trans.toList (hterm e he) <+: e'.trans.toList (hterm e' he') → e = e' := by
    intro e he e' he' hinit hpre
    rw [hF, Finset.mem_image] at he he'
    obtain ⟨x, hxS, rfl⟩ := he
    obtain ⟨x', hx'S, rfl⟩ := he'
    exact tight_trace_prefix_eq ls (e := x.1) (e' := x'.1) (τ := τ) _ _
      ⟨x.2.2.1, x.2.2.2⟩ ⟨x'.2.2.1, x'.2.2.2⟩ hinit hpre
  have hbound := pe.probOf_antichain F hterm hpf
  -- A membership-independent summand (`dite` on `Terminates`) so we can reindex.
  set f : AlterSeq State Label → ENNReal :=
    fun a => if h : a.trans.Terminates then pe.probOf a h else 0 with hf
  have hattach : (∑ a ∈ F.attach, pe.probOf a.1 (hterm a.1 a.2)) = ∑ a ∈ F, f a := by
    rw [← Finset.sum_attach F f]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hf, dif_pos (hterm a.1 a.2)]
  -- `Subtype.val` is injective on `S`, so `Finset.sum_image` reindexes `F` onto `S`.
  have hinjon : Set.InjOn (fun x : T => x.1) (S : Set T) := by
    intro x _ y _ hxy
    exact Subtype.ext hxy
  have himage : (∑ a ∈ F, f a) = ∑ x ∈ S, f x.1 := by
    rw [hF]; exact Finset.sum_image hinjon
  have hfval : (∑ x ∈ S, f x.1) = ∑ x ∈ S, pe.probOf x.1 x.2.1 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hf, dif_pos x.2.1]
  calc (∑ x ∈ S, pe.probOf x.1 x.2.1)
      = ∑ a ∈ F.attach, pe.probOf a.1 (hterm a.1 a.2) := by
        rw [hattach, himage, hfval]
    _ ≤ 1 := hbound

/-! ### The expansion construction (M2)

Top-down skeleton. `expand_exists` is reduced to:
* `Scheduler.expand` — the `sys`-scheduler simulating `pe'` by running each weak
  step's witnessing chain (TO BE CONSTRUCTED, lower layers);
* `expand_traceProb_eq` — its trace-distribution agrees with `pe'` (TO BE PROVEN).
Both are stubbed here so the interface is fixed before the construction is built. -/

open Classical in
/-- A one-external-step, a.s.-stopping `sys`-scheduler realizing a single
`hyperStep`-style external move: from a starting state `s ∈ ν.support`, emit
`(l, μ)` with `μ ∼ κ s` (then halt); off `ν.support`, halt immediately. -/
noncomputable def Scheduler.extStep (sys : LabelledSystem State Label)
    (ν : PMF State) (l : Label) (κ : State → PMF (PMF State))
    (hκ : ∀ s ∈ ν.support, ∀ μ ∈ (κ s).support, sys.step s l μ) :
    Scheduler sys.toSystem where
  next e :=
    if e.trans = Seq.nil ∧ e.init ∈ ν.support then
      (κ e.init).map (fun μ => some (l, μ))
    else PMF.pure none
  valid := by
    intro e n s h_term h_state l' μ h_supp
    by_cases h_cond : e.trans = Seq.nil ∧ e.init ∈ ν.support
    · simp only [if_pos h_cond, PMF.mem_support_map_iff] at h_supp
      obtain ⟨μ', hμ'_supp, hμ'_eq⟩ := h_supp
      simp only [Option.some.injEq, Prod.mk.injEq] at hμ'_eq
      obtain ⟨h_l, h_μ⟩ := hμ'_eq
      subst h_l; subst h_μ
      have h_init_eq : s = e.init := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          have : e.stateAt 0 = some e.init := rfl
          rw [this] at h_state; exact (Option.some.inj h_state).symm
        · exfalso
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
          rw [hk] at h_state
          change (e.trans.get? k).map Prod.snd = some s at h_state
          rw [h_cond.1] at h_state; simp at h_state
      rw [h_init_eq]
      exact hκ e.init h_cond.2 μ' hμ'_supp
    · simp only [if_neg h_cond, PMF.mem_support_pure_iff] at h_supp
      exact absurd h_supp (by simp)

open Classical in
/-- `extStep`'s halting mass, integrated over the end-state against any `g`,
equals integrating `g` against the post-distribution `ν.bind (fun s => (κ s).bind id)`. -/
theorem extStep_pushforward (sys : LabelledSystem State Label)
    (ν : PMF State) (l : Label) (κ : State → PMF (PMF State))
    (hκ : ∀ s ∈ ν.support, ∀ μ ∈ (κ s).support, sys.step s l μ)
    (g : State → ENNReal) :
    (∑' e, (Scheduler.extStep sys ν l κ hκ).haltMass ν e * g (e.1.endState e.2))
      = ∑' t : State, (ν.bind (fun s => (κ s).bind id)) t * g t := by
  classical
  set σ := Scheduler.extStep sys ν l κ hκ with hσ
  set pe : ProbabilisticExecution sys.toSystem := ⟨ν, σ⟩ with hpe
  -- `σ.next` at the empty prefix from `s₀ ∈ ν.support` is `(κ s₀).map (some (l, ·))`.
  have hnext_active : ∀ s₀ : State, s₀ ∈ ν.support →
      σ.next ⟨s₀, Seq.nil⟩ = (κ s₀).map (fun μ => some (l, μ)) := by
    intro s₀ hs₀
    change (if (Seq.nil : Seq (Label × State)) = Seq.nil ∧ s₀ ∈ ν.support
      then (κ s₀).map (fun μ => some (l, μ)) else PMF.pure none) = _
    rw [if_pos ⟨rfl, hs₀⟩]
  -- The single-transition fiber terminates.
  have hcons_term : ∀ s' : State,
      (Seq.cons (l, s') Seq.nil : Seq (Label × State)).Terminates :=
    fun _ => Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
  -- `σ.next` emits `none` with mass `1` on any non-(active-empty) prefix.
  have hnext_none_one : ∀ e' : AlterSeq State Label,
      ¬(e'.trans = Seq.nil ∧ e'.init ∈ ν.support) → σ.next e' none = 1 := by
    intro e' hcond
    change (if e'.trans = Seq.nil ∧ e'.init ∈ ν.support
      then (κ e'.init).map (fun μ => some (l, μ)) else PMF.pure none) none = 1
    rw [if_neg hcond]; exact PMF.pure_apply_self none
  -- `σ.next` emits `none` with mass `0` on an active-empty prefix.
  have hnext_none_zero : ∀ e' : AlterSeq State Label,
      (e'.trans = Seq.nil ∧ e'.init ∈ ν.support) → σ.next e' none = 0 := by
    intro e' hcond
    change (if e'.trans = Seq.nil ∧ e'.init ∈ ν.support
      then (κ e'.init).map (fun μ => some (l, μ)) else PMF.pure none) none = 0
    rw [if_pos hcond]
    rw [PMF.map_apply]
    simp only [reduceCtorEq, if_false, tsum_zero]
  -- The one-step kernel from `⟨s₀, nil⟩` with `s₀ ∈ ν.support`.
  have hker : ∀ (s₀ s' : State), s₀ ∈ ν.support →
      pe.kernel ⟨s₀, Seq.nil⟩ (l, s') = ((κ s₀).bind id) s' := by
    intro s₀ s' hs₀
    unfold ProbabilisticExecution.kernel
    have hsched : pe.scheduler.next ⟨s₀, Seq.nil⟩ = (κ s₀).map (fun μ => some (l, μ)) := by
      rw [hpe]; exact hnext_active s₀ hs₀
    simp only [hsched]
    have hmap : ∀ μ : PMF State,
        ((κ s₀).map (fun μ => some (l, μ))) (some ((l, s').1, μ)) = κ s₀ μ := by
      intro μ
      rw [PMF.map_apply]
      rw [tsum_eq_single μ (by
        intro b hb
        rw [if_neg (by
          simp only [Option.some.injEq, Prod.mk.injEq]
          rintro ⟨_, h⟩; exact hb h.symm)])]
      rw [if_pos rfl]
    simp only [hmap]
    rw [PMF.bind_apply]
    rfl
  -- `probOf` of the single-transition fiber from `s₀ ∈ ν.support`.
  have hprob_fiber : ∀ (s₀ s' : State), s₀ ∈ ν.support →
      pe.probOf ⟨s₀, Seq.cons (l, s') Seq.nil⟩ (hcons_term s')
        = ν s₀ * ((κ s₀).bind id) s' := by
    intro s₀ s' hs₀
    have happ : (Seq.nil.append (Seq.cons (l, s') Seq.nil) : Seq (Label × State)).Terminates := by
      rw [Stream'.Seq.nil_append]; exact hcons_term s'
    have hrw : pe.probOf ⟨s₀, Seq.cons (l, s') Seq.nil⟩ (hcons_term s')
        = pe.probOf ⟨s₀, Seq.nil.append (Seq.cons (l, s') Seq.nil)⟩ happ := by
      congr 1; rw [Stream'.Seq.nil_append]
    rw [hrw, ProbabilisticExecution.probOf_append_singleton _ _ _ Stream'.Seq.terminates_nil _ happ,
      ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState, hker s₀ s' hs₀]
  -- The halting mass on a single-transition fiber from `s₀ ∈ ν.support`.
  have hhalt_fiber : ∀ (s₀ s' : State), s₀ ∈ ν.support →
      σ.haltMass ν ⟨⟨s₀, Seq.cons (l, s') Seq.nil⟩, hcons_term s'⟩
        = ν s₀ * ((κ s₀).bind id) s' := by
    intro s₀ s' hs₀
    unfold Scheduler.haltMass
    rw [← hpe, hprob_fiber s₀ s' hs₀]
    rw [hnext_none_one ⟨s₀, Seq.cons (l, s') Seq.nil⟩ (by
      rintro ⟨htr, _⟩; exact absurd htr (by simp)), mul_one]
  -- A nonzero one-step kernel forces the active-prefix shape.
  have hker_ne : ∀ (init : State) (previous : Seq (Label × State)) (last : Label × State),
      pe.kernel ⟨init, previous⟩ last ≠ 0 →
      (init ∈ ν.support ∧ previous = Seq.nil ∧ last.1 = l) := by
    intro init previous last hne
    by_cases hcond : previous = Seq.nil ∧ init ∈ ν.support
    · refine ⟨hcond.2, hcond.1, ?_⟩
      by_contra hl
      apply hne
      unfold ProbabilisticExecution.kernel
      have hsched : pe.scheduler.next ⟨init, previous⟩ = (κ init).map (fun μ => some (l, μ)) := by
        rw [hpe]; rw [hcond.1]; exact hnext_active init hcond.2
      simp only [hsched]
      have hz : ∀ μ : PMF State,
          ((κ init).map (fun μ => some (l, μ))) (some (last.1, μ)) = 0 := by
        intro μ
        rw [PMF.map_apply]
        refine ENNReal.tsum_eq_zero.mpr (fun a => ?_)
        rw [if_neg]
        simp only [Option.some.injEq, Prod.mk.injEq]
        rintro ⟨h_eq, _⟩; exact hl h_eq
      simp only [hz, zero_mul, tsum_zero]
    · exfalso
      apply hne
      unfold ProbabilisticExecution.kernel
      have hsched : pe.scheduler.next ⟨init, previous⟩ = PMF.pure none := by
        rw [hpe]
        change (if previous = Seq.nil ∧ init ∈ ν.support
          then (κ init).map (fun μ => some (l, μ)) else PMF.pure none) = _
        rw [if_neg hcond]
      simp only [hsched]
      have hz : ∀ μ : PMF State,
          (PMF.pure none : PMF (Option (Label × PMF State))) (some (last.1, μ)) = 0 :=
        fun μ => PMF.pure_apply_of_ne _ _ (by simp)
      simp only [hz, zero_mul, tsum_zero]
  -- Support condition: nonzero halting mass forces the single-transition fiber.
  have hsupp : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      σ.haltMass ν e ≠ 0 →
      ∃ s₀ s' : State, s₀ ∈ ν.support ∧
        (⟨s₀, Seq.cons (l, s') Seq.nil⟩ : AlterSeq State Label) = e.1 := by
    rintro ⟨⟨init', trans'⟩, hterm⟩ hne
    simp only at hterm hne ⊢
    have hprob_ne : pe.probOf ⟨init', trans'⟩ hterm ≠ 0 := by
      intro h0; apply hne
      unfold Scheduler.haltMass; rw [← hpe, h0, zero_mul]
    have hnone_ne : σ.next ⟨init', trans'⟩ none ≠ 0 := by
      intro h0; apply hne
      unfold Scheduler.haltMass; rw [← hpe, h0, mul_zero]
    have hncond : ¬((⟨init', trans'⟩ : AlterSeq State Label).trans = Seq.nil ∧
        (⟨init', trans'⟩ : AlterSeq State Label).init ∈ ν.support) := by
      intro hcond; exact hnone_ne (hnext_none_zero _ hcond)
    -- `trans' ≠ nil`: else `probOf` would be `ν init'`, and active-empty would hold.
    have htrans_ne : trans' ≠ Seq.nil := by
      intro hnil
      apply hncond
      refine ⟨hnil, ?_⟩
      change init' ∈ ν.support
      rw [PMF.mem_support_iff]
      intro hinit
      apply hprob_ne
      have hrw : pe.probOf ⟨init', trans'⟩ hterm
          = pe.probOf ⟨init', Seq.nil⟩ Stream'.Seq.terminates_nil := by
        subst hnil; rfl
      rw [hrw, ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState]
      exact hinit
    -- Peel the last transition.
    have hnonempty : trans'.toList hterm ≠ [] := by
      intro hnil; apply htrans_ne
      have := Stream'.Seq.ofList_toList trans' hterm
      rw [hnil, Stream'.Seq.ofList_nil] at this; exact this.symm
    obtain ⟨previous, last, h_prev, h_split, _, _⟩ :=
      Stream'.Seq.exists_split_last trans' hterm hnonempty
    have hprob_split : pe.probOf ⟨init', trans'⟩ hterm
        = pe.probOf ⟨init', previous⟩ h_prev * pe.kernel ⟨init', previous⟩ last := by
      have happ : (previous.append (Seq.cons last Seq.nil)).Terminates := h_split ▸ hterm
      have hrw : pe.probOf ⟨init', trans'⟩ hterm
          = pe.probOf ⟨init', previous.append (Seq.cons last Seq.nil)⟩ happ := by
        exact h_split ▸ rfl
      rw [hrw, ProbabilisticExecution.probOf_append_singleton _ _ _ h_prev _ happ]
    have hker_ne' : pe.kernel ⟨init', previous⟩ last ≠ 0 := by
      intro h0; apply hprob_ne; rw [hprob_split, h0, mul_zero]
    obtain ⟨hinit_supp, hprev_nil, hlast⟩ := hker_ne _ _ _ hker_ne'
    refine ⟨init', last.2, hinit_supp, ?_⟩
    have htrans_eq : trans' = Seq.cons (l, last.2) Seq.nil := by
      rw [h_split, hprev_nil, Stream'.Seq.nil_append]
      obtain ⟨l', s'⟩ := last
      simp only at hlast
      rw [hlast]
    exact AlterSeq.mk.injEq .. ▸ ⟨rfl, htrans_eq.symm⟩
  -- The fiber map `(s₀, s') ↦ ⟨s₀, cons (l, s') nil⟩` is injective.
  have hi_inj :
      Function.Injective
        (fun p : State × State =>
          (⟨⟨p.1, Seq.cons (l, p.2) Seq.nil⟩, hcons_term p.2⟩
            : {e : AlterSeq State Label // e.trans.Terminates})) := by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hab
    have h := Subtype.ext_iff.mp hab
    simp only at h
    have h_init := congrArg AlterSeq.init h
    have h_trans := congrArg AlterSeq.trans h
    simp only at h_init h_trans
    have h2 : a₂ = b₂ := by
      have := (Stream'.Seq.cons_eq_cons.mp h_trans).1
      exact (Prod.mk.injEq l a₂ l b₂ ▸ this).2
    rw [h_init, h2]
  -- Reindex the LHS sum over single-transition fibers parameterized by `State × State`.
  have hmid :
      (∑' e, σ.haltMass ν e * g (e.1.endState e.2))
        = ∑' p : State × State, ν p.1 * ((κ p.1).bind id) p.2 * g p.2 := by
    refine tsum_eq_tsum_of_ne_zero_bij
      (i := fun p : (Function.support
          (fun q : State × State => ν q.1 * ((κ q.1).bind id) q.2 * g q.2)) =>
          (⟨⟨p.1.1, Seq.cons (l, p.1.2) Seq.nil⟩, hcons_term p.1.2⟩
            : {e : AlterSeq State Label // e.trans.Terminates}))
      ?_ ?_ ?_
    · -- injectivity
      intro p q hpq
      exact Subtype.ext (hi_inj hpq)
    · -- support ⊆ range
      intro e he
      obtain ⟨s₀, s', hs₀, hfib⟩ := hsupp e (by
        intro h0; rw [Function.mem_support] at he; rw [h0, zero_mul] at he; exact he rfl)
      -- Replace `e` by its explicit single-transition form.
      have he_eq : e = ⟨⟨s₀, Seq.cons (l, s') Seq.nil⟩, hcons_term s'⟩ :=
        Subtype.ext hfib.symm
      subst he_eq
      rw [Function.mem_support] at he
      have hp_ne : ν s₀ * ((κ s₀).bind id) s' * g s' ≠ 0 := by
        intro h0
        apply he
        rw [AlterSeq.endState_singleton_cons, hhalt_fiber s₀ s' hs₀, h0]
      exact ⟨⟨(s₀, s'), hp_ne⟩, rfl⟩
    · -- value match
      rintro ⟨⟨s₀, s'⟩, hp⟩
      simp only
      rw [show ((⟨⟨s₀, Seq.cons (l, s') Seq.nil⟩, hcons_term s'⟩
          : {e : AlterSeq State Label // e.trans.Terminates}).1.endState
            (⟨⟨s₀, Seq.cons (l, s') Seq.nil⟩, hcons_term s'⟩
              : {e : AlterSeq State Label // e.trans.Terminates}).2)
          = s' from AlterSeq.endState_singleton_cons s₀ l s']
      have hs₀ : s₀ ∈ ν.support := by
        rw [PMF.mem_support_iff]
        intro h0
        rw [Function.mem_support] at hp
        apply hp
        simp only
        rw [h0, zero_mul, zero_mul]
      rw [hhalt_fiber s₀ s' hs₀]
  rw [hmid]
  -- Collapse the pair sum onto the bind.
  rw [ENNReal.tsum_prod']
  -- RHS: expand the bind and pull `g t` out of the inner sum.
  have hrhs : (∑' t : State, (ν.bind (fun s => (κ s).bind id)) t * g t)
      = ∑' (t : State) (s₀ : State), ν s₀ * ((κ s₀).bind id) t * g t := by
    apply tsum_congr; intro t
    rw [PMF.bind_apply, ENNReal.tsum_mul_right]
  rw [hrhs, ENNReal.tsum_comm]

open Classical in
/-- The per-weak-step witness `sys`-scheduler realizing a `sys^w` step
`s -[l]→ μ`: the `weakTau` witness if `l` internal; else the external chain
`weakTau-pre ; one hyperStep l ; weakTau-post` composed with `Scheduler.bind`. -/
noncomputable def Scheduler.weakStepWitness (sys : LabelledSystem State Label)
    (s : State) (l : Label) (μ : PMF State) (h : sys^w.step s l μ) :
    Scheduler sys.toSystem :=
  if h_int : sys.internal l then
    let hwt : weakTau sys (PMF.pure s) μ := (h.resolve_right (fun hb => hb.1 h_int)).2
    hwt.witnessScheduler.toScheduler
  else
    let hws : weakStep sys (PMF.pure s) l μ := (h.resolve_left (fun ha => h_int ha.1)).2
    Scheduler.bind hws.weakTau_pre.witnessScheduler.toScheduler (fun _ =>
      Scheduler.bind (Scheduler.extStep sys hws.preDist l hws.hyperStep_mid.kernel
          (hws.hyperStep_mid.kernel_step))
        (fun _ => hws.weakTau_post.witnessScheduler.toScheduler))

theorem Scheduler.weakStepWitness_pushforward (sys : LabelledSystem State Label)
    (s : State) (l : Label) (μ : PMF State) (h : sys^w.step s l μ) (g : State → ENNReal) :
    (∑' e, (Scheduler.weakStepWitness sys s l μ h).haltMass (PMF.pure s) e * g (e.1.endState e.2))
      = ∑' t, μ t * g t := by
  classical
  by_cases h_int : sys.internal l
  · have hwt : weakTau sys (PMF.pure s) μ := (h.resolve_right (fun hb => hb.1 h_int)).2
    have hsched : Scheduler.weakStepWitness sys s l μ h = hwt.witnessScheduler.toScheduler := by
      unfold Scheduler.weakStepWitness; rw [dif_pos h_int]
    rw [hsched]
    exact hwt.integrate g
  · have hws : weakStep sys (PMF.pure s) l μ := (h.resolve_left (fun ha => h_int ha.1)).2
    set ν := hws.preDist with hν
    set ν' := hws.postDist with hν'
    have h_pre : weakTau sys (PMF.pure s) ν := hws.weakTau_pre
    have h_mid : hyperStep sys ν l ν' := hws.hyperStep_mid
    have h_post : weakTau sys ν' μ := hws.weakTau_post
    set σpre := h_pre.witnessScheduler.toScheduler with hσpre
    set σext := Scheduler.extStep sys ν l h_mid.kernel h_mid.kernel_step with hσext
    set σpost := h_post.witnessScheduler.toScheduler with hσpost
    have hsched : Scheduler.weakStepWitness sys s l μ h
        = Scheduler.bind σpre (fun _ => Scheduler.bind σext (fun _ => σpost)) := by
      unfold Scheduler.weakStepWitness; rw [dif_neg h_int]
    rw [hsched]
    -- Step 1: outer bind composition.
    rw [Scheduler.bind_compose_integrate σpre (fun _ =>
      Scheduler.bind σext (fun _ => σpost)) (PMF.pure s) g]
    -- INNER r := ∑' f₂, (σext.bind (fun _ => σpost)).haltMass (pure r) f₂ * g(f₂.end)
    set INNER : State → ENNReal := fun r =>
      ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
        (Scheduler.bind σext (fun _ => σpost)).haltMass (PMF.pure r) f₂
          * g (f₂.1.endState f₂.2) with hINNER
    -- Step 2: τ-collapse the pre-segment via `weakTau.integrate h_pre`.
    have h2 := h_pre.integrate INNER
    -- Bridge the `WeakScheduler.haltMass`/`Scheduler.haltMass` defeq and fold `INNER`.
    rw [show (∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
          σpre.haltMass (PMF.pure s) f₁ *
            ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
              (Scheduler.bind σext (fun _ => σpost)).haltMass (PMF.pure (f₁.1.endState f₁.2)) f₂
                * g (f₂.1.endState f₂.2))
        = ∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
            h_pre.witnessScheduler.haltMass (PMF.pure s) f₁ * INNER (f₁.1.endState f₁.2) from rfl,
      h2]
    -- POST r' := ∑' f₃, σpost.haltMass (pure r') f₃ * g(f₃.end)
    set POST : State → ENNReal := fun r' =>
      ∑' f₃ : {e : AlterSeq State Label // e.trans.Terminates},
        σpost.haltMass (PMF.pure r') f₃ * g (f₃.1.endState f₃.2) with hPOST
    -- Step 3: unfold each `INNER r` via the inner bind composition.
    have h3 : ∀ r : State, INNER r
        = ∑' f₂' : {e : AlterSeq State Label // e.trans.Terminates},
            σext.haltMass (PMF.pure r) f₂' * POST (f₂'.1.endState f₂'.2) := by
      intro r
      rw [hINNER]
      exact Scheduler.bind_compose_integrate σext (fun _ => σpost) (PMF.pure r) g
    rw [tsum_congr (fun r => by rw [h3 r])]
    -- Step 4: pull `ν r` in, swap, and fold the source-mixture via `haltMass_init_mix`.
    have hpull : ∀ r : State,
        ν r * (∑' f₂' : {e : AlterSeq State Label // e.trans.Terminates},
            σext.haltMass (PMF.pure r) f₂' * POST (f₂'.1.endState f₂'.2))
          = ∑' f₂' : {e : AlterSeq State Label // e.trans.Terminates},
              ν r * σext.haltMass (PMF.pure r) f₂' * POST (f₂'.1.endState f₂'.2) := by
      intro r
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr (fun f₂' => by ring)
    rw [tsum_congr hpull, ENNReal.tsum_comm]
    have hmix : ∀ f₂' : {e : AlterSeq State Label // e.trans.Terminates},
        (∑' r : State, ν r * σext.haltMass (PMF.pure r) f₂' * POST (f₂'.1.endState f₂'.2))
          = σext.haltMass ν f₂' * POST (f₂'.1.endState f₂'.2) := by
      intro f₂'
      rw [ENNReal.tsum_mul_right, ← Scheduler.haltMass_init_mix σext ν f₂']
    rw [tsum_congr hmix]
    -- Step 5: push the external step forward; rewrite the bind back to `ν'`.
    rw [hσext, extStep_pushforward sys ν l h_mid.kernel h_mid.kernel_step POST,
      ← h_mid.post_eq_bind]
    -- Step 6: τ-collapse the post-segment (same `haltMass_init_mix`/`integrate` pattern).
    have hpull' : ∀ t : State, ν' t * POST t
        = ∑' f₃ : {e : AlterSeq State Label // e.trans.Terminates},
            ν' t * σpost.haltMass (PMF.pure t) f₃ * g (f₃.1.endState f₃.2) := by
      intro t
      rw [hPOST, ← ENNReal.tsum_mul_left]
      exact tsum_congr (fun f₃ => by ring)
    rw [tsum_congr hpull', ENNReal.tsum_comm]
    have hmix' : ∀ f₃ : {e : AlterSeq State Label // e.trans.Terminates},
        (∑' t : State, ν' t * σpost.haltMass (PMF.pure t) f₃ * g (f₃.1.endState f₃.2))
          = σpost.haltMass ν' f₃ * g (f₃.1.endState f₃.2) := by
      intro f₃
      rw [ENNReal.tsum_mul_right, ← Scheduler.haltMass_init_mix σpost ν' f₃]
    rw [tsum_congr hmix']
    exact h_post.integrate g

theorem Scheduler.weakStepWitness_haltMass_one (sys : LabelledSystem State Label)
    (s : State) (l : Label) (μ : PMF State) (h : sys^w.step s l μ) :
    (∑' e, (Scheduler.weakStepWitness sys s l μ h).haltMass (PMF.pure s) e) = 1 := by
  have hp := Scheduler.weakStepWitness_pushforward sys s l μ h (fun _ => 1)
  simp only [mul_one] at hp
  rw [hp, PMF.tsum_coe]

/-- A trivially-valid `sys`-scheduler that halts immediately (emits `none`). -/
noncomputable def Scheduler.haltNow (sys : LabelledSystem State Label) :
    Scheduler sys.toSystem where
  next _ := PMF.pure none
  valid := by
    intro e n s _ _ l μ h_supp
    -- support of `pure none` is `{none}`; `some (l,μ) ∉ {none}`.
    simp only [PMF.support_pure, Set.mem_singleton_iff] at h_supp
    exact absurd h_supp (by simp)

open Classical in
/-- The per-weak-step witness extended to all `(l, μ)`: the genuine
`weakStepWitness` when `sys^w.step s l μ` holds, else the immediate-halt scheduler.
(`expand.next` applies this to scheduler emissions; validity is recovered at the
support, where `sys^w.step` holds.) -/
noncomputable def Scheduler.weakStepWitnessTotal (sys : LabelledSystem State Label)
    (s : State) (l : Label) (μ : PMF State) : Scheduler sys.toSystem :=
  if h : sys^w.step s l μ then Scheduler.weakStepWitness sys s l μ h else Scheduler.haltNow sys

/-- When the weak step is real, `weakStepWitnessTotal` is the genuine witness. -/
theorem Scheduler.weakStepWitnessTotal_eq (sys : LabelledSystem State Label)
    (s : State) (l : Label) (μ : PMF State) (h : sys^w.step s l μ) :
    Scheduler.weakStepWitnessTotal sys s l μ = Scheduler.weakStepWitness sys s l μ h := by
  unfold Scheduler.weakStepWitnessTotal; rw [dif_pos h]

open Classical in
/-- Un-normalized **trace-cone belief weight** over `sys^w`-histories: the
`probOf`-mass of terminating, tight `sys^w`-histories whose external trace is
`τ`. (Stutter-invariant: conditions on the external trace, not the full
weak-step label list.) -/
noncomputable def ProbabilisticExecution.beliefExpandW {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (τ : Seq Label)
    (E : AlterSeq State Label) : ENNReal :=
  if h : E.trans.Terminates ∧ sys^w.trace E = τ ∧ sys^w.IsTight E then
    pe'.probOf E h.1
  else 0

/-- The trace-cone belief weight sums to `≤ 1` — exactly `sys^w.traceProb pe' τ`. -/
theorem ProbabilisticExecution.beliefExpandW_tsum_le_one {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (τ : Seq Label) :
    (∑' E : AlterSeq State Label, pe'.beliefExpandW τ E) ≤ 1 := by
  classical
  set P : AlterSeq State Label → Prop := fun E =>
    E.trans.Terminates ∧ sys^w.trace E = τ ∧ sys^w.IsTight E with hP
  have heq : (∑' E : AlterSeq State Label, pe'.beliefExpandW τ E)
      = sys^w.traceProb pe' τ := by
    rw [LabelledSystem.traceProb]
    -- Rewrite the subtype-sum summand `probOf ↑e _` as `beliefExpandW ↑e` (dif_pos via e.2).
    have hsub : (∑' e : {e : AlterSeq State Label // P e}, pe'.probOf e.1 e.2.1)
        = ∑' e : {e : AlterSeq State Label // P e}, pe'.beliefExpandW τ e.1 := by
      refine tsum_congr (fun e => ?_)
      rw [ProbabilisticExecution.beliefExpandW, dif_pos e.2]
    rw [hsub]
    -- `∑' e : ↥{P}, beliefExpandW e.1 = ∑' E, indicator E = ∑' E, beliefExpandW E`.
    have hts : (∑' e : {e : AlterSeq State Label // P e}, pe'.beliefExpandW τ e.1)
        = ∑' E : AlterSeq State Label,
            ({E : AlterSeq State Label | P E}).indicator (pe'.beliefExpandW τ) E :=
      tsum_subtype {E : AlterSeq State Label | P E} (pe'.beliefExpandW τ)
    rw [hts]
    refine (tsum_congr (fun E => ?_)).symm
    by_cases hc : P E
    · exact Set.indicator_of_mem (s := {E : AlterSeq State Label | P E}) hc _
    · rw [Set.indicator_of_notMem (s := {E : AlterSeq State Label | P E}) hc,
        ProbabilisticExecution.beliefExpandW, dif_neg hc]
  rw [heq]
  exact sys^w.traceProb_le_one pe' τ

/-- Hence the normalizer is finite. -/
theorem ProbabilisticExecution.beliefExpandW_tsum_ne_top {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (τ : Seq Label) :
    (∑' E : AlterSeq State Label, pe'.beliefExpandW τ E) ≠ ⊤ :=
  (lt_of_le_of_lt (pe'.beliefExpandW_tsum_le_one τ) ENNReal.one_lt_top).ne

open Classical in
/-- The normalized **trace-cone belief** PMF (fallback `pure ⟨sys.init, nil⟩` when
the weight is `0`). -/
noncomputable def ProbabilisticExecution.beliefExpand {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (τ : Seq Label) :
    PMF (AlterSeq State Label) :=
  if h0 : (∑' E, pe'.beliefExpandW τ E) ≠ 0 then
    PMF.normalize (pe'.beliefExpandW τ) h0 (pe'.beliefExpandW_tsum_ne_top τ)
  else
    PMF.pure (⟨sys.toSystem.init, Seq.nil⟩ : AlterSeq State Label)

open Classical in
/-- The post-τ-closure witness of the weak step `s_prev →[a] μ` (external `a`),
as a `sys`-scheduler; `haltNow` when there is no such external weak step. (Used by
`expand` to realize the carried-over post-τ-closure of the just-completed external
weak step.) -/
noncomputable def Scheduler.postTauWitness (sys : LabelledSystem State Label)
    (s_prev : State) (a : Label) (μ : PMF State) : Scheduler sys.toSystem :=
  if h : (¬ sys.internal a) ∧ sys^w.step s_prev a μ then
    ((h.2.resolve_left (fun hl => h.1 hl.1)).2).weakTau_post.witnessScheduler.toScheduler
  else Scheduler.haltNow sys

/-- At a `sys^w`-history `E`, draw the next weak step `(l, μ) ∼ pe'.scheduler.next E`
and run its total witness from state `s`. The validity is recovered at the support:
on a real emission `(l, μ)`, the per-step total witness is a valid `sys`-scheduler. -/
noncomputable def Scheduler.nextSegment (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (E : AlterSeq State Label) (s : State) :
    Scheduler sys.toSystem where
  next e' := (pe'.scheduler.next E).bind (fun opt =>
    match opt with
    | none => PMF.pure none
    | some (l, μ) => (Scheduler.weakStepWitnessTotal sys s l μ).next e')
  valid := by
    intro e' n s' hterm hstate l' μ' h_supp
    rw [PMF.mem_support_bind_iff] at h_supp
    obtain ⟨opt, _, h_supp⟩ := h_supp
    cases opt with
    | none =>
      change some (l', μ') ∈ (PMF.pure (α := Option (Label × PMF State)) none).support at h_supp
      rw [PMF.support_pure, Set.mem_singleton_iff] at h_supp
      exact absurd h_supp (by simp)
    | some lμ =>
      obtain ⟨l, μ⟩ := lμ
      change some (l', μ') ∈
        ((Scheduler.weakStepWitnessTotal sys s l μ).next e').support at h_supp
      exact (Scheduler.weakStepWitnessTotal sys s l μ).valid e' n s' hterm hstate l' μ' h_supp

/-! #### `internalSuffix`: the maximal all-internal tail of an execution -/

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

/-- `toList` is invariant under equality of the underlying `Seq` (the termination
proofs are irrelevant). -/
theorem Stream'.Seq.toList_congr_pub {γ : Type} {s t : Seq γ} (heq : s = t)
    (hs : s.Terminates) (ht : t.Terminates) : s.toList hs = t.toList ht := by subst heq; rfl

/-- `(s.drop j).toList` is the `List.drop j` of `s.toList`. -/
theorem Stream'.Seq.drop_toList_eq_pub {γ : Type} (s : Seq γ) (h : s.Terminates) (j : ℕ)
    (hd : (s.drop j).Terminates) : (s.drop j).toList hd = (s.toList h).drop j := by
  have key : s.drop j = Seq.ofList ((s.toList h).drop j) := by
    conv_lhs => rw [← Stream'.Seq.ofList_toList s h]; rw [Stream'.Seq.drop_ofList_pub]
  rw [Stream'.Seq.toList_congr_pub key hd (Stream'.Seq.terminates_ofList _),
    Stream'.Seq.toList_ofList]

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

open Classical in
/-- Posterior over the distribution `μ` that `pe'` emitted for `E`'s last weak step,
given `E`'s last transition `(a, s_last)` and the preceding history `E'`. Weight
`μ ↦ pe'.scheduler.next E' (some (a, μ)) * μ s_last`, normalized by the last-step
kernel. Fallback `pure (PMF.pure E.init)` when `E` is empty/non-terminating or the
weight vanishes. -/
noncomputable def ProbabilisticExecution.lastMuBelief
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (E : AlterSeq State Label) : PMF (PMF State) :=
  if hT : E.trans.Terminates then
    if hne : E.trans.toList hT ≠ [] then
      let spl := Stream'.Seq.exists_split_last E.trans hT hne
      let prev := spl.choose
      let last := spl.choose_spec.choose
      let E' : AlterSeq State Label := ⟨E.init, prev⟩
      let a := last.1
      let s_last := last.2
      let w : PMF State → ENNReal := fun μ => pe'.scheduler.next E' (some (a, μ)) * μ s_last
      if h0 : (∑' μ, w μ) ≠ 0 then
        PMF.normalize w h0
          (by
            have hwtsum : (∑' μ, w μ) = pe'.kernel E' (a, s_last) := rfl
            rw [hwtsum]
            exact ne_top_of_le_ne_top ENNReal.one_ne_top (pe'.kernel_le_one E' (a, s_last)))
      else PMF.pure (PMF.pure E.init)
    else PMF.pure (PMF.pure E.init)
  else PMF.pure (PMF.pure E.init)

open Classical in
/-- The carried-over post-τ-closure witness for a `sys^w`-history `E` with last
emitted distribution `μ_k`: the post-τ-closure of `E`'s last *external* weak step
`(a)` from its preceding history `E'`'s end-state, with distribution `μ_k`.
Degenerates to `haltNow` when `E` is empty/non-terminating. A valid `sys`-scheduler
in every branch (`postTauWitness`/`haltNow` are valid). -/
noncomputable def Scheduler.expandPostScheduler (sys : LabelledSystem State Label)
    (E : AlterSeq State Label) (μ_k : PMF State) : Scheduler sys.toSystem :=
  if hT : E.trans.Terminates then
    if hne : E.trans.toList hT ≠ [] then
      let spl := Stream'.Seq.exists_split_last E.trans hT hne
      Scheduler.postTauWitness sys
        ((⟨E.init, spl.choose⟩ : AlterSeq State Label).endState spl.choose_spec.choose_spec.choose)
        spl.choose_spec.choose.1
        μ_k
    else Scheduler.haltNow sys
  else Scheduler.haltNow sys

/-- **The expand scheduler** (M2 witness). Simulates `pe'`
over `sys^w` by a `sys`-scheduler that, at each `sys`-history, runs the
witnessing chain of `pe'`'s current weak step: a run-to-halt `weakTau` τ-closure,
possibly one external `hyperStep`, another τ-closure. The hidden "where in the
expansion am I" is resolved by a belief (external-skeleton over `sys^w`-histories
+ `WeakScheduler.bind` for the internal segments). -/
noncomputable def Scheduler.expand (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) : Scheduler sys.toSystem where
  next e :=
    open Classical in
    if h_term : e.trans.Terminates then
      (pe'.beliefExpand (sys.trace e)).bind (fun E =>
        (pe'.lastMuBelief E).bind (fun μ_k =>
          (Scheduler.bind (Scheduler.expandPostScheduler sys E μ_k)
            (Scheduler.nextSegment sys pe' E)).next (sys.internalSuffix e)))
    else PMF.pure none
  valid := by
    classical
    intro e n s e_term_n e_stateAt_eq l μ h_supp
    have h_term : e.trans.Terminates := ⟨n, e_term_n⟩
    have h_find_le : Nat.find h_term ≤ n := Nat.find_le e_term_n
    have h_n_le : n ≤ Nat.find h_term := by
      by_contra h_lt
      push Not at h_lt
      rcases n with _ | k
      · exact absurd h_lt (Nat.not_lt_zero _)
      · have hk_ge : Nat.find h_term ≤ k := Nat.lt_succ_iff.mp h_lt
        have h_term_k : e.trans.TerminatedAt k :=
          Stream'.Seq.terminated_stable e.trans hk_ge (Nat.find_spec h_term)
        have h_state_none : e.stateAt (k + 1) = none := by
          change (e.trans.get? k).map Prod.snd = none
          rw [show e.trans.get? k = none from h_term_k]
          rfl
        rw [h_state_none] at e_stateAt_eq
        exact Option.some_ne_none s e_stateAt_eq.symm
    have h_n_eq : n = Nat.find h_term := le_antisymm h_n_le h_find_le
    have h_s_eq : s = e.endState h_term := by
      have h := AlterSeq.stateAt_find_eq_endState e h_term
      rw [← h_n_eq] at h
      rw [h] at e_stateAt_eq
      exact (Option.some.inj e_stateAt_eq).symm
    subst h_s_eq
    -- Reduce `next e` to the belief-bind branch.
    change some (l, μ) ∈
      (open Classical in
        if h_term' : e.trans.Terminates then
          (pe'.beliefExpand (sys.trace e)).bind (fun E =>
            (pe'.lastMuBelief E).bind (fun μ_k =>
              (Scheduler.bind (Scheduler.expandPostScheduler sys E μ_k)
                (Scheduler.nextSegment sys pe' E)).next (sys.internalSuffix e)))
        else PMF.pure none).support at h_supp
    rw [dif_pos h_term] at h_supp
    rw [PMF.mem_support_bind_iff] at h_supp
    obtain ⟨E, _, h_supp⟩ := h_supp
    rw [PMF.mem_support_bind_iff] at h_supp
    obtain ⟨μ_k, _, h_supp⟩ := h_supp
    -- `internalSuffix e` terminates (it's a suffix of the terminating `e`).
    have h'' : (sys.internalSuffix e).trans.Terminates := by
      rw [LabelledSystem.internalSuffix, dif_pos h_term]
      exact Stream'.Seq.drop_terminates_pub h_term _
    -- Apply validity of the (valid) bound scheduler at the canonical end of `internalSuffix e`.
    set σ : Scheduler sys.toSystem :=
      Scheduler.bind (Scheduler.expandPostScheduler sys E μ_k) (Scheduler.nextSegment sys pe' E)
      with hσ
    have hvalid := σ.valid (sys.internalSuffix e) (Nat.find h'')
      ((sys.internalSuffix e).endState h'') (Nat.find_spec h'')
      (AlterSeq.stateAt_find_eq_endState (sys.internalSuffix e) h'') l μ h_supp
    -- Bridge the end-state of the suffix back to `e`'s end-state.
    rwa [sys.internalSuffix_endState e h_term h''] at hvalid

/-- **Trace preservation for `Scheduler.expand`** (the M2 core, TO BE PROVEN):
the expanded `sys`-execution has the same trace distribution as `pe'`. Proven by
grouping both `traceProb`s by external trace and matching per `sys^w`-execution,
using a.s.-termination of the witnesses (mass preservation) and
`hyperStep_marginal_decomp` for the external steps. -/
theorem expand_traceProb_eq (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (h_init : pe'.initState = PMF.pure sys^w.toSystem.init) (τ : Seq Label) :
    sys.traceProb ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ τ
      = sys^w.traceProb pe' τ :=
  sorry

/-- **Expansion existence (the M2 core).** Every probabilistic execution of
`sys^w` from the Dirac initial state is matched, trace-distribution-wise, by a
probabilistic execution of `sys`. Assembled from `Scheduler.expand` and
`expand_traceProb_eq`. -/
theorem expand_exists (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (h_init : pe'.initState = PMF.pure sys^w.toSystem.init) :
    ∃ pe : ProbabilisticExecution sys.toSystem,
      pe.initState = PMF.pure sys.toSystem.init ∧
      ∀ τ, sys.traceProb pe τ = sys^w.traceProb pe' τ :=
  ⟨⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩, rfl,
    fun τ => expand_traceProb_eq sys pe' h_init τ⟩

/-- **Hard direction of `weakClosure_traceProb_eq`**: every trace distribution
achievable by `sys^w` is achievable by `sys`. Reduces to `expand_exists`. -/
theorem weakClosure_traceProb_superset (sys : LabelledSystem State Label) :
    achievableTraceDists sys^w ⊆ achievableTraceDists sys := by
  rintro D ⟨pe', h_init, hpe'⟩
  obtain ⟨pe, hpe_init, hpe_trace⟩ := expand_exists sys pe' h_init
  exact ⟨pe, hpe_init, fun τ => (hpe_trace τ).trans (hpe' τ)⟩

/-- **Weak-closure construction preserves trace distributions.** -/
theorem weakClosure_traceProb_eq (sys : LabelledSystem State Label) :
    achievableTraceDists sys = achievableTraceDists sys^w :=
  Set.Subset.antisymm
    (weakClosure_traceProb_subset sys)
    (weakClosure_traceProb_superset sys)

end PLTS
