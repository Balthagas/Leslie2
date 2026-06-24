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
/-- **Shape of `extStep`'s halting executions from a Dirac source.** If
`extStep`'s halting mass from `PMF.pure r` at `E` is nonzero, then either
`r ∉ ν.support` and `E` is the empty execution `⟨r, nil⟩` (immediate halt), or
`r ∈ ν.support` and `E` is the single external transition `⟨r, cons (l, s') nil⟩`. -/
theorem extStep_haltMass_ne_zero (sys : LabelledSystem State Label)
    (ν : PMF State) (l : Label) (κ : State → PMF (PMF State))
    (hκ : ∀ s ∈ ν.support, ∀ μ ∈ (κ s).support, sys.step s l μ) (r : State)
    (E : {e : AlterSeq State Label // e.trans.Terminates})
    (hne : (Scheduler.extStep sys ν l κ hκ).haltMass (PMF.pure r) E ≠ 0) :
    (r ∉ ν.support ∧ E.1 = ⟨r, Seq.nil⟩) ∨
      (r ∈ ν.support ∧ ∃ s' : State, E.1 = ⟨r, Seq.cons (l, s') Seq.nil⟩) := by
  classical
  set σ := Scheduler.extStep sys ν l κ hκ with hσ
  set pe : ProbabilisticExecution sys.toSystem := ⟨PMF.pure r, σ⟩ with hpe
  -- `next` emits `none` with mass `1` on any non-(active-empty) prefix.
  have hnext_none_one : ∀ e' : AlterSeq State Label,
      ¬(e'.trans = Seq.nil ∧ e'.init ∈ ν.support) → σ.next e' none = 1 := by
    intro e' hcond
    change (if e'.trans = Seq.nil ∧ e'.init ∈ ν.support
      then (κ e'.init).map (fun μ => some (l, μ)) else PMF.pure none) none = 1
    rw [if_neg hcond]; exact PMF.pure_apply_self none
  have hnext_none_zero : ∀ e' : AlterSeq State Label,
      (e'.trans = Seq.nil ∧ e'.init ∈ ν.support) → σ.next e' none = 0 := by
    intro e' hcond
    change (if e'.trans = Seq.nil ∧ e'.init ∈ ν.support
      then (κ e'.init).map (fun μ => some (l, μ)) else PMF.pure none) none = 0
    rw [if_pos hcond, PMF.map_apply]
    simp only [reduceCtorEq, if_false, tsum_zero]
  -- A nonzero one-step kernel forces the active-prefix shape.
  have hker_ne : ∀ (init : State) (previous : Seq (Label × State)) (last : Label × State),
      pe.kernel ⟨init, previous⟩ last ≠ 0 →
      (init ∈ ν.support ∧ previous = Seq.nil ∧ last.1 = l) := by
    intro init previous last hne'
    by_cases hcond : previous = Seq.nil ∧ init ∈ ν.support
    · refine ⟨hcond.2, hcond.1, ?_⟩
      by_contra hl
      apply hne'
      unfold ProbabilisticExecution.kernel
      have hsched : pe.scheduler.next ⟨init, previous⟩ = (κ init).map (fun μ => some (l, μ)) := by
        change (if previous = Seq.nil ∧ init ∈ ν.support
          then (κ init).map (fun μ => some (l, μ)) else PMF.pure none) = _
        rw [if_pos hcond]
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
      apply hne'
      unfold ProbabilisticExecution.kernel
      have hsched : pe.scheduler.next ⟨init, previous⟩ = PMF.pure none := by
        change (if previous = Seq.nil ∧ init ∈ ν.support
          then (κ init).map (fun μ => some (l, μ)) else PMF.pure none) = _
        rw [if_neg hcond]
      simp only [hsched]
      have hz : ∀ μ : PMF State,
          (PMF.pure none : PMF (Option (Label × PMF State))) (some (last.1, μ)) = 0 :=
        fun μ => PMF.pure_apply_of_ne _ _ (by simp)
      simp only [hz, zero_mul, tsum_zero]
  -- Unpack `E`.
  obtain ⟨⟨init', trans'⟩, hterm⟩ := E
  simp only at hterm hne ⊢
  have hprob_ne : pe.probOf ⟨init', trans'⟩ hterm ≠ 0 := by
    intro h0; apply hne
    unfold Scheduler.haltMass; rw [← hpe, h0, zero_mul]
  have hnone_ne : σ.next ⟨init', trans'⟩ none ≠ 0 := by
    intro h0; apply hne
    unfold Scheduler.haltMass; rw [← hpe, h0, mul_zero]
  -- `init' = r` (else `probOf` from `pure r` vanishes).
  have hinit_r : init' = r := by
    by_contra hne_r
    apply hprob_ne
    rw [ProbabilisticExecution.probOf_init_factor σ (PMF.pure r) ⟨init', trans'⟩ hterm]
    rw [show (⟨init', trans'⟩ : AlterSeq State Label).init = init' from rfl,
      PMF.pure_apply_of_ne _ _ hne_r, zero_mul]
  subst hinit_r
  have hncond : ¬((⟨init', trans'⟩ : AlterSeq State Label).trans = Seq.nil ∧
      (⟨init', trans'⟩ : AlterSeq State Label).init ∈ ν.support) :=
    fun hcond => hnone_ne (hnext_none_zero _ hcond)
  by_cases htrans_nil : trans' = Seq.nil
  · -- empty execution: `r ∉ ν.support`.
    left
    have hr_notin : init' ∉ ν.support := by
      intro hin; exact hncond ⟨htrans_nil, hin⟩
    exact ⟨hr_notin, AlterSeq.mk.injEq .. ▸ ⟨rfl, htrans_nil⟩⟩
  · -- nonempty: single external transition; `r ∈ ν.support`.
    right
    have hnonempty : trans'.toList hterm ≠ [] := by
      intro hnil; apply htrans_nil
      have := Stream'.Seq.ofList_toList trans' hterm
      rw [hnil, Stream'.Seq.ofList_nil] at this; exact this.symm
    obtain ⟨previous, last, h_prev, h_split, _, _⟩ :=
      Stream'.Seq.exists_split_last trans' hterm hnonempty
    have hprob_split : pe.probOf ⟨init', trans'⟩ hterm
        = pe.probOf ⟨init', previous⟩ h_prev * pe.kernel ⟨init', previous⟩ last := by
      have happ : (previous.append (Seq.cons last Seq.nil)).Terminates := h_split ▸ hterm
      have hrw : pe.probOf ⟨init', trans'⟩ hterm
          = pe.probOf ⟨init', previous.append (Seq.cons last Seq.nil)⟩ happ := h_split ▸ rfl
      rw [hrw, ProbabilisticExecution.probOf_append_singleton _ _ _ h_prev _ happ]
    have hker_ne' : pe.kernel ⟨init', previous⟩ last ≠ 0 :=
      fun h0 => hprob_ne (by rw [hprob_split, h0, mul_zero])
    obtain ⟨hinit_supp, hprev_nil, hlast⟩ := hker_ne _ _ _ hker_ne'
    refine ⟨hinit_supp, last.2, ?_⟩
    have htrans_eq : trans' = Seq.cons (l, last.2) Seq.nil := by
      rw [h_split, hprev_nil, Stream'.Seq.nil_append]
      obtain ⟨l', s'⟩ := last
      simp only at hlast
      rw [hlast]
    exact AlterSeq.mk.injEq .. ▸ ⟨rfl, htrans_eq⟩

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

/-! #### Generic suffix / endState helpers -/

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

/-- Public version of `LabelledSystem.map_ofList`: `Seq.map f (ofList L) = ofList (L.map f)`. -/
private theorem Seq.map_ofList_pub {α β : Type} (f : α → β) (L : List α) :
    (Seq.ofList L).map f = Seq.ofList (L.map f) := by
  induction L with
  | nil => rw [Stream'.Seq.ofList_nil, Stream'.Seq.map_nil, List.map_nil, Stream'.Seq.ofList_nil]
  | cons a L ih =>
    rw [Stream'.Seq.ofList_cons, Stream'.Seq.map_cons, List.map_cons, Stream'.Seq.ofList_cons, ih]

/-- Public version: `Seq.take j (ofList L) = L.take j`. -/
private theorem Seq.take_ofList_pub {α : Type} (L : List α) (j : ℕ) :
    Seq.take j (Seq.ofList L) = L.take j := by
  induction L generalizing j with
  | nil => cases j <;> simp [Stream'.Seq.ofList_nil, Stream'.Seq.take]
  | cons a L ih =>
    cases j with
    | zero => simp [Stream'.Seq.take]
    | succ n =>
      rw [Stream'.Seq.ofList_cons, Stream'.Seq.take_succ_cons, List.take_succ_cons, ih]

open scoped Classical in
/-- Filtering `ofList L` by a predicate that fails everywhere on `L` yields `nil`. -/
private theorem Seq.filter_ofList_eq_nil_pub {α : Type} (p : α → Prop)
    (L : List α) (h : ∀ x ∈ L, ¬ p x) : (Seq.ofList L).filter p = Seq.nil := by
  induction L with
  | nil => rw [Stream'.Seq.ofList_nil, Stream'.Seq.filter_nil]
  | cons a L ih =>
    rw [Stream'.Seq.ofList_cons, Stream'.Seq.filter_cons_neg a _ (h a (List.mem_cons_self ..))]
    exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

/-- A nonzero one-step kernel of a `WeakScheduler` forces the emitted label to be
internal. -/
private theorem WeakScheduler.kernel_ne_zero_internal {State Label : Type}
    {sys : LabelledSystem State Label} (σ : WeakScheduler sys)
    (e : AlterSeq State Label) (l : Label) (s' : State)
    (hne : (⟨PMF.pure e.init, σ.toScheduler⟩ : ProbabilisticExecution sys.toSystem).kernel
        e (l, s') ≠ 0) :
    sys.internal l := by
  classical
  -- `kernel e (l,s') = ∑' μ, next e (some (l,μ)) * μ s'`; nonzero ⟹ some `(l,μ)` in support.
  unfold ProbabilisticExecution.kernel at hne
  by_contra h_ext
  apply hne
  refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
  by_cases hsupp : some (l, μ) ∈ (σ.next e).support
  · exact absurd (σ.internal_only e l μ hsupp) h_ext
  · rw [PMF.mem_support_iff, not_not] at hsupp
    change σ.toScheduler.next e (some (l, μ)) * μ s' = 0
    rw [show σ.toScheduler.next e (some (l, μ)) = σ.next e (some (l, μ)) from rfl, hsupp, zero_mul]

/-- **Every positive-probability execution of a `WeakScheduler` has an all-internal
label list** (so its trace is empty): each one-step kernel along the path is
nonzero, and `WeakScheduler`s only emit internal labels. -/
private theorem WeakScheduler.probOf_all_internal {State Label : Type}
    {sys : LabelledSystem State Label} (σ : WeakScheduler sys) (μ_init : PMF State)
    (e : AlterSeq State Label) (h : e.trans.Terminates)
    (hpos : (⟨μ_init, σ.toScheduler⟩ : ProbabilisticExecution sys.toSystem).probOf e h ≠ 0) :
    ∀ p ∈ e.trans.toList h, sys.internal p.1 := by
  classical
  set pe : ProbabilisticExecution sys.toSystem := ⟨PMF.pure e.init, σ.toScheduler⟩ with hpe
  -- Reduce to the Dirac source (kernels are source-independent).
  have hpos' : pe.probOf e h ≠ 0 := by
    rw [hpe]
    intro h0
    apply hpos
    rw [ProbabilisticExecution.probOf_init_factor σ.toScheduler μ_init e h, h0, mul_zero]
  -- Induct on the transition list (reverse recursion).
  -- Generalize over the (terminating) trans sequence by working on its toList.
  have key : ∀ (L : List (Label × State)) (s₀ : State)
      (hL : (Seq.ofList L : Seq (Label × State)).Terminates),
      (⟨PMF.pure s₀, σ.toScheduler⟩ : ProbabilisticExecution sys.toSystem).probOf
          ⟨s₀, Seq.ofList L⟩ hL ≠ 0 →
      ∀ p ∈ L, sys.internal p.1 := by
    intro L
    induction L using List.reverseRecOn with
    | nil => intro s₀ hL _ p hp; simp at hp
    | append_singleton rest last ih =>
      intro s₀ hL hposL p hp
      have hrest : (Seq.ofList rest : Seq (Label × State)).Terminates :=
        Stream'.Seq.terminates_ofList rest
      have heq : (Seq.ofList (rest ++ [last]) : Seq (Label × State))
          = (Seq.ofList rest).append (Seq.cons last Seq.nil) := by
        rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
      have happ : ((Seq.ofList rest).append (Seq.cons last Seq.nil)
          : Seq (Label × State)).Terminates := heq ▸ hL
      -- factor probOf at the last transition
      have hfac : (⟨PMF.pure s₀, σ.toScheduler⟩
            : ProbabilisticExecution sys.toSystem).probOf ⟨s₀, Seq.ofList (rest ++ [last])⟩ hL
          = (⟨PMF.pure s₀, σ.toScheduler⟩
              : ProbabilisticExecution sys.toSystem).probOf ⟨s₀, Seq.ofList rest⟩ hrest
            * (⟨PMF.pure s₀, σ.toScheduler⟩
                : ProbabilisticExecution sys.toSystem).kernel ⟨s₀, Seq.ofList rest⟩ last := by
        have hrw : (⟨PMF.pure s₀, σ.toScheduler⟩
              : ProbabilisticExecution sys.toSystem).probOf ⟨s₀, Seq.ofList (rest ++ [last])⟩ hL
            = (⟨PMF.pure s₀, σ.toScheduler⟩
                : ProbabilisticExecution sys.toSystem).probOf
                  ⟨s₀, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩ happ := by
          congr 1
          exact AlterSeq.mk.injEq .. ▸ ⟨rfl, heq⟩
        rw [hrw, ProbabilisticExecution.probOf_append_singleton _ s₀ (Seq.ofList rest) hrest
          last happ]
      rw [hfac] at hposL
      have hprev_ne : (⟨PMF.pure s₀, σ.toScheduler⟩
          : ProbabilisticExecution sys.toSystem).probOf ⟨s₀, Seq.ofList rest⟩ hrest ≠ 0 :=
        fun h0 => hposL (by rw [h0, zero_mul])
      have hker_ne : (⟨PMF.pure s₀, σ.toScheduler⟩
          : ProbabilisticExecution sys.toSystem).kernel ⟨s₀, Seq.ofList rest⟩ last ≠ 0 :=
        fun h0 => hposL (by rw [h0, mul_zero])
      rcases List.mem_append.mp hp with hp_rest | hp_last
      · exact ih s₀ hrest hprev_ne p hp_rest
      · -- `p = last`; its label is internal via `kernel_ne_zero_internal`.
        rw [List.mem_singleton] at hp_last
        subst hp_last
        have : (⟨s₀, Seq.ofList rest⟩ : AlterSeq State Label).init = s₀ := rfl
        exact WeakScheduler.kernel_ne_zero_internal σ ⟨s₀, Seq.ofList rest⟩ p.1 p.2
          (by rw [this]; exact hker_ne)
  -- Apply `key` to `e.trans.toList h`.
  have he_eq : (⟨e.init, Seq.ofList (e.trans.toList h)⟩ : AlterSeq State Label) = e := by
    congr 1; exact Stream'.Seq.ofList_toList e.trans h
  have hterm' : (Seq.ofList (e.trans.toList h) : Seq (Label × State)).Terminates := by
    rw [Stream'.Seq.ofList_toList e.trans h]; exact h
  have hpos'' : (⟨PMF.pure e.init, σ.toScheduler⟩
      : ProbabilisticExecution sys.toSystem).probOf
        ⟨e.init, Seq.ofList (e.trans.toList h)⟩ hterm' ≠ 0 := by
    have : (⟨e.init, Seq.ofList (e.trans.toList h)⟩ : AlterSeq State Label) = e := he_eq
    rw [show (⟨PMF.pure e.init, σ.toScheduler⟩
        : ProbabilisticExecution sys.toSystem).probOf
          ⟨e.init, Seq.ofList (e.trans.toList h)⟩ hterm'
        = pe.probOf e h from by rw [hpe]; congr 1]
    exact hpos'
  exact key (e.trans.toList h) e.init hterm' hpos''

open Classical in
/-- **The witness's halting mass at a single execution is bounded by the target
distribution at its end-state.** A single summand of `weakTau.witness_pushforward`. -/
private theorem weakTau.witness_haltMass_le {State Label : Type}
    {sys : LabelledSystem State Label} {μ_init μ : PMF State} (h : weakTau sys μ_init μ)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) :
    h.witnessScheduler.haltMass μ_init e ≤ μ (e.1.endState e.2) := by
  classical
  rw [h.witness_pushforward (e.1.endState e.2)]
  refine le_trans ?_ (ENNReal.le_tsum e)
  rw [if_pos rfl, mul_one]

/-- **End-state of a `j`-prefix.** The end-state of the prefix
`⟨e.init, ofList (take j e.trans)⟩` is the state of `e` after `j` transitions,
`(e.stateAt j).getD e.init`, for `j ≤ length`. -/
private theorem AlterSeq.endState_take_prefix {State Label : Type}
    (e : AlterSeq State Label) (h : e.trans.Terminates) (j : ℕ) (hj : j ≤ e.trans.length h) :
    (⟨e.init, Seq.ofList (Seq.take j e.trans)⟩ : AlterSeq State Label).endState
        (Stream'.Seq.terminates_ofList _)
      = (e.stateAt j).getD e.init := by
  classical
  rw [AlterSeq.endState_eq_getLast? _ (Stream'.Seq.terminates_ofList _)]
  -- `(ofList (take j)).toList = take j`, and `take j = (toList).take j`.
  rw [show (⟨e.init, Seq.ofList (Seq.take j e.trans)⟩ : AlterSeq State Label).trans.toList
        (Stream'.Seq.terminates_ofList _) = Seq.take j e.trans from by
    change (Seq.ofList (Seq.take j e.trans)).toList (Stream'.Seq.terminates_ofList _)
      = Seq.take j e.trans
    rw [Stream'.Seq.toList_ofList]]
  have htake_list : Seq.take j e.trans = (e.trans.toList h).take j := by
    conv_lhs => rw [← Stream'.Seq.ofList_toList e.trans h]
    rw [Seq.take_ofList_pub]
  rw [htake_list, List.getLast?_take]
  have hlenT : (e.trans.toList h).length = e.trans.length h := Stream'.Seq.length_toList e.trans h
  cases j with
  | zero => simp only []; rfl
  | succ n =>
    rw [if_neg (Nat.succ_ne_zero n)]
    have hlt : n < (e.trans.toList h).length := by rw [hlenT]; omega
    have hsome : (e.trans.toList h)[n]? = e.trans.get? n := Stream'.Seq.getElem?_toList e.trans h n
    have hne : (e.trans.toList h)[n]?.isSome := by
      rw [List.getElem?_eq_getElem hlt]; exact Option.isSome_some
    rw [Nat.add_sub_cancel, Option.or_of_isSome hne, hsome]
    change (e.trans.get? n).elim e.init Prod.snd = ((e.trans.get? n).map Prod.snd).getD e.init
    cases hg : e.trans.get? n with
    | none => rw [List.getElem?_eq_getElem hlt] at hsome; rw [hg] at hsome; simp at hsome
    | some p => simp

open Classical in
/-- **`extLabMass` as a sum over the tight trace-`τ` cone** (`g`-weighted analogue
of `traceProb_eq_labProb_sum` collapsed to a single subtype sum): the external
level mass `extLabMass τ g` equals the `tsum` of `probOf · g(endState)` over the
terminating, trace-`τ`, tight executions. Mirrors the bijection in
`traceProb_eq_labProb_sum` (with the `g`-weight carried through). -/
theorem LabelledSystem.extLabMass_eq_tight_tsum {State Label : Type}
    (ls : LabelledSystem State Label) (pe : ProbabilisticExecution ls.toSystem)
    (extLabs : List Label) (g : State → ENNReal) :
    ls.extLabMass pe extLabs g
      = ∑' e : {e : AlterSeq State Label //
          e.trans.Terminates ∧ ls.trace e = Seq.ofList extLabs ∧ ls.IsTight e},
          pe.probOf e.1 e.2.1 * g (e.1.endState e.2.1) := by
  classical
  unfold LabelledSystem.extLabMass ProbabilisticExecution.labMass
  -- Step 1: push the `if` inside the inner `tsum`.
  rw [show (∑' labs : List Label,
        (if ls.traceTightLabs (Seq.ofList extLabs) labs then
          ∑' e : AlterSeq State Label,
            dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs)
              (fun h => pe.probOf e h.1 * g (e.endState h.1)) (fun _ => 0)
        else 0))
      = ∑' labs : List Label, ∑' e : AlterSeq State Label,
          (if ls.traceTightLabs (Seq.ofList extLabs) labs then
            dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs)
              (fun h => pe.probOf e h.1 * g (e.endState h.1)) (fun _ => 0)
          else 0) from by
    refine tsum_congr fun labs => ?_
    by_cases hc : ls.traceTightLabs (Seq.ofList extLabs) labs
    · simp only [if_pos hc]
    · simp only [if_neg hc, tsum_zero]]
  rw [← ENNReal.tsum_prod' (f := fun p : List Label × AlterSeq State Label =>
      if ls.traceTightLabs (Seq.ofList extLabs) p.1 then
        dite (p.2.trans.Terminates ∧ Seq.map Prod.fst p.2.trans = (↑p.1 : Seq Label))
          (fun h => pe.probOf p.2 h.1 * g (p.2.endState h.1)) (fun _ => 0)
      else 0)]
  set G : List Label × AlterSeq State Label → ENNReal := fun p =>
      if ls.traceTightLabs (Seq.ofList extLabs) p.1 then
        dite (p.2.trans.Terminates ∧ Seq.map Prod.fst p.2.trans = (↑p.1 : Seq Label))
          (fun h => pe.probOf p.2 h.1 * g (p.2.endState h.1)) (fun _ => 0)
      else 0 with hG_def
  -- The subtype RHS summand.
  set H : {e : AlterSeq State Label //
      e.trans.Terminates ∧ ls.trace e = Seq.ofList extLabs ∧ ls.IsTight e} → ENNReal :=
    fun e => pe.probOf e.1 e.2.1 * g (e.1.endState e.2.1) with hH_def
  have G_supp : ∀ p : List Label × AlterSeq State Label, G p ≠ 0 →
      ls.traceTightLabs (Seq.ofList extLabs) p.1 ∧
        ∃ hT : p.2.trans.Terminates, Seq.map Prod.fst p.2.trans = (↑p.1 : Seq Label) := by
    intro p hp
    rw [hG_def] at hp
    simp only at hp
    by_cases hc : ls.traceTightLabs (Seq.ofList extLabs) p.1
    · rw [if_pos hc] at hp
      by_cases hd : p.2.trans.Terminates ∧ Seq.map Prod.fst p.2.trans = (↑p.1 : Seq Label)
      · exact ⟨hc, hd.1, hd.2⟩
      · rw [dif_neg hd] at hp; exact absurd rfl hp
    · rw [if_neg hc] at hp; exact absurd rfl hp
  -- Forward map: a tight trace-`τ` execution `e` produces the pair `(labs_e, e)`.
  refine (tsum_eq_tsum_of_ne_zero_bij
    (f := G) (g := H)
    (i := fun p => ((((p : {e : AlterSeq State Label //
          e.trans.Terminates ∧ ls.trace e = Seq.ofList extLabs ∧ ls.IsTight e}).1.trans.toList
            (p : {e : AlterSeq State Label //
          e.trans.Terminates ∧ ls.trace e = Seq.ofList extLabs ∧ ls.IsTight e}).2.1).map Prod.fst,
        (p : {e : AlterSeq State Label //
          e.trans.Terminates ∧ ls.trace e = Seq.ofList extLabs ∧ ls.IsTight e}).1)))
    ?hinj ?hf ?hfg)
  case hinj =>
    rintro ⟨⟨e₁, h₁⟩, hp₁⟩ ⟨⟨e₂, h₂⟩, hp₂⟩ heq
    have h2 : e₁ = e₂ := (Prod.ext_iff.mp heq).2
    exact Subtype.ext (Subtype.ext h2)
  case hf =>
    rintro p hp
    obtain ⟨hc, hT, hmap⟩ := G_supp p hp
    -- recover trace/tight from `traceTightLabs`.
    have h_p1 : p.1 = (p.2.trans.toList hT).map Prod.fst := by
      apply Stream'.Seq.ofList_injective
      rw [← Seq.map_ofList_pub, Stream'.Seq.ofList_toList p.2.trans hT, hmap]
    have htt := (ls.tight_iff (Seq.ofList extLabs) p.2 hT).mpr (h_p1 ▸ hc)
    refine ⟨⟨⟨p.2, hT, htt.1, htt.2⟩, ?_⟩, ?_⟩
    · -- the subtype element is in `support H`.
      change pe.probOf p.2 hT * g (p.2.endState hT) ≠ 0
      intro h0
      apply hp
      rw [hG_def]; simp only
      rw [if_pos hc, dif_pos ⟨hT, hmap⟩, h0]
    · -- `i` of it is `p`.
      simp only
      exact Prod.ext h_p1.symm rfl
  case hfg =>
    rintro ⟨⟨e, hT, htr, hti⟩, hne⟩
    set labs := (e.trans.toList hT).map Prod.fst with hlabs
    have h_tt : ls.traceTightLabs (Seq.ofList extLabs) labs :=
      (ls.tight_iff (Seq.ofList extLabs) e hT).mp ⟨htr, hti⟩
    have h_map : Seq.map Prod.fst e.trans = (↑labs : Seq Label) := by
      rw [hlabs, ← Seq.map_ofList_pub, Stream'.Seq.ofList_toList e.trans hT]
    change G (labs, e) = H ⟨e, hT, htr, hti⟩
    rw [hG_def, hH_def]; simp only
    rw [if_pos h_tt, dif_pos ⟨hT, h_map⟩]

/-! #### `internalSuffix`: the maximal all-internal tail of an execution -/

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

/-! ### The `expand` belief (post-τ-aware)

A first attempt (the deleted `lastMuBelief`) weighted a candidate weak-step result
`μ` by `μ s_last`, where `s_last` is the recorded hyperStep target `ν'`. But `ν'` is
sampled from the hyperStep *target* distribution (the **pre**-post-τ
distribution); the post-τ then moves mass to `μ`, so `μ ν'` is generically `0`
and the belief degenerates (see `MyMathlibProject/FlawCheck.lean`). The fix:

* weight by `(postDist of the candidate weak step)(ν')` instead of `μ ν'`, and
* range the belief over a *clean* prior `pe'`-history `E'` — drawn so that the
  next-step query hits `pe'` on-path — with label list `L.dropLast` (`L` the
  full external trace so far, last label `l`).

`beliefExpandW` is the unnormalised weight; `beliefExpand` its normalisation. -/

/-- Generic (any-`System`) form of `tsum_kernel_le_one`: the one-step kernel,
summed over result states for a fixed label, is `≤ 1` (the scheduler emits a
sub-probability). -/
theorem ProbabilisticExecution.tsum_kernel_le_one' {S Label : Type} {Sys : System S Label}
    (pe : ProbabilisticExecution Sys) (e : AlterSeq S Label) (l : Label) :
    (∑' s' : S, pe.kernel e (l, s')) ≤ 1 := by
  calc (∑' s' : S, pe.kernel e (l, s'))
      = ∑' (s' : S) (μ : PMF S), pe.scheduler.next e (some (l, μ)) * μ s' := rfl
    _ = ∑' (μ : PMF S) (s' : S), pe.scheduler.next e (some (l, μ)) * μ s' := ENNReal.tsum_comm
    _ = ∑' μ : PMF S, pe.scheduler.next e (some (l, μ)) := by
        refine tsum_congr fun μ => ?_
        rw [ENNReal.tsum_mul_left, μ.tsum_coe, mul_one]
    _ ≤ ∑' opt, pe.scheduler.next e opt :=
        ENNReal.tsum_comp_le_tsum_of_injective (f := fun μ : PMF S => some (l, μ))
          (fun _ _ h => (Prod.mk.inj (Option.some.inj h)).2) _
    _ = 1 := (pe.scheduler.next e).tsum_coe

/-- Generic (any-`System`) level-sum bound: the total `probOf`-mass of histories
with a fixed label list is `≤ 1`. The `g = 1` slice of the level-mass recursion,
proven by `List.reverseRecOn` via `labMass_nil`, `labMass_step` and
`tsum_kernel_le_one'`. (Generic analogue of `probOf_labels_tsum_le_one`, which is
stated only for `𝒟(sys)`-histories.) -/
theorem ProbabilisticExecution.labMass_one_le_one {S Label : Type} {Sys : System S Label}
    (pe : ProbabilisticExecution Sys) (labs : List Label) :
    pe.labMass labs (fun _ => (1 : ENNReal)) ≤ 1 := by
  classical
  induction labs using List.reverseRecOn with
  | nil =>
      rw [pe.labMass_nil]; simp only [mul_one]; exact le_of_eq pe.initState.tsum_coe
  | append_singleton labs l ih =>
      rw [pe.labMass_step labs l (fun _ => 1)]
      refine le_trans (ENNReal.tsum_le_tsum (fun e' => ?_)) ih
      by_cases hc : e'.trans.Terminates ∧ e'.trans.map Prod.fst = Seq.ofList labs
      · rw [dif_pos hc, dif_pos hc]; simp only [mul_one]
        exact mul_le_of_le_one_right' (pe.tsum_kernel_le_one' e' l)
      · rw [dif_neg hc, dif_neg hc]

open Classical in
/-- **Unnormalised weight of the corrected `expand` belief.** A weight over pairs
`(E', μ)` = (prior clean `pe'`-history `E'`, the last weak step's result PMF `μ`),
parameterised by the full external trace `L` so far (nonempty here) and the
observed hyperStep target `ν'`. With `l := L.getLast?`, the weight is
`probOf(E') * next(E')(some (l, μ)) * postDist(ν')`, where `postDist` is the
hyperStep-target distribution of the weak step `sys^w.step (E'.endState) l μ` —
nonzero only when `E'` terminates with label list `L.dropLast`, `l` is external,
and that weak step holds. (Contrast `lastMuBelief`, which uses `μ ν'`.)

FOLLOW-UP (post-τ side of the 7th-flaw fix): like the *pre-τ* re-draw fixed in
`drawAndRun` (now posterior-conditioned via `drawAndRunW`), this *post-τ* draw of
the weak-step result `μ` conditions only on the hyperStep boundary `ν'` (via
`postDist ν'`), NOT on the post-τ *trajectory* actually replayed by
`postTauWitness`. For randomized post-τ with nontrivial branching this can leak
mass to off-trajectory post-τ continuations, exactly as the old `drawAndRun` did
pre-τ. The validated drawAndRun fix is the B2Check-exercised piece; trajectory-
conditioning this post-τ `μ`-draw (reweighting `beliefExpandW` by the likelihood of
the replayed post-τ history under each `(E', μ)`) is the analogous follow-up for the
general case. -/
noncomputable def ProbabilisticExecution.beliefExpandW {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (L : List Label) (ν' : State) : AlterSeq State Label × PMF State → ENNReal :=
  fun p =>
    match L.getLast? with
    | none => 0
    | some l =>
      if hT : p.1.trans.Terminates ∧ p.1.trans.map Prod.fst = Seq.ofList L.dropLast then
        if hstep : (¬ sys.internal l) ∧ sys^w.step (p.1.endState hT.1) l p.2 then
          pe'.probOf p.1 hT.1 * pe'.scheduler.next p.1 (some (l, p.2))
            * (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν'
        else 0
      else 0

open Classical in
/-- Reduced form of `beliefExpandW` once `L.getLast? = some l` is known (the
`match` on the option collapses to its `some` branch). -/
theorem ProbabilisticExecution.beliefExpandW_eq {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (L : List Label) (ν' : State) (l : Label) (hL : L.getLast? = some l)
    (p : AlterSeq State Label × PMF State) :
    pe'.beliefExpandW L ν' p =
      if hT : p.1.trans.Terminates ∧ p.1.trans.map Prod.fst = Seq.ofList L.dropLast then
        if hstep : (¬ sys.internal l) ∧ sys^w.step (p.1.endState hT.1) l p.2 then
          pe'.probOf p.1 hT.1 * pe'.scheduler.next p.1 (some (l, p.2))
            * (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν'
        else 0
      else 0 := by
  classical
  conv_lhs => rw [ProbabilisticExecution.beliefExpandW]
  rw [hL]

open Classical in
/-- **Finiteness of the corrected-belief normaliser.** Each term is `≤
probOf(E') * next(E')(some (l, μ))` (since `postDist ν' ≤ 1` as a PMF value);
summing `μ` out gives `≤ ∑' E' [label list L.dropLast], probOf(E') ≤ 1` by the
level-sum bound `labMass_one_le_one`. Hence the normaliser is `≤ 1`, in
particular `≠ ⊤` (for `PMF.normalize`). -/
theorem ProbabilisticExecution.beliefExpandW_tsum_ne_top {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (L : List Label) (ν' : State) :
    (∑' p, pe'.beliefExpandW L ν' p) ≠ ⊤ := by
  classical
  suffices h : (∑' p, pe'.beliefExpandW L ν' p) ≤ 1 from
    (lt_of_le_of_lt h ENNReal.one_lt_top).ne
  cases hL : L.getLast? with
  | none =>
      have hz : ∀ p : AlterSeq State Label × PMF State, pe'.beliefExpandW L ν' p = 0 := by
        intro p; unfold ProbabilisticExecution.beliefExpandW; rw [hL]
      simp only [hz, tsum_zero]; exact zero_le_one
  | some l =>
      have hterm : ∀ p : AlterSeq State Label × PMF State,
          pe'.beliefExpandW L ν' p ≤
            (if hT : p.1.trans.Terminates ∧ p.1.trans.map Prod.fst = Seq.ofList L.dropLast then
              pe'.probOf p.1 hT.1 * pe'.scheduler.next p.1 (some (l, p.2)) else 0) := by
        intro p
        rw [pe'.beliefExpandW_eq L ν' l hL p]
        by_cases hT : p.1.trans.Terminates ∧ p.1.trans.map Prod.fst = Seq.ofList L.dropLast
        · rw [dif_pos hT, dif_pos hT]
          by_cases hstep : (¬ sys.internal l) ∧ sys^w.step (p.1.endState hT.1) l p.2
          · rw [dif_pos hstep]
            exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
          · rw [dif_neg hstep]; exact bot_le
        · rw [dif_neg hT, dif_neg hT]
      refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
      rw [ENNReal.tsum_prod' (f := fun p : AlterSeq State Label × PMF State =>
        if hT : p.1.trans.Terminates ∧ p.1.trans.map Prod.fst = Seq.ofList L.dropLast then
          pe'.probOf p.1 hT.1 * pe'.scheduler.next p.1 (some (l, p.2)) else 0)]
      simp only []
      refine le_trans ?_ (pe'.labMass_one_le_one L.dropLast)
      unfold ProbabilisticExecution.labMass
      refine ENNReal.tsum_le_tsum (fun E' => ?_)
      by_cases hT : E'.trans.Terminates ∧ E'.trans.map Prod.fst = Seq.ofList L.dropLast
      · rw [dif_pos hT]
        rw [show (∑' μ : PMF State, if hT' : E'.trans.Terminates ∧
              E'.trans.map Prod.fst = Seq.ofList L.dropLast then
              pe'.probOf E' hT'.1 * pe'.scheduler.next E' (some (l, μ)) else 0)
            = ∑' μ : PMF State, pe'.probOf E' hT.1 * pe'.scheduler.next E' (some (l, μ)) from
            tsum_congr (fun μ => by rw [dif_pos hT])]
        rw [ENNReal.tsum_mul_left, mul_one]
        refine mul_le_of_le_one_right' ?_
        calc (∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ)))
            ≤ ∑' opt, pe'.scheduler.next E' opt :=
              ENNReal.tsum_comp_le_tsum_of_injective
                (f := fun μ : PMF State => some (l, μ))
                (fun _ _ h => (Prod.mk.inj (Option.some.inj h)).2) _
          _ = 1 := (pe'.scheduler.next E').tsum_coe
      · rw [dif_neg hT]; simp only [dif_neg hT, tsum_zero]; exact bot_le

open Classical in
/-- **The corrected `expand` belief.** Normalisation of `beliefExpandW`; total
fallback `pure ⟨⟨sys.init, nil⟩, pure sys.init⟩` when the weight vanishes
(mirroring `beliefTC`). -/
noncomputable def ProbabilisticExecution.beliefExpand {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (L : List Label) (ν' : State) : PMF (AlterSeq State Label × PMF State) :=
  if h0 : (∑' p, pe'.beliefExpandW L ν' p) ≠ 0 then
    PMF.normalize (pe'.beliefExpandW L ν') h0 (pe'.beliefExpandW_tsum_ne_top L ν')
  else
    PMF.pure ⟨⟨sys.toSystem.init, Seq.nil⟩, PMF.pure sys.toSystem.init⟩

open Classical in
/-- Every pair in `beliefExpand`'s support has nonzero `beliefExpandW`-weight,
when the normaliser is nonzero (the normalisation branch). Mirrors
`beliefTC_support`. -/
theorem ProbabilisticExecution.beliefExpand_support {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (L : List Label) (ν' : State)
    (h0 : (∑' p, pe'.beliefExpandW L ν' p) ≠ 0)
    {p : AlterSeq State Label × PMF State}
    (hp : p ∈ (pe'.beliefExpand L ν').support) :
    pe'.beliefExpandW L ν' p ≠ 0 := by
  classical
  unfold ProbabilisticExecution.beliefExpand at hp
  rw [dif_pos h0, PMF.mem_support_normalize_iff] at hp
  exact hp

/-- **Corrected `expand` belief normaliser cancellation.** Multiplying the
(possibly unnormalised) `beliefExpand`-expectation by the normaliser recovers the
unnormalised `beliefExpandW`-weighted sum; covers the `Z = 0` fallback too.
Mirrors `beliefTC_normalize_cancel`. -/
theorem ProbabilisticExecution.beliefExpand_normalize_cancel {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (L : List Label) (ν' : State) (w : AlterSeq State Label × PMF State → ENNReal) :
    (∑' p, pe'.beliefExpandW L ν' p) * (∑' p, pe'.beliefExpand L ν' p * w p)
      = ∑' p, pe'.beliefExpandW L ν' p * w p := by
  classical
  by_cases hZ : (∑' p, pe'.beliefExpandW L ν' p) = 0
  · rw [hZ, zero_mul]
    have hz : ∀ p, pe'.beliefExpandW L ν' p = 0 := ENNReal.tsum_eq_zero.mp hZ
    exact (ENNReal.tsum_eq_zero.mpr (fun p => by rw [hz p, zero_mul])).symm
  · have hZtop : (∑' p, pe'.beliefExpandW L ν' p) ≠ ⊤ := pe'.beliefExpandW_tsum_ne_top L ν'
    have hbel : ∀ p, pe'.beliefExpand L ν' p
        = pe'.beliefExpandW L ν' p * (∑' p', pe'.beliefExpandW L ν' p')⁻¹ := by
      intro p
      unfold ProbabilisticExecution.beliefExpand
      rw [dif_pos hZ, PMF.normalize_apply]
    rw [show (∑' p, pe'.beliefExpand L ν' p * w p)
          = ∑' p, (pe'.beliefExpandW L ν' p * (∑' p', pe'.beliefExpandW L ν' p')⁻¹) * w p from
        tsum_congr (fun p => by rw [hbel p]),
      ← ENNReal.tsum_mul_left]
    refine tsum_congr (fun p => ?_)
    rw [show (∑' p', pe'.beliefExpandW L ν' p') *
          (pe'.beliefExpandW L ν' p * (∑' p', pe'.beliefExpandW L ν' p')⁻¹ * w p)
          = ((∑' p', pe'.beliefExpandW L ν' p') * (∑' p', pe'.beliefExpandW L ν' p')⁻¹) *
            (pe'.beliefExpandW L ν' p * w p) by ring,
      ENNReal.mul_inv_cancel hZ hZtop, one_mul]

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

/-! #### Witness-lowering of a `sys^w`-history into a `sys`-scheduler

The `weakChain` construction runs a *list* of weak steps `(lᵢ, μᵢ)` in sequence,
each realized by its total per-step witness `weakStepWitnessTotal`, threading the
source state through the `bind` halt state. The key analytic property
(`weakChain_pushforward`) is that — provided each step is a genuine `sys^w`-step
from the threaded source — the chain almost-surely halts, with the integral of a
test `g` against the halting end-state equal to the iterated pushforward
`weakChainPush` (composition of the `μᵢ`). This is the foundational lowering
object for the new `expand` construction. -/

/-- The iterated pushforward of a chain of weak steps: integrate the test `g`
against the final distribution obtained by running the steps `(lᵢ, μᵢ)` in
sequence from source `s`. Base case `[]`: `g s` (no step, halt at `s`); step
`(l, μ) :: rest`: `∑' t, μ t * weakChainPush rest t g` (push the first step's
result `μ` forward, recurse from each `t`). This is the RHS of
`weakChain_pushforward`. -/
noncomputable def weakChainPush :
    List (Label × PMF State) → State → (State → ENNReal) → ENNReal
  | List.nil, s, g => g s
  | List.cons (_, μ) rest, _, g => ∑' t, μ t * weakChainPush rest t g

/-- **Validity of a weak-step chain from a source `s`.** Threading the source
state through the chain: the first step `(l, μ)` must be a genuine `sys^w.step`
from `s`, and the remainder must be valid from *every* possible result state `t`
in `μ.support` (in fact from every `t`, which is the cleanest sufficient form for
the pushforward induction). The empty chain is vacuously valid. -/
def WeakChainValid (sys : LabelledSystem State Label) :
    List (Label × PMF State) → State → Prop
  | List.nil, _ => True
  | List.cons (l, μ) rest, s => sys^w.step s l μ ∧ ∀ t, WeakChainValid sys rest t

/-- A `sys`-scheduler that runs a list of weak steps `(lᵢ, μᵢ)` in sequence, each
via its total witness `weakStepWitnessTotal`, then halts. The source state of the
first step is `s`; each subsequent step's source is the previous witness's halt
end-state (threaded by `bind`). The empty list halts immediately. -/
noncomputable def Scheduler.weakChain (sys : LabelledSystem State Label) :
    List (Label × PMF State) → State → Scheduler sys.toSystem
  | List.nil, _ => Scheduler.haltNow sys
  | List.cons (l, μ) rest, s =>
      Scheduler.bind (Scheduler.weakStepWitnessTotal sys s l μ)
        (fun s' => Scheduler.weakChain sys rest s')

/-- **Base case of `weakChain_pushforward`.** The immediate-halt scheduler
`haltNow`, from a Dirac source `PMF.pure s`, halts only on the empty execution
`⟨s, nil⟩` (it never emits a transition, so the one-step kernel is identically
`0`), and its halt mass there is `1`. Hence integrating `g` against the halting
end-state recovers `g s`. -/
theorem Scheduler.haltNow_pushforward (sys : LabelledSystem State Label)
    (s : State) (g : State → ENNReal) :
    (∑' e, (Scheduler.haltNow sys).haltMass (PMF.pure s) e * g (e.1.endState e.2)) = g s := by
  classical
  set σ := Scheduler.haltNow sys with hσ
  set pe : ProbabilisticExecution sys.toSystem := ⟨PMF.pure s, σ⟩ with hpe
  -- `σ.next` always emits `none` with mass `1`.
  have hnext_none : ∀ e' : AlterSeq State Label, σ.next e' none = 1 := by
    intro e'; rw [hσ]; exact PMF.pure_apply_self none
  -- `σ.next` emits any `some` with mass `0`; hence the one-step kernel is `0`.
  have hker_zero : ∀ (e' : AlterSeq State Label) (step : Label × State),
      pe.kernel e' step = 0 := by
    intro e' step
    unfold ProbabilisticExecution.kernel
    refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
    have : pe.scheduler.next e' (some (step.1, μ)) = 0 := by
      rw [hpe, hσ]; exact PMF.pure_apply_of_ne _ _ (by simp)
    rw [this, zero_mul]
  -- The empty execution `⟨s, nil⟩` is the unique fiber with nonzero halt mass.
  set e₀ : {e : AlterSeq State Label // e.trans.Terminates} :=
    ⟨⟨s, Seq.nil⟩, Stream'.Seq.terminates_nil⟩ with he₀
  -- Halt mass of a nonempty execution is `0`: peel the last transition, kernel `= 0`.
  have hsupp : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      σ.haltMass (PMF.pure s) e ≠ 0 → e = e₀ := by
    rintro ⟨⟨init', trans'⟩, hterm⟩ hne
    simp only at hterm hne ⊢
    have hprob_ne : pe.probOf ⟨init', trans'⟩ hterm ≠ 0 := by
      intro h0; apply hne
      unfold Scheduler.haltMass; rw [← hpe, h0, zero_mul]
    -- `trans' = nil`: else the last kernel factor would be `0`.
    have htrans_nil : trans' = Seq.nil := by
      by_contra htrans_ne
      have hnonempty : trans'.toList hterm ≠ [] := by
        intro hnil; apply htrans_ne
        have := Stream'.Seq.ofList_toList trans' hterm
        rw [hnil, Stream'.Seq.ofList_nil] at this; exact this.symm
      obtain ⟨previous, last, h_prev, h_split, _, _⟩ :=
        Stream'.Seq.exists_split_last trans' hterm hnonempty
      apply hprob_ne
      have happ : (previous.append (Seq.cons last Seq.nil)).Terminates := h_split ▸ hterm
      have hrw : pe.probOf ⟨init', trans'⟩ hterm
          = pe.probOf ⟨init', previous.append (Seq.cons last Seq.nil)⟩ happ := h_split ▸ rfl
      rw [hrw, ProbabilisticExecution.probOf_append_singleton _ _ _ h_prev _ happ,
        hker_zero ⟨init', previous⟩ last, mul_zero]
    -- `init' = s`: else the initial mass `(pure s) init'` would be `0`.
    have hinit_eq : init' = s := by
      by_contra hne_init
      apply hprob_ne
      have hrw : pe.probOf ⟨init', trans'⟩ hterm
          = pe.probOf ⟨init', Seq.nil⟩ Stream'.Seq.terminates_nil := by subst htrans_nil; rfl
      rw [hrw, ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState, hpe]
      exact PMF.pure_apply_of_ne _ _ hne_init
    rw [he₀]
    exact Subtype.ext (by subst htrans_nil; subst hinit_eq; rfl)
  -- Halt mass at `e₀` is `1`: `probOf ⟨s, nil⟩ = (pure s) s = 1`, times `next none = 1`.
  have hhalt₀ : σ.haltMass (PMF.pure s) e₀ = 1 := by
    rw [he₀]
    unfold Scheduler.haltMass
    rw [← hpe]
    rw [show pe.probOf (⟨s, Seq.nil⟩ : AlterSeq State Label) Stream'.Seq.terminates_nil
        = (1 : ENNReal) by
      rw [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState, hpe,
        PMF.pure_apply_self]]
    rw [hnext_none, mul_one]
  -- Collapse the sum to the single fiber `e₀`.
  rw [tsum_eq_single e₀ (fun e he => by
    by_cases hz : σ.haltMass (PMF.pure s) e = 0
    · rw [hz, zero_mul]
    · exact absurd (hsupp e hz) he)]
  rw [hhalt₀, one_mul]
  -- `e₀.1.endState e₀.2 = s`.
  rw [he₀]
  rw [AlterSeq.endState_of_trans_nil ⟨s, Seq.nil⟩ rfl Stream'.Seq.terminates_nil]

/-- **The chain almost-surely halts with the composed pushforward.** Given that
every step of `steps` is a genuine `sys^w`-step from the threaded source
(`WeakChainValid`), integrating a test `g` against the halting end-state of
`Scheduler.weakChain sys steps s` (from the Dirac source `PMF.pure s`) equals the
iterated pushforward `weakChainPush steps s g`. Proven by induction on `steps`:
the base case is `haltNow_pushforward`, and the step peels the first witness via
`bind_compose_integrate`, applies the IH to the continuation, and collapses the
first weak step via `weakStepWitness_pushforward`. -/
theorem Scheduler.weakChain_pushforward (sys : LabelledSystem State Label) :
    ∀ (steps : List (Label × PMF State)) (s : State) (g : State → ENNReal),
      WeakChainValid sys steps s →
      (∑' e, (Scheduler.weakChain sys steps s).haltMass (PMF.pure s) e * g (e.1.endState e.2))
        = weakChainPush steps s g
  | List.nil, s, g, _ => by
      rw [show Scheduler.weakChain sys List.nil s = Scheduler.haltNow sys from rfl]
      rw [Scheduler.haltNow_pushforward sys s g]
      rfl
  | List.cons (l, μ) rest, s, g, hvalid => by
      classical
      obtain ⟨hstep, hrest⟩ := hvalid
      -- Unfold `weakChain` on the cons and peel the first witness via `bind`.
      rw [show Scheduler.weakChain sys (List.cons (l, μ) rest) s
          = Scheduler.bind (Scheduler.weakStepWitnessTotal sys s l μ)
              (fun s' => Scheduler.weakChain sys rest s') from rfl]
      rw [Scheduler.bind_compose_integrate (Scheduler.weakStepWitnessTotal sys s l μ)
        (fun s' => Scheduler.weakChain sys rest s') (PMF.pure s) g]
      -- The inner sum over `f₂` is the IH from `f₁`'s end-state.
      have hinner : ∀ f₁ : {e : AlterSeq State Label // e.trans.Terminates},
          (∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
              (Scheduler.weakChain sys rest (f₁.1.endState f₁.2)).haltMass
                (PMF.pure (f₁.1.endState f₁.2)) f₂ * g (f₂.1.endState f₂.2))
            = weakChainPush rest (f₁.1.endState f₁.2) g :=
        fun f₁ => Scheduler.weakChain_pushforward sys rest (f₁.1.endState f₁.2) g
          (hrest (f₁.1.endState f₁.2))
      rw [tsum_congr (fun f₁ => by rw [hinner f₁])]
      -- Rewrite the total witness to the genuine one and apply its pushforward.
      rw [Scheduler.weakStepWitnessTotal_eq sys s l μ hstep]
      rw [Scheduler.weakStepWitness_pushforward sys s l μ hstep
        (fun t => weakChainPush rest t g)]
      rfl

/-- **The chain almost-surely halts** (corollary, `g = 1`): given validity, the
total halt mass of `Scheduler.weakChain sys steps s` from `PMF.pure s` is `1`.
Follows from `weakChain_pushforward` with the constant test `g = fun _ => 1`,
since `weakChainPush steps s (fun _ => 1) = 1` (each `μ` is a PMF). -/
theorem Scheduler.weakChain_haltMass_one (sys : LabelledSystem State Label)
    (steps : List (Label × PMF State)) (s : State) (hvalid : WeakChainValid sys steps s) :
    (∑' e, (Scheduler.weakChain sys steps s).haltMass (PMF.pure s) e) = 1 := by
  have hp := Scheduler.weakChain_pushforward sys steps s (fun _ => 1) hvalid
  simp only [mul_one] at hp
  rw [hp]
  -- `weakChainPush steps s (fun _ => 1) = 1`, by induction on `steps`.
  clear hp hvalid
  induction steps generalizing s with
  | nil => rfl
  | cons hd rest ih =>
      obtain ⟨l, μ⟩ := hd
      rw [show weakChainPush (List.cons (l, μ) rest) s (fun _ => 1)
          = ∑' t, μ t * weakChainPush rest t (fun _ => 1) from rfl]
      rw [tsum_congr (fun t => by rw [ih t])]
      simp only [mul_one]
      exact PMF.tsum_coe μ

/-! #### The `expand` construction (belief-draw design)

`Scheduler.expand` is the *history-dependent* memoryless stuttering simulation of `pe'`.
At a terminating `sys`-history `e`:

* `ν' := (sys.internalSuffix e).init` is the *observable* last hyperStep boundary `ν'_k`
  (the state after `e`'s last external transition; `= e.init` at `⟨init, nil⟩`), and
  `L := (sys.trace e).toList` is the external trace realized so far. The trailing internal
  run (from `ν'`) is the in-progress post-τ;pre-τ;hs, threaded by `Scheduler.bind` at
  `sys.internalSuffix e`.

On `L.getLast?`:
* `none` (no external label yet): run `drawAndRun pe' ⟨init, nil⟩` — query `pe'` at the empty
  clean history and run the first weak step's pre-τ;hs.
* `some l` (`l` = the just-completed weak step's external label): draw `(E', μ)` from the
  belief `pe'.beliefExpand L ν'`, where `E'` is the **clean** prior `sys^w`-history (σ-states,
  no stutter) and `μ` the just-completed step's result PMF. The belief weights `μ` by
  `postDist ν'` — the hyperStep-target distribution `ν'` is genuinely sampled from — so it
  recovers the drawn `μ` (unlike the old `lastMuBelief`, which weighted by `μ ν'` and
  degenerated). Then run `segmentScheduler pe' ν' l E' μ`: replay the post-τ
  (`postTauWitness (E'.endState) l μ`) to reach a sample `σ_k`, form the **clean** history
  `E' ++ [(l, σ_k)]`, and `drawAndRun` the next step there (so `pe'` is queried *on-path*).

Validity is **free**: every branch (`postTauWitness`, `preHsWitness`, `haltNow`,
`Scheduler.bind`) is a valid `Scheduler sys.toSystem`, so the belief mixture is valid too. -/

open Classical in
/-- The **pre-τ-and-hs** witness of the weak step `s →[l] μ`: the `weakStepWitness` chain
*minus its final post-τ closure* (that is the next segment's post-τ). For external `l`,
`Scheduler.bind (pre-τ witness) (extStep for the hs)`; for internal `l`, the τ-witness; off
support, `haltNow`. The decisive point for continuation: for external `l` it always emits a
transition (the pre-τ's first step or the hs `l`). -/
noncomputable def Scheduler.preHsWitness (sys : LabelledSystem State Label)
    (s : State) (l : Label) (μ : PMF State) : Scheduler sys.toSystem :=
  if h : sys^w.step s l μ then
    if h_int : sys.internal l then
      (((h.resolve_right (fun hb => hb.1 h_int)).2).witnessScheduler.toScheduler)
    else
      let hws : weakStep sys (PMF.pure s) l μ := (h.resolve_left (fun ha => h_int ha.1)).2
      Scheduler.bind hws.weakTau_pre.witnessScheduler.toScheduler (fun _ =>
        Scheduler.extStep sys hws.preDist l hws.hyperStep_mid.kernel
          (hws.hyperStep_mid.kernel_step))
  else Scheduler.haltNow sys

open Classical in
/-- **The posterior weight of a drawn weak step `opt` given the running trajectory `h`.**
The fixed prior `pe'.scheduler.next E''` is reweighted by the *likelihood* of the running
`sys`-history `h` under each option: for `some (l, μ)`, the likelihood is the `probOf` that
`preHsWitness sys (E''.endState hT) l μ` (run from the Dirac source `pure (E''.endState hT)`)
realizes exactly `h`; for `none`, the likelihood is `1` iff `h` is the empty halt history at
`E''`'s end-state, else `0`. Options whose witness *cannot* produce `h` (off-trajectory) get
likelihood `0` and drop out — eliminating the spurious off-trajectory halt mass that the
fixed-prior re-draw leaked (the 7th flaw; see `B2Check`). -/
noncomputable def Scheduler.drawAndRunW {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E'' : AlterSeq State Label)
    (hT : E''.trans.Terminates) (h : AlterSeq State Label) :
    Option (Label × PMF State) → ENNReal := fun opt =>
  pe'.scheduler.next E'' opt *
    (match opt with
     | none => if h = (⟨E''.endState hT, Stream'.Seq.nil⟩ : AlterSeq State Label) then 1 else 0
     | some (l, μ) =>
         if hh : h.trans.Terminates then
           (⟨PMF.pure (E''.endState hT), Scheduler.preHsWitness sys (E''.endState hT) l μ⟩
              : ProbabilisticExecution sys.toSystem).probOf h hh
         else 0)

/-- **Finiteness of the posterior normaliser.** Each likelihood factor is `≤ 1` (a `probOf`
is `≤ pe.init ≤ 1`, and the `if … 1 else 0` is `≤ 1`), so `∑' opt, drawAndRunW … opt ≤
∑' opt, pe'.scheduler.next E'' opt = 1 ≠ ⊤`. -/
theorem Scheduler.drawAndRunW_tsum_ne_top {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E'' : AlterSeq State Label)
    (hT : E''.trans.Terminates) (h : AlterSeq State Label) :
    (∑' opt, Scheduler.drawAndRunW pe' E'' hT h opt) ≠ ⊤ := by
  classical
  suffices hle : (∑' opt, Scheduler.drawAndRunW pe' E'' hT h opt) ≤ 1 from
    (lt_of_le_of_lt hle ENNReal.one_lt_top).ne
  calc (∑' opt, Scheduler.drawAndRunW pe' E'' hT h opt)
      ≤ ∑' opt, pe'.scheduler.next E'' opt := by
        refine ENNReal.tsum_le_tsum (fun opt => ?_)
        unfold Scheduler.drawAndRunW
        refine mul_le_of_le_one_right' ?_
        split
        · split <;> simp
        · split
          · exact le_trans (ProbabilisticExecution.probOf_le_init _ _ _) (PMF.coe_le_one _ _)
          · exact zero_le_one
    _ = 1 := (pe'.scheduler.next E'').tsum_coe

open Classical in
/-- **Draw the next clean weak step from `pe'` (POSTERIOR-conditioned) and run its pre-τ;hs.**
Takes the *clean* `sys^w`-history `E''` directly (`E' ++ [(l, σ_k)]`, the reached on-path
history after the just-completed step's post-τ). When `E''` terminates, reweight the prior
`pe'.scheduler.next E''` by the likelihood of the running `sys`-history `h` (see
`drawAndRunW`) and *normalise* — this conditions the draw on the trajectory, so off-path
options drop out (fixing the 7th flaw). On a drawn `some (l, μ)`, run `preHsWitness sys
(E''.endState) l μ` at `h`; on `none`, halt. If the posterior normaliser vanishes (no option
explains `h`) or `E''` does not terminate, halt. -/
noncomputable def Scheduler.drawAndRun {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E'' : AlterSeq State Label) :
    Scheduler sys.toSystem where
  next h :=
    if hT : E''.trans.Terminates then
      if h0 : (∑' opt, Scheduler.drawAndRunW pe' E'' hT h opt) ≠ 0 then
        (PMF.normalize (Scheduler.drawAndRunW pe' E'' hT h) h0
            (Scheduler.drawAndRunW_tsum_ne_top pe' E'' hT h)).bind (fun opt =>
          match opt with
          | none        => PMF.pure none
          | some (l, μ) => (Scheduler.preHsWitness sys (E''.endState hT) l μ).next h)
      else PMF.pure none
    else PMF.pure none
  valid := by
    classical
    intro e n s' e_term_n e_stateAt_eq l μ h_supp
    change some (l, μ) ∈
      (if hT : E''.trans.Terminates then
        if h0 : (∑' opt, Scheduler.drawAndRunW pe' E'' hT e opt) ≠ 0 then
          (PMF.normalize (Scheduler.drawAndRunW pe' E'' hT e) h0
              (Scheduler.drawAndRunW_tsum_ne_top pe' E'' hT e)).bind (fun opt =>
            match opt with
            | none        => PMF.pure none
            | some (l', μ') => (Scheduler.preHsWitness sys (E''.endState hT) l' μ').next e)
        else PMF.pure none
      else PMF.pure none).support at h_supp
    by_cases hT : E''.trans.Terminates
    · rw [dif_pos hT] at h_supp
      by_cases h0 : (∑' opt, Scheduler.drawAndRunW pe' E'' hT e opt) ≠ 0
      · rw [dif_pos h0, PMF.mem_support_bind_iff] at h_supp
        obtain ⟨opt, _hopt, h_supp⟩ := h_supp
        cases opt with
        | none =>
          change some (l, μ) ∈ (PMF.pure (α := Option (Label × PMF State)) none).support at h_supp
          rw [PMF.support_pure, Set.mem_singleton_iff] at h_supp
          exact absurd h_supp (by simp)
        | some lμ =>
          obtain ⟨l', μ'⟩ := lμ
          exact (Scheduler.preHsWitness sys (E''.endState hT) l' μ').valid
            e n s' e_term_n e_stateAt_eq l μ h_supp
      · rw [dif_neg h0, PMF.support_pure, Set.mem_singleton_iff] at h_supp
        exact absurd h_supp (by simp)
    · rw [dif_neg hT, PMF.support_pure, Set.mem_singleton_iff] at h_supp
      exact absurd h_supp (by simp)

/-- The one-step kernel of `haltNow` is `0`: the immediate-halt scheduler never
emits a `some` step, so `(⟨ν, haltNow⟩).kernel e p = 0` for every prefix `e` and
step `p`. -/
theorem Scheduler.haltNow_kernel_eq_zero (sys : LabelledSystem State Label)
    (ν : PMF State) (e : AlterSeq State Label) (p : Label × State) :
    (⟨ν, Scheduler.haltNow sys⟩ : ProbabilisticExecution sys.toSystem).kernel e p = 0 := by
  unfold ProbabilisticExecution.kernel
  refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
  change (Scheduler.haltNow sys).next e (some (p.1, μ)) * μ p.2 = 0
  simp [Scheduler.haltNow, PMF.pure_apply]

open Classical in
/-- **`probOf` under `haltNow`.** The immediate-halt scheduler run from the Dirac
source `pure s` realizes exactly the empty execution `⟨s, nil⟩` with mass `1`, and
everything else with mass `0`. -/
theorem Scheduler.haltNow_probOf (sys : LabelledSystem State Label) (s : State)
    (e : AlterSeq State Label) (he : e.trans.Terminates) :
    (⟨PMF.pure s, Scheduler.haltNow sys⟩ : ProbabilisticExecution sys.toSystem).probOf e he
      = if e = (⟨s, Stream'.Seq.nil⟩ : AlterSeq State Label) then 1 else 0 := by
  classical
  obtain ⟨ei, et⟩ := e
  set pe : ProbabilisticExecution sys.toSystem := ⟨PMF.pure s, Scheduler.haltNow sys⟩ with hpe
  -- rewrite `et` as `ofList (toList)` and factor via pathWeight
  have he_ofList : (⟨ei, et⟩ : AlterSeq State Label)
      = ⟨ei, Seq.ofList (et.toList he)⟩ := by
    congr 1; exact (Stream'.Seq.ofList_toList et he).symm
  rw [pe.probOf_congr ⟨ei, et⟩ ⟨ei, Seq.ofList (et.toList he)⟩ he_ofList he
        (Stream'.Seq.terminates_ofList _),
    pe.probOf_eq_pathWeight ei (et.toList he) (Stream'.Seq.terminates_ofList _)]
  -- pathWeight from a haltNow scheduler: `1` on the empty list, `0` otherwise
  rcases List.eq_nil_or_concat (et.toList he) with hL | ⟨rest, last, hL⟩
  · -- empty trans: probOf = init = (pure s) ei = if ei = s then 1 else 0
    rw [hL]
    unfold ProbabilisticExecution.pathWeight
    rw [List.reverseRecOn_nil, mul_one]
    change (PMF.pure s) ei = _
    rw [PMF.pure_apply]
    -- `et = nil` since toList = []
    have htrans_nil : et = Seq.nil := by
      have := Stream'.Seq.ofList_toList et he
      rw [hL] at this; rw [← this]; rfl
    by_cases hi : ei = s
    · have heq : (⟨ei, et⟩ : AlterSeq State Label) = ⟨s, Seq.nil⟩ := by
        rw [htrans_nil, hi]
      rw [if_pos hi, if_pos heq]
    · have hne : (⟨ei, et⟩ : AlterSeq State Label) ≠ ⟨s, Seq.nil⟩ := by
        intro hcon; exact hi (congrArg AlterSeq.init hcon)
      rw [if_neg hi, if_neg hne]
  · -- nonempty trans: pathWeight has a `0` kernel factor, so probOf = 0
    rw [hL, List.concat_eq_append]
    unfold ProbabilisticExecution.pathWeight
    rw [List.reverseRecOn_concat, Scheduler.haltNow_kernel_eq_zero, mul_zero, mul_zero]
    rw [if_neg]
    intro hcon
    -- `⟨ei,et⟩ = ⟨s, nil⟩` forces `et = nil` hence `toList = []`, contradicting `hL`
    have hnil : et = Seq.nil := congrArg AlterSeq.trans hcon
    have : et.toList he = [] := by simp [hnil, Stream'.Seq.toList_nil]
    rw [this, List.concat_eq_append] at hL
    exact (List.append_ne_nil_of_right_ne_nil rest (by simp)) hL.symm

open Classical in
/-- The per-option **committed witness** of a drawn weak step `opt` (the scheduler the
posterior-bind `drawAndRun` actually runs once `opt` is committed): for `some (l, μ)` it is
the pre-τ;hs witness `preHsWitness sys s l μ`; for `none` (halt) it is `haltNow`. -/
noncomputable def Scheduler.drawWit (sys : LabelledSystem State Label) (s : State) :
    Option (Label × PMF State) → Scheduler sys.toSystem
  | none        => Scheduler.haltNow sys
  | some (l, μ) => Scheduler.preHsWitness sys s l μ

/-- **The likelihood factor of `drawAndRunW` is the witness `probOf`.** For terminating `h`,
the per-option likelihood weight in `drawAndRunW` equals `(⟨pure (endState), drawWit opt⟩).probOf h`
(the `none` branch's `if h = ⟨endState,nil⟩ then 1 else 0` is exactly `haltNow`'s `probOf`). -/
theorem Scheduler.drawAndRunW_eq {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E'' : AlterSeq State Label)
    (hT : E''.trans.Terminates) (h : AlterSeq State Label) (hh : h.trans.Terminates)
    (opt : Option (Label × PMF State)) :
    Scheduler.drawAndRunW pe' E'' hT h opt
      = pe'.scheduler.next E'' opt *
          (⟨PMF.pure (E''.endState hT), Scheduler.drawWit sys (E''.endState hT) opt⟩
            : ProbabilisticExecution sys.toSystem).probOf h hh := by
  classical
  unfold Scheduler.drawAndRunW
  congr 1
  cases opt with
  | none =>
    simp only [Scheduler.drawWit]
    rw [Scheduler.haltNow_probOf]
  | some lμ =>
    obtain ⟨l, μ⟩ := lμ
    simp only [Scheduler.drawWit, dif_pos hh]

/-- **Generic `normalize` cancellation** (the `beliefExpand_normalize_cancel` shape, abstracted):
`(∑' o, W o) * (∑' o, normalize(W) o * w o) = ∑' o, W o * w o`, valid whether or not the
normaliser vanishes. -/
theorem ProbabilisticExecution.normalize_cancel {ι : Type*} (W : ι → ENNReal)
    (hWtop : (∑' o, W o) ≠ ⊤) (w : ι → ENNReal) (hZ0 : (∑' o, W o) ≠ 0) :
    (∑' o, W o) * (∑' o, W o * (∑' o', W o')⁻¹ * w o) = ∑' o, W o * w o := by
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr (fun o => ?_)
  rw [show (∑' o', W o') * (W o * (∑' o', W o')⁻¹ * w o)
        = ((∑' o', W o') * (∑' o', W o')⁻¹) * (W o * w o) by ring,
    ENNReal.mul_inv_cancel hZ0 hWtop, one_mul]

/-- **Expansion of the posterior-bind emission.** When the posterior normaliser does not vanish,
the emission `drawAndRun.next e' (some (l, μ))` is the posterior-weighted sum of the per-option
committed-witness emissions `(drawWit opt).next e' (some (l, μ))` (the `none` branch's `pure none`
agrees with `haltNow`'s emission, namely `0`). -/
theorem Scheduler.drawAndRun_next_some {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E'' : AlterSeq State Label)
    (hT : E''.trans.Terminates) (e' : AlterSeq State Label)
    (h0 : (∑' opt, Scheduler.drawAndRunW pe' E'' hT e' opt) ≠ 0) (l : Label) (μ : PMF State) :
    (Scheduler.drawAndRun pe' E'').next e' (some (l, μ))
      = ∑' opt, (PMF.normalize (Scheduler.drawAndRunW pe' E'' hT e') h0
            (Scheduler.drawAndRunW_tsum_ne_top pe' E'' hT e')) opt *
          (Scheduler.drawWit sys (E''.endState hT) opt).next e' (some (l, μ)) := by
  classical
  change (if hT' : E''.trans.Terminates then
      if h0' : (∑' opt, Scheduler.drawAndRunW pe' E'' hT' e' opt) ≠ 0 then
        (PMF.normalize (Scheduler.drawAndRunW pe' E'' hT' e') h0'
            (Scheduler.drawAndRunW_tsum_ne_top pe' E'' hT' e')).bind (fun opt =>
          match opt with
          | none        => PMF.pure none
          | some (l, μ) => (Scheduler.preHsWitness sys (E''.endState hT') l μ).next e')
      else PMF.pure none
    else PMF.pure none) (some (l, μ)) = _
  rw [dif_pos hT, dif_pos h0, PMF.bind_apply]
  refine tsum_congr (fun opt => ?_)
  congr 1
  cases opt with
  | none =>
    change (PMF.pure (α := Option (Label × PMF State)) none) (some (l, μ))
      = (Scheduler.haltNow sys).next e' (some (l, μ))
    simp [Scheduler.haltNow, PMF.pure_apply]
  | some lμ =>
    obtain ⟨l₀, μ₀⟩ := lμ
    rfl

/-- **One-step kernel of the posterior-bind scheduler as a posterior average.** When the
posterior normaliser `Z' := ∑' opt, drawAndRunW … opt` does not vanish, the `drawAndRun`
kernel at `e'` is the posterior-weighted average of the committed witnesses' kernels. -/
theorem Scheduler.drawAndRun_kernel_eq {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E'' : AlterSeq State Label)
    (hT : E''.trans.Terminates) (e' : AlterSeq State Label)
    (h0 : (∑' opt, Scheduler.drawAndRunW pe' E'' hT e' opt) ≠ 0) (p : Label × State) :
    (⟨PMF.pure (E''.endState hT), Scheduler.drawAndRun pe' E''⟩
        : ProbabilisticExecution sys.toSystem).kernel e' p
      = ∑' opt, (PMF.normalize (Scheduler.drawAndRunW pe' E'' hT e') h0
            (Scheduler.drawAndRunW_tsum_ne_top pe' E'' hT e')) opt *
          (⟨PMF.pure (E''.endState hT), Scheduler.drawWit sys (E''.endState hT) opt⟩
            : ProbabilisticExecution sys.toSystem).kernel e' p := by
  classical
  obtain ⟨l, s'⟩ := p
  unfold ProbabilisticExecution.kernel
  -- expand the scheduler emission, swap sums, pull the posterior weight out
  have hexp : ∀ μ : PMF State,
      (⟨PMF.pure (E''.endState hT), Scheduler.drawAndRun pe' E''⟩
          : ProbabilisticExecution sys.toSystem).scheduler.next e' (some (l, μ)) * μ s'
        = ∑' opt, (PMF.normalize (Scheduler.drawAndRunW pe' E'' hT e') h0
              (Scheduler.drawAndRunW_tsum_ne_top pe' E'' hT e')) opt *
            ((Scheduler.drawWit sys (E''.endState hT) opt).next e' (some (l, μ)) * μ s') := by
    intro μ
    rw [show (⟨PMF.pure (E''.endState hT), Scheduler.drawAndRun pe' E''⟩
            : ProbabilisticExecution sys.toSystem).scheduler.next e' (some (l, μ))
          = (Scheduler.drawAndRun pe' E'').next e' (some (l, μ)) from rfl,
      Scheduler.drawAndRun_next_some pe' E'' hT e' h0 l μ, ← ENNReal.tsum_mul_right]
    refine tsum_congr (fun opt => ?_); rw [mul_assoc]
  rw [tsum_congr hexp, ENNReal.tsum_comm]
  refine tsum_congr (fun opt => ?_)
  rw [ENNReal.tsum_mul_left]

/-- The **posterior marginal** `Z e'` at a running history `e'`: the prior-weighted sum of the
committed witnesses' `probOf` (the RHS of the keystone, evaluated at the prefix `e'`). -/
noncomputable def Scheduler.drawZ {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E'' : AlterSeq State Label)
    (hT : E''.trans.Terminates) (e' : AlterSeq State Label) (he' : e'.trans.Terminates) :
    ENNReal :=
  ∑' opt : Option (Label × PMF State),
    pe'.scheduler.next E'' opt *
      (⟨PMF.pure (E''.endState hT), Scheduler.drawWit sys (E''.endState hT) opt⟩
        : ProbabilisticExecution sys.toSystem).probOf e' he'

/-- `drawZ` depends only on the running history, not the termination proof (equal histories
have equal `drawZ`). -/
theorem Scheduler.drawZ_congr {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E'' : AlterSeq State Label)
    (hT : E''.trans.Terminates) (e e' : AlterSeq State Label) (h_eq : e = e')
    (he : e.trans.Terminates) (he' : e'.trans.Terminates) :
    Scheduler.drawZ pe' E'' hT e he = Scheduler.drawZ pe' E'' hT e' he' := by
  subst h_eq; rfl

/-- `drawZ` is exactly the posterior normaliser `∑' opt, drawAndRunW … opt`. -/
theorem Scheduler.drawZ_eq_tsum_drawAndRunW {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E'' : AlterSeq State Label)
    (hT : E''.trans.Terminates) (e' : AlterSeq State Label) (he' : e'.trans.Terminates) :
    Scheduler.drawZ pe' E'' hT e' he'
      = ∑' opt, Scheduler.drawAndRunW pe' E'' hT e' opt := by
  unfold Scheduler.drawZ
  exact (tsum_congr (fun opt => (Scheduler.drawAndRunW_eq pe' E'' hT e' he' opt).symm))

/-- **Telescoping step (multiplicative kernel-ratio).** Extending the running history `⟨s₀, sq⟩`
by one transition `last` multiplies the posterior marginal `drawZ` by the `drawAndRun` kernel:
`drawZ (⟨s₀, sq ++ [last]⟩) = drawZ ⟨s₀, sq⟩ * drawAndRun.kernel ⟨s₀, sq⟩ last`. This is the
division-free form of `kernel = Z(e'++[t]) / Z(e')`, handling the vanishing-normaliser case. -/
theorem Scheduler.drawZ_step {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E'' : AlterSeq State Label)
    (hT : E''.trans.Terminates) (s₀ : State) (sq : Seq (Label × State)) (h_sq : sq.Terminates)
    (last : Label × State)
    (h_app : (sq.append (Seq.cons last Seq.nil)).Terminates) :
    Scheduler.drawZ pe' E'' hT ⟨s₀, sq.append (Seq.cons last Seq.nil)⟩ h_app
      = Scheduler.drawZ pe' E'' hT ⟨s₀, sq⟩ h_sq
        * (⟨PMF.pure (E''.endState hT), Scheduler.drawAndRun pe' E''⟩
            : ProbabilisticExecution sys.toSystem).kernel ⟨s₀, sq⟩ last := by
  classical
  set e' : AlterSeq State Label := ⟨s₀, sq⟩ with he'_def
  set e'' : AlterSeq State Label := ⟨s₀, sq.append (Seq.cons last Seq.nil)⟩ with he''_def
  -- each witness `probOf` telescopes: probOf(e'') = probOf(e') * kernel
  have htel : ∀ opt : Option (Label × PMF State),
      (⟨PMF.pure (E''.endState hT), Scheduler.drawWit sys (E''.endState hT) opt⟩
          : ProbabilisticExecution sys.toSystem).probOf e'' h_app
        = (⟨PMF.pure (E''.endState hT), Scheduler.drawWit sys (E''.endState hT) opt⟩
            : ProbabilisticExecution sys.toSystem).probOf e' h_sq
          * (⟨PMF.pure (E''.endState hT), Scheduler.drawWit sys (E''.endState hT) opt⟩
              : ProbabilisticExecution sys.toSystem).kernel e' last := by
    intro opt
    exact (ProbabilisticExecution.probOf_append_singleton _ s₀ sq h_sq last h_app)
  by_cases h0 : Scheduler.drawZ pe' E'' hT e' h_sq = 0
  · -- vanishing normaliser: both sides are 0
    rw [h0, zero_mul]
    -- drawZ e' = 0 ⟹ every prior·probOf(e') = 0 ⟹ every prior·probOf(e'') = 0
    have hz : ∀ opt, pe'.scheduler.next E'' opt *
        (⟨PMF.pure (E''.endState hT), Scheduler.drawWit sys (E''.endState hT) opt⟩
          : ProbabilisticExecution sys.toSystem).probOf e' h_sq = 0 :=
      ENNReal.tsum_eq_zero.mp h0
    unfold Scheduler.drawZ
    refine ENNReal.tsum_eq_zero.mpr (fun opt => ?_)
    rw [htel opt, ← mul_assoc, hz opt, zero_mul]
  · -- nonvanishing normaliser: use the kernel-as-posterior-average + normalize cancel
    have h0' : (∑' opt, Scheduler.drawAndRunW pe' E'' hT e' opt) ≠ 0 := by
      rwa [← Scheduler.drawZ_eq_tsum_drawAndRunW pe' E'' hT e' h_sq]
    rw [Scheduler.drawAndRun_kernel_eq pe' E'' hT e' h0' last]
    -- pull the normaliser through: drawZ e' * ∑' opt, normalize(W) opt * K opt
    --   = ∑' opt, W opt * K opt  (normalize_cancel) = ∑' opt, prior·probOf(e')·K = drawZ e''
    rw [show Scheduler.drawZ pe' E'' hT e' h_sq
          = ∑' opt, Scheduler.drawAndRunW pe' E'' hT e' opt
        from Scheduler.drawZ_eq_tsum_drawAndRunW pe' E'' hT e' h_sq]
    simp only [PMF.normalize_apply]
    rw [ProbabilisticExecution.normalize_cancel _
        (Scheduler.drawAndRunW_tsum_ne_top pe' E'' hT e') _ h0']
    -- now: ∑' opt, drawAndRunW opt * K opt = drawZ e''
    unfold Scheduler.drawZ
    refine tsum_congr (fun opt => ?_)
    rw [Scheduler.drawAndRunW_eq pe' E'' hT e' h_sq opt, htel opt, mul_assoc]

/-- **Base case `Z₀ = 1`.** At the empty halt history `⟨endState, nil⟩`, every committed witness
realizes the empty execution with mass `1` (the Dirac source `pure endState` puts mass `1` on
`endState`), so the posterior marginal collapses to the prior PMF's total mass `1`. This is why
`drawAndRun` carries **no** extra normalisation factor — its prior `pe'.next E''` is a full PMF. -/
theorem Scheduler.drawZ_nil {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E'' : AlterSeq State Label)
    (hT : E''.trans.Terminates) :
    Scheduler.drawZ pe' E'' hT ⟨E''.endState hT, Stream'.Seq.nil⟩ Stream'.Seq.terminates_nil
      = 1 := by
  unfold Scheduler.drawZ
  rw [show (∑' opt : Option (Label × PMF State), pe'.scheduler.next E'' opt *
        (⟨PMF.pure (E''.endState hT), Scheduler.drawWit sys (E''.endState hT) opt⟩
          : ProbabilisticExecution sys.toSystem).probOf
            ⟨E''.endState hT, Stream'.Seq.nil⟩ Stream'.Seq.terminates_nil)
      = ∑' opt, pe'.scheduler.next E'' opt from
    tsum_congr (fun opt => by
      rw [ProbabilisticExecution.probOf_nil]
      change pe'.scheduler.next E'' opt * (PMF.pure (E''.endState hT)) (E''.endState hT) = _
      rw [PMF.pure_apply_self, mul_one])]
  exact (pe'.scheduler.next E'').tsum_coe

/-- **Telescoping (auxiliary, over `ofList`).** The `drawAndRun` `probOf` from the Dirac source
`pure (endState)` equals the posterior marginal `drawZ`, proven by reverse (cons-end) induction on
the transition list: base = `drawZ_nil = 1`; step = `probOf_append_singleton` (peel `last`) + the
IH + the kernel-ratio `drawZ_step`. -/
theorem Scheduler.drawAndRun_probOf_eq_drawZ_ofList {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E'' : AlterSeq State Label)
    (hT : E''.trans.Terminates) (trans : List (Label × State))
    (hFin : (Seq.ofList trans : Seq (Label × State)).Terminates) :
    (⟨PMF.pure (E''.endState hT), Scheduler.drawAndRun pe' E''⟩
        : ProbabilisticExecution sys.toSystem).probOf
          ⟨E''.endState hT, Seq.ofList trans⟩ hFin
      = Scheduler.drawZ pe' E'' hT ⟨E''.endState hT, Seq.ofList trans⟩ hFin := by
  classical
  induction trans using List.reverseRecOn with
  | nil =>
    -- base: probOf ⟨endState, nil⟩ = init endState = 1 = drawZ ⟨endState, nil⟩
    have hnil : (⟨E''.endState hT, Seq.ofList []⟩ : AlterSeq State Label)
        = ⟨E''.endState hT, Stream'.Seq.nil⟩ := by simp [Stream'.Seq.ofList_nil]
    rw [ProbabilisticExecution.probOf_congr _ ⟨E''.endState hT, Seq.ofList []⟩
        ⟨E''.endState hT, Stream'.Seq.nil⟩ hnil hFin Stream'.Seq.terminates_nil,
      ProbabilisticExecution.probOf_nil,
      Scheduler.drawZ_congr pe' E'' hT ⟨E''.endState hT, Seq.ofList []⟩
        ⟨E''.endState hT, Stream'.Seq.nil⟩ hnil hFin Stream'.Seq.terminates_nil,
      Scheduler.drawZ_nil]
    change (PMF.pure (E''.endState hT)) (E''.endState hT) = 1
    rw [PMF.pure_apply_self]
  | append_singleton rest last ih =>
    -- step: peel `last`, use IH on `rest`, then `drawZ_step`
    have hrest_term : (Seq.ofList rest : Seq (Label × State)).Terminates :=
      Stream'.Seq.terminates_ofList rest
    -- ofList (rest ++ [last]) = (ofList rest).append (cons last nil)
    have hsplit : (Seq.ofList (rest ++ [last]) : Seq (Label × State))
        = (Seq.ofList rest).append (Seq.cons last Seq.nil) := by
      rw [Stream'.Seq.ofList_append]
      congr 1
      rw [Stream'.Seq.ofList_cons]
      simp [Stream'.Seq.ofList_nil]
    have happ_term : ((Seq.ofList rest).append (Seq.cons last Seq.nil)
        : Seq (Label × State)).Terminates := by rw [← hsplit]; exact hFin
    have heq_ext : (⟨E''.endState hT, Seq.ofList (rest ++ [last])⟩ : AlterSeq State Label)
        = ⟨E''.endState hT, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩ := by rw [hsplit]
    rw [ProbabilisticExecution.probOf_congr _
        ⟨E''.endState hT, Seq.ofList (rest ++ [last])⟩
        ⟨E''.endState hT, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩
        heq_ext hFin happ_term,
      ProbabilisticExecution.probOf_append_singleton _ (E''.endState hT) (Seq.ofList rest)
        hrest_term last happ_term,
      ih hrest_term,
      ← Scheduler.drawZ_step pe' E'' hT (E''.endState hT) (Seq.ofList rest) hrest_term last
        happ_term]
    -- conclude: drawZ at the appended form = drawZ at ofList (rest ++ [last])
    exact Scheduler.drawZ_congr pe' E'' hT
      ⟨E''.endState hT, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩
      ⟨E''.endState hT, Seq.ofList (rest ++ [last])⟩ heq_ext.symm happ_term hFin

/-- **KEYSTONE: the filter-marginal identity for `drawAndRun`.** The posterior-bind scheduler's
`probOf` from the Dirac source `pure (E''.endState hT)` is the **prior-weighted sum** of the
committed witnesses' `probOf`:
`drawAndRun.probOf e = ∑' opt, pe'.next E'' opt * (⟨pure endState, drawWit opt⟩).probOf e`.
(`drawWit none = haltNow`, `drawWit (some (l,μ)) = preHsWitness sys (endState) l μ`.) There is
**no extra normalisation factor**: the base marginal `Z₀ = drawZ ⟨endState, nil⟩ = 1`, because the
prior `pe'.next E''` is a full PMF and every witness realizes the empty history with mass `1`.
Proven by HMM/Bayes-filter telescoping (`drawZ_step` kernel-ratio +
`drawAndRun_probOf_eq_drawZ_ofList`). -/
theorem Scheduler.drawAndRun_probOf_eq {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E'' : AlterSeq State Label)
    (hT : E''.trans.Terminates)
    (e : AlterSeq State Label) (he : e.trans.Terminates) (he_init : e.init = E''.endState hT) :
    (⟨PMF.pure (E''.endState hT), Scheduler.drawAndRun pe' E''⟩
        : ProbabilisticExecution sys.toSystem).probOf e he
      = ∑' opt : Option (Label × PMF State),
          pe'.scheduler.next E'' opt *
            (⟨PMF.pure (E''.endState hT), Scheduler.drawWit sys (E''.endState hT) opt⟩
              : ProbabilisticExecution sys.toSystem).probOf e he := by
  classical
  -- rewrite `e` to its `ofList`/`endState` normal form, then invoke the telescoping aux
  have he_ofList : e = ⟨E''.endState hT, Seq.ofList (e.trans.toList he)⟩ := by
    obtain ⟨ei, et⟩ := e
    simp only at he_init
    subst he_init
    congr 1
    exact (Stream'.Seq.ofList_toList et he).symm
  have hFin' : (Seq.ofList (e.trans.toList he) : Seq (Label × State)).Terminates :=
    Stream'.Seq.terminates_ofList _
  rw [ProbabilisticExecution.probOf_congr _ e
      ⟨E''.endState hT, Seq.ofList (e.trans.toList he)⟩ he_ofList he hFin',
    Scheduler.drawAndRun_probOf_eq_drawZ_ofList pe' E'' hT (e.trans.toList he) hFin']
  -- the RHS sum is exactly `drawZ e he` after the same `probOf_congr`
  unfold Scheduler.drawZ
  refine tsum_congr (fun opt => ?_)
  rw [ProbabilisticExecution.probOf_congr _ e
      ⟨E''.endState hT, Seq.ofList (e.trans.toList he)⟩ he_ofList he hFin']

/-- **The `none`-emission of the posterior-bind scheduler as a posterior average.** When the
posterior normaliser does not vanish, `drawAndRun.next e' none` is the posterior-weighted sum of
the per-option committed-witness `none`-emissions (mirror of `drawAndRun_next_some`). The `none`
branch's `pure none` puts mass `1` on `none`, matching `haltNow`'s `next _ none = 1`. -/
theorem Scheduler.drawAndRun_next_none {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E'' : AlterSeq State Label)
    (hT : E''.trans.Terminates) (e' : AlterSeq State Label)
    (h0 : (∑' opt, Scheduler.drawAndRunW pe' E'' hT e' opt) ≠ 0) :
    (Scheduler.drawAndRun pe' E'').next e' none
      = ∑' opt, (PMF.normalize (Scheduler.drawAndRunW pe' E'' hT e') h0
            (Scheduler.drawAndRunW_tsum_ne_top pe' E'' hT e')) opt *
          (Scheduler.drawWit sys (E''.endState hT) opt).next e' none := by
  classical
  change (if hT' : E''.trans.Terminates then
      if h0' : (∑' opt, Scheduler.drawAndRunW pe' E'' hT' e' opt) ≠ 0 then
        (PMF.normalize (Scheduler.drawAndRunW pe' E'' hT' e') h0'
            (Scheduler.drawAndRunW_tsum_ne_top pe' E'' hT' e')).bind (fun opt =>
          match opt with
          | none        => PMF.pure none
          | some (l, μ) => (Scheduler.preHsWitness sys (E''.endState hT') l μ).next e')
      else PMF.pure none
    else PMF.pure none) none = _
  rw [dif_pos hT, dif_pos h0, PMF.bind_apply]
  refine tsum_congr (fun opt => ?_)
  congr 1
  cases opt with
  | none =>
    change (PMF.pure (α := Option (Label × PMF State)) none) none
      = (Scheduler.haltNow sys).next e' none
    simp [Scheduler.haltNow, PMF.pure_apply]
  | some lμ =>
    obtain ⟨l₀, μ₀⟩ := lμ
    rfl

/-- **Per-execution halt-mass marginal of `drawAndRun`** (the `haltMass` analogue of the
keystone `drawAndRun_probOf_eq`). The halting mass of the posterior-bind scheduler at a
terminating execution `e` (boundary `e.init = endState`) is the **prior-weighted sum** of the
committed witnesses' halt masses:
`drawAndRun.haltMass e = ∑' opt, pe'.next E'' opt * (drawWit opt).haltMass e`.
The proof multiplies the `probOf` marginal (keystone) by the `none`-emission posterior average:
the `drawZ e` normaliser cancels (`Z₀ = 1`). -/
theorem Scheduler.drawAndRun_haltMass_marginal {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E'' : AlterSeq State Label)
    (hT : E''.trans.Terminates)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) (he_init : e.1.init = E''.endState hT) :
    (Scheduler.drawAndRun pe' E'').haltMass (PMF.pure (E''.endState hT)) e
      = ∑' opt : Option (Label × PMF State),
          pe'.scheduler.next E'' opt *
            (Scheduler.drawWit sys (E''.endState hT) opt).haltMass
              (PMF.pure (E''.endState hT)) e := by
  classical
  -- key rewrite: probOf of `drawAndRun` from the Dirac source at `e` equals `drawZ e`
  have hPeq : (⟨PMF.pure (E''.endState hT), Scheduler.drawAndRun pe' E''⟩
        : ProbabilisticExecution sys.toSystem).probOf e.1 e.2
      = Scheduler.drawZ pe' E'' hT e.1 e.2 := by
    rw [Scheduler.drawAndRun_probOf_eq pe' E'' hT e.1 e.2 he_init]; rfl
  unfold Scheduler.haltMass
  rw [hPeq]
  by_cases h0 : (∑' opt, Scheduler.drawAndRunW pe' E'' hT e.1 opt) ≠ 0
  · -- nonvanishing normaliser: expand `next none` as posterior average, multiply by drawZ e
    rw [Scheduler.drawAndRun_next_none pe' E'' hT e.1 h0,
      Scheduler.drawZ_eq_tsum_drawAndRunW pe' E'' hT e.1 e.2]
    -- now: (∑' opt, W opt) * (∑' opt, normalize(W) opt * K opt) = ∑' opt, W opt * K opt
    -- where K opt = (drawWit opt).next none
    simp only [PMF.normalize_apply]
    rw [ProbabilisticExecution.normalize_cancel _
        (Scheduler.drawAndRunW_tsum_ne_top pe' E'' hT e.1) _ h0]
    -- ∑' opt, W opt * (drawWit opt).next none = ∑' opt, prior·probOf(e)·(drawWit opt).next none
    refine tsum_congr (fun opt => ?_)
    rw [Scheduler.drawAndRunW_eq pe' E'' hT e.1 e.2 opt, mul_assoc]
  · -- vanishing normaliser: drawZ e = 0, so probOf e = 0 and every prior·(drawWit).probOf e = 0
    push Not at h0
    have hZ0 : Scheduler.drawZ pe' E'' hT e.1 e.2 = 0 := by
      rw [Scheduler.drawZ_eq_tsum_drawAndRunW pe' E'' hT e.1 e.2]; exact h0
    rw [hZ0, zero_mul]
    -- RHS: every term `prior·(drawWit).haltMass e = prior·probOf(e)·(drawWit).next none = 0`
    have hz : ∀ opt, pe'.scheduler.next E'' opt *
        (⟨PMF.pure (E''.endState hT), Scheduler.drawWit sys (E''.endState hT) opt⟩
          : ProbabilisticExecution sys.toSystem).probOf e.1 e.2 = 0 :=
      ENNReal.tsum_eq_zero.mp hZ0
    refine (ENNReal.tsum_eq_zero.mpr (fun opt => ?_)).symm
    change pe'.scheduler.next E'' opt *
        ((⟨PMF.pure (E''.endState hT), Scheduler.drawWit sys (E''.endState hT) opt⟩
          : ProbabilisticExecution sys.toSystem).probOf e.1 e.2
            * (Scheduler.drawWit sys (E''.endState hT) opt).next e.1 none) = 0
    rw [← mul_assoc, hz opt, zero_mul]

/-- **PIECE A: pushforward (`haltMass`-integral) form of the keystone, for `drawAndRun`.**
Integrating a test `g` against the halting end-state of `drawAndRun` (from the Dirac source
`pure (E''.endState hT)`) equals the prior-weighted sum over ALL options `opt` of the committed
witnesses' pushforwards. This is the **unfiltered** marginal (no trace indicator, summed over
every `opt`); it is proven cleanly from the posterior-telescoping keystone
`drawAndRun_probOf_eq` — the current posterior-conditioned `drawAndRun` (the 7th-flaw fix) is a
`PMF.normalize`-bind that DEPENDS on the running prefix, so the constant-mixture OBSTACLE flagged
for the old `Scheduler.drawAndRun_pushforward` (Lemma B2, below) does not arise here. Obtained
from the per-execution halt-mass marginal `drawAndRun_haltMass_marginal` by `∑'_e` and swapping
the order of summation (`ENNReal.tsum_comm`). -/
theorem Scheduler.drawAndRun_pushforward_all {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E'' : AlterSeq State Label)
    (hT : E''.trans.Terminates) (g : State → ENNReal) :
    (∑' e, (Scheduler.drawAndRun pe' E'').haltMass (PMF.pure (E''.endState hT)) e
        * g (e.1.endState e.2))
      = ∑' opt : Option (Label × PMF State), pe'.scheduler.next E'' opt
          * (∑' e, (Scheduler.drawWit sys (E''.endState hT) opt).haltMass
              (PMF.pure (E''.endState hT)) e * g (e.1.endState e.2)) := by
  classical
  -- rewrite each summand via the per-execution halt-mass marginal, distributing `g`
  have hterm : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      (Scheduler.drawAndRun pe' E'').haltMass (PMF.pure (E''.endState hT)) e
          * g (e.1.endState e.2)
        = ∑' opt : Option (Label × PMF State), pe'.scheduler.next E'' opt
            * ((Scheduler.drawWit sys (E''.endState hT) opt).haltMass
                (PMF.pure (E''.endState hT)) e * g (e.1.endState e.2)) := by
    intro e
    by_cases hinit : e.1.init = E''.endState hT
    · rw [Scheduler.drawAndRun_haltMass_marginal pe' E'' hT e hinit, ← ENNReal.tsum_mul_right]
      exact tsum_congr (fun opt => by rw [mul_assoc])
    · -- off-boundary `e`: both `drawAndRun` and every `drawWit` halt mass vanish (Dirac source)
      have hlhs : (Scheduler.drawAndRun pe' E'').haltMass (PMF.pure (E''.endState hT)) e = 0 := by
        unfold Scheduler.haltMass
        rw [ProbabilisticExecution.probOf_init_factor _ (PMF.pure (E''.endState hT)) e.1 e.2,
          PMF.pure_apply_of_ne _ _ hinit, zero_mul, zero_mul]
      rw [hlhs, zero_mul]
      refine (ENNReal.tsum_eq_zero.mpr (fun opt => ?_)).symm
      have hwit : (Scheduler.drawWit sys (E''.endState hT) opt).haltMass
          (PMF.pure (E''.endState hT)) e = 0 := by
        unfold Scheduler.haltMass
        rw [ProbabilisticExecution.probOf_init_factor _ (PMF.pure (E''.endState hT)) e.1 e.2,
          PMF.pure_apply_of_ne _ _ hinit, zero_mul, zero_mul]
      rw [hwit, zero_mul, mul_zero]
  rw [tsum_congr hterm, ENNReal.tsum_comm]
  exact tsum_congr (fun opt => ENNReal.tsum_mul_left)

open Classical in
/-- **Unnormalised weight of the POSTERIOR post-τ `μ`-draw** (the post-τ analogue of
`drawAndRunW`). For a clean prior `pe'`-history `E'` (terminating, with `hT`), an external
label `l` of the just-completed weak step, and the running *post-τ* `sys`-history `h` (whose
boundary `h.init` is the hyperStep target `ν'`), the prior `pe'.scheduler.next E' (some (l, μ))`
(the mass `pe'` assigns to result `μ` for this step) is reweighted by the *likelihood* of `h`
under the candidate post-τ closure `postTauWitness sys (E'.endState hT) l μ`, run from the
Dirac source `PMF.pure h.init`: candidate `μ`'s whose post-τ witness *cannot* produce the
observed trajectory `h` get likelihood `0` and drop out. This conditions the `μ`-draw on the
post-τ trajectory, fixing the post-τ analogue of the 7th flaw (the `beliefExpand` `μ`-draw was
conditioned only on the boundary `ν'`, not the replayed post-τ). -/
noncomputable def Scheduler.postTauDrawW {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (h : AlterSeq State Label) :
    PMF State → ENNReal := fun μ =>
  pe'.scheduler.next E' (some (l, μ)) *
    (if hh : h.trans.Terminates then
       (⟨PMF.pure h.init, Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
          : ProbabilisticExecution sys.toSystem).probOf h hh
     else 0)

/-- **Finiteness of the post-τ posterior normaliser** (mirrors `drawAndRunW_tsum_ne_top`).
Each likelihood factor is a `probOf ≤ pe.init ≤ 1`, so `∑' μ, postTauDrawW … μ ≤ ∑' μ,
pe'.scheduler.next E' (some (l, μ)) ≤ ∑' opt, pe'.scheduler.next E' opt = 1 ≠ ⊤` (the
`(l,·)`-fiber sub-sum of the PMF `pe'.next E'` is `≤ 1` via `tsum_comp_le_tsum_of_injective`
+ `tsum_coe`, as in `beliefExpandW_tsum_ne_top`). -/
theorem Scheduler.postTauDrawW_tsum_ne_top {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (h : AlterSeq State Label) :
    (∑' μ, Scheduler.postTauDrawW pe' E' hT l h μ) ≠ ⊤ := by
  classical
  suffices hle : (∑' μ, Scheduler.postTauDrawW pe' E' hT l h μ) ≤ 1 from
    (lt_of_le_of_lt hle ENNReal.one_lt_top).ne
  calc (∑' μ, Scheduler.postTauDrawW pe' E' hT l h μ)
      ≤ ∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ)) := by
        refine ENNReal.tsum_le_tsum (fun μ => ?_)
        unfold Scheduler.postTauDrawW
        refine mul_le_of_le_one_right' ?_
        split
        · exact le_trans (ProbabilisticExecution.probOf_le_init _ _ _) (PMF.coe_le_one _ _)
        · exact zero_le_one
    _ ≤ ∑' opt, pe'.scheduler.next E' opt :=
        ENNReal.tsum_comp_le_tsum_of_injective (f := fun μ : PMF State => some (l, μ))
          (fun _ _ h => (Prod.mk.inj (Option.some.inj h)).2) _
    _ = 1 := (pe'.scheduler.next E').tsum_coe

open Classical in
/-- **Draw the just-completed step's result `μ` (POSTERIOR-conditioned) and run its post-τ.**
The post-τ analogue of `drawAndRun`: at a concrete post-τ boundary history `h` (boundary
`h.init = ν'`), reweight the prior `pe'.scheduler.next E' (some (l, ·))` by the likelihood of
the running post-τ history `h` (see `postTauDrawW`) and *normalise* — conditioning the `μ`-draw
on the post-τ trajectory so off-path `μ`'s drop out (the post-τ 7th-flaw fix). On a drawn `μ`,
run `postTauWitness sys (E'.endState hT) l μ` at `h`. If the normaliser vanishes (no `μ`
explains `h`) or `E'` does not terminate, halt. -/
noncomputable def Scheduler.postTauDraw {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label) (l : Label) :
    Scheduler sys.toSystem where
  next h :=
    if hT : E'.trans.Terminates then
      if h0 : (∑' μ, Scheduler.postTauDrawW pe' E' hT l h μ) ≠ 0 then
        (PMF.normalize (Scheduler.postTauDrawW pe' E' hT l h) h0
            (Scheduler.postTauDrawW_tsum_ne_top pe' E' hT l h)).bind (fun μ =>
          (Scheduler.postTauWitness sys (E'.endState hT) l μ).next h)
      else PMF.pure none
    else PMF.pure none
  valid := by
    classical
    intro e n s' e_term_n e_stateAt_eq l' μ h_supp
    change some (l', μ) ∈
      (if hT : E'.trans.Terminates then
        if h0 : (∑' μ, Scheduler.postTauDrawW pe' E' hT l e μ) ≠ 0 then
          (PMF.normalize (Scheduler.postTauDrawW pe' E' hT l e) h0
              (Scheduler.postTauDrawW_tsum_ne_top pe' E' hT l e)).bind (fun μ =>
            (Scheduler.postTauWitness sys (E'.endState hT) l μ).next e)
        else PMF.pure none
      else PMF.pure none).support at h_supp
    by_cases hT : E'.trans.Terminates
    · rw [dif_pos hT] at h_supp
      by_cases h0 : (∑' μ, Scheduler.postTauDrawW pe' E' hT l e μ) ≠ 0
      · rw [dif_pos h0, PMF.mem_support_bind_iff] at h_supp
        obtain ⟨μ₀, _hμ₀, h_supp⟩ := h_supp
        exact (Scheduler.postTauWitness sys (E'.endState hT) l μ₀).valid
          e n s' e_term_n e_stateAt_eq l' μ h_supp
      · rw [dif_neg h0, PMF.support_pure, Set.mem_singleton_iff] at h_supp
        exact absurd h_supp (by simp)
    · rw [dif_neg hT, PMF.support_pure, Set.mem_singleton_iff] at h_supp
      exact absurd h_supp (by simp)

/-! ### PIECE B: the `postTauDraw` filter-marginal

The post-τ analogue of the keystone. Unlike `drawAndRun`, the prior of `postTauDraw` is the
`(l,·)`-FIBER `pe'.next E' (some (l, ·))` of the PMF `pe'.next E'`, NOT a full PMF, so the base
marginal `Z₀ = ∑' μ, pe'.next E' (some (l, μ))` need not be `1`. We therefore prove the
filter-marginal in MULTIPLIED (division-free) form `Z₀ * probOf e = postTauZ e`. The
machinery mirrors `drawZ`/`drawZ_step`/`drawZ_nil`/`drawAndRun_probOf_eq_drawZ_ofList`. -/

open Classical in
/-- **`postTauDrawW` as `prior · witness probOf`.** For a running history `e'` with boundary
`e'.init = ν'` (the source `postTauDraw` is run from), the unnormalised weight `postTauDrawW`
equals `pe'.next E' (some (l, μ)) · (⟨pure ν', postTauWitness …⟩).probOf e'` (analogue of
`drawAndRunW_eq`). -/
theorem Scheduler.postTauDrawW_eq {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (ν' : State) (e' : AlterSeq State Label)
    (he' : e'.trans.Terminates) (he'_init : e'.init = ν') (μ : PMF State) :
    Scheduler.postTauDrawW pe' E' hT l e' μ
      = pe'.scheduler.next E' (some (l, μ)) *
          (⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
            : ProbabilisticExecution sys.toSystem).probOf e' he' := by
  classical
  unfold Scheduler.postTauDrawW
  rw [dif_pos he']
  congr 2
  rw [he'_init]

open Classical in
/-- **The `some (l, μ)`-emission of `postTauDraw` as a posterior average** (analogue of
`drawAndRun_next_some`). When the posterior normaliser does not vanish, the emission is the
posterior-weighted sum of the per-`μ` post-τ witnesses' emissions. -/
theorem Scheduler.postTauDraw_next_some {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (e' : AlterSeq State Label)
    (h0 : (∑' μ, Scheduler.postTauDrawW pe' E' hT l e' μ) ≠ 0) (l₁ : Label) (μ₁ : PMF State) :
    (Scheduler.postTauDraw pe' E' l).next e' (some (l₁, μ₁))
      = ∑' μ, (PMF.normalize (Scheduler.postTauDrawW pe' E' hT l e') h0
            (Scheduler.postTauDrawW_tsum_ne_top pe' E' hT l e')) μ *
          (Scheduler.postTauWitness sys (E'.endState hT) l μ).next e' (some (l₁, μ₁)) := by
  classical
  change (if hT' : E'.trans.Terminates then
      if h0' : (∑' μ, Scheduler.postTauDrawW pe' E' hT' l e' μ) ≠ 0 then
        (PMF.normalize (Scheduler.postTauDrawW pe' E' hT' l e') h0'
            (Scheduler.postTauDrawW_tsum_ne_top pe' E' hT' l e')).bind (fun μ =>
          (Scheduler.postTauWitness sys (E'.endState hT') l μ).next e')
      else PMF.pure none
    else PMF.pure none) (some (l₁, μ₁)) = _
  rw [dif_pos hT, dif_pos h0, PMF.bind_apply]

open Classical in
/-- **The `none`-emission of `postTauDraw` as a posterior average** (analogue of
`drawAndRun_next_none`). -/
theorem Scheduler.postTauDraw_next_none {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (e' : AlterSeq State Label)
    (h0 : (∑' μ, Scheduler.postTauDrawW pe' E' hT l e' μ) ≠ 0) :
    (Scheduler.postTauDraw pe' E' l).next e' none
      = ∑' μ, (PMF.normalize (Scheduler.postTauDrawW pe' E' hT l e') h0
            (Scheduler.postTauDrawW_tsum_ne_top pe' E' hT l e')) μ *
          (Scheduler.postTauWitness sys (E'.endState hT) l μ).next e' none := by
  classical
  change (if hT' : E'.trans.Terminates then
      if h0' : (∑' μ, Scheduler.postTauDrawW pe' E' hT' l e' μ) ≠ 0 then
        (PMF.normalize (Scheduler.postTauDrawW pe' E' hT' l e') h0'
            (Scheduler.postTauDrawW_tsum_ne_top pe' E' hT' l e')).bind (fun μ =>
          (Scheduler.postTauWitness sys (E'.endState hT') l μ).next e')
      else PMF.pure none
    else PMF.pure none) none = _
  rw [dif_pos hT, dif_pos h0, PMF.bind_apply]

/-- The **post-τ posterior marginal** `postTauZ e'` at a running history `e'` (with boundary
`ν'`): the prior-weighted sum of the per-`μ` post-τ witnesses' `probOf` (the RHS of the
filter-marginal). The post-τ analogue of `drawZ`; here the prior is the `(l,·)`-fiber. -/
noncomputable def Scheduler.postTauZ {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (ν' : State) (e' : AlterSeq State Label)
    (he' : e'.trans.Terminates) : ENNReal :=
  ∑' μ : PMF State,
    pe'.scheduler.next E' (some (l, μ)) *
      (⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
        : ProbabilisticExecution sys.toSystem).probOf e' he'

/-- `postTauZ` depends only on the running history, not the termination proof. -/
theorem Scheduler.postTauZ_congr {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (ν' : State) (e e' : AlterSeq State Label)
    (h_eq : e = e') (he : e.trans.Terminates) (he' : e'.trans.Terminates) :
    Scheduler.postTauZ pe' E' hT l ν' e he = Scheduler.postTauZ pe' E' hT l ν' e' he' := by
  subst h_eq; rfl

/-- `postTauZ` at a boundary-`ν'` history is exactly the posterior normaliser
`∑' μ, postTauDrawW … μ`. -/
theorem Scheduler.postTauZ_eq_tsum_postTauDrawW {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (ν' : State) (e' : AlterSeq State Label)
    (he' : e'.trans.Terminates) (he'_init : e'.init = ν') :
    Scheduler.postTauZ pe' E' hT l ν' e' he'
      = ∑' μ, Scheduler.postTauDrawW pe' E' hT l e' μ := by
  unfold Scheduler.postTauZ
  exact (tsum_congr (fun μ =>
    (Scheduler.postTauDrawW_eq pe' E' hT l ν' e' he' he'_init μ).symm))

/-- **One-step kernel of `postTauDraw` as a posterior average** (analogue of
`drawAndRun_kernel_eq`). -/
theorem Scheduler.postTauDraw_kernel_eq {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (ν' : State) (e' : AlterSeq State Label)
    (h0 : (∑' μ, Scheduler.postTauDrawW pe' E' hT l e' μ) ≠ 0) (p : Label × State) :
    (⟨PMF.pure ν', Scheduler.postTauDraw pe' E' l⟩
        : ProbabilisticExecution sys.toSystem).kernel e' p
      = ∑' μ, (PMF.normalize (Scheduler.postTauDrawW pe' E' hT l e') h0
            (Scheduler.postTauDrawW_tsum_ne_top pe' E' hT l e')) μ *
          (⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
            : ProbabilisticExecution sys.toSystem).kernel e' p := by
  classical
  obtain ⟨l₁, s'⟩ := p
  unfold ProbabilisticExecution.kernel
  have hexp : ∀ μ₁ : PMF State,
      (⟨PMF.pure ν', Scheduler.postTauDraw pe' E' l⟩
          : ProbabilisticExecution sys.toSystem).scheduler.next e' (some (l₁, μ₁)) * μ₁ s'
        = ∑' μ, (PMF.normalize (Scheduler.postTauDrawW pe' E' hT l e') h0
              (Scheduler.postTauDrawW_tsum_ne_top pe' E' hT l e')) μ *
            ((Scheduler.postTauWitness sys (E'.endState hT) l μ).next e' (some (l₁, μ₁))
              * μ₁ s') := by
    intro μ₁
    rw [show (⟨PMF.pure ν', Scheduler.postTauDraw pe' E' l⟩
            : ProbabilisticExecution sys.toSystem).scheduler.next e' (some (l₁, μ₁))
          = (Scheduler.postTauDraw pe' E' l).next e' (some (l₁, μ₁)) from rfl,
      Scheduler.postTauDraw_next_some pe' E' hT l e' h0 l₁ μ₁, ← ENNReal.tsum_mul_right]
    refine tsum_congr (fun μ => ?_); rw [mul_assoc]
  rw [tsum_congr hexp, ENNReal.tsum_comm]
  refine tsum_congr (fun μ => ?_)
  rw [ENNReal.tsum_mul_left]

/-- **Telescoping step (multiplicative kernel-ratio) for `postTauZ`** (analogue of
`drawZ_step`). -/
theorem Scheduler.postTauZ_step {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (ν' : State) (sq : Seq (Label × State))
    (h_sq : sq.Terminates) (last : Label × State)
    (h_app : (sq.append (Seq.cons last Seq.nil)).Terminates) :
    Scheduler.postTauZ pe' E' hT l ν' ⟨ν', sq.append (Seq.cons last Seq.nil)⟩ h_app
      = Scheduler.postTauZ pe' E' hT l ν' ⟨ν', sq⟩ h_sq
        * (⟨PMF.pure ν', Scheduler.postTauDraw pe' E' l⟩
            : ProbabilisticExecution sys.toSystem).kernel ⟨ν', sq⟩ last := by
  classical
  set e' : AlterSeq State Label := ⟨ν', sq⟩ with he'_def
  set e'' : AlterSeq State Label := ⟨ν', sq.append (Seq.cons last Seq.nil)⟩ with he''_def
  have he'_init : e'.init = ν' := rfl
  -- each witness `probOf` telescopes: probOf(e'') = probOf(e') * kernel
  have htel : ∀ μ : PMF State,
      (⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
          : ProbabilisticExecution sys.toSystem).probOf e'' h_app
        = (⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
            : ProbabilisticExecution sys.toSystem).probOf e' h_sq
          * (⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
              : ProbabilisticExecution sys.toSystem).kernel e' last := by
    intro μ
    exact (ProbabilisticExecution.probOf_append_singleton _ ν' sq h_sq last h_app)
  by_cases h0 : Scheduler.postTauZ pe' E' hT l ν' e' h_sq = 0
  · rw [h0, zero_mul]
    have hz : ∀ μ, pe'.scheduler.next E' (some (l, μ)) *
        (⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
          : ProbabilisticExecution sys.toSystem).probOf e' h_sq = 0 :=
      ENNReal.tsum_eq_zero.mp h0
    unfold Scheduler.postTauZ
    refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
    rw [htel μ, ← mul_assoc, hz μ, zero_mul]
  · have h0' : (∑' μ, Scheduler.postTauDrawW pe' E' hT l e' μ) ≠ 0 := by
      rwa [← Scheduler.postTauZ_eq_tsum_postTauDrawW pe' E' hT l ν' e' h_sq he'_init]
    rw [Scheduler.postTauDraw_kernel_eq pe' E' hT l ν' e' h0' last]
    rw [show Scheduler.postTauZ pe' E' hT l ν' e' h_sq
          = ∑' μ, Scheduler.postTauDrawW pe' E' hT l e' μ
        from Scheduler.postTauZ_eq_tsum_postTauDrawW pe' E' hT l ν' e' h_sq he'_init]
    simp only [PMF.normalize_apply]
    rw [ProbabilisticExecution.normalize_cancel _
        (Scheduler.postTauDrawW_tsum_ne_top pe' E' hT l e') _ h0']
    unfold Scheduler.postTauZ
    refine tsum_congr (fun μ => ?_)
    rw [Scheduler.postTauDrawW_eq pe' E' hT l ν' e' h_sq he'_init μ, htel μ, mul_assoc]

/-- **Base value `Z₀` for `postTauZ`** (analogue of `drawZ_nil`, but NOT `1`). At the empty
history `⟨ν', nil⟩`, every post-τ witness realizes the empty execution with mass `1` (Dirac
source `pure ν'`), so the marginal collapses to the FIBER mass `∑' μ, pe'.next E' (some (l, μ))`
— the prior here is a fiber, not a full PMF. -/
theorem Scheduler.postTauZ_nil {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (ν' : State) :
    Scheduler.postTauZ pe' E' hT l ν' ⟨ν', Stream'.Seq.nil⟩ Stream'.Seq.terminates_nil
      = ∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ)) := by
  unfold Scheduler.postTauZ
  refine tsum_congr (fun μ => ?_)
  rw [ProbabilisticExecution.probOf_nil]
  change pe'.scheduler.next E' (some (l, μ)) * (PMF.pure ν') ν' = _
  rw [PMF.pure_apply_self, mul_one]

/-- **Telescoping over `ofList`** (analogue of `drawAndRun_probOf_eq_drawZ_ofList`): the
MULTIPLIED filter-marginal `Z₀ · probOf e = postTauZ e` for histories of the form
`⟨ν', ofList trans⟩`, by reverse induction. Base = `postTauZ_nil` (= `Z₀`, and `probOf nil = 1`);
step = `probOf_append_singleton` + IH + `postTauZ_step`. -/
theorem Scheduler.postTauDraw_probOf_eq_postTauZ_ofList {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (ν' : State) (trans : List (Label × State))
    (hFin : (Seq.ofList trans : Seq (Label × State)).Terminates) :
    Scheduler.postTauZ pe' E' hT l ν' ⟨ν', Stream'.Seq.nil⟩ Stream'.Seq.terminates_nil
        * (⟨PMF.pure ν', Scheduler.postTauDraw pe' E' l⟩
            : ProbabilisticExecution sys.toSystem).probOf ⟨ν', Seq.ofList trans⟩ hFin
      = Scheduler.postTauZ pe' E' hT l ν' ⟨ν', Seq.ofList trans⟩ hFin := by
  classical
  induction trans using List.reverseRecOn with
  | nil =>
    have hnil : (⟨ν', Seq.ofList []⟩ : AlterSeq State Label)
        = ⟨ν', Stream'.Seq.nil⟩ := by simp [Stream'.Seq.ofList_nil]
    rw [ProbabilisticExecution.probOf_congr _ ⟨ν', Seq.ofList []⟩
        ⟨ν', Stream'.Seq.nil⟩ hnil hFin Stream'.Seq.terminates_nil,
      ProbabilisticExecution.probOf_nil,
      Scheduler.postTauZ_congr pe' E' hT l ν' ⟨ν', Seq.ofList []⟩
        ⟨ν', Stream'.Seq.nil⟩ hnil hFin Stream'.Seq.terminates_nil]
    change Scheduler.postTauZ pe' E' hT l ν' ⟨ν', Stream'.Seq.nil⟩ Stream'.Seq.terminates_nil
        * (PMF.pure ν') ν' = _
    rw [PMF.pure_apply_self, mul_one]
  | append_singleton rest last ih =>
    have hrest_term : (Seq.ofList rest : Seq (Label × State)).Terminates :=
      Stream'.Seq.terminates_ofList rest
    have hsplit : (Seq.ofList (rest ++ [last]) : Seq (Label × State))
        = (Seq.ofList rest).append (Seq.cons last Seq.nil) := by
      rw [Stream'.Seq.ofList_append]
      congr 1
      rw [Stream'.Seq.ofList_cons]
      simp [Stream'.Seq.ofList_nil]
    have happ_term : ((Seq.ofList rest).append (Seq.cons last Seq.nil)
        : Seq (Label × State)).Terminates := by rw [← hsplit]; exact hFin
    have heq_ext : (⟨ν', Seq.ofList (rest ++ [last])⟩ : AlterSeq State Label)
        = ⟨ν', (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩ := by rw [hsplit]
    rw [ProbabilisticExecution.probOf_congr _
        ⟨ν', Seq.ofList (rest ++ [last])⟩
        ⟨ν', (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩
        heq_ext hFin happ_term,
      ProbabilisticExecution.probOf_append_singleton _ ν' (Seq.ofList rest)
        hrest_term last happ_term,
      ← mul_assoc, ih hrest_term,
      ← Scheduler.postTauZ_step pe' E' hT l ν' (Seq.ofList rest) hrest_term last happ_term]
    exact Scheduler.postTauZ_congr pe' E' hT l ν'
      ⟨ν', (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩
      ⟨ν', Seq.ofList (rest ++ [last])⟩ heq_ext.symm happ_term hFin

/-- **PIECE B (probOf form): the post-τ filter-marginal, MULTIPLIED form.** The fiber mass
`Z₀ = ∑' μ, pe'.next E' (some (l, μ))` times `postTauDraw.probOf e` (from `pure ν'`) equals the
prior-weighted sum of the per-`μ` post-τ witnesses' `probOf`. Division-free (the base normaliser
`Z₀` need not be `1`). -/
theorem Scheduler.postTauDraw_probOf_eq {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (ν' : State)
    (e : AlterSeq State Label) (he : e.trans.Terminates) (he_init : e.init = ν') :
    (∑' μ, pe'.scheduler.next E' (some (l, μ))) *
      (⟨PMF.pure ν', Scheduler.postTauDraw pe' E' l⟩
        : ProbabilisticExecution sys.toSystem).probOf e he
      = ∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ))
          * (⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
              : ProbabilisticExecution sys.toSystem).probOf e he := by
  classical
  -- rewrite `e` to `⟨ν', ofList (toList)⟩`, invoke the telescoping aux
  have he_ofList : e = ⟨ν', Seq.ofList (e.trans.toList he)⟩ := by
    obtain ⟨ei, et⟩ := e
    simp only at he_init
    subst he_init
    congr 1
    exact (Stream'.Seq.ofList_toList et he).symm
  have hFin' : (Seq.ofList (e.trans.toList he) : Seq (Label × State)).Terminates :=
    Stream'.Seq.terminates_ofList _
  -- Z₀ as `postTauZ_nil`
  rw [show (∑' μ, pe'.scheduler.next E' (some (l, μ)))
        = Scheduler.postTauZ pe' E' hT l ν' ⟨ν', Stream'.Seq.nil⟩ Stream'.Seq.terminates_nil
      from (Scheduler.postTauZ_nil pe' E' hT l ν').symm,
    ProbabilisticExecution.probOf_congr _ e
      ⟨ν', Seq.ofList (e.trans.toList he)⟩ he_ofList he hFin',
    Scheduler.postTauDraw_probOf_eq_postTauZ_ofList pe' E' hT l ν' (e.trans.toList he) hFin']
  -- the RHS sum is `postTauZ e he` after the same `probOf_congr`
  unfold Scheduler.postTauZ
  refine tsum_congr (fun μ => ?_)
  rw [ProbabilisticExecution.probOf_congr _ e
      ⟨ν', Seq.ofList (e.trans.toList he)⟩ he_ofList he hFin']

/-- **Per-execution halt-mass marginal of `postTauDraw`, MULTIPLIED form** (the `haltMass`
analogue of `postTauDraw_probOf_eq`). `Z₀ · postTauDraw.haltMass e = ∑' μ, pe'.next E' (some
(l, μ)) · (postTauWitness … μ).haltMass e`. Proven by multiplying the multiplied probOf
marginal by the `none`-emission posterior average; the `postTauZ e` normaliser cancels. -/
theorem Scheduler.postTauDraw_haltMass_marginal {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (ν' : State)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) (he_init : e.1.init = ν') :
    (∑' μ, pe'.scheduler.next E' (some (l, μ))) *
        (Scheduler.postTauDraw pe' E' l).haltMass (PMF.pure ν') e
      = ∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ))
          * (Scheduler.postTauWitness sys (E'.endState hT) l μ).haltMass (PMF.pure ν') e := by
  classical
  unfold Scheduler.haltMass
  by_cases h0 : (∑' μ, Scheduler.postTauDrawW pe' E' hT l e.1 μ) ≠ 0
  · -- nonvanishing normaliser: expand `next none`, multiply by the multiplied probOf marginal
    rw [Scheduler.postTauDraw_next_none pe' E' hT l e.1 h0]
    -- LHS = Z₀ · (probOf e · ∑' μ, normalize(W) μ · (postTauWit μ).next none)
    -- regroup: (Z₀ · probOf e) · (∑' μ, normalize(W) μ · K μ) = postTauZ e · (…)
    rw [show (∑' μ, pe'.scheduler.next E' (some (l, μ))) *
            ((⟨PMF.pure ν', Scheduler.postTauDraw pe' E' l⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2
              * ∑' μ, (PMF.normalize (Scheduler.postTauDrawW pe' E' hT l e.1) h0
                  (Scheduler.postTauDrawW_tsum_ne_top pe' E' hT l e.1)) μ *
                (Scheduler.postTauWitness sys (E'.endState hT) l μ).next e.1 none)
          = ((∑' μ, pe'.scheduler.next E' (some (l, μ))) *
              (⟨PMF.pure ν', Scheduler.postTauDraw pe' E' l⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2)
            * ∑' μ, (PMF.normalize (Scheduler.postTauDrawW pe' E' hT l e.1) h0
                  (Scheduler.postTauDrawW_tsum_ne_top pe' E' hT l e.1)) μ *
                (Scheduler.postTauWitness sys (E'.endState hT) l μ).next e.1 none by ring,
      Scheduler.postTauDraw_probOf_eq pe' E' hT l ν' e.1 e.2 he_init]
    -- now postTauZ e = ∑' μ, W μ ; recognise the multiplied form and cancel
    rw [show (∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ))
            * (⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2)
          = ∑' μ, Scheduler.postTauDrawW pe' E' hT l e.1 μ from
        tsum_congr (fun μ =>
          (Scheduler.postTauDrawW_eq pe' E' hT l ν' e.1 e.2 he_init μ).symm)]
    simp only [PMF.normalize_apply]
    rw [ProbabilisticExecution.normalize_cancel _
        (Scheduler.postTauDrawW_tsum_ne_top pe' E' hT l e.1) _ h0]
    refine tsum_congr (fun μ => ?_)
    rw [Scheduler.postTauDrawW_eq pe' E' hT l ν' e.1 e.2 he_init μ, mul_assoc]
  · -- vanishing normaliser: postTauZ e = 0 ⟹ probOf e = 0 and every prior·probOf(e) = 0
    push Not at h0
    have hZ0 : Scheduler.postTauZ pe' E' hT l ν' e.1 e.2 = 0 := by
      rw [Scheduler.postTauZ_eq_tsum_postTauDrawW pe' E' hT l ν' e.1 e.2 he_init]; exact h0
    -- LHS: `Z₀ · probOf e · next none`; `Z₀ · probOf e = postTauZ e = 0`
    rw [show (∑' μ, pe'.scheduler.next E' (some (l, μ))) *
            ((⟨PMF.pure ν', Scheduler.postTauDraw pe' E' l⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2
              * (Scheduler.postTauDraw pe' E' l).next e.1 none)
          = ((∑' μ, pe'.scheduler.next E' (some (l, μ))) *
              (⟨PMF.pure ν', Scheduler.postTauDraw pe' E' l⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2)
            * (Scheduler.postTauDraw pe' E' l).next e.1 none by ring,
      Scheduler.postTauDraw_probOf_eq pe' E' hT l ν' e.1 e.2 he_init,
      show (∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ))
            * (⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2)
          = Scheduler.postTauZ pe' E' hT l ν' e.1 e.2 from rfl,
      hZ0, zero_mul]
    -- RHS: every term `prior·(postTauWit μ).haltMass e = prior·probOf(e)·next none = 0`
    have hz : ∀ μ, pe'.scheduler.next E' (some (l, μ)) *
        (⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
          : ProbabilisticExecution sys.toSystem).probOf e.1 e.2 = 0 :=
      ENNReal.tsum_eq_zero.mp hZ0
    refine (ENNReal.tsum_eq_zero.mpr (fun μ => ?_)).symm
    change pe'.scheduler.next E' (some (l, μ)) *
        ((⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
          : ProbabilisticExecution sys.toSystem).probOf e.1 e.2
            * (Scheduler.postTauWitness sys (E'.endState hT) l μ).next e.1 none) = 0
    rw [← mul_assoc, hz μ, zero_mul]

/-- **PIECE B (pushforward form): the post-τ filter-marginal `g`-integral, MULTIPLIED form.**
`Z₀ · postTauDraw.pushforward g = ∑' μ, pe'.next E' (some (l, μ)) · (postTauWitness … μ).pushforward
g`, where `Z₀ = ∑' μ, pe'.next E' (some (l, μ))` is the fiber mass. Obtained from
`postTauDraw_haltMass_marginal` by `∑'_e` + `ENNReal.tsum_comm`. -/
theorem Scheduler.postTauDraw_pushforward {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (ν' : State) (g : State → ENNReal) :
    (∑' μ, pe'.scheduler.next E' (some (l, μ))) *
        (∑' e, (Scheduler.postTauDraw pe' E' l).haltMass (PMF.pure ν') e * g (e.1.endState e.2))
      = ∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ))
          * (∑' e, (Scheduler.postTauWitness sys (E'.endState hT) l μ).haltMass
              (PMF.pure ν') e * g (e.1.endState e.2)) := by
  classical
  rw [← ENNReal.tsum_mul_left]
  have hterm : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      (∑' μ, pe'.scheduler.next E' (some (l, μ))) *
          ((Scheduler.postTauDraw pe' E' l).haltMass (PMF.pure ν') e * g (e.1.endState e.2))
        = ∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ))
            * ((Scheduler.postTauWitness sys (E'.endState hT) l μ).haltMass
                (PMF.pure ν') e * g (e.1.endState e.2)) := by
    intro e
    by_cases hinit : e.1.init = ν'
    · rw [show (∑' μ, pe'.scheduler.next E' (some (l, μ))) *
              ((Scheduler.postTauDraw pe' E' l).haltMass (PMF.pure ν') e * g (e.1.endState e.2))
            = ((∑' μ, pe'.scheduler.next E' (some (l, μ))) *
                (Scheduler.postTauDraw pe' E' l).haltMass (PMF.pure ν') e) * g (e.1.endState e.2)
            by ring,
        Scheduler.postTauDraw_haltMass_marginal pe' E' hT l ν' e hinit, ← ENNReal.tsum_mul_right]
      exact tsum_congr (fun μ => by rw [mul_assoc])
    · -- off-boundary `e`: both halt masses vanish (Dirac source `pure ν'`)
      have hlhs : (Scheduler.postTauDraw pe' E' l).haltMass (PMF.pure ν') e = 0 := by
        unfold Scheduler.haltMass
        rw [ProbabilisticExecution.probOf_init_factor _ (PMF.pure ν') e.1 e.2,
          PMF.pure_apply_of_ne _ _ hinit, zero_mul, zero_mul]
      rw [hlhs, zero_mul, mul_zero]
      refine (ENNReal.tsum_eq_zero.mpr (fun μ => ?_)).symm
      have hwit : (Scheduler.postTauWitness sys (E'.endState hT) l μ).haltMass
          (PMF.pure ν') e = 0 := by
        unfold Scheduler.haltMass
        rw [ProbabilisticExecution.probOf_init_factor _ (PMF.pure ν') e.1 e.2,
          PMF.pure_apply_of_ne _ _ hinit, zero_mul, zero_mul]
      rw [hwit, zero_mul, mul_zero]
  rw [tsum_congr hterm, ENNReal.tsum_comm]
  exact tsum_congr (fun μ => ENNReal.tsum_mul_left)

open Classical in
/-- The **segment** scheduler realizing one expand step from boundary `ν'`, given the
externally-drawn `E'` (clean prior `pe'`-history). First replay the just-completed step's
*post-τ closure* — the post-τ of the full weak step `E'.endState →[l]→ μ` — but now the
result `μ` is **drawn POSTERIOR-conditioned on the post-τ trajectory** via `postTauDraw pe'
E' l` (mirroring the pre-τ `drawAndRun` fix: previously `μ` was taken as a parameter, drawn
by `beliefExpand` conditioned only on the boundary `ν'`, which leaked mass to off-trajectory
post-τ continuations — the post-τ analogue of the 7th flaw). The post-τ run reaches a sample
`σ_k ∼ μ`; thread `σ_k` via `Scheduler.bind` into `drawAndRun pe'` at the CLEAN history
`E' ++ [(l, σ_k)]` (draw the next weak step at the on-path reached state and run its
pre-τ;hs). The `μ` argument is retained (unused for the post-τ) so the trace-equality scaffold
(`beliefExpand`/`beliefExpandW`, `hsLabMass_eq_Z_sum`, …) is unchanged pending its update. -/
noncomputable def Scheduler.segmentScheduler {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (_ν' : State) (l : Label) (E' : AlterSeq State Label) (_μ : PMF State) :
    Scheduler sys.toSystem :=
  if _hT : E'.trans.Terminates then
    Scheduler.bind (Scheduler.postTauDraw pe' E' l)
      (fun σ_k => Scheduler.drawAndRun pe'
        ⟨E'.init, E'.trans.append (Seq.cons (l, σ_k) Seq.nil)⟩)
  else Scheduler.haltNow sys

/-- **The segment's per-`σ` continuation pushforward** (PIECE C's `INNER`). For a reached
post-τ state `σ`, the `g`-pushforward of the next-step draw `drawAndRun pe' (E' ++ [(l, σ)])`
run from `pure σ`, written in its PIECE-A (prior-weighted, committed-witness) form. The
committed witnesses `drawWit sys σ opt` are run from the Dirac source `pure σ` (the reached
on-path state). -/
noncomputable def Scheduler.segContPush {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (l : Label) (E' : AlterSeq State Label)
    (g : State → ENNReal) (σ : State) : ENNReal :=
  ∑' opt : Option (Label × PMF State),
    pe'.scheduler.next ⟨E'.init, E'.trans.append (Seq.cons (l, σ) Seq.nil)⟩ opt
      * (∑' f₂, (Scheduler.drawWit sys σ opt).haltMass (PMF.pure σ) f₂ * g (f₂.1.endState f₂.2))

/-- **`segContPush` is the `drawAndRun` continuation pushforward** (PIECE A, specialised to the
extended clean history `E' ++ [(l, σ)]` whose end-state is `σ`). -/
theorem Scheduler.segContPush_eq {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (l : Label) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (g : State → ENNReal) (σ : State) :
    (∑' f₂, (Scheduler.drawAndRun pe'
          ⟨E'.init, E'.trans.append (Seq.cons (l, σ) Seq.nil)⟩).haltMass
        (PMF.pure σ) f₂ * g (f₂.1.endState f₂.2))
      = Scheduler.segContPush pe' l E' g σ := by
  classical
  set E'' : AlterSeq State Label := ⟨E'.init, E'.trans.append (Seq.cons (l, σ) Seq.nil)⟩ with hE''
  have hT'' : E''.trans.Terminates :=
    ⟨Nat.find hT + 1, Stream'.Seq.terminatedAt_append_find hT
      (show (Seq.cons (l, σ) Seq.nil).TerminatedAt 1 from rfl)⟩
  have hend : E''.endState hT'' = σ :=
    AlterSeq.endState_append_singleton E' hT l σ
  -- PIECE A from source `pure (E''.endState hT'') = pure σ`
  rw [show (PMF.pure σ : PMF State) = PMF.pure (E''.endState hT'') by rw [hend],
    Scheduler.drawAndRun_pushforward_all pe' E'' hT'' g]
  unfold Scheduler.segContPush
  rw [← hE'']
  refine tsum_congr (fun opt => ?_)
  rw [hend]

/-- **PIECE C: segment pushforward (MULTIPLIED form).** Integrating a test `g` against the
halting end-state of `segmentScheduler pe' ν' l E' μ_ig` (run from the Dirac source `pure ν'`),
scaled by the fiber mass `Z₀ = ∑' μ, pe'.next E' (some (l, μ))`, equals the prior-weighted
post-τ-witness pushforward of the per-`σ` continuation `segContPush`. Derivation:
`bind_compose_integrate` (peel the post-τ draw) → PIECE A on the inner draw (`segContPush_eq`)
→ PIECE B (`postTauDraw_pushforward`, multiplied form) to factor the fiber-mass out.

The remaining work for the trace-equality induction (NOT done here): split each `opt` inside
`segContPush` into `some (l', μ')` (→ `hsExpect σ l' μ' g` via `preHsWitness_pushforward`) and
`none` (→ `g σ` via `haltNow_pushforward`) — that split needs `pe'`-validity / `hExt` and
belongs to the outer induction over `ν'`. -/
theorem Scheduler.segment_pushforward {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (ν' : State) (l : Label)
    (E' : AlterSeq State Label) (μ_ig : PMF State) (hT : E'.trans.Terminates)
    (g : State → ENNReal) :
    (∑' μ, pe'.scheduler.next E' (some (l, μ))) *
        (∑' e, (Scheduler.segmentScheduler pe' ν' l E' μ_ig).haltMass (PMF.pure ν') e
            * g (e.1.endState e.2))
      = ∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ))
          * (∑' f₁, (Scheduler.postTauWitness sys (E'.endState hT) l μ).haltMass (PMF.pure ν') f₁
              * Scheduler.segContPush pe' l E' g (f₁.1.endState f₁.2)) := by
  classical
  -- unfold the segment scheduler (the `hT` branch is a `bind`)
  rw [show Scheduler.segmentScheduler pe' ν' l E' μ_ig
        = Scheduler.bind (Scheduler.postTauDraw pe' E' l)
            (fun σ_k => Scheduler.drawAndRun pe'
              ⟨E'.init, E'.trans.append (Seq.cons (l, σ_k) Seq.nil)⟩) by
      unfold Scheduler.segmentScheduler; rw [dif_pos hT]]
  -- Step 1: bind_compose_integrate peels the post-τ draw
  rw [Scheduler.bind_compose_integrate (Scheduler.postTauDraw pe' E' l)
      (fun σ_k => Scheduler.drawAndRun pe'
        ⟨E'.init, E'.trans.append (Seq.cons (l, σ_k) Seq.nil)⟩) (PMF.pure ν') g]
  -- Step 2: PIECE A (segContPush_eq) folds the inner draw at each `f₁.end`
  rw [show (∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
          (Scheduler.postTauDraw pe' E' l).haltMass (PMF.pure ν') f₁ *
            ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
              (Scheduler.drawAndRun pe'
                  ⟨E'.init, E'.trans.append
                    (Seq.cons (l, f₁.1.endState f₁.2) Seq.nil)⟩).haltMass
                (PMF.pure (f₁.1.endState f₁.2)) f₂ * g (f₂.1.endState f₂.2))
        = ∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
            (Scheduler.postTauDraw pe' E' l).haltMass (PMF.pure ν') f₁ *
              Scheduler.segContPush pe' l E' g (f₁.1.endState f₁.2) from
      tsum_congr (fun f₁ => by
        rw [Scheduler.segContPush_eq pe' l E' hT g (f₁.1.endState f₁.2)])]
  -- Step 3: PIECE B (postTauDraw_pushforward, multiplied form) with test `segContPush … g`
  rw [Scheduler.postTauDraw_pushforward pe' E' hT l ν' (Scheduler.segContPush pe' l E' g)]

open Classical in
/-- **The rebuilt expand scheduler** (M2 witness, belief-draw design). At a terminating
`sys`-history `e`: let `ν' := (sys.internalSuffix e).init` (the observable last
external-target boundary) and `L := (sys.trace e).toList` (the external trace so far). On
`L.getLast?`:

* `none` (no external label yet): run `drawAndRun pe' ⟨init, nil⟩` (the empty clean history)
  at `sys.internalSuffix e`; it queries `pe'.next ⟨init, nil⟩` and runs the first weak step's
  pre-τ;hs.
* `some l` (`l` = the just-completed weak step's external label): draw `(E', μ)` from
  `pe'.beliefExpand L ν'` (which weights `μ` by `postDist ν'`, recovering the drawn result),
  and run `segmentScheduler pe' ν' l E' μ` at `sys.internalSuffix e` — replaying the step's
  post-τ to reach `σ_k` and then drawing the next step at the CLEAN history `E' ++ [(l, σ_k)]`.

Validity is free: every branch (`postTauWitness`, `preHsWitness`, `haltNow`,
`Scheduler.bind`, and the belief mixture) is a valid `sys`-scheduler. -/
noncomputable def Scheduler.expand (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) : Scheduler sys.toSystem where
  next e :=
    if hT : e.trans.Terminates then
      let ν' := (sys.internalSuffix e).init
      let L := (sys.trace e).toList
        (Stream'.Seq.terminates_map_iff.mpr (Stream'.Seq.terminates_filter _ _ hT))
      match L.getLast? with
      | none => (Scheduler.drawAndRun pe' ⟨sys.toSystem.init, Seq.nil⟩).next (sys.internalSuffix e)
      | some l =>
          (pe'.beliefExpand L ν').bind (fun p =>
            (Scheduler.segmentScheduler pe' ν' l p.1 p.2).next (sys.internalSuffix e))
    else
      PMF.pure none
  valid := by
    classical
    intro e n s' e_term_n e_stateAt_eq l μ h_supp
    have h_term : e.trans.Terminates := ⟨n, e_term_n⟩
    -- `s' = e.endState` (the `valid` index `n` is terminal), and
    -- `(internalSuffix e).endState = e.endState`, so the inner scheduler's emission at the
    -- suffix's canonical end is a valid step from `s'`.
    have h_find_le : Nat.find h_term ≤ n := Nat.find_le e_term_n
    have h_n_le : n ≤ Nat.find h_term := by
      by_contra h_lt
      push Not at h_lt
      rcases n with _ | m
      · exact absurd h_lt (Nat.not_lt_zero _)
      · have hk_ge : Nat.find h_term ≤ m := Nat.lt_succ_iff.mp h_lt
        have h_term_k : e.trans.TerminatedAt m :=
          Stream'.Seq.terminated_stable e.trans hk_ge (Nat.find_spec h_term)
        have h_state_none : e.stateAt (m + 1) = none := by
          change (e.trans.get? m).map Prod.snd = none
          rw [show e.trans.get? m = none from h_term_k]; rfl
        rw [h_state_none] at e_stateAt_eq
        exact Option.some_ne_none s' e_stateAt_eq.symm
    have h_n_eq : n = Nat.find h_term := le_antisymm h_n_le h_find_le
    have h_s_eq : s' = e.endState h_term := by
      have h := AlterSeq.stateAt_find_eq_endState e h_term
      rw [← h_n_eq] at h; rw [h] at e_stateAt_eq
      exact (Option.some.inj e_stateAt_eq).symm
    set d := sys.internalSuffix e with hd
    have hd_term : d.trans.Terminates := by
      rw [hd, LabelledSystem.internalSuffix, dif_pos h_term]
      exact Stream'.Seq.drop_terminates_pub h_term _
    -- Reduce the `next`-emission at `e` to the inner scheduler's emission at `d`.
    set ν' := (sys.internalSuffix e).init with hν'
    set L := (sys.trace e).toList
        (Stream'.Seq.terminates_map_iff.mpr (Stream'.Seq.terminates_filter _ _ h_term)) with hL
    -- Any emission `some (l, μ)` at `e` is, on either `getLast?` branch, an emission of a
    -- valid `sys`-scheduler at `d` (the suffix). Peel the belief `bind` in the `some` case.
    have h_inner : ∀ σ : Scheduler sys.toSystem,
        some (l, μ) ∈ (σ.next d).support → sys.step (e.endState h_term) l μ := by
      intro σ hσ
      have hstep := σ.valid d (Nat.find hd_term) (d.endState hd_term) (Nat.find_spec hd_term)
        (AlterSeq.stateAt_find_eq_endState d hd_term) l μ hσ
      rw [sys.internalSuffix_endState e h_term hd_term] at hstep
      exact hstep
    rw [h_s_eq]
    change some (l, μ) ∈
      (if hT : e.trans.Terminates then
        match (sys.trace e).toList
            (Stream'.Seq.terminates_map_iff.mpr (Stream'.Seq.terminates_filter _ _ hT)) |>.getLast?
        with
        | none =>
            (Scheduler.drawAndRun pe' ⟨sys.toSystem.init, Seq.nil⟩).next (sys.internalSuffix e)
        | some l' =>
            (pe'.beliefExpand
                ((sys.trace e).toList
                  (Stream'.Seq.terminates_map_iff.mpr (Stream'.Seq.terminates_filter _ _ hT)))
                (sys.internalSuffix e).init).bind (fun p =>
              (Scheduler.segmentScheduler pe' (sys.internalSuffix e).init l' p.1 p.2).next
                (sys.internalSuffix e))
      else PMF.pure none).support at h_supp
    rw [dif_pos h_term] at h_supp
    rw [← hd, ← hν', ← hL] at h_supp
    cases hgl : L.getLast? with
    | none =>
      rw [hgl] at h_supp
      exact h_inner (Scheduler.drawAndRun pe' ⟨sys.toSystem.init, Seq.nil⟩) h_supp
    | some l' =>
      rw [hgl] at h_supp
      rw [PMF.mem_support_bind_iff] at h_supp
      obtain ⟨p, _hp, h_supp⟩ := h_supp
      exact h_inner (Scheduler.segmentScheduler pe' ν' l' p.1 p.2) h_supp

/-- **A scheduler that emits nothing at `⟨s₀, nil⟩` halts immediately there.** If a valid
`sys`-scheduler `σ` puts no mass on any `some` at the empty history `⟨s₀, nil⟩`, then from
the Dirac source `PMF.pure s₀` it never takes a step: all its halting mass lives on the
empty execution `⟨s₀, nil⟩`, so integrating any `g` against the halting end-state recovers
`g s₀`. (Generalizes `haltNow_pushforward`: `σ`'s behaviour off `⟨s₀, nil⟩` is irrelevant,
since `pure s₀` never reaches any non-empty prefix.) -/
theorem Scheduler.pushforward_of_next_halts (sys : LabelledSystem State Label)
    (σ : Scheduler sys.toSystem) (s₀ : State)
    (hnone : ∀ x : Label × PMF State, σ.next ⟨s₀, Seq.nil⟩ (some x) = 0) (g : State → ENNReal) :
    (∑' e, σ.haltMass (PMF.pure s₀) e * g (e.1.endState e.2)) = g s₀ := by
  classical
  set pe : ProbabilisticExecution sys.toSystem := ⟨PMF.pure s₀, σ⟩ with hpe
  -- The one-step kernel at `⟨s₀, nil⟩` is `0` (no `some` emitted there).
  have hker_nil_zero : ∀ step : Label × State, pe.kernel ⟨s₀, Seq.nil⟩ step = 0 := by
    intro step
    unfold ProbabilisticExecution.kernel
    refine ENNReal.tsum_eq_zero.mpr (fun ν => ?_)
    have : pe.scheduler.next ⟨s₀, Seq.nil⟩ (some (step.1, ν)) = 0 := by rw [hpe]; exact hnone _
    rw [this, zero_mul]
  set e₀ : {e : AlterSeq State Label // e.trans.Terminates} :=
    ⟨⟨s₀, Seq.nil⟩, Stream'.Seq.terminates_nil⟩ with he₀
  -- A nonempty execution from `s₀` has `probOf = 0`: reverse-induct on its transition list;
  -- the front-most transition needs the (zero) kernel at `⟨s₀, nil⟩`.
  have hprob_zero : ∀ (L : List (Label × State))
      (hL : (Seq.ofList L : Seq (Label × State)).Terminates),
      L ≠ [] → pe.probOf ⟨s₀, Seq.ofList L⟩ hL = 0 := by
    intro L
    induction L using List.reverseRecOn with
    | nil => intro _ hne; exact absurd rfl hne
    | append_singleton rest last ih =>
      intro hL _
      have hrest : (Seq.ofList rest : Seq (Label × State)).Terminates :=
        Stream'.Seq.terminates_ofList rest
      have hseq : (Seq.ofList (rest ++ [last]) : Seq (Label × State))
          = (Seq.ofList rest).append (Seq.cons last Seq.nil) := by
        rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
      have happ : ((Seq.ofList rest).append (Seq.cons last Seq.nil)
          : Seq (Label × State)).Terminates := by rw [← hseq]; exact hL
      have hrw : pe.probOf ⟨s₀, Seq.ofList (rest ++ [last])⟩ hL
          = pe.probOf ⟨s₀, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩ happ := by
        have key : ∀ (sq : Seq (Label × State)) (hsq : sq.Terminates),
            sq = (Seq.ofList rest).append (Seq.cons last Seq.nil) →
            pe.probOf ⟨s₀, sq⟩ hsq
              = pe.probOf ⟨s₀, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩ happ := by
          rintro sq hsq rfl; rfl
        exact key _ hL hseq
      rw [hrw, ProbabilisticExecution.probOf_append_singleton _ _ _ hrest _ happ]
      by_cases hrnil : rest = []
      · -- `rest = []`: the front transition `last` needs the zero kernel at `⟨s₀, nil⟩`.
        refine mul_eq_zero.mpr (Or.inr ?_)
        have hknil : pe.kernel ⟨s₀, Seq.ofList rest⟩ last = pe.kernel ⟨s₀, Seq.nil⟩ last := by
          subst hrnil; rw [Stream'.Seq.ofList_nil]
        rw [hknil, hker_nil_zero last]
      · -- `rest ≠ []`: the prefix already has zero `probOf`.
        rw [ih hrest hrnil, zero_mul]
  -- Only the empty execution `⟨s₀, nil⟩` carries nonzero halt mass.
  have hsupp : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      σ.haltMass (PMF.pure s₀) e ≠ 0 → e = e₀ := by
    rintro ⟨⟨init', trans'⟩, hterm⟩ hne
    simp only at hterm hne ⊢
    have hprob_ne : pe.probOf ⟨init', trans'⟩ hterm ≠ 0 := by
      intro h0; apply hne; unfold Scheduler.haltMass; rw [← hpe, h0, zero_mul]
    -- `init' = s₀` (else initial mass vanishes).
    have hinit_eq : init' = s₀ := by
      by_contra hne_init
      apply hprob_ne
      refine le_antisymm ?_ bot_le
      refine le_trans (pe.probOf_le_init _ hterm) ?_
      rw [ProbabilisticExecution.init_eq_initState, hpe]
      exact le_of_eq (PMF.pure_apply_of_ne _ _ hne_init)
    subst hinit_eq
    -- `trans' = nil`: a nonempty execution from `s₀` has zero `probOf` (`hprob_zero`).
    have htrans_nil : trans' = Seq.nil := by
      by_contra htrans_ne
      apply hprob_ne
      have hL := Stream'.Seq.ofList_toList trans' hterm
      have hne_list : trans'.toList hterm ≠ [] := by
        intro hnil; apply htrans_ne
        rw [hnil, Stream'.Seq.ofList_nil] at hL; exact hL.symm
      have hofterm : (Seq.ofList (trans'.toList hterm) : Seq (Label × State)).Terminates :=
        Stream'.Seq.terminates_ofList _
      rw [pe.probOf_congr (⟨init', trans'⟩ : AlterSeq State Label)
            (⟨init', Seq.ofList (trans'.toList hterm)⟩ : AlterSeq State Label)
            (by rw [hL]) hterm hofterm]
      exact hprob_zero (trans'.toList hterm) hofterm hne_list
    rw [he₀]; exact Subtype.ext (by subst htrans_nil; rfl)
  -- Halt mass at `e₀` is `1`.
  have hhalt₀ : σ.haltMass (PMF.pure s₀) e₀ = 1 := by
    rw [he₀]; unfold Scheduler.haltMass; rw [← hpe]
    rw [show pe.probOf (⟨s₀, Seq.nil⟩ : AlterSeq State Label) Stream'.Seq.terminates_nil
        = (1 : ENNReal) by
      rw [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState, hpe,
        PMF.pure_apply_self]]
    have hnext_none : σ.next ⟨s₀, Seq.nil⟩ none = 1 := by
      have hsum := (σ.next ⟨s₀, Seq.nil⟩).tsum_coe
      rw [← hsum]
      refine (tsum_eq_single none ?_).symm
      rintro (_ | x) hx
      · exact absurd rfl hx
      · exact hnone x
    rw [hnext_none, mul_one]
  rw [tsum_eq_single e₀ (fun e he => by
    by_cases hz : σ.haltMass (PMF.pure s₀) e = 0
    · rw [hz, zero_mul]
    · exact absurd (hsupp e hz) he)]
  rw [hhalt₀, one_mul, he₀,
    AlterSeq.endState_of_trans_nil ⟨s₀, Seq.nil⟩ rfl Stream'.Seq.terminates_nil]

/-- **A `PMF.bind` emits a transition** whenever some `some`-weighted branch is itself
non-silent. If the source PMF `p` puts positive mass on `b₀` and the continuation `W b₀`
puts `< 1` mass on `none` (`W b₀ none ≠ 1`), then the mixture `p.bind W` differs from
`PMF.pure none` (it has positive mass on some `some`). -/
theorem Scheduler.bind_emits_of_branch {γ : Type}
    (p : PMF γ) (W : γ → PMF (Option (Label × PMF State))) (b₀ : γ)
    (hpos : p b₀ ≠ 0) (hbranch : W b₀ none ≠ 1) :
    p.bind W ≠ PMF.pure none := by
  classical
  intro hbad
  -- `none`-mass of the mixture is `1`; isolate the `b₀` term.
  have hmass : (p.bind W) none = 1 := by rw [hbad]; exact PMF.pure_apply_self none
  rw [PMF.bind_apply] at hmass
  have hle : ∀ b, p b * (W b) none ≤ p b :=
    fun b => mul_le_of_le_one_right' (PMF.coe_le_one _ _)
  have hsum_one : (∑' b, p b) = 1 := p.tsum_coe
  -- Every term equals the source weight (else the total would be `< 1`).
  have hterm_eq : ∀ b, p b * (W b) none = p b := by
    by_contra hne
    push Not at hne
    obtain ⟨b₁, hb₁⟩ := hne
    have hlt : p b₁ * (W b₁) none < p b₁ := lt_of_le_of_ne (hle b₁) hb₁
    have hstrict := ENNReal.tsum_lt_tsum (i := b₁)
      (f := fun b => p b * (W b) none) (g := fun b => p b)
      (by rw [hmass]; exact ENNReal.one_ne_top) hle hlt
    rw [hmass, hsum_one] at hstrict
    exact lt_irrefl 1 hstrict
  -- At `b₀`: positive weight forces `W b₀ none = 1`, contradiction.
  have heq := hterm_eq b₀
  have hWnone : (W b₀) none = 1 :=
    (ENNReal.mul_eq_left hpos (PMF.apply_ne_top _ _)).mp heq
  exact hbranch hWnone


/-- A non-terminating (infinite) trace is achieved with probability `0`: no finite
execution has an infinite trace. -/
theorem LabelledSystem.traceProb_eq_zero_of_not_terminates
    (ls : LabelledSystem State Label) (pe : ProbabilisticExecution ls.toSystem)
    (τ : Seq Label) (hτ : ¬ τ.Terminates) :
    ls.traceProb pe τ = 0 := by
  unfold LabelledSystem.traceProb
  have : IsEmpty {e : AlterSeq State Label //
      e.trans.Terminates ∧ ls.trace e = τ ∧ ls.IsTight e} := by
    refine ⟨fun e => hτ ?_⟩
    rw [← e.2.2.1, LabelledSystem.trace,
      Stream'.Seq.terminates_map_iff]
    exact Stream'.Seq.terminates_filter _ _ e.2.1
  exact tsum_empty

/-- **The mixture-realization core of `expand_traceProb_eq`** (the `lower_labProb_eq_aux`
analogue, at the trace level `g = 1`). The total `probOf`-mass that the expanded
`sys`-execution assigns to *tight* `sys`-executions with external trace `ofList L` equals
the total `probOf`-mass that `pe'` assigns to *tight* `sys^w`-histories with external trace
`ofList L`.

This is the headline trace-equality. The proof route (see `expand_extLabMass_eq` /
`expand_traceProb_eq_hExt`): under `hExt` (`pe'` schedules only external weak steps, so its
label list = its external trace) reduce both sides to the external level mass and prove the
`g`-indexed invariant `expand.extLabMass L g = pe'.hsLabMass L g` by induction on `L`
(the `lower_labProb_eq_aux` analogue under stutter — the pe'-side is integrated at the
hyperStep boundary `ν'` via `hsLabMass`, not the post-τ result, since the two differ by one
post-τ at general `g`); the `g = 1` slice gives the trace-equality. Then a Phase-2 WLOG
drops `hExt` (normalizing internal weak steps into the next external step's pre-τ via
`weakTau_trans`). -/
theorem expand_traceProb_tight_tsum_eq (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (h_init : pe'.initState = PMF.pure sys^w.toSystem.init) (L : List Label) :
    (∑' e : {e : AlterSeq State Label //
        e.trans.Terminates ∧ sys.trace e = Seq.ofList L ∧ sys.IsTight e},
        (⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ :
          ProbabilisticExecution sys.toSystem).probOf e.1 e.2.1)
      = ∑' E : {e : AlterSeq State Label //
          e.trans.Terminates ∧ sys^w.trace e = Seq.ofList L ∧ sys^w.IsTight e},
          pe'.probOf E.1 E.2.1 := by
  classical
  -- Both sides are `traceProb`s at `Seq.ofList L`: the LHS for the expanded `sys`-execution,
  -- the RHS literally the definition of `sys^w.traceProb pe' (Seq.ofList L)`.
  have hLHS : (∑' e : {e : AlterSeq State Label //
        e.trans.Terminates ∧ sys.trace e = Seq.ofList L ∧ sys.IsTight e},
        (⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ :
          ProbabilisticExecution sys.toSystem).probOf e.1 e.2.1)
      = sys.traceProb ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ (Seq.ofList L) := rfl
  have hRHS : (∑' E : {e : AlterSeq State Label //
          e.trans.Terminates ∧ sys^w.trace e = Seq.ofList L ∧ sys^w.IsTight e},
          pe'.probOf E.1 E.2.1)
      = sys^w.traceProb pe' (Seq.ofList L) := rfl
  rw [hLHS, hRHS]
  -- RESIDUAL: `sys.traceProb ⟨pure init, expand⟩ (ofList L) = sys^w.traceProb pe' (ofList L)`.
  -- Under `hExt` this is exactly `expand_traceProb_eq_hExt` (proven modulo the inductive
  -- STEP of `expand_extLabMass_eq` — the `lower_kernel_g_sum` analogue under stutter). The
  -- general statement here additionally needs the Phase-2 WLOG dropping `hExt`
  -- (normalizing internal weak steps into the next external step's pre-τ via
  -- `weakTau_trans`). Both pieces are pending; see `expand_extLabMass_eq`.
  sorry

/-- **Trace preservation for `Scheduler.expand`** (the M2 core, TO BE PROVEN):
the expanded `sys`-execution has the same trace distribution as `pe'`. Proven by
grouping both `traceProb`s by external trace and matching per `sys^w`-execution,
using a.s.-termination of the witnesses (mass preservation) and
`hyperStep_marginal_decomp` for the external steps. -/
theorem expand_traceProb_eq (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (h_init : pe'.initState = PMF.pure sys^w.toSystem.init) (τ : Seq Label) :
    sys.traceProb ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ τ
      = sys^w.traceProb pe' τ := by
  classical
  -- Infinite traces: both sides are `0` (no finite execution has an infinite trace).
  by_cases hτ : τ.Terminates
  · -- Finite trace: write `τ = ofList L` and reduce to the external-trace level mass.
    obtain ⟨L, rfl⟩ : ∃ L : List Label, τ = Seq.ofList L :=
      ⟨τ.toList hτ, (Stream'.Seq.ofList_toList τ hτ).symm⟩
    -- Reformulate both sides as the `g = 1` slice of the external-trace level mass,
    -- i.e. the total `probOf`-mass over tight, trace-`L` executions.
    rw [sys.traceProb_eq_extLabMass ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ L,
        sys^w.traceProb_eq_extLabMass pe' L,
        sys.extLabMass_eq_tight_tsum ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ L
          (fun _ => 1),
        sys^w.extLabMass_eq_tight_tsum pe' L (fun _ => 1)]
    simp only [mul_one]
    exact expand_traceProb_tight_tsum_eq sys pe' h_init L
  · rw [LabelledSystem.traceProb_eq_zero_of_not_terminates sys _ τ hτ,
      LabelledSystem.traceProb_eq_zero_of_not_terminates sys^w pe' τ hτ]

/-- Under `hExt` (`pe'` schedules only external labels), the one-step kernel of
`pe'` at an internal label is `0`: every `some (l, μ)` with `l` internal is
outside the scheduler support, so contributes `0`. -/
theorem ProbabilisticExecution.kernel_eq_zero_of_internal {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (E : AlterSeq State Label) (l : Label) (s' : State) (hl : sys.internal l) :
    pe'.kernel E (l, s') = 0 := by
  unfold ProbabilisticExecution.kernel
  have hzero : ∀ μ : PMF State, pe'.scheduler.next E (some (l, μ)) = 0 := by
    intro μ
    apply (PMF.apply_eq_zero_iff _ _).mpr
    intro hmem
    exact hExt E l μ hmem hl
  simp only [hzero, zero_mul, tsum_zero]

/-- Under `hExt`, any `pe'`-execution built from a transition list `L` (as
`⟨s₀, Seq.ofList L⟩`) whose label list contains an internal label has
`probOf = 0`: the cons-end recursion multiplies in the (zero) one-step kernel at
the internal transition. -/
theorem ProbabilisticExecution.probOf_ofList_eq_zero_of_internal_mem {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (s₀ : State) (L : List (Label × State))
    (h : (Seq.ofList L : Seq (Label × State)).Terminates)
    (hmem : ∃ p ∈ L, sys.internal p.1) :
    pe'.probOf ⟨s₀, Seq.ofList L⟩ h = 0 := by
  classical
  induction L using List.reverseRecOn with
  | nil => simp at hmem
  | append_singleton rest last ih =>
    -- Factor off the last transition via `probOf_append_singleton`.
    have hrest : (Seq.ofList rest : Seq (Label × State)).Terminates :=
      Stream'.Seq.terminates_ofList rest
    have hseq : (Seq.ofList (rest ++ [last]) : Seq (Label × State))
        = (Seq.ofList rest).append (Seq.cons last Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have happ : ((Seq.ofList rest).append (Seq.cons last Seq.nil)
        : Seq (Label × State)).Terminates := by rw [← hseq]; exact h
    -- Transport `probOf` through `hseq` (proof-irrelevant in the termination proof).
    have htrans : pe'.probOf ⟨s₀, Seq.ofList (rest ++ [last])⟩ h
        = pe'.probOf ⟨s₀, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩ happ := by
      have key : ∀ (sq : Seq (Label × State)) (hsq : sq.Terminates),
          sq = (Seq.ofList rest).append (Seq.cons last Seq.nil) →
          pe'.probOf ⟨s₀, sq⟩ hsq
            = pe'.probOf ⟨s₀, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩ happ := by
        rintro sq hsq rfl; rfl
      exact key _ h hseq
    have hfact :
        pe'.probOf ⟨s₀, Seq.ofList (rest ++ [last])⟩ h
          = pe'.probOf ⟨s₀, Seq.ofList rest⟩ hrest *
              pe'.kernel ⟨s₀, Seq.ofList rest⟩ last := by
      rw [htrans]
      exact pe'.probOf_append_singleton s₀ (Seq.ofList rest) hrest last happ
    rw [hfact]
    rcases hmem with ⟨p, hp_mem, hp_int⟩
    rw [List.mem_append] at hp_mem
    rcases hp_mem with hp_rest | hp_last
    · -- Internal label sits in `rest`: the prefix `probOf` is `0`.
      rw [ih hrest ⟨p, hp_rest, hp_int⟩, zero_mul]
    · -- Internal label is the last transition: the kernel factor is `0`.
      rw [List.mem_singleton] at hp_last
      subst hp_last
      rw [pe'.kernel_eq_zero_of_internal hExt ⟨s₀, Seq.ofList rest⟩ p.1 p.2 hp_int, mul_zero]

/-- Under `hExt`, `pe'`'s level mass at any label list containing an internal
label is `0`: every contributing execution has `probOf = 0`
(`probOf_ofList_eq_zero_of_internal_mem`). -/
theorem ProbabilisticExecution.labMass_eq_zero_of_internal_mem {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (labs : List Label) (g : State → ENNReal) (hint : ∃ l ∈ labs, sys.internal l) :
    pe'.labMass labs g = 0 := by
  classical
  obtain ⟨l, hl_mem, hl_int⟩ := hint
  unfold ProbabilisticExecution.labMass
  rw [ENNReal.tsum_eq_zero]
  intro e
  by_cases hc : e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs
  · rw [dif_pos hc]
    -- The label list of `e` is `labs`, which contains the internal label `l`.
    have hlabs : (e.trans.toList hc.1).map Prod.fst = labs := by
      apply Stream'.Seq.ofList_injective
      have e1 : (Seq.ofList (e.trans.toList hc.1) : Seq (Label × State)).map Prod.fst
          = Seq.ofList ((e.trans.toList hc.1).map Prod.fst) := by
        induction (e.trans.toList hc.1) with
        | nil => rw [Stream'.Seq.ofList_nil, Stream'.Seq.map_nil, List.map_nil,
            Stream'.Seq.ofList_nil]
        | cons a l ih => rw [Stream'.Seq.ofList_cons, Stream'.Seq.map_cons, List.map_cons,
            Stream'.Seq.ofList_cons, ih]
      rw [← e1, Stream'.Seq.ofList_toList e.trans hc.1]
      exact hc.2
    -- Transport `probOf e` to the `ofList`-form to apply the zero lemma.
    have hreassemble : (⟨e.init, Seq.ofList (e.trans.toList hc.1)⟩ : AlterSeq State Label) = e :=
      congrArg₂ AlterSeq.mk rfl (Stream'.Seq.ofList_toList e.trans hc.1)
    have hterm : (Seq.ofList (e.trans.toList hc.1) : Seq (Label × State)).Terminates :=
      Stream'.Seq.terminates_ofList _
    have hprob : pe'.probOf e hc.1
        = pe'.probOf ⟨e.init, Seq.ofList (e.trans.toList hc.1)⟩ hterm := by
      have key : ∀ (E : AlterSeq State Label) (hE : E.trans.Terminates),
          E = (⟨e.init, Seq.ofList (e.trans.toList hc.1)⟩ : AlterSeq State Label) →
          pe'.probOf E hE
            = pe'.probOf ⟨e.init, Seq.ofList (e.trans.toList hc.1)⟩ hterm := by
        rintro E hE rfl; rfl
      exact key e hc.1 hreassemble.symm
    -- Find the transition carrying the internal label `l`.
    have hwitness : ∃ p ∈ e.trans.toList hc.1, sys.internal p.1 := by
      have hmem' : l ∈ (e.trans.toList hc.1).map Prod.fst := hlabs.symm ▸ hl_mem
      obtain ⟨p, hp_mem, hp_eq⟩ := List.mem_map.mp hmem'
      exact ⟨p, hp_mem, hp_eq.symm ▸ hl_int⟩
    rw [hprob,
      pe'.probOf_ofList_eq_zero_of_internal_mem hExt e.init (e.trans.toList hc.1) hterm hwitness,
      zero_mul]
  · rw [dif_neg hc]

/-- Under `hExt` (`pe'` schedules only external labels), `pe'` takes no internal
transitions, so its external-trace level mass `extLabMass` collapses to the plain
label-list level mass `labMass`. -/
theorem ProbabilisticExecution.extLabMass_eq_labMass_noInternal {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (extLabs : List Label) (g : State → ENNReal) :
    sys^w.extLabMass pe' extLabs g = pe'.labMass extLabs g := by
  classical
  unfold LabelledSystem.extLabMass
  -- Per-`labs` equality: the trace-tight selector agrees with `labs = extLabs`,
  -- except possibly on label lists with an internal label, where `labMass = 0`.
  have hcongr : ∀ labs : List Label,
      (if sys^w.traceTightLabs (Seq.ofList extLabs) labs then pe'.labMass labs g else 0)
        = (if labs = extLabs then pe'.labMass labs g else 0) := by
    intro labs
    by_cases hext : ∀ l ∈ labs, ¬ sys.internal l
    · -- All-external `labs`: the trace-tight selector is exactly `labs = extLabs`.
      have hfilter : (Seq.ofList labs).filter (fun l => ¬ (sys^w).internal l)
          = Seq.ofList labs := by
        rw [ofList_filter_helper]
        congr 1
        rw [List.filter_eq_self]
        intro l hl
        simpa [LabelledSystem.weakClosure] using hext l hl
      have hiff : sys^w.traceTightLabs (Seq.ofList extLabs) labs ↔ labs = extLabs := by
        unfold LabelledSystem.traceTightLabs
        rw [hfilter]
        constructor
        · rintro ⟨h1, _⟩
          exact Stream'.Seq.ofList_injective h1
        · rintro rfl
          refine ⟨rfl, ?_⟩
          intro l hl
          have hmem : l ∈ labs := List.mem_of_getLast? hl
          simpa [LabelledSystem.weakClosure] using hext l hmem
      by_cases heq : labs = extLabs
      · rw [if_pos (hiff.mpr heq), if_pos heq]
      · rw [if_neg (fun h => heq (hiff.mp h)), if_neg heq]
    · -- `labs` has an internal label: `labMass labs g = 0`, so both sides vanish.
      simp only [not_forall, not_not] at hext
      obtain ⟨l, hl_mem, hl_int⟩ := hext
      have hzero : pe'.labMass labs g = 0 :=
        pe'.labMass_eq_zero_of_internal_mem hExt labs g ⟨l, hl_mem, hl_int⟩
      rw [hzero]
      simp
  rw [tsum_congr hcongr]
  rw [tsum_eq_single extLabs (fun b hb => if_neg hb), if_pos rfl]

/-! ### HyperStep-boundary level mass (`pe'`-side)

The `pe'`-side accountant for the expand-direction trace equality. `hsExpect`
reads, off a single weak step `s →[l] μ`, the `g`-expectation of its
*hyper-step target* `postDist` (the distribution reached after the τ-closure and
the visible `l`-step, before the trailing τ-closure). `hsLabMass` sums these
hyper-step expectations over all `sys^w`-histories with external trace
`L.dropLast`, weighted by `probOf` and the scheduler's emission probability of
the last label `l := L.getLast?`. Under `hExt` (only external labels scheduled),
the `g = 1` slice of `hsLabMass` equals `pe'`'s `traceProb` at `Seq.ofList L`.
This is the bridge target for `expand_extLabMass_eq`. -/

open Classical in
/-- The hyper-step-target `g`-expectation of a weak step `s →[l] μ`: `0` for an
internal `l` or a non-step, else `∑' s', postDist s' * g s'` where `postDist` is
the hyper-step target of the underlying `weakStep sys (PMF.pure s) l μ`. -/
noncomputable def ProbabilisticExecution.hsExpect
    {sys : LabelledSystem State Label} (_pe' : ProbabilisticExecution sys^w.toSystem)
    (s : State) (l : Label) (μ : PMF State) (g : State → ENNReal) : ENNReal :=
  if h : sys^w.step s l μ then
    if h_int : sys.internal l then 0
    else
      let hws : weakStep sys (PMF.pure s) l μ := (h.resolve_left (fun ha => h_int ha.1)).2
      ∑' s' : State, hws.postDist s' * g s'
  else 0

open Classical in
/-- **Lemma B1 (pre-τ;hs pushforward).** For external `l`, the pre-τ-and-hyperStep witness of a
weak step `s →[l] μ`, run from `pure s` and integrated against `g`, equals the hyper-step
expectation `hsExpect s l μ g` (`∑' s'', postDist s'' * g s''`). Mirrors the EXTERNAL case of
`weakStepWitness_pushforward`, stopping before the post-τ collapse. -/
theorem Scheduler.preHsWitness_pushforward {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (s : State) (l : Label) (μ : PMF State)
    (h : sys^w.step s l μ) (hext : ¬ sys.internal l) (g : State → ENNReal) :
    (∑' e, (Scheduler.preHsWitness sys s l μ).haltMass (PMF.pure s) e * g (e.1.endState e.2))
      = pe'.hsExpect s l μ g := by
  classical
  have hws : weakStep sys (PMF.pure s) l μ := (h.resolve_left (fun ha => hext ha.1)).2
  set ν := hws.preDist with hν
  set ν' := hws.postDist with hν'
  have h_pre : weakTau sys (PMF.pure s) ν := hws.weakTau_pre
  have h_mid : hyperStep sys ν l ν' := hws.hyperStep_mid
  set σpre := h_pre.witnessScheduler.toScheduler with hσpre
  set σext := Scheduler.extStep sys ν l h_mid.kernel h_mid.kernel_step with hσext
  have hsched : Scheduler.preHsWitness sys s l μ = Scheduler.bind σpre (fun _ => σext) := by
    unfold Scheduler.preHsWitness; rw [dif_pos h, dif_neg hext]
  rw [hsched]
  -- Step 1: outer bind composition.
  rw [Scheduler.bind_compose_integrate σpre (fun _ => σext) (PMF.pure s) g]
  -- INNER r := ∑' f₂, σext.haltMass (pure r) f₂ * g(f₂.end)
  set INNER : State → ENNReal := fun r =>
    ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
      σext.haltMass (PMF.pure r) f₂ * g (f₂.1.endState f₂.2) with hINNER
  -- Step 2: τ-collapse the pre-segment via `weakTau.integrate h_pre`.
  have h2 := h_pre.integrate INNER
  rw [show (∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
        σpre.haltMass (PMF.pure s) f₁ *
          ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
            σext.haltMass (PMF.pure (f₁.1.endState f₁.2)) f₂ * g (f₂.1.endState f₂.2))
      = ∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
          h_pre.witnessScheduler.haltMass (PMF.pure s) f₁ * INNER (f₁.1.endState f₁.2) from rfl,
    h2]
  -- Step 3: pull `ν r` in, swap, fold the source-mixture via `haltMass_init_mix`.
  have hpull : ∀ r : State,
      ν r * INNER r
        = ∑' f₂' : {e : AlterSeq State Label // e.trans.Terminates},
            ν r * σext.haltMass (PMF.pure r) f₂' * g (f₂'.1.endState f₂'.2) := by
    intro r
    rw [hINNER, ← ENNReal.tsum_mul_left]
    exact tsum_congr (fun f₂' => by ring)
  rw [tsum_congr hpull, ENNReal.tsum_comm]
  have hmix : ∀ f₂' : {e : AlterSeq State Label // e.trans.Terminates},
      (∑' r : State, ν r * σext.haltMass (PMF.pure r) f₂' * g (f₂'.1.endState f₂'.2))
        = σext.haltMass ν f₂' * g (f₂'.1.endState f₂'.2) := by
    intro f₂'
    rw [ENNReal.tsum_mul_right, ← Scheduler.haltMass_init_mix σext ν f₂']
  rw [tsum_congr hmix]
  -- Step 4: push the external step forward; rewrite the bind back to `ν'`.
  rw [hσext, extStep_pushforward sys ν l h_mid.kernel h_mid.kernel_step g, ← h_mid.post_eq_bind]
  -- The result `∑' s'', ν' s'' * g s''` is exactly `hsExpect s l μ g`.
  unfold ProbabilisticExecution.hsExpect
  rw [dif_pos h, dif_neg hext]

open Classical in
/-- **Lemma E (post-τ marginal collapse).** Integrating the post-τ witness from each
hyperStep-target sample `ν'`, weighted by `postDist ν'`, collapses to the weak-step result `μ`.
Mirrors the post-τ collapse step of `weakStepWitness_pushforward`: fold the `ν'`-mixture into
`haltMass postDist` via `haltMass_init_mix`, then `weakTau.integrate weakTau_post`. -/
theorem Scheduler.postTau_marginal_collapse {sys : LabelledSystem State Label}
    (s : State) (l : Label) (μ : PMF State) (h : sys^w.step s l μ) (hext : ¬ sys.internal l)
    (g' : State → ENNReal) :
    (∑' ν' : State,
        ((h.resolve_left (fun ha => hext ha.1)).2 : weakStep sys (PMF.pure s) l μ).postDist ν' *
        (∑' e, (Scheduler.postTauWitness sys s l μ).haltMass (PMF.pure ν') e
            * g' (e.1.endState e.2)))
      = ∑' σ : State, μ σ * g' σ := by
  classical
  set hws : weakStep sys (PMF.pure s) l μ := (h.resolve_left (fun ha => hext ha.1)).2 with hhws
  set ν' := hws.postDist with hν'
  have h_post : weakTau sys ν' μ := hws.weakTau_post
  -- `postTauWitness sys s l μ = h_post.witnessScheduler.toScheduler` (`dif_pos ⟨hext, h⟩` branch).
  have hsched : Scheduler.postTauWitness sys s l μ = h_post.witnessScheduler.toScheduler := by
    unfold Scheduler.postTauWitness
    rw [dif_pos ⟨hext, h⟩]
  set σpost := h_post.witnessScheduler.toScheduler with hσpost
  rw [hsched]
  -- Pull `ν' t` into the inner `e`-sum, swap, fold the `t`-mixture via `haltMass_init_mix`.
  have hpull : ∀ t : State,
      ν' t * (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          σpost.haltMass (PMF.pure t) e * g' (e.1.endState e.2))
        = ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
            ν' t * σpost.haltMass (PMF.pure t) e * g' (e.1.endState e.2) := by
    intro t
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr (fun e => by ring)
  rw [tsum_congr hpull, ENNReal.tsum_comm]
  have hmix : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      (∑' t : State, ν' t * σpost.haltMass (PMF.pure t) e * g' (e.1.endState e.2))
        = σpost.haltMass ν' e * g' (e.1.endState e.2) := by
    intro e
    rw [ENNReal.tsum_mul_right, ← Scheduler.haltMass_init_mix σpost ν' e]
  rw [tsum_congr hmix]
  exact h_post.integrate g'

open Classical in
/-- The **hyper-step-boundary level mass** of `pe'` at external trace `L`. For
empty `L` it is the initial `g`-expectation; otherwise, with `l := L.getLast?`,
it sums over `sys^w`-histories `E'` with label list `L.dropLast` the product of
`probOf E'` and the emission-weighted hyper-step expectation of the next weak
step labelled `l`. -/
noncomputable def ProbabilisticExecution.hsLabMass
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (L : List Label) (g : State → ENNReal) : ENNReal :=
  match L.getLast? with
  | none => ∑' s : State, pe'.initState s * g s
  | some l =>
      ∑' E' : AlterSeq State Label,
        dite (E'.trans.Terminates ∧ E'.trans.map Prod.fst = Seq.ofList L.dropLast)
          (fun h => pe'.probOf E' h.1 *
            ∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ)) *
              pe'.hsExpect (E'.endState h.1) l μ g)
          (fun _ => 0)

/-- The empty-trace `hsLabMass` is the initial `g`-expectation. -/
theorem ProbabilisticExecution.hsLabMass_nil
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (g : State → ENNReal) :
    pe'.hsLabMass [] g = ∑' s : State, pe'.initState s * g s := by
  unfold ProbabilisticExecution.hsLabMass
  rw [List.getLast?_nil]

open Classical in
/-- **Regrouping `hsLabMass` by the hyper-step target `ν'`.** The
hyper-step-boundary level mass at external trace `L` (with `L.getLast? = some l`)
equals, summed over the boundary distribution-target `ν'`, the total
`beliefExpandW`-normaliser at `ν'` weighted by `h ν'`. The analogue of
`lower_labProb_eq_aux`'s `stepA` regrouping for the `expand` telescoping. -/
theorem ProbabilisticExecution.hsLabMass_eq_Z_sum {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (L : List Label) (l : Label) (hL : L.getLast? = some l) (h : State → ENNReal) :
    pe'.hsLabMass L h = ∑' ν' : State, (∑' p, pe'.beliefExpandW L ν' p) * h ν' := by
  classical
  -- The common triple-sum form `∑' E' ∑' μ ∑' ν', G E' μ ν'`.
  set G : AlterSeq State Label → PMF State → State → ENNReal :=
    fun E' μ ν' =>
      if hT : E'.trans.Terminates ∧ E'.trans.map Prod.fst = Seq.ofList L.dropLast then
        if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT.1) l μ then
          pe'.probOf E' hT.1 * pe'.scheduler.next E' (some (l, μ))
            * (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' * h ν'
        else 0
      else 0 with hG
  have hLHS : pe'.hsLabMass L h
      = ∑' E' : AlterSeq State Label, ∑' μ : PMF State, ∑' ν' : State, G E' μ ν' := by
    rw [ProbabilisticExecution.hsLabMass, hL]
    dsimp only []
    refine tsum_congr (fun E' => ?_)
    by_cases hT : E'.trans.Terminates ∧ E'.trans.map Prod.fst = Seq.ofList L.dropLast
    · rw [dif_pos hT, ← ENNReal.tsum_mul_left]
      refine tsum_congr (fun μ => ?_)
      by_cases hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT.1) l μ
      · -- `hsExpect` opens to the `postDist`-integral; pull constants into the `ν'`-sum.
        rw [show pe'.hsExpect (E'.endState hT.1) l μ h
              = ∑' s' : State, (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist s'
                  * h s' from by
          unfold ProbabilisticExecution.hsExpect
          rw [dif_pos hstep.2, dif_neg hstep.1]]
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        refine tsum_congr (fun ν' => ?_)
        rw [hG]
        simp only [dif_pos hT, dif_pos hstep]
        ring
      · -- No external step at `μ`: `hsExpect = 0`, and every `G`-term vanishes.
        rw [show pe'.hsExpect (E'.endState hT.1) l μ h = 0 from by
          unfold ProbabilisticExecution.hsExpect
          by_cases hsw : sys^w.step (E'.endState hT.1) l μ
          · rw [dif_pos hsw]
            by_cases hint : sys.internal l
            · rw [dif_pos hint]
            · exact absurd ⟨hint, hsw⟩ hstep
          · rw [dif_neg hsw]]
        rw [mul_zero, mul_zero]
        symm
        refine ENNReal.tsum_eq_zero.mpr (fun ν' => ?_)
        rw [hG]; simp only [dif_pos hT, dif_neg hstep]
    · rw [dif_neg hT]
      symm
      refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
      refine ENNReal.tsum_eq_zero.mpr (fun ν' => ?_)
      rw [hG]; simp only [dif_neg hT]
  have hRHS : (∑' ν' : State, (∑' p, pe'.beliefExpandW L ν' p) * h ν')
      = ∑' E' : AlterSeq State Label, ∑' μ : PMF State, ∑' ν' : State, G E' μ ν' := by
    rw [show (∑' ν' : State, (∑' p, pe'.beliefExpandW L ν' p) * h ν')
          = ∑' ν' : State, ∑' p : AlterSeq State Label × PMF State,
              pe'.beliefExpandW L ν' p * h ν' from
        tsum_congr (fun ν' => by rw [ENNReal.tsum_mul_right])]
    rw [show (∑' ν' : State, ∑' p : AlterSeq State Label × PMF State,
              pe'.beliefExpandW L ν' p * h ν')
          = ∑' ν' : State, ∑' E' : AlterSeq State Label, ∑' μ : PMF State,
              pe'.beliefExpandW L ν' (E', μ) * h ν' from
        tsum_congr (fun ν' => by rw [ENNReal.tsum_prod'])]
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun E' => ?_)
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun μ => ?_)
    refine tsum_congr (fun ν' => ?_)
    rw [pe'.beliefExpandW_eq L ν' l hL (E', μ), hG]
    by_cases hT : E'.trans.Terminates ∧ E'.trans.map Prod.fst = Seq.ofList L.dropLast
    · simp only [dif_pos hT]
      by_cases hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT.1) l μ
      · simp only [dif_pos hstep]
      · simp only [dif_neg hstep, zero_mul]
    · simp only [dif_neg hT, zero_mul]
  rw [hLHS, hRHS]

/-- **Scheduler validity at the canonical terminal index.** For a terminating
history `E'` and an emitted `some (l, μ)`, the weak step `sys^w.step
(E'.endState hT) l μ` holds. -/
theorem ProbabilisticExecution.step_of_mem_support
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (E' : AlterSeq State Label) (hT : E'.trans.Terminates) (l : Label) (μ : PMF State)
    (h_supp : some (l, μ) ∈ (pe'.scheduler.next E').support) :
    sys^w.step (E'.endState hT) l μ :=
  pe'.scheduler.valid E' (Nat.find hT) (E'.endState hT) (Nat.find_spec hT)
    (E'.stateAt_find_eq_endState hT) l μ h_supp

/-- **The `g = 1` slice of `hsLabMass` is `pe'`'s `traceProb`** (under `hExt`).
For external schedules the hyper-step expectation of each scheduled step is the
total mass of its target PMF, namely `1`, so `hsLabMass L 1` collapses to the
total scheduler mass on label `L.getLast?` over `L.dropLast`-histories, which is
exactly `pe'.labMass L 1 = sys^w.traceProb pe' (Seq.ofList L)`. -/
theorem ProbabilisticExecution.hsLabMass_one_eq_traceProb
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (L : List Label) :
    pe'.hsLabMass L (fun _ => 1) = sys^w.traceProb pe' (Seq.ofList L) := by
  classical
  -- Reduce the RHS to `pe'.labMass L 1`.
  rw [sys^w.traceProb_eq_extLabMass pe' L, pe'.extLabMass_eq_labMass_noInternal hExt L]
  -- Case on whether `L` is empty.
  induction L using List.reverseRecOn with
  | nil =>
      rw [pe'.hsLabMass_nil (fun _ => 1), pe'.labMass_nil (fun _ => 1)]
  | append_singleton L' l _ih =>
      -- LHS: `getLast? (L' ++ [l]) = some l`, `dropLast (L' ++ [l]) = L'`.
      rw [pe'.labMass_step L' l (fun _ => 1)]
      unfold ProbabilisticExecution.hsLabMass
      simp only [List.getLast?_concat, List.dropLast_concat]
      refine tsum_congr fun E' => ?_
      by_cases hc : E'.trans.Terminates ∧ E'.trans.map Prod.fst = Seq.ofList L'
      · rw [dif_pos hc, dif_pos hc]
        -- The inner sums agree: `∑' μ, next (l,μ) * hsExpect = ∑' s', kernel (l,s') * 1`.
        congr 1
        -- First rewrite each `hsExpect` to `1` (when scheduled) so the `μ`-sum becomes
        -- the total scheduler mass on label `l`; then turn that into the kernel `s'`-sum.
        have hμ : ∀ μ : PMF State,
            pe'.scheduler.next E' (some (l, μ)) *
              pe'.hsExpect (E'.endState hc.1) l μ (fun _ => 1)
              = pe'.scheduler.next E' (some (l, μ)) := by
          intro μ
          by_cases hz : pe'.scheduler.next E' (some (l, μ)) = 0
          · rw [hz, zero_mul]
          · -- scheduled: derive the weak step and that `l` is external.
            have h_supp : some (l, μ) ∈ (pe'.scheduler.next E').support :=
              (PMF.mem_support_iff _ _).mpr hz
            have h_step : sys^w.step (E'.endState hc.1) l μ :=
              pe'.step_of_mem_support E' hc.1 l μ h_supp
            have h_int : ¬ sys.internal l := hExt E' l μ h_supp
            have hexp : pe'.hsExpect (E'.endState hc.1) l μ (fun _ => 1) = 1 := by
              unfold ProbabilisticExecution.hsExpect
              rw [dif_pos h_step, dif_neg h_int]
              simp only [mul_one]
              exact (h_step.resolve_left (fun ha => h_int ha.1)).2.postDist.tsum_coe
            rw [hexp, mul_one]
        rw [tsum_congr hμ]
        -- Now `∑' μ, next (l,μ) = ∑' s', kernel (l,s') * 1`.
        simp only [mul_one]
        unfold ProbabilisticExecution.kernel
        -- `∑' s', ∑' μ, next (l,μ) * μ s' = ∑' μ, next (l,μ) * ∑' s', μ s' = ∑' μ, next (l,μ)`.
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun μ => ?_
        simp only
        rw [ENNReal.tsum_mul_left, μ.tsum_coe, mul_one]
      · rw [dif_neg hc, dif_neg hc]

/-- **`segContPush` reduces to the `hsExpect`/`g` per-option split** (under `hExt`). The
per-`σ` continuation pushforward `segContPush l E' g σ` splits, over the emissions `opt` of
`pe'` at the extended clean history `E' ++ [(l, σ)]`, into: the halting branch
(`opt = none`, contributing `next (none) · g σ`) and each external next-step branch
(`opt = some (l', μ')`, contributing `next (some (l', μ')) · hsExpect σ l' μ' g` via
`preHsWitness_pushforward`). Every scheduled `some (l', μ')` is external by `hExt`, so the
`drawWit` split is exactly `haltNow`/`preHsWitness`. -/
theorem Scheduler.segContPush_split {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (l : Label) (E' : AlterSeq State Label) (hT : E'.trans.Terminates) (g : State → ENNReal)
    (σ : State) :
    Scheduler.segContPush pe' l E' g σ
      = pe'.scheduler.next ⟨E'.init, E'.trans.append (Seq.cons (l, σ) Seq.nil)⟩ none * g σ
        + ∑' lμ : Label × PMF State,
            pe'.scheduler.next ⟨E'.init, E'.trans.append (Seq.cons (l, σ) Seq.nil)⟩
                (some lμ)
              * pe'.hsExpect σ lμ.1 lμ.2 g := by
  classical
  set E'' : AlterSeq State Label := ⟨E'.init, E'.trans.append (Seq.cons (l, σ) Seq.nil)⟩ with hE''
  have hT'' : E''.trans.Terminates :=
    ⟨Nat.find hT + 1, Stream'.Seq.terminatedAt_append_find hT
      (show (Seq.cons (l, σ) Seq.nil).TerminatedAt 1 from rfl)⟩
  unfold Scheduler.segContPush
  rw [← hE'']
  -- Split the option-sum into the `none` term and the `some`-sum.
  rw [show (∑' opt : Option (Label × PMF State),
        pe'.scheduler.next E'' opt *
          ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
            (Scheduler.drawWit sys σ opt).haltMass (PMF.pure σ) f₂ * g (f₂.1.endState f₂.2))
      = (fun opt => pe'.scheduler.next E'' opt *
          ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
            (Scheduler.drawWit sys σ opt).haltMass (PMF.pure σ) f₂ * g (f₂.1.endState f₂.2)) none
        + ∑' n, (fun opt => pe'.scheduler.next E'' opt *
            ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
              (Scheduler.drawWit sys σ opt).haltMass (PMF.pure σ) f₂ * g (f₂.1.endState f₂.2))
            (some n) from by
    rw [← (Equiv.optionEquivSumPUnit.{0} (Label × PMF State)).symm.tsum_eq,
      Summable.tsum_sum ENNReal.summable ENNReal.summable, add_comm]
    congr 1
    rw [tsum_eq_single PUnit.unit (by rintro ⟨⟩ h; exact absurd rfl h)]
    rfl]
  simp only []
  congr 1
  · -- `none`: `drawWit σ none = haltNow`, pushforward `= g σ`.
    rw [Scheduler.drawWit, Scheduler.haltNow_pushforward sys σ g]
  · -- `some (l', μ')`: reduce the inner pushforward to `hsExpect σ l' μ' g`.
    refine tsum_congr (fun lμ => ?_)
    obtain ⟨l', μ'⟩ := lμ
    by_cases hz : pe'.scheduler.next E'' (some (l', μ')) = 0
    · rw [hz, zero_mul, zero_mul]
    · have h_supp : some (l', μ') ∈ (pe'.scheduler.next E'').support :=
        (PMF.mem_support_iff _ _).mpr hz
      have h_int : ¬ sys.internal l' := hExt E'' l' μ' h_supp
      have h_step : sys^w.step (E''.endState hT'') l' μ' :=
        pe'.step_of_mem_support E'' hT'' l' μ' h_supp
      have hend : E''.endState hT'' = σ := AlterSeq.endState_append_singleton E' hT l σ
      rw [hend] at h_step
      rw [Scheduler.drawWit,
        Scheduler.preHsWitness_pushforward pe' σ l' μ' h_step h_int g]

/-- **End-peel for `pathWeight`** (the defining cons-end recursion, extracted as a lemma):
`pathWeight base (rest ++ [last]) = pathWeight base rest * kernel ⟨base.init, base.trans ++
ofList rest⟩ last`. -/
theorem ProbabilisticExecution.pathWeight_concat {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (base : AlterSeq State Label) (rest : List (Label × State)) (last : Label × State) :
    pe.pathWeight base (rest ++ [last])
      = pe.pathWeight base rest
        * pe.kernel ⟨base.init, base.trans.append (Seq.ofList rest)⟩ last := by
  unfold ProbabilisticExecution.pathWeight
  rw [List.reverseRecOn_concat]

/-- **`pathWeight` splits along list concatenation.** From the empty base at `s₀`, the
path weight of `preList ++ segList` factors into the path weight of `preList` times the
path weight of `segList` evaluated from the base `⟨s₀, ofList preList⟩`. End-recursive
on `segList`. -/
theorem ProbabilisticExecution.pathWeight_append {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (s₀ : State) (preList segList : List (Label × State)) :
    pe.pathWeight ⟨s₀, Seq.nil⟩ (preList ++ segList)
      = pe.pathWeight ⟨s₀, Seq.nil⟩ preList
        * pe.pathWeight ⟨s₀, Seq.ofList preList⟩ segList := by
  induction segList using List.reverseRecOn with
  | nil =>
    simp only [List.append_nil]
    rw [show pe.pathWeight ⟨s₀, Seq.ofList preList⟩ [] = 1 from by
          unfold ProbabilisticExecution.pathWeight; rw [List.reverseRecOn_nil], mul_one]
  | append_singleton rest last ih =>
    rw [show preList ++ (rest ++ [last]) = (preList ++ rest) ++ [last] by
          rw [List.append_assoc]]
    rw [pe.pathWeight_concat ⟨s₀, Seq.nil⟩ (preList ++ rest) last,
        pe.pathWeight_concat ⟨s₀, Seq.ofList preList⟩ rest last, ih]
    simp only [Stream'.Seq.nil_append]
    rw [← Stream'.Seq.ofList_append]
    ring

/-- **`pathWeight` agrees across executions when kernels agree.** If `pe` from base
`⟨s₀, ofList preList⟩` and `pe'` from base `⟨s₀', nil⟩` have the same one-step kernel at
every position along `segList`, their `pathWeight`s along `segList` coincide. The kernel
hypothesis is only required for `pref ++ [step] <+: segList` (the positions actually
visited). -/
theorem ProbabilisticExecution.pathWeight_congr_of_kernel_eq {State Label : Type}
    {sys : System State Label} (pe pe' : ProbabilisticExecution sys)
    (s₀ s₀' : State) (preList segList : List (Label × State))
    (hker : ∀ (pref : List (Label × State)) (step : Label × State),
      pref ++ [step] <+: segList →
      pe.kernel ⟨s₀, Seq.ofList (preList ++ pref)⟩ step
        = pe'.kernel ⟨s₀', Seq.ofList pref⟩ step) :
    pe.pathWeight ⟨s₀, Seq.ofList preList⟩ segList
      = pe'.pathWeight ⟨s₀', Seq.nil⟩ segList := by
  induction segList using List.reverseRecOn with
  | nil =>
    unfold ProbabilisticExecution.pathWeight
    rw [List.reverseRecOn_nil, List.reverseRecOn_nil]
  | append_singleton rest last ih =>
    rw [pe.pathWeight_concat ⟨s₀, Seq.ofList preList⟩ rest last,
        pe'.pathWeight_concat ⟨s₀', Seq.nil⟩ rest last]
    rw [ih (fun pref step hp => hker pref step
      (hp.trans (List.prefix_append rest [last])))]
    -- match the two trailing kernels
    have hk := hker rest last (List.prefix_refl _)
    simp only [Stream'.Seq.nil_append]
    rw [← Stream'.Seq.ofList_append, hk]

/-- **Helper 3 — `probOf` concatenation factorization (kernel-agreement form).**
If `pe` and `pe'` agree on the one-step kernel at every position along `segList`
(`pe.kernel ⟨s₀, ofList (preList ++ pref)⟩ step = pe'.kernel ⟨s₀', ofList pref⟩ step` for
every `pref ++ [step] <+: segList`, where `s₀'` is the end-state of `⟨s₀, ofList preList⟩`)
and `pe'.init s₀' = 1`, then the `probOf` of the concatenated path factors as the prefix
`probOf` times the segment `probOf` from `s₀'`. Combines `probOf_eq_pathWeight`,
`pathWeight_append`, and `pathWeight_congr_of_kernel_eq`. -/
theorem ProbabilisticExecution.probOf_append_of_kernel_eq {State Label : Type}
    {sys : System State Label} (pe pe' : ProbabilisticExecution sys)
    (s₀ s₀' : State) (preList segList : List (Label × State))
    (hinit' : pe'.init s₀' = 1)
    (hker : ∀ (pref : List (Label × State)) (step : Label × State),
      pref ++ [step] <+: segList →
      pe.kernel ⟨s₀, Seq.ofList (preList ++ pref)⟩ step
        = pe'.kernel ⟨s₀', Seq.ofList pref⟩ step) :
    pe.probOf ⟨s₀, Seq.ofList (preList ++ segList)⟩
        (Stream'.Seq.terminates_ofList _)
      = pe.probOf ⟨s₀, Seq.ofList preList⟩ (Stream'.Seq.terminates_ofList _)
        * pe'.probOf ⟨s₀', Seq.ofList segList⟩ (Stream'.Seq.terminates_ofList _) := by
  rw [pe.probOf_eq_pathWeight s₀ (preList ++ segList) (Stream'.Seq.terminates_ofList _),
      pe.probOf_eq_pathWeight s₀ preList (Stream'.Seq.terminates_ofList _),
      pe'.probOf_eq_pathWeight s₀' segList (Stream'.Seq.terminates_ofList _),
      pe.pathWeight_append s₀ preList segList,
      pe.pathWeight_congr_of_kernel_eq pe' s₀ s₀' preList segList hker]
  rw [show pe.init s₀ * (pe.pathWeight ⟨s₀, Seq.nil⟩ preList
          * pe'.pathWeight ⟨s₀', Seq.nil⟩ segList)
        = (pe.init s₀ * pe.pathWeight ⟨s₀, Seq.nil⟩ preList)
          * (pe'.init s₀' * pe'.pathWeight ⟨s₀', Seq.nil⟩ segList) by
      rw [hinit', one_mul]; ring]

/-- **Appending all-internal transitions leaves the trace unchanged.** -/
theorem LabelledSystem.trace_append_internal (sys : LabelledSystem State Label)
    (s₀ : State) (preList pref : List (Label × State))
    (hpref : ∀ p ∈ pref, sys.internal p.1) :
    sys.trace ⟨s₀, Seq.ofList (preList ++ pref)⟩ = sys.trace ⟨s₀, Seq.ofList preList⟩ := by
  classical
  unfold LabelledSystem.trace
  rw [Stream'.Seq.ofList_append,
      Stream'.Seq.filter_append _ _ _ (Stream'.Seq.terminates_ofList _)]
  -- the `pref` part filters to `nil` (all internal)
  rw [show (Seq.ofList pref).filter (fun p => ¬ sys.internal p.1) = Seq.nil from ?_,
      Stream'.Seq.append_nil]
  -- `filter (¬internal) (ofList pref) = nil` since every element is internal
  induction pref with
  | nil => rw [Stream'.Seq.ofList_nil, Stream'.Seq.filter_nil]
  | cons a t ih =>
    rw [Stream'.Seq.ofList_cons,
        Stream'.Seq.filter_cons_neg a _ (by simpa using hpref a (by simp))]
    exact ih (fun p hp => hpref p (List.mem_cons_of_mem a hp))

/-- **A tight execution ends with an external transition.** (`IsTight`'s content via
`tight_iff`.) Supplies the `hpre_ext` hypothesis of `expand_probOf_append_factor`. -/
theorem LabelledSystem.tight_getLast_external (sys : LabelledSystem State Label)
    (e : AlterSeq State Label) (h : e.trans.Terminates) (htight : sys.IsTight e)
    (p : Label × State) (hp : (e.trans.toList h).getLast? = some p) :
    ¬ sys.internal p.1 := by
  have htt := ((sys.tight_iff (sys.trace e) e h).mp ⟨rfl, htight⟩).2
  exact htt p.1 (by rw [List.getLast?_map, hp]; rfl)

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

/-- **Trace of an append** (the trace ignores states; it depends only on the transition
sequence). -/
theorem LabelledSystem.trace_append (sys : LabelledSystem State Label)
    (s s' : State) (A B : Seq (Label × State)) (hA : A.Terminates) :
    sys.trace ⟨s, A.append B⟩ = (sys.trace ⟨s, A⟩).append (sys.trace ⟨s', B⟩) := by
  unfold LabelledSystem.trace
  rw [Stream'.Seq.filter_append _ _ _ hA, Stream'.Seq.map_append]

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

/-- **List filter-split into a tight prefix.** If `L.filter P = a ++ b` with `b` nonempty,
then `L` splits as `L1 ++ L2` with `L1.filter P = a`, `L2.filter P = b`, and `L1` "tight"
(empty or ending with a `P`-element). `L1` is the shortest prefix with filter `a`: it ends
right after the `|a|`-th `P`-element, so any trailing non-`P` run is pushed into `L2`. -/
private theorem List.exists_filter_split_tight {α : Type} (P : α → Bool) :
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

/-! ### `internalSuffix` of tight / segment-extended histories (PEEL step 1a) -/

/-- **`takeWhile` of a list ending with a `¬P`-element is empty after reversal.** If `L`'s
last element fails `P`, then `L.reverse.takeWhile P = []` (the reversal's head is `L`'s last,
which is consumed immediately). -/
theorem List.takeWhile_reverse_eq_nil_of_getLast {α : Type} (L : List α) (P : α → Bool)
    (hlast : ∀ x, L.getLast? = some x → ¬ P x) :
    L.reverse.takeWhile P = [] := by
  cases hL : L.reverse with
  | nil => simp
  | cons a t =>
    rw [List.takeWhile_cons]
    have hne : L ≠ [] := by intro h; rw [h] at hL; simp at hL
    have ha : a = L.getLast hne := by
      have h1 : L.reverse.head? = some a := by rw [hL]; rfl
      rw [List.head?_reverse, List.getLast?_eq_some_getLast hne] at h1
      exact (Option.some.injEq _ _).mp h1.symm
    rw [if_neg (by rw [ha]; exact hlast _ (List.getLast?_eq_some_getLast hne))]

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

/-- **Dropping a terminating sequence past its length yields `nil`.** -/
theorem Stream'.Seq.drop_length_eq_nil {α : Type} (s : Seq α) (h : s.Terminates) :
    s.drop (s.length h) = Seq.nil := by
  have hd : (s.drop (s.length h)).Terminates := Stream'.Seq.drop_terminates_pub h _
  have htl : (s.drop (s.length h)).toList hd = (s.toList h).drop (s.length h) :=
    Stream'.Seq.drop_toList_eq_pub s h _ hd
  have hlen : (s.toList h).length = s.length h := Stream'.Seq.length_toList s h
  have hnil : (s.toList h).drop (s.length h) = [] :=
    List.drop_eq_nil_of_le (by rw [hlen])
  rw [hnil] at htl
  have := Stream'.Seq.ofList_toList (s.drop (s.length h)) hd
  rw [htl, Stream'.Seq.ofList_nil] at this
  exact this.symm

/-- **`internalSuffix` of a tight execution is the empty suffix at its end-state.** A tight
execution ends with an external transition, so its maximal trailing internal run is empty:
`internalSuffix e = ⟨e.endState, nil⟩`. (PEEL step 1a, tight case.) -/
theorem LabelledSystem.internalSuffix_of_tight (sys : LabelledSystem State Label)
    (e : AlterSeq State Label) (h : e.trans.Terminates) (htight : sys.IsTight e) :
    sys.internalSuffix e = ⟨e.endState h, Seq.nil⟩ := by
  classical
  set Ltr := e.trans.toList h with hLtr
  have htw : (Ltr.reverse.takeWhile (fun p => decide (sys.internal p.1))) = [] := by
    apply List.takeWhile_reverse_eq_nil_of_getLast
    intro x hx
    simpa using sys.tight_getLast_external e h htight x hx
  have hlen : Ltr.length = e.trans.length h := Stream'.Seq.length_toList e.trans h
  have hfind : Nat.find h = e.trans.length h := rfl
  rw [LabelledSystem.internalSuffix, dif_pos h]
  simp only [← hLtr, htw, List.length_nil, Nat.sub_zero]
  have hstate : e.stateAt Ltr.length = some (e.endState h) := by
    rw [hlen, ← hfind]; exact AlterSeq.stateAt_find_eq_endState e h
  have hdrop : e.trans.drop Ltr.length = Seq.nil := by
    rw [hlen]; exact Stream'.Seq.drop_length_eq_nil e.trans h
  rw [hstate, hdrop, Option.getD_some]

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

/-! ### `expandCont`: the segment continuation scheduler (PEEL step 1b) -/

/-- **The expand-segment continuation scheduler.** At a trace-`L'` boundary `ν'` with
just-completed external label `l'`, this is the belief-mixed segment scheduler: draw a belief
sample `p = (E', μ)` from `pe'.beliefExpand L' ν'` and run `segmentScheduler pe' ν' l' E' μ`.
Validity is inherited from each `segmentScheduler`. This is the scheduler that
`Scheduler.expand` runs (at the `internalSuffix`) once the trace-`L'` prefix is committed and
its last external label `l'` is observed (see `expand_next_eq_expandCont`). -/
noncomputable def Scheduler.expandCont (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (L' : List Label) (ν' : State) (l' : Label) :
    Scheduler sys.toSystem where
  next d := (pe'.beliefExpand L' ν').bind (fun p =>
    (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).next d)
  valid := by
    classical
    intro d n s' hterm hstate l μ h_supp
    rw [PMF.mem_support_bind_iff] at h_supp
    obtain ⟨p, _hp, h_supp⟩ := h_supp
    exact (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).valid d n s' hterm hstate l μ h_supp

/-- **`Scheduler.expand`'s emission factors through `expandCont` at the internal suffix.** On a
terminating history `e` whose external trace label list ends with `l'` (the `some l'` branch of
`expand.next`), the expanded scheduler's emission at `e` equals `expandCont`'s emission at the
`internalSuffix` of `e`. (PEEL step 1b reduction; combined with `internalSuffix_append_internal`
this gives the kernel-agreement along a segment.) -/
theorem expand_next_eq_expandCont (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e : AlterSeq State Label) (hT : e.trans.Terminates) (l' : Label)
    (hgl : ((sys.trace e).toList (Stream'.Seq.terminates_map_iff.mpr
        (Stream'.Seq.terminates_filter _ _ hT))).getLast? = some l') :
    (Scheduler.expand sys pe').next e
      = (Scheduler.expandCont sys pe' ((sys.trace e).toList
          (Stream'.Seq.terminates_map_iff.mpr (Stream'.Seq.terminates_filter _ _ hT)))
          (sys.internalSuffix e).init l').next (sys.internalSuffix e) := by
  classical
  unfold Scheduler.expand
  simp only [dif_pos hT]
  rw [hgl]
  rfl

open Classical in
/-- **The expand-segment continuation `g`-mass, restricted to the new external label `l`.** The
total `g`-integrated halting mass of `expandCont sys pe' L' ν' l'` (run from the Dirac source
`pure ν'`) on executions whose external trace is exactly the single new label `l` (ending at its
hyper-step target). This is the continuation kernel `K' ν' g` of the PEEL: the trace-`(L'++[l])`
external level mass factors as the trace-`L'` external level mass of `K'` (see
`expand_extLabMass_step`). -/
noncomputable def ProbabilisticExecution.expandK
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (L' : List Label) (l' l : Label) (g : State → ENNReal) (ν' : State) : ENNReal :=
  ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
    (Scheduler.expandCont sys pe' L' ν' l').haltMass (PMF.pure ν') e
      * (if sys.trace e.1 = Seq.ofList [l] then g (e.1.endState e.2) else 0)

open Classical in
/-- **Kernel-agreement along an expand segment (PEEL step 1b/1a, fully proven).** At a
within-segment position `⟨init, ofList (preList ++ pref₀)⟩` — where `preList` ends with an
external transition whose external trace is `ofList L'` (`L'` nonempty, last label `l'`) and
`pref₀` is all-internal — the expanded scheduler's one-step kernel coincides with that of the
single segment-continuation execution `⟨pure ν', expandCont sys pe' L' ν' l'⟩` at `⟨ν',
ofList pref₀⟩`, where `ν' = endState preList`. Combines `trace_append_internal` (the running
external trace stays `ofList L'`, keeping `expand.next` on the `some l'` branch),
`internalSuffix_append_internal` (the internal suffix is `⟨ν', ofList pref₀⟩`) and
`expand_next_eq_expandCont`. -/
theorem expand_kernel_eq_expandCont {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (init : State) (L' : List Label) (l' : Label) (hL' : L'.getLast? = some l')
    (preList pref₀ : List (Label × State))
    (hpre_ext : ∀ x, preList.getLast? = some x → ¬ sys.internal x.1)
    (hpre_tr : sys.trace ⟨init, Seq.ofList preList⟩ = Seq.ofList L')
    (hpref_int : ∀ p ∈ pref₀, sys.internal p.1)
    (step : Label × State) :
    (⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩
        : ProbabilisticExecution sys.toSystem).kernel
        ⟨init, Seq.ofList (preList ++ pref₀)⟩ step
      = (⟨PMF.pure ((⟨init, Seq.ofList preList⟩ : AlterSeq State Label).endState
            (Stream'.Seq.terminates_ofList _)), Scheduler.expandCont sys pe' L'
            ((⟨init, Seq.ofList preList⟩ : AlterSeq State Label).endState
              (Stream'.Seq.terminates_ofList _)) l'⟩
          : ProbabilisticExecution sys.toSystem).kernel
        ⟨(⟨init, Seq.ofList preList⟩ : AlterSeq State Label).endState
            (Stream'.Seq.terminates_ofList _), Seq.ofList pref₀⟩ step := by
  classical
  set ν' := (⟨init, Seq.ofList preList⟩ : AlterSeq State Label).endState
    (Stream'.Seq.terminates_ofList _) with hν'
  -- The full position and its termination.
  set e : AlterSeq State Label := ⟨init, Seq.ofList (preList ++ pref₀)⟩ with he
  have heT : e.trans.Terminates := Stream'.Seq.terminates_ofList _
  -- Running external trace is `ofList L'` (appending internal `pref₀` leaves it unchanged).
  have htr : sys.trace e = Seq.ofList L' := by
    rw [he, sys.trace_append_internal init preList pref₀ hpref_int, hpre_tr]
  -- Its trace.toList = L', so getLast? = some l'.
  have hmapT : (sys.trace e).Terminates := by rw [htr]; exact Stream'.Seq.terminates_ofList _
  have hgl : ((sys.trace e).toList
      (Stream'.Seq.terminates_map_iff.mpr (Stream'.Seq.terminates_filter _ _ heT))).getLast?
      = some l' := by
    have hcongr : (sys.trace e).toList
        (Stream'.Seq.terminates_map_iff.mpr (Stream'.Seq.terminates_filter _ _ heT)) = L' := by
      apply Stream'.Seq.ofList_injective
      rw [Stream'.Seq.ofList_toList, htr]
    rw [hcongr, hL']
  -- The internal suffix is `⟨ν', ofList pref₀⟩`.
  have hsuf : sys.internalSuffix e = ⟨ν', Seq.ofList pref₀⟩ := by
    rw [he, sys.internalSuffix_append_internal init preList pref₀ hpre_ext hpref_int]
  -- `expand.next e = (expandCont L' ν' l').next ⟨ν', ofList pref₀⟩`.
  have hnext : (Scheduler.expand sys pe').next e
      = (Scheduler.expandCont sys pe' L' ν' l').next ⟨ν', Seq.ofList pref₀⟩ := by
    rw [expand_next_eq_expandCont sys pe' e heT l' hgl]
    -- match the `L'` / `ν'` / suffix arguments
    have hLeq : (sys.trace e).toList
        (Stream'.Seq.terminates_map_iff.mpr (Stream'.Seq.terminates_filter _ _ heT)) = L' := by
      apply Stream'.Seq.ofList_injective
      rw [Stream'.Seq.ofList_toList, htr]
    rw [hLeq, hsuf]
  -- Kernels are tsums of the (equal) `next`s.
  unfold ProbabilisticExecution.kernel
  refine tsum_congr (fun μ => ?_)
  rw [show (⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩
        : ProbabilisticExecution sys.toSystem).scheduler = Scheduler.expand sys pe' from rfl,
    show (⟨PMF.pure ν', Scheduler.expandCont sys pe' L' ν' l'⟩
        : ProbabilisticExecution sys.toSystem).scheduler = Scheduler.expandCont sys pe' L' ν' l'
      from rfl]
  rw [hnext]

open Classical in
/-- **`probOf` factorization along an expand segment (PEEL step 1c, fully proven).** A tight
trace-`(L' ++ [l])` execution written as `⟨init, ofList (preList ++ segList)⟩` — with `preList`
a tight trace-`L'` prefix ending in an external transition (last label `l'`, `L'` nonempty),
and `segList` the trace-`[l]` continuation whose only external transition is its last — has
`expand`-probability factoring as the prefix `probOf` times the segment-continuation `probOf`
of `⟨pure ν', expandCont sys pe' L' ν' l'⟩` (`ν' = endState preList`). The factorization is
`probOf_append_of_kernel_eq` fed the kernel-agreement `expand_kernel_eq_expandCont`. -/
theorem expand_probOf_segment_factor {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (init : State) (L' : List Label) (l' : Label) (hL' : L'.getLast? = some l')
    (preList segList : List (Label × State))
    (hpre_ext : ∀ x, preList.getLast? = some x → ¬ sys.internal x.1)
    (hpre_tr : sys.trace ⟨init, Seq.ofList preList⟩ = Seq.ofList L')
    (hseg_int : ∀ (pref : List (Label × State)) (stp : Label × State),
      pref ++ [stp] <+: segList → ∀ q ∈ pref, sys.internal q.1) :
    (⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩
        : ProbabilisticExecution sys.toSystem).probOf
        ⟨init, Seq.ofList (preList ++ segList)⟩ (Stream'.Seq.terminates_ofList _)
      = (⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩
            : ProbabilisticExecution sys.toSystem).probOf
          ⟨init, Seq.ofList preList⟩ (Stream'.Seq.terminates_ofList _)
        * (⟨PMF.pure ((⟨init, Seq.ofList preList⟩ : AlterSeq State Label).endState
              (Stream'.Seq.terminates_ofList _)),
            Scheduler.expandCont sys pe' L'
              ((⟨init, Seq.ofList preList⟩ : AlterSeq State Label).endState
                (Stream'.Seq.terminates_ofList _)) l'⟩
            : ProbabilisticExecution sys.toSystem).probOf
          ⟨(⟨init, Seq.ofList preList⟩ : AlterSeq State Label).endState
              (Stream'.Seq.terminates_ofList _), Seq.ofList segList⟩
          (Stream'.Seq.terminates_ofList _) := by
  classical
  set ν' := (⟨init, Seq.ofList preList⟩ : AlterSeq State Label).endState
    (Stream'.Seq.terminates_ofList _) with hν'
  refine (⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩
      : ProbabilisticExecution sys.toSystem).probOf_append_of_kernel_eq
    (⟨PMF.pure ν', Scheduler.expandCont sys pe' L' ν' l'⟩
      : ProbabilisticExecution sys.toSystem)
    init ν' preList segList ?_ ?_
  · -- `pe'.init ν' = 1`: the segment source is `pure ν'`.
    rw [ProbabilisticExecution.init_eq_initState]
    exact PMF.pure_apply_self ν'
  · -- kernel agreement at every visited within-segment position.
    intro pref stp hpf
    have hpref_int : ∀ p ∈ pref, sys.internal p.1 := hseg_int pref stp hpf
    exact expand_kernel_eq_expandCont pe' init L' l' hL' preList pref hpre_ext hpre_tr hpref_int stp

/-- **The inductive step of `expand_extLabMass_eq` (PEEL + ASSEMBLE).** Given the
induction hypothesis (`extLabMass L' g' = hsLabMass L' g'` for every test `g'`), the
trace-`(L' ++ [l])` external level mass of the expanded `sys`-execution equals `pe'`'s
hyper-step-boundary level mass at `(L' ++ [l])`.

The proof route (PEEL + ASSEMBLE):

* **PEEL (step 1c):** factor the trace-`(L' ++ [l])` external level mass as the trace-`L'`
  external level mass of a continuation kernel `K' ν' g`. Every tight trace-`(L' ++ [l])`
  `sys`-execution splits *uniquely* as `⟨init, ofList (preList ++ pref)⟩` with `preList` a tight
  trace-`L'` prefix (via `exists_filter_split_tight` / `tight_singleton_prefix_internal`) and
  `pref` a trace-`[l]` continuation. Along the segment the expanded scheduler's kernel agrees
  with `expandCont`'s — the kernel-agreement comes from `expand_next_eq_expandCont` plus the
  `internalSuffix` reduction `internalSuffix_append_internal` (which gives `internalSuffix
  ⟨init, ofList (preList ++ pref₀)⟩ = ⟨ν', ofList pref₀⟩` at each within-segment position
  `pref₀`, where `ν' = endState preList`) and `trace_append_internal` (which keeps the running
  trace equal to `ofList L'` along the segment, so `expand.next` stays on the `some
  (L'.getLast?)` branch). So `probOf_append_of_kernel_eq` factors the `probOf`, and regrouping
  by `preList` gives `extLabMass (L' ++ [l]) g = extLabMass L' (fun ν' => expandK pe' L'
  (L'.getLast?) l g ν')` — modulo the `L' = []` case, whose continuation is the `none`-branch
  `drawAndRun ⟨init, nil⟩` directly.

* **ASSEMBLE (steps 2–3, mirrors `lower_labProb_eq_aux`):** apply the IH to turn the trace-`L'`
  `extLabMass` of `K'` into `hsLabMass L' (K' ·)`, then collapse `hsLabMass L' (K' ·) = hsLabMass
  (L' ++ [l]) g` via `hsLabMass_eq_Z_sum` (stepA), `beliefExpand_normalize_cancel` (stepB),
  `segment_pushforward` (C), `postTau_marginal_collapse` (E), and `drawAndRun_pushforward` (the
  trace-`[l]` new-label slice). The pieces are all proven; what remains is the PEEL's tight-exec
  bijection bookkeeping and the `K'`-collapse reindex, isolated in this single `sorry`. -/
theorem expand_extLabMass_step {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (h_init : pe'.initState = PMF.pure sys^w.toSystem.init)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (L' : List Label) (l : Label) (g : State → ENNReal)
    (ih : ∀ g' : State → ENNReal,
      sys.extLabMass ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ L' g'
        = pe'.hsLabMass L' g') :
    sys.extLabMass ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ (L' ++ [l]) g
      = pe'.hsLabMass (L' ++ [l]) g := by
  -- STATUS (gap analysis, kept precise for the next pass):
  --
  -- PEEL CORE — DONE. The per-segment kernel-agreement and `probOf` factorization are now proven,
  -- self-contained, reusable lemmas:
  --   * `expand_kernel_eq_expandCont` — at any within-segment position `⟨init, ofList (preList ++
  --     pref₀)⟩` (preList tight-`L'`, ending external `l'`; `pref₀` internal) the `expand` kernel
  --     equals `(⟨pure ν', expandCont L' ν' l'⟩).kernel ⟨ν', ofList pref₀⟩` (via
  --     `trace_append_internal` + `internalSuffix_append_internal` + `expand_next_eq_expandCont`).
  --   * `expand_probOf_segment_factor` — hence `expand.probOf ⟨init, ofList (preList ++ segList)⟩
  --     = expand.probOf ⟨init, ofList preList⟩ · (⟨pure ν', expandCont L' ν' l'⟩).probOf
  --       ⟨ν', ofList segList⟩` (via `probOf_append_of_kernel_eq`).
  --
  -- GAP 1 (PEEL bijection bookkeeping — TRUE, mechanical). Build the bijection between tight
  -- trace-`(L'++[l])` execs and pairs (tight trace-`L'` prefix `preList`, trace-`[l]` segment
  -- `segList`) via `exists_filter_split_tight` (on the label list) +
  -- `tight_singleton_prefix_internal` (segment internals) + `isTight_append`/`trace_append`, then
  -- apply `expand_probOf_segment_factor` and regroup by `preList` (using `extLabMass_eq_tight_tsum`
  -- both ways). NOTE: this also needs the haltMass-vs-probOf reconciliation — `extLabMass` sums
  -- *raw* `probOf` over tight (= ending-external) execs, whereas `expandK` is defined via
  -- `expandCont.haltMass` (= probOf · next none); the inner segment sum `∑' segList trace-[l],
  -- expandCont.probOf · g(end)` must be identified with `expandK` (likely by recasting `expandK` in
  -- the raw tight-tsum form, since a tight trace-`[l]` segment is a maximal/halting continuation).
  --
  -- GAP 2 (ASSEMBLE `expandK`-collapse — GENUINELY OPEN, soundness-class). After IH +
  -- `hsLabMass_eq_Z_sum`, the collapse needs `expandK L' l' l g ν' = ∑' p, beliefExpand L' ν' p ·
  -- (single-draw segment trace-[l] g-mass of `segmentScheduler … p`)`. But `expandCont`'s emission
  -- `(beliefExpand L' ν').bind (fun p => (segmentScheduler … p).next d)` is a *history-independent
  -- (constant)* belief mixture — it re-draws `p` afresh at every prefix. `probOf` is a *product* of
  -- mixture kernels, and for ≥2-transition execs (the `l'`-step pre-τ is multi-step internal) the
  -- product of mixtures ≠ the mixture of products. This is the SAME constant-mixture re-draw
  -- phenomenon flagged OPEN (bears on SOUNDNESS) in `Scheduler.drawAndRun_pushforward` (Lemma B2) —
  -- with the crucial difference that `drawAndRun`'s mixture is *posterior-conditioned*
  -- (`drawAndRunW`/`normalize` depends on the running prefix, which is exactly what makes its
  -- marginal `drawAndRun_haltMass_marginal` — and hence B2 — go through), whereas `beliefExpand` is
  -- NOT posterior-conditioned, so no analogous marginal exists. Establishing this collapse (or
  -- refuting it with a randomized-`pe'` + multi-step-pre-τ counterexample, à la `FlawCheck`) is the
  -- genuine remaining mathematical content; it cannot be discharged by rearrangement. (The proven
  -- ASSEMBLE supporting pieces — `hsLabMass_eq_Z_sum`, `beliefExpand_normalize_cancel`,
  -- `segment_pushforward`, `segContPush_split`, `postTau_marginal_collapse`, and
  -- `drawAndRun_pushforward` — would finish the step the moment GAP 1 + GAP 2 are closed.)
  sorry

/-- **The expand-direction external level-mass identity** (under `hExt`). The
external level mass of the expanded `sys`-execution at trace `L` equals `pe'`'s
hyper-step-boundary level mass `hsLabMass`. The base case (`L = []`) is the
shared initial `g`-expectation; the step case is `expand_extLabMass_step`. -/
theorem expand_extLabMass_eq {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (h_init : pe'.initState = PMF.pure sys^w.toSystem.init)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (L : List Label) (g : State → ENNReal) :
    sys.extLabMass ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ L g
      = pe'.hsLabMass L g := by
  classical
  induction L using List.reverseRecOn generalizing g with
  | nil =>
      -- Both sides collapse to `g sys.init`.
      rw [sys.extLabMass_nil ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ g,
          pe'.hsLabMass_nil g, h_init]
      -- LHS: `∑' s, (pure sys.init) s * g s = g sys.init`.
      -- RHS: `∑' s, (pure sys^w.init) s * g s = g sys^w.init`, and `sys^w.init = sys.init`.
      have hL : (∑' s : State, (PMF.pure sys.toSystem.init) s * g s) = g sys.toSystem.init := by
        rw [tsum_eq_single sys.toSystem.init (fun s hs => by
              rw [PMF.pure_apply, if_neg hs, zero_mul]),
            PMF.pure_apply, if_pos rfl, one_mul]
      have hR : (∑' s : State, (PMF.pure sys^w.toSystem.init) s * g s)
          = g sys^w.toSystem.init := by
        rw [tsum_eq_single sys^w.toSystem.init (fun s hs => by
              rw [PMF.pure_apply, if_neg hs, zero_mul]),
            PMF.pure_apply, if_pos rfl, one_mul]
      rw [hL, hR]
      -- `sys^w.toSystem.init = sys.toSystem.init` definitionally (weakClosure preserves init).
      rfl
  | append_singleton L' l ih =>
      exact expand_extLabMass_step pe' h_init hExt L' l g ih

/-- **The expand-direction trace equality** (under `hExt`): the expanded
`sys`-execution and `pe'` assign the same probability to every finite external
trace `Seq.ofList L`. Clean modulo the step-`sorry` in `expand_extLabMass_step`. -/
theorem expand_traceProb_eq_hExt {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (h_init : pe'.initState = PMF.pure sys^w.toSystem.init)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (L : List Label) :
    sys.traceProb ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ (Seq.ofList L)
      = sys^w.traceProb pe' (Seq.ofList L) := by
  classical
  rw [sys.traceProb_eq_extLabMass ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ L,
      expand_extLabMass_eq pe' h_init hExt L (fun _ => 1),
      pe'.hsLabMass_one_eq_traceProb hExt L]

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

/-- **Reconstruction of a terminating sequence from its `j`-split.** `e.trans` is the
`ofList`-prefix of its first `j` transitions appended to the drop of the rest. -/
theorem Stream'.Seq.take_append_drop_pub {γ : Type} (s : Seq γ) (h : s.Terminates) (j : ℕ) :
    s = (Seq.ofList (Seq.take j s)).append (s.drop j) := by
  have hpre : (Seq.ofList (Seq.take j s) : Seq γ).Terminates := Stream'.Seq.terminates_ofList _
  have hdrop : (s.drop j).Terminates := Stream'.Seq.drop_terminates_pub h j
  have happ : ((Seq.ofList (Seq.take j s)).append (s.drop j)).Terminates :=
    ⟨Nat.find hpre + Nat.find hdrop,
      Stream'.Seq.terminatedAt_append_find hpre (Nat.find_spec hdrop)⟩
  -- Equal `toList` ⟹ equal `Seq` (both terminate), via `ofList_toList`.
  have htoList : s.toList h
      = ((Seq.ofList (Seq.take j s)).append (s.drop j)).toList happ := by
    rw [Stream'.Seq.toList_append _ _ hpre hdrop happ, Stream'.Seq.toList_ofList,
      Stream'.Seq.drop_toList_eq_pub s h j hdrop]
    rw [show Seq.take j s = (s.toList h).take j from by
      conv_lhs => rw [← Stream'.Seq.ofList_toList s h]
      rw [Seq.take_ofList_pub]]
    rw [List.take_append_drop]
  calc s = Seq.ofList (s.toList h) := (Stream'.Seq.ofList_toList s h).symm
    _ = Seq.ofList (((Seq.ofList (Seq.take j s)).append (s.drop j)).toList happ) := by rw [htoList]
    _ = (Seq.ofList (Seq.take j s)).append (s.drop j) := Stream'.Seq.ofList_toList _ happ

/-- **Trace of a halting `bind` execution splits over the σ/k boundary.** If `bind σ k`
halts at `e` (positive halt mass) and every halting σ-execution (from `μ`) has trace
`t₁`, while every halting `k r`-execution (from `pure r`, *for `r` reachable as the end
of a positive-mass halting σ-prefix*) has trace `t₂`, then `e`'s trace is `t₁ ++ t₂`.
Derived from the split-point convolution `bind_haltMass`: some split index has both
factors nonzero, and `trace` splits over the corresponding `append` (`trace_append`).
The reachability hypothesis on `r` lets the continuation's trace claim be restricted to
the states the prefix actually reaches (e.g. the support of a target distribution). -/
theorem Scheduler.bind_haltMass_trace (sys : LabelledSystem State Label)
    (σ : Scheduler sys.toSystem) (k : State → Scheduler sys.toSystem) (μ : PMF State)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) (t₁ t₂ : Seq Label)
    (hne : (Scheduler.bind σ k).haltMass μ e ≠ 0)
    (hσμ : ∀ f : {e : AlterSeq State Label // e.trans.Terminates},
        σ.haltMass μ f ≠ 0 → sys.trace f.1 = t₁)
    (hk : ∀ (r : State) (f : {e : AlterSeq State Label // e.trans.Terminates}),
        (∃ pre : {e : AlterSeq State Label // e.trans.Terminates},
          σ.haltMass μ pre ≠ 0 ∧ pre.1.endState pre.2 = r) →
        (k r).haltMass (PMF.pure r) f ≠ 0 → sys.trace f.1 = t₂) :
    sys.trace e.1 = t₁.append t₂ := by
  classical
  -- A split index `j` with both halt-mass factors nonzero.
  rw [Scheduler.bind_haltMass σ k μ e] at hne
  obtain ⟨j, _hj, hj_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [mul_ne_zero_iff] at hj_ne
  obtain ⟨hpre_ne, hsuf_ne⟩ := hj_ne
  -- `e.1.trans = (ofList (take j)).append (drop j)`.
  have hsplit : e.1.trans = (Seq.ofList (Seq.take j e.1.trans)).append (e.1.trans.drop j) :=
    Stream'.Seq.take_append_drop_pub e.1.trans e.2 j
  -- `trace e.1 = trace ⟨e.init, ofList (take j)⟩ ++ trace ⟨stateAfter, drop j⟩`.
  have htrace_split : sys.trace e.1
      = (sys.trace ⟨e.1.init, Seq.ofList (Seq.take j e.1.trans)⟩).append
          (sys.trace ⟨e.1.init, e.1.trans.drop j⟩) := by
    conv_lhs => rw [show e.1 = ⟨e.1.init, e.1.trans⟩ from rfl, hsplit]
    exact sys.trace_append e.1.init e.1.init _ _ (Stream'.Seq.terminates_ofList _)
  rw [htrace_split]
  -- the prefix has trace `t₁` (it's a halting σ-execution from `μ`).
  have ht1 : sys.trace ⟨e.1.init, Seq.ofList (Seq.take j e.1.trans)⟩ = t₁ :=
    hσμ ⟨⟨e.1.init, Seq.ofList (Seq.take j e.1.trans)⟩, Stream'.Seq.terminates_ofList _⟩ hpre_ne
  -- the threaded state `r` is the end-state of the (positive-mass) halting σ-prefix.
  have hreach : ∃ pre : {e : AlterSeq State Label // e.trans.Terminates},
      σ.haltMass μ pre ≠ 0 ∧ pre.1.endState pre.2
        = (⟨e.1.init, Seq.ofList (Seq.take j e.1.trans)⟩ : AlterSeq State Label).endState
            (Stream'.Seq.terminates_ofList _) :=
    ⟨⟨⟨e.1.init, Seq.ofList (Seq.take j e.1.trans)⟩, Stream'.Seq.terminates_ofList _⟩, hpre_ne, rfl⟩
  -- the suffix has trace `t₂` (it's a halting `k _`-execution from `pure _`); its trace
  -- depends only on the transitions, so the differing init state is irrelevant.
  have ht2 : sys.trace ⟨e.1.init, e.1.trans.drop j⟩ = t₂ := by
    -- Apply `hk` to the suffix factor of `hsuf_ne` (its `r`/`f` are inferred). The
    -- reachability witness uses that `stateAfter = endState of the take-prefix`.
    have hsuf := hk _ _ ?_ hsuf_ne
    · unfold LabelledSystem.trace at hsuf ⊢; exact hsuf
    · refine ⟨⟨⟨e.1.init, Seq.ofList (Seq.take j e.1.trans)⟩,
        Stream'.Seq.terminates_ofList _⟩, hpre_ne, ?_⟩
      -- `endState ⟨e.init, ofList (take j)⟩ = stateAfter e.1 j`.
      have hjle : j ≤ e.1.trans.length e.2 := by
        rw [Finset.mem_range] at _hj; omega
      rw [AlterSeq.endState_take_prefix e.1 e.2 j hjle]; rfl
  rw [ht1, ht2]

/-- **Halting executions of a `WeakScheduler` have empty trace.** A `WeakScheduler` only
emits internal labels, so any positive-probability (hence positive-halt-mass) execution
has an all-internal transition list and therefore an empty external trace. -/
theorem WeakScheduler.haltMass_trace_nil {State Label : Type}
    {sys : LabelledSystem State Label} (σ : WeakScheduler sys) (μ : PMF State)
    (e : {e : AlterSeq State Label // e.trans.Terminates})
    (hne : σ.haltMass μ e ≠ 0) :
    sys.trace e.1 = Seq.nil := by
  classical
  -- `haltMass ≠ 0 ⟹ probOf ≠ 0`.
  have hprob : (⟨μ, σ.toScheduler⟩ : ProbabilisticExecution sys.toSystem).probOf e.1 e.2 ≠ 0 := by
    intro h0; apply hne
    change (⟨μ, σ.toScheduler⟩ : ProbabilisticExecution sys.toSystem).probOf e.1 e.2
      * σ.toScheduler.next e.1 none = 0
    rw [h0, zero_mul]
  -- all transitions internal
  have hall := WeakScheduler.probOf_all_internal σ μ e.1 e.2 hprob
  -- trace = nil since every transition label is internal
  unfold LabelledSystem.trace
  rw [show e.1.trans = Seq.ofList (e.1.trans.toList e.2) from (Stream'.Seq.ofList_toList _ _).symm]
  rw [Seq.filter_ofList_eq_nil_pub (fun p => ¬ sys.internal p.1) (e.1.trans.toList e.2)
    (fun x hx => by simpa using hall x hx), Stream'.Seq.map_nil]

/-- **Halting executions of `extStep` from a state in support have trace `[l]`.** On
support, the single-external-step scheduler `extStep sys ν l κ` emits exactly the
external label `l` (then halts), so its halting executions from `pure r` (with
`r ∈ ν.support`) have external trace `[l]` (assuming `l` is external). -/
theorem extStep_haltMass_trace {State Label : Type} (sys : LabelledSystem State Label)
    (ν : PMF State) (l : Label) (κ : State → PMF (PMF State))
    (hκ : ∀ s ∈ ν.support, ∀ μ ∈ (κ s).support, sys.step s l μ) (r : State)
    (hr : r ∈ ν.support) (hl : ¬ sys.internal l)
    (E : {e : AlterSeq State Label // e.trans.Terminates})
    (hne : (Scheduler.extStep sys ν l κ hκ).haltMass (PMF.pure r) E ≠ 0) :
    sys.trace E.1 = Seq.ofList [l] := by
  rcases extStep_haltMass_ne_zero sys ν l κ hκ r E hne with ⟨hns, _⟩ | ⟨_, s', hE⟩
  · exact absurd hr hns
  · rw [hE]
    rw [sys.trace_cons_external r l s' Seq.nil hl, sys.trace_init]
    rw [Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]

open Classical in
/-- **The per-step witness produces exactly its step's external trace.** Every halting
execution of `Scheduler.weakStepWitness sys s l μ h` (from the Dirac source `pure s`) has
external trace `[l]` when `l` is external, and the empty trace when `l` is internal. -/
theorem Scheduler.weakStepWitness_halting_trace (sys : LabelledSystem State Label)
    (s : State) (l : Label) (μ : PMF State) (h : sys^w.step s l μ)
    (e : {e : AlterSeq State Label // e.trans.Terminates})
    (hne : (Scheduler.weakStepWitness sys s l μ h).haltMass (PMF.pure s) e ≠ 0) :
    sys.trace e.1 = (if sys.internal l then Seq.nil else Seq.ofList [l]) := by
  classical
  by_cases h_int : sys.internal l
  · -- internal: the witness is a `WeakScheduler`, all-internal, trace nil.
    rw [if_pos h_int]
    have hwt : weakTau sys (PMF.pure s) μ := (h.resolve_right (fun hb => hb.1 h_int)).2
    have hsched : Scheduler.weakStepWitness sys s l μ h = hwt.witnessScheduler.toScheduler := by
      unfold Scheduler.weakStepWitness; rw [dif_pos h_int]
    rw [hsched] at hne
    exact hwt.witnessScheduler.haltMass_trace_nil (PMF.pure s) e hne
  · -- external: `bind σpre (bind σext σpost)`; trace `nil ++ ([l] ++ nil) = [l]`.
    rw [if_neg h_int]
    have hws : weakStep sys (PMF.pure s) l μ := (h.resolve_left (fun ha => h_int ha.1)).2
    set ν := hws.preDist with hν
    have h_pre : weakTau sys (PMF.pure s) ν := hws.weakTau_pre
    have h_mid : hyperStep sys ν l hws.postDist := hws.hyperStep_mid
    have h_post : weakTau sys hws.postDist μ := hws.weakTau_post
    set σpre := h_pre.witnessScheduler.toScheduler with hσpre
    set σext := Scheduler.extStep sys ν l h_mid.kernel h_mid.kernel_step with hσext
    set σpost := h_post.witnessScheduler.toScheduler with hσpost
    have hsched : Scheduler.weakStepWitness sys s l μ h
        = Scheduler.bind σpre (fun _ => Scheduler.bind σext (fun _ => σpost)) := by
      unfold Scheduler.weakStepWitness; rw [dif_neg h_int]
    rw [hsched] at hne
    -- Outer split: trace = (σpre trace = nil) ++ ((bind σext σpost) trace = [l]).
    rw [show (Seq.ofList [l] : Seq Label) = Seq.nil.append (Seq.ofList [l]) from
      (Stream'.Seq.nil_append _).symm]
    refine Scheduler.bind_haltMass_trace sys σpre (fun _ => Scheduler.bind σext (fun _ => σpost))
      (PMF.pure s) e Seq.nil (Seq.ofList [l]) hne ?_ ?_
    · -- σpre is a weak scheduler: halting execs have trace nil.
      intro f hf
      exact h_pre.witnessScheduler.haltMass_trace_nil (PMF.pure s) f hf
    · -- For `r` reached by σpre (∈ ν.support), the inner `bind σext σpost` has trace `[l]`.
      intro r f hreach hf
      -- `r ∈ ν.support` via `witness_haltMass_le`.
      obtain ⟨pre, hpre_ne, hpre_end⟩ := hreach
      have hr_supp : r ∈ ν.support := by
        rw [PMF.mem_support_iff]
        intro hr0
        apply hpre_ne
        have hle : σpre.haltMass (PMF.pure s) pre ≤ ν (pre.1.endState pre.2) :=
          weakTau.witness_haltMass_le h_pre pre
        rw [hpre_end, hr0] at hle
        exact le_antisymm hle bot_le
      -- Inner split: trace = (σext trace = [l]) ++ (σpost trace = nil).
      rw [show (Seq.ofList [l] : Seq Label) = (Seq.ofList [l]).append Seq.nil from
        (Stream'.Seq.append_nil _).symm]
      refine Scheduler.bind_haltMass_trace sys σext (fun _ => σpost) (PMF.pure r) f
        (Seq.ofList [l]) Seq.nil hf ?_ ?_
      · -- σext halting from `pure r` (with `r ∈ ν.support`) has trace `[l]`.
        intro g hg
        exact extStep_haltMass_trace sys ν l h_mid.kernel h_mid.kernel_step r hr_supp h_int g hg
      · -- σpost is a weak scheduler: halting execs have trace nil.
        intro r' g _ hg
        exact h_post.witnessScheduler.haltMass_trace_nil (PMF.pure r') g hg

open Classical in
/-- **For an external label `l`, the per-step witness cannot be a.s.-silent** at the empty
history `⟨s, nil⟩`: its `none`-mass is `≠ 1`. If it were `1`, no `some` is emitted at the
first step, so by `pushforward_of_next_halts` all its halt mass sits on the empty execution
`⟨s, nil⟩` (trace `nil`); but `weakStepWitness_halting_trace` forces every halting
execution's external trace to be `[l] ≠ nil`. -/
theorem Scheduler.weakStepWitness_external_next_none_ne_one
    (sys : LabelledSystem State Label) (s : State) (l : Label) (μ : PMF State)
    (h : sys^w.step s l μ) (hext : ¬ sys.internal l) :
    (Scheduler.weakStepWitness sys s l μ h).next ⟨s, Seq.nil⟩ none ≠ 1 := by
  classical
  intro hone
  set e₀ : {e : AlterSeq State Label // e.trans.Terminates} :=
    ⟨⟨s, Seq.nil⟩, Stream'.Seq.terminates_nil⟩ with he₀
  -- Halt mass at `e₀` is `probOf ⟨s,nil⟩ * next ⟨s,nil⟩ none = 1 * 1 = 1 ≠ 0`.
  have hhalt_ne : (Scheduler.weakStepWitness sys s l μ h).haltMass (PMF.pure s) e₀ ≠ 0 := by
    unfold Scheduler.haltMass
    rw [he₀]
    rw [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState,
      PMF.pure_apply_self, one_mul, hone]
    exact one_ne_zero
  -- Every halting execution has external trace `[l]` (external `l`); but `e₀` has trace `nil`.
  have htr := Scheduler.weakStepWitness_halting_trace sys s l μ h e₀ hhalt_ne
  rw [if_neg hext] at htr
  rw [he₀] at htr
  simp only at htr
  rw [sys.trace_init s] at htr
  exact absurd htr.symm (by simp [Stream'.Seq.ofList_cons])

open Classical in
/-- **Halting executions of `preHsWitness` (external `l`) have external trace `[l]`.** For
external `l`, `preHsWitness sys s l μ = bind σpre σext`; its halting executions (from `pure
s`) split as `(σpre trace nil) ++ (σext trace [l])`, so the external trace is `[l]`. -/
theorem Scheduler.preHsWitness_halting_trace (sys : LabelledSystem State Label)
    (s : State) (l : Label) (μ : PMF State) (h : sys^w.step s l μ) (hext : ¬ sys.internal l)
    (e : {e : AlterSeq State Label // e.trans.Terminates})
    (hne : (Scheduler.preHsWitness sys s l μ).haltMass (PMF.pure s) e ≠ 0) :
    sys.trace e.1 = Seq.ofList [l] := by
  classical
  set hws : weakStep sys (PMF.pure s) l μ := (h.resolve_left (fun ha => hext ha.1)).2 with hhws
  set ν := hws.preDist with hν
  have h_pre : weakTau sys (PMF.pure s) ν := hws.weakTau_pre
  have h_mid : hyperStep sys ν l hws.postDist := hws.hyperStep_mid
  set σpre := h_pre.witnessScheduler.toScheduler with hσpre
  set σext := Scheduler.extStep sys ν l h_mid.kernel h_mid.kernel_step with hσext
  have hsched : Scheduler.preHsWitness sys s l μ = Scheduler.bind σpre (fun _ => σext) := by
    unfold Scheduler.preHsWitness
    rw [dif_pos h, dif_neg hext]
  rw [hsched] at hne
  -- Outer split: trace = (σpre trace = nil) ++ (σext trace = [l]).
  rw [show (Seq.ofList [l] : Seq Label) = Seq.nil.append (Seq.ofList [l]) from
    (Stream'.Seq.nil_append _).symm]
  refine Scheduler.bind_haltMass_trace sys σpre (fun _ => σext)
    (PMF.pure s) e Seq.nil (Seq.ofList [l]) hne ?_ ?_
  · intro f hf
    exact h_pre.witnessScheduler.haltMass_trace_nil (PMF.pure s) f hf
  · intro r f hreach hf
    obtain ⟨pre, hpre_ne, hpre_end⟩ := hreach
    have hr_supp : r ∈ ν.support := by
      rw [PMF.mem_support_iff]
      intro hr0
      apply hpre_ne
      have hle : σpre.haltMass (PMF.pure s) pre ≤ ν (pre.1.endState pre.2) :=
        weakTau.witness_haltMass_le h_pre pre
      rw [hpre_end, hr0] at hle
      exact le_antisymm hle bot_le
    exact extStep_haltMass_trace sys ν l h_mid.kernel h_mid.kernel_step r hr_supp hext f hf

open Classical in
/-- **Lemma B2 (drawAndRun pushforward).** `drawAndRun pe' E''`, run from the Dirac source
`pure (E''.endState)` and restricted (via the trace indicator) to halting executions whose
external trace is `[l]`, integrates `g` to the `pe'`-emission-weighted hyper-step expectation:
the sum over drawn `μ` of `pe'.next E'' (some (l, μ)) * hsExpect (E''.endState) l μ g`.

OBSTACLE (genuine, not a missing-lemma gap): `drawAndRun pe' E''` is a **constant mixture**
of schedulers, *not* a `Scheduler.bind`. Concretely (confirmed by unfolding `.next`):
`(drawAndRun pe' E'').next e = (pe'.scheduler.next E'').bind (fun opt => (runOpt opt).next e)`
where `runOpt (some (l,μ)) = preHsWitness sys (E''.endState) l μ` and `runOpt none = haltNow`,
and crucially the draw weights `pe'.scheduler.next E''` are **independent of the running
prefix `e`** (they always query the FIXED clean history `E''`, never the running history).
Such a scheduler RE-DRAWS `opt ~ pe'.next E''` at every prefix. Its halting mass is therefore
NOT the `pe'.next E''`-weighted sum of the component halt masses: `probOf` is a *product* of
per-step kernels, each kernel is the mixture `∑ opt, w opt * (runOpt opt).kernel`, and for
executions with ≥ 2 transitions the product of mixtures ≠ mixture of products (a hidden-Markov
re-draw, not a single up-front draw). ⚠️ WHETHER B2 IS TRUE IS OPEN — and it bears on
SOUNDNESS. For a weak step with nontrivial pre-τ (≥2 concrete steps) under a *randomized*
`pe'.next E''` (≥2 options with disjoint pre-τ trajectories), the re-draw underweights the
natural trajectory: e.g. with two ½-mass options, `drawAndRun.probOf(a-path) = ½·½ = ¼` while
the committed mixture gives `½·1 = ½`; the missing ¼ leaks to spurious partial-halts (trace
`[]`) unless recovered by cross-trajectory paths (whose contribution depends on
`preHsWitness_b`'s OFF-trajectory behavior — unknown). If the cross-paths do NOT recover the
mass, B2 is FALSE and the construction is unsound for randomized `pe'` + nontrivial pre-τ (a
7th flaw, same class as the prior memoryless-re-draw-under-stutter issues: `lower` avoids it
because `distHyperKernel` is ONE concrete step + `beliefTC` is a posterior; here the multi-step
witness is re-driven from the FIXED prior `pe'.next E''`). MUST be verified concretely (a
randomized-`pe'` + 2-step-pre-τ counterexample, à la `FlawCheck`) before relying on it. B1
(`preHsWitness_pushforward`) and E (`postTau_marginal_collapse`) — the single-witness pieces —
are fully proven above and reusable regardless of B2's fate. -/
theorem Scheduler.drawAndRun_pushforward {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (E'' : AlterSeq State Label) (hT : E''.trans.Terminates) (l : Label) (g : State → ENNReal) :
    (∑' e, (Scheduler.drawAndRun pe' E'').haltMass (PMF.pure (E''.endState hT)) e *
        (if sys.trace e.1 = Seq.ofList [l] then g (e.1.endState e.2) else 0))
      = ∑' μ : PMF State, pe'.scheduler.next E'' (some (l, μ)) *
          pe'.hsExpect (E''.endState hT) l μ g := by
  classical
  -- Abbreviate the trace-restricted test function.
  set g' : {e : AlterSeq State Label // e.trans.Terminates} → ENNReal :=
    fun e => if sys.trace e.1 = Seq.ofList [l] then g (e.1.endState e.2) else 0 with hg'
  -- Step 1: per-`e` marginal split, then swap sums over `opt`.
  have hterm : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      (Scheduler.drawAndRun pe' E'').haltMass (PMF.pure (E''.endState hT)) e * g' e
        = ∑' opt : Option (Label × PMF State), pe'.scheduler.next E'' opt
            * ((Scheduler.drawWit sys (E''.endState hT) opt).haltMass
                (PMF.pure (E''.endState hT)) e * g' e) := by
    intro e
    by_cases hinit : e.1.init = E''.endState hT
    · rw [Scheduler.drawAndRun_haltMass_marginal pe' E'' hT e hinit, ← ENNReal.tsum_mul_right]
      exact tsum_congr (fun opt => by rw [mul_assoc])
    · -- off-boundary `e`: both `drawAndRun` and every `drawWit` halt mass vanish (Dirac source)
      have hlhs : (Scheduler.drawAndRun pe' E'').haltMass (PMF.pure (E''.endState hT)) e = 0 := by
        unfold Scheduler.haltMass
        rw [ProbabilisticExecution.probOf_init_factor _ (PMF.pure (E''.endState hT)) e.1 e.2,
          PMF.pure_apply_of_ne _ _ hinit, zero_mul, zero_mul]
      rw [hlhs, zero_mul]
      refine (ENNReal.tsum_eq_zero.mpr (fun opt => ?_)).symm
      have hwit : (Scheduler.drawWit sys (E''.endState hT) opt).haltMass
          (PMF.pure (E''.endState hT)) e = 0 := by
        unfold Scheduler.haltMass
        rw [ProbabilisticExecution.probOf_init_factor _ (PMF.pure (E''.endState hT)) e.1 e.2,
          PMF.pure_apply_of_ne _ _ hinit, zero_mul, zero_mul]
      rw [hwit, zero_mul, mul_zero]
  rw [tsum_congr hterm, ENNReal.tsum_comm]
  -- INNER opt := ∑' e, drawWit(opt).haltMass · g' e (trace-restricted pushforward of witness `opt`)
  rw [show (∑' opt : Option (Label × PMF State), ∑' e,
          pe'.scheduler.next E'' opt
            * ((Scheduler.drawWit sys (E''.endState hT) opt).haltMass
                (PMF.pure (E''.endState hT)) e * g' e))
        = ∑' opt : Option (Label × PMF State), pe'.scheduler.next E'' opt
            * (∑' e, (Scheduler.drawWit sys (E''.endState hT) opt).haltMass
                (PMF.pure (E''.endState hT)) e * g' e) from
      tsum_congr (fun opt => ENNReal.tsum_mul_left)]
  -- Step 2: split the `opt`-sum (over `Option (Label × PMF State)`) into the `none` term plus the
  -- `(l', μ')`-sum (mirroring `segContPush_split`).
  rw [show (∑' opt : Option (Label × PMF State), pe'.scheduler.next E'' opt
          * (∑' e, (Scheduler.drawWit sys (E''.endState hT) opt).haltMass
              (PMF.pure (E''.endState hT)) e * g' e))
        = (fun opt => pe'.scheduler.next E'' opt
            * (∑' e, (Scheduler.drawWit sys (E''.endState hT) opt).haltMass
                (PMF.pure (E''.endState hT)) e * g' e)) none
          + ∑' n, (fun opt => pe'.scheduler.next E'' opt
              * (∑' e, (Scheduler.drawWit sys (E''.endState hT) opt).haltMass
                  (PMF.pure (E''.endState hT)) e * g' e)) (some n) from by
    rw [← (Equiv.optionEquivSumPUnit.{0} (Label × PMF State)).symm.tsum_eq,
      Summable.tsum_sum ENNReal.summable ENNReal.summable, add_comm]
    congr 1
    rw [tsum_eq_single PUnit.unit (by rintro ⟨⟩ h; exact absurd rfl h)]
    rfl]
  simp only []
  -- The `none` branch contributes `0`: `drawWit none = haltNow`, which halts only at the empty
  -- execution (trace `nil ≠ [l]`), so the trace indicator `g'` kills every halting fiber.
  rw [show pe'.scheduler.next E'' none
          * (∑' e, (Scheduler.drawWit sys (E''.endState hT) none).haltMass
              (PMF.pure (E''.endState hT)) e * g' e) = 0 from by
    have hnone : (∑' e, (Scheduler.drawWit sys (E''.endState hT) none).haltMass
        (PMF.pure (E''.endState hT)) e * g' e) = 0 := by
      refine ENNReal.tsum_eq_zero.mpr (fun e => ?_)
      by_cases hz : (Scheduler.drawWit sys (E''.endState hT) none).haltMass
          (PMF.pure (E''.endState hT)) e = 0
      · rw [hz, zero_mul]
      · -- nonzero halt mass of `haltNow` forces `e = ⟨endState, nil⟩` (trace `nil`).
        rw [Scheduler.drawWit] at hz ⊢
        have he_nil : e.1 = ⟨E''.endState hT, Seq.nil⟩ := by
          rcases e with ⟨⟨ei, et⟩, hterm_e⟩
          have hprob_ne : (⟨PMF.pure (E''.endState hT), Scheduler.haltNow sys⟩
              : ProbabilisticExecution sys.toSystem).probOf ⟨ei, et⟩ hterm_e ≠ 0 := by
            intro h0; apply hz; unfold Scheduler.haltMass; rw [h0, zero_mul]
          have hker_zero : ∀ (e' : AlterSeq State Label) (step : Label × State),
              (⟨PMF.pure (E''.endState hT), Scheduler.haltNow sys⟩
                : ProbabilisticExecution sys.toSystem).kernel e' step = 0 := by
            intro e' step
            unfold ProbabilisticExecution.kernel
            refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
            rw [show (⟨PMF.pure (E''.endState hT), Scheduler.haltNow sys⟩
                : ProbabilisticExecution sys.toSystem).scheduler.next e' (some (step.1, μ)) = 0 from
              PMF.pure_apply_of_ne _ _ (by simp), zero_mul]
          have htrans_nil : et = Seq.nil := by
            by_contra htrans_ne
            have hnonempty : et.toList hterm_e ≠ [] := by
              intro hnil; apply htrans_ne
              have := Stream'.Seq.ofList_toList et hterm_e
              rw [hnil, Stream'.Seq.ofList_nil] at this; exact this.symm
            obtain ⟨previous, last, h_prev, h_split, _, _⟩ :=
              Stream'.Seq.exists_split_last et hterm_e hnonempty
            apply hprob_ne
            have happ : (previous.append (Seq.cons last Seq.nil)).Terminates := h_split ▸ hterm_e
            have hrw : (⟨PMF.pure (E''.endState hT), Scheduler.haltNow sys⟩
                  : ProbabilisticExecution sys.toSystem).probOf ⟨ei, et⟩ hterm_e
                = (⟨PMF.pure (E''.endState hT), Scheduler.haltNow sys⟩
                  : ProbabilisticExecution sys.toSystem).probOf
                    ⟨ei, previous.append (Seq.cons last Seq.nil)⟩ happ := h_split ▸ rfl
            rw [hrw, ProbabilisticExecution.probOf_append_singleton _ _ _ h_prev _ happ,
              hker_zero ⟨ei, previous⟩ last, mul_zero]
          have hinit_eq : ei = E''.endState hT := by
            by_contra hne_init
            apply hprob_ne
            have hrw : (⟨PMF.pure (E''.endState hT), Scheduler.haltNow sys⟩
                  : ProbabilisticExecution sys.toSystem).probOf ⟨ei, et⟩ hterm_e
                = (⟨PMF.pure (E''.endState hT), Scheduler.haltNow sys⟩
                  : ProbabilisticExecution sys.toSystem).probOf ⟨ei, Seq.nil⟩
                    Stream'.Seq.terminates_nil := by subst htrans_nil; rfl
            rw [hrw, ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState]
            exact PMF.pure_apply_of_ne _ _ hne_init
          simp only at *
          subst htrans_nil; subst hinit_eq; rfl
        -- `g' e = 0` since `trace e.1 = nil ≠ ofList [l]`.
        have hg'0 : g' e = 0 := by
          simp only [hg', he_nil, sys.trace_init]
          rw [if_neg (by simp [Stream'.Seq.ofList_cons])]
        rw [hg'0, mul_zero]
    rw [hnone, mul_zero]]
  rw [zero_add]
  -- Step 3: the `some (l', μ')`-sum. For each scheduled `(l', μ')` (external by `hExt`), the
  -- witness `preHsWitness` halts only with trace `[l']`, so the indicator `g'` is constant
  -- (`= [l' = l] · g(end)`); the unrestricted pushforward `preHsWitness_pushforward` then gives
  -- `[l' = l] · hsExpect (endState) l' μ' g`.
  rw [show (∑' lμ : Label × PMF State, pe'.scheduler.next E'' (some lμ)
          * (∑' e, (Scheduler.drawWit sys (E''.endState hT) (some lμ)).haltMass
              (PMF.pure (E''.endState hT)) e * g' e))
        = ∑' lμ : Label × PMF State, pe'.scheduler.next E'' (some lμ)
            * (if lμ.1 = l then pe'.hsExpect (E''.endState hT) lμ.1 lμ.2 g else 0) from by
    refine tsum_congr (fun lμ => ?_)
    obtain ⟨l', μ'⟩ := lμ
    by_cases hz : pe'.scheduler.next E'' (some (l', μ')) = 0
    · rw [hz, zero_mul, zero_mul]
    · have h_supp : some (l', μ') ∈ (pe'.scheduler.next E'').support :=
        (PMF.mem_support_iff _ _).mpr hz
      have h_int : ¬ sys.internal l' := hExt E'' l' μ' h_supp
      have h_step : sys^w.step (E''.endState hT) l' μ' :=
        pe'.step_of_mem_support E'' hT l' μ' h_supp
      congr 1
      -- Rewrite the trace indicator to `[l' = l]` (constant in `e`) using the witness trace.
      have hrestr : (∑' e, (Scheduler.drawWit sys (E''.endState hT) (some (l', μ'))).haltMass
            (PMF.pure (E''.endState hT)) e * g' e)
          = if l' = l then (∑' e, (Scheduler.preHsWitness sys (E''.endState hT) l' μ').haltMass
              (PMF.pure (E''.endState hT)) e * g (e.1.endState e.2)) else 0 := by
        rw [Scheduler.drawWit]
        by_cases hll : l' = l
        · rw [if_pos hll]
          refine tsum_congr (fun e => ?_)
          by_cases hzz : (Scheduler.preHsWitness sys (E''.endState hT) l' μ').haltMass
              (PMF.pure (E''.endState hT)) e = 0
          · rw [hzz, zero_mul, zero_mul]
          · have htr := Scheduler.preHsWitness_halting_trace sys (E''.endState hT) l' μ'
              h_step h_int e hzz
            simp only [hg']
            rw [if_pos (by rw [htr, hll])]
        · rw [if_neg hll]
          refine ENNReal.tsum_eq_zero.mpr (fun e => ?_)
          by_cases hzz : (Scheduler.preHsWitness sys (E''.endState hT) l' μ').haltMass
              (PMF.pure (E''.endState hT)) e = 0
          · rw [hzz, zero_mul]
          · have htr := Scheduler.preHsWitness_halting_trace sys (E''.endState hT) l' μ'
              h_step h_int e hzz
            have hne : sys.trace e.1 ≠ Seq.ofList [l] := by
              rw [htr]
              intro hc
              exact hll (by simpa using Stream'.Seq.ofList_injective hc)
            simp only [hg']
            rw [if_neg hne, mul_zero]
      rw [hrestr]
      by_cases hll : l' = l
      · rw [if_pos hll, if_pos hll,
          Scheduler.preHsWitness_pushforward pe' (E''.endState hT) l' μ' h_step h_int g]
      · rw [if_neg hll, if_neg hll]]
  -- Step 4: the indicator `[l' = l]` collapses the `(l', μ')`-sum to the `μ`-sum at `l' = l`.
  rw [ENNReal.tsum_prod']
  rw [tsum_eq_single l (fun l' hl' => by
    refine ENNReal.tsum_eq_zero.mpr (fun μ' => ?_)
    rw [if_neg hl', mul_zero])]
  refine tsum_congr (fun μ => ?_)
  rw [if_pos rfl]


open Classical in
/-- **For an external label `l`, `preHsWitness` cannot be a.s.-silent** at `⟨s, nil⟩`: its
`none`-mass is `≠ 1`. Same argument as `weakStepWitness_external_next_none_ne_one`, via
`preHsWitness_halting_trace`. -/
theorem Scheduler.preHsWitness_external_next_none_ne_one (sys : LabelledSystem State Label)
    (s : State) (l : Label) (μ : PMF State) (h : sys^w.step s l μ) (hext : ¬ sys.internal l) :
    (Scheduler.preHsWitness sys s l μ).next ⟨s, Seq.nil⟩ none ≠ 1 := by
  classical
  intro hone
  set e₀ : {e : AlterSeq State Label // e.trans.Terminates} :=
    ⟨⟨s, Seq.nil⟩, Stream'.Seq.terminates_nil⟩ with he₀
  have hhalt_ne : (Scheduler.preHsWitness sys s l μ).haltMass (PMF.pure s) e₀ ≠ 0 := by
    unfold Scheduler.haltMass
    rw [he₀]
    rw [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState,
      PMF.pure_apply_self, one_mul, hone]
    exact one_ne_zero
  have htr := Scheduler.preHsWitness_halting_trace sys s l μ h hext e₀ hhalt_ne
  rw [he₀] at htr
  simp only at htr
  rw [sys.trace_init s] at htr
  exact absurd htr.symm (by simp [Stream'.Seq.ofList_cons])

open Classical in
/-- **`weakChain` produces its external trace on every halting execution.** Under
`WeakChainValid`, every halting execution of `Scheduler.weakChain sys steps s` (from the
Dirac source `pure s`) has external trace equal to `extTrace steps` — the external labels
of `steps`, `(steps.map Prod.fst).filter (¬ sys.internal ·)`. By induction on `steps`: the
base case is the immediate-halt `⟨s, nil⟩`; the cons step splits the `bind` over the
witness/continuation boundary (`bind_haltMass_trace`), with the witness contributing `[l]`
(external) or `[]` (internal) and the continuation contributing `extTrace rest` (IH). -/
theorem Scheduler.weakChain_halting_trace (sys : LabelledSystem State Label) :
    ∀ (steps : List (Label × PMF State)) (s : State),
      WeakChainValid sys steps s →
      ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
        (Scheduler.weakChain sys steps s).haltMass (PMF.pure s) e ≠ 0 →
        sys.trace e.1 = Seq.ofList ((steps.map Prod.fst).filter (fun l => ¬ sys.internal l))
  | List.nil, s, _, e, hne => by
      classical
      -- `weakChain [] s = haltNow`; its only halting execution is `⟨s, nil⟩` (trace nil).
      rw [show Scheduler.weakChain sys List.nil s = Scheduler.haltNow sys from rfl] at hne
      -- From `haltNow_pushforward`'s analysis: halting ⟹ `e.1 = ⟨s, nil⟩`.
      have hg := Scheduler.haltNow_pushforward sys s (fun t => if sys.trace e.1 = Seq.nil then 0
        else 1)
      -- Easier: directly characterise the halting fiber via the kernel-zero argument.
      -- The trace target is `[]`.
      rw [show ((List.nil : List (Label × PMF State)).map Prod.fst).filter
            (fun l => ¬ sys.internal l) = ([] : List Label) by simp, Stream'.Seq.ofList_nil]
      -- A `haltNow` halting execution is `⟨s, nil⟩`.
      have he_nil : e.1 = ⟨s, Seq.nil⟩ := by
        clear hg
        obtain ⟨⟨init', trans'⟩, hterm⟩ := e
        simp only at hne ⊢
        set pe : ProbabilisticExecution sys.toSystem := ⟨PMF.pure s, Scheduler.haltNow sys⟩
          with hpe
        have hprob_ne : pe.probOf ⟨init', trans'⟩ hterm ≠ 0 := by
          intro h0; apply hne
          change pe.probOf ⟨init', trans'⟩ hterm * (Scheduler.haltNow sys).next _ none = 0
          rw [h0, zero_mul]
        have hker_zero : ∀ (e' : AlterSeq State Label) (step : Label × State),
            pe.kernel e' step = 0 := by
          intro e' step
          unfold ProbabilisticExecution.kernel
          refine ENNReal.tsum_eq_zero.mpr (fun κ => ?_)
          rw [show pe.scheduler.next e' (some (step.1, κ)) = 0 from
            PMF.pure_apply_of_ne _ _ (by simp), zero_mul]
        have htrans_nil : trans' = Seq.nil := by
          by_contra htrans_ne
          have hnonempty : trans'.toList hterm ≠ [] := by
            intro hnil; apply htrans_ne
            have := Stream'.Seq.ofList_toList trans' hterm
            rw [hnil, Stream'.Seq.ofList_nil] at this; exact this.symm
          obtain ⟨previous, last, h_prev, h_split, _, _⟩ :=
            Stream'.Seq.exists_split_last trans' hterm hnonempty
          apply hprob_ne
          have happ : (previous.append (Seq.cons last Seq.nil)).Terminates := h_split ▸ hterm
          have hrw : pe.probOf ⟨init', trans'⟩ hterm
              = pe.probOf ⟨init', previous.append (Seq.cons last Seq.nil)⟩ happ := h_split ▸ rfl
          rw [hrw, ProbabilisticExecution.probOf_append_singleton _ _ _ h_prev _ happ,
            hker_zero ⟨init', previous⟩ last, mul_zero]
        have hinit_eq : init' = s := by
          by_contra hne_init
          apply hprob_ne
          have hrw : pe.probOf ⟨init', trans'⟩ hterm
              = pe.probOf ⟨init', Seq.nil⟩ Stream'.Seq.terminates_nil := by subst htrans_nil; rfl
          rw [hrw, ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState,
            hpe]
          exact PMF.pure_apply_of_ne _ _ hne_init
        subst htrans_nil; subst hinit_eq; rfl
      rw [he_nil]; exact sys.trace_init s
  | List.cons (l, μ) rest, s, hvalid, e, hne => by
      classical
      obtain ⟨hstep, hrest⟩ := hvalid
      rw [show Scheduler.weakChain sys (List.cons (l, μ) rest) s
          = Scheduler.bind (Scheduler.weakStepWitnessTotal sys s l μ)
              (fun s' => Scheduler.weakChain sys rest s') from rfl] at hne
      -- `extTrace ((l,μ)::rest) = (if internal l then [] else [l]) ++ extTrace rest`.
      have hext : (Seq.ofList (((List.cons (l, μ) rest).map Prod.fst).filter
            (fun a => ¬ sys.internal a)) : Seq Label)
          = (if sys.internal l then Seq.nil else Seq.ofList [l]).append
              (Seq.ofList ((rest.map Prod.fst).filter (fun a => ¬ sys.internal a))) := by
        rw [List.map_cons, List.filter_cons]
        by_cases h_int : sys.internal l
        · rw [if_neg (by simpa using h_int), if_pos h_int, Stream'.Seq.nil_append]
        · rw [if_pos (by simpa using h_int), if_neg h_int]
          rw [Stream'.Seq.ofList_cons, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil,
            Stream'.Seq.cons_append, Stream'.Seq.nil_append]
      rw [hext]
      refine Scheduler.bind_haltMass_trace sys (Scheduler.weakStepWitnessTotal sys s l μ)
        (fun s' => Scheduler.weakChain sys rest s') (PMF.pure s) e _ _ hne ?_ ?_
      · -- the witness contributes `[l]`/`[]` (`weakStepWitness_halting_trace`).
        intro f hf
        rw [Scheduler.weakStepWitnessTotal_eq sys s l μ hstep] at hf
        exact Scheduler.weakStepWitness_halting_trace sys s l μ hstep f hf
      · -- the continuation contributes `extTrace rest` (IH; valid from every state).
        intro r f _ hf
        exact Scheduler.weakChain_halting_trace sys rest r (hrest r) f hf

open Classical in
/-- **`weakChain` produces its external trace almost surely** (the `g = 1`
trace-preservation fact). Under `WeakChainValid`, the witness-lowering scheduler
`Scheduler.weakChain sys steps s` from the Dirac source `PMF.pure s` produces, with
probability `1`, the external trace `extTrace steps` — the external labels of
`steps`, i.e. `(steps.map Prod.fst).filter (¬ sys.internal ·)`.

Proven cleanly via the GENERAL post-τ-accounting lemma `traceProb_eq_one_of_asHalt`:
the chain almost surely halts (`weakChain_haltMass_one`, hypothesis (i)), and every
halting execution has external trace `extTrace steps` (`weakChain_halting_trace`,
hypothesis (ii)). The trailing-internal-suffix bookkeeping is fully absorbed by the
general lemma (its bridge `haltMass_le_traceProb`), so no `extLabMass` machinery is
needed here. -/
theorem Scheduler.weakChain_traceProb_extTrace (sys : LabelledSystem State Label)
    (steps : List (Label × PMF State)) (s : State) (hv : WeakChainValid sys steps s) :
    sys.traceProb ⟨PMF.pure s, Scheduler.weakChain sys steps s⟩
        (Seq.ofList ((steps.map Prod.fst).filter (fun l => ¬ sys.internal l))) = 1 := by
  refine LabelledSystem.traceProb_eq_one_of_asHalt sys (Scheduler.weakChain sys steps s)
    (PMF.pure s) _ ?_ ?_
  · -- (i) the chain almost surely halts
    exact Scheduler.weakChain_haltMass_one sys steps s hv
  · -- (ii) every halting execution has the external trace `extTrace steps`
    intro e hne
    exact Scheduler.weakChain_halting_trace sys steps s hv e hne

end PLTS
