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

open Classical in
/-- **External-trace `extLabMass`/`bind` decomposition, `g = 1`** (the M2 trace-cone
core, the cons step of `weakChain_extLabMass_eq_push`). The tight-trace-cone
`extLabMass`-mass (at the constant test `g = fun _ => 1`) of the composed scheduler
`bind (weakStepWitnessTotal sys s l μ) (weakChain sys rest)` at its full external
trace factors through the witness's post-distribution `μ`:

  `extLabMass ⟨pure s, bind witness (weakChain rest)⟩ (extTrace ((l,μ)::rest)) 1`
    `= ∑' t, μ t * extLabMass ⟨pure t, weakChain rest t⟩ (extTrace rest) 1`.

This is the trace-cone (tight-execution) analogue of `weakStepWitness_pushforward`,
at the `g = 1` slice. The subtlety — and the reason this does not follow from the
raw `haltMass` pushforward — is the **trailing-internal suffix**: a halting
execution of the witness need not be tight (its post-τ closure can append internal
transitions after the external `l`), so the tight executions realising `extTrace`
are the *prefixes* of halting executions obtained by stripping the trailing
all-internal run. The decomposition holds because that stripping is mass-preserving
(the witness almost surely halts, `weakStepWitness_haltMass_one`), but accounting for
it requires the a.s.-termination-from-prefix bookkeeping that closes M2.

WHY ONLY `g = 1`: for a general test `g`, the statement is FALSE. `extLabMass` cuts
the tight cone at the last external transition's hyperStep boundary `ν'`, whereas the
right-hand side integrates `g` against the post-τ result `μ`. In general `ν' ≠ μ`
(the post-τ internal closure moves mass), so the two `g`-expectations disagree. At
`g = fun _ => 1` both sides are mass, and the trailing post-τ closure is
mass-preserving (a.s.-halting), so the identity is the honest fiber-mass accounting
`∑_{halting e over the tight prefix e'} haltMass(e) = probOf(e')`, which is TRUE.

RESIDUAL (TRUE, left open): this is the documented hard core of the M2 superset
direction (the "(Ib) post-τ flaw"), now in its correct `g = 1` form. It is stated
and consumed by `weakChain_extLabMass_eq_push`; its proof (the trailing-internal
post-τ fiber-mass equality, via `internalSuffix` and a Kraft-style
halt-mass-from-prefix bound built on `pathWeight_antichain`) is left open. It is
TRUE-as-stated, unlike the previous general-`g` version which was false (`ν' ≠ μ`). -/
theorem LabelledSystem.weakChain_extLabMass_cons (sys : LabelledSystem State Label)
    (l : Label) (μ : PMF State) (rest : List (Label × PMF State)) (s : State)
    (hstep : sys^w.step s l μ)
    (hrest : ∀ t, WeakChainValid sys rest t) :
    sys.extLabMass ⟨PMF.pure s, Scheduler.bind (Scheduler.weakStepWitnessTotal sys s l μ)
          (fun s' => Scheduler.weakChain sys rest s')⟩
        (((l, μ) :: rest).map Prod.fst |>.filter (fun a => ¬ sys.internal a)) (fun _ => 1)
      = ∑' t, μ t * sys.extLabMass ⟨PMF.pure t, Scheduler.weakChain sys rest t⟩
          ((rest.map Prod.fst).filter (fun a => ¬ sys.internal a)) (fun _ => 1) := by
  sorry

open Classical in
/-- **External-trace level-mass of a `weakChain`, in pushforward form (`g = 1`).** The
tight-trace-cone `extLabMass`-mass (at the constant test `g = fun _ => 1`) of
`Scheduler.weakChain sys steps s` at its own external trace `extTrace steps` equals
the iterated pushforward `weakChainPush steps s (fun _ => 1)`. Composed with
`traceProb_eq_extLabMass` this is the trace-preservation fact
`weakChain_traceProb_extTrace`.

WHY ONLY `g = 1`: the cons step (`weakChain_extLabMass_cons`) is TRUE only at
`g = fun _ => 1` — for general `g`, `extLabMass` cuts the tight cone at the last
external hyperStep boundary `ν'` while `weakChainPush` integrates `g` against the
post-τ result `μ`, and `ν' ≠ μ` in general. The downstream consumer
(`weakChain_traceProb_extTrace`) only needs `g = 1`, so this lemma is stated at that
slice.

Proven by induction on `steps`. The base case (`steps = []`, `extTrace = []`) is
the initial expectation via `extLabMass_nil`. The cons step is the **external-trace
`extLabMass`/`bind` decomposition** (`weakChain_extLabMass_cons`, `g = 1`): the
tight-trace-cone mass of the composed scheduler factors through the witness's
post-distribution `μ`. -/
theorem LabelledSystem.weakChain_extLabMass_eq_push (sys : LabelledSystem State Label) :
    ∀ (steps : List (Label × PMF State)) (s : State),
      WeakChainValid sys steps s →
      sys.extLabMass ⟨PMF.pure s, Scheduler.weakChain sys steps s⟩
          ((steps.map Prod.fst).filter (fun l => ¬ sys.internal l)) (fun _ => 1)
        = weakChainPush steps s (fun _ => 1)
  | List.nil, s, _ => by
      classical
      -- `extTrace [] = []`; `extLabMass _ [] 1 = ∑' s₀, (pure s) s₀ * 1 = 1`.
      rw [show ((List.nil : List (Label × PMF State)).map Prod.fst).filter
              (fun l => ¬ sys.internal l) = ([] : List Label) by simp]
      rw [sys.extLabMass_nil ⟨PMF.pure s, Scheduler.weakChain sys List.nil s⟩ (fun _ => 1)]
      rw [show (⟨PMF.pure s, Scheduler.weakChain sys List.nil s⟩ :
          ProbabilisticExecution sys.toSystem).initState = PMF.pure s from rfl]
      rw [tsum_eq_single s (fun b hb => by rw [PMF.pure_apply_of_ne _ _ hb, zero_mul]),
        PMF.pure_apply_self, one_mul]
      rfl
  | List.cons (l, μ) rest, s, hvalid => by
      classical
      obtain ⟨hstep, hrest⟩ := hvalid
      -- The cons external trace: prepend `l` iff external.
      -- Decompose the composed-scheduler `extLabMass` through the witness's
      -- post-distribution `μ`, then close each fibre with the IH at `t`.
      have ih : ∀ t : State,
          sys.extLabMass ⟨PMF.pure t, Scheduler.weakChain sys rest t⟩
              ((rest.map Prod.fst).filter (fun l => ¬ sys.internal l)) (fun _ => 1)
            = weakChainPush rest t (fun _ => 1) :=
        fun t => sys.weakChain_extLabMass_eq_push rest t (hrest t)
      rw [show weakChainPush (List.cons (l, μ) rest) s (fun _ => 1)
          = ∑' t, μ t * weakChainPush rest t (fun _ => 1) from rfl]
      rw [tsum_congr (fun t => by rw [← ih t])]
      -- The external-trace `extLabMass`/`bind` decomposition (M2 trace-cone core, `g = 1`).
      exact sys.weakChain_extLabMass_cons l μ rest s hstep hrest

open Classical in
/-- **`extLabMass` = `haltMass`-integral for a `weakChain` (`g = 1`)** (the *key
equality* behind `weakChain_traceProb_extTrace`). Both sides equal the pushforward
`weakChainPush steps s (fun _ => 1)`: the left by `weakChain_extLabMass_eq_push`, the
right by `weakChain_pushforward`. Restricted to the constant test `g = fun _ => 1`
because `weakChain_extLabMass_eq_push` is TRUE only at that slice (the cons step's
post-τ boundary `ν' ≠ μ` for general `g`); the downstream `traceProb` consumer needs
only `g = 1`. -/
theorem LabelledSystem.weakChain_extLabMass_eq_haltMass_integral
    (sys : LabelledSystem State Label) (steps : List (Label × PMF State)) (s : State)
    (hv : WeakChainValid sys steps s) :
    sys.extLabMass ⟨PMF.pure s, Scheduler.weakChain sys steps s⟩
        ((steps.map Prod.fst).filter (fun l => ¬ sys.internal l)) (fun _ => 1)
      = ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          (Scheduler.weakChain sys steps s).haltMass (PMF.pure s) e
            * (fun _ => 1) (e.1.endState e.2) := by
  rw [sys.weakChain_extLabMass_eq_push steps s hv,
    ← Scheduler.weakChain_pushforward sys steps s (fun _ => 1) hv]

open Classical in
/-- **`weakChain` produces its external trace almost surely** (the `g = 1`
trace-preservation fact). Under `WeakChainValid`, the witness-lowering scheduler
`Scheduler.weakChain sys steps s` from the Dirac source `PMF.pure s` produces, with
probability `1`, the external trace `extTrace steps` — the external labels of
`steps`, i.e. `(steps.map Prod.fst).filter (¬ sys.internal ·)`.

The proof reduces, via `traceProb_eq_extLabMass`, to the *key equality* `KEY` that
the tight-trace-cone `extLabMass`-mass equals the all-halting `haltMass`-integral.
With `g = 1` the latter is the total halt mass, which is `1` by
`weakChain_haltMass_one`. -/
theorem Scheduler.weakChain_traceProb_extTrace (sys : LabelledSystem State Label)
    (steps : List (Label × PMF State)) (s : State) (hv : WeakChainValid sys steps s) :
    sys.traceProb ⟨PMF.pure s, Scheduler.weakChain sys steps s⟩
        (Seq.ofList ((steps.map Prod.fst).filter (fun l => ¬ sys.internal l))) = 1 := by
  classical
  set extLabs := (steps.map Prod.fst).filter (fun l => ¬ sys.internal l) with hext
  set ρ := Scheduler.weakChain sys steps s with hρ
  set D : ProbabilisticExecution sys.toSystem := ⟨PMF.pure s, ρ⟩ with hD
  -- KEY (`g = 1`): the tight-trace-cone `extLabMass`-mass equals the all-halting
  -- `haltMass`-integral. The RHS is the total halt mass, hence `1`.
  have KEY :
      sys.extLabMass D extLabs (fun _ => 1)
        = ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
            ρ.haltMass (PMF.pure s) e * (fun _ => 1) (e.1.endState e.2) :=
    sys.weakChain_extLabMass_eq_haltMass_integral steps s hv
  rw [sys.traceProb_eq_extLabMass D extLabs, KEY]
  simp only [mul_one]
  exact Scheduler.weakChain_haltMass_one sys steps s hv

/-- **The expand scheduler** (M2 witness). To be implemented by the new design:
the previous segment-based belief construction was unsound and has been removed. -/
noncomputable def Scheduler.expand (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) : Scheduler sys.toSystem :=
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
      = sys^w.traceProb pe' τ :=
  sorry

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
