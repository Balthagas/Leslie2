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

/-! ### State-anchored belief (refactor) -/

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

open Classical in
/-- **Segment bridge (`extLabMass ↔ haltMass`).** For the reassociated segment
witness "τ-closure `σ_τ : weakTau (pure s) ν`, then one external `hyperStep ν l ν'`,
then halt", the external level mass at trace `[l]` integrated against `g` equals the
post-hyperStep distribution's `g`-expectation `∑ t, ν' t * g t`. (The witness halts
right after `l`, so its trace-cone-`[l]` mass = its haltMass-integral; the latter
collapses by `bind_compose_integrate` + `weakTau.integrate` + `extStep_pushforward`
+ `hyperStep.post_eq_bind`.) -/
theorem extLabMass_segment_bridge {State Label : Type} (sys : LabelledSystem State Label)
    (s : State) (ν ν' : PMF State) (l : Label)
    (h_τ : weakTau sys (PMF.pure s) ν) (h_hyper : hyperStep sys ν l ν')
    (h_ext : ¬ sys.internal l) (g : State → ENNReal) :
    sys.extLabMass ⟨PMF.pure s,
        Scheduler.bind h_τ.witnessScheduler.toScheduler
          (fun _ => Scheduler.extStep sys ν l h_hyper.kernel h_hyper.kernel_step)⟩ [l] g
      = ∑' t : State, ν' t * g t := by
  classical
  set σ_τ := h_τ.witnessScheduler.toScheduler with hσ_τ
  set σext := Scheduler.extStep sys ν l h_hyper.kernel h_hyper.kernel_step with hσext
  set ρ := Scheduler.bind σ_τ (fun _ => σext) with hρ
  -- Part B (general `g'`): the haltMass-integral collapses to the post-hyperStep
  -- `g'`-expectation. (Same combinator chain as `weakStepWitness_pushforward`'s
  -- external branch, with no trailing post-τ.)
  have hpush : ∀ g' : State → ENNReal,
      (∑' e, ρ.haltMass (PMF.pure s) e * g' (e.1.endState e.2)) = ∑' t : State, ν' t * g' t := by
    intro g'
    rw [hρ]
    rw [Scheduler.bind_compose_integrate σ_τ (fun _ => σext) (PMF.pure s) g']
    set POST : State → ENNReal := fun r =>
      ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
        σext.haltMass (PMF.pure r) f₂ * g' (f₂.1.endState f₂.2) with hPOST
    have hτint := h_τ.integrate POST
    rw [show (∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
          σ_τ.haltMass (PMF.pure s) f₁ *
            ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
              σext.haltMass (PMF.pure (f₁.1.endState f₁.2)) f₂ * g' (f₂.1.endState f₂.2))
        = ∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
            h_τ.witnessScheduler.haltMass (PMF.pure s) f₁ * POST (f₁.1.endState f₁.2) from rfl,
      hτint]
    have hpull : ∀ r : State, ν r * POST r
        = ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
            ν r * σext.haltMass (PMF.pure r) f₂ * g' (f₂.1.endState f₂.2) := by
      intro r
      rw [hPOST, ← ENNReal.tsum_mul_left]
      exact tsum_congr (fun f₂ => by ring)
    rw [tsum_congr hpull, ENNReal.tsum_comm]
    have hmix : ∀ f₂ : {e : AlterSeq State Label // e.trans.Terminates},
        (∑' r : State, ν r * σext.haltMass (PMF.pure r) f₂ * g' (f₂.1.endState f₂.2))
          = σext.haltMass ν f₂ * g' (f₂.1.endState f₂.2) := by
      intro f₂
      rw [ENNReal.tsum_mul_right, ← Scheduler.haltMass_init_mix σext ν f₂]
    rw [tsum_congr hmix]
    rw [hσext, extStep_pushforward sys ν l h_hyper.kernel h_hyper.kernel_step g',
      ← h_hyper.post_eq_bind]
  -- The total halting mass of `ρ` is `1` (the `g' = 1` slice).
  have htotal : (∑' e, ρ.haltMass (PMF.pure s) e) = 1 := by
    have := hpush (fun _ => 1); simp only [mul_one] at this; rw [this, PMF.tsum_coe]
  -- The trace-cone condition predicate.
  set cond : {e : AlterSeq State Label // e.trans.Terminates} → Prop :=
    fun e => sys.trace e.1 = Seq.ofList [l] ∧ sys.IsTight e.1 with hcond
  -- termwise: `haltMass ≤ probOf`.
  have hle : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      ρ.haltMass (PMF.pure s) e
        ≤ (⟨PMF.pure s, ρ⟩ : ProbabilisticExecution sys.toSystem).probOf e.1 e.2 := by
    intro e
    unfold Scheduler.haltMass
    calc (⟨PMF.pure s, ρ⟩ : ProbabilisticExecution sys.toSystem).probOf e.1 e.2 * ρ.next e.1 none
        ≤ (⟨PMF.pure s, ρ⟩ : ProbabilisticExecution sys.toSystem).probOf e.1 e.2 * 1 := by
          gcongr; exact PMF.coe_le_one _ _
      _ = (⟨PMF.pure s, ρ⟩ : ProbabilisticExecution sys.toSystem).probOf e.1 e.2 := mul_one _
  -- Fact (i): every halting execution of `ρ` is a tight trace-`[l]` execution.
  have hfacti : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      ρ.haltMass (PMF.pure s) e ≠ 0 → cond e := by
    intro e hne
    rw [hρ, Scheduler.bind_haltMass σ_τ (fun _ => σext) (PMF.pure s) e] at hne
    -- Extract a nonzero summand `j ≤ length`.
    obtain ⟨j, hj_mem, hj_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    rw [Finset.mem_range, Nat.lt_succ_iff] at hj_mem
    set r := (e.1.stateAt j).getD e.1.init with hr
    -- Recast the summand via defeq: the private `stateAfter`/`drop_terminates` are
    -- defeq to `r` and `drop_terminates_pub`.
    have hj_ne' : σ_τ.haltMass (PMF.pure s)
          ⟨⟨e.1.init, Seq.ofList (Seq.take j e.1.trans)⟩, Stream'.Seq.terminates_ofList _⟩
        * σext.haltMass (PMF.pure r)
            ⟨⟨r, e.1.trans.drop j⟩, Stream'.Seq.drop_terminates_pub e.2 j⟩ ≠ 0 := hj_ne
    have hpre_ne : σ_τ.haltMass (PMF.pure s)
        ⟨⟨e.1.init, Seq.ofList (Seq.take j e.1.trans)⟩, Stream'.Seq.terminates_ofList _⟩ ≠ 0 :=
      fun h0 => hj_ne' (by rw [h0, zero_mul])
    have hext_ne : σext.haltMass (PMF.pure r)
        ⟨⟨r, e.1.trans.drop j⟩, Stream'.Seq.drop_terminates_pub e.2 j⟩ ≠ 0 :=
      fun h0 => hj_ne' (by rw [h0, mul_zero])
    -- The prefix `⟨e.init, ofList (take j)⟩`; the σ_τ-bound gives its end-state in `ν.support`.
    set pre : {e : AlterSeq State Label // e.trans.Terminates} :=
      ⟨⟨e.1.init, Seq.ofList (Seq.take j e.1.trans)⟩, Stream'.Seq.terminates_ofList _⟩ with hpre
    have hq_supp : pre.1.endState pre.2 ∈ ν.support := by
      rw [PMF.mem_support_iff]
      intro hq0
      apply hpre_ne
      have hbd := h_τ.witness_haltMass_le pre
      rw [hσ_τ]; rw [hq0] at hbd; exact le_antisymm hbd bot_le
    -- `e.trans.toList = take j ++ (drop j).toList` (public Seq facts).
    have htake : Seq.take j e.1.trans = (e.1.trans.toList e.2).take j := by
      conv_lhs => rw [← Stream'.Seq.ofList_toList e.1.trans e.2]
      rw [Seq.take_ofList_pub]
    have hdrop : (e.1.trans.drop j).toList (Stream'.Seq.drop_terminates_pub e.2 j)
        = (e.1.trans.toList e.2).drop j :=
      Stream'.Seq.drop_toList_eq_pub e.1.trans e.2 j (Stream'.Seq.drop_terminates_pub e.2 j)
    -- Case on the shape of `extStep`'s halting suffix.
    rcases extStep_haltMass_ne_zero sys ν l h_hyper.kernel h_hyper.kernel_step r
        ⟨⟨r, e.1.trans.drop j⟩, Stream'.Seq.drop_terminates_pub e.2 j⟩ hext_ne with
      ⟨hr_notin, hEnil⟩ | ⟨hr_in, s', hEcons⟩
    · -- Empty case is impossible: `pre.endState = r ∈ ν.support` contradicts `r ∉ ν.support`.
      exfalso
      have hr_end : pre.1.endState pre.2 = r :=
        AlterSeq.endState_take_prefix e.1 e.2 j hj_mem
      rw [hr_end] at hq_supp
      exact hr_notin hq_supp
    · -- External case: `drop j = cons (l, s') nil`, `r ∈ ν.support`, prefix all internal.
      have hdrop_cons : e.1.trans.drop j = Seq.cons (l, s') Seq.nil :=
        (AlterSeq.mk.injEq .. ▸ hEcons).2
      -- `(drop j).toList = [(l, s')]`.
      have hdroplist : (e.1.trans.toList e.2).drop j = [(l, s')] := by
        rw [← hdrop]
        rw [Stream'.Seq.toList_congr_pub hdrop_cons (Stream'.Seq.drop_terminates_pub e.2 j)
          (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil),
          Stream'.Seq.toList_cons, Stream'.Seq.toList_nil]
      -- The label list of `e`: `(take j).map fst ++ [l]`.
      have hlabs_eq : (e.1.trans.toList e.2).map Prod.fst
          = ((e.1.trans.toList e.2).take j).map Prod.fst ++ [l] := by
        conv_lhs => rw [← List.take_append_drop j (e.1.trans.toList e.2)]
        rw [List.map_append, hdroplist, List.map_cons, List.map_nil]
      -- All labels of the `take j` prefix are internal.
      have hpre_int : ∀ p ∈ ((e.1.trans.toList e.2).take j).map Prod.fst, ¬ ¬ sys.internal p := by
        have hpre_prob : (⟨PMF.pure s, h_τ.witnessScheduler.toScheduler⟩
            : ProbabilisticExecution sys.toSystem).probOf
            ⟨e.1.init, Seq.ofList (Seq.take j e.1.trans)⟩
            (Stream'.Seq.terminates_ofList _) ≠ 0 := by
          intro h0
          apply hpre_ne
          change h_τ.witnessScheduler.toScheduler.haltMass (PMF.pure s) pre = 0
          unfold Scheduler.haltMass
          rw [hpre]; simp only; rw [h0, zero_mul]
        have hpre_all := WeakScheduler.probOf_all_internal h_τ.witnessScheduler (PMF.pure s)
          ⟨e.1.init, Seq.ofList (Seq.take j e.1.trans)⟩ (Stream'.Seq.terminates_ofList _)
          hpre_prob
        have htoL : (⟨e.1.init, Seq.ofList (Seq.take j e.1.trans)⟩
            : AlterSeq State Label).trans.toList (Stream'.Seq.terminates_ofList _)
            = (e.1.trans.toList e.2).take j := by
          change (Seq.ofList (Seq.take j e.1.trans)).toList (Stream'.Seq.terminates_ofList _)
            = (e.1.trans.toList e.2).take j
          rw [Stream'.Seq.toList_ofList, htake]
        rw [htoL] at hpre_all
        intro lab hlab
        rw [List.mem_map] at hlab
        obtain ⟨p, hp_mem, hp_eq⟩ := hlab
        rw [← hp_eq]; exact not_not.mpr (hpre_all p hp_mem)
      -- `traceTightLabs (ofList [l]) (labs)`, then `tight_iff`.
      have h_tt : sys.traceTightLabs (Seq.ofList [l]) ((e.1.trans.toList e.2).map Prod.fst) := by
        rw [hlabs_eq]
        refine ⟨?_, ?_⟩
        · rw [Stream'.Seq.ofList_append,
            Stream'.Seq.filter_append _ _ _ (Stream'.Seq.terminates_ofList _),
            Seq.filter_ofList_eq_nil_pub (fun l => ¬ sys.internal l) _ hpre_int,
            Stream'.Seq.nil_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil,
            Stream'.Seq.filter_cons_pos l _ h_ext, Stream'.Seq.filter_nil]
        · intro last hlast
          rw [List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_singleton] at hlast
          rw [Option.some.injEq] at hlast; rw [← hlast]; exact h_ext
      have htight := (sys.tight_iff (Seq.ofList [l]) e.1 e.2).mpr h_tt
      exact ⟨htight.1, htight.2⟩
  -- Reindex any `haltMass`-weighted sum from all-terminating executions onto the
  -- tight trace-`[l]` cone `T` (the off-`T` halting mass is zero, by `hfacti`).
  have hreindex : ∀ g' : State → ENNReal,
      (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          ρ.haltMass (PMF.pure s) e * g' (e.1.endState e.2))
        = ∑' e : {e : AlterSeq State Label //
            e.trans.Terminates ∧ sys.trace e = Seq.ofList [l] ∧ sys.IsTight e},
            ρ.haltMass (PMF.pure s) ⟨e.1, e.2.1⟩ * g' (e.1.endState e.2.1) := by
    intro g'
    refine tsum_eq_tsum_of_ne_zero_bij
      (i := fun p => (⟨(p : {e : AlterSeq State Label //
          e.trans.Terminates ∧ sys.trace e = Seq.ofList [l] ∧ sys.IsTight e}).1,
            (p : {e : AlterSeq State Label //
          e.trans.Terminates ∧ sys.trace e = Seq.ofList [l] ∧ sys.IsTight e}).2.1⟩
        : {e : AlterSeq State Label // e.trans.Terminates})) ?_ ?_ ?_
    · rintro ⟨⟨e₁, h₁⟩, hp₁⟩ ⟨⟨e₂, h₂⟩, hp₂⟩ heq
      have : e₁ = e₂ := congrArg Subtype.val heq
      exact Subtype.ext (Subtype.ext this)
    · rintro ⟨e, hterm⟩ hmem
      have hhalt_ne : ρ.haltMass (PMF.pure s) ⟨e, hterm⟩ ≠ 0 := by
        intro h0; rw [Function.mem_support] at hmem; rw [h0, zero_mul] at hmem; exact hmem rfl
      obtain ⟨htr, hti⟩ := hfacti ⟨e, hterm⟩ hhalt_ne
      exact ⟨⟨⟨e, hterm, htr, hti⟩, hmem⟩, rfl⟩
    · rintro ⟨⟨e, hterm, htr, hti⟩, hp⟩; rfl
  -- Fact (ii'): on `T`, `haltMass = probOf` (mass-cancellation with `g' = 1`).
  have hfactii : ∀ e : {e : AlterSeq State Label //
        e.trans.Terminates ∧ sys.trace e = Seq.ofList [l] ∧ sys.IsTight e},
      ρ.haltMass (PMF.pure s) ⟨e.1, e.2.1⟩
        = (⟨PMF.pure s, ρ⟩ : ProbabilisticExecution sys.toSystem).probOf e.1 e.2.1 := by
    set aT : {e : AlterSeq State Label //
        e.trans.Terminates ∧ sys.trace e = Seq.ofList [l] ∧ sys.IsTight e} → ENNReal := fun e =>
      (⟨PMF.pure s, ρ⟩ : ProbabilisticExecution sys.toSystem).probOf e.1 e.2.1 with haT
    set bT : {e : AlterSeq State Label //
        e.trans.Terminates ∧ sys.trace e = Seq.ofList [l] ∧ sys.IsTight e} → ENNReal := fun e =>
      ρ.haltMass (PMF.pure s) ⟨e.1, e.2.1⟩ with hbT
    have hble : ∀ e, bT e ≤ aT e := fun e => hle ⟨e.1, e.2.1⟩
    have hsumb : (∑' e, bT e) = 1 := by
      have := hreindex (fun _ => 1)
      simp only [mul_one] at this
      rw [hbT, ← this, htotal]
    have hsuma_le : (∑' e, aT e) ≤ 1 := by
      have hkey : (∑' e, aT e) = sys.extLabMass ⟨PMF.pure s, ρ⟩ [l] (fun _ => 1) := by
        rw [sys.extLabMass_eq_tight_tsum ⟨PMF.pure s, ρ⟩ [l] (fun _ => 1)]
        refine tsum_congr (fun e => ?_); rw [haT, mul_one]
      rw [hkey, ← sys.traceProb_eq_extLabMass ⟨PMF.pure s, ρ⟩ [l]]
      exact sys.traceProb_le_one ⟨PMF.pure s, ρ⟩ (Seq.ofList [l])
    have hsumb_ne : (∑' e, bT e) ≠ ⊤ := by rw [hsumb]; exact ENNReal.one_ne_top
    have hba : (∑' e, bT e) ≤ ∑' e, aT e := ENNReal.tsum_le_tsum hble
    have hsum_eq : (∑' e, bT e) = ∑' e, aT e :=
      le_antisymm hba (by rw [hsumb]; exact hsuma_le)
    -- Cancellation via `tsum_lt_tsum`: strict inequality at any `e` would contradict equality.
    intro e
    by_contra hne_e
    have hlt : bT e < aT e := lt_of_le_of_ne (hble e) hne_e
    have := ENNReal.tsum_lt_tsum (i := e) hsumb_ne hble hlt
    rw [hsum_eq] at this
    exact (lt_irrefl _ this)
  -- Assemble Part A.
  rw [sys.extLabMass_eq_tight_tsum ⟨PMF.pure s, ρ⟩ [l] g]
  rw [show (∑' e : {e : AlterSeq State Label //
        e.trans.Terminates ∧ sys.trace e = Seq.ofList [l] ∧ sys.IsTight e},
        (⟨PMF.pure s, ρ⟩ : ProbabilisticExecution sys.toSystem).probOf e.1 e.2.1
          * g (e.1.endState e.2.1))
      = ∑' e : {e : AlterSeq State Label //
          e.trans.Terminates ∧ sys.trace e = Seq.ofList [l] ∧ sys.IsTight e},
          ρ.haltMass (PMF.pure s) ⟨e.1, e.2.1⟩ * g (e.1.endState e.2.1) from
    tsum_congr (fun e => by rw [hfactii e])]
  rw [← hreindex g]
  exact hpush g

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
/-- The **hyperStep boundary** `ν'` of the external weak step `s_prev -[a]→ μ`:
the post-distribution of the `hyperStep` inside the weak step's witness (the hidden
state distribution right after the observable `a`-transition, BEFORE the post-τ-closure).
Total: junk `PMF.pure s_prev` when there is no such external weak step. -/
noncomputable def LabelledSystem.hyperBoundary (sys : LabelledSystem State Label)
    (s_prev : State) (a : Label) (μ : PMF State) : PMF State :=
  if h : ¬ sys.internal a ∧ sys^w.step s_prev a μ then
    ((h.2.resolve_left (fun hl => h.1 hl.1)).2 : weakStep sys (PMF.pure s_prev) a μ).postDist
  else PMF.pure s_prev

open Classical in
/-- The posterior probability that the **hyperStep boundary** of `E`'s last weak step
samples to the concrete state `s`. For a nonempty terminating `E` with last transition
`(a, _)` from penult-history `E'`, this marginalizes the last-step distribution `μ`
(via `lastMuBelief`) against `(hyperBoundary E'.endState a μ) s`. For empty/non-terminating
`E`, the boundary is the initial state, so it is `if E.init = s then 1 else 0`. -/
noncomputable def ProbabilisticExecution.boundaryMarginal {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E : AlterSeq State Label) (s : State) :
    ENNReal :=
  if hT : E.trans.Terminates then
    if hne : E.trans.toList hT ≠ [] then
      let spl := Stream'.Seq.exists_split_last E.trans hT hne
      let E' : AlterSeq State Label := ⟨E.init, spl.choose⟩
      let a := spl.choose_spec.choose.1
      ∑' μ : PMF State, pe'.lastMuBelief E μ *
        (sys.hyperBoundary (E'.endState spl.choose_spec.choose_spec.choose) a μ) s
    else (if E.init = s then 1 else 0)
  else (if E.init = s then 1 else 0)

/-- The boundary marginal is a (sub)probability: `boundaryMarginal E s ≤ 1`. In the
nonempty branch the inner tsum is bounded by `∑' μ, lastMuBelief E μ * 1 = 1` since
`lastMuBelief E` is a PMF and `(hyperBoundary …) s ≤ 1`; the empty/non-terminating
branches are `0` or `1`. -/
theorem ProbabilisticExecution.boundaryMarginal_le_one {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E : AlterSeq State Label) (s : State) :
    pe'.boundaryMarginal E s ≤ 1 := by
  classical
  unfold ProbabilisticExecution.boundaryMarginal
  split_ifs with hT hne
  · -- Nonempty terminating branch: bound the inner tsum by the PMF total mass.
    calc (∑' μ : PMF State, pe'.lastMuBelief E μ *
            (sys.hyperBoundary
              ((⟨E.init, (Stream'.Seq.exists_split_last E.trans hT hne).choose⟩ :
                  AlterSeq State Label).endState
                (Stream'.Seq.exists_split_last E.trans hT hne).choose_spec.choose_spec.choose)
              (Stream'.Seq.exists_split_last E.trans hT hne).choose_spec.choose.1 μ) s)
          ≤ ∑' μ : PMF State, pe'.lastMuBelief E μ :=
            ENNReal.tsum_le_tsum (fun μ => mul_le_of_le_one_right' (PMF.coe_le_one _ s))
      _ = 1 := PMF.tsum_coe (pe'.lastMuBelief E)
  all_goals simp

/-- The boundary marginal is a genuine probability distribution over `State`:
`∑' s, boundaryMarginal E s = 1`. In the nonempty terminating branch this swaps the
`s`/`μ` sums and uses that `hyperBoundary … μ` is a `PMF State` (`PMF.tsum_coe`) and
`lastMuBelief E` is a `PMF (PMF State)`; the empty/non-terminating branches sum the
Dirac `if E.init = s then 1 else 0`. -/
theorem ProbabilisticExecution.boundaryMarginal_tsum_one {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E : AlterSeq State Label) :
    (∑' s : State, pe'.boundaryMarginal E s) = 1 := by
  classical
  unfold ProbabilisticExecution.boundaryMarginal
  split_ifs with hT hne
  · -- Nonempty terminating branch: swap `s`/`μ`, collapse each PMF total.
    rw [ENNReal.tsum_comm]
    rw [show (∑' (μ : PMF State) (s : State), pe'.lastMuBelief E μ *
          (sys.hyperBoundary
            ((⟨E.init, (Stream'.Seq.exists_split_last E.trans hT hne).choose⟩ :
                AlterSeq State Label).endState
              (Stream'.Seq.exists_split_last E.trans hT hne).choose_spec.choose_spec.choose)
            (Stream'.Seq.exists_split_last E.trans hT hne).choose_spec.choose.1 μ) s)
        = ∑' μ : PMF State, pe'.lastMuBelief E μ from
      tsum_congr (fun μ => by
        rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one])]
    exact PMF.tsum_coe (pe'.lastMuBelief E)
  · rw [tsum_eq_single E.init (fun b hb => if_neg (Ne.symm hb))]; rw [if_pos rfl]
  · rw [tsum_eq_single E.init (fun b hb => if_neg (Ne.symm hb))]; rw [if_pos rfl]

open Classical in
/-- Un-normalized **ρ-anchored** belief weight (corrected): a tight `sys^w`-history `E`
with external trace `extLabs`, weighted by the posterior prob its hidden hyperStep
boundary samples to the concrete state `s` (`boundaryMarginal`). This anchors on the
hyperStep boundary `ν'` (where concrete tight executions cut), not on `E.endState = μ`. -/
noncomputable def ProbabilisticExecution.beliefExpandAtW {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (extLabs : List Label) (s : State)
    (E : AlterSeq State Label) : ENNReal :=
  if h : E.trans.Terminates ∧ sys^w.trace E = Seq.ofList extLabs ∧ sys^w.IsTight E then
    pe'.probOf E h.1 * pe'.boundaryMarginal E s
  else 0

/-- The ρ-anchored belief weight has finite total mass (`≤ 1`): dropping the boundary
marginal (which is `≤ 1`) bounds it by the un-anchored trace-cone weight, whose tsum
is exactly `sys^w.traceProb pe' (Seq.ofList extLabs) ≤ 1`. -/
theorem ProbabilisticExecution.beliefExpandAtW_tsum_le_one {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (extLabs : List Label) (s : State) :
    (∑' E, pe'.beliefExpandAtW extLabs s E) ≤ 1 := by
  classical
  -- Bound by the un-anchored trace-cone weight (`dite` on the trace-cone predicate).
  set ub : AlterSeq State Label → ENNReal := fun E =>
    dite (E.trans.Terminates ∧ sys^w.trace E = Seq.ofList extLabs ∧ sys^w.IsTight E)
      (fun h => pe'.probOf E h.1) (fun _ => 0) with hub
  refine le_trans (ENNReal.tsum_le_tsum (g := ub) (fun E => ?_)) ?_
  · show pe'.beliefExpandAtW extLabs s E ≤ ub E
    rw [hub]
    unfold ProbabilisticExecution.beliefExpandAtW
    by_cases hP : E.trans.Terminates ∧ sys^w.trace E = Seq.ofList extLabs ∧ sys^w.IsTight E
    · simp only [dif_pos hP]
      exact mul_le_of_le_one_right' (pe'.boundaryMarginal_le_one E s)
    · simp only [dif_neg hP, le_refl]
  · -- The un-anchored tsum is the `traceProb` of the trace-cone, hence `≤ 1`.
    set S : Set (AlterSeq State Label) := {e : AlterSeq State Label |
        e.trans.Terminates ∧ sys^w.trace e = Seq.ofList extLabs ∧ sys^w.IsTight e} with hS
    have hrw : (∑' E : AlterSeq State Label, ub E)
        = sys^w.traceProb pe' (Seq.ofList extLabs) := by
      unfold LabelledSystem.traceProb
      -- Reindex the subtype `traceProb` sum to a full sum via `tsum_subtype`/`Set.indicator`.
      rw [show (∑' e : {e : AlterSeq State Label //
            e.trans.Terminates ∧ sys^w.trace e = Seq.ofList extLabs ∧ sys^w.IsTight e},
              pe'.probOf e.1 e.2.1)
          = ∑' e : S, ub e.1 from
        tsum_congr (fun e => by rw [hub]; simp only [dif_pos e.2])]
      rw [tsum_subtype S ub]
      refine tsum_congr (fun E => ?_)
      by_cases hP : E ∈ S
      · rw [Set.indicator_of_mem hP]
      · rw [Set.indicator_of_notMem hP, hub]
        simp only []
        rw [dif_neg (by rw [hS] at hP; exact hP)]
    rw [hrw]
    exact sys^w.traceProb_le_one pe' (Seq.ofList extLabs)

/-- The ρ-anchored belief normalizer is finite (`≠ ⊤`), from `≤ 1`. -/
theorem ProbabilisticExecution.beliefExpandAtW_tsum_ne_top {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (extLabs : List Label) (s : State) :
    (∑' E, pe'.beliefExpandAtW extLabs s E) ≠ ⊤ :=
  (lt_of_le_of_lt (pe'.beliefExpandAtW_tsum_le_one extLabs s) ENNReal.one_lt_top).ne

open Classical in
/-- **ρ-anchored expansion belief.** Posterior over `sys^w`-histories with external
trace `extLabs` whose hidden hyperStep boundary samples to the concrete state `s`;
falls back to the Dirac at the trivial history `⟨s, nil⟩` when the normalizer vanishes. -/
noncomputable def ProbabilisticExecution.beliefExpandAt {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (extLabs : List Label) (s : State) :
    PMF (AlterSeq State Label) :=
  if h0 : (∑' E, pe'.beliefExpandAtW extLabs s E) ≠ 0 then
    PMF.normalize (pe'.beliefExpandAtW extLabs s) h0 (pe'.beliefExpandAtW_tsum_ne_top extLabs s)
  else PMF.pure (⟨s, Seq.nil⟩ : AlterSeq State Label)

open Classical in
/-- Un-normalized **end-state-anchored** belief weight: a tight `sys^w`-history `E`
with external trace `extLabs`, weighted by the Dirac that its `endState` equals the
concrete state `s`. (Used by `anchoredNextSegment` for phase 2 — the *next* weak step,
which runs from `E.endState = s`, not from the hyperStep boundary.) -/
noncomputable def ProbabilisticExecution.beliefExpandAtEndW {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (extLabs : List Label) (s : State)
    (E : AlterSeq State Label) : ENNReal :=
  if h : E.trans.Terminates ∧ sys^w.trace E = Seq.ofList extLabs ∧ sys^w.IsTight E then
    pe'.probOf E h.1 * (if E.endState h.1 = s then 1 else 0)
  else 0

/-- The end-state-anchored belief weight has finite total mass (`≤ 1`): dropping the
Dirac (which is `≤ 1`) bounds it by the un-anchored trace-cone weight, whose tsum is
exactly `sys^w.traceProb pe' (Seq.ofList extLabs) ≤ 1`. -/
theorem ProbabilisticExecution.beliefExpandAtEndW_tsum_le_one {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (extLabs : List Label) (s : State) :
    (∑' E, pe'.beliefExpandAtEndW extLabs s E) ≤ 1 := by
  classical
  -- Bound by the un-anchored trace-cone weight (`dite` on the trace-cone predicate).
  set ub : AlterSeq State Label → ENNReal := fun E =>
    dite (E.trans.Terminates ∧ sys^w.trace E = Seq.ofList extLabs ∧ sys^w.IsTight E)
      (fun h => pe'.probOf E h.1) (fun _ => 0) with hub
  refine le_trans (ENNReal.tsum_le_tsum (g := ub) (fun E => ?_)) ?_
  · show pe'.beliefExpandAtEndW extLabs s E ≤ ub E
    rw [hub]
    unfold ProbabilisticExecution.beliefExpandAtEndW
    by_cases hP : E.trans.Terminates ∧ sys^w.trace E = Seq.ofList extLabs ∧ sys^w.IsTight E
    · simp only [dif_pos hP]
      refine mul_le_of_le_one_right' ?_
      split_ifs <;> simp
    · simp only [dif_neg hP, le_refl]
  · -- The un-anchored tsum is the `traceProb` of the trace-cone, hence `≤ 1`.
    set S : Set (AlterSeq State Label) := {e : AlterSeq State Label |
        e.trans.Terminates ∧ sys^w.trace e = Seq.ofList extLabs ∧ sys^w.IsTight e} with hS
    have hrw : (∑' E : AlterSeq State Label, ub E)
        = sys^w.traceProb pe' (Seq.ofList extLabs) := by
      unfold LabelledSystem.traceProb
      -- Reindex the subtype `traceProb` sum to a full sum via `tsum_subtype`/`Set.indicator`.
      rw [show (∑' e : {e : AlterSeq State Label //
            e.trans.Terminates ∧ sys^w.trace e = Seq.ofList extLabs ∧ sys^w.IsTight e},
              pe'.probOf e.1 e.2.1)
          = ∑' e : S, ub e.1 from
        tsum_congr (fun e => by rw [hub]; simp only [dif_pos e.2])]
      rw [tsum_subtype S ub]
      refine tsum_congr (fun E => ?_)
      by_cases hP : E ∈ S
      · rw [Set.indicator_of_mem hP]
      · rw [Set.indicator_of_notMem hP, hub]
        simp only []
        rw [dif_neg (by rw [hS] at hP; exact hP)]
    rw [hrw]
    exact sys^w.traceProb_le_one pe' (Seq.ofList extLabs)

/-- The end-state-anchored belief normalizer is finite (`≠ ⊤`), from `≤ 1`. -/
theorem ProbabilisticExecution.beliefExpandAtEndW_tsum_ne_top {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (extLabs : List Label) (s : State) :
    (∑' E, pe'.beliefExpandAtEndW extLabs s E) ≠ ⊤ :=
  (lt_of_le_of_lt (pe'.beliefExpandAtEndW_tsum_le_one extLabs s) ENNReal.one_lt_top).ne

open Classical in
/-- **End-state-anchored expansion belief.** Posterior over `sys^w`-histories with
external trace `extLabs` whose `endState` is the concrete state `s`; falls back to the
Dirac at the trivial history `⟨s, nil⟩` when the normalizer vanishes. -/
noncomputable def ProbabilisticExecution.beliefExpandAtEnd {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (extLabs : List Label) (s : State) :
    PMF (AlterSeq State Label) :=
  if h0 : (∑' E, pe'.beliefExpandAtEndW extLabs s E) ≠ 0 then
    PMF.normalize (pe'.beliefExpandAtEndW extLabs s) h0
      (pe'.beliefExpandAtEndW_tsum_ne_top extLabs s)
  else PMF.pure (⟨s, Seq.nil⟩ : AlterSeq State Label)

open Classical in
/-- **Per-weak-step belief-averaging (the soundness experiment).** Averaged over the
end-state-anchored belief weight, "draw the next weak step from `pe'.scheduler.next E`
and integrate `g` over the witness's halting from the concrete state `s`" equals "draw
the next weak step and take its result-distribution `g`-expectation `∑ t, μ t * g t`".
Sound because a nonzero `beliefExpandAtEndW … E` forces `E.endState = s`, so the drawn
step `(l, μ) ∼ pe'.scheduler.next E` is a real `sys^w.step s l μ`, whose total witness
pushes `g` forward to `∑ t, μ t * g t` (`weakStepWitness_pushforward`). -/
theorem ProbabilisticExecution.expand_step_belief_averaging
    {State Label : Type} (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (extLabs : List Label) (s : State)
    (g : State → ENNReal) :
    (∑' E : AlterSeq State Label, pe'.beliefExpandAtEndW extLabs s E *
        (∑' lω : Label × PMF State, pe'.scheduler.next E (some lω) *
          (∑' e, (Scheduler.weakStepWitnessTotal sys s lω.1 lω.2).haltMass (PMF.pure s) e
                    * g (e.1.endState e.2))))
      = ∑' E : AlterSeq State Label, pe'.beliefExpandAtEndW extLabs s E *
        (∑' lω : Label × PMF State, pe'.scheduler.next E (some lω) *
          (∑' t : State, lω.2 t * g t)) := by
  classical
  refine tsum_congr (fun E => ?_)
  -- If the belief weight vanishes the summand is `0` on both sides; else extract
  -- `E` terminating with `E.endState = s`.
  by_cases hW : pe'.beliefExpandAtEndW extLabs s E = 0
  · rw [hW, zero_mul, zero_mul]
  · refine congrArg (pe'.beliefExpandAtEndW extLabs s E * ·) ?_
    -- Extract `hT : E.trans.Terminates` and `hs : E.endState hT = s` from `hW`.
    have hP : E.trans.Terminates ∧ sys^w.trace E = Seq.ofList extLabs ∧ sys^w.IsTight E := by
      by_contra hP
      exact hW (by unfold ProbabilisticExecution.beliefExpandAtEndW; rw [dif_neg hP])
    have hT : E.trans.Terminates := hP.1
    have hs : E.endState hT = s := by
      by_contra hne
      apply hW
      unfold ProbabilisticExecution.beliefExpandAtEndW
      rw [dif_pos hP]
      simp only [hne, if_false, mul_zero]
    -- Per `lω = (l, μ)`: if `next E (some lω) ≠ 0`, the step is real, so the witness
    -- pushforward collapses the inner integral to `∑ t, μ t * g t`.
    refine tsum_congr (fun lω => ?_)
    obtain ⟨l, μ⟩ := lω
    by_cases hnext : pe'.scheduler.next E (some (l, μ)) = 0
    · rw [hnext, zero_mul, zero_mul]
    · refine congrArg (pe'.scheduler.next E (some (l, μ)) * ·) ?_
      have hmem : some (l, μ) ∈ (pe'.scheduler.next E).support := by
        rw [PMF.mem_support_iff]; exact hnext
      have hstep : sys^w.step (E.endState hT) l μ :=
        pe'.scheduler.valid E (Nat.find hT) (E.endState hT) (Nat.find_spec hT)
          (AlterSeq.stateAt_find_eq_endState E hT) l μ hmem
      rw [hs] at hstep
      rw [Scheduler.weakStepWitnessTotal_eq sys s l μ hstep,
        Scheduler.weakStepWitness_pushforward sys s l μ hstep g]

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

open Classical in
/-- Anchored successor segment: at the concrete boundary state `s`, re-sample a
`sys^w`-history `E'` ending at `s` (end-state-anchored belief `beliefExpandAtEnd`), draw
the next weak step from `pe'.scheduler.next E'` — valid from `s` since `E'.endState = s` —
and run its total witness. -/
noncomputable def Scheduler.anchoredNextSegment (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (extLabs : List Label) (s : State) :
    Scheduler sys.toSystem where
  next e' := (pe'.beliefExpandAtEnd extLabs s).bind (fun E' =>
    (pe'.scheduler.next E').bind (fun opt =>
      match opt with
      | none => PMF.pure none
      | some (l, μ) => (Scheduler.weakStepWitnessTotal sys s l μ).next e'))
  valid := by
    intro e' n s' hterm hstate l' μ' h_supp
    rw [PMF.mem_support_bind_iff] at h_supp
    obtain ⟨E', _, h_supp⟩ := h_supp
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
      (pe'.beliefExpandAt ((sys.trace e).toList
          (Stream'.Seq.terminates_map_iff.mpr
            (Stream'.Seq.terminates_filter _ _ h_term))) (e.endState h_term)).bind (fun E =>
        (pe'.lastMuBelief E).bind (fun μ_k =>
          (Scheduler.bind (Scheduler.expandPostScheduler sys E μ_k)
            (Scheduler.anchoredNextSegment sys pe' ((sys.trace e).toList
              (Stream'.Seq.terminates_map_iff.mpr
                (Stream'.Seq.terminates_filter _ _ h_term))))).next
              (sys.internalSuffix e)))
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
          (pe'.beliefExpandAt ((sys.trace e).toList
              (Stream'.Seq.terminates_map_iff.mpr
                (Stream'.Seq.terminates_filter _ _ h_term'))) (e.endState h_term')).bind (fun E =>
            (pe'.lastMuBelief E).bind (fun μ_k =>
              (Scheduler.bind (Scheduler.expandPostScheduler sys E μ_k)
                (Scheduler.anchoredNextSegment sys pe' ((sys.trace e).toList
                  (Stream'.Seq.terminates_map_iff.mpr
                    (Stream'.Seq.terminates_filter _ _ h_term'))))).next
                  (sys.internalSuffix e)))
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
      Scheduler.bind (Scheduler.expandPostScheduler sys E μ_k)
        (Scheduler.anchoredNextSegment sys pe' ((sys.trace e).toList
          (Stream'.Seq.terminates_map_iff.mpr
            (Stream'.Seq.terminates_filter _ _ h_term))))
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

/-- **State-anchored belief normalizer cancellation** (mirror of
`beliefTC_normalize_cancel`). Multiplying the (possibly un-normalized)
`beliefExpandAt`-expectation by its normalizer recovers the un-normalized
`beliefExpandAtW`-weighted sum; covers the `Z = 0` fallback too. -/
theorem ProbabilisticExecution.beliefExpandAt_normalize_cancel
    {State Label : Type} {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (extLabs : List Label) (s : State)
    (w : AlterSeq State Label → ENNReal) :
    (∑' E, pe'.beliefExpandAtW extLabs s E) *
        (∑' E, pe'.beliefExpandAt extLabs s E * w E)
      = ∑' E, pe'.beliefExpandAtW extLabs s E * w E := by
  classical
  by_cases hZ : (∑' E, pe'.beliefExpandAtW extLabs s E) = 0
  · rw [hZ, zero_mul]
    have hz : ∀ E, pe'.beliefExpandAtW extLabs s E = 0 := ENNReal.tsum_eq_zero.mp hZ
    exact (ENNReal.tsum_eq_zero.mpr (fun E => by rw [hz E, zero_mul])).symm
  · have hZtop : (∑' E, pe'.beliefExpandAtW extLabs s E) ≠ ⊤ :=
      pe'.beliefExpandAtW_tsum_ne_top extLabs s
    have hbel : ∀ E, pe'.beliefExpandAt extLabs s E
        = pe'.beliefExpandAtW extLabs s E * (∑' E', pe'.beliefExpandAtW extLabs s E')⁻¹ := by
      intro E
      unfold ProbabilisticExecution.beliefExpandAt
      rw [dif_pos hZ, PMF.normalize_apply]
    rw [show (∑' E, pe'.beliefExpandAt extLabs s E * w E)
          = ∑' E, (pe'.beliefExpandAtW extLabs s E *
              (∑' E', pe'.beliefExpandAtW extLabs s E')⁻¹) * w E from
        tsum_congr (fun E => by rw [hbel E]),
      ← ENNReal.tsum_mul_left]
    refine tsum_congr (fun E => ?_)
    rw [show (∑' E', pe'.beliefExpandAtW extLabs s E') *
          (pe'.beliefExpandAtW extLabs s E *
            (∑' E', pe'.beliefExpandAtW extLabs s E')⁻¹ * w E)
          = ((∑' E', pe'.beliefExpandAtW extLabs s E') *
              (∑' E', pe'.beliefExpandAtW extLabs s E')⁻¹) *
            (pe'.beliefExpandAtW extLabs s E * w E) by ring,
      ENNReal.mul_inv_cancel hZ hZtop, one_mul]

/-- **End-state-anchored belief normalizer cancellation** (trivial mirror of
`beliefExpandAt_normalize_cancel`, for the `beliefExpandAtEnd` belief used by
`anchoredNextSegment`). Multiplying the (possibly un-normalized) `beliefExpandAtEnd`-
expectation by its normalizer recovers the un-normalized `beliefExpandAtEndW`-weighted
sum; covers the `Z = 0` fallback too. -/
theorem ProbabilisticExecution.beliefExpandAtEnd_normalize_cancel
    {State Label : Type} {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (extLabs : List Label) (s : State)
    (w : AlterSeq State Label → ENNReal) :
    (∑' E, pe'.beliefExpandAtEndW extLabs s E) *
        (∑' E, pe'.beliefExpandAtEnd extLabs s E * w E)
      = ∑' E, pe'.beliefExpandAtEndW extLabs s E * w E := by
  classical
  by_cases hZ : (∑' E, pe'.beliefExpandAtEndW extLabs s E) = 0
  · rw [hZ, zero_mul]
    have hz : ∀ E, pe'.beliefExpandAtEndW extLabs s E = 0 := ENNReal.tsum_eq_zero.mp hZ
    exact (ENNReal.tsum_eq_zero.mpr (fun E => by rw [hz E, zero_mul])).symm
  · have hZtop : (∑' E, pe'.beliefExpandAtEndW extLabs s E) ≠ ⊤ :=
      pe'.beliefExpandAtEndW_tsum_ne_top extLabs s
    have hbel : ∀ E, pe'.beliefExpandAtEnd extLabs s E
        = pe'.beliefExpandAtEndW extLabs s E * (∑' E', pe'.beliefExpandAtEndW extLabs s E')⁻¹ := by
      intro E
      unfold ProbabilisticExecution.beliefExpandAtEnd
      rw [dif_pos hZ, PMF.normalize_apply]
    rw [show (∑' E, pe'.beliefExpandAtEnd extLabs s E * w E)
          = ∑' E, (pe'.beliefExpandAtEndW extLabs s E *
              (∑' E', pe'.beliefExpandAtEndW extLabs s E')⁻¹) * w E from
        tsum_congr (fun E => by rw [hbel E]),
      ← ENNReal.tsum_mul_left]
    refine tsum_congr (fun E => ?_)
    rw [show (∑' E', pe'.beliefExpandAtEndW extLabs s E') *
          (pe'.beliefExpandAtEndW extLabs s E *
            (∑' E', pe'.beliefExpandAtEndW extLabs s E')⁻¹ * w E)
          = ((∑' E', pe'.beliefExpandAtEndW extLabs s E') *
              (∑' E', pe'.beliefExpandAtEndW extLabs s E')⁻¹) *
            (pe'.beliefExpandAtEndW extLabs s E * w E) by ring,
      ENNReal.mul_inv_cancel hZ hZtop, one_mul]

open Classical in
/-- The pe'-side **ρ-expectation**: total `probOf`-mass of tight trace-`labs`
`sys^w`-histories, each weighted by the `g`-expectation over its hidden hyperStep
boundary distribution (`boundaryMarginal`). This is the invariant matched by the
expand construction's external level mass (cut at the hyperStep boundary ν'). -/
noncomputable def ProbabilisticExecution.rhoExpect {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (labs : List Label) (g : State → ENNReal) :
    ENNReal :=
  ∑' E : AlterSeq State Label,
    dite (E.trans.Terminates ∧ sys^w.trace E = Seq.ofList labs ∧ sys^w.IsTight E)
      (fun h => pe'.probOf E h.1 * (∑' s : State, pe'.boundaryMarginal E s * g s)) (fun _ => 0)

open Classical in
/-- **The single-weak-step expansion `g`-expectation from a tight-`labs` boundary state
`s'`.** This is the integrand fed to the IH in `expand_extLabMass_step_g`: averaged over
the boundary-anchored expansion belief `beliefExpandAt labs s'` (the `sys^w`-histories
with external trace `labs` whose hidden hyperStep boundary samples to `s'`), draw the
next external weak step `(l, μ) ∼ pe'.scheduler.next E` and integrate `g` over its
*hyperStep boundary* `ν' = hyperBoundary s' l μ` (the post-distribution of the observable
`l`-transition, where the next tight concrete execution cuts). Only the appended label
`l` contributes (the `if lω.1 = l`); other emissions are masked, matching the trace
constraint that the appended external label is exactly `l`.

This is the `expand`-side analogue of `lower_kernel_g_sum`'s belief-averaged kernel
`g`-sum, re-anchored at the concrete boundary state. -/
noncomputable def ProbabilisticExecution.segExp {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (labs : List Label) (l : Label)
    (g : State → ENNReal) (s' : State) : ENNReal :=
  ∑' E : AlterSeq State Label, pe'.beliefExpandAt labs s' E *
    (∑' lω : Label × PMF State, pe'.scheduler.next E (some lω) *
      (if lω.1 = l then (∑' t : State, (sys.hyperBoundary s' lω.1 lω.2) t * g t) else 0))

/-- **`g = 1` slice of `rhoExpect`.** At `g = 1` the boundary marginal sums to `1`
(`boundaryMarginal_tsum_one`), so each tight-`labs` history contributes its plain
`probOf`, recovering `sys^w.extLabMass pe' labs 1` via the subtype-sum form
(`extLabMass_eq_tight_tsum`). -/
theorem ProbabilisticExecution.rhoExpect_one {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (labs : List Label) :
    pe'.rhoExpect labs (fun _ => 1) = sys^w.extLabMass pe' labs (fun _ => 1) := by
  classical
  rw [sys^w.extLabMass_eq_tight_tsum pe' labs (fun _ => 1)]
  unfold ProbabilisticExecution.rhoExpect
  -- Per-`E`, collapse the boundary-marginal `g = 1` integral to `1`.
  rw [show (∑' E : AlterSeq State Label,
        dite (E.trans.Terminates ∧ sys^w.trace E = Seq.ofList labs ∧ sys^w.IsTight E)
          (fun h => pe'.probOf E h.1 * (∑' s : State, pe'.boundaryMarginal E s * 1)) (fun _ => 0))
      = ∑' E : AlterSeq State Label,
          dite (E.trans.Terminates ∧ sys^w.trace E = Seq.ofList labs ∧ sys^w.IsTight E)
            (fun h => pe'.probOf E h.1) (fun _ => 0) from
    tsum_congr (fun E => by
      by_cases hc : E.trans.Terminates ∧ sys^w.trace E = Seq.ofList labs ∧ sys^w.IsTight E
      · rw [dif_pos hc, dif_pos hc]
        simp_rw [mul_one]
        rw [pe'.boundaryMarginal_tsum_one E, mul_one]
      · rw [dif_neg hc, dif_neg hc])]
  -- Bridge the `dite`-over-all-`E` sum to the subtype sum (mirror of
  -- `beliefExpandAtW_tsum_le_one`'s `traceProb` reduction).
  set S : Set (AlterSeq State Label) := {e : AlterSeq State Label |
      e.trans.Terminates ∧ sys^w.trace e = Seq.ofList labs ∧ sys^w.IsTight e} with hS
  set ub : AlterSeq State Label → ENNReal := fun E =>
    dite (E.trans.Terminates ∧ sys^w.trace E = Seq.ofList labs ∧ sys^w.IsTight E)
      (fun h => pe'.probOf E h.1) (fun _ => 0) with hub
  rw [show (∑' e : {e : AlterSeq State Label //
        e.trans.Terminates ∧ sys^w.trace e = Seq.ofList labs ∧ sys^w.IsTight e},
          pe'.probOf e.1 e.2.1 * (1 : ENNReal))
      = ∑' e : S, ub e.1 from
    tsum_congr (fun e => by rw [hub]; simp only [dif_pos e.2, mul_one])]
  rw [tsum_subtype S ub]
  refine (tsum_congr (fun E => ?_)).symm
  by_cases hP : E ∈ S
  · rw [Set.indicator_of_mem hP]
  · rw [Set.indicator_of_notMem hP]
    have hP' : ¬ (E.trans.Terminates ∧ sys^w.trace E = Seq.ofList labs ∧ sys^w.IsTight E) := hP
    rw [dif_neg hP']

/-- A tight execution with empty external trace has no transitions: `trace E = nil`
and `IsTight E` force the full label list to be `[]`, hence `E.trans = nil`. -/
theorem tight_trace_nil {State Label : Type} (ls : LabelledSystem State Label)
    (E : AlterSeq State Label) (hT : E.trans.Terminates)
    (htr : ls.trace E = Seq.ofList ([] : List Label)) (hti : ls.IsTight E) :
    E.trans = Seq.nil := by
  classical
  have htt : ls.traceTightLabs (Seq.ofList ([] : List Label)) ((E.trans.toList hT).map Prod.fst) :=
    (ls.tight_iff (Seq.ofList ([] : List Label)) E hT).mp ⟨htr, hti⟩
  -- The full label list is `[]`.
  have hlabs_nil : (E.trans.toList hT).map Prod.fst = [] := by
    have h_filter0 : (Seq.ofList ((E.trans.toList hT).map Prod.fst)).filter
        (fun l => ¬ ls.internal l) = Seq.nil := by
      have := htt.1; rw [Stream'.Seq.ofList_nil] at this; exact this
    by_contra h_ne
    -- A nonempty list: tightness forces the last to be external, contradiction with empty filter.
    obtain ⟨last, h_gl⟩ : ∃ last, ((E.trans.toList hT).map Prod.fst).getLast? = some last := by
      rcases h_last_opt : ((E.trans.toList hT).map Prod.fst).getLast? with _ | last
      · exact absurd (List.getLast?_eq_none_iff.mp h_last_opt) h_ne
      · exact ⟨last, rfl⟩
    have h_ext : ¬ ls.internal last := htt.2 last h_gl
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp h_gl
    rw [hys] at h_filter0
    rw [Stream'.Seq.ofList_append, Stream'.Seq.filter_append _ _ _
      (Stream'.Seq.terminates_ofList ys)] at h_filter0
    rw [Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil,
      Stream'.Seq.filter_cons_pos last _ h_ext] at h_filter0
    have h_term : (Stream'.Seq.filter (fun l => ¬ ls.internal l) (Seq.ofList ys)).Terminates :=
      Stream'.Seq.terminates_filter _ _ (Stream'.Seq.terminates_ofList ys)
    have h_get := Stream'.Seq.get?_append_find h_term
      (Seq.cons last (Stream'.Seq.filter (fun l => ¬ ls.internal l) Seq.nil)) 0
    rw [h_filter0] at h_get
    simp only [Stream'.Seq.get?_nil, Stream'.Seq.get?_cons_zero] at h_get
    cases h_get
  -- `map Prod.fst (toList) = []` ⇒ `toList = []` ⇒ `trans = nil`.
  have h0 : Stream'.Seq.length' E.trans = 0 := by
    rw [← Stream'.Seq.length'_map (f := Prod.fst)]
    have hmapnil : E.trans.map Prod.fst = Seq.ofList ([] : List Label) := by
      conv_lhs => rw [← Stream'.Seq.ofList_toList E.trans hT]
      rw [Seq.map_ofList_pub, hlabs_nil]
    rw [hmapnil, Stream'.Seq.ofList_nil, Stream'.Seq.length'_nil]
  exact (Stream'.Seq.length'_eq_zero_iff_nil E.trans).mp h0

/-- **`[]`-base of the `rhoExpect` invariant.** The only tight trace-`[]`
`sys^w`-history is `⟨s₀, nil⟩`, whose boundary marginal is the Dirac at `s₀`; so
`rhoExpect [] g` is the `pe'`-initial `g`-expectation. -/
theorem ProbabilisticExecution.rhoExpect_nil {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (g : State → ENNReal) :
    pe'.rhoExpect [] g = ∑' s₀ : State, pe'.initState s₀ * g s₀ := by
  classical
  unfold ProbabilisticExecution.rhoExpect
  -- Per-`E`, the summand vanishes unless `E.trans = nil`, where it becomes
  -- `initState E.init * g E.init`. Bijection with `s₀ ↦ ⟨s₀, nil⟩`.
  set f : AlterSeq State Label → ENNReal := fun E =>
    dite (E.trans.Terminates ∧ sys^w.trace E = Seq.ofList ([] : List Label) ∧ sys^w.IsTight E)
      (fun h => pe'.probOf E h.1 * (∑' s : State, pe'.boundaryMarginal E s * g s)) (fun _ => 0)
      with hf_def
  set rhs : State → ENNReal := fun s₀ => pe'.initState s₀ * g s₀ with hrhs_def
  have f_supp_cond : ∀ E : AlterSeq State Label, f E ≠ 0 →
      E.trans.Terminates ∧ sys^w.trace E = Seq.ofList ([] : List Label) ∧ sys^w.IsTight E := by
    intro E hE
    by_contra hc
    rw [hf_def] at hE; simp only at hE; rw [dif_neg hc] at hE; exact hE rfl
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun s₀ => (⟨(s₀ : State), Seq.nil⟩ : AlterSeq State Label)) ?hinj ?hf ?hfg
  case hinj =>
    rintro a b hab
    exact Subtype.ext (congrArg AlterSeq.init hab)
  case hf =>
    intro E he_mem
    have hE := f_supp_cond E (Function.mem_support.mp he_mem)
    have h_nil : E.trans = Seq.nil := tight_trace_nil sys^w E hE.1 hE.2.1 hE.2.2
    have h_reassemble : (⟨E.init, Seq.nil⟩ : AlterSeq State Label) = E :=
      congrArg₂ AlterSeq.mk rfl h_nil.symm
    have hf_pos : rhs E.init ≠ 0 := by
      rw [hrhs_def]; simp only
      intro hzero
      apply Function.mem_support.mp he_mem
      change f E = 0
      rw [hf_def]; simp only; rw [dif_pos hE]
      have h_prob : pe'.probOf E hE.1 = pe'.initState E.init := by
        have key : ∀ (A : AlterSeq State Label) (hA : A.trans.Terminates),
            A = (⟨E.init, Seq.nil⟩ : AlterSeq State Label) →
            pe'.probOf A hA = pe'.probOf (⟨E.init, Seq.nil⟩ : AlterSeq State Label)
              Stream'.Seq.terminates_nil := by rintro A hA rfl; rfl
        rw [key E hE.1 h_reassemble.symm, ProbabilisticExecution.probOf_nil,
          ProbabilisticExecution.init_eq_initState]
      -- the boundary integral collapses to `g E.init`.
      have h_bound : (∑' s : State, pe'.boundaryMarginal E s * g s) = g E.init := by
        have hbm : ∀ s : State, pe'.boundaryMarginal E s = (if E.init = s then 1 else 0) := by
          intro s
          unfold ProbabilisticExecution.boundaryMarginal
          rw [dif_pos hE.1, dif_neg (by
            rw [show E.trans.toList hE.1 = [] from by
              rw [Stream'.Seq.toList_congr_pub h_nil hE.1 Stream'.Seq.terminates_nil,
                Stream'.Seq.toList_nil]]
            simp)]
        simp_rw [hbm]
        rw [tsum_eq_single E.init (fun b hb => by rw [if_neg (Ne.symm hb), zero_mul]),
          if_pos rfl, one_mul]
      rw [h_prob, h_bound]; exact hzero
    exact ⟨⟨E.init, hf_pos⟩, by simp only; exact h_reassemble⟩
  case hfg =>
    rintro x
    set s₀ := (x : State) with hs₀_def
    have h_cond : (⟨s₀, Seq.nil⟩ : AlterSeq State Label).trans.Terminates ∧
        sys^w.trace (⟨s₀, Seq.nil⟩ : AlterSeq State Label) = Seq.ofList ([] : List Label) ∧
        sys^w.IsTight (⟨s₀, Seq.nil⟩ : AlterSeq State Label) := by
      refine ⟨Stream'.Seq.terminates_nil, ?_, ?_⟩
      · rw [LabelledSystem.trace_init, Stream'.Seq.ofList_nil]
      · left; exact Stream'.Seq.terminatedAt_zero_iff.mpr rfl
    change f (⟨s₀, Seq.nil⟩ : AlterSeq State Label) = rhs s₀
    rw [hf_def]; simp only; rw [dif_pos h_cond]
    rw [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState]
    have h_bound : (∑' s : State, pe'.boundaryMarginal (⟨s₀, Seq.nil⟩ : AlterSeq State Label) s
          * g s) = g s₀ := by
      have hbm : ∀ s : State,
          pe'.boundaryMarginal (⟨s₀, Seq.nil⟩ : AlterSeq State Label) s
            = (if s₀ = s then 1 else 0) := by
        intro s
        unfold ProbabilisticExecution.boundaryMarginal
        rw [dif_pos Stream'.Seq.terminates_nil, dif_neg (by
          rw [Stream'.Seq.toList_nil]; simp)]
      simp_rw [hbm]
      rw [tsum_eq_single s₀ (fun b hb => by rw [if_neg (Ne.symm hb), zero_mul]),
        if_pos rfl, one_mul]
    rw [h_bound]

/-- **(I) External-boundary disintegration of `expand`'s level mass (the hard part).**
Appending one external label `l`, the `expand` construction's tight trace-`(labs++[l])`
external level mass factors at its last external label into the tight trace-`labs`
prefix (governed by the IH) and a successor SEGMENT, whose belief-averaged segment
`g`-integral — over the boundary-anchored expansion belief `beliefExpandAt labs s'`, then
the carried post-τ `expandPostScheduler`, then `anchoredNextSegment`'s next external weak
step and its witness — telescopes to `segExp labs l g s'` at each tight-`labs` boundary
state `s'`. Concretely:
`extLabMass D (labs++[l]) g = extLabMass D labs (segExp labs l g)`
where `D = ⟨pure init, expand sys pe'⟩`.

PROOF SKETCH (mirrors `lower_labProb_eq_aux`'s step, but per external label is a SEGMENT
and `expand`'s belief RE-ANCHORS): via `extLabMass_eq_tight_tsum` on both sides, a tight
trace-`(labs++[l])` exec `e` of `D` splits at its last external transition into a tight
trace-`labs` prefix `e_pre` (end-state `s' = e_pre.endState`) and a segment `seg` from
`s'`. Along `seg` the trace stays `labs`, so `expand.next` at `e_pre ⊕ seg-prefix` runs
the carried segment scheduler on `internalSuffix = seg-prefix` (since `e_pre` ends
external ⟹ `internalSuffix(e_pre ⊕ internal-seg-prefix) = seg-prefix`). The re-anchored
belief's own segment `g`-integral, averaged, telescopes to `segExp` by
`expand_step_belief_averaging` (external draw) + `extLabMass_segment_bridge` /
`weakTau.integrate` (τ-closures) + `beliefExpandAt(End)_normalize_cancel`. This is the
combinatorial segment-level disintegration of the belief-bind `expand.next` — it has NO
template and is the genuine research crux. -/
theorem expand_extLabMass_disintegrate (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (h_init : pe'.initState = PMF.pure sys^w.toSystem.init)
    (labs : List Label) (l : Label) (g : State → ENNReal) :
    sys.extLabMass ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ (labs ++ [l]) g
      = sys.extLabMass ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ labs
          (pe'.segExp labs l g) := by
  sorry

open Classical in
/-- Under `hExt`, `rhoExpect labs g` collapses to a sum over `sys^w`-histories whose
**label list is exactly `labs`** (no internal labels interspersed), weighted by
`probOf · boundaryMarginal`-`g`-integral. (Mirror of `extLabMass_eq_labMass_noInternal`,
keeping the `boundaryMarginal` weight: tight trace-`labs` histories with label list ≠
`labs` carry an internal label, hence `probOf = 0`; and conversely.) -/
theorem ProbabilisticExecution.rhoExpect_eq_labelCone {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (labs : List Label) (g : State → ENNReal) :
    pe'.rhoExpect labs g
      = ∑' E : AlterSeq State Label,
          dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
            (fun h => pe'.probOf E h.1 * (∑' s : State, pe'.boundaryMarginal E s * g s))
            (fun _ => 0) := by
  classical
  unfold ProbabilisticExecution.rhoExpect
  refine tsum_congr (fun E => ?_)
  -- Both summands carry the same weight `W` when their predicate holds; we show the
  -- two `dite`s agree by case analysis on termination + internal-label presence.
  by_cases hT : E.trans.Terminates
  · -- The label list of `E`.
    set labsE : List Label := (E.trans.toList hT).map Prod.fst with hlabsE
    have hmapE : E.trans.map Prod.fst = Seq.ofList labsE := by
      rw [hlabsE, ← Seq.map_ofList_pub, Stream'.Seq.ofList_toList E.trans hT]
    by_cases hext : ∀ p ∈ E.trans.toList hT, ¬ sys.internal p.1
    · -- All-external: tightness ⇔ label list = labs (mirror of `tight_iff`/no-internal).
      -- Each label of `E` is external.
      have hextlab : ∀ lab ∈ labsE, ¬ (sys^w).internal lab := by
        intro lab hlab
        obtain ⟨p, hp_mem, hp_eq⟩ := List.mem_map.mp hlab
        simpa [LabelledSystem.weakClosure] using (hp_eq ▸ hext p hp_mem)
      -- The trace-tight predicate over `labsE` reduces to `labsE = labs`.
      have hfilter : (Seq.ofList labsE).filter (fun lab => ¬ (sys^w).internal lab)
          = Seq.ofList labsE := by
        rw [ofList_filter_helper]
        congr 1
        rw [List.filter_eq_self]
        intro lab hlab; simpa using hextlab lab hlab
      have htt_iff : sys^w.traceTightLabs (Seq.ofList labs) labsE ↔ labsE = labs := by
        unfold LabelledSystem.traceTightLabs
        rw [hfilter]
        constructor
        · rintro ⟨h1, _⟩; exact Stream'.Seq.ofList_injective h1
        · rintro rfl
          refine ⟨rfl, ?_⟩
          intro lab hlab; exact hextlab lab (List.mem_of_getLast? hlab)
      -- Bridge the tight-trace dite to the `traceTightLabs` predicate via `tight_iff`.
      have htight_iff : (sys^w.trace E = Seq.ofList labs ∧ sys^w.IsTight E)
          ↔ sys^w.traceTightLabs (Seq.ofList labs) labsE :=
        sys^w.tight_iff (Seq.ofList labs) E hT
      by_cases hlab_eq : labsE = labs
      · -- Matching label list: both dites fire with the same weight.
        rw [dif_pos ⟨hT, (htight_iff.mpr (htt_iff.mpr hlab_eq)).1,
              (htight_iff.mpr (htt_iff.mpr hlab_eq)).2⟩,
          dif_pos ⟨hT, by rw [hmapE, hlab_eq]⟩]
      · -- Mismatched label list: both dites are off.
        rw [dif_neg (fun h => hlab_eq (htt_iff.mp (htight_iff.mp ⟨h.2.1, h.2.2⟩))),
          dif_neg (fun h => hlab_eq (by
            have : Seq.ofList labsE = Seq.ofList labs := by rw [← hmapE]; exact h.2
            exact Stream'.Seq.ofList_injective this))]
    · -- Has an internal label ⟹ `probOf E = 0`, both `dite`s collapse to `0`.
      push Not at hext
      obtain ⟨p, hp_mem, hp_int⟩ := hext
      have hprob0 : pe'.probOf E hT = 0 := by
        have hreassemble : (⟨E.init, Seq.ofList (E.trans.toList hT)⟩ : AlterSeq State Label) = E :=
          congrArg₂ AlterSeq.mk rfl (Stream'.Seq.ofList_toList E.trans hT)
        have hterm : (Seq.ofList (E.trans.toList hT) : Seq (Label × State)).Terminates :=
          Stream'.Seq.terminates_ofList _
        have hprob : pe'.probOf E hT
            = pe'.probOf ⟨E.init, Seq.ofList (E.trans.toList hT)⟩ hterm := by
          have key : ∀ (E' : AlterSeq State Label) (hE : E'.trans.Terminates),
              E' = (⟨E.init, Seq.ofList (E.trans.toList hT)⟩ : AlterSeq State Label) →
              pe'.probOf E' hE
                = pe'.probOf ⟨E.init, Seq.ofList (E.trans.toList hT)⟩ hterm := by
            rintro E' hE rfl; rfl
          exact key E hT hreassemble.symm
        rw [hprob, pe'.probOf_ofList_eq_zero_of_internal_mem hExt E.init
          (E.trans.toList hT) hterm ⟨p, hp_mem, hp_int⟩]
      by_cases h1 : E.trans.Terminates ∧ sys^w.trace E = Seq.ofList labs ∧ sys^w.IsTight E
      · rw [dif_pos h1, hprob0, zero_mul]
        by_cases h2 : E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs
        · rw [dif_pos h2, hprob0, zero_mul]
        · rw [dif_neg h2]
      · rw [dif_neg h1]
        by_cases h2 : E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs
        · rw [dif_pos h2, hprob0, zero_mul]
        · rw [dif_neg h2]
  · -- Non-terminating: both predicates fail (they require `Terminates`).
    rw [dif_neg (fun h => hT h.1), dif_neg (fun h => hT h.1)]

open Classical in
/-- **`lastMuBelief` of an appended history (the linchpin cancellation).** For
`E = ⟨s₀, sq ++ [(a, sk)]⟩` with preceding history `E_pre = ⟨s₀, sq⟩` (terminating),
the posterior over the last-emitted distribution `μ`, weighted by the cancellation,
satisfies
`probOf E · lastMuBelief E μ = probOf E_pre · next E_pre (some (a, μ)) · μ sk`.
(When the last-step kernel `kernel E_pre (a, sk)` vanishes, both sides are `0`:
`probOf E = probOf E_pre · kernel E_pre (a, sk) = 0`.) -/
theorem ProbabilisticExecution.probOf_mul_lastMuBelief_append {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (s₀ : State) (sq : Seq (Label × State)) (h_sq : sq.Terminates)
    (a : Label) (sk : State)
    (h_app : (sq.append (Seq.cons (a, sk) Seq.nil)).Terminates) (μ : PMF State) :
    pe'.probOf ⟨s₀, sq.append (Seq.cons (a, sk) Seq.nil)⟩ h_app *
        pe'.lastMuBelief ⟨s₀, sq.append (Seq.cons (a, sk) Seq.nil)⟩ μ
      = pe'.probOf ⟨s₀, sq⟩ h_sq *
          (pe'.scheduler.next ⟨s₀, sq⟩ (some (a, μ)) * μ sk) := by
  classical
  -- Abbreviations for the appended history `E` and prefix `Epre`.
  have hprobE : pe'.probOf ⟨s₀, sq.append (Seq.cons (a, sk) Seq.nil)⟩ h_app
      = pe'.probOf ⟨s₀, sq⟩ h_sq * pe'.kernel ⟨s₀, sq⟩ (a, sk) :=
    pe'.probOf_append_singleton s₀ sq h_sq (a, sk) h_app
  have hsingle : (Seq.cons (a, sk) Seq.nil : Seq (Label × State)).Terminates :=
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
  -- The `toList` of `E.trans` ends with `(a, sk)`.
  have htl : (sq.append (Seq.cons (a, sk) Seq.nil)).toList h_app = sq.toList h_sq ++ [(a, sk)] := by
    rw [Stream'.Seq.toList_append sq (Seq.cons (a, sk) Seq.nil) h_sq hsingle h_app,
      Stream'.Seq.toList_cons, Stream'.Seq.toList_nil]
  -- `E.trans.toList` is nonempty (it ends with `(a, sk)`).
  have hne : (sq.append (Seq.cons (a, sk) Seq.nil)).toList h_app ≠ [] := by rw [htl]; simp
  -- `getLast` of the appended toList is `(a, sk)` (proof-irrelevant transport).
  have hgetLast : ∀ (h' : (sq.append (Seq.cons (a, sk) Seq.nil)).toList h_app ≠ []),
      ((sq.append (Seq.cons (a, sk) Seq.nil)).toList h_app).getLast h' = (a, sk) := by
    intro h'
    have hgl? : ((sq.append (Seq.cons (a, sk) Seq.nil)).toList h_app).getLast? = some (a, sk) := by
      rw [htl]; exact List.getLast?_concat
    exact List.getLast_of_getLast?_eq_some hgl?
  -- Resolve the `exists_split_last` data for `E`, quantified over the nonempty proof
  -- (so it matches the internal proof instance produced by `lastMuBelief`).
  have hlast : ∀ (h' : (sq.append (Seq.cons (a, sk) Seq.nil)).toList h_app ≠ []),
      (Stream'.Seq.exists_split_last (sq.append (Seq.cons (a, sk) Seq.nil))
        h_app h').choose_spec.choose = (a, sk) := by
    intro h'
    have h := (Stream'.Seq.exists_split_last (sq.append (Seq.cons (a, sk) Seq.nil))
      h_app h').choose_spec.choose_spec.choose_spec.2.2
    rw [h, hgetLast]
  have hlast1 : ∀ (h' : (sq.append (Seq.cons (a, sk) Seq.nil)).toList h_app ≠ []),
      (Stream'.Seq.exists_split_last (sq.append (Seq.cons (a, sk) Seq.nil))
        h_app h').choose_spec.choose.1 = a := fun h' => by rw [hlast h']
  have hlast2 : ∀ (h' : (sq.append (Seq.cons (a, sk) Seq.nil)).toList h_app ≠ []),
      (Stream'.Seq.exists_split_last (sq.append (Seq.cons (a, sk) Seq.nil))
        h_app h').choose_spec.choose.2 = sk := fun h' => by rw [hlast h']
  -- The chosen `prev` equals `sq` (same `toList`).
  have hprev_seq : ∀ (h' : (sq.append (Seq.cons (a, sk) Seq.nil)).toList h_app ≠ []),
      (Stream'.Seq.exists_split_last (sq.append (Seq.cons (a, sk) Seq.nil))
        h_app h').choose = sq := by
    intro h'
    have hprev_term := (Stream'.Seq.exists_split_last (sq.append (Seq.cons (a, sk) Seq.nil))
      h_app h').choose_spec.choose_spec.choose
    have htoL := (Stream'.Seq.exists_split_last (sq.append (Seq.cons (a, sk) Seq.nil))
      h_app h').choose_spec.choose_spec.choose_spec.2.1
    rw [← Stream'.Seq.ofList_toList (Stream'.Seq.exists_split_last
      (sq.append (Seq.cons (a, sk) Seq.nil)) h_app h').choose hprev_term, htoL]
    conv_lhs => rw [htl]
    simp [Stream'.Seq.ofList_toList sq h_sq]
  -- Unfold `lastMuBelief` at `E`. The `dite` resolves through `hlast1`/`hlast2`/`hprev_seq`:
  -- the chosen last transition is `(a, sk)` and the chosen prefix-seq is `sq`. The only
  -- residual is a `choose`-defeq plumbing step: the *internal* `exists_split_last` proof
  -- instance produced by `lastMuBelief` (`lastMuBelief._proof_*`, over `{init,trans}.trans`)
  -- is propositionally — but not syntactically — the `exists_split_last (sq.append …)` term
  -- of `hlast1`/`hlast2`/`hprev_seq`, so neither `simp`/`rw`/`conv` fires under the `dite`.
  -- ISOLATED SUB-LEMMA (the EXACT residual goal, after `unfold lastMuBelief;
  --   rw [dif_pos h_app, dif_pos hne]`):
  -- ⊢ (dite (∑' μ, next ⟨s₀, spl.choose⟩ (some (spl.choose_spec.choose.1, μ))
  --            * μ spl.choose_spec.choose.2 ≠ 0)
  --       (fun h0 => PMF.normalize (fun μ => next ⟨s₀, spl.choose⟩
  --            (some (spl.choose_spec.choose.1, μ)) * μ spl.choose_spec.choose.2) h0 _ μ)
  --       (fun _ => (PMF.pure (PMF.pure s₀)) μ))
  --   = (dite (∑' ν, next ⟨s₀, sq⟩ (some (a, ν)) * ν sk ≠ 0)
  --       (fun h0 => next ⟨s₀, sq⟩ (some (a, μ)) * μ sk * (∑' ν, …)⁻¹)
  --       (fun _ => (PMF.pure (PMF.pure s₀)) μ))
  -- where `spl = exists_split_last (sq.append (cons (a,sk) nil)) h_app hne`, given
  -- `hlast1 : spl.choose_spec.choose.1 = a`, `hlast2 : … .2 = sk`, `hprev_seq : spl.choose = sq`.
  -- Closable by aligning the internal proof instance with `Subsingleton.elim` then
  -- `rw [hlast1, hlast2, hprev_seq]` once the `⋯` matches `spl` syntactically.
  have hlmb : pe'.lastMuBelief ⟨s₀, sq.append (Seq.cons (a, sk) Seq.nil)⟩ μ
      = (if h0 : (∑' ν : PMF State, pe'.scheduler.next ⟨s₀, sq⟩ (some (a, ν)) * ν sk) ≠ 0 then
          (pe'.scheduler.next ⟨s₀, sq⟩ (some (a, μ)) * μ sk) *
            (∑' ν : PMF State, pe'.scheduler.next ⟨s₀, sq⟩ (some (a, ν)) * ν sk)⁻¹
        else (PMF.pure (PMF.pure s₀) : PMF (PMF State)) μ) := by
    -- Restate the resolved `exists_split_last` data with the *internal* subject
    -- `(⟨s₀, sq.append …⟩ : AlterSeq).trans` (defeq to `sq.append …`, but syntactically the
    -- form that `lastMuBelief`'s unfolding produces), so the rewrites fire under the `dite`.
    have kp : (Stream'.Seq.exists_split_last
        ((⟨s₀, sq.append (Seq.cons (a, sk) Seq.nil)⟩ : AlterSeq State Label).trans)
        h_app hne).choose = sq := hprev_seq hne
    have kl : (Stream'.Seq.exists_split_last
        ((⟨s₀, sq.append (Seq.cons (a, sk) Seq.nil)⟩ : AlterSeq State Label).trans)
        h_app hne).choose_spec.choose = (a, sk) := hlast hne
    unfold ProbabilisticExecution.lastMuBelief
    rw [dif_pos h_app, dif_pos hne]
    -- Rewrite the chosen `last = (a, sk)` BEFORE the chosen `prev = sq`: the `prev`-rewrite
    -- would dependently recast the `last`-term's `exists_split_last` instance and prevent the
    -- `last`-rewrite from firing.
    simp only [kl]
    simp only [kp]
    -- Now both sides are the `dite` on the same normalizer; the `then` branch is
    -- `PMF.normalize w h0 _ μ` for `w μ = next ⟨s₀, sq⟩ (some (a, μ)) * μ sk`.
    split_ifs with h0
    · rw [PMF.normalize_apply]
    · rfl
  rw [hlmb, hprobE]
  -- The last-step kernel is the normalizer.
  have hker : pe'.kernel ⟨s₀, sq⟩ (a, sk)
      = ∑' ν : PMF State, pe'.scheduler.next ⟨s₀, sq⟩ (some (a, ν)) * ν sk := rfl
  split_ifs with h0
  · -- Nonzero normalizer: cancel.
    have hZtop : (∑' ν : PMF State, pe'.scheduler.next ⟨s₀, sq⟩ (some (a, ν)) * ν sk) ≠ ⊤ := by
      rw [← hker]
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (pe'.kernel_le_one ⟨s₀, sq⟩ (a, sk))
    rw [hker]
    rw [show pe'.probOf ⟨s₀, sq⟩ h_sq *
          (∑' ν : PMF State, pe'.scheduler.next ⟨s₀, sq⟩ (some (a, ν)) * ν sk) *
          (pe'.scheduler.next ⟨s₀, sq⟩ (some (a, μ)) * μ sk *
            (∑' ν : PMF State, pe'.scheduler.next ⟨s₀, sq⟩ (some (a, ν)) * ν sk)⁻¹)
        = pe'.probOf ⟨s₀, sq⟩ h_sq * (pe'.scheduler.next ⟨s₀, sq⟩ (some (a, μ)) * μ sk) *
            ((∑' ν : PMF State, pe'.scheduler.next ⟨s₀, sq⟩ (some (a, ν)) * ν sk) *
              (∑' ν : PMF State, pe'.scheduler.next ⟨s₀, sq⟩ (some (a, ν)) * ν sk)⁻¹) by ring,
      ENNReal.mul_inv_cancel h0 hZtop, mul_one]
  · -- Zero normalizer ⟹ the kernel is `0` ⟹ `probOf E = 0` and the RHS factor is `0`.
    push Not at h0
    rw [hker, h0, mul_zero, zero_mul]
    -- RHS: `next Epre (some (a,μ)) * μ sk` is one summand of the (zero) normalizer, so `0`.
    have hsummand : pe'.scheduler.next ⟨s₀, sq⟩ (some (a, μ)) * μ sk = 0 :=
      (ENNReal.tsum_eq_zero.mp h0) μ
    rw [hsummand, mul_zero]

open Classical in
/-- **`boundaryMarginal` of an appended history.** For `E = ⟨s₀, sq ++ [(l, sk)]⟩` with
preceding history `E_pre = ⟨s₀, sq⟩` (terminating), the boundary marginal at `s`
marginalizes `lastMuBelief E` against the hyperStep boundary of the last weak step
`(l, μ)` taken from the penult-history end-state `E_pre.endState`:
`boundaryMarginal E s = ∑' μ, lastMuBelief E μ · hyperBoundary (E_pre.endState) l μ s`. -/
theorem ProbabilisticExecution.boundaryMarginal_append_singleton {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (s₀ : State) (sq : Seq (Label × State)) (h_sq : sq.Terminates)
    (l : Label) (sk : State)
    (h_app : (sq.append (Seq.cons (l, sk) Seq.nil)).Terminates) (s : State) :
    pe'.boundaryMarginal ⟨s₀, sq.append (Seq.cons (l, sk) Seq.nil)⟩ s
      = ∑' μ : PMF State, pe'.lastMuBelief ⟨s₀, sq.append (Seq.cons (l, sk) Seq.nil)⟩ μ *
          (sys.hyperBoundary ((⟨s₀, sq⟩ : AlterSeq State Label).endState h_sq) l μ) s := by
  classical
  -- Resolve `exists_split_last` data for `E` (mirrors `probOf_mul_lastMuBelief_append`).
  have htl : (sq.append (Seq.cons (l, sk) Seq.nil)).toList h_app = sq.toList h_sq ++ [(l, sk)] := by
    rw [Stream'.Seq.toList_append sq (Seq.cons (l, sk) Seq.nil) h_sq
        (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil) h_app,
      Stream'.Seq.toList_cons, Stream'.Seq.toList_nil]
  have hne : (sq.append (Seq.cons (l, sk) Seq.nil)).toList h_app ≠ [] := by rw [htl]; simp
  have hgetLast : ((sq.append (Seq.cons (l, sk) Seq.nil)).toList h_app).getLast hne = (l, sk) := by
    have hgl? : ((sq.append (Seq.cons (l, sk) Seq.nil)).toList h_app).getLast? = some (l, sk) := by
      rw [htl]; exact List.getLast?_concat
    exact List.getLast_of_getLast?_eq_some hgl?
  -- The chosen last transition `(l, sk)` and prefix `sq`, stated with the internal subject.
  have kl : (Stream'.Seq.exists_split_last
      ((⟨s₀, sq.append (Seq.cons (l, sk) Seq.nil)⟩ : AlterSeq State Label).trans)
      h_app hne).choose_spec.choose = (l, sk) := by
    have h := (Stream'.Seq.exists_split_last (sq.append (Seq.cons (l, sk) Seq.nil))
      h_app hne).choose_spec.choose_spec.choose_spec.2.2
    rw [h, hgetLast]
  have kp : (Stream'.Seq.exists_split_last
      ((⟨s₀, sq.append (Seq.cons (l, sk) Seq.nil)⟩ : AlterSeq State Label).trans)
      h_app hne).choose = sq := by
    have hprev_term := (Stream'.Seq.exists_split_last (sq.append (Seq.cons (l, sk) Seq.nil))
      h_app hne).choose_spec.choose_spec.choose
    have htoL := (Stream'.Seq.exists_split_last (sq.append (Seq.cons (l, sk) Seq.nil))
      h_app hne).choose_spec.choose_spec.choose_spec.2.1
    rw [← Stream'.Seq.ofList_toList (Stream'.Seq.exists_split_last
      (sq.append (Seq.cons (l, sk) Seq.nil)) h_app hne).choose hprev_term, htoL]
    conv_lhs => rw [htl]
    simp [Stream'.Seq.ofList_toList sq h_sq]
  have kl1 : (Stream'.Seq.exists_split_last
      ((⟨s₀, sq.append (Seq.cons (l, sk) Seq.nil)⟩ : AlterSeq State Label).trans)
      h_app hne).choose_spec.choose.1 = l := by rw [kl]
  unfold ProbabilisticExecution.boundaryMarginal
  rw [dif_pos h_app, dif_pos hne]
  -- Rewrite `last` before `prev` (the prev-rewrite recasts the last-instance), then align
  -- the penult end-state of `⟨s₀, sq⟩` (proof-irrelevant termination argument).
  simp only [kl1]
  simp only [kp]

open Classical in
/-- **(III) The boundary belief-algebra ρ-recursion.** Feeding the per-state single-step
expansion integrand `segExp labs l g` into the tight trace-`labs` ρ-expectation recovers
the tight trace-`(labs++[l])` ρ-expectation:
`rhoExpect labs (segExp labs l g) = rhoExpect (labs++[l]) g`.

This is pure belief algebra (the `hyperStep_marginal_decomp` analogue), with NO new
scheduler reasoning. A tight trace-`(labs++[l])` `sys^w`-history `E` = a tight trace-`labs`
history `E_pre` + one external weak step `(l, s_k)` (`probOf_append_singleton`/`tight_iff`
reindex). Its `boundaryMarginal E` marginalizes `lastMuBelief E` against
`hyperBoundary E_pre.endState l μ` — exactly the `hyperBoundary` integrand of `segExp`,
once the `beliefExpandAt labs s'` belief normalizer is cancelled
(`beliefExpandAt_normalize_cancel`) against the `boundaryMarginal E_pre`-weighting of the
ρ_k boundary, and the `lastMuBelief` cancellation
`probOf(E)·lastMuBelief(E)(μ) = probOf(E_pre)·next(E_pre)(l,μ)·μ(s_k)` is applied. -/
theorem rhoExpect_segExp_step (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (labs : List Label) (l : Label) (g : State → ENNReal) :
    pe'.rhoExpect labs (pe'.segExp labs l g) = pe'.rhoExpect (labs ++ [l]) g := by
  classical
  -- Collapse both ρ-expectations to label-list cones (under `hExt` all labels are external).
  rw [pe'.rhoExpect_eq_labelCone hExt labs (pe'.segExp labs l g),
    pe'.rhoExpect_eq_labelCone hExt (labs ++ [l]) g]
  -- REMAINING (the append-singleton boundary reindex):
  -- LHS `∑' E_pre, dite(labelList = labs) (probOf E_pre · ∑' s', boundaryMarginal E_pre s'
  --        · segExp labs l g s')`
  -- RHS `∑' E,     dite(labelList = labs++[l]) (probOf E · ∑' s, boundaryMarginal E s · g s)`.
  -- Reindex RHS via the bijection `E ↔ (E_pre, (l, sk))` (label-list `labs++[l]` ↔ a
  -- label-list-`labs` prefix `E_pre` + last external transition `(l, sk)`), mirroring
  -- `tsum_probOf_labels_append`. The appended history's `boundaryMarginal E s`
  -- (`= ∑' μ, lastMuBelief E μ · hyperBoundary E_pre.endState l μ s`) collapses against
  -- `probOf E` by `probOf_mul_lastMuBelief_append`
  -- (`probOf E · lastMuBelief E μ = probOf E_pre · next E_pre (l,μ) · μ sk`), giving
  -- `∑' (sk,μ), probOf E_pre · next E_pre (l,μ) · μ sk · (∑' s, hyperBoundary … s · g s)`.
  -- On the LHS, `segExp labs l g s'` is the `beliefExpandAt labs s'`-average of
  -- `∑' μ, next E_b (l,μ) · (∑' t, hyperBoundary s' l μ t · g t)`; the
  -- `boundaryMarginal E_pre s'`-weighting + `beliefExpandAt_normalize_cancel` matches the
  -- belief `beliefExpandAtW labs s' E_b = probOf E_b · boundaryMarginal E_b s'` against the
  -- reindexed RHS prefix `E_pre`/boundary `s' = E_pre.endState`, closing the recursion.
  sorry

/-- **The general-`g` inductive step of the `rhoExpect` invariant for `expand`** (the
research crux — the SOLE remaining `sorry` of the no-internal trace invariant).

Appending one external label `l` to a tight trace-`labs` prefix, the `expand`
construction runs a multi-transition segment that re-anchors its belief at the current
concrete state, draws the next external weak step, and integrates `g` at the new
hyperStep boundary. Given the **general-`g`** IH (`∀ g'`), the appended external level
mass equals `rhoExpect (labs ++ [l]) g`.

EXACT GOAL (this theorem's statement):
`sys.extLabMass ⟨PMF.pure sys.init, Scheduler.expand sys pe'⟩ (labs ++ [l]) g`
  `= pe'.rhoExpect (labs ++ [l]) g`.

INTENDED PROOF (mirrors `lower_labProb_eq_aux`'s step, but each external label is a
multi-transition SEGMENT and the `expand` belief RE-ANCHORS at the current state):
1. **LHS disintegration.** Every tight trace-`(labs ++ [l])` execution `e` of `expand`
   factors at its last external label `l` into a tight trace-`labs` prefix `e_pre`
   (end-state `s' = e_pre.endState`, a ν'_k sample) and a successor SEGMENT starting at
   `s'`: the carried post-τ `expandPostScheduler` (ν'-anchored via `beliefExpandAt`,
   halts a.s. since `s' ∈ ν'_k.support`) reaches a μ_k sample, then `anchoredNextSegment`
   draws the next weak step `(l, μ)` and runs its witness, integrating `g` at the next
   hyperStep boundary ν'_{k+1}.
2. **Segment `g`-integral.** Averaged over the belief at `s'`, the segment's `g`-integral
   equals the belief-weighted next-step boundary expectation, by
   `expand_step_belief_averaging` (external draw) + `weakTau.integrate` /
   `Scheduler.haltMass_init_mix` (τ-closures) + `extLabMass_segment_bridge`.
3. **Fold the prefix** via the general-`g` `ih` with the per-segment integrand as `g'`,
   cancel the belief normalizers with `beliefExpandAt_normalize_cancel` (and a mirror
   `beliefExpandAtEnd_normalize_cancel` if needed), and apply the boundary-marginal
   one-step decomposition (the `hyperStep_marginal_decomp` analogue: one weak step on the
   ρ_k boundary distribution yields the ρ_{k+1} boundary) to land on
   `rhoExpect (labs ++ [l]) g`.

BLOCKING SUB-LEMMA (missing infrastructure, NOT a reuse of any existing lemma): the
external-boundary disintegration of `extLabMass` for the `expand` scheduler — that a
tight `(labs ++ [l])`-trace execution's level mass factors at its last external label
into the IH-governed prefix and the `extLabMass_segment_bridge`-governed successor
segment, with the carried post-τ `expandPostScheduler` reassociated with the next weak
step's pre-τ via `weakTau_trans`. This segment-level disintegration of the belief-bind
`expand.next` (run over the `internalSuffix`) is combinatorial and has no template.

The proof is now the three-step factorization through `segExp`:
`(I)` `extLabMass D (labs++[l]) g = extLabMass D labs (segExp labs l g)`
  (`expand_extLabMass_disintegrate`, the hard belief-re-anchoring disintegration);
`(II)` `extLabMass D labs (segExp labs l g) = rhoExpect labs (segExp labs l g)`
  (immediate from the general-`g` `ih`);
`(III)` `rhoExpect labs (segExp labs l g) = rhoExpect (labs++[l]) g`
  (`rhoExpect_segExp_step`, the boundary belief-algebra recursion). -/
theorem expand_extLabMass_step_g (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (h_init : pe'.initState = PMF.pure sys^w.toSystem.init)
    (labs : List Label) (l : Label) (g : State → ENNReal)
    (ih : ∀ g' : State → ENNReal,
      sys.extLabMass ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ labs g'
        = pe'.rhoExpect labs g') :
    sys.extLabMass ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ (labs ++ [l]) g
      = pe'.rhoExpect (labs ++ [l]) g := by
  -- (I) external-boundary disintegration through the per-state `segExp` integrand.
  rw [expand_extLabMass_disintegrate sys pe' hExt h_init labs l g]
  -- (II) fold the tight-`labs` prefix by the general-`g` IH.
  rw [ih (pe'.segExp labs l g)]
  -- (III) the boundary belief-algebra ρ-recursion.
  rw [rhoExpect_segExp_step sys pe' hExt labs l g]

/-- **The general-`g` `rhoExpect` invariant for `expand`.** The `sys`-side external
level mass of the `expand` construction equals the `pe'`-side ρ-expectation, for every
external label list and every `g`. The base is `rhoExpect_nil`; the inductive step is
the genuinely hard `expand_extLabMass_step_g` (multi-transition segment with belief
re-anchoring). The IH is **general-`g`** (`∀ g'`), obtained by reverting `g` before the
induction. -/
theorem expand_extLabMass_eq_aux (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (h_init : pe'.initState = PMF.pure sys^w.toSystem.init) (labs : List Label) :
    ∀ g : State → ENNReal,
      sys.extLabMass ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ labs g
        = pe'.rhoExpect labs g := by
  classical
  induction labs using List.reverseRecOn with
  | nil =>
      intro g
      rw [sys.extLabMass_nil _ g, pe'.rhoExpect_nil g, h_init]
      simp [LabelledSystem.weakClosure]
  | append_singleton labs l ih =>
      intro g
      exact expand_extLabMass_step_g sys pe' hExt h_init labs l g ih

/-- **Core trace invariant (no internal weak steps).** Under the
assumption that `pe'` schedules only external weak steps, the expanded `sys`-execution
and `pe'` assign the same total `probOf`-mass to every finite external trace `extLabs`
(the `g = 1` external level mass). The general-`g` invariant is `expand_extLabMass_eq_aux`
landing on `rhoExpect`; the `g = 1` slice is `rhoExpect_one`. -/
theorem expand_extLabMass_eq_noInternal (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (h_init : pe'.initState = PMF.pure sys^w.toSystem.init) (extLabs : List Label) :
    sys.extLabMass ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ extLabs (fun _ => 1)
      = sys^w.extLabMass pe' extLabs (fun _ => 1) := by
  rw [expand_extLabMass_eq_aux sys pe' hExt h_init extLabs (fun _ => 1), pe'.rhoExpect_one extLabs]

/-- Trace-distribution preservation for `expand` UNDER the no-internal-weak-steps
assumption (Phase 1). Reduces to `expand_extLabMass_eq_noInternal` for finite
traces; both sides are `0` for infinite traces. -/
theorem expand_traceProb_eq_noInternal (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (h_init : pe'.initState = PMF.pure sys^w.toSystem.init) (τ : Seq Label) :
    sys.traceProb ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ τ
      = sys^w.traceProb pe' τ := by
  by_cases hτ : τ.Terminates
  · obtain ⟨L, hL⟩ : ∃ L, τ = Seq.ofList L :=
      ⟨τ.toList hτ, (Stream'.Seq.ofList_toList τ hτ).symm⟩
    subst hL
    rw [sys.traceProb_eq_extLabMass _ L, sys^w.traceProb_eq_extLabMass pe' L]
    exact expand_extLabMass_eq_noInternal sys pe' hExt h_init L
  · rw [sys.traceProb_eq_zero_of_not_terminates _ τ hτ,
        sys^w.traceProb_eq_zero_of_not_terminates pe' τ hτ]

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
