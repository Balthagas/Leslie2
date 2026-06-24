/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.WeakStep
import MyMathlibProject.DistConstruction
import MyMathlibProject.TraceProbBound
import MyMathlibProject.PostTauAccounting
import MyMathlibProject.TightTrace

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

/-- A trivially-valid `sys`-scheduler that halts immediately (emits `none`). -/
noncomputable def Scheduler.haltNow (sys : LabelledSystem State Label) :
    Scheduler sys.toSystem where
  next _ := PMF.pure none
  valid := by
    intro e n s _ _ l μ h_supp
    -- support of `pure none` is `{none}`; `some (l,μ) ∉ {none}`.
    simp only [PMF.support_pure, Set.mem_singleton_iff] at h_supp
    exact absurd h_supp (by simp)

/-! #### Generic suffix / endState helpers -/

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
theorem ProbabilisticExecution.beliefExpandW_tsum_le_one {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (L : List Label) (ν' : State) :
    (∑' p, pe'.beliefExpandW L ν' p) ≤ 1 := by
  classical
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
    (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
       (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist h.init else 0) *
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
        rw [mul_assoc]
        refine mul_le_of_le_one_right' (mul_le_one' ?_ ?_)
        · split
          · exact PMF.coe_le_one _ _
          · exact zero_le_one
        · split
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
          (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
            (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0) *
          (⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
            : ProbabilisticExecution sys.toSystem).probOf e' he' := by
  classical
  unfold Scheduler.postTauDrawW
  rw [dif_pos he', he'_init]

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

open Classical in
/-- The **post-τ posterior marginal** `postTauZ e'` at a running history `e'` (with boundary
`ν'`): the prior-weighted sum of the per-`μ` post-τ witnesses' `probOf` (the RHS of the
filter-marginal). The post-τ analogue of `drawZ`; here the prior is the `(l,·)`-fiber. -/
noncomputable def Scheduler.postTauZ {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (ν' : State) (e' : AlterSeq State Label)
    (he' : e'.trans.Terminates) : ENNReal :=
  ∑' μ : PMF State,
    pe'.scheduler.next E' (some (l, μ)) *
      (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
        (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0) *
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
        (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
          (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0) *
        (⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
          : ProbabilisticExecution sys.toSystem).probOf e' h_sq = 0 :=
      ENNReal.tsum_eq_zero.mp (by rw [Scheduler.postTauZ] at h0; exact h0)
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
    rw [Scheduler.postTauDrawW_eq pe' E' hT l ν' e' h_sq he'_init μ, htel μ]; ring

open Classical in
/-- **Base value `Z₀` for `postTauZ`** (analogue of `drawZ_nil`, but NOT `1`). At the empty
history `⟨ν', nil⟩`, every post-τ witness realizes the empty execution with mass `1` (Dirac
source `pure ν'`), so the marginal collapses to the postDist-weighted FIBER mass `∑' μ,
pe'.next E' (some (l, μ)) · postDist_μ(ν')` — the new normaliser `Z₀(ν')` is the reach-`ν'`
likelihood (the prior here is a fiber, not a full PMF). -/
theorem Scheduler.postTauZ_nil {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (ν' : State) :
    Scheduler.postTauZ pe' E' hT l ν' ⟨ν', Stream'.Seq.nil⟩ Stream'.Seq.terminates_nil
      = ∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ)) *
          (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
            (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0) := by
  unfold Scheduler.postTauZ
  refine tsum_congr (fun μ => ?_)
  rw [ProbabilisticExecution.probOf_nil]
  change pe'.scheduler.next E' (some (l, μ)) * _ * (PMF.pure ν') ν' = _
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

open Classical in
/-- **PIECE B (probOf form): the post-τ filter-marginal, MULTIPLIED form.** The reach-`ν'`
likelihood `Z₀(ν') = ∑' μ, pe'.next E' (some (l, μ)) · postDist_μ(ν')` times `postTauDraw.probOf e`
(from `pure ν'`) equals the prior-weighted sum of the per-`μ` post-τ witnesses' `postDist_μ(ν') ·
probOf`. Division-free (the base normaliser `Z₀(ν')` need not be `1`). -/
theorem Scheduler.postTauDraw_probOf_eq {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (ν' : State)
    (e : AlterSeq State Label) (he : e.trans.Terminates) (he_init : e.init = ν') :
    (∑' μ, pe'.scheduler.next E' (some (l, μ)) *
        (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
          (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)) *
      (⟨PMF.pure ν', Scheduler.postTauDraw pe' E' l⟩
        : ProbabilisticExecution sys.toSystem).probOf e he
      = ∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ))
          * (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
              (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)
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
  rw [show (∑' μ, pe'.scheduler.next E' (some (l, μ)) *
            (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
              (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0))
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

open Classical in
/-- **Per-execution halt-mass marginal of `postTauDraw`, MULTIPLIED form** (the `haltMass`
analogue of `postTauDraw_probOf_eq`). `Z₀(ν') · postTauDraw.haltMass e = ∑' μ, pe'.next E' (some
(l, μ)) · postDist_μ(ν') · (postTauWitness … μ).haltMass e`. Proven by multiplying the multiplied
probOf marginal by the `none`-emission posterior average; the `postTauZ e` normaliser cancels. -/
theorem Scheduler.postTauDraw_haltMass_marginal {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (ν' : State)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) (he_init : e.1.init = ν') :
    (∑' μ, pe'.scheduler.next E' (some (l, μ)) *
        (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
          (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)) *
        (Scheduler.postTauDraw pe' E' l).haltMass (PMF.pure ν') e
      = ∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ))
          * (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
              (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)
          * (Scheduler.postTauWitness sys (E'.endState hT) l μ).haltMass (PMF.pure ν') e := by
  classical
  unfold Scheduler.haltMass
  by_cases h0 : (∑' μ, Scheduler.postTauDrawW pe' E' hT l e.1 μ) ≠ 0
  · -- nonvanishing normaliser: expand `next none`, multiply by the multiplied probOf marginal
    rw [Scheduler.postTauDraw_next_none pe' E' hT l e.1 h0]
    -- LHS = Z₀ · (probOf e · ∑' μ, normalize(W) μ · (postTauWit μ).next none)
    -- regroup: (Z₀ · probOf e) · (∑' μ, normalize(W) μ · K μ) = postTauZ e · (…)
    rw [show (∑' μ, pe'.scheduler.next E' (some (l, μ)) *
              (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
                (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)) *
            ((⟨PMF.pure ν', Scheduler.postTauDraw pe' E' l⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2
              * ∑' μ, (PMF.normalize (Scheduler.postTauDrawW pe' E' hT l e.1) h0
                  (Scheduler.postTauDrawW_tsum_ne_top pe' E' hT l e.1)) μ *
                (Scheduler.postTauWitness sys (E'.endState hT) l μ).next e.1 none)
          = ((∑' μ, pe'.scheduler.next E' (some (l, μ)) *
              (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
                (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)) *
              (⟨PMF.pure ν', Scheduler.postTauDraw pe' E' l⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2)
            * ∑' μ, (PMF.normalize (Scheduler.postTauDrawW pe' E' hT l e.1) h0
                  (Scheduler.postTauDrawW_tsum_ne_top pe' E' hT l e.1)) μ *
                (Scheduler.postTauWitness sys (E'.endState hT) l μ).next e.1 none by ring,
      Scheduler.postTauDraw_probOf_eq pe' E' hT l ν' e.1 e.2 he_init]
    -- now postTauZ e = ∑' μ, W μ ; recognise the multiplied form and cancel
    rw [show (∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ))
            * (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
                (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)
            * (⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2)
          = ∑' μ, Scheduler.postTauDrawW pe' E' hT l e.1 μ from
        tsum_congr (fun μ =>
          (Scheduler.postTauDrawW_eq pe' E' hT l ν' e.1 e.2 he_init μ).symm)]
    simp only [PMF.normalize_apply]
    rw [ProbabilisticExecution.normalize_cancel _
        (Scheduler.postTauDrawW_tsum_ne_top pe' E' hT l e.1) _ h0]
    refine tsum_congr (fun μ => ?_)
    rw [Scheduler.postTauDrawW_eq pe' E' hT l ν' e.1 e.2 he_init μ]; ring
  · -- vanishing normaliser: postTauZ e = 0 ⟹ probOf e = 0 and every prior·probOf(e) = 0
    push Not at h0
    have hZ0 : Scheduler.postTauZ pe' E' hT l ν' e.1 e.2 = 0 := by
      rw [Scheduler.postTauZ_eq_tsum_postTauDrawW pe' E' hT l ν' e.1 e.2 he_init]; exact h0
    -- LHS: `Z₀ · probOf e · next none`; `Z₀ · probOf e = postTauZ e = 0`
    rw [show (∑' μ, pe'.scheduler.next E' (some (l, μ)) *
              (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
                (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)) *
            ((⟨PMF.pure ν', Scheduler.postTauDraw pe' E' l⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2
              * (Scheduler.postTauDraw pe' E' l).next e.1 none)
          = ((∑' μ, pe'.scheduler.next E' (some (l, μ)) *
              (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
                (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)) *
              (⟨PMF.pure ν', Scheduler.postTauDraw pe' E' l⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2)
            * (Scheduler.postTauDraw pe' E' l).next e.1 none by ring,
      Scheduler.postTauDraw_probOf_eq pe' E' hT l ν' e.1 e.2 he_init,
      show (∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ))
            * (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
                (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)
            * (⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2)
          = Scheduler.postTauZ pe' E' hT l ν' e.1 e.2 from rfl,
      hZ0, zero_mul]
    -- RHS: every term `prior·(postTauWit μ).haltMass e = prior·probOf(e)·next none = 0`
    have hz : ∀ μ, pe'.scheduler.next E' (some (l, μ)) *
        (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
          (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0) *
        (⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
          : ProbabilisticExecution sys.toSystem).probOf e.1 e.2 = 0 :=
      ENNReal.tsum_eq_zero.mp (by rw [Scheduler.postTauZ] at hZ0; exact hZ0)
    refine (ENNReal.tsum_eq_zero.mpr (fun μ => ?_)).symm
    change pe'.scheduler.next E' (some (l, μ)) *
        (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
          (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0) *
        ((⟨PMF.pure ν', Scheduler.postTauWitness sys (E'.endState hT) l μ⟩
          : ProbabilisticExecution sys.toSystem).probOf e.1 e.2
            * (Scheduler.postTauWitness sys (E'.endState hT) l μ).next e.1 none) = 0
    rw [← mul_assoc, hz μ, zero_mul]

open Classical in
/-- **PIECE B (pushforward form): the post-τ filter-marginal `g`-integral, MULTIPLIED form.**
`Z₀(ν') · postTauDraw.pushforward g = ∑' μ, pe'.next E' (some (l, μ)) · postDist_μ(ν') ·
(postTauWitness … μ).pushforward g`, where `Z₀(ν') = ∑' μ, pe'.next E' (some (l, μ)) ·
postDist_μ(ν')` is the reach-`ν'` likelihood. Obtained from `postTauDraw_haltMass_marginal` by
`∑'_e` + `ENNReal.tsum_comm`. -/
theorem Scheduler.postTauDraw_pushforward {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem) (E' : AlterSeq State Label)
    (hT : E'.trans.Terminates) (l : Label) (ν' : State) (g : State → ENNReal) :
    (∑' μ, pe'.scheduler.next E' (some (l, μ)) *
        (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
          (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)) *
        (∑' e, (Scheduler.postTauDraw pe' E' l).haltMass (PMF.pure ν') e * g (e.1.endState e.2))
      = ∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ))
          * (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
              (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)
          * (∑' e, (Scheduler.postTauWitness sys (E'.endState hT) l μ).haltMass
              (PMF.pure ν') e * g (e.1.endState e.2)) := by
  classical
  rw [← ENNReal.tsum_mul_left]
  have hterm : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      (∑' μ, pe'.scheduler.next E' (some (l, μ)) *
          (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
            (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)) *
          ((Scheduler.postTauDraw pe' E' l).haltMass (PMF.pure ν') e * g (e.1.endState e.2))
        = ∑' μ : PMF State, pe'.scheduler.next E' (some (l, μ))
            * (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
                (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)
            * ((Scheduler.postTauWitness sys (E'.endState hT) l μ).haltMass
                (PMF.pure ν') e * g (e.1.endState e.2)) := by
    intro e
    by_cases hinit : e.1.init = ν'
    · rw [show (∑' μ, pe'.scheduler.next E' (some (l, μ)) *
              (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
                (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)) *
              ((Scheduler.postTauDraw pe' E' l).haltMass (PMF.pure ν') e * g (e.1.endState e.2))
            = ((∑' μ, pe'.scheduler.next E' (some (l, μ)) *
                (if hstep : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ then
                  (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)) *
                (Scheduler.postTauDraw pe' E' l).haltMass (PMF.pure ν') e) * g (e.1.endState e.2)
            by ring,
        Scheduler.postTauDraw_haltMass_marginal pe' E' hT l ν' e hinit, ← ENNReal.tsum_mul_right]
      exact tsum_congr (fun μ => by ring)
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

open Classical in
/-- **Unnormalised weight of the POSTERIOR expand-segment draw** (the third posterior-bind
weight, mirroring `drawAndRunW` / `postTauDrawW`). At a trace-`L'` boundary `ν'` with
just-completed external label `l'`, and a running `sys`-history `h` (boundary `h.init = ν'`),
the prior `pe'.beliefExpandW L' ν' p` (the unnormalised `beliefExpand` weight on the pair
`p = (E', μ)`) is reweighted by the *likelihood* of `h` under the candidate segment scheduler
`segmentScheduler pe' ν' l' E' μ`, run from the Dirac source `PMF.pure ν'`. Candidate pairs `p`
whose segment scheduler *cannot* produce the observed trajectory `h` get likelihood `0` and drop
out. This conditions the belief draw on the segment trajectory (the GAP-2 fix: the old OUTER
belief was a constant mixture re-drawn each within-segment step, so `expandCont.probOf` was a
product of mixtures, not a sum of products). -/
noncomputable def Scheduler.expandContW (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (L' : List Label) (ν' : State) (l' : Label)
    (h : AlterSeq State Label) : AlterSeq State Label × PMF State → ENNReal := fun p =>
  pe'.beliefExpandW L' ν' p *
    (if hh : h.trans.Terminates then
       (⟨PMF.pure ν', Scheduler.segmentScheduler pe' ν' l' p.1 p.2⟩
          : ProbabilisticExecution sys.toSystem).probOf h hh
     else 0)

/-- **Finiteness of the expand-segment posterior normaliser** (mirrors `postTauDrawW_tsum_ne_top`).
Each likelihood factor is a `probOf ≤ pe.init ≤ 1`, so `∑' p, expandContW … p ≤ ∑' p,
beliefExpandW L' ν' p ≤ 1` by `beliefExpandW_tsum_le_one`. -/
theorem Scheduler.expandContW_tsum_ne_top (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (L' : List Label) (ν' : State) (l' : Label)
    (h : AlterSeq State Label) :
    (∑' p, Scheduler.expandContW sys pe' L' ν' l' h p) ≠ ⊤ := by
  classical
  suffices hle : (∑' p, Scheduler.expandContW sys pe' L' ν' l' h p) ≤ 1 from
    (lt_of_le_of_lt hle ENNReal.one_lt_top).ne
  calc (∑' p, Scheduler.expandContW sys pe' L' ν' l' h p)
      ≤ ∑' p, pe'.beliefExpandW L' ν' p := by
        refine ENNReal.tsum_le_tsum (fun p => ?_)
        unfold Scheduler.expandContW
        refine mul_le_of_le_one_right' ?_
        split
        · exact le_trans (ProbabilisticExecution.probOf_le_init _ _ _) (PMF.coe_le_one _ _)
        · exact zero_le_one
    _ ≤ 1 := pe'.beliefExpandW_tsum_le_one L' ν'

/-- **The expand-segment continuation scheduler (POSTERIOR-bind).** At a trace-`L'` boundary `ν'`
with just-completed external label `l'`, and a running `sys`-history `d` (boundary `ν'`), reweight
the prior `pe'.beliefExpandW L' ν' p` by the likelihood of `d` under each candidate segment
scheduler (see `expandContW`) and *normalise* — conditioning the belief draw on the segment
trajectory so off-path pairs `p` drop out (the GAP-2 fix). On a drawn `p = (E', μ)`, run
`segmentScheduler pe' ν' l' E' μ` at `d`. If the posterior normaliser vanishes (no pair explains
`d`), halt. Validity is inherited from each `segmentScheduler`. This is the scheduler that
`Scheduler.expand` runs (at the `internalSuffix`) once the trace-`L'` prefix is committed and
its last external label `l'` is observed (see `expand_next_eq_expandCont`). -/
noncomputable def Scheduler.expandCont (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (L' : List Label) (ν' : State) (l' : Label) :
    Scheduler sys.toSystem where
  next d :=
    if h0 : (∑' p, Scheduler.expandContW sys pe' L' ν' l' d p) ≠ 0 then
      (PMF.normalize (Scheduler.expandContW sys pe' L' ν' l' d) h0
          (Scheduler.expandContW_tsum_ne_top sys pe' L' ν' l' d)).bind (fun p =>
        (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).next d)
    else PMF.pure none
  valid := by
    classical
    intro d n s' hterm hstate l μ h_supp
    change some (l, μ) ∈
      (if h0 : (∑' p, Scheduler.expandContW sys pe' L' ν' l' d p) ≠ 0 then
        (PMF.normalize (Scheduler.expandContW sys pe' L' ν' l' d) h0
            (Scheduler.expandContW_tsum_ne_top sys pe' L' ν' l' d)).bind (fun p =>
          (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).next d)
      else PMF.pure none).support at h_supp
    by_cases h0 : (∑' p, Scheduler.expandContW sys pe' L' ν' l' d p) ≠ 0
    · rw [dif_pos h0, PMF.mem_support_bind_iff] at h_supp
      obtain ⟨p, _hp, h_supp⟩ := h_supp
      exact (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).valid d n s' hterm hstate l μ h_supp
    · rw [dif_neg h0, PMF.support_pure, Set.mem_singleton_iff] at h_supp
      exact absurd h_supp (by simp)

/-! ### `expandCont` filter-marginal (GAP-2 collapse, MULTIPLIED form like `postTauDraw`)

The third instance of the posterior-bind keystone. The prior of `expandCont` is the
`beliefExpandW L' ν'` weight (NOT a full PMF), so the base marginal `Z₀ = ∑' p, beliefExpandW
L' ν' p` need not be `1`. We prove the filter-marginal in MULTIPLIED (division-free) form
`Z₀ · probOf e = expandZ e`, mirroring `postTauZ`/`postTauZ_step`/`postTauZ_nil`/
`postTauDraw_probOf_eq_postTauZ_ofList`. This is the GAP-2 collapse: `expandCont.probOf`
factors through the per-`p` segment `probOf`, so the old constant-mixture pathology (product of
re-drawn mixtures) is gone (the posterior reconditioning telescopes). -/

open Classical in
/-- **`expandContW` as `prior · witness probOf`.** For a running history `e'` with boundary
`e'.init = ν'`, the unnormalised weight `expandContW` equals `beliefExpandW L' ν' p ·
(⟨pure ν', segmentScheduler …⟩).probOf e'` (analogue of `postTauDrawW_eq`). -/
theorem Scheduler.expandContW_eq (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (L' : List Label) (ν' : State) (l' : Label)
    (e' : AlterSeq State Label) (he' : e'.trans.Terminates)
    (p : AlterSeq State Label × PMF State) :
    Scheduler.expandContW sys pe' L' ν' l' e' p
      = pe'.beliefExpandW L' ν' p *
          (⟨PMF.pure ν', Scheduler.segmentScheduler pe' ν' l' p.1 p.2⟩
            : ProbabilisticExecution sys.toSystem).probOf e' he' := by
  classical
  unfold Scheduler.expandContW
  rw [dif_pos he']

open Classical in
/-- **The `some (l, μ)`-emission of `expandCont` as a posterior average** (analogue of
`postTauDraw_next_some`). When the posterior normaliser does not vanish, the emission is the
posterior-weighted sum of the per-`p` segment schedulers' emissions. -/
theorem Scheduler.expandCont_next_some (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (L' : List Label) (ν' : State) (l' : Label)
    (e' : AlterSeq State Label)
    (h0 : (∑' p, Scheduler.expandContW sys pe' L' ν' l' e' p) ≠ 0) (l₁ : Label) (μ₁ : PMF State) :
    (Scheduler.expandCont sys pe' L' ν' l').next e' (some (l₁, μ₁))
      = ∑' p, (PMF.normalize (Scheduler.expandContW sys pe' L' ν' l' e') h0
            (Scheduler.expandContW_tsum_ne_top sys pe' L' ν' l' e')) p *
          (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).next e' (some (l₁, μ₁)) := by
  classical
  change (if h0' : (∑' p, Scheduler.expandContW sys pe' L' ν' l' e' p) ≠ 0 then
      (PMF.normalize (Scheduler.expandContW sys pe' L' ν' l' e') h0'
          (Scheduler.expandContW_tsum_ne_top sys pe' L' ν' l' e')).bind (fun p =>
        (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).next e')
    else PMF.pure none) (some (l₁, μ₁)) = _
  rw [dif_pos h0, PMF.bind_apply]

open Classical in
/-- **The `none`-emission of `expandCont` as a posterior average** (analogue of
`postTauDraw_next_none`). -/
theorem Scheduler.expandCont_next_none (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (L' : List Label) (ν' : State) (l' : Label)
    (e' : AlterSeq State Label)
    (h0 : (∑' p, Scheduler.expandContW sys pe' L' ν' l' e' p) ≠ 0) :
    (Scheduler.expandCont sys pe' L' ν' l').next e' none
      = ∑' p, (PMF.normalize (Scheduler.expandContW sys pe' L' ν' l' e') h0
            (Scheduler.expandContW_tsum_ne_top sys pe' L' ν' l' e')) p *
          (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).next e' none := by
  classical
  change (if h0' : (∑' p, Scheduler.expandContW sys pe' L' ν' l' e' p) ≠ 0 then
      (PMF.normalize (Scheduler.expandContW sys pe' L' ν' l' e') h0'
          (Scheduler.expandContW_tsum_ne_top sys pe' L' ν' l' e')).bind (fun p =>
        (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).next e')
    else PMF.pure none) none = _
  rw [dif_pos h0, PMF.bind_apply]

/-- The **expand-segment posterior marginal** `expandZ e'` at a running history `e'` (boundary
`ν'`): the prior-weighted sum of the per-`p` segment schedulers' `probOf` (the RHS of the
filter-marginal). The third analogue of `drawZ`/`postTauZ`; here the prior is `beliefExpandW`. -/
noncomputable def Scheduler.expandZ (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (L' : List Label) (ν' : State) (l' : Label)
    (e' : AlterSeq State Label) (he' : e'.trans.Terminates) : ENNReal :=
  ∑' p : AlterSeq State Label × PMF State,
    pe'.beliefExpandW L' ν' p *
      (⟨PMF.pure ν', Scheduler.segmentScheduler pe' ν' l' p.1 p.2⟩
        : ProbabilisticExecution sys.toSystem).probOf e' he'

/-- `expandZ` depends only on the running history, not the termination proof. -/
theorem Scheduler.expandZ_congr (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (L' : List Label) (ν' : State) (l' : Label)
    (e e' : AlterSeq State Label) (h_eq : e = e')
    (he : e.trans.Terminates) (he' : e'.trans.Terminates) :
    Scheduler.expandZ sys pe' L' ν' l' e he = Scheduler.expandZ sys pe' L' ν' l' e' he' := by
  subst h_eq; rfl

/-- `expandZ` at a boundary-`ν'` history is exactly the posterior normaliser
`∑' p, expandContW … p`. -/
theorem Scheduler.expandZ_eq_tsum_expandContW (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (L' : List Label) (ν' : State) (l' : Label)
    (e' : AlterSeq State Label) (he' : e'.trans.Terminates) :
    Scheduler.expandZ sys pe' L' ν' l' e' he'
      = ∑' p, Scheduler.expandContW sys pe' L' ν' l' e' p := by
  unfold Scheduler.expandZ
  exact (tsum_congr (fun p => (Scheduler.expandContW_eq sys pe' L' ν' l' e' he' p).symm))

/-- **One-step kernel of `expandCont` as a posterior average** (analogue of
`postTauDraw_kernel_eq`). -/
theorem Scheduler.expandCont_kernel_eq (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (L' : List Label) (ν' : State) (l' : Label)
    (e' : AlterSeq State Label)
    (h0 : (∑' p, Scheduler.expandContW sys pe' L' ν' l' e' p) ≠ 0) (q : Label × State) :
    (⟨PMF.pure ν', Scheduler.expandCont sys pe' L' ν' l'⟩
        : ProbabilisticExecution sys.toSystem).kernel e' q
      = ∑' p, (PMF.normalize (Scheduler.expandContW sys pe' L' ν' l' e') h0
            (Scheduler.expandContW_tsum_ne_top sys pe' L' ν' l' e')) p *
          (⟨PMF.pure ν', Scheduler.segmentScheduler pe' ν' l' p.1 p.2⟩
            : ProbabilisticExecution sys.toSystem).kernel e' q := by
  classical
  obtain ⟨l₁, s'⟩ := q
  unfold ProbabilisticExecution.kernel
  have hexp : ∀ μ₁ : PMF State,
      (⟨PMF.pure ν', Scheduler.expandCont sys pe' L' ν' l'⟩
          : ProbabilisticExecution sys.toSystem).scheduler.next e' (some (l₁, μ₁)) * μ₁ s'
        = ∑' p, (PMF.normalize (Scheduler.expandContW sys pe' L' ν' l' e') h0
              (Scheduler.expandContW_tsum_ne_top sys pe' L' ν' l' e')) p *
            ((Scheduler.segmentScheduler pe' ν' l' p.1 p.2).next e' (some (l₁, μ₁)) * μ₁ s') := by
    intro μ₁
    rw [show (⟨PMF.pure ν', Scheduler.expandCont sys pe' L' ν' l'⟩
            : ProbabilisticExecution sys.toSystem).scheduler.next e' (some (l₁, μ₁))
          = (Scheduler.expandCont sys pe' L' ν' l').next e' (some (l₁, μ₁)) from rfl,
      Scheduler.expandCont_next_some sys pe' L' ν' l' e' h0 l₁ μ₁, ← ENNReal.tsum_mul_right]
    refine tsum_congr (fun p => ?_); rw [mul_assoc]
  rw [tsum_congr hexp, ENNReal.tsum_comm]
  refine tsum_congr (fun p => ?_)
  rw [ENNReal.tsum_mul_left]

/-- **Telescoping step (multiplicative kernel-ratio) for `expandZ`** (analogue of
`postTauZ_step`). -/
theorem Scheduler.expandZ_step (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (L' : List Label) (ν' : State) (l' : Label)
    (sq : Seq (Label × State)) (h_sq : sq.Terminates) (last : Label × State)
    (h_app : (sq.append (Seq.cons last Seq.nil)).Terminates) :
    Scheduler.expandZ sys pe' L' ν' l' ⟨ν', sq.append (Seq.cons last Seq.nil)⟩ h_app
      = Scheduler.expandZ sys pe' L' ν' l' ⟨ν', sq⟩ h_sq
        * (⟨PMF.pure ν', Scheduler.expandCont sys pe' L' ν' l'⟩
            : ProbabilisticExecution sys.toSystem).kernel ⟨ν', sq⟩ last := by
  classical
  set e' : AlterSeq State Label := ⟨ν', sq⟩ with he'_def
  set e'' : AlterSeq State Label := ⟨ν', sq.append (Seq.cons last Seq.nil)⟩ with he''_def
  have htel : ∀ p : AlterSeq State Label × PMF State,
      (⟨PMF.pure ν', Scheduler.segmentScheduler pe' ν' l' p.1 p.2⟩
          : ProbabilisticExecution sys.toSystem).probOf e'' h_app
        = (⟨PMF.pure ν', Scheduler.segmentScheduler pe' ν' l' p.1 p.2⟩
            : ProbabilisticExecution sys.toSystem).probOf e' h_sq
          * (⟨PMF.pure ν', Scheduler.segmentScheduler pe' ν' l' p.1 p.2⟩
              : ProbabilisticExecution sys.toSystem).kernel e' last := by
    intro p
    exact (ProbabilisticExecution.probOf_append_singleton _ ν' sq h_sq last h_app)
  by_cases h0 : Scheduler.expandZ sys pe' L' ν' l' e' h_sq = 0
  · rw [h0, zero_mul]
    have hz : ∀ p, pe'.beliefExpandW L' ν' p *
        (⟨PMF.pure ν', Scheduler.segmentScheduler pe' ν' l' p.1 p.2⟩
          : ProbabilisticExecution sys.toSystem).probOf e' h_sq = 0 :=
      ENNReal.tsum_eq_zero.mp h0
    unfold Scheduler.expandZ
    refine ENNReal.tsum_eq_zero.mpr (fun p => ?_)
    rw [htel p, ← mul_assoc, hz p, zero_mul]
  · have h0' : (∑' p, Scheduler.expandContW sys pe' L' ν' l' e' p) ≠ 0 := by
      rwa [← Scheduler.expandZ_eq_tsum_expandContW sys pe' L' ν' l' e' h_sq]
    rw [Scheduler.expandCont_kernel_eq sys pe' L' ν' l' e' h0' last]
    rw [show Scheduler.expandZ sys pe' L' ν' l' e' h_sq
          = ∑' p, Scheduler.expandContW sys pe' L' ν' l' e' p
        from Scheduler.expandZ_eq_tsum_expandContW sys pe' L' ν' l' e' h_sq]
    simp only [PMF.normalize_apply]
    rw [ProbabilisticExecution.normalize_cancel _
        (Scheduler.expandContW_tsum_ne_top sys pe' L' ν' l' e') _ h0']
    unfold Scheduler.expandZ
    refine tsum_congr (fun p => ?_)
    rw [Scheduler.expandContW_eq sys pe' L' ν' l' e' h_sq p, htel p, mul_assoc]

/-- **Base value `Z₀` for `expandZ`** (analogue of `postTauZ_nil`, NOT `1`). At the empty
history `⟨ν', nil⟩`, every segment scheduler realizes the empty execution with mass `1` (Dirac
source `pure ν'`), so the marginal collapses to the prior weight-sum `∑' p, beliefExpandW L' ν' p`
— the prior here is the `beliefExpandW` weight, not a full PMF. -/
theorem Scheduler.expandZ_nil (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (L' : List Label) (ν' : State) (l' : Label) :
    Scheduler.expandZ sys pe' L' ν' l' ⟨ν', Stream'.Seq.nil⟩ Stream'.Seq.terminates_nil
      = ∑' p, pe'.beliefExpandW L' ν' p := by
  unfold Scheduler.expandZ
  refine tsum_congr (fun p => ?_)
  rw [ProbabilisticExecution.probOf_nil]
  change pe'.beliefExpandW L' ν' p * (PMF.pure ν') ν' = _
  rw [PMF.pure_apply_self, mul_one]

/-- **Telescoping over `ofList`** (analogue of `postTauDraw_probOf_eq_postTauZ_ofList`): the
MULTIPLIED filter-marginal `Z₀ · probOf e = expandZ e` for histories `⟨ν', ofList trans⟩`, by
reverse induction. Base = `expandZ_nil` (= `Z₀`, `probOf nil = 1`); step =
`probOf_append_singleton` + IH + `expandZ_step`. -/
theorem Scheduler.expandCont_probOf_eq_expandZ_ofList (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (L' : List Label) (ν' : State) (l' : Label)
    (trans : List (Label × State))
    (hFin : (Seq.ofList trans : Seq (Label × State)).Terminates) :
    Scheduler.expandZ sys pe' L' ν' l' ⟨ν', Stream'.Seq.nil⟩ Stream'.Seq.terminates_nil
        * (⟨PMF.pure ν', Scheduler.expandCont sys pe' L' ν' l'⟩
            : ProbabilisticExecution sys.toSystem).probOf ⟨ν', Seq.ofList trans⟩ hFin
      = Scheduler.expandZ sys pe' L' ν' l' ⟨ν', Seq.ofList trans⟩ hFin := by
  classical
  induction trans using List.reverseRecOn with
  | nil =>
    have hnil : (⟨ν', Seq.ofList []⟩ : AlterSeq State Label)
        = ⟨ν', Stream'.Seq.nil⟩ := by simp [Stream'.Seq.ofList_nil]
    rw [ProbabilisticExecution.probOf_congr _ ⟨ν', Seq.ofList []⟩
        ⟨ν', Stream'.Seq.nil⟩ hnil hFin Stream'.Seq.terminates_nil,
      ProbabilisticExecution.probOf_nil,
      Scheduler.expandZ_congr sys pe' L' ν' l' ⟨ν', Seq.ofList []⟩
        ⟨ν', Stream'.Seq.nil⟩ hnil hFin Stream'.Seq.terminates_nil]
    change Scheduler.expandZ sys pe' L' ν' l' ⟨ν', Stream'.Seq.nil⟩ Stream'.Seq.terminates_nil
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
      ← Scheduler.expandZ_step sys pe' L' ν' l' (Seq.ofList rest) hrest_term last happ_term]
    exact Scheduler.expandZ_congr sys pe' L' ν' l'
      ⟨ν', (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩
      ⟨ν', Seq.ofList (rest ++ [last])⟩ heq_ext.symm happ_term hFin

/-- **KEYSTONE: the `expandCont` filter-marginal, MULTIPLIED form (the GAP-2 collapse).** The
prior weight-sum `Z₀ = ∑' p, beliefExpandW L' ν' p` times `expandCont.probOf e` (from `pure ν'`)
equals the prior-weighted sum of the per-`p` segment schedulers' `probOf`:
`Z₀ · expandCont.probOf e = ∑' p, beliefExpandW L' ν' p · (⟨pure ν', segmentScheduler …⟩).probOf
e`. Division-free (the base normaliser `Z₀` need not be `1`). This makes `expandCont.probOf`
factor through the per-`p` segment `probOf`, so the constant-mixture pathology (the OUTER belief
re-drawn each within-segment step, giving a product of mixtures) is GONE: the posterior
reconditioning telescopes (HMM/Bayes-filter `expandZ_step` kernel-ratio +
`expandCont_probOf_eq_expandZ_ofList`). -/
theorem Scheduler.expandCont_probOf_eq (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (L' : List Label) (ν' : State) (l' : Label)
    (e : AlterSeq State Label) (he : e.trans.Terminates) (he_init : e.init = ν') :
    (∑' p, pe'.beliefExpandW L' ν' p) *
      (⟨PMF.pure ν', Scheduler.expandCont sys pe' L' ν' l'⟩
        : ProbabilisticExecution sys.toSystem).probOf e he
      = ∑' p : AlterSeq State Label × PMF State,
          pe'.beliefExpandW L' ν' p
            * (⟨PMF.pure ν', Scheduler.segmentScheduler pe' ν' l' p.1 p.2⟩
                : ProbabilisticExecution sys.toSystem).probOf e he := by
  classical
  have he_ofList : e = ⟨ν', Seq.ofList (e.trans.toList he)⟩ := by
    obtain ⟨ei, et⟩ := e
    simp only at he_init
    subst he_init
    congr 1
    exact (Stream'.Seq.ofList_toList et he).symm
  have hFin' : (Seq.ofList (e.trans.toList he) : Seq (Label × State)).Terminates :=
    Stream'.Seq.terminates_ofList _
  rw [show (∑' p, pe'.beliefExpandW L' ν' p)
        = Scheduler.expandZ sys pe' L' ν' l' ⟨ν', Stream'.Seq.nil⟩ Stream'.Seq.terminates_nil
      from (Scheduler.expandZ_nil sys pe' L' ν' l').symm,
    ProbabilisticExecution.probOf_congr _ e
      ⟨ν', Seq.ofList (e.trans.toList he)⟩ he_ofList he hFin',
    Scheduler.expandCont_probOf_eq_expandZ_ofList sys pe' L' ν' l' (e.trans.toList he) hFin']
  unfold Scheduler.expandZ
  refine tsum_congr (fun p => ?_)
  rw [ProbabilisticExecution.probOf_congr _ e
      ⟨ν', Seq.ofList (e.trans.toList he)⟩ he_ofList he hFin']

/-- **Per-execution halt-mass marginal of `expandCont`, MULTIPLIED form** (the `haltMass`
analogue of `expandCont_probOf_eq`, mirroring `postTauDraw_haltMass_marginal`). `Z₀ ·
expandCont.haltMass e = ∑' p, beliefExpandW L' ν' p · (⟨pure ν', segmentScheduler … p⟩).haltMass
e`. Proven by multiplying the MULTIPLIED probOf marginal by the `none`-emission posterior
average; the `expandZ e` normaliser cancels. This is the GAP-2 collapse in halting-mass form
(what the ASSEMBLE `expandK`-collapse reads off). -/
theorem Scheduler.expandCont_haltMass_marginal (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (L' : List Label) (ν' : State) (l' : Label)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) (he_init : e.1.init = ν') :
    (∑' p, pe'.beliefExpandW L' ν' p) *
        (Scheduler.expandCont sys pe' L' ν' l').haltMass (PMF.pure ν') e
      = ∑' p : AlterSeq State Label × PMF State, pe'.beliefExpandW L' ν' p
          * (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).haltMass (PMF.pure ν') e := by
  classical
  unfold Scheduler.haltMass
  by_cases h0 : (∑' p, Scheduler.expandContW sys pe' L' ν' l' e.1 p) ≠ 0
  · -- nonvanishing normaliser: expand `next none`, multiply by the MULTIPLIED probOf marginal
    rw [Scheduler.expandCont_next_none sys pe' L' ν' l' e.1 h0]
    rw [show (∑' p, pe'.beliefExpandW L' ν' p) *
            ((⟨PMF.pure ν', Scheduler.expandCont sys pe' L' ν' l'⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2
              * ∑' p, (PMF.normalize (Scheduler.expandContW sys pe' L' ν' l' e.1) h0
                  (Scheduler.expandContW_tsum_ne_top sys pe' L' ν' l' e.1)) p *
                (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).next e.1 none)
          = ((∑' p, pe'.beliefExpandW L' ν' p) *
              (⟨PMF.pure ν', Scheduler.expandCont sys pe' L' ν' l'⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2)
            * ∑' p, (PMF.normalize (Scheduler.expandContW sys pe' L' ν' l' e.1) h0
                  (Scheduler.expandContW_tsum_ne_top sys pe' L' ν' l' e.1)) p *
                (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).next e.1 none by ring,
      Scheduler.expandCont_probOf_eq sys pe' L' ν' l' e.1 e.2 he_init]
    rw [show (∑' p : AlterSeq State Label × PMF State, pe'.beliefExpandW L' ν' p
            * (⟨PMF.pure ν', Scheduler.segmentScheduler pe' ν' l' p.1 p.2⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2)
          = ∑' p, Scheduler.expandContW sys pe' L' ν' l' e.1 p from
        tsum_congr (fun p =>
          (Scheduler.expandContW_eq sys pe' L' ν' l' e.1 e.2 p).symm)]
    simp only [PMF.normalize_apply]
    rw [ProbabilisticExecution.normalize_cancel _
        (Scheduler.expandContW_tsum_ne_top sys pe' L' ν' l' e.1) _ h0]
    refine tsum_congr (fun p => ?_)
    rw [Scheduler.expandContW_eq sys pe' L' ν' l' e.1 e.2 p, mul_assoc]
  · -- vanishing normaliser: expandZ e = 0 ⟹ probOf e = 0 and every prior·probOf(e) = 0
    push Not at h0
    have hZ0 : Scheduler.expandZ sys pe' L' ν' l' e.1 e.2 = 0 := by
      rw [Scheduler.expandZ_eq_tsum_expandContW sys pe' L' ν' l' e.1 e.2]; exact h0
    rw [show (∑' p, pe'.beliefExpandW L' ν' p) *
            ((⟨PMF.pure ν', Scheduler.expandCont sys pe' L' ν' l'⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2
              * (Scheduler.expandCont sys pe' L' ν' l').next e.1 none)
          = ((∑' p, pe'.beliefExpandW L' ν' p) *
              (⟨PMF.pure ν', Scheduler.expandCont sys pe' L' ν' l'⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2)
            * (Scheduler.expandCont sys pe' L' ν' l').next e.1 none by ring,
      Scheduler.expandCont_probOf_eq sys pe' L' ν' l' e.1 e.2 he_init,
      show (∑' p : AlterSeq State Label × PMF State, pe'.beliefExpandW L' ν' p
            * (⟨PMF.pure ν', Scheduler.segmentScheduler pe' ν' l' p.1 p.2⟩
                : ProbabilisticExecution sys.toSystem).probOf e.1 e.2)
          = Scheduler.expandZ sys pe' L' ν' l' e.1 e.2 from rfl,
      hZ0, zero_mul]
    have hz : ∀ p, pe'.beliefExpandW L' ν' p *
        (⟨PMF.pure ν', Scheduler.segmentScheduler pe' ν' l' p.1 p.2⟩
          : ProbabilisticExecution sys.toSystem).probOf e.1 e.2 = 0 :=
      ENNReal.tsum_eq_zero.mp hZ0
    refine (ENNReal.tsum_eq_zero.mpr (fun p => ?_)).symm
    change pe'.beliefExpandW L' ν' p *
        ((⟨PMF.pure ν', Scheduler.segmentScheduler pe' ν' l' p.1 p.2⟩
          : ProbabilisticExecution sys.toSystem).probOf e.1 e.2
            * (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).next e.1 none) = 0
    rw [← mul_assoc, hz p, zero_mul]

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
          (Scheduler.expandCont sys pe' L ν' l).next (sys.internalSuffix e)
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
            (Scheduler.expandCont sys pe'
                ((sys.trace e).toList
                  (Stream'.Seq.terminates_map_iff.mpr (Stream'.Seq.terminates_filter _ _ hT)))
                (sys.internalSuffix e).init l').next (sys.internalSuffix e)
      else PMF.pure none).support at h_supp
    rw [dif_pos h_term] at h_supp
    rw [← hd, ← hν', ← hL] at h_supp
    cases hgl : L.getLast? with
    | none =>
      rw [hgl] at h_supp
      exact h_inner (Scheduler.drawAndRun pe' ⟨sys.toSystem.init, Seq.nil⟩) h_supp
    | some l' =>
      rw [hgl] at h_supp
      exact h_inner (Scheduler.expandCont sys pe' L ν' l') h_supp

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

/-! ### `expandCont`: the segment continuation scheduler (PEEL step 1b) -/

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

open Classical in
/-- **`Z₀`-multiplied form of `expandK` as a prior-weighted segment trace-`[l]` mass** (the
GAP-2 collapse, read off through `expandCont_haltMass_marginal`). Multiplying `expandK L' l' l
g ν'` by the prior normaliser `Z₀ = ∑' p, beliefExpandW L' ν' p` factors it through the per-`p`
segment scheduler's trace-`[l]` `g`-mass:
`Z₀ · expandK L' l' l g ν' = ∑' p, beliefExpandW L' ν' p · (∑' e, segmentScheduler.haltMass
(pure ν') e · [trace e = [l]]·g(end))`. Pure tsum bookkeeping on top of
`expandCont_haltMass_marginal`. -/
theorem expandK_Z_mul {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (L' : List Label) (l' l : Label) (g : State → ENNReal) (ν' : State) :
    (∑' p, pe'.beliefExpandW L' ν' p) * pe'.expandK L' l' l g ν'
      = ∑' p : AlterSeq State Label × PMF State, pe'.beliefExpandW L' ν' p
          * ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
              (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).haltMass (PMF.pure ν') e
                * (if sys.trace e.1 = Seq.ofList [l] then g (e.1.endState e.2) else 0) := by
  classical
  unfold ProbabilisticExecution.expandK
  -- Pull `Z₀` into the `e`-sum, apply the haltMass marginal per `e`, swap to `p`-outer.
  rw [← ENNReal.tsum_mul_left]
  rw [show (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        (∑' p, pe'.beliefExpandW L' ν' p) *
          ((Scheduler.expandCont sys pe' L' ν' l').haltMass (PMF.pure ν') e
            * (if sys.trace e.1 = Seq.ofList [l] then g (e.1.endState e.2) else 0)))
      = ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          ∑' p : AlterSeq State Label × PMF State, pe'.beliefExpandW L' ν' p
            * ((Scheduler.segmentScheduler pe' ν' l' p.1 p.2).haltMass (PMF.pure ν') e
              * (if sys.trace e.1 = Seq.ofList [l] then g (e.1.endState e.2) else 0)) from by
    refine tsum_congr (fun e => ?_)
    by_cases hinit : e.1.init = ν'
    · -- on-boundary: factor `Z₀ · halt = ∑' p, beliefExpandW · seg.halt` then distribute the test
      rw [show (∑' p, pe'.beliefExpandW L' ν' p) *
              ((Scheduler.expandCont sys pe' L' ν' l').haltMass (PMF.pure ν') e
                * (if sys.trace e.1 = Seq.ofList [l] then g (e.1.endState e.2) else 0))
            = ((∑' p, pe'.beliefExpandW L' ν' p) *
                (Scheduler.expandCont sys pe' L' ν' l').haltMass (PMF.pure ν') e)
              * (if sys.trace e.1 = Seq.ofList [l] then g (e.1.endState e.2) else 0) by ring,
        Scheduler.expandCont_haltMass_marginal sys pe' L' ν' l' e hinit, ← ENNReal.tsum_mul_right]
      exact tsum_congr (fun p => by ring)
    · -- off-boundary: `expandCont.haltMass = 0` (Dirac source) and each `seg.haltMass = 0` too
      have hlhs : (Scheduler.expandCont sys pe' L' ν' l').haltMass (PMF.pure ν') e = 0 := by
        unfold Scheduler.haltMass
        rw [ProbabilisticExecution.probOf_init_factor _ (PMF.pure ν') e.1 e.2,
          PMF.pure_apply_of_ne _ _ hinit, zero_mul, zero_mul]
      rw [hlhs, zero_mul, mul_zero]
      refine (ENNReal.tsum_eq_zero.mpr (fun p => ?_)).symm
      have hwit : (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).haltMass (PMF.pure ν') e = 0 := by
        unfold Scheduler.haltMass
        rw [ProbabilisticExecution.probOf_init_factor _ (PMF.pure ν') e.1 e.2,
          PMF.pure_apply_of_ne _ _ hinit, zero_mul, zero_mul]
      rw [hwit, zero_mul, mul_zero]]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun p => ?_)
  rw [← ENNReal.tsum_mul_left]

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

/-- **A `WeakScheduler` cannot realize an externally-labelled execution.** Since a
`WeakScheduler` only emits internal labels, any execution `e` with a nonempty external trace
has `probOf e = 0`: a positive `probOf` would force every transition internal, hence an empty
trace. -/
theorem WeakScheduler.probOf_eq_zero_of_trace_ne_nil {State Label : Type}
    {sys : LabelledSystem State Label} (σ : WeakScheduler sys) (μ_init : PMF State)
    (e : AlterSeq State Label) (h : e.trans.Terminates) (htr : sys.trace e ≠ Seq.nil) :
    (⟨μ_init, σ.toScheduler⟩ : ProbabilisticExecution sys.toSystem).probOf e h = 0 := by
  classical
  by_contra hpos
  apply htr
  have hall := WeakScheduler.probOf_all_internal σ μ_init e h hpos
  unfold LabelledSystem.trace
  rw [show e.trans = Seq.ofList (e.trans.toList h) from (Stream'.Seq.ofList_toList _ _).symm]
  rw [Seq.filter_ofList_eq_nil_pub (fun p => ¬ sys.internal p.1) (e.trans.toList h)
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

/-- **L1: `extStep` emits nothing after the first step.** Past the initial empty history
(`e.trans ≠ nil`), the single-external-step scheduler `extStep sys ν l κ` always halts
(`next = pure none`), so it never emits a `some` step. -/
theorem extStep_next_some_eq_zero {State Label : Type} (sys : LabelledSystem State Label)
    (ν : PMF State) (l : Label) (κ : State → PMF (PMF State))
    (hκ : ∀ s ∈ ν.support, ∀ μ ∈ (κ s).support, sys.step s l μ)
    (e : AlterSeq State Label) (he : e.trans ≠ Seq.nil) (a : Label × PMF State) :
    (Scheduler.extStep sys ν l κ hκ).next e (some a) = 0 := by
  classical
  change (if e.trans = Seq.nil ∧ e.init ∈ ν.support then
      (κ e.init).map (fun μ => some (l, μ)) else PMF.pure none) (some a) = 0
  rw [if_neg (fun h => he h.1)]
  simp [PMF.pure_apply]

open Classical in
/-- **L2′: `preHsWitness` emits nothing once past its external label.** For an external `l`,
`preHsWitness sys s l μ = bind σpre (extStep …)`, where `σpre` is an internal-only weak-τ
witness and `extStep` emits its single external label only at the empty history. At any
terminating execution `e` whose external trace is already nonempty (i.e. `e` has consumed the
external `l`), `preHsWitness` emits no further step: `next e (some a) = 0`. Discharges H2's core
via `Scheduler.bind_next_some_eq_zero` (the `none`-split is dead because the internal-only
`σpre` cannot realize an externally-labelled `e`; every `some`-split lands `extStep` on a
nonempty suffix, where it halts). -/
theorem Scheduler.preHsWitness_next_some_eq_zero (sys : LabelledSystem State Label)
    (s : State) (l : Label) (μ : PMF State) (h : sys^w.step s l μ) (hext : ¬ sys.internal l)
    (e : AlterSeq State Label) (hT : e.trans.Terminates) (htr : sys.trace e ≠ Seq.nil)
    (a : Label × PMF State) :
    (Scheduler.preHsWitness sys s l μ).next e (some a) = 0 := by
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
  rw [hsched]
  refine Scheduler.bind_next_some_eq_zero σpre (fun _ => σext) e hT a ?_ ?_
  · -- `σpre` (internal-only weak-τ witness) cannot realize an externally-labelled `e`.
    exact WeakScheduler.probOf_eq_zero_of_trace_ne_nil h_pre.witnessScheduler (PMF.pure e.init)
      e hT htr
  · -- every nonempty suffix lands `extStep` past its external label, where it halts.
    intro s' t ht
    exact extStep_next_some_eq_zero sys ν l h_mid.kernel h_mid.kernel_step ⟨s', t⟩ ht a

open Classical in
/-- **L3: `drawAndRun` emits nothing once past the drawn external label.** Each committed
witness `drawWit (E''.endState) opt` is either `haltNow` (for the `none` draw) or a
`preHsWitness` (for a `some (l, μ)` draw, external by `hExt`); both are silent at any execution
whose external trace is already nonempty. Since `drawAndRun.next` is the posterior average of
these witnesses' emissions, it too emits nothing: `next e' (some a) = 0`. -/
theorem Scheduler.drawAndRun_next_some_eq_zero {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (E'' : AlterSeq State Label) (hT : E''.trans.Terminates) (e' : AlterSeq State Label)
    (he' : e'.trans.Terminates) (htr : sys.trace e' ≠ Seq.nil) (a : Label × PMF State) :
    (Scheduler.drawAndRun pe' E'').next e' (some a) = 0 := by
  classical
  by_cases h0 : (∑' opt, Scheduler.drawAndRunW pe' E'' hT e' opt) ≠ 0
  · rw [Scheduler.drawAndRun_next_some pe' E'' hT e' h0 a.1 a.2]
    refine ENNReal.tsum_eq_zero.mpr (fun opt => ?_)
    -- For each draw `opt`: either its posterior weight is `0`, or its committed witness is silent.
    cases opt with
    | none =>
      have hwit : (Scheduler.drawWit sys (E''.endState hT) none).next e' (some (a.1, a.2)) = 0 := by
        change (Scheduler.haltNow sys).next e' (some (a.1, a.2)) = 0
        simp [Scheduler.haltNow, PMF.pure_apply]
      rw [hwit, mul_zero]
    | some lμ =>
      obtain ⟨l', μ'⟩ := lμ
      by_cases hz : pe'.scheduler.next E'' (some (l', μ')) = 0
      · -- off-support draw: its posterior weight vanishes (the prior factor is `0`).
        have hwz : (PMF.normalize (Scheduler.drawAndRunW pe' E'' hT e') h0
            (Scheduler.drawAndRunW_tsum_ne_top pe' E'' hT e')) (some (l', μ')) = 0 := by
          rw [PMF.normalize_apply]
          have : Scheduler.drawAndRunW pe' E'' hT e' (some (l', μ')) = 0 := by
            unfold Scheduler.drawAndRunW; rw [hz, zero_mul]
          rw [this, zero_mul]
        rw [hwz, zero_mul]
      · -- in-support draw: external label (`hExt`) + genuine step ⟹ the witness is silent.
        have h_supp : some (l', μ') ∈ (pe'.scheduler.next E'').support :=
          (PMF.mem_support_iff _ _).mpr hz
        have hint : ¬ sys.internal l' := hExt E'' l' μ' h_supp
        have hstep : sys^w.step (E''.endState hT) l' μ' :=
          pe'.step_of_mem_support E'' hT l' μ' h_supp
        have hwit : (Scheduler.drawWit sys (E''.endState hT) (some (l', μ'))).next e'
            (some (a.1, a.2)) = 0 := by
          change (Scheduler.preHsWitness sys (E''.endState hT) l' μ').next e' (some (a.1, a.2)) = 0
          exact Scheduler.preHsWitness_next_some_eq_zero sys (E''.endState hT) l' μ' hstep hint
            e' he' htr (a.1, a.2)
        rw [hwit, mul_zero]
  · -- zero posterior normaliser ⟹ `drawAndRun.next e' = pure none`.
    push Not at h0
    have : (Scheduler.drawAndRun pe' E'').next e' = PMF.pure none := by
      change (if hT' : E''.trans.Terminates then
          if h0' : (∑' opt, Scheduler.drawAndRunW pe' E'' hT' e' opt) ≠ 0 then
            (PMF.normalize (Scheduler.drawAndRunW pe' E'' hT' e') h0'
                (Scheduler.drawAndRunW_tsum_ne_top pe' E'' hT' e')).bind (fun opt =>
              match opt with
              | none        => PMF.pure none
              | some (l, μ) => (Scheduler.preHsWitness sys (E''.endState hT') l μ).next e')
          else PMF.pure none
        else PMF.pure none) = PMF.pure none
      rw [dif_pos hT, dif_neg (by rw [h0]; exact fun h => h rfl)]
    rw [this, PMF.pure_apply, if_neg (by simp)]

open Classical in
/-- **`drawAndRun` pushforward.** `drawAndRun pe' E''`, run from the Dirac source
`pure (E''.endState)` and restricted (via the trace indicator) to halting executions whose
external trace is `[l]`, integrates `g` to the `pe'`-emission-weighted hyper-step expectation:
the sum over drawn `μ` of `pe'.next E'' (some (l, μ)) * hsExpect (E''.endState) l μ g`.

`drawAndRun` is the trajectory-conditioned Bayesian posterior (the re-draw fix), so the
keystone posterior-bind filter-marginal `drawAndRun_probOf_eq` applies with normaliser
`Z₀ = 1` (its prior `pe'.next E''` is a full PMF): `drawAndRun.haltMass` equals the
`pe'.next E''`-weighted sum of the component witnesses' halt masses. The trace-`[l]` indicator
then splits per option — `some (l', μ)` (external by `hExt`) contributes `hsExpect` via
`preHsWitness_pushforward`, while `none` halts at trace `[]` ≠ `[l]` and drops out. -/
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
/-- **A scheduler emitting only internal labels has trace-nil halting executions.** Generic
form of `WeakScheduler.haltMass_trace_nil`: if every `some (l, μ)` that `σ` ever emits has
internal `l`, then any positive-halt-mass execution from any source has empty external trace.
The kernel-along-the-path argument mirrors `WeakScheduler.probOf_all_internal`. -/
theorem Scheduler.haltMass_trace_nil_of_internal {State Label : Type}
    {sys : LabelledSystem State Label} (σ : Scheduler sys.toSystem) (μ_init : PMF State)
    (hint : ∀ (e' : AlterSeq State Label) (l : Label) (μ : PMF State),
        σ.next e' (some (l, μ)) ≠ 0 → sys.internal l)
    (e : {e : AlterSeq State Label // e.trans.Terminates})
    (hne : σ.haltMass μ_init e ≠ 0) :
    sys.trace e.1 = Seq.nil := by
  classical
  have hprob : (⟨μ_init, σ⟩ : ProbabilisticExecution sys.toSystem).probOf e.1 e.2 ≠ 0 := by
    intro h0; apply hne
    change (⟨μ_init, σ⟩ : ProbabilisticExecution sys.toSystem).probOf e.1 e.2 * σ.next e.1 none = 0
    rw [h0, zero_mul]
  -- Every transition label is internal: induct on the reversed transition list.
  have hall : ∀ p ∈ e.1.trans.toList e.2, sys.internal p.1 := by
    have hprob' : (⟨PMF.pure e.1.init, σ⟩ : ProbabilisticExecution sys.toSystem).probOf e.1 e.2
        ≠ 0 := by
      intro h0; apply hprob
      rw [ProbabilisticExecution.probOf_init_factor σ μ_init e.1 e.2, h0, mul_zero]
    have key : ∀ (L : List (Label × State)) (s₀ : State)
        (hL : (Seq.ofList L : Seq (Label × State)).Terminates),
        (⟨PMF.pure s₀, σ⟩ : ProbabilisticExecution sys.toSystem).probOf
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
        have hfac : (⟨PMF.pure s₀, σ⟩
              : ProbabilisticExecution sys.toSystem).probOf ⟨s₀, Seq.ofList (rest ++ [last])⟩ hL
            = (⟨PMF.pure s₀, σ⟩
                : ProbabilisticExecution sys.toSystem).probOf ⟨s₀, Seq.ofList rest⟩ hrest
              * (⟨PMF.pure s₀, σ⟩
                  : ProbabilisticExecution sys.toSystem).kernel ⟨s₀, Seq.ofList rest⟩ last := by
          have hrw : (⟨PMF.pure s₀, σ⟩
                : ProbabilisticExecution sys.toSystem).probOf ⟨s₀, Seq.ofList (rest ++ [last])⟩ hL
              = (⟨PMF.pure s₀, σ⟩
                  : ProbabilisticExecution sys.toSystem).probOf
                    ⟨s₀, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩ happ := by
            congr 1
            exact AlterSeq.mk.injEq .. ▸ ⟨rfl, heq⟩
          rw [hrw, ProbabilisticExecution.probOf_append_singleton _ s₀ (Seq.ofList rest) hrest
            last happ]
        rw [hfac] at hposL
        have hprev_ne : (⟨PMF.pure s₀, σ⟩
            : ProbabilisticExecution sys.toSystem).probOf ⟨s₀, Seq.ofList rest⟩ hrest ≠ 0 :=
          fun h0 => hposL (by rw [h0, zero_mul])
        have hker_ne : (⟨PMF.pure s₀, σ⟩
            : ProbabilisticExecution sys.toSystem).kernel ⟨s₀, Seq.ofList rest⟩ last ≠ 0 :=
          fun h0 => hposL (by rw [h0, mul_zero])
        rcases List.mem_append.mp hp with hp_rest | hp_last
        · exact ih s₀ hrest hprev_ne p hp_rest
        · rw [List.mem_singleton] at hp_last
          subst hp_last
          -- `kernel ≠ 0 ⟹ some (p.1, μ) emitted ⟹ p.1 internal` via `hint`.
          unfold ProbabilisticExecution.kernel at hker_ne
          by_contra h_ext
          apply hker_ne
          refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
          by_cases hsupp : σ.next ⟨s₀, Seq.ofList rest⟩ (some (p.1, μ)) = 0
          · change σ.next ⟨s₀, Seq.ofList rest⟩ (some (p.1, μ)) * μ p.2 = 0
            rw [hsupp, zero_mul]
          · exact absurd (hint ⟨s₀, Seq.ofList rest⟩ p.1 μ hsupp) h_ext
    have he_eq : (⟨e.1.init, Seq.ofList (e.1.trans.toList e.2)⟩ : AlterSeq State Label) = e.1 := by
      congr 1; exact Stream'.Seq.ofList_toList e.1.trans e.2
    have hterm' : (Seq.ofList (e.1.trans.toList e.2) : Seq (Label × State)).Terminates := by
      rw [Stream'.Seq.ofList_toList e.1.trans e.2]; exact e.2
    have hpos'' : (⟨PMF.pure e.1.init, σ⟩
        : ProbabilisticExecution sys.toSystem).probOf
          ⟨e.1.init, Seq.ofList (e.1.trans.toList e.2)⟩ hterm' ≠ 0 := by
      rw [ProbabilisticExecution.probOf_congr (⟨PMF.pure e.1.init, σ⟩
          : ProbabilisticExecution sys.toSystem) _ e.1 he_eq hterm' e.2]
      exact hprob'
    exact key (e.1.trans.toList e.2) e.1.init hterm' hpos''
  -- trace = nil since every transition label is internal
  unfold LabelledSystem.trace
  rw [show e.1.trans = Seq.ofList (e.1.trans.toList e.2) from (Stream'.Seq.ofList_toList _ _).symm]
  rw [Seq.filter_ofList_eq_nil_pub (fun p => ¬ sys.internal p.1) (e.1.trans.toList e.2)
    (fun x hx => by simpa using hall x hx), Stream'.Seq.map_nil]

open Classical in
/-- **`postTauDraw` emits only internal labels.** Its `next` is a posterior average of the
post-τ witnesses `postTauWitness`, each of which is internal-only (a `weakTau` witness, or
`haltNow` which emits no `some`). -/
theorem Scheduler.postTauDraw_internal_only {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (E' : AlterSeq State Label) (l : Label) (e' : AlterSeq State Label) (l₁ : Label)
    (μ₁ : PMF State) (hne : (Scheduler.postTauDraw pe' E' l).next e' (some (l₁, μ₁)) ≠ 0) :
    sys.internal l₁ := by
  classical
  -- The post-τ witness emits only internal labels.
  have hwit : ∀ (μ : PMF State) (hT : E'.trans.Terminates),
      (Scheduler.postTauWitness sys (E'.endState hT) l μ).next e' (some (l₁, μ₁)) ≠ 0
        → sys.internal l₁ := by
    intro μ hT hwne
    unfold Scheduler.postTauWitness at hwne
    by_cases hcond : (¬ sys.internal l) ∧ sys^w.step (E'.endState hT) l μ
    · rw [dif_pos hcond] at hwne
      exact (((hcond.2.resolve_left (fun hl => hcond.1 hl.1)).2).weakTau_post.witnessScheduler
        ).internal_only e' l₁ μ₁ ((PMF.mem_support_iff _ _).mpr hwne)
    · rw [dif_neg hcond] at hwne
      -- `haltNow` emits only `none`.
      exact absurd (PMF.pure_apply_of_ne _ (some (l₁, μ₁)) (by simp)) hwne
  -- Reduce `postTauDraw.next` to the witness emissions.
  by_cases hT : E'.trans.Terminates
  · by_cases h0 : (∑' μ, Scheduler.postTauDrawW pe' E' hT l e' μ) ≠ 0
    · rw [Scheduler.postTauDraw_next_some pe' E' hT l e' h0 l₁ μ₁] at hne
      obtain ⟨μ, hμ⟩ : ∃ μ, (PMF.normalize (Scheduler.postTauDrawW pe' E' hT l e') h0
          (Scheduler.postTauDrawW_tsum_ne_top pe' E' hT l e')) μ *
          (Scheduler.postTauWitness sys (E'.endState hT) l μ).next e' (some (l₁, μ₁)) ≠ 0 := by
        by_contra hall
        rw [not_exists] at hall
        exact hne (ENNReal.tsum_eq_zero.mpr (fun μ => not_not.mp (hall μ)))
      have hwne : (Scheduler.postTauWitness sys (E'.endState hT) l μ).next e' (some (l₁, μ₁)) ≠ 0 :=
        fun h => hμ (by rw [h, mul_zero])
      exact hwit μ hT hwne
    · exfalso; apply hne
      change (if hT' : E'.trans.Terminates then
          if h0' : (∑' μ, Scheduler.postTauDrawW pe' E' hT' l e' μ) ≠ 0 then _
          else PMF.pure none
        else PMF.pure none) (some (l₁, μ₁)) = 0
      rw [dif_pos hT, dif_neg h0]
      exact PMF.pure_apply_of_ne _ _ (by simp)
  · exfalso; apply hne
    change (if hT' : E'.trans.Terminates then _ else PMF.pure none) (some (l₁, μ₁)) = 0
    rw [dif_neg hT]
    exact PMF.pure_apply_of_ne _ _ (by simp)

open Classical in
/-- **An internal-only scheduler cannot realize an externally-labelled execution** (`probOf`
form of `Scheduler.haltMass_trace_nil_of_internal`). If every `some (l, μ)` that `σ` ever emits
has internal `l`, then any execution `e` with nonempty external trace has `probOf e = 0`. -/
theorem Scheduler.probOf_eq_zero_of_trace_ne_nil_of_internal {State Label : Type}
    {sys : LabelledSystem State Label} (σ : Scheduler sys.toSystem) (μ_init : PMF State)
    (hint : ∀ (e' : AlterSeq State Label) (l : Label) (μ : PMF State),
        σ.next e' (some (l, μ)) ≠ 0 → sys.internal l)
    (e : AlterSeq State Label) (h : e.trans.Terminates) (htr : sys.trace e ≠ Seq.nil) :
    (⟨μ_init, σ⟩ : ProbabilisticExecution sys.toSystem).probOf e h = 0 := by
  classical
  by_contra hpos
  apply htr
  -- `probOf ≠ 0 ⟹ haltMass ≠ 0` is NOT available, so route through the trace-nil-of-internal
  -- lemma at the *halt* of `e`: append a halting step. Instead, reduce to its `hall` core by
  -- noticing `haltMass_trace_nil_of_internal` only needs `probOf ≠ 0` (its `hne` is used solely
  -- to derive `probOf ≠ 0`). We re-run the same all-internal induction directly here.
  have hprob' : (⟨PMF.pure e.init, σ⟩ : ProbabilisticExecution sys.toSystem).probOf e h ≠ 0 := by
    intro h0; apply hpos
    rw [ProbabilisticExecution.probOf_init_factor σ μ_init e h, h0, mul_zero]
  have hall : ∀ p ∈ e.trans.toList h, sys.internal p.1 := by
    have key : ∀ (L : List (Label × State)) (s₀ : State)
        (hL : (Seq.ofList L : Seq (Label × State)).Terminates),
        (⟨PMF.pure s₀, σ⟩ : ProbabilisticExecution sys.toSystem).probOf
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
        have hfac : (⟨PMF.pure s₀, σ⟩
              : ProbabilisticExecution sys.toSystem).probOf ⟨s₀, Seq.ofList (rest ++ [last])⟩ hL
            = (⟨PMF.pure s₀, σ⟩
                : ProbabilisticExecution sys.toSystem).probOf ⟨s₀, Seq.ofList rest⟩ hrest
              * (⟨PMF.pure s₀, σ⟩
                  : ProbabilisticExecution sys.toSystem).kernel ⟨s₀, Seq.ofList rest⟩ last := by
          have hrw : (⟨PMF.pure s₀, σ⟩
                : ProbabilisticExecution sys.toSystem).probOf ⟨s₀, Seq.ofList (rest ++ [last])⟩ hL
              = (⟨PMF.pure s₀, σ⟩
                  : ProbabilisticExecution sys.toSystem).probOf
                    ⟨s₀, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩ happ := by
            congr 1
            exact AlterSeq.mk.injEq .. ▸ ⟨rfl, heq⟩
          rw [hrw, ProbabilisticExecution.probOf_append_singleton _ s₀ (Seq.ofList rest) hrest
            last happ]
        rw [hfac] at hposL
        have hprev_ne : (⟨PMF.pure s₀, σ⟩
            : ProbabilisticExecution sys.toSystem).probOf ⟨s₀, Seq.ofList rest⟩ hrest ≠ 0 :=
          fun h0 => hposL (by rw [h0, zero_mul])
        have hker_ne : (⟨PMF.pure s₀, σ⟩
            : ProbabilisticExecution sys.toSystem).kernel ⟨s₀, Seq.ofList rest⟩ last ≠ 0 :=
          fun h0 => hposL (by rw [h0, mul_zero])
        rcases List.mem_append.mp hp with hp_rest | hp_last
        · exact ih s₀ hrest hprev_ne p hp_rest
        · rw [List.mem_singleton] at hp_last
          subst hp_last
          unfold ProbabilisticExecution.kernel at hker_ne
          by_contra h_ext
          apply hker_ne
          refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
          by_cases hsupp : σ.next ⟨s₀, Seq.ofList rest⟩ (some (p.1, μ)) = 0
          · change σ.next ⟨s₀, Seq.ofList rest⟩ (some (p.1, μ)) * μ p.2 = 0
            rw [hsupp, zero_mul]
          · exact absurd (hint ⟨s₀, Seq.ofList rest⟩ p.1 μ hsupp) h_ext
    have he_eq : (⟨e.init, Seq.ofList (e.trans.toList h)⟩ : AlterSeq State Label) = e := by
      congr 1; exact Stream'.Seq.ofList_toList e.trans h
    have hterm' : (Seq.ofList (e.trans.toList h) : Seq (Label × State)).Terminates := by
      rw [Stream'.Seq.ofList_toList e.trans h]; exact h
    have hpos'' : (⟨PMF.pure e.init, σ⟩
        : ProbabilisticExecution sys.toSystem).probOf
          ⟨e.init, Seq.ofList (e.trans.toList h)⟩ hterm' ≠ 0 := by
      rw [ProbabilisticExecution.probOf_congr (⟨PMF.pure e.init, σ⟩
          : ProbabilisticExecution sys.toSystem) _ e he_eq hterm' h]
      exact hprob'
    exact key (e.trans.toList h) e.init hterm' hpos''
  unfold LabelledSystem.trace
  rw [show e.trans = Seq.ofList (e.trans.toList h) from (Stream'.Seq.ofList_toList _ _).symm]
  rw [Seq.filter_ofList_eq_nil_pub (fun p => ¬ sys.internal p.1) (e.trans.toList h)
    (fun x hx => by simpa using hall x hx), Stream'.Seq.map_nil]

open Classical in
/-- **L4: `segmentScheduler` emits nothing once past the external label.** With
`E'.trans.Terminates`, `segmentScheduler = bind (postTauDraw …) (drawAndRun …)`, where
`postTauDraw` is internal-only and `drawAndRun` is silent on external-trace suffixes (L3). For a
terminating `e` whose external trace is already nonempty, every live split lands `drawAndRun` on
a suffix that carries the full (nonempty) external trace (the internal-only prefix contributes
nothing), where it is silent. Hence `next e (some a) = 0`. -/
theorem Scheduler.segmentScheduler_next_some_eq_zero {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (ν' : State) (l : Label) (E' : AlterSeq State Label) (μ : PMF State)
    (e : AlterSeq State Label) (hT : e.trans.Terminates) (htr : sys.trace e ≠ Seq.nil)
    (a : Label × PMF State) :
    (Scheduler.segmentScheduler pe' ν' l E' μ).next e (some a) = 0 := by
  classical
  by_cases hTE : E'.trans.Terminates
  · have hsched : Scheduler.segmentScheduler pe' ν' l E' μ
        = Scheduler.bind (Scheduler.postTauDraw pe' E' l)
            (fun σ_k => Scheduler.drawAndRun pe'
              ⟨E'.init, E'.trans.append (Seq.cons (l, σ_k) Seq.nil)⟩) := by
      unfold Scheduler.segmentScheduler; rw [dif_pos hTE]
    rw [hsched]
    refine Scheduler.bind_next_some_eq_zero_of_suffix (Scheduler.postTauDraw pe' E' l) _ e hT a
      ?_ ?_
    · -- `postTauDraw` is internal-only, so it cannot realize the externally-labelled `e`.
      exact Scheduler.probOf_eq_zero_of_trace_ne_nil_of_internal (Scheduler.postTauDraw pe' E' l)
        (PMF.pure e.init)
        (fun e' l₁ μ₁ hne => Scheduler.postTauDraw_internal_only pe' E' l e' l₁ μ₁ hne)
        e hT htr
    · -- at each live split, the suffix carries the full (nonempty) external trace ⟹ L3 silences.
      intro j hj hpre_ne
      -- the internal-only prefix `take j` has trace nil.
      have hpre_nil : sys.trace (⟨e.init, Seq.ofList (e.trans.take j)⟩ : AlterSeq State Label)
          = Seq.nil := by
        refine Scheduler.haltMass_trace_nil_of_internal (Scheduler.postTauDraw pe' E' l)
          (PMF.pure e.init)
          (fun e' l₁ μ₁ hne => Scheduler.postTauDraw_internal_only pe' E' l e' l₁ μ₁ hne)
          ⟨⟨e.init, Seq.ofList (e.trans.take j)⟩, Stream'.Seq.terminates_ofList _⟩ hpre_ne
      -- the suffix `drop j` carries the full trace of `e`.
      have hdropT : (e.trans.drop j).Terminates := Stream'.Seq.drop_terminates_pub hT j
      have hsplit : e.trans = (Seq.ofList (Seq.take j e.trans)).append (e.trans.drop j) :=
        Stream'.Seq.take_append_drop_pub e.trans hT j
      have htr_suffix : sys.trace
          (⟨(e.stateAt j).getD e.init, e.trans.drop j⟩ : AlterSeq State Label) ≠ Seq.nil := by
        intro hsuf_nil
        apply htr
        have hsplit_trace : sys.trace e
            = (sys.trace (⟨e.init, Seq.ofList (Seq.take j e.trans)⟩
                  : AlterSeq State Label)).append
                (sys.trace (⟨(e.stateAt j).getD e.init, e.trans.drop j⟩
                  : AlterSeq State Label)) := by
          conv_lhs => rw [show e = ⟨e.init, e.trans⟩ from rfl, hsplit]
          exact sys.trace_append e.init ((e.stateAt j).getD e.init) _ _
            (Stream'.Seq.terminates_ofList _)
        rw [hsplit_trace, hpre_nil, hsuf_nil, Stream'.Seq.nil_append]
      exact Scheduler.drawAndRun_next_some_eq_zero pe' hExt
        ⟨E'.init, E'.trans.append (Seq.cons (l, (e.stateAt j).getD e.init) Seq.nil)⟩
        ⟨Nat.find hTE + 1, Stream'.Seq.terminatedAt_append_find hTE
          (show (Seq.cons (l, (e.stateAt j).getD e.init) Seq.nil).TerminatedAt 1 from rfl)⟩
        ⟨(e.stateAt j).getD e.init, e.trans.drop j⟩ hdropT htr_suffix a
  · -- `E'` does not terminate ⟹ `segmentScheduler = haltNow`.
    have hsched : Scheduler.segmentScheduler pe' ν' l E' μ = Scheduler.haltNow sys := by
      unfold Scheduler.segmentScheduler; rw [dif_neg hTE]
    rw [hsched]
    change (Scheduler.haltNow sys).next e (some a) = 0
    simp [Scheduler.haltNow, PMF.pure_apply]

open Classical in
/-- **L5 = H2: `expandCont` emits nothing once past the external label.** `expandCont.next` is the
posterior average of the per-`p` segment schedulers' emissions; each segment scheduler is silent
on external-trace executions (L4). Hence at any terminating `e` whose external trace is already
nonempty, `expandCont.next e (some a) = 0`. This is the structural core of H2: such an `e` halts
terminally. -/
theorem Scheduler.expandCont_next_some_eq_zero (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (L' : List Label) (ν' : State) (l' : Label) (e' : AlterSeq State Label)
    (he' : e'.trans.Terminates) (htr : sys.trace e' ≠ Seq.nil) (a : Label × PMF State) :
    (Scheduler.expandCont sys pe' L' ν' l').next e' (some a) = 0 := by
  classical
  by_cases h0 : (∑' p, Scheduler.expandContW sys pe' L' ν' l' e' p) ≠ 0
  · rw [Scheduler.expandCont_next_some sys pe' L' ν' l' e' h0 a.1 a.2]
    refine ENNReal.tsum_eq_zero.mpr (fun p => ?_)
    have hseg : (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).next e' (some (a.1, a.2)) = 0 :=
      Scheduler.segmentScheduler_next_some_eq_zero pe' hExt ν' l' p.1 p.2 e' he' htr (a.1, a.2)
    rw [hseg, mul_zero]
  · -- zero posterior normaliser ⟹ `expandCont.next e' = pure none`.
    push Not at h0
    have hpure : (Scheduler.expandCont sys pe' L' ν' l').next e' = PMF.pure none := by
      change (if h0' : (∑' p, Scheduler.expandContW sys pe' L' ν' l' e' p) ≠ 0 then
          (PMF.normalize (Scheduler.expandContW sys pe' L' ν' l' e') h0'
              (Scheduler.expandContW_tsum_ne_top sys pe' L' ν' l' e')).bind (fun p =>
            (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).next e')
        else PMF.pure none) = PMF.pure none
      rw [dif_neg (by rw [h0]; exact fun h => h rfl)]
    rw [hpure, PMF.pure_apply, if_neg (by simp)]

open Classical in
/-- **Trace-restricted bind/compose integration.** When every `σ`-halting execution (from
`μ_init`) has empty external trace, the trace-`[l]`-restricted `g`-mass of `bind σ k` factors
through the split point exactly as in `bind_compose_integrate`, but with the trace indicator now
restricting the *continuation* execution `f₂`: since the prefix contributes the empty trace,
`trace (concat f₁ f₂) = trace f₂`, so the restriction `[trace e = [l]]` commutes with the
peel. Built from the generalized bijection `bind_compose_integrate_gen` (in `WeakStep`). -/
theorem Scheduler.bind_compose_integrate_traceL {State Label : Type}
    {sys : LabelledSystem State Label} (σ : Scheduler sys.toSystem)
    (k : State → Scheduler sys.toSystem) (μ_init : PMF State) (l : Label) (g : State → ENNReal)
    (hσnil : ∀ f₁ : {e : AlterSeq State Label // e.trans.Terminates},
        σ.haltMass μ_init f₁ ≠ 0 → sys.trace f₁.1 = Seq.nil) :
    (∑' e, (Scheduler.bind σ k).haltMass μ_init e
        * (if sys.trace e.1 = Seq.ofList [l] then g (e.1.endState e.2) else 0))
      = ∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
          σ.haltMass μ_init f₁ *
            ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
              (k (f₁.1.endState f₁.2)).haltMass (PMF.pure (f₁.1.endState f₁.2)) f₂
                * (if sys.trace f₂.1 = Seq.ofList [l] then g (f₂.1.endState f₂.2) else 0) := by
  classical
  rw [Scheduler.bind_compose_integrate_gen σ k μ_init
    (fun e => if sys.trace e.1 = Seq.ofList [l] then g (e.1.endState e.2) else 0)]
  -- Per `f₁`, per `f₂`: rewrite the `concat`-test to the suffix-test (using `trace f₁ = nil`).
  refine tsum_congr (fun f₁ => ?_)
  by_cases hf₁ : σ.haltMass μ_init f₁ = 0
  · rw [hf₁, zero_mul, zero_mul]
  · have htr_pre : sys.trace f₁.1 = Seq.nil := hσnil f₁ hf₁
    congr 1
    refine tsum_congr (fun f₂ => ?_)
    -- `trace (concat f₁ f₂) = trace f₂` and `end (concat f₁ f₂) = end f₂`.
    have hconcat_trans : (WeakScheduler.concat f₁ f₂).trans
        = (Seq.ofList (f₁.1.trans.toList f₁.2)).append (Seq.ofList (f₂.1.trans.toList f₂.2)) := by
      unfold WeakScheduler.concat
      rw [Stream'.Seq.ofList_append]
    have htr_concat : sys.trace (⟨WeakScheduler.concat f₁ f₂,
          WeakScheduler.concat_terminates f₁ f₂⟩ :
          {e : AlterSeq State Label // e.trans.Terminates}).1 = sys.trace f₂.1 := by
      change sys.trace (WeakScheduler.concat f₁ f₂) = sys.trace f₂.1
      have hpre_eq : sys.trace (⟨(WeakScheduler.concat f₁ f₂).init,
            Seq.ofList (f₁.1.trans.toList f₁.2)⟩ : AlterSeq State Label) = Seq.nil := by
        rw [show (⟨(WeakScheduler.concat f₁ f₂).init, Seq.ofList (f₁.1.trans.toList f₁.2)⟩
              : AlterSeq State Label) = f₁.1 from by
          obtain ⟨⟨fi, ft⟩, fh⟩ := f₁
          simp only [WeakScheduler.concat]
          rw [Stream'.Seq.ofList_toList]]
        exact htr_pre
      have hsuf_eq : sys.trace (⟨f₁.1.init, Seq.ofList (f₂.1.trans.toList f₂.2)⟩
            : AlterSeq State Label) = sys.trace f₂.1 := by
        unfold LabelledSystem.trace
        rw [Stream'.Seq.ofList_toList]
      rw [show (WeakScheduler.concat f₁ f₂)
          = ⟨(WeakScheduler.concat f₁ f₂).init,
              (Seq.ofList (f₁.1.trans.toList f₁.2)).append
                (Seq.ofList (f₂.1.trans.toList f₂.2))⟩ from by
        rw [← hconcat_trans]]
      rw [sys.trace_append (WeakScheduler.concat f₁ f₂).init f₁.1.init _ _
        (Stream'.Seq.terminates_ofList _)]
      rw [show (WeakScheduler.concat f₁ f₂).init = f₁.1.init from rfl] at hpre_eq ⊢
      rw [hpre_eq, Stream'.Seq.nil_append, hsuf_eq]
    rw [htr_concat]
    by_cases htr : sys.trace f₂.1 = Seq.ofList [l]
    · rw [if_pos htr, if_pos htr]
      -- end-states agree (f₂ nonempty since its trace is `[l] ≠ nil`).
      have hf₂_ne : f₂.1.trans.toList f₂.2 ≠ [] := by
        intro hnil
        have : sys.trace f₂.1 = Seq.nil := by
          unfold LabelledSystem.trace
          rw [show f₂.1.trans = Seq.ofList (f₂.1.trans.toList f₂.2) from
            (Stream'.Seq.ofList_toList _ _).symm, hnil, Stream'.Seq.ofList_nil,
            Stream'.Seq.filter_nil, Stream'.Seq.map_nil]
        rw [this] at htr
        exact absurd htr.symm (by simp [Stream'.Seq.ofList_cons])
      -- `concat f₁ f₂` in append form, with end-state `= f₂.end`.
      have hconcat_eq : WeakScheduler.concat f₁ f₂ = ⟨f₁.1.init,
          (Seq.ofList (f₁.1.trans.toList f₁.2)).append (Seq.ofList (f₂.1.trans.toList f₂.2))⟩ := by
        have hi : (WeakScheduler.concat f₁ f₂).init = f₁.1.init := rfl
        cases hc : WeakScheduler.concat f₁ f₂ with
        | mk ci ct =>
          have ht : ct = (Seq.ofList (f₁.1.trans.toList f₁.2)).append
              (Seq.ofList (f₂.1.trans.toList f₂.2)) := by
            rw [← hconcat_trans, hc]
          rw [ht]
          congr 1
          rw [← hi, hc]
      have hend : (⟨WeakScheduler.concat f₁ f₂, WeakScheduler.concat_terminates f₁ f₂⟩ :
            {e : AlterSeq State Label // e.trans.Terminates}).1.endState
            (WeakScheduler.concat_terminates f₁ f₂) = f₂.1.endState f₂.2 := by
        rw [AlterSeq.endState_congr_pub hconcat_eq (WeakScheduler.concat_terminates f₁ f₂)
          ⟨_, Stream'.Seq.terminatedAt_append_find (Stream'.Seq.terminates_ofList _)
            (Nat.find_spec (Stream'.Seq.terminates_ofList _))⟩]
        rw [AlterSeq.endState_append f₁.1.init f₂.1.init _ _
          (Stream'.Seq.terminates_ofList _) (Stream'.Seq.terminates_ofList _)
          (by rw [Stream'.Seq.toList_ofList]; exact hf₂_ne)]
        apply AlterSeq.endState_congr_pub
        have : (⟨f₂.1.init, Seq.ofList (f₂.1.trans.toList f₂.2)⟩ : AlterSeq State Label)
            = ⟨f₂.1.init, f₂.1.trans⟩ := by rw [Stream'.Seq.ofList_toList]
        rw [this]
      rw [hend]
    · rw [if_neg htr, if_neg htr]

open Classical in
/-- **Segment trace-`[l]` `g`-mass as a one-external-step expectation.** The trace-`[l]`
`g`-mass of `segmentScheduler pe' ν' l' E' μ_ig` (run from `pure ν'`), scaled by the
`(l',·)`-fiber `Z₀ = ∑' μ, pe'.next E' (some (l', μ))`, equals the prior-weighted post-τ
collapse: integrate the post-τ-witness pushforward of the per-`σ` `drawAndRun` trace-`[l]`
slice. Combines `bind_compose_integrate` (peeling the post-τ draw — legitimate here because the
post-τ witness emits internal-only labels, so the segment's external trace equals the
`drawAndRun` part's trace) with `drawAndRun_pushforward` (the trace-`[l]` new-label slice) and
`postTauDraw_pushforward`.

REMAINING BLOCKER: the trace restriction `[trace e = [l]]` cannot be threaded through
`bind_compose_integrate` directly (that lemma integrates only *end-state* tests `h(e.end)`, not
trace-restricted ones). One needs a trace-restricted `bind_compose` step: since the post-τ part
emits internal-only labels (`postTauWitness = weakTau_post.witnessScheduler`, so
`haltMass_trace_nil`), the composed segment's external trace equals the `drawAndRun` part's
trace, so `[trace(f₁∘f₂) = [l]] = [trace f₂ = [l]]` and the restriction commutes with the post-τ
peel. That trace-restricted `bind_compose_integrate` (built from `bind_haltMass_trace` +
`haltMass_trace_nil`) is the missing intermediate; once available, `drawAndRun_pushforward`
supplies the inner trace-[l] slice. -/
theorem segmentScheduler_traceL_pushforward {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (ν' : State) (l' l : Label) (E' : AlterSeq State Label) (μ_ig : PMF State)
    (hT : E'.trans.Terminates) (g : State → ENNReal) :
    (∑' μ, pe'.scheduler.next E' (some (l', μ)) *
        (if hstep : (¬ sys.internal l') ∧ sys^w.step (E'.endState hT) l' μ then
          (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)) *
        (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          (Scheduler.segmentScheduler pe' ν' l' E' μ_ig).haltMass (PMF.pure ν') e
            * (if sys.trace e.1 = Seq.ofList [l] then g (e.1.endState e.2) else 0))
      = ∑' μ : PMF State, pe'.scheduler.next E' (some (l', μ))
          * (if hstep : (¬ sys.internal l') ∧ sys^w.step (E'.endState hT) l' μ then
              (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0)
          * (∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
              (Scheduler.postTauWitness sys (E'.endState hT) l' μ).haltMass (PMF.pure ν') f₁
                * (∑' μ_n : PMF State,
                    pe'.scheduler.next ⟨E'.init, E'.trans.append
                        (Seq.cons (l', f₁.1.endState f₁.2) Seq.nil)⟩ (some (l, μ_n))
                      * pe'.hsExpect (f₁.1.endState f₁.2) l μ_n g)) := by
  classical
  -- The end-state test for the post-τ collapse.
  set g' : State → ENNReal := fun σ =>
    ∑' μ_n : PMF State,
      pe'.scheduler.next ⟨E'.init, E'.trans.append (Seq.cons (l', σ) Seq.nil)⟩ (some (l, μ_n))
        * pe'.hsExpect σ l μ_n g with hg'
  -- Step 1: unfold the segment scheduler to its `bind`.
  rw [show Scheduler.segmentScheduler pe' ν' l' E' μ_ig
        = Scheduler.bind (Scheduler.postTauDraw pe' E' l')
            (fun σ_k => Scheduler.drawAndRun pe'
              ⟨E'.init, E'.trans.append (Seq.cons (l', σ_k) Seq.nil)⟩) by
      unfold Scheduler.segmentScheduler; rw [dif_pos hT]]
  -- Step 2: trace-restricted bind-compose peels the (trace-nil) post-τ draw.
  rw [Scheduler.bind_compose_integrate_traceL (Scheduler.postTauDraw pe' E' l')
      (fun σ_k => Scheduler.drawAndRun pe'
        ⟨E'.init, E'.trans.append (Seq.cons (l', σ_k) Seq.nil)⟩) (PMF.pure ν') l g
      (fun f₁ hf₁ => Scheduler.haltMass_trace_nil_of_internal _ (PMF.pure ν')
        (fun e' l₁ μ₁ hne => Scheduler.postTauDraw_internal_only pe' E' l' e' l₁ μ₁ hne) f₁ hf₁)]
  -- Step 3: the inner `drawAndRun` trace-[l] slice (`drawAndRun_pushforward`) at each `f₁.end`.
  rw [show (∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
          (Scheduler.postTauDraw pe' E' l').haltMass (PMF.pure ν') f₁ *
            ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
              (Scheduler.drawAndRun pe'
                  ⟨E'.init, E'.trans.append
                    (Seq.cons (l', f₁.1.endState f₁.2) Seq.nil)⟩).haltMass
                (PMF.pure (f₁.1.endState f₁.2)) f₂ *
                (if sys.trace f₂.1 = Seq.ofList [l] then g (f₂.1.endState f₂.2) else 0))
        = ∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
            (Scheduler.postTauDraw pe' E' l').haltMass (PMF.pure ν') f₁ * g' (f₁.1.endState f₁.2)
      from by
    refine tsum_congr (fun f₁ => ?_)
    congr 1
    set E'' : AlterSeq State Label :=
      ⟨E'.init, E'.trans.append (Seq.cons (l', f₁.1.endState f₁.2) Seq.nil)⟩ with hE''
    have hT'' : E''.trans.Terminates :=
      ⟨Nat.find hT + 1, Stream'.Seq.terminatedAt_append_find hT
        (show (Seq.cons (l', f₁.1.endState f₁.2) Seq.nil).TerminatedAt 1 from rfl)⟩
    have hend'' : E''.endState hT'' = f₁.1.endState f₁.2 :=
      AlterSeq.endState_append_singleton E' hT l' (f₁.1.endState f₁.2)
    rw [show (PMF.pure (f₁.1.endState f₁.2) : PMF State) = PMF.pure (E''.endState hT'') by
      rw [hend'']]
    rw [Scheduler.drawAndRun_pushforward pe' hExt E'' hT'' l g]
    rw [hg', hend'']]
  -- Step 4: rewrite the RHS inner expectation as `g'`, then apply the post-τ marginal pushforward.
  rw [show (∑' (μ : PMF State), pe'.scheduler.next E' (some (l', μ)) *
        (if hstep : (¬ sys.internal l') ∧ sys^w.step (E'.endState hT) l' μ then
          (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0) *
        ∑' (f₁ : {e : AlterSeq State Label // e.trans.Terminates}),
          (Scheduler.postTauWitness sys (E'.endState hT) l' μ).haltMass (PMF.pure ν') f₁ *
            ∑' μ_n : PMF State,
              pe'.scheduler.next ⟨E'.init, E'.trans.append
                  (Seq.cons (l', f₁.1.endState f₁.2) Seq.nil)⟩ (some (l, μ_n))
                * pe'.hsExpect (f₁.1.endState f₁.2) l μ_n g)
      = ∑' (μ : PMF State), pe'.scheduler.next E' (some (l', μ)) *
          (if hstep : (¬ sys.internal l') ∧ sys^w.step (E'.endState hT) l' μ then
            (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0) *
          ∑' (f₁ : {e : AlterSeq State Label // e.trans.Terminates}),
            (Scheduler.postTauWitness sys (E'.endState hT) l' μ).haltMass (PMF.pure ν') f₁ *
              g' (f₁.1.endState f₁.2) from
    tsum_congr (fun μ => by rw [hg'])]
  exact Scheduler.postTauDraw_pushforward pe' E' hT l' ν' g'

open Classical in
/-- **Append-singleton reindex (with a test) for `hsLabMass`-style sums.** Summing the
prefix-`probOf` times the one-step kernel `kernel E' (l', σ)` times a test `F` evaluated at the
extended history `⟨E'.init, E'.trans ++ [(l', σ)]⟩`, over `(E', σ)` with `E'` of label list
`labs`, equals summing `probOf E · F E` over `E` of label list `labs ++ [l']`. The
`(E', σ) ↔ ⟨E'.init, E'.trans ++ [(l', σ)]⟩` bijection + `probOf_append_singleton`. Mirrors
`tsum_probOf_labels_append`. -/
theorem tsum_probOf_kernel_test_append {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (labs : List Label) (l' : Label) (F : AlterSeq State Label → ENNReal) :
    (∑' E : AlterSeq State Label,
        dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList (labs ++ [l']))
          (fun h => pe'.probOf E h.1 * F E) (fun _ => 0))
      = ∑' (E' : AlterSeq State Label) (σ : State),
          dite (E'.trans.Terminates ∧ E'.trans.map Prod.fst = Seq.ofList labs)
            (fun h => pe'.probOf E' h.1 * pe'.kernel E' (l', σ)
              * F ⟨E'.init, E'.trans.append (Seq.cons (l', σ) Seq.nil)⟩) (fun _ => 0) := by
  classical
  rw [← ENNReal.tsum_prod' (f := fun p : AlterSeq State Label × State =>
      dite (p.1.trans.Terminates ∧ Seq.map Prod.fst p.1.trans = (↑labs : Seq Label))
        (fun h => pe'.probOf p.1 h.1 * pe'.kernel p.1 (l', p.2)
          * F ⟨p.1.init, p.1.trans.append (Seq.cons (l', p.2) Seq.nil)⟩) (fun _ => 0))]
  set f : AlterSeq State Label → ENNReal := fun E =>
      dite (E.trans.Terminates ∧ Seq.map Prod.fst E.trans = (↑(labs ++ [l']) : Seq Label))
        (fun h => pe'.probOf E h.1 * F E) (fun _ => 0) with hf_def
  set g : AlterSeq State Label × State → ENNReal := fun p =>
      dite (p.1.trans.Terminates ∧ Seq.map Prod.fst p.1.trans = (↑labs : Seq Label))
        (fun h => pe'.probOf p.1 h.1 * pe'.kernel p.1 (l', p.2)
          * F ⟨p.1.init, p.1.trans.append (Seq.cons (l', p.2) Seq.nil)⟩) (fun _ => 0) with hg_def
  have g_supp_cond : ∀ p : AlterSeq State Label × State, g p ≠ 0 →
      p.1.trans.Terminates ∧ Seq.map Prod.fst p.1.trans = (↑labs : Seq Label) := by
    intro p hp
    by_contra hcond
    rw [hg_def] at hp; simp only at hp; rw [dif_neg hcond] at hp; exact hp rfl
  have f_supp_cond : ∀ E : AlterSeq State Label, f E ≠ 0 →
      E.trans.Terminates ∧ Seq.map Prod.fst E.trans = (↑(labs ++ [l']) : Seq Label) := by
    intro E hE
    by_contra hcond
    rw [hf_def] at hE; simp only at hE; rw [dif_neg hcond] at hE; exact hE rfl
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun x => (⟨(x.1).1.init,
        (x.1).1.trans.append (Seq.cons (l', (x.1).2) Seq.nil)⟩ : AlterSeq State Label))
    ?hinj ?hf ?hfg
  case hinj =>
    rintro x y hxy
    have hx := g_supp_cond x.1 x.2
    have hy := g_supp_cond y.1 y.2
    have h_trans := congrArg AlterSeq.trans hxy
    have h_init := congrArg AlterSeq.init hxy
    simp only at h_trans h_init
    have h_last := Stream'.Seq.append_singleton_inj_right
      (x.1).1.trans (y.1).1.trans hx.1 hy.1 _ _ h_trans
    have hσ : (x.1).2 = (y.1).2 := (Prod.mk.inj h_last).2
    have h_prev := Stream'.Seq.append_singleton_inj_left
      (x.1).1.trans (y.1).1.trans hx.1 hy.1 _ _ h_trans
    refine Subtype.ext (Prod.ext ?_ hσ)
    exact congrArg₂ AlterSeq.mk h_init h_prev
  case hf =>
    intro E hE_mem
    have hE := f_supp_cond E hE_mem
    have h_ne : E.trans.toList hE.1 ≠ [] := by
      intro hnil
      have h_map_nil : E.trans.map Prod.fst = Stream'.Seq.nil := by
        have : E.trans = Stream'.Seq.nil := by
          rw [← Stream'.Seq.ofList_toList E.trans hE.1, hnil, Stream'.Seq.ofList_nil]
        rw [this, Stream'.Seq.map_nil]
      rw [hE.2] at h_map_nil
      have h_len := congrArg Stream'.Seq.length' h_map_nil
      rw [Stream'.Seq.length'_nil,
        Stream'.Seq.length'_of_terminates (Stream'.Seq.terminates_ofList _),
        ← Stream'.Seq.length_toList _ (Stream'.Seq.terminates_ofList _),
        Stream'.Seq.toList_ofList] at h_len
      simp only [List.length_append, List.length_singleton, Nat.cast_eq_zero] at h_len
      omega
    obtain ⟨prev, last, h_prev_term, h_split, _, _⟩ :=
      Stream'.Seq.exists_split_last E.trans hE.1 h_ne
    have h_trans_map := hE.2
    rw [h_split, Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil] at h_trans_map
    rw [show (↑(labs ++ [l']) : Seq Label)
        = (↑labs : Seq Label).append (Seq.cons l' Seq.nil) by
        rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]]
      at h_trans_map
    have h_prev_map_term : (prev.map Prod.fst).Terminates :=
      Stream'.Seq.terminates_map_iff.mpr h_prev_term
    have h_prev_map : prev.map Prod.fst = (↑labs : Seq Label) :=
      Stream'.Seq.append_singleton_inj_left _ _ h_prev_map_term
        (Stream'.Seq.terminates_ofList _) _ _ h_trans_map
    have h_last : last.1 = l' :=
      Stream'.Seq.append_singleton_inj_right _ _ h_prev_map_term
        (Stream'.Seq.terminates_ofList _) _ _ h_trans_map
    have h_app_term : (prev.append (Seq.cons (l', last.2) Seq.nil)).Terminates := by
      rw [show (Seq.cons (l', last.2) Seq.nil) = Seq.cons last Seq.nil by rw [← h_last]]
      exact h_split ▸ hE.1
    have h_factor := ProbabilisticExecution.probOf_append_singleton pe'
      E.init prev h_prev_term (l', last.2) h_app_term
    have h_reassemble : (⟨E.init, prev.append (Seq.cons (l', last.2) Seq.nil)⟩
        : AlterSeq State Label) = E := by
      refine congrArg₂ AlterSeq.mk rfl ?_
      rw [show (Seq.cons (l', last.2) Seq.nil) = Seq.cons last Seq.nil by rw [← h_last]]
      exact h_split.symm
    -- `g (preimage) = probOf E · F E = f E ≠ 0`.
    have h_probOf_kernel : pe'.probOf ⟨E.init, prev⟩ h_prev_term
        * pe'.kernel ⟨E.init, prev⟩ (l', last.2) = pe'.probOf E hE.1 := by
      rw [← h_factor,
        ProbabilisticExecution.probOf_congr pe'
          ⟨E.init, prev.append (Seq.cons (l', last.2) Seq.nil)⟩ E h_reassemble h_app_term hE.1]
    have hg_eq : g (⟨E.init, prev⟩, last.2) = pe'.probOf E hE.1 * F E := by
      rw [hg_def]; simp only
      rw [dif_pos ⟨h_prev_term, h_prev_map⟩]
      refine congrArg₂ (· * ·) ?_ (congrArg F h_reassemble)
      exact h_probOf_kernel
    have hf_eq : f E = pe'.probOf E hE.1 * F E := by
      rw [hf_def]; simp only; rw [dif_pos hE]
    have hg_pos : g (⟨E.init, prev⟩, last.2) ≠ 0 := by
      rw [hg_eq, ← hf_eq]; exact Function.mem_support.mp hE_mem
    refine ⟨⟨(⟨E.init, prev⟩, last.2), hg_pos⟩, ?_⟩
    simp only
    refine congrArg₂ AlterSeq.mk rfl ?_
    rw [show (Seq.cons (l', last.2) Seq.nil) = Seq.cons last Seq.nil by rw [← h_last]]
    exact h_split.symm
  case hfg =>
    rintro x
    set E' := (x.1).1 with hE'_def
    set σ := (x.1).2 with hσ_def
    have hx := g_supp_cond x.1 x.2
    have h_g : g x.1 = pe'.probOf E' hx.1 * pe'.kernel E' (l', σ)
        * F ⟨E'.init, E'.trans.append (Seq.cons (l', σ) Seq.nil)⟩ := by
      rw [hg_def]; simp only; rw [dif_pos hx]
    have h_app_term : (E'.trans.append (Seq.cons (l', σ) Seq.nil)).Terminates :=
      ⟨_, Stream'.Seq.terminatedAt_append_find hx.1
        (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil).choose_spec⟩
    have h_map : Seq.map Prod.fst (E'.trans.append (Seq.cons (l', σ) Seq.nil))
        = (↑(labs ++ [l']) : Seq Label) := by
      rw [Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil, hx.2,
        Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have h_f : f (⟨E'.init, E'.trans.append (Seq.cons (l', σ) Seq.nil)⟩
        : AlterSeq State Label)
        = pe'.probOf ⟨E'.init, E'.trans.append (Seq.cons (l', σ) Seq.nil)⟩ h_app_term
          * F ⟨E'.init, E'.trans.append (Seq.cons (l', σ) Seq.nil)⟩ := by
      rw [hf_def]; simp only; rw [dif_pos ⟨h_app_term, h_map⟩]
    change f (⟨E'.init, E'.trans.append (Seq.cons (l', σ) Seq.nil)⟩
        : AlterSeq State Label) = g x.1
    rw [h_f, h_g]
    rw [ProbabilisticExecution.probOf_append_singleton pe' E'.init E'.trans hx.1 (l', σ)
      h_app_term]

open Classical in
/-- **ASSEMBLE half** (nonempty `L'`): collapsing the trace-`L'` continuation kernel `expandK`
back to the trace-`(L' ++ [l])` hyper-step-boundary mass. Mirrors `lower_labProb_eq_aux`'s
stepA/stepB/decomp_g, now telescoping the `expandK`-`Z₀` factor through the proven GAP-2
collapse `expandK_Z_mul`, the segment trace-`[l]` pushforward, and `postTau_marginal_collapse`. -/
theorem hsLabMass_expandK_step {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (L' : List Label) (l' l : Label) (hL' : L'.getLast? = some l') (g : State → ENNReal) :
    pe'.hsLabMass L' (fun ν' => pe'.expandK L' l' l g ν') = pe'.hsLabMass (L' ++ [l]) g := by
  classical
  -- LHS via `hsLabMass_eq_Z_sum` then the GAP-2 collapse `expandK_Z_mul`.
  rw [pe'.hsLabMass_eq_Z_sum L' l' hL' (fun ν' => pe'.expandK L' l' l g ν')]
  rw [show (∑' ν' : State, (∑' p, pe'.beliefExpandW L' ν' p) * pe'.expandK L' l' l g ν')
        = ∑' ν' : State, ∑' p : AlterSeq State Label × PMF State, pe'.beliefExpandW L' ν' p
            * ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
                (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).haltMass (PMF.pure ν') e
                  * (if sys.trace e.1 = Seq.ofList [l] then g (e.1.endState e.2) else 0) from
      tsum_congr (fun ν' => expandK_Z_mul pe' L' l' l g ν')]
  -- RHS unfolded.
  have hRHS : pe'.hsLabMass (L' ++ [l]) g
      = ∑' E' : AlterSeq State Label,
          dite (E'.trans.Terminates ∧ E'.trans.map Prod.fst = Seq.ofList L')
            (fun h => pe'.probOf E' h.1 *
              ∑' μ_n : PMF State, pe'.scheduler.next E' (some (l, μ_n)) *
                pe'.hsExpect (E'.endState h.1) l μ_n g)
            (fun _ => 0) := by
    unfold ProbabilisticExecution.hsLabMass
    rw [show (L' ++ [l]).getLast? = some l from by simp]
    simp only [List.dropLast_concat]
  rw [hRHS]
  -- Abbreviate the (μ-independent) segment trace-[l] g-mass `SegMass ν' E'`.
  set SegMass : State → AlterSeq State Label → ENNReal := fun ν' E' =>
    ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
      (Scheduler.segmentScheduler pe' ν' l' E' (PMF.pure ν')).haltMass (PMF.pure ν') e
        * (if sys.trace e.1 = Seq.ofList [l] then g (e.1.endState e.2) else 0) with hSegMass
  -- The segment scheduler ignores its `μ` argument, so `SegMass` captures every pair `(E', μ)`.
  have hseg_indep : ∀ (ν' : State) (p : AlterSeq State Label × PMF State),
      (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).haltMass (PMF.pure ν') e
          * (if sys.trace e.1 = Seq.ofList [l] then g (e.1.endState e.2) else 0))
        = SegMass ν' p.1 := by
    intro ν' p
    rw [hSegMass]
    simp only []
    refine tsum_congr (fun e => ?_)
    have hsegeq : Scheduler.segmentScheduler pe' ν' l' p.1 p.2
        = Scheduler.segmentScheduler pe' ν' l' p.1 (PMF.pure ν') := rfl
    rw [hsegeq]
  -- Reindex `p = (E', μ)`, swap to `E'`-outer, apply `beliefExpandW_eq`.
  rw [show (∑' (ν' : State) (p : AlterSeq State Label × PMF State),
        pe'.beliefExpandW L' ν' p *
          ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
            (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).haltMass (PMF.pure ν') e *
              (if sys.trace e.1 = Seq.ofList [l] then g (e.1.endState e.2) else 0))
      = ∑' (E' : AlterSeq State Label) (ν' : State) (μ : PMF State),
          pe'.beliefExpandW L' ν' (E', μ) * SegMass ν' E' from by
    rw [show (∑' (ν' : State) (p : AlterSeq State Label × PMF State),
          pe'.beliefExpandW L' ν' p *
            ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
              (Scheduler.segmentScheduler pe' ν' l' p.1 p.2).haltMass (PMF.pure ν') e *
                (if sys.trace e.1 = Seq.ofList [l] then g (e.1.endState e.2) else 0))
        = ∑' (ν' : State) (E' : AlterSeq State Label) (μ : PMF State),
            pe'.beliefExpandW L' ν' (E', μ) * SegMass ν' E' from
      tsum_congr (fun ν' => by
        rw [ENNReal.tsum_prod']
        refine tsum_congr (fun E' => ?_)
        refine tsum_congr (fun μ => ?_)
        rw [hseg_indep ν' (E', μ)])]
    rw [ENNReal.tsum_comm]]
  -- The post-fix ASSEMBLE: `postDist` now travels with `μ̃`, so the per-`E'` core collapses via
  -- `segmentScheduler_traceL_pushforward` + `postTau_marginal_collapse` (PER `μ`, no cross-term),
  -- then the `(E', σ) ↔ E'++[(l',σ)]` reindex (`tsum_probOf_kernel_test_append`) hits the RHS.
  -- The RHS test `F` (per full history `E_full`), via `dite` on termination.
  set F : AlterSeq State Label → ENNReal := fun E =>
    if hE : E.trans.Terminates then
      ∑' μ_n : PMF State, pe'.scheduler.next E (some (l, μ_n))
        * pe'.hsExpect (E.endState hE) l μ_n g
    else 0 with hF
  -- Reindex the RHS: `∑' E_full [tight L'] probOf · F =
  --   ∑' E' σ [tight L'.dropLast] probOf · kernel · F`.
  have hL'_eq : L'.dropLast ++ [l'] = L' :=
    List.dropLast_append_getLast? l' (by rw [hL']; rfl)
  rw [show (∑' (E' : AlterSeq State Label),
        if h : E'.trans.Terminates ∧ Seq.map Prod.fst E'.trans = ↑L' then
          pe'.probOf E' h.1 *
            ∑' (μ_n : PMF State), (pe'.scheduler.next E') (some (l, μ_n))
              * pe'.hsExpect (E'.endState h.1) l μ_n g
        else 0)
      = ∑' (E : AlterSeq State Label),
          dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList (L'.dropLast ++ [l']))
            (fun h => pe'.probOf E h.1 * F E) (fun _ => 0) from by
    rw [hL'_eq]
    refine tsum_congr (fun E => ?_)
    by_cases hc : E.trans.Terminates ∧ Seq.map Prod.fst E.trans = (↑L' : Seq Label)
    · rw [dif_pos hc, dif_pos hc, hF]; simp only [dif_pos hc.1]
    · rw [dif_neg hc, dif_neg hc]]
  rw [tsum_probOf_kernel_test_append pe' L'.dropLast l' F]
  -- Now match the LHS `∑' E' ν' μ` to `∑' E' σ [tight L'.dropLast] probOf · kernel · F⟨…⟩`.
  refine tsum_congr (fun E' => ?_)
  by_cases hT : E'.trans.Terminates ∧ E'.trans.map Prod.fst = Seq.ofList L'.dropLast
  · -- Tight `E'`: collapse the segment via `segmentScheduler_traceL_pushforward` + `postTau`.
    -- `g'(σ) = F ⟨E'.init, E'.trans++[(l',σ)]⟩` (the segment-collapse test).
    set g' : State → ENNReal := fun σ =>
      ∑' μ_n : PMF State,
        pe'.scheduler.next ⟨E'.init, E'.trans.append (Seq.cons (l', σ) Seq.nil)⟩ (some (l, μ_n))
          * pe'.hsExpect σ l μ_n g with hg'
    have hFeq : ∀ σ : State,
        F ⟨E'.init, E'.trans.append (Seq.cons (l', σ) Seq.nil)⟩ = g' σ := by
      intro σ
      have happT : (E'.trans.append (Seq.cons (l', σ) Seq.nil)).Terminates :=
        ⟨_, Stream'.Seq.terminatedAt_append_find hT.1
          (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil).choose_spec⟩
      rw [hF]; simp only [dif_pos happT]
      rw [hg']
      refine tsum_congr (fun μ_n => ?_)
      rw [show (⟨E'.init, E'.trans.append (Seq.cons (l', σ) Seq.nil)⟩
            : AlterSeq State Label).endState happT = σ from
        AlterSeq.endState_append_singleton E' hT.1 l' σ]
    -- RHS for this `E'`: `∑' σ, [tight] probOf E' · kernel E'(l',σ) · F⟨…⟩`. Pull out `probOf E'`.
    rw [show (∑' σ : State,
            dite (E'.trans.Terminates ∧ Seq.map Prod.fst E'.trans = (↑L'.dropLast : Seq Label))
              (fun h => pe'.probOf E' h.1 * pe'.kernel E' (l', σ)
                * F ⟨E'.init, E'.trans.append (Seq.cons (l', σ) Seq.nil)⟩) (fun _ => 0))
          = pe'.probOf E' hT.1 * ∑' σ : State, pe'.kernel E' (l', σ) * g' σ from by
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr (fun σ => ?_)
      rw [dif_pos hT, hFeq σ]; ring]
    -- LHS for this `E'`: collapse `∑' ν' μ` to `probOf E' · ∑' σ, kernel E'(l',σ) · g' σ`.
    -- The (μ-dependent) reach-likelihood factor `postDist_μ(ν')`.
    set pd : PMF State → State → ENNReal := fun μ ν' =>
      if hstep : (¬ sys.internal l') ∧ sys^w.step (E'.endState hT.1) l' μ then
        (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0 with hpd
    -- The per-`μ` post-τ-witness pushforward of `g'` from boundary `ν'`.
    set W : PMF State → State → ENNReal := fun μ ν' =>
      ∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
        (Scheduler.postTauWitness sys (E'.endState hT.1) l' μ).haltMass (PMF.pure ν') f₁
          * g' (f₁.1.endState f₁.2) with hW
    -- Step 1: expand `beliefExpandW` (tight `E'`) as `probOf E' · next(some(l',μ)) · pd μ ν'`.
    have hbel : ∀ (ν' : State) (μ : PMF State),
        pe'.beliefExpandW L' ν' (E', μ) * SegMass ν' E'
          = pe'.probOf E' hT.1 *
              ((pe'.scheduler.next E' (some (l', μ)) * pd μ ν') * SegMass ν' E') := by
      intro ν' μ
      rw [pe'.beliefExpandW_eq L' ν' l' hL' (E', μ)]
      dsimp only
      rw [dif_pos hT]
      change _ = pe'.probOf E' hT.1 *
        ((pe'.scheduler.next E' (some (l', μ)) *
          (if hstep : (¬ sys.internal l') ∧ sys^w.step (E'.endState hT.1) l' μ then
            (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' else 0))
          * SegMass ν' E')
      by_cases hstep : (¬ sys.internal l') ∧ sys^w.step (E'.endState hT.1) l' μ
      · rw [dif_pos hstep, dif_pos hstep]; ring
      · rw [dif_neg hstep, dif_neg hstep]; ring
    -- Step 2: per `ν'` and `μ`, identify the segment pushforward (postDist bundled with `μ̃`).
    -- `segmentScheduler_traceL_pushforward`: `Z₀(ν') · SegMass = ∑' μ, next·pd·W`.
    have hpush : ∀ ν' : State,
        (∑' μ : PMF State, pe'.scheduler.next E' (some (l', μ)) * pd μ ν') * SegMass ν' E'
          = ∑' μ : PMF State, pe'.scheduler.next E' (some (l', μ)) * pd μ ν' * W μ ν' := by
      intro ν'
      have hps := segmentScheduler_traceL_pushforward pe' hExt ν' l' l E' (PMF.pure ν') hT.1 g
      rw [hpd, hSegMass, hW, hg']
      simp only []
      exact hps
    -- Step 3: assemble. Pull `probOf E'` out, swap `ν' ↔ μ`, collapse per `μ`.
    -- Per `ν'`: `∑' μ, beliefExpandW·SegMass = probOf · ∑' μ, next·pd·W`.
    have hperν' : ∀ ν' : State,
        (∑' μ : PMF State, pe'.beliefExpandW L' ν' (E', μ) * SegMass ν' E')
          = pe'.probOf E' hT.1 *
              ∑' μ : PMF State, pe'.scheduler.next E' (some (l', μ)) * pd μ ν' * W μ ν' := by
      intro ν'
      have step1 : (∑' μ : PMF State, pe'.beliefExpandW L' ν' (E', μ) * SegMass ν' E')
          = pe'.probOf E' hT.1 *
              ∑' μ : PMF State,
                pe'.scheduler.next E' (some (l', μ)) * pd μ ν' * SegMass ν' E' := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr (fun μ => ?_)
        rw [hbel ν' μ]
      rw [step1]
      refine congrArg _ ?_
      rw [← hpush ν', ENNReal.tsum_mul_right]
    calc (∑' (ν' : State) (μ : PMF State), pe'.beliefExpandW L' ν' (E', μ) * SegMass ν' E')
        = pe'.probOf E' hT.1 *
            ∑' ν' : State, ∑' μ : PMF State,
              pe'.scheduler.next E' (some (l', μ)) * pd μ ν' * W μ ν' := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr hperν'
      _ = pe'.probOf E' hT.1 *
            ∑' μ : PMF State, pe'.scheduler.next E' (some (l', μ)) * ∑' σ : State, μ σ * g' σ := by
          refine congrArg _ ?_
          rw [ENNReal.tsum_comm (f := fun ν' μ =>
            pe'.scheduler.next E' (some (l', μ)) * pd μ ν' * W μ ν')]
          refine tsum_congr (fun μ => ?_)
          by_cases hns : pe'.scheduler.next E' (some (l', μ)) = 0
          · rw [hns]
            simp only [zero_mul, tsum_zero]
          · have hstep : (¬ sys.internal l') ∧ sys^w.step (E'.endState hT.1) l' μ :=
              ⟨hExt E' l' μ ((PMF.mem_support_iff _ _).mpr hns),
                pe'.step_of_mem_support E' hT.1 l' μ ((PMF.mem_support_iff _ _).mpr hns)⟩
            rw [show (∑' ν' : State,
                    pe'.scheduler.next E' (some (l', μ)) * pd μ ν' * W μ ν')
                  = pe'.scheduler.next E' (some (l', μ)) *
                      ∑' ν' : State, pd μ ν' * W μ ν' from by
              rw [← ENNReal.tsum_mul_left]; exact tsum_congr (fun ν' => by ring)]
            refine congrArg _ ?_
            rw [hW]
            rw [show (∑' ν' : State, pd μ ν' *
                    ∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
                      (Scheduler.postTauWitness sys (E'.endState hT.1) l' μ).haltMass
                          (PMF.pure ν') f₁ * g' (f₁.1.endState f₁.2))
                  = ∑' ν' : State,
                      (((hstep.2).resolve_left (fun ha => hstep.1 ha.1)).2).postDist ν' *
                      ∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
                        (Scheduler.postTauWitness sys (E'.endState hT.1) l' μ).haltMass
                            (PMF.pure ν') f₁ * g' (f₁.1.endState f₁.2) from by
              refine tsum_congr (fun ν' => ?_)
              rw [hpd]
              simp only [dif_pos hstep]]
            exact Scheduler.postTau_marginal_collapse (E'.endState hT.1) l' μ hstep.2 hstep.1 g'
      _ = pe'.probOf E' hT.1 * ∑' σ : State, pe'.kernel E' (l', σ) * g' σ := by
          congr 1
          unfold ProbabilisticExecution.kernel
          rw [show (∑' σ : State, (∑' μ : PMF State,
                  pe'.scheduler.next E' (some (l', μ)) * μ σ) * g' σ)
                = ∑' μ : PMF State, ∑' σ : State,
                    pe'.scheduler.next E' (some (l', μ)) * μ σ * g' σ from by
            rw [show (∑' σ : State, (∑' μ : PMF State,
                    pe'.scheduler.next E' (some (l', μ)) * μ σ) * g' σ)
                  = ∑' σ : State, ∑' μ : PMF State,
                      pe'.scheduler.next E' (some (l', μ)) * μ σ * g' σ from
                tsum_congr (fun σ => by rw [ENNReal.tsum_mul_right])]
            rw [ENNReal.tsum_comm]]
          refine tsum_congr (fun μ => ?_)
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr (fun σ => by ring)
  · -- Non-tight `E'`: both sides vanish.
    rw [show (∑' σ : State,
            dite (E'.trans.Terminates ∧ Seq.map Prod.fst E'.trans = (↑L'.dropLast : Seq Label))
              (fun h => pe'.probOf E' h.1 * pe'.kernel E' (l', σ)
                * F ⟨E'.init, E'.trans.append (Seq.cons (l', σ) Seq.nil)⟩) (fun _ => 0)) = 0 from by
      refine ENNReal.tsum_eq_zero.mpr (fun σ => ?_); rw [dif_neg hT]]
    refine ENNReal.tsum_eq_zero.mpr (fun ν' => ?_)
    refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
    rw [pe'.beliefExpandW_eq L' ν' l' hL' (E', μ)]
    rw [dif_neg hT, zero_mul]

/-- **`next none = 1` from a vanishing `some`-spectrum.** A scheduler that emits nothing
(`next e (some a) = 0` for every step `a`) at a prefix `e` halts there with probability `1`,
since `next e` is a PMF whose total mass is `1`. -/
theorem Scheduler.next_none_eq_one_of_next_some_zero {State Label : Type}
    {sys : System State Label} (σ : Scheduler sys) (e : AlterSeq State Label)
    (h : ∀ a : Label × PMF State, σ.next e (some a) = 0) :
    σ.next e none = 1 := by
  classical
  have htot : (∑' o : Option (Label × PMF State), σ.next e o) = 1 := (σ.next e).tsum_coe
  rw [tsum_eq_single none (fun o ho => by
    cases o with
    | none => exact absurd rfl ho
    | some a => exact h a)] at htot
  exact htot

open Classical in
/-- **Bridge variant with trace recovered from the indicator.** Identical conclusion to
`extLabMass_eq_haltMass_tsum`, but the tightness hypothesis `hHalt` is conditioned on the trace
already being `ofList τ` (recovered for free from the `[trace = ofList τ]` indicator in the
target sum). This is the form actually dischargeable for `expandCont`, whose positive-haltMass
executions need NOT all have trace `ofList τ` (the drawn label can differ), but those that DO are
tight (they halt immediately after the single external label). -/
theorem extLabMass_eq_haltMass_tsum_tight {State Label : Type}
    {sys : LabelledSystem State Label} (σ : Scheduler sys.toSystem) (ν : PMF State)
    (τ : List Label) (g : State → ENNReal)
    (hHalt : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      σ.haltMass ν e ≠ 0 → sys.trace e.1 = Seq.ofList τ → sys.IsTight e.1)
    (hTight : ∀ e : AlterSeq State Label, (he : e.trans.Terminates) →
      sys.trace e = Seq.ofList τ → sys.IsTight e →
      (⟨ν, σ⟩ : ProbabilisticExecution sys.toSystem).probOf e he ≠ 0 →
      σ.next e none = 1) :
    sys.extLabMass ⟨ν, σ⟩ τ g
      = ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          σ.haltMass ν e * (if sys.trace e.1 = Seq.ofList τ then g (e.1.endState e.2) else 0) := by
  classical
  rw [sys.extLabMass_eq_tight_tsum ⟨ν, σ⟩ τ g]
  set R : {e : AlterSeq State Label // e.trans.Terminates} → ENNReal :=
    fun e => σ.haltMass ν e * (if sys.trace e.1 = Seq.ofList τ then g (e.1.endState e.2) else 0)
    with hR
  set i : {e : AlterSeq State Label // e.trans.Terminates ∧ sys.trace e = Seq.ofList τ
        ∧ sys.IsTight e} → {e : AlterSeq State Label // e.trans.Terminates} :=
    fun e => ⟨e.1, e.2.1⟩ with hi
  have hinj : Function.Injective i := by
    intro a b hab
    have : (i a).1 = (i b).1 := congrArg Subtype.val hab
    exact Subtype.ext this
  have hsupp : Function.support R ⊆ Set.range i := by
    intro e he
    rw [Function.mem_support] at he
    have hz : σ.haltMass ν e ≠ 0 := by
      intro h0; apply he; rw [hR]; simp only [h0, zero_mul]
    -- the trace indicator is the only way `R e` survives, so `trace e = ofList τ`.
    have htr : sys.trace e.1 = Seq.ofList τ := by
      by_contra hne
      apply he; rw [hR]; simp only [if_neg hne, mul_zero]
    have htight : sys.IsTight e.1 := hHalt e hz htr
    exact ⟨⟨e.1, ⟨e.2, htr, htight⟩⟩, Subtype.ext rfl⟩
  rw [← Function.Injective.tsum_eq hinj (f := R) hsupp]
  refine tsum_congr (fun e => ?_)
  rw [hR, hi]
  simp only []
  rw [if_pos e.2.2.1]
  rw [show σ.haltMass ν ⟨e.1, e.2.1⟩
        = (⟨ν, σ⟩ : ProbabilisticExecution sys.toSystem).probOf e.1 e.2.1
            * σ.next e.1 none from rfl]
  by_cases hp : (⟨ν, σ⟩ : ProbabilisticExecution sys.toSystem).probOf e.1 e.2.1 = 0
  · rw [hp]; simp
  · rw [hTight e.1 e.2.1 e.2.2.1 e.2.2.2 hp, mul_one]

open Classical in
/-- **The expand-segment external level mass collapses to `expandK`.** Applying the (tightness-
only) bridge `extLabMass_eq_haltMass_tsum_tight` to the segment-continuation scheduler
`expandCont sys pe' L' ν' l'` (run from the Dirac source `pure ν'`) at trace `[l]`: H1-tightness
holds because `expandCont` is silent past the external label (L5, `expandCont_next_some_eq_zero`),
so every positive-haltMass trace-`[l]` execution halts right after `l` (`isTight_of_silent_past_
trace`); H2 holds by the same silence (`next_none_eq_one_of_next_some_zero`). The bridge RHS is
exactly the definition of `expandK`. -/
theorem expandCont_extLabMass_eq_expandK {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (L' : List Label) (ν' : State) (l' l : Label) (g : State → ENNReal) :
    sys.extLabMass ⟨PMF.pure ν', Scheduler.expandCont sys pe' L' ν' l'⟩ [l] g
      = pe'.expandK L' l' l g ν' := by
  classical
  -- L5 silence (at terminating histories), packaged for the two bridge hypotheses.
  have hsilent : ∀ (e' : AlterSeq State Label), e'.trans.Terminates → sys.trace e' ≠ Seq.nil →
      ∀ a : Label × PMF State, (Scheduler.expandCont sys pe' L' ν' l').next e' (some a) = 0 :=
    fun e' heT htr a => Scheduler.expandCont_next_some_eq_zero sys pe' hExt L' ν' l' e' heT htr a
  rw [extLabMass_eq_haltMass_tsum_tight (Scheduler.expandCont sys pe' L' ν' l') (PMF.pure ν')
    [l] g ?_ ?_]
  · -- the bridge RHS is exactly `expandK` (same indicator, same haltMass).
    rfl
  · -- H1 (tightness): positive-haltMass trace-`[l]` execs are tight (silent ⟹ no trailing).
    intro e hne htr
    have hprob : (⟨PMF.pure ν', Scheduler.expandCont sys pe' L' ν' l'⟩
        : ProbabilisticExecution sys.toSystem).probOf e.1 e.2 ≠ 0 := by
      intro h0; apply hne
      change (⟨PMF.pure ν', Scheduler.expandCont sys pe' L' ν' l'⟩
          : ProbabilisticExecution sys.toSystem).probOf e.1 e.2
            * (Scheduler.expandCont sys pe' L' ν' l').next e.1 none = 0
      rw [h0, zero_mul]
    refine sys.isTight_of_silent_past_trace (Scheduler.expandCont sys pe' L' ν' l') (PMF.pure ν')
      hsilent e.1 e.2 ?_ hprob
    rw [htr]; exact (by simp [Stream'.Seq.ofList_cons] : (Seq.ofList [l] : Seq Label) ≠ Seq.nil)
  · -- H2: positive-probOf tight trace-`[l]` execs halt terminally.
    intro e he htr _htight _hp
    refine Scheduler.next_none_eq_one_of_next_some_zero
      (Scheduler.expandCont sys pe' L' ν' l') e (fun a => ?_)
    exact hsilent e he (by rw [htr]; simp [Stream'.Seq.ofList_cons]) a

open Classical in
/-- **`expandK` as a tight-`probOf` sum.** Restating `expandCont_extLabMass_eq_expandK` through
`extLabMass_eq_tight_tsum`: `expandK L' l' l g ν'` equals the `probOf`-weighted `g`-mass over the
tight trace-`[l]` executions of `⟨pure ν', expandCont …⟩`. This is the form fed to the PEEL
bijection (`expand_probOf_segment_factor` multiplies prefix `probOf` by this segment `probOf`). -/
theorem expandK_eq_tight_tsum {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (L' : List Label) (ν' : State) (l' l : Label) (g : State → ENNReal) :
    pe'.expandK L' l' l g ν'
      = ∑' seg : {e : AlterSeq State Label //
          e.trans.Terminates ∧ sys.trace e = Seq.ofList [l] ∧ sys.IsTight e},
          (⟨PMF.pure ν', Scheduler.expandCont sys pe' L' ν' l'⟩
            : ProbabilisticExecution sys.toSystem).probOf seg.1 seg.2.1
            * g (seg.1.endState seg.2.1) := by
  rw [← expandCont_extLabMass_eq_expandK pe' hExt L' ν' l' l g,
    sys.extLabMass_eq_tight_tsum ⟨PMF.pure ν', Scheduler.expandCont sys pe' L' ν' l'⟩ [l] g]

open Classical in
/-- **Tight-execution split at the last external transition.** A tight trace-`(L' ++ [l])`
execution `e` splits as `e.trans.toList = preList ++ segList` where `⟨e.init, ofList preList⟩` is
a tight trace-`L'` prefix (its last transition external) and `⟨ν', ofList segList⟩` (any source
`ν'`) is a tight trace-`[l]` segment whose only external transition is its last. The split is the
shortest prefix whose external sub-list is `L'`. Built on `List.exists_filter_split_tight`. -/
theorem LabelledSystem.tight_split_last_external {State Label : Type}
    (sys : LabelledSystem State Label) (e : AlterSeq State Label) (h : e.trans.Terminates)
    (L' : List Label) (l : Label)
    (htr : sys.trace e = Seq.ofList (L' ++ [l])) (htight : sys.IsTight e) :
    ∃ preList segList : List (Label × State),
      e.trans.toList h = preList ++ segList ∧
      (∀ x, preList.getLast? = some x → ¬ sys.internal x.1) ∧
      sys.trace ⟨e.init, Seq.ofList preList⟩ = Seq.ofList L' ∧
      sys.trace ⟨e.init, Seq.ofList segList⟩ = Seq.ofList [l] ∧
      sys.IsTight ⟨e.init, Seq.ofList segList⟩ ∧
      segList ≠ [] := by
  classical
  set Ltr := e.trans.toList h with hLtr
  set P : Label × State → Bool := fun p => decide (¬ sys.internal p.1) with hP
  -- `trace ⟨s, ofList K⟩ = ofList ((K.filter P).map fst)` for any list `K` and source `s`.
  have htrace_ofList : ∀ (s : State) (K : List (Label × State)),
      sys.trace ⟨s, Seq.ofList K⟩ = Seq.ofList ((K.filter P).map Prod.fst) := by
    intro s K
    change ((Seq.ofList K).filter (fun p => ¬ sys.internal p.1)).map Prod.fst = _
    rw [Stream'.Seq.filter_ofList_pub, Seq.map_ofList_pub]
  -- The external transition sub-list `T := Ltr.filter P` has fst-image `L' ++ [l]`.
  have hfst_filter : (Ltr.filter P).map Prod.fst = L' ++ [l] := by
    have htraceL : sys.trace ⟨e.init, Seq.ofList Ltr⟩ = Seq.ofList (L' ++ [l]) := by
      rw [hLtr]
      have : (⟨e.init, Seq.ofList (e.trans.toList h)⟩ : AlterSeq State Label) = e := by
        obtain ⟨ei, et⟩ := e
        simp only [AlterSeq.mk.injEq, true_and]
        exact Stream'.Seq.ofList_toList et h
      rw [this]; exact htr
    rw [htrace_ofList] at htraceL
    exact Stream'.Seq.ofList_injective htraceL
  -- `T = Tpre ++ [tlast]`: split off the last external transition (fst = `l`).
  obtain ⟨Tpre, tlast, hTsplit⟩ :
      ∃ Tpre tlast, Ltr.filter P = Tpre ++ [tlast] := by
    have hTne : Ltr.filter P ≠ [] := by
      intro hc; rw [hc, List.map_nil] at hfst_filter; exact absurd hfst_filter.symm (by simp)
    exact ⟨(Ltr.filter P).dropLast, (Ltr.filter P).getLast hTne,
      (List.dropLast_append_getLast hTne).symm⟩
  have hTpre_fst : Tpre.map Prod.fst = L' := by
    rw [hTsplit, List.map_append, List.map_singleton] at hfst_filter
    exact List.append_inj_left' hfst_filter (by simp)
  have htlast_l : tlast.1 = l := by
    rw [hTsplit, List.map_append, List.map_singleton] at hfst_filter
    have := List.append_inj_right' hfst_filter (by simp)
    simpa using this
  -- Split `Ltr` into `preList ++ segList` via the filter split.
  obtain ⟨preList, segList, hLtr_split, hpre_filt, hseg_filt, hpre_tight⟩ :=
    List.exists_filter_split_tight P Ltr Tpre [tlast] (by simp) hTsplit
  refine ⟨preList, segList, hLtr_split, ?_, ?_, ?_, ?_, ?_⟩
  · -- `preList`'s last transition is external (it satisfies `P`).
    intro x hx
    have := hpre_tight x hx
    simpa [hP] using this
  · -- trace of the prefix is `ofList L'`.
    rw [htrace_ofList, hpre_filt, hTpre_fst]
  · -- trace of the segment is `ofList [l]`.
    rw [htrace_ofList, hseg_filt, List.map_singleton, htlast_l]
  · -- the segment is tight: its trace is `[l]` and its last transition is external.
    -- `segList` is a nonempty suffix of `Ltr`, so its last transition equals `e`'s last,
    -- which is external by `e`'s tightness.
    have hsegne : segList ≠ [] := by
      intro hc; rw [hc, List.filter_nil] at hseg_filt; exact absurd hseg_filt.symm (by simp)
    have hseg_last : segList.getLast? = Ltr.getLast? := by
      rw [hLtr_split, List.getLast?_append_of_ne_nil _ hsegne]
    have hLtr_last_ext : ∀ ll, Ltr.getLast? = some ll → ¬ sys.internal ll.1 := by
      intro ll hll
      exact sys.tight_getLast_external e h htight ll (by rw [← hLtr]; exact hll)
    -- `traceTightLabs [l] (segList.map fst)`: filter is `[l]`, last label external.
    refine ((sys.tight_iff (Seq.ofList [l]) ⟨e.init, Seq.ofList segList⟩
      (Stream'.Seq.terminates_ofList _)).mpr ?_).2
    -- the label list is `segList.map fst` (since `(ofList segList).toList = segList`).
    have hlabs : (((⟨e.init, Seq.ofList segList⟩ : AlterSeq State Label).trans.toList
        (Stream'.Seq.terminates_ofList _)).map Prod.fst) = segList.map Prod.fst := by
      change ((Seq.ofList segList).toList _).map Prod.fst = _
      rw [Stream'.Seq.toList_ofList]
    rw [LabelledSystem.traceTightLabs, hlabs]
    refine ⟨?_, ?_⟩
    · -- filter of label list is `ofList [l]`.
      have hcomm : (Seq.ofList (segList.map Prod.fst)).filter (fun lab => ¬ sys.internal lab)
          = Seq.ofList (((segList.map Prod.fst).filter
              (fun lab => decide (¬ sys.internal lab)))) := Stream'.Seq.filter_ofList_pub _ _
      rw [hcomm]
      congr 1
      have : (segList.map Prod.fst).filter (fun lab => decide (¬ sys.internal lab))
          = (segList.filter P).map Prod.fst := by rw [List.filter_map]; rfl
      rw [this, hseg_filt, List.map_singleton, htlast_l]
    · -- last label is external.
      intro lab hlab
      rw [List.getLast?_map, hseg_last] at hlab
      cases hgl : Ltr.getLast? with
      | none => rw [hgl] at hlab; simp at hlab
      | some ll =>
        rw [hgl, Option.map_some] at hlab
        rw [← Option.some.inj hlab]
        exact hLtr_last_ext ll hgl
  · -- segList is nonempty (its filter `[tlast]` is nonempty).
    intro hc; rw [hc, List.filter_nil] at hseg_filt; exact absurd hseg_filt.symm (by simp)

open Classical in
/-- **PEEL half**: the trace-`(L' ++ [l])` external level mass of the expanded `sys`-execution
factors as the trace-`L'` external level mass of the continuation `expandK`. The tight-exec
bijection between trace-`(L'++[l])` execs and (tight trace-`L'` prefix, trace-`[l]` segment)
pairs, fed `expand_probOf_segment_factor`. Nonempty-`L'` case.

REMAINING BLOCKER: (1) the tight-exec bijection itself — each tight trace-`(L'++[l])` exec
`⟨init, ofList E⟩` splits uniquely as `E = preList ++ segList` with `⟨init, ofList preList⟩` the
tight trace-`L'` prefix (`exists_filter_split_tight` + `tight_singleton_prefix_internal` +
`isTight_append`/`trace_append`) and `segList` the trace-`[l]` segment; (2) the
haltMass-vs-probOf reconciliation — `extLabMass_eq_tight_tsum` sums *raw* `probOf` over tight
(ending-external) execs, whereas `expandK` is defined via `expandCont.haltMass` (= probOf · next
none). The inner segment sum `∑' segList tight-trace-[l], expandCont.probOf segList · g(end)`
must be identified with `expandK L' l' l g (endState preList)` (= the `haltMass`-weighted
trace-[l] mass). These agree because a tight trace-[l] segment ends at the new hyperStep
boundary where `expandCont` halts, but the precise raw-probOf ↔ haltMass equality needs its own
lemma (mirroring the tight-exec ↔ haltMass correspondence inside `extLabMass_eq_tight_tsum`). -/
theorem expand_extLabMass_peel {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (L' : List Label) (l' l : Label) (hL' : L'.getLast? = some l') (g : State → ENNReal) :
    sys.extLabMass ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ (L' ++ [l]) g
      = sys.extLabMass ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ L'
          (fun ν' => pe'.expandK L' l' l g ν') := by
  classical
  set PE : ProbabilisticExecution sys.toSystem :=
    ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ with hPE
  -- Reduce both sides to tight-`probOf` tsums; rewrite the RHS continuation via `expandK`.
  rw [sys.extLabMass_eq_tight_tsum PE (L' ++ [l]) g,
    sys.extLabMass_eq_tight_tsum PE L' (fun ν' => pe'.expandK L' l' l g ν')]
  -- Expand `expandK` into its tight trace-`[l]` segment sum and pull the prefix `probOf` in.
  have hRHS : ∀ e' : {e : AlterSeq State Label //
        e.trans.Terminates ∧ sys.trace e = Seq.ofList L' ∧ sys.IsTight e},
      PE.probOf e'.1 e'.2.1 * pe'.expandK L' l' l g (e'.1.endState e'.2.1)
        = ∑' seg : {e : AlterSeq State Label //
            e.trans.Terminates ∧ sys.trace e = Seq.ofList [l] ∧ sys.IsTight e},
          PE.probOf e'.1 e'.2.1
            * ((⟨PMF.pure (e'.1.endState e'.2.1),
                  Scheduler.expandCont sys pe' L' (e'.1.endState e'.2.1) l'⟩
                : ProbabilisticExecution sys.toSystem).probOf seg.1 seg.2.1
              * g (seg.1.endState seg.2.1)) := by
    intro e'
    rw [expandK_eq_tight_tsum pe' hExt L' (e'.1.endState e'.2.1) l' l g, ENNReal.tsum_mul_left]
  rw [tsum_congr hRHS]
  -- Abbreviations for the two summands.
  set Top : Type := {e : AlterSeq State Label //
      e.trans.Terminates ∧ sys.trace e = Seq.ofList (L' ++ [l]) ∧ sys.IsTight e} with hTop
  set Pre : Type := {e : AlterSeq State Label //
      e.trans.Terminates ∧ sys.trace e = Seq.ofList L' ∧ sys.IsTight e} with hPre
  set Seg : Type := {e : AlterSeq State Label //
      e.trans.Terminates ∧ sys.trace e = Seq.ofList [l] ∧ sys.IsTight e} with hSeg
  set fTop : Top → ENNReal := fun e => PE.probOf e.1 e.2.1 * g (e.1.endState e.2.1) with hfTop
  set fSig : ((_ : Pre) × Seg) → ENNReal :=
    fun p => PE.probOf p.1.1 p.1.2.1
      * ((⟨PMF.pure (p.1.1.endState p.1.2.1),
            Scheduler.expandCont sys pe' L' (p.1.1.endState p.1.2.1) l'⟩
          : ProbabilisticExecution sys.toSystem).probOf p.2.1 p.2.2.1
        * g (p.2.1.endState p.2.2.1)) with hfSig
  -- Fold the RHS double-tsum into a single tsum over the sigma type.
  rw [show (∑' (b : Pre) (seg : Seg),
          PE.probOf b.1 b.2.1
            * ((⟨PMF.pure (b.1.endState b.2.1),
                  Scheduler.expandCont sys pe' L' (b.1.endState b.2.1) l'⟩
                : ProbabilisticExecution sys.toSystem).probOf seg.1 seg.2.1
              * g (seg.1.endState seg.2.1)))
        = ∑' p : ((_ : Pre) × Seg), fSig p from (ENNReal.tsum_sigma' fSig).symm]
  -- The bijection: split each tight trace-`(L'++[l])` execution at its last external transition.
  symm
  -- For a tight `e : Top`, choose its split via `tight_split_last_external`.
  have hsplit : ∀ e : Top, ∃ preList segList : List (Label × State),
      e.1.trans.toList e.2.1 = preList ++ segList ∧
      (∀ x, preList.getLast? = some x → ¬ sys.internal x.1) ∧
      sys.trace ⟨e.1.init, Seq.ofList preList⟩ = Seq.ofList L' ∧
      sys.trace ⟨e.1.init, Seq.ofList segList⟩ = Seq.ofList [l] ∧
      sys.IsTight ⟨e.1.init, Seq.ofList segList⟩ ∧ segList ≠ [] :=
    fun e => sys.tight_split_last_external e.1 e.2.1 L' l e.2.2.1 e.2.2.2
  -- The chosen split lists and their properties, per `e : Top`.
  set preL : Top → List (Label × State) := fun e => (hsplit e).choose with hpreL
  set segL : Top → List (Label × State) := fun e => (hsplit e).choose_spec.choose with hsegL
  have hspec : ∀ e : Top,
      e.1.trans.toList e.2.1 = preL e ++ segL e ∧
      (∀ x, (preL e).getLast? = some x → ¬ sys.internal x.1) ∧
      sys.trace ⟨e.1.init, Seq.ofList (preL e)⟩ = Seq.ofList L' ∧
      sys.trace ⟨e.1.init, Seq.ofList (segL e)⟩ = Seq.ofList [l] ∧
      sys.IsTight ⟨e.1.init, Seq.ofList (segL e)⟩ ∧ segL e ≠ [] :=
    fun e => (hsplit e).choose_spec.choose_spec
  -- A list whose execution has trace `ofList τ` and whose last transition is external is tight.
  have htight_ofList : ∀ (s : State) (K : List (Label × State)) (τ : List Label),
      sys.trace ⟨s, Seq.ofList K⟩ = Seq.ofList τ →
      (∀ x, K.getLast? = some x → ¬ sys.internal x.1) →
      sys.IsTight ⟨s, Seq.ofList K⟩ := by
    intro s K τ htrK hlast
    refine ((sys.tight_iff (Seq.ofList τ) ⟨s, Seq.ofList K⟩
      (Stream'.Seq.terminates_ofList _)).mpr ?_).2
    have hlabs : (((⟨s, Seq.ofList K⟩ : AlterSeq State Label).trans.toList
        (Stream'.Seq.terminates_ofList _)).map Prod.fst) = K.map Prod.fst := by
      change ((Seq.ofList K).toList _).map Prod.fst = _
      rw [Stream'.Seq.toList_ofList]
    rw [LabelledSystem.traceTightLabs, hlabs]
    refine ⟨?_, ?_⟩
    · -- filter of label list = `ofList τ`: this is exactly `trace` of `⟨s, ofList K⟩`.
      have hfm : (Seq.ofList (K.map Prod.fst)).filter (fun lab => ¬ sys.internal lab)
          = ((Seq.ofList K).filter (fun p => ¬ sys.internal p.1)).map Prod.fst := by
        rw [Stream'.Seq.filter_ofList_pub, Stream'.Seq.filter_ofList_pub, Seq.map_ofList_pub]
        congr 1
        rw [List.filter_map]; rfl
      rw [hfm]; exact htrK
    · -- last label external.
      intro lab hlab
      rw [List.getLast?_map] at hlab
      cases hgl : K.getLast? with
      | none => rw [hgl] at hlab; simp at hlab
      | some x =>
        rw [hgl, Option.map_some] at hlab
        rw [← Option.some.inj hlab]
        exact hlast x hgl
  -- The prefix execution `⟨e.init, ofList (preL e)⟩ : Pre`.
  have hpreExec : ∀ e : Top, (Seq.ofList (preL e) : Seq (Label × State)).Terminates ∧
      sys.trace ⟨e.1.init, Seq.ofList (preL e)⟩ = Seq.ofList L' ∧
      sys.IsTight ⟨e.1.init, Seq.ofList (preL e)⟩ := by
    intro e
    exact ⟨Stream'.Seq.terminates_ofList _, (hspec e).2.2.1,
      htight_ofList e.1.init (preL e) L' (hspec e).2.2.1 (hspec e).2.1⟩
  -- The segment execution `⟨ν', ofList (segL e)⟩ : Seg`, where `ν' = preExec.end`.
  set preExec : Top → Pre := fun e =>
    ⟨⟨e.1.init, Seq.ofList (preL e)⟩, (hpreExec e).1, (hpreExec e).2.1, (hpreExec e).2.2⟩
    with hpreExecDef
  set nu : Top → State := fun e => (preExec e).1.endState (preExec e).2.1 with hnu
  have hsegExec : ∀ e : Top, (Seq.ofList (segL e) : Seq (Label × State)).Terminates ∧
      sys.trace ⟨nu e, Seq.ofList (segL e)⟩ = Seq.ofList [l] ∧
      sys.IsTight ⟨nu e, Seq.ofList (segL e)⟩ := by
    intro e
    refine ⟨Stream'.Seq.terminates_ofList _, (hspec e).2.2.2.1, ?_⟩
    exact sys.isTight_init_irrel e.1.init (nu e) _ (hspec e).2.2.2.2.1
  set segExec : Top → Seg := fun e =>
    ⟨⟨nu e, Seq.ofList (segL e)⟩, (hsegExec e).1, (hsegExec e).2.1, (hsegExec e).2.2⟩
    with hsegExecDef
  -- Reconstruction: every `e : Top` is the concatenation of its split lists.
  have hrecon : ∀ e : Top,
      e.1 = ⟨e.1.init, Seq.ofList (preL e ++ segL e)⟩ := by
    intro e
    have htrans : e.1.trans = Seq.ofList (preL e ++ segL e) := by
      conv_lhs => rw [← Stream'.Seq.ofList_toList e.1.trans e.2.1]
      rw [(hspec e).1]
    calc e.1 = ⟨e.1.init, e.1.trans⟩ := rfl
      _ = ⟨e.1.init, Seq.ofList (preL e ++ segL e)⟩ := by rw [htrans]
  -- The segment is the (init-`ν'`) segment execution; its internal-prefix property.
  have hseg_int : ∀ e : Top, ∀ (pref : List (Label × State)) (stp : Label × State),
      pref ++ [stp] <+: segL e → ∀ q ∈ pref, sys.internal q.1 := by
    intro e pref stp hpf q hq
    refine sys.tight_singleton_prefix_internal ⟨nu e, Seq.ofList (segL e)⟩
      (Stream'.Seq.terminates_ofList _) l (hsegExec e).2.1 (hsegExec e).2.2 pref stp ?_ q hq
    change pref ++ [stp] <+: (Seq.ofList (segL e)).toList _
    rw [Stream'.Seq.toList_ofList]; exact hpf
  -- **The unconditional value match**: `fSig ⟨preExec e, segExec e⟩ = fTop e` for every `e`.
  have hval_gen : ∀ e : Top, fSig ⟨preExec e, segExec e⟩ = fTop e := by
    intro e
    simp only [hfSig, hfTop]
    -- Factor `PE.probOf e.1` through the segment via `expand_probOf_segment_factor`.
    have hfactor := expand_probOf_segment_factor pe' e.1.init L' l' hL' (preL e) (segL e)
      (hspec e).2.1 (hspec e).2.2.1 (hseg_int e)
    have hpreVal : (preExec e).1 = (⟨e.1.init, Seq.ofList (preL e)⟩ : AlterSeq State Label) := rfl
    have hsegVal : (segExec e).1 = (⟨nu e, Seq.ofList (segL e)⟩ : AlterSeq State Label) := rfl
    have hABterm : ((Seq.ofList (preL e)).append (Seq.ofList (segL e))).Terminates := by
      rw [← Stream'.Seq.ofList_append]; exact Stream'.Seq.terminates_ofList _
    -- Match end-states: `e.1.end = (segExec e).1.end`.
    have hend : e.1.endState e.2.1 = (segExec e).1.endState (hsegExec e).1 := by
      have hsplit_end := AlterSeq.endState_append (s := e.1.init) (s' := nu e)
        (Seq.ofList (preL e)) (Seq.ofList (segL e))
        (Stream'.Seq.terminates_ofList _) (Stream'.Seq.terminates_ofList _)
        (by rw [Stream'.Seq.toList_ofList]; exact (hspec e).2.2.2.2.2) hABterm
      calc e.1.endState e.2.1
          = (⟨e.1.init, Seq.ofList (preL e ++ segL e)⟩ : AlterSeq State Label).endState
              (Stream'.Seq.terminates_ofList _) :=
            AlterSeq.endState_congr_pub (hrecon e) _ _
        _ = (⟨e.1.init, (Seq.ofList (preL e)).append (Seq.ofList (segL e))⟩
              : AlterSeq State Label).endState hABterm :=
            AlterSeq.endState_congr_pub
              (congrArg (AlterSeq.mk e.1.init) (Stream'.Seq.ofList_append _ _)) _ _
        _ = (⟨nu e, Seq.ofList (segL e)⟩ : AlterSeq State Label).endState
              (Stream'.Seq.terminates_ofList _) := hsplit_end
        _ = (segExec e).1.endState (hsegExec e).1 :=
            AlterSeq.endState_congr_pub hsegVal.symm _ (hsegExec e).1
    rw [hend]
    -- Factor the probOf via `expand_probOf_segment_factor` (= `hfactor`).
    have hprob : PE.probOf e.1 e.2.1
        = PE.probOf (preExec e).1 (hpreExec e).1
          * (⟨PMF.pure (nu e), Scheduler.expandCont sys pe' L' (nu e) l'⟩
              : ProbabilisticExecution sys.toSystem).probOf (segExec e).1 (hsegExec e).1 := by
      calc PE.probOf e.1 e.2.1
          = PE.probOf (⟨e.1.init, Seq.ofList (preL e ++ segL e)⟩ : AlterSeq State Label)
              (Stream'.Seq.terminates_ofList _) :=
            PE.probOf_congr _ _ (hrecon e) _ _
        _ = PE.probOf (⟨e.1.init, Seq.ofList (preL e)⟩ : AlterSeq State Label)
              (Stream'.Seq.terminates_ofList _)
            * (⟨PMF.pure (nu e), Scheduler.expandCont sys pe' L' (nu e) l'⟩
                : ProbabilisticExecution sys.toSystem).probOf
                (⟨nu e, Seq.ofList (segL e)⟩ : AlterSeq State Label)
                (Stream'.Seq.terminates_ofList _) := by rw [hPE]; exact hfactor
        _ = PE.probOf (preExec e).1 (hpreExec e).1
            * (⟨PMF.pure (nu e), Scheduler.expandCont sys pe' L' (nu e) l'⟩
                : ProbabilisticExecution sys.toSystem).probOf (segExec e).1 (hsegExec e).1 := by
            rw [PE.probOf_congr (⟨e.1.init, Seq.ofList (preL e)⟩ : AlterSeq State Label)
                (preExec e).1 hpreVal.symm (Stream'.Seq.terminates_ofList _) (hpreExec e).1,
              ProbabilisticExecution.probOf_congr _
                (⟨nu e, Seq.ofList (segL e)⟩ : AlterSeq State Label) (segExec e).1 hsegVal.symm
                (Stream'.Seq.terminates_ofList _) (hsegExec e).1]
    rw [hprob]; ring
  -- The split map.
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun x => ⟨preExec x.1, segExec x.1⟩) ?hinj ?hf ?hfg
  case hfg =>
    rintro ⟨e, he⟩
    exact hval_gen e
  case hinj =>
    rintro ⟨e₁, hx₁⟩ ⟨e₂, hx₂⟩ heq
    -- Recover `init`, `preL`, `segL` equalities from the sigma equality.
    have hinit : e₁.1.init = e₂.1.init :=
      congrArg (fun p => (p.1.1 : AlterSeq State Label).init) heq
    have hpreEq : preL e₁ = preL e₂ := by
      have h := congrArg (fun p => (p.1.1 : AlterSeq State Label).trans) heq
      exact Stream'.Seq.ofList_injective h
    have hsegEq : segL e₁ = segL e₂ := by
      have h := congrArg (fun p => (p.2.1 : AlterSeq State Label).trans) heq
      exact Stream'.Seq.ofList_injective h
    -- Reconstruct: both are `⟨init, ofList (preL ++ segL)⟩`.
    refine Subtype.ext (Subtype.ext ?_)
    rw [hrecon e₁, hrecon e₂, hinit, hpreEq, hsegEq]
  case hf =>
    rintro ⟨b, seg⟩ hbseg
    -- `fSig ≠ 0` forces `seg.init = b.end` (Dirac source `pure b.end`).
    have hsegInit : seg.1.init = b.1.endState b.2.1 := by
      by_contra hne
      apply hbseg
      simp only [hfSig]
      have hz : (⟨PMF.pure (b.1.endState b.2.1),
            Scheduler.expandCont sys pe' L' (b.1.endState b.2.1) l'⟩
          : ProbabilisticExecution sys.toSystem).probOf seg.1 seg.2.1 = 0 := by
        rw [ProbabilisticExecution.probOf_init_factor _ (PMF.pure (b.1.endState b.2.1))
            seg.1 seg.2.1,
          PMF.pure_apply_of_ne (b.1.endState b.2.1) seg.1.init hne, zero_mul]
      rw [hz, zero_mul, mul_zero]
    -- The concatenated execution `e := ⟨b.init, b.trans.append seg.trans⟩`.
    have hABterm : (b.1.trans.append seg.1.trans).Terminates :=
      ⟨Nat.find b.2.1 + Nat.find seg.2.1,
        Stream'.Seq.terminatedAt_append_find b.2.1 (Nat.find_spec seg.2.1)⟩
    have hseg_ne : seg.1.trans.toList seg.2.1 ≠ [] :=
      sys.tight_singleton_trans_nonempty seg.1 seg.2.1 l seg.2.2.1
    -- trace of the concatenation is `ofList (L' ++ [l])`.
    have htr_e : sys.trace ⟨b.1.init, b.1.trans.append seg.1.trans⟩ = Seq.ofList (L' ++ [l]) := by
      rw [sys.trace_append b.1.init seg.1.init b.1.trans seg.1.trans b.2.1,
        b.2.2.1, seg.2.2.1, ← Stream'.Seq.ofList_append]
    -- tightness of the concatenation.
    have htight_e : sys.IsTight ⟨b.1.init, b.1.trans.append seg.1.trans⟩ :=
      sys.isTight_append b.1.init b.1.trans seg.1.trans b.2.1 seg.2.1 hseg_ne
        (sys.isTight_init_irrel seg.1.init b.1.init seg.1.trans seg.2.2.2)
    set e : Top := ⟨⟨b.1.init, b.1.trans.append seg.1.trans⟩, hABterm, htr_e, htight_e⟩ with heDef
    -- The transition list of `e` is `b.trans.toList ++ seg.trans.toList`.
    have he_toList : e.1.trans.toList e.2.1
        = b.1.trans.toList b.2.1 ++ seg.1.trans.toList seg.2.1 :=
      Stream'.Seq.toList_append b.1.trans seg.1.trans b.2.1 seg.2.1 e.2.1
    -- The chosen split of `e` coincides with `(b.trans.toList, seg.trans.toList)`.
    set P : Label × State → Bool := fun p => decide (¬ sys.internal p.1) with hP
    -- The `P`-filter of any `K` with trace-`τ` execution has fst-image `τ`.
    have hPfilterMap : ∀ (s : State) (K : List (Label × State)) (τ : List Label),
        sys.trace ⟨s, Seq.ofList K⟩ = Seq.ofList τ → (K.filter P).map Prod.fst = τ := by
      intro s K τ hK
      have : Seq.ofList ((K.filter P).map Prod.fst) = Seq.ofList τ := by
        rw [← Seq.map_ofList_pub, hP, ← Stream'.Seq.filter_ofList_pub]; exact hK
      exact Stream'.Seq.ofList_injective this
    have hbtr : sys.trace ⟨b.1.init, Seq.ofList (b.1.trans.toList b.2.1)⟩ = Seq.ofList L' := by
      rw [Stream'.Seq.ofList_toList]; exact b.2.2.1
    have hbfilt_len : ((b.1.trans.toList b.2.1).filter P).length = L'.length := by
      rw [← List.length_map (as := (b.1.trans.toList b.2.1).filter P) Prod.fst,
        hPfilterMap b.1.init _ L' hbtr]
    have hprefilt_len : ((preL e).filter P).length = L'.length := by
      rw [← List.length_map (as := (preL e).filter P) Prod.fst,
        hPfilterMap e.1.init _ L' (hspec e).2.2.1]
    -- the two prefix `P`-filters agree (both are the first `|L'|` externals of `e.toList`).
    have hfilt_eq : (b.1.trans.toList b.2.1).filter P = (preL e).filter P := by
      have hcat : (b.1.trans.toList b.2.1).filter P ++ (seg.1.trans.toList seg.2.1).filter P
          = (preL e).filter P ++ (segL e).filter P := by
        rw [← List.filter_append, ← List.filter_append, ← he_toList, (hspec e).1]
      exact List.append_inj_left hcat (by rw [hbfilt_len, hprefilt_len])
    -- `b.toList` and `preL e` are tight prefixes (both end external).
    have hb_ext : ∀ y, (b.1.trans.toList b.2.1).getLast? = some y → P y := by
      intro y hy; simpa [hP] using sys.tight_getLast_external b.1 b.2.1 b.2.2.2 y hy
    have hsplit_eq : b.1.trans.toList b.2.1 = preL e :=
      List.filter_tight_split_unique P (b.1.trans.toList b.2.1) (seg.1.trans.toList seg.2.1)
        (preL e) (segL e) (by rw [← he_toList, (hspec e).1]) hfilt_eq hb_ext
        (by intro y hy; simpa [hP] using (hspec e).2.1 y hy)
    -- hence `segL e = seg.toList` too.
    have hsegL_eq : seg.1.trans.toList seg.2.1 = segL e := by
      have hcat : b.1.trans.toList b.2.1 ++ seg.1.trans.toList seg.2.1 = preL e ++ segL e := by
        rw [← he_toList, (hspec e).1]
      rw [hsplit_eq] at hcat
      exact List.append_cancel_left hcat
    -- `preExec e = b` and `segExec e = seg`.
    have hpreExec_eq : preExec e = b := by
      refine Subtype.ext ?_
      have : (preExec e).1 = (⟨b.1.init, Seq.ofList (preL e)⟩ : AlterSeq State Label) := rfl
      rw [this, ← hsplit_eq, Stream'.Seq.ofList_toList]
    have hnu_eq : nu e = b.1.endState b.2.1 := by
      rw [hnu]
      have : (preExec e).1.endState (preExec e).2.1 = b.1.endState b.2.1 :=
        AlterSeq.endState_congr_pub (congrArg Subtype.val hpreExec_eq) _ _
      exact this
    have hsegExec_eq : segExec e = seg := by
      refine Subtype.ext ?_
      have hsv : (segExec e).1 = (⟨nu e, Seq.ofList (segL e)⟩ : AlterSeq State Label) := rfl
      rw [hsv, hnu_eq, ← hsegL_eq, Stream'.Seq.ofList_toList, ← hsegInit]
    -- `fTop e = fSig ⟨b, seg⟩` (unconditional value match, via `preExec e = b`, `segExec e = seg`).
    have hval : fTop e = fSig ⟨b, seg⟩ := by
      rw [← hval_gen e, hpreExec_eq, hsegExec_eq]
    refine ⟨⟨e, ?_⟩, ?_⟩
    · -- `e ∈ support fTop`: `fTop e = fSig ⟨b, seg⟩ ≠ 0`.
      change fTop e ≠ 0
      rw [hval]; exact hbseg
    · -- the witness maps to `⟨b, seg⟩`.
      simp only []
      rw [hpreExec_eq, hsegExec_eq]

/-- **`expand`'s emission at a trace-empty history is the empty-history `drawAndRun`'s** (the
`none`-branch of `expand.next`). On a terminating history `e` whose external trace is empty, the
expanded scheduler's emission equals `drawAndRun pe' ⟨sys.init, nil⟩`'s emission at the
`internalSuffix` of `e`. (PEEL base case, nil analogue of `expand_next_eq_expandCont`.) -/
theorem expand_next_eq_drawAndRun (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e : AlterSeq State Label) (hT : e.trans.Terminates)
    (hgl : ((sys.trace e).toList (Stream'.Seq.terminates_map_iff.mpr
        (Stream'.Seq.terminates_filter _ _ hT))).getLast? = none) :
    (Scheduler.expand sys pe').next e
      = (Scheduler.drawAndRun pe' ⟨sys.toSystem.init, Seq.nil⟩).next (sys.internalSuffix e) := by
  classical
  unfold Scheduler.expand
  simp only [dif_pos hT]
  rw [hgl]

open Classical in
/-- **Kernel-agreement on a trace-empty internal prefix.** At an all-internal within-segment
position `⟨sys.init, ofList pref₀⟩` (so the running external trace is empty), the expanded
scheduler's one-step kernel coincides with that of `⟨pure sys.init, drawAndRun pe' ⟨sys.init,
nil⟩⟩` at `⟨sys.init, ofList pref₀⟩`. The nil analogue of `expand_kernel_eq_expandCont` (with
empty `preList`, source `sys.init`). -/
theorem expand_kernel_eq_drawAndRun {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (pref₀ : List (Label × State)) (hpref_int : ∀ p ∈ pref₀, sys.internal p.1)
    (step : Label × State) :
    (⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩
        : ProbabilisticExecution sys.toSystem).kernel
        ⟨sys.toSystem.init, Seq.ofList pref₀⟩ step
      = (⟨PMF.pure sys.toSystem.init, Scheduler.drawAndRun pe' ⟨sys.toSystem.init, Seq.nil⟩⟩
          : ProbabilisticExecution sys.toSystem).kernel
        ⟨sys.toSystem.init, Seq.ofList pref₀⟩ step := by
  classical
  set e : AlterSeq State Label := ⟨sys.toSystem.init, Seq.ofList pref₀⟩ with he
  have heT : e.trans.Terminates := Stream'.Seq.terminates_ofList _
  -- Running external trace is empty (all transitions internal).
  have htr : sys.trace e = Seq.nil := by
    rw [he, show (Seq.ofList pref₀ : Seq (Label × State)) = Seq.ofList ([] ++ pref₀)
        by rw [List.nil_append],
      sys.trace_append_internal sys.toSystem.init [] pref₀ hpref_int]
    rw [Stream'.Seq.ofList_nil]
    exact sys.trace_init sys.toSystem.init
  -- The trace label list is empty, so getLast? = none.
  have hgl : ((sys.trace e).toList
      (Stream'.Seq.terminates_map_iff.mpr (Stream'.Seq.terminates_filter _ _ heT))).getLast?
      = none := by
    have hcongr : (sys.trace e).toList
        (Stream'.Seq.terminates_map_iff.mpr (Stream'.Seq.terminates_filter _ _ heT)) = [] := by
      apply Stream'.Seq.ofList_injective
      rw [Stream'.Seq.ofList_toList, htr, Stream'.Seq.ofList_nil]
    rw [hcongr]; rfl
  -- The internal suffix is `⟨sys.init, ofList pref₀⟩ = e`.
  have hsuf : sys.internalSuffix e = e := by
    rw [he, show (Seq.ofList pref₀ : Seq (Label × State)) = Seq.ofList ([] ++ pref₀)
        by rw [List.nil_append]]
    rw [sys.internalSuffix_append_internal sys.toSystem.init [] pref₀ (by simp) hpref_int]
    congr 1
    rw [AlterSeq.endState_eq_getLast? _ (Stream'.Seq.terminates_ofList _)]
    rw [Stream'.Seq.toList_ofList]; rfl
  -- `expand.next e = drawAndRun.next e`.
  have hnext : (Scheduler.expand sys pe').next e
      = (Scheduler.drawAndRun pe' ⟨sys.toSystem.init, Seq.nil⟩).next e := by
    rw [expand_next_eq_drawAndRun sys pe' e heT hgl, hsuf]
  -- Kernels are tsums of the (equal) `next`s.
  unfold ProbabilisticExecution.kernel
  refine tsum_congr (fun μ => ?_)
  rw [show (⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩
        : ProbabilisticExecution sys.toSystem).scheduler = Scheduler.expand sys pe' from rfl,
    show (⟨PMF.pure sys.toSystem.init, Scheduler.drawAndRun pe' ⟨sys.toSystem.init, Seq.nil⟩⟩
        : ProbabilisticExecution sys.toSystem).scheduler
      = Scheduler.drawAndRun pe' ⟨sys.toSystem.init, Seq.nil⟩ from rfl]
  rw [hnext]

open Classical in
/-- **`probOf` agreement of `expand` and the empty-history `drawAndRun` on a tight trace-`[l]`
execution.** A tight trace-`[l]` execution `⟨sys.init, ofList segList⟩` (whose only external
transition is its last, `segList`'s prefixes-before-last all internal) has the same `expand`- and
`drawAndRun ⟨sys.init,nil⟩`-probability. Fed `probOf_append_of_kernel_eq` with empty `preList`
and the nil kernel-agreement `expand_kernel_eq_drawAndRun`. -/
theorem expand_probOf_eq_drawAndRun {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (segList : List (Label × State))
    (hseg_int : ∀ (pref : List (Label × State)) (stp : Label × State),
      pref ++ [stp] <+: segList → ∀ q ∈ pref, sys.internal q.1) :
    (⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩
        : ProbabilisticExecution sys.toSystem).probOf
        ⟨sys.toSystem.init, Seq.ofList segList⟩ (Stream'.Seq.terminates_ofList _)
      = (⟨PMF.pure sys.toSystem.init, Scheduler.drawAndRun pe' ⟨sys.toSystem.init, Seq.nil⟩⟩
          : ProbabilisticExecution sys.toSystem).probOf
        ⟨sys.toSystem.init, Seq.ofList segList⟩ (Stream'.Seq.terminates_ofList _) := by
  classical
  have hfactor := (⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩
      : ProbabilisticExecution sys.toSystem).probOf_append_of_kernel_eq
    (⟨PMF.pure sys.toSystem.init, Scheduler.drawAndRun pe' ⟨sys.toSystem.init, Seq.nil⟩⟩
      : ProbabilisticExecution sys.toSystem)
    sys.toSystem.init sys.toSystem.init [] segList ?_ ?_
  · -- `pe.probOf ⟨init, ofList ([] ++ segList)⟩ = probOf ⟨init, ofList []⟩ · drawAndRun.probOf …`.
    rw [List.nil_append] at hfactor
    have hempty : (⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩
          : ProbabilisticExecution sys.toSystem).probOf ⟨sys.toSystem.init, Seq.ofList []⟩
          (Stream'.Seq.terminates_ofList _) = 1 := by
      rw [ProbabilisticExecution.probOf_congr _ ⟨sys.toSystem.init, Seq.ofList []⟩
        ⟨sys.toSystem.init, Seq.nil⟩
        (by rw [Stream'.Seq.ofList_nil]) (Stream'.Seq.terminates_ofList _)
        Stream'.Seq.terminates_nil,
        ProbabilisticExecution.probOf_nil]
      exact PMF.pure_apply_self _
    rw [hfactor, hempty, one_mul]
  · -- `drawAndRun`'s init at `sys.init` is `1`.
    rw [ProbabilisticExecution.init_eq_initState]; exact PMF.pure_apply_self _
  · -- kernel agreement at every visited within-segment (all-internal) position.
    intro pref stp hpf
    have hpref_int : ∀ p ∈ pref, sys.internal p.1 := hseg_int pref stp hpf
    rw [List.nil_append]
    exact expand_kernel_eq_drawAndRun pe' pref hpref_int stp

open Classical in
/-- **The `L' = []` base step.** The trace-`[l]` external level mass of the expanded
`sys`-execution equals `pe'`'s hyper-step-boundary mass at `[l]`. The expanded scheduler at
`⟨init, nil⟩` runs the empty-history `none`-branch `drawAndRun ⟨init, nil⟩` (kernel-agreeing on
the all-internal prefix up to and including the `l`-emission, `expand_probOf_eq_drawAndRun`),
whose trace-`[l]` slice (`drawAndRun_pushforward`) is exactly `hsLabMass [l] g`'s single-history
(`E' = ⟨init, nil⟩`) summand (`hsLabMass_eq_Z_sum` route, here read directly off the definition). -/
theorem expand_extLabMass_step_nil {State Label : Type}
    {sys : LabelledSystem State Label} (pe' : ProbabilisticExecution sys^w.toSystem)
    (h_init : pe'.initState = PMF.pure sys^w.toSystem.init)
    (hExt : ∀ E l μ, some (l, μ) ∈ (pe'.scheduler.next E).support → ¬ sys.internal l)
    (l : Label) (g : State → ENNReal) :
    sys.extLabMass ⟨PMF.pure sys.toSystem.init, Scheduler.expand sys pe'⟩ ([] ++ [l]) g
      = pe'.hsLabMass ([] ++ [l]) g := by
  classical
  rw [List.nil_append]
  set ι := sys.toSystem.init with hι
  -- STEP 1: replace `expand` by the empty-history `drawAndRun ⟨ι, nil⟩` (probOf-agree on
  -- tight trace-`[l]` execs via `expand_probOf_eq_drawAndRun`).
  have hreplace : sys.extLabMass ⟨PMF.pure ι, Scheduler.expand sys pe'⟩ [l] g
      = sys.extLabMass ⟨PMF.pure ι, Scheduler.drawAndRun pe' ⟨ι, Seq.nil⟩⟩ [l] g := by
    rw [sys.extLabMass_eq_tight_tsum ⟨PMF.pure ι, Scheduler.expand sys pe'⟩ [l] g,
      sys.extLabMass_eq_tight_tsum ⟨PMF.pure ι, Scheduler.drawAndRun pe' ⟨ι, Seq.nil⟩⟩ [l] g]
    refine tsum_congr (fun e => ?_)
    by_cases hinit : e.1.init = ι
    · -- on-support exec: rewrite `e.1` as `⟨ι, ofList (e.toList)⟩` and apply the probOf-agreement.
      have he1 : e.1 = (⟨ι, Seq.ofList (e.1.trans.toList e.2.1)⟩ : AlterSeq State Label) := by
        calc e.1 = ⟨e.1.init, e.1.trans⟩ := rfl
          _ = ⟨ι, Seq.ofList (e.1.trans.toList e.2.1)⟩ := by
              rw [hinit, Stream'.Seq.ofList_toList]
      have hseg_int : ∀ (pref : List (Label × State)) (stp : Label × State),
          pref ++ [stp] <+: e.1.trans.toList e.2.1 → ∀ q ∈ pref, sys.internal q.1 := by
        intro pref stp hpf q hq
        exact sys.tight_singleton_prefix_internal e.1 e.2.1 l e.2.2.1 e.2.2.2 pref stp hpf q hq
      have hpe := expand_probOf_eq_drawAndRun pe' (e.1.trans.toList e.2.1) hseg_int
      rw [show (⟨PMF.pure ι, Scheduler.expand sys pe'⟩
            : ProbabilisticExecution sys.toSystem).probOf e.1 e.2.1
          = (⟨PMF.pure ι, Scheduler.expand sys pe'⟩
              : ProbabilisticExecution sys.toSystem).probOf
              ⟨ι, Seq.ofList (e.1.trans.toList e.2.1)⟩ (Stream'.Seq.terminates_ofList _) from
        ProbabilisticExecution.probOf_congr _ _ _ he1 _ _]
      rw [show (⟨PMF.pure ι, Scheduler.drawAndRun pe' ⟨ι, Seq.nil⟩⟩
            : ProbabilisticExecution sys.toSystem).probOf e.1 e.2.1
          = (⟨PMF.pure ι, Scheduler.drawAndRun pe' ⟨ι, Seq.nil⟩⟩
              : ProbabilisticExecution sys.toSystem).probOf
              ⟨ι, Seq.ofList (e.1.trans.toList e.2.1)⟩ (Stream'.Seq.terminates_ofList _) from
        ProbabilisticExecution.probOf_congr _ _ _ he1 _ _]
      rw [hpe]
    · -- off-support exec: both `probOf`s vanish (Dirac init factor).
      rw [ProbabilisticExecution.probOf_init_factor (Scheduler.expand sys pe') (PMF.pure ι)
          e.1 e.2.1,
        ProbabilisticExecution.probOf_init_factor (Scheduler.drawAndRun pe' ⟨ι, Seq.nil⟩)
          (PMF.pure ι) e.1 e.2.1,
        PMF.pure_apply_of_ne ι e.1.init hinit, zero_mul, zero_mul, zero_mul, zero_mul]
  rw [hreplace]
  -- STEP 2: `drawAndRun`-bridge to the haltMass form (silence ⟹ tight) + `drawAndRun_pushforward`.
  have hsilent : ∀ (e' : AlterSeq State Label), e'.trans.Terminates → sys.trace e' ≠ Seq.nil →
      ∀ a : Label × PMF State, (Scheduler.drawAndRun pe' ⟨ι, Seq.nil⟩).next e' (some a) = 0 :=
    fun e' heT htr a => Scheduler.drawAndRun_next_some_eq_zero pe' hExt ⟨ι, Seq.nil⟩
      Stream'.Seq.terminates_nil e' heT htr a
  rw [extLabMass_eq_haltMass_tsum_tight (Scheduler.drawAndRun pe' ⟨ι, Seq.nil⟩) (PMF.pure ι)
    [l] g ?_ ?_]
  · -- the haltMass sum is `drawAndRun_pushforward` at `E'' = ⟨ι, nil⟩` (end-state `ι`).
    have hend : (⟨ι, Seq.nil⟩ : AlterSeq State Label).endState Stream'.Seq.terminates_nil = ι := by
      rw [AlterSeq.endState_of_trans_nil _ rfl Stream'.Seq.terminates_nil]
    rw [show (PMF.pure ι : PMF State)
          = PMF.pure ((⟨ι, Seq.nil⟩ : AlterSeq State Label).endState Stream'.Seq.terminates_nil)
        from by rw [hend]]
    rw [Scheduler.drawAndRun_pushforward pe' hExt ⟨ι, Seq.nil⟩ Stream'.Seq.terminates_nil l g, hend]
    -- RHS: `hsLabMass [l] g` over the single history `⟨ι, nil⟩`, read off the definition.
    -- `map fst s = nil ⟹ s = nil`.
    have hmapnil : ∀ s : Seq (Label × State), Seq.map Prod.fst s = Seq.nil → s = Seq.nil := by
      intro s hs
      have h0 : (Seq.map Prod.fst s).get? 0 = none := by rw [hs]; rfl
      rw [Stream'.Seq.map_get?] at h0
      have hs0 : s.get? 0 = none := by
        cases hg : s.get? 0 with
        | none => rfl
        | some a => rw [hg] at h0; simp at h0
      exact Stream'.Seq.terminatedAt_zero_iff.mp hs0
    have hRHS : pe'.hsLabMass [l] g
        = ∑' μ : PMF State,
            pe'.scheduler.next ⟨ι, Seq.nil⟩ (some (l, μ)) * pe'.hsExpect ι l μ g := by
      rw [ProbabilisticExecution.hsLabMass, List.getLast?_singleton]
      simp only [List.dropLast_singleton]
      -- only `E' = ⟨ι, nil⟩` survives the `dite` (map-fst = `ofList [] = nil` forces `trans = nil`,
      -- and `probOf ⟨ι, nil⟩ = initState ι = 1`).
      rw [tsum_eq_single (⟨ι, Seq.nil⟩ : AlterSeq State Label) ?_]
      · rw [dif_pos ⟨Stream'.Seq.terminates_nil,
            by rw [Stream'.Seq.map_nil, Stream'.Seq.ofList_nil]⟩]
        have hpnil : pe'.probOf ⟨ι, Seq.nil⟩ Stream'.Seq.terminates_nil = 1 := by
          rw [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState, h_init]
          exact PMF.pure_apply_self _
        have hes : (⟨ι, Seq.nil⟩ : AlterSeq State Label).endState Stream'.Seq.terminates_nil = ι :=
          by rw [AlterSeq.endState_of_trans_nil _ rfl Stream'.Seq.terminates_nil]
        rw [hpnil, one_mul, hes]
      · -- every other `E'` has summand `0`: either the `dite` fails (`map-fst ≠ nil`), or
        -- `trans = nil` but `init ≠ ι`, so `probOf = (pure ι) init = 0`.
        intro E' hne
        by_cases hc : E'.trans.Terminates ∧ Seq.map Prod.fst E'.trans = Seq.ofList ([] : List Label)
        · rw [dif_pos hc]
          have htrans_nil : E'.trans = Seq.nil := by
            rw [Stream'.Seq.ofList_nil] at hc
            exact hmapnil E'.trans hc.2
          have hinit_E' : E'.init ≠ ι := by
            intro hii; apply hne
            obtain ⟨ei, et⟩ := E'
            simp only at htrans_nil hii
            rw [htrans_nil, hii]
          have hprob0 : pe'.probOf E' hc.1 = 0 := by
            rw [show pe'.probOf E' hc.1
                = pe'.initState E'.init * (⟨PMF.pure E'.init, pe'.scheduler⟩
                    : ProbabilisticExecution sys^w.toSystem).probOf E' hc.1 from
              ProbabilisticExecution.probOf_init_factor pe'.scheduler pe'.initState E' hc.1]
            rw [h_init, PMF.pure_apply_of_ne sys^w.toSystem.init E'.init hinit_E', zero_mul]
          rw [hprob0, zero_mul]
        · rw [dif_neg hc]
    rw [hRHS]
  · -- H1 (tightness): positive-haltMass trace-`[l]` execs are tight.
    intro e hne htr
    have hprob : (⟨PMF.pure ι, Scheduler.drawAndRun pe' ⟨ι, Seq.nil⟩⟩
        : ProbabilisticExecution sys.toSystem).probOf e.1 e.2 ≠ 0 := by
      intro h0; apply hne
      change (⟨PMF.pure ι, Scheduler.drawAndRun pe' ⟨ι, Seq.nil⟩⟩
          : ProbabilisticExecution sys.toSystem).probOf e.1 e.2
            * (Scheduler.drawAndRun pe' ⟨ι, Seq.nil⟩).next e.1 none = 0
      rw [h0, zero_mul]
    refine sys.isTight_of_silent_past_trace (Scheduler.drawAndRun pe' ⟨ι, Seq.nil⟩) (PMF.pure ι)
      hsilent e.1 e.2 ?_ hprob
    rw [htr]; exact (by simp [Stream'.Seq.ofList_cons] : (Seq.ofList [l] : Seq Label) ≠ Seq.nil)
  · -- H2: positive-probOf tight trace-`[l]` execs halt terminally.
    intro e he htr _htight _hp
    refine Scheduler.next_none_eq_one_of_next_some_zero
      (Scheduler.drawAndRun pe' ⟨ι, Seq.nil⟩) e (fun a => ?_)
    exact hsilent e he (by rw [htr]; simp [Stream'.Seq.ofList_cons]) a

/-- **The inductive step of `expand_extLabMass_eq` (PEEL + ASSEMBLE).** Given the
induction hypothesis (`extLabMass L' g' = hsLabMass L' g'` for every test `g'`), the
trace-`(L' ++ [l])` external level mass of the expanded `sys`-execution equals `pe'`'s
hyper-step-boundary level mass at `(L' ++ [l])`. Route: PEEL (`expand_extLabMass_peel`) factors
the trace-`(L'++[l])` mass as the trace-`L'` mass of the continuation `expandK`; the IH rewrites
that to `hsLabMass L' (expandK …)`; ASSEMBLE (`hsLabMass_expandK_step`) collapses it to
`hsLabMass (L'++[l]) g`. The `L' = []` case is handled directly (the continuation is the
`none`-branch). -/
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
  classical
  match hLm : L'.getLast? with
  | some l' =>
      rw [expand_extLabMass_peel pe' hExt L' l' l hLm g,
          ih (fun ν' => pe'.expandK L' l' l g ν'),
          hsLabMass_expandK_step pe' hExt L' l' l hLm g]
  | none =>
      -- `L' = []`: the continuation is the empty-history `none`-branch. Isolated sub-step.
      have hnil : L' = [] := List.getLast?_eq_none_iff.mp hLm
      subst hnil
      exact expand_extLabMass_step_nil pe' h_init hExt l g

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
      rfl
  | append_singleton L' l ih =>
      exact expand_extLabMass_step pe' h_init hExt L' l g ih

/-- **The expand-direction trace equality** (under `hExt`): the expanded
`sys`-execution and `pe'` assign the same probability to every finite external
trace `Seq.ofList L`. -/
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

/-! ### Trace-equality (general) and the M2 goal theorems

These sit last: `expand_traceProb_tight_tsum_eq` is the only remaining `sorry` (the Phase-2
WLOG dropping `hExt`); `expand_traceProb_eq`/`expand_exists`/`weakClosure_*` are the M2 goals
that consume it. Everything above is the construction + the (axiom-clean) hExt trace-equality. -/

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
