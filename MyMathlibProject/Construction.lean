/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.WeakStep

/-!
# Constructions on PLTSs

This file collects constructions that build new probabilistic labelled
transition systems from existing ones, using the weak-step infrastructure
from `WeakStep.lean`.
-/

open Stream'

namespace PLTS

variable {α β State State_C State_A Label : Type}

/-! ## The distribution-monad construction

Lift a labelled PLTS `sys` to a new labelled PLTS whose state space is
`PMF State` (the free PMF on `State`) and whose steps are exactly the
`hyperStep`s of `sys`. -/

/-- The **distribution-monad construction** on a labelled PLTS.

Given `sys : LabelledSystem State Label`, lift the state space to `PMF State`.
The lifted system has:

* `init := PMF.pure sys.init` — a Dirac on the original initial state;
* `step μ l ω := hyperStep sys μ l (ω.bind id)` — a transition from
  the pre-distribution `μ` at label `l` to a `PMF (PMF State)` outcome `ω`
  is valid iff the flattened destination `ω.bind id : PMF State` is reachable
  from `μ` via a `hyperStep`;
* `internal := sys.internal` — the label classification is inherited.

The PMF wrapper on the post-state slot of `System.step` is "absorbed" by
flattening with `bind id`; the lifted step thus identifies any two
post-state-of-post-state distributions that agree after one bind, which is
the natural identification under the PMF-monad multiplication
`μ : PMF (PMF α) ↦ μ.bind id : PMF α`. -/
noncomputable def LabelledSystem.dist (sys : LabelledSystem State Label) :
    LabelledSystem (PMF State) Label where
  init := PMF.pure sys.init
  step μ l ω := hyperStep sys μ l (ω.bind id)
  internal := sys.internal

/-- `𝒟(sys)` is sugar for `LabelledSystem.dist sys`, the distribution-monad
construction lifting `sys` to a labelled system over `PMF State`. -/
scoped notation:max "𝒟(" sys ")" => LabelledSystem.dist sys

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

Both `𝒟(·)` and `·^w` are designed to leave the *set of achievable trace
distributions* invariant. Each preservation theorem splits into two set
inclusions ("subset" and "superset"). One direction of each is the structural
lift of `sys`-executions into the construction; the other is the harder
"flatten" / "expand" direction.
-/

/-! ### Trace-distribution sets achievable by a system -/

/-- The set of trace distributions achievable by some probabilistic execution
of the labelled system `ls`. Equality of this set across two systems means
the systems are trace-distribution-equivalent. -/
def achievableTraceDists (ls : LabelledSystem State Label) :
    Set (Seq Label → ENNReal) :=
  {D | ∃ pe : ProbabilisticExecution ls.toSystem, ∀ τ, ls.traceProb pe τ = D τ}

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
  rintro D ⟨pe, hpe⟩
  refine ⟨
    { initState := pe.initState
      scheduler :=
        { next := pe.scheduler.next
          valid := fun e n s h_term h_state l μ h_supp =>
            sys.step_le_weakClosure_step
              (pe.scheduler.valid e n s h_term h_state l μ h_supp) } }, ?_⟩
  intro τ
  exact hpe τ

/-! #### Algorithmic construction of `pe` from `pe'`

For the hard direction (`achievableTraceDists sys^w ⊆ achievableTraceDists sys`),
we construct `pe : ProbabilisticExecution sys.toSystem` from
`pe' : ProbabilisticExecution sys^w.toSystem` via the following algorithm:

  Initialize:  e_w ← ⟨s₀, Seq.nil⟩,  e ← ⟨s₀, Seq.nil⟩   (s₀ ∼ pe'.initState)

  Outer loop:
    sample emit ∼ pe'.scheduler.next e_w
    match emit with
    | none           → STOP (pe halts)
    | some (l, μ)    → execute the weak-step witness on sys:
                       sub-sample each emitted sys-step (l', μ'), update e
                       (the sub-loop ends when the witness scheduler halts).
                       After the sub-loop, append (l, e.endState) to e_w.
    repeat

The algorithm maintains two histories `(e_w, e)` jointly; pe.scheduler observes
only `e` and marginalises over the hidden `e_w`.

* A **stutter** at one outer-iteration is the event that pe' emits some weak
  step (l, μ), but the witness's sub-loop emits *zero* sys-steps (the witness
  scheduler halts on its first call). The outer loop continues with `e_w`
  extended by `(l, e.endState)` but `e` unchanged.
* A **stutter trap** at observed `e` is the event that, starting from `e`,
  every reachable `e_w` extension stutters forever — no visible sys-step and
  no halt is ever produced. -/

/-- **Reaching probability** of the joint algorithm state `(e_w, e)`: the
probability that the algorithm visits `(e_w, e)` at some outer-iteration. -/
private noncomputable def reachProb (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (_e_w _e : AlterSeq State Label) : ENNReal :=
  sorry

/-- **Single-iteration outcome distribution** at joint state `(e_w, e)`.
Possible outcomes per outer-iteration sample:
* `none` — pe' returns `none` (algorithm halts).
* `some d` — pe' returns `some (l, μ)` and the weak-step witness's first
  sub-iteration emits a sys-step whose distribution is `d : PMF (Label × PMF State)`.

Stutter outcomes (pe' returns `some (l, μ)` but the witness halts
immediately) contribute *zero mass* to this PMF — they are accounted for via
the e_w-marginalisation, which sums over stutter-extended `e_w`'s. -/
private noncomputable def iterOutcome (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (_e_w _e : AlterSeq State Label) :
    PMF (Option (PMF (Label × PMF State))) :=
  sorry

/-- **Total mass** of non-stutter outcomes at observed `e`, summed over all
reachable hidden `e_w`: the denominator of the renewal-corrected scheduler. -/
private noncomputable def totalMass (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (_e : AlterSeq State Label) : ENNReal :=
  sorry

/-- **Witness pe : ProbabilisticExecution sys.toSystem** constructed
algorithmically from `pe' : ProbabilisticExecution sys^w.toSystem`. -/
private noncomputable def pe_of_weak (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) :
    ProbabilisticExecution sys.toSystem where
  initState := pe'.initState
  scheduler :=
    { next := fun e =>
        if totalMass sys pe' e = 0 then
          -- **Stutter-trap fallback.** From observed `e`, the algorithm
          -- enters infinite stutter with probability 1 (no future visible
          -- action and pe' never halts). We default to `PMF.pure none`,
          -- treating the trap as a halt at `e`.
          --
          -- NOTE: this fallback choice is plausible but not 100% verified.
          -- If trace-coupling proofs fail at the trap case, revisit.
          PMF.pure none
        else
          sorry -- normalised marginalised PMF over `(Option (Label × PMF State))`
      valid := sorry }

/-- **Hard direction of `weakClosure_traceProb_eq`** (deferred): every trace
distribution achievable by `sys^w` is achievable by `sys`. The witness is
`pe_of_weak sys pe'`, an algorithmic construction that "executes" pe''s weak
transitions on the original system. See the comment block above for the
algorithm. -/
theorem weakClosure_traceProb_superset (sys : LabelledSystem State Label) :
    achievableTraceDists sys^w ⊆ achievableTraceDists sys := by
  sorry

/-- **Weak-closure construction preserves trace distributions.** -/
theorem weakClosure_traceProb_eq (sys : LabelledSystem State Label) :
    achievableTraceDists sys = achievableTraceDists sys^w :=
  Set.Subset.antisymm
    (weakClosure_traceProb_subset sys)
    (weakClosure_traceProb_superset sys)

/-! ### The distribution-monad construction preserves trace distributions

Both directions are non-trivial: lifting a `pe` over `sys` to `𝒟(sys)`
requires reshaping `pe`'s scheduler signature to operate on histories over
`PMF State` (with Dirac-state lifts of each transition), while the reverse
direction requires flattening genuine `PMF (PMF State)`-randomness from
`𝒟(sys)` back into `pe`-on-`sys`. Both are deferred. -/

/-- **Subset direction of `dist_traceProb_eq`** (deferred). -/
theorem dist_traceProb_subset (sys : LabelledSystem State Label) :
    achievableTraceDists sys ⊆ achievableTraceDists 𝒟(sys) := by
  sorry

/-- **Superset direction of `dist_traceProb_eq`** (deferred). -/
theorem dist_traceProb_superset (sys : LabelledSystem State Label) :
    achievableTraceDists 𝒟(sys) ⊆ achievableTraceDists sys := by
  sorry

/-- **Distribution-monad construction preserves trace distributions.** -/
theorem dist_traceProb_eq (sys : LabelledSystem State Label) :
    achievableTraceDists sys = achievableTraceDists 𝒟(sys) :=
  Set.Subset.antisymm
    (dist_traceProb_subset sys)
    (dist_traceProb_superset sys)

end PLTS
