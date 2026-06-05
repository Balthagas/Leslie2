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

/-- Per-outer-iteration outcome at joint state `(e_w, e)`:
* `halt` — pe' returns `none` (algorithm halts).
* `visible d` — pe' returns `some (l, μ)` and the weak-step witness's first
  sub-iteration emits a sys-step with distribution `d : PMF (Label × PMF State)`.
* `stutter` — pe' returns `some (l, μ)` but the witness halts immediately
  (zero sys-steps emitted in this iteration). The outer loop will continue. -/
inductive AlgoStepOutcome (Label : Type) (State : Type) where
  | halt    : AlgoStepOutcome Label State
  | visible : PMF (Label × PMF State) → AlgoStepOutcome Label State
  | stutter : AlgoStepOutcome Label State

/-- Predicate: an outcome is non-stutter (i.e., counts toward `totalMass`). -/
def AlgoStepOutcome.isNonStutter {Label State : Type}
    (o : AlgoStepOutcome Label State) : Prop :=
  match o with
  | .halt      => True
  | .visible _ => True
  | .stutter   => False

/-- **Single-iteration outcome distribution** at joint state `(e_w, e)`. This
samples once from `pe'.scheduler.next e_w` and (if not a halt) starts the
weak-step expansion, exposing either the first sys-step's distribution
(`visible d`) or signalling immediate stutter (`stutter`).

For non-terminating `e_w` (unreachable in the algorithm), defaults to `halt`. -/
private noncomputable def iterOutcome (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w _e : AlterSeq State Label) :
    PMF (AlgoStepOutcome Label State) :=
  open Classical in
  if h_term : e_w.trans.Terminates then
    let s_pre : State := e_w.endState h_term
    (pe'.scheduler.next e_w).bind fun emit =>
      -- `Option.elim` (rather than `match`) makes the case-split reduce
      -- cleanly via `Option.elim_none` / `Option.elim_some` in downstream proofs.
      emit.elim
        -- emit = none: pe' halts immediately.
        (PMF.pure AlgoStepOutcome.halt)
        -- emit = some lμ: process the weak step.
        (fun lμ =>
          if h_supp : some lμ ∈ (pe'.scheduler.next e_w).support then
            have h_sw : sys^w.step s_pre lμ.1 lμ.2 :=
              pe'.scheduler.valid e_w (Nat.find h_term) s_pre
                (Nat.find_spec h_term)
                (AlterSeq.stateAt_find_eq_endState e_w h_term)
                lμ.1 lμ.2 h_supp
            if h_int : sys.internal lμ.1 then
              -- Internal weak step: extract weakTau witness.
              have h_wt : weakTau sys (PMF.pure s_pre) lμ.2 := by
                rcases h_sw with ⟨_, h⟩ | ⟨h_ext, _⟩
                · exact h
                · exact absurd h_int h_ext
              (h_wt.witness.next ⟨s_pre, Seq.nil⟩).bind fun sub_emit =>
                sub_emit.elim
                  -- σ halts: stutter.
                  (PMF.pure AlgoStepOutcome.stutter)
                  -- σ emits sub_lμ: visible PMF.pure sub_lμ.
                  (fun sub_lμ =>
                    PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ)))
            else
              -- External weak step: extract weakStep witness chain.
              have h_ws : weakStep sys (PMF.pure s_pre) lμ.1 lμ.2 := by
                rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
                · exact absurd h_int' h_int
                · exact h
              (h_ws.weakTau_pre.witness.next ⟨s_pre, Seq.nil⟩).bind fun sub_emit =>
                sub_emit.elim
                  -- σ_pre halts: proceed to labelled hyperStep.
                  (PMF.pure (AlgoStepOutcome.visible
                    ((h_ws.hyperStep_mid.kernel s_pre).map (fun μ_l => (lμ.1, μ_l)))))
                  -- σ_pre emits sub_lμ: visible PMF.pure sub_lμ.
                  (fun sub_lμ =>
                    PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ)))
          else
            -- (l, μ) outside support: zero-mass anyway. Default to halt.
            PMF.pure AlgoStepOutcome.halt)
  else
    -- Non-terminating e_w (unreachable). Default to halt.
    PMF.pure AlgoStepOutcome.halt

/-- **Chain probability** of a weak scheduler σ producing exactly `chain` then
halting, starting from sub-prefix `sub_prefix`.

Definition (recursive on `chain`):
* `[]`        — σ halts immediately at `sub_prefix`. Probability `σ.next sub_prefix none`.
* `(l,s)::rest` — σ first emits some `(l, μ)` with `s ∈ μ.support`, then
  continues from the extended sub-prefix.  Probability factor
  `∑ μ, σ.next sub_prefix (some (l, μ)) · μ s` times the chain-probability of
  `rest` from the extended sub-prefix.

Used as a sub-component of `oneIterTransitionProb`. -/
private noncomputable def chainProb {sys : LabelledSystem State Label}
    (σ : WeakScheduler sys) (sub_prefix : AlterSeq State Label) :
    List (Label × State) → ENNReal
  | List.nil => σ.next sub_prefix none
  | List.cons hd rest =>
      (∑' μ : PMF State, σ.next sub_prefix (some (hd.1, μ)) * μ hd.2) *
      chainProb σ ⟨sub_prefix.init, sub_prefix.trans.append (Seq.cons hd Seq.nil)⟩ rest

/-- Split a list of `(Label × State)` at the first occurrence of label `l`:
returns `(prefix-before-l, none)` if `l` doesn't occur, or
`(prefix-before-l, some (s_mid, suffix-after-l))` if `(l, s_mid)` is the first
entry whose label is `l`. -/
private noncomputable def splitAtLabel (l : Label) :
    List (Label × State) →
      List (Label × State) × Option (State × List (Label × State))
  | List.nil => (List.nil, none)
  | List.cons pair rest =>
      open Classical in
      if pair.1 = l then
        (List.nil, some (pair.2, rest))
      else
        let split_rest := splitAtLabel l rest
        (List.cons pair split_rest.1, split_rest.2)

/-- **One-iteration transition probability**: from joint state `(e_w_prev, e_prev)`,
the probability that a single outer-iteration emits weak step `(l_last, μ)`
(for some `μ`) and the witness's expansion produces a sys-step chain that
extends `e_prev` exactly to `e`.

  oneIterTransitionProb = ∑_μ pe'.scheduler.next e_w_prev (some (l_last, μ))
                            · P[witness for (l_last, μ) produces this chain]

The chain-probability factor depends on the witness structure:
* **Internal `l_last`**: witness is a single `weakTau` `WeakScheduler σ`;
  chain-probability is `chainProb σ ⟨s_pre, Seq.nil⟩ chain`.
* **External `l_last`**: witness chain is σ_pre + hyperStep at `l_last` + σ_post;
  the chain is decomposed at the unique `l_last`-position. (Deferred.) -/
private noncomputable def oneIterTransitionProb
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_prev : AlterSeq State Label) (l_last : Label)
    (e_prev e : AlterSeq State Label) : ENNReal :=
  open Classical in
  if h_ewp : e_w_prev.trans.Terminates then
  if h_ep : e_prev.trans.Terminates then
  if h_e : e.trans.Terminates then
    let s_pre : State := e_w_prev.endState h_ewp
    let e_prev_list : List (Label × State) := e_prev.trans.toList h_ep
    let e_list : List (Label × State) := e.trans.toList h_e
    -- Chain extending e_prev to e: requires e_prev's trans to be a prefix of
    -- e's trans, and initial states to agree.
    if h_prefix : e_prev.init = e.init ∧ e_list.take e_prev_list.length = e_prev_list then
      let chain : List (Label × State) := e_list.drop e_prev_list.length
      ∑' μ : PMF State,
        pe'.scheduler.next e_w_prev (some (l_last, μ)) *
        (if h_supp : some (l_last, μ) ∈ (pe'.scheduler.next e_w_prev).support then
          have h_sw : sys^w.step s_pre l_last μ :=
            pe'.scheduler.valid e_w_prev (Nat.find h_ewp) s_pre
              (Nat.find_spec h_ewp)
              (AlterSeq.stateAt_find_eq_endState e_w_prev h_ewp)
              l_last μ h_supp
          if h_int : sys.internal l_last then
            -- Internal: extract weakTau witness and run chainProb on σ.
            have h_wt : weakTau sys (PMF.pure s_pre) μ := by
              rcases h_sw with ⟨_, h⟩ | ⟨h_ext, _⟩
              · exact h
              · exact absurd h_int h_ext
            chainProb h_wt.witness ⟨s_pre, Seq.nil⟩ chain
          else
            -- External: decompose chain at the first `l_last`-position into
            -- chain_pre + [(l_last, s_mid)] + chain_post.
            have h_ws : weakStep sys (PMF.pure s_pre) l_last μ := by
              rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
              · exact absurd h_int' h_int
              · exact h
            let σ_pre := h_ws.weakTau_pre.witness
            let σ_post := h_ws.weakTau_post.witness
            let p := h_ws.hyperStep_mid.kernel
            let split := splitAtLabel l_last chain
            let chain_pre := split.1
            match split.2 with
            | none =>
                -- No `l_last` in chain: not a valid external-step expansion.
                0
            | some (s_mid, chain_post) =>
                -- State immediately before the labelled hyperStep:
                -- last state of chain_pre if non-empty, else s_pre.
                let s_mid_pre : State :=
                  (chain_pre.getLast?.map Prod.snd).getD s_pre
                chainProb σ_pre ⟨s_pre, Seq.nil⟩ chain_pre *
                  (∑' μ_l : PMF State, p s_mid_pre μ_l * μ_l s_mid) *
                  chainProb σ_post ⟨s_mid, Seq.nil⟩ chain_post
        else 0)
    else 0
  else 0
  else 0
  else 0

/-- **Reaching probability** of the joint algorithm state `(e_w, e)`: the
probability that the algorithm visits `(e_w, e)` at some outer-iteration.

Recursive structure on `e_w.trans.toList` (via `List.reverseRecOn`):

* **Base** (`e_w.trans = nil`): the algorithm is in its initial state. Returns
  `pe'.initState e_w.init` if `e = ⟨e_w.init, Seq.nil⟩`, else `0`.
* **Step** (`e_w.trans = trans_prev ++ [(l_last, s_last)]`): one outer-iteration
  transitioned the algorithm from `(e_w_prev, e_prev)` to `(e_w, e)` where
  `e_w_prev = ⟨e_w.init, Seq.ofList trans_prev⟩` and `e_prev` is some prefix
  of `e`. Sum `reachProb (e_w_prev, e_prev) * oneIterTransitionProb …` over
  `e_prev`. -/
private noncomputable def reachProb (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w e : AlterSeq State Label) : ENNReal :=
  open Classical in
  if h_e_w_term : e_w.trans.Terminates then
    (e_w.trans.toList h_e_w_term).reverseRecOn
      (motive := fun _ => AlterSeq State Label → ENNReal)
      -- Base: the initial joint state.
      (fun e' =>
        if e_w.init = e'.init ∧ e'.trans = Seq.nil then
          pe'.initState e_w.init
        else 0)
      -- Step: previous joint state was `(e_w_prev, e_prev)`, one iteration
      -- transitioned to `(e_w, e')`. The algorithm's invariant `e_w.endState =
      -- e.endState` is enforced explicitly: only joint states with matching
      -- endStates contribute. (Each outer-iteration appends `(l, e.endState)`
      -- to `e_w`, so the new `last_step.2` must equal `e'.endState`.)
      (fun trans_prev last_step ih_function e' =>
        if h_e'_term : e'.trans.Terminates then
          if e'.endState h_e'_term = last_step.2 then
            let e_w_prev : AlterSeq State Label :=
              ⟨e_w.init, Seq.ofList trans_prev⟩
            ∑' e_prev : AlterSeq State Label,
              ih_function e_prev *
                oneIterTransitionProb sys pe' e_w_prev last_step.1 e_prev e'
          else 0
        else 0)
      e
  else 0

/-- **Unnormalised joint kernel** at observed `e`: function on
`Option (Label × PMF State)` returning the joint mass over all `e_w`
contributing a non-stutter outcome with that emission. -/
private noncomputable def jointUnnorm (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e : AlterSeq State Label) :
    Option (Label × PMF State) → ENNReal
  | none => ∑' e_w : AlterSeq State Label,
              reachProb sys pe' e_w e * (iterOutcome sys pe' e_w e .halt)
  | some (l, μ) => ∑' e_w : AlterSeq State Label,
                     reachProb sys pe' e_w e *
                       ∑' d : PMF (Label × PMF State),
                         iterOutcome sys pe' e_w e (.visible d) * d (l, μ)

/-- **Total mass** of non-stutter outcomes at observed `e`, equal to the
tsum of `jointUnnorm` over `Option (Label × PMF State)`. This is the
normalisation denominator for the marginalised scheduler.

By the algebra (Fubini + `PMF.tsum_coe`), this also equals
`∑' e_w, reachProb pe' e_w e * (halt-mass + ∑' d, visible-d-mass)`. -/
private noncomputable def totalMass (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e : AlterSeq State Label) : ENNReal :=
  ∑' opt : Option (Label × PMF State), jointUnnorm sys pe' e opt

/-- **Step-validity of `iterOutcome`'s `visible` outputs.** If `iterOutcome`
at `(e_w, e)` assigns positive mass to `visible d`, then every `(l, μ) ∈ d.support`
satisfies `sys.step (e_w.endState) l μ`.

Justification (deferred): unfold `iterOutcome`'s case-split. In each branch
that emits `visible d`, `d` is either `PMF.pure (l_int, μ_int)` (from σ's
emission, σ.valid gives sys.step) or `p.map (μ_l ↦ (l, μ_l))` (from
`hyperStep.kernel`, kernel_step gives sys.step). Both cases give the needed
sys.step at `e_w.endState`. -/
private lemma iterOutcome_visible_implies_step
    {sys : LabelledSystem State Label}
    {pe' : ProbabilisticExecution sys^w.toSystem}
    (e_w e : AlterSeq State Label) (h_e_w_term : e_w.trans.Terminates)
    (d : PMF (Label × PMF State))
    (h_iter_pos : iterOutcome sys pe' e_w e (.visible d) ≠ 0)
    (l : Label) (μ : PMF State)
    (h_d_supp : (l, μ) ∈ d.support) :
    sys.step (e_w.endState h_e_w_term) l μ := by
  classical
  set s_pre : State := e_w.endState h_e_w_term with h_s_pre_def
  -- Unfold iterOutcome and take the then-branch via h_e_w_term.
  simp only [iterOutcome, dif_pos h_e_w_term] at h_iter_pos
  -- Outer bind: extract a positive emit.
  rw [PMF.bind_apply] at h_iter_pos
  rw [Ne, ENNReal.tsum_eq_zero] at h_iter_pos
  push Not at h_iter_pos
  obtain ⟨emit, h_emit_ne⟩ := h_iter_pos
  rw [mul_ne_zero_iff] at h_emit_ne
  obtain ⟨h_P_ne, h_inner_ne⟩ := h_emit_ne
  rcases emit with _ | ⟨l_pe, μ_pe⟩
  · -- emit = none: reduces to PMF.pure halt, no visible d-mass.
    simp only [Option.elim_none] at h_inner_ne
    exfalso; apply h_inner_ne
    simp [PMF.pure_apply]
  · -- emit = some (l_pe, μ_pe). Reduce Option.elim and the dif on h_supp.
    have h_emit_supp : some (l_pe, μ_pe) ∈ (pe'.scheduler.next e_w).support := h_P_ne
    simp only [Option.elim_some, dif_pos h_emit_supp] at h_inner_ne
    have h_sw : sys^w.step s_pre l_pe μ_pe :=
      pe'.scheduler.valid e_w (Nat.find h_e_w_term) s_pre
        (Nat.find_spec h_e_w_term)
        (AlterSeq.stateAt_find_eq_endState e_w h_e_w_term)
        l_pe μ_pe h_emit_supp
    by_cases h_int : sys.internal l_pe
    · -- Internal weak step.
      simp only [dif_pos h_int] at h_inner_ne
      -- Sub-bind on σ.next ⟨s_pre, Seq.nil⟩.
      rw [PMF.bind_apply] at h_inner_ne
      rw [Ne, ENNReal.tsum_eq_zero] at h_inner_ne
      push Not at h_inner_ne
      obtain ⟨sub_emit, h_sub_ne⟩ := h_inner_ne
      rw [mul_ne_zero_iff] at h_sub_ne
      obtain ⟨h_sub_P, h_sub_inner⟩ := h_sub_ne
      rcases sub_emit with _ | ⟨l_int, μ_int⟩
      · -- sub_emit = none: PMF.pure stutter, no visible d.
        simp only [Option.elim_none] at h_sub_inner
        exfalso; apply h_sub_inner
        simp [PMF.pure_apply]
      · -- sub_emit = some (l_int, μ_int): PMF.pure (visible (PMF.pure (l_int, μ_int))).
        simp only [Option.elim_some] at h_sub_inner
        -- d must equal PMF.pure (l_int, μ_int).
        have h_d_eq : d = PMF.pure (l_int, μ_int) := by
          by_contra h_ne
          apply h_sub_inner
          rw [PMF.pure_apply, if_neg]
          intro h_eq
          apply h_ne
          injection h_eq
        rw [h_d_eq, PMF.mem_support_iff, PMF.pure_apply] at h_d_supp
        have h_pair_eq : (l, μ) = (l_int, μ_int) := by
          by_contra h_ne
          apply h_d_supp; rw [if_neg h_ne]
        -- Extract the WeakScheduler witness and use its validity.
        have h_wt : weakTau sys (PMF.pure s_pre) μ_pe := by
          rcases h_sw with ⟨_, h⟩ | ⟨hext, _⟩
          · exact h
          · exact absurd h_int hext
        have h_sub_supp :
            some (l_int, μ_int) ∈ (h_wt.witness.next ⟨s_pre, Seq.nil⟩).support := h_sub_P
        have h_σ_valid : sys.step s_pre l_int μ_int :=
          h_wt.witness.valid ⟨s_pre, Seq.nil⟩ 0 s_pre
            (show (Seq.nil : Seq (Label × State)).TerminatedAt 0 from
              Stream'.Seq.terminatedAt_nil)
            rfl l_int μ_int h_sub_supp
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_pair_eq
        exact h_σ_valid
    · -- External weak step.
      simp only [dif_neg h_int] at h_inner_ne
      rw [PMF.bind_apply] at h_inner_ne
      rw [Ne, ENNReal.tsum_eq_zero] at h_inner_ne
      push Not at h_inner_ne
      obtain ⟨sub_emit, h_sub_ne⟩ := h_inner_ne
      rw [mul_ne_zero_iff] at h_sub_ne
      obtain ⟨h_sub_P, h_sub_inner⟩ := h_sub_ne
      have h_ws : weakStep sys (PMF.pure s_pre) l_pe μ_pe := by
        rcases h_sw with ⟨hint, _⟩ | ⟨_, h⟩
        · exact absurd hint h_int
        · exact h
      rcases sub_emit with _ | ⟨l_pre, μ_pre⟩
      · -- σ_pre halts: d = (h_ws.hyperStep_mid.kernel s_pre).map (·).
        simp only [Option.elim_none] at h_sub_inner
        have h_d_eq : d = (h_ws.hyperStep_mid.kernel s_pre).map (fun μ_l => (l_pe, μ_l)) := by
          by_contra h_ne
          apply h_sub_inner
          rw [PMF.pure_apply, if_neg]
          intro h_eq
          apply h_ne
          injection h_eq
        rw [h_d_eq, PMF.mem_support_map_iff] at h_d_supp
        obtain ⟨μ_l, h_μ_l_supp, h_pair⟩ := h_d_supp
        have h_l_eq : l = l_pe := (Prod.mk.inj h_pair).1.symm
        have h_μ_eq : μ = μ_l := (Prod.mk.inj h_pair).2.symm
        -- We need s_pre ∈ h_ws.preDist.support to apply hyperStep.kernel_step.
        -- Argument: σ_pre.next ⟨s_pre, Seq.nil⟩ has positive mass at `none`
        -- (h_sub_P, since we're in the sub_emit = none case). The runFromState
        -- recursion's none-branch keeps s_pre at s_pre, so this lower-bounds
        -- (σ_pre.run n s_pre) s_pre by σ_pre.next none (via the helper
        -- `WeakScheduler.run_apply_self_ge_next_none`). The witness equation
        -- gives h_ws.preDist s_pre = (σ_pre.run n s_pre) s_pre.
        have h_s_pre_in_preDist : s_pre ∈ h_ws.preDist.support := by
          rw [PMF.mem_support_iff]
          set σ_pre := h_ws.weakTau_pre.witness with h_σ_pre_def
          set n := h_ws.weakTau_pre.witness_fuel with h_n_def
          have h_run : (PMF.pure s_pre).bind (σ_pre.run n) = h_ws.preDist :=
            h_ws.weakTau_pre.witness_run
          rw [PMF.pure_bind] at h_run
          rw [← h_run]
          have h_lb : σ_pre.next ⟨s_pre, Seq.nil⟩ none ≤ (σ_pre.run n s_pre) s_pre :=
            σ_pre.run_apply_self_ge_next_none s_pre n
          intro h_eq
          apply h_sub_P
          have h_ub : σ_pre.next ⟨s_pre, Seq.nil⟩ none ≤ 0 := h_eq ▸ h_lb
          exact le_antisymm h_ub bot_le
        have h_kstep := h_ws.hyperStep_mid.kernel_step s_pre h_s_pre_in_preDist μ_l h_μ_l_supp
        rcases h_kstep with h_step | ⟨h_int_l_pe, _⟩
        · rw [h_l_eq, h_μ_eq]; exact h_step
        · exact absurd h_int_l_pe h_int
      · -- σ_pre emits some (l_pre, μ_pre): d = PMF.pure (l_pre, μ_pre).
        simp only [Option.elim_some] at h_sub_inner
        have h_sub_supp :
            some (l_pre, μ_pre) ∈ (h_ws.weakTau_pre.witness.next ⟨s_pre, Seq.nil⟩).support :=
          h_sub_P
        have h_d_eq : d = PMF.pure (l_pre, μ_pre) := by
          by_contra h_ne
          apply h_sub_inner
          rw [PMF.pure_apply, if_neg]
          intro h_eq
          apply h_ne
          injection h_eq
        rw [h_d_eq, PMF.mem_support_iff, PMF.pure_apply] at h_d_supp
        have h_pair_eq : (l, μ) = (l_pre, μ_pre) := by
          by_contra h_ne
          apply h_d_supp; rw [if_neg h_ne]
        have h_σ_pre_valid : sys.step s_pre l_pre μ_pre :=
          h_ws.weakTau_pre.witness.valid ⟨s_pre, Seq.nil⟩ 0 s_pre
            (show (Seq.nil : Seq (Label × State)).TerminatedAt 0 from
              Stream'.Seq.terminatedAt_nil)
            rfl l_pre μ_pre h_sub_supp
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_pair_eq
        exact h_σ_pre_valid

/-- **Reaching invariant**: positive reaching probability at `(e_w, e)`
implies (a) `e_w` terminates and (b) `e_w.endState = e.endState`. The
endState-equality is enforced explicitly in the definition of `reachProb`
(step body checks `e'.endState = last_step.2`) and at the base (`e.init =
e_w.init ∧ e.trans = Seq.nil`).

This lemma is **provable in principle** under the corrected `reachProb`
definition: part (a) follows from the outer `if` in `reachProb` (proven
below); part (b) follows by induction on `e_w.trans.toList`, using
`List.reverseRecOn_nil` (base case) and `List.reverseRecOn_concat` (step
case). The full proof has been deferred due to dependent-type entanglement
between `Nat.find h_term`, `AlterSeq.endState`, and the `reverseRecOn`
motive — a clean discharge requires either custom congr lemmas or
intermediate helper lemmas about `endState ⟨init, Seq.ofList _⟩`. -/
private lemma reachProb_invariant
    {sys : LabelledSystem State Label}
    {pe' : ProbabilisticExecution sys^w.toSystem}
    (e_w e : AlterSeq State Label)
    (h_e_term : e.trans.Terminates)
    (h_reach : reachProb sys pe' e_w e ≠ 0) :
    ∃ (h_e_w_term : e_w.trans.Terminates),
      e_w.endState h_e_w_term = e.endState h_e_term := by
  -- (a) e_w.trans.Terminates: from the outer `if` in reachProb.
  have h_e_w_term : e_w.trans.Terminates := by
    by_contra h_neg
    apply h_reach
    unfold reachProb
    exact dif_neg h_neg
  refine ⟨h_e_w_term, ?_⟩
  -- (b) endState equality. Unfold `reachProb` and case-split on whether
  -- the trans-list is empty.
  -- We extract the relevant guarded equation from `h_reach` using the
  -- structural decomposition of `e_w.trans` via `Stream'.Seq.exists_split_last`.
  -- Rewrite `h_reach` to expose the `reverseRecOn` body.
  have h_reach' : (open Classical in
      (e_w.trans.toList h_e_w_term).reverseRecOn
        (motive := fun _ => AlterSeq State Label → ENNReal)
        (fun e' =>
          if e_w.init = e'.init ∧ e'.trans = Seq.nil then
            pe'.initState e_w.init
          else 0)
        (fun trans_prev last_step ih_function e' =>
          if h_e'_term : e'.trans.Terminates then
            if e'.endState h_e'_term = last_step.2 then
              let e_w_prev : AlterSeq State Label :=
                ⟨e_w.init, Seq.ofList trans_prev⟩
              ∑' e_prev : AlterSeq State Label,
                ih_function e_prev *
                  oneIterTransitionProb sys pe' e_w_prev last_step.1 e_prev e'
            else 0
          else 0)
        e) ≠ 0 := by
    intro h_zero
    apply h_reach
    unfold reachProb
    rw [dif_pos h_e_w_term]
    exact h_zero
  -- Case split on whether the trans-list is empty.
  by_cases h_empty : e_w.trans.toList h_e_w_term = []
  · -- Base case: e_w.trans.toList = []
    rw [h_empty, List.reverseRecOn_nil] at h_reach'
    -- h_reach' : (if e_w.init = e.init ∧ e.trans = Seq.nil then ... else 0) ≠ 0
    by_cases h_cond : e_w.init = e.init ∧ e.trans = Seq.nil
    · -- Both inits match and e.trans = nil; need e_w.trans = nil too.
      obtain ⟨h_init_eq, h_e_nil⟩ := h_cond
      -- e_w.trans.toList = [] ⟹ e_w.trans = Seq.nil via ofList_toList.
      have h_e_w_nil : e_w.trans = Seq.nil := by
        have := Stream'.Seq.ofList_toList e_w.trans h_e_w_term
        rw [h_empty] at this
        exact this.symm
      -- Both endStates collapse to inits.
      rw [AlterSeq.endState_of_trans_nil e_w h_e_w_nil h_e_w_term,
          AlterSeq.endState_of_trans_nil e h_e_nil h_e_term]
      exact h_init_eq
    · -- Contradiction: reachProb reduces to 0.
      rw [if_neg h_cond] at h_reach'
      exact absurd rfl h_reach'
  · -- Step case: e_w.trans.toList = previous_list ++ [last_step].
    obtain ⟨previous, last_step, h_prev_term, h_e_w_struct,
            h_prev_toList, h_last_eq⟩ :=
      Stream'.Seq.exists_split_last e_w.trans h_e_w_term h_empty
    -- previous.toList h_prev_term = (e_w.trans.toList h_e_w_term).dropLast
    -- and e_w.trans = previous.append (cons last_step nil).
    -- Rewrite h_reach' using h_prev_toList to expose the concat structure.
    have h_concat : e_w.trans.toList h_e_w_term =
        previous.toList h_prev_term ++ [last_step] := by
      rw [h_prev_toList, h_last_eq]
      exact (List.dropLast_append_getLast h_empty).symm
    rw [h_concat, List.reverseRecOn_concat] at h_reach'
    -- Now h_reach' is a guarded expression where the guard ensures
    -- e.endState h_e_term = last_step.2.
    by_cases h_e_term' : e.trans.Terminates
    · rw [dif_pos h_e_term'] at h_reach'
      by_cases h_end_eq : e.endState h_e_term' = last_step.2
      · rw [if_pos h_end_eq] at h_reach'
        -- We have e.endState = last_step.2. Need e_w.endState = last_step.2 too.
        -- Use h_e_w_struct: e_w.trans = previous.append (cons last_step nil).
        have h_e_w_end : e_w.endState h_e_w_term = last_step.2 := by
          -- Cases e_w to destructure init and trans.
          obtain ⟨ew_init, ew_trans⟩ := e_w
          -- h_e_w_struct : ew_trans = previous.append (cons last_step nil)
          subst h_e_w_struct
          -- Now use endState_append_singleton.
          -- endState_append_singleton takes h : previous.Terminates,
          -- returns endState of ⟨init, append⟩ with the canonical proof.
          -- We have h_e_w_term : (append).Terminates; need to align proofs.
          have h_canon :=
            AlterSeq.endState_append_singleton
              ({init := ew_init, trans := previous} : AlterSeq State Label)
              h_prev_term last_step.1 last_step.2
          -- Two Terminates proofs for the same Seq are proof-irrelevant
          -- (Terminates is a Prop), so the endStates are equal.
          convert h_canon
        rw [h_e_w_end]
        -- Goal: last_step.2 = e.endState h_e_term
        -- We have h_end_eq : e.endState h_e_term' = last_step.2 and
        -- proof-irrelevance gives h_e_term' = h_e_term.
        rw [show h_e_term = h_e_term' from rfl]
        exact h_end_eq.symm
      · rw [if_neg h_end_eq] at h_reach'
        exact absurd rfl h_reach'
    · rw [dif_neg h_e_term'] at h_reach'
      exact absurd rfl h_reach'

/-- **`tsum` over `Option α` splits into the `none` summand and the `some`-sum.**
Mirror of `tsum_list_split_head_tail` for `Option`. -/
private lemma tsum_option_split_none_some {α : Type} (f : Option α → ENNReal) :
    ∑' o : Option α, f o = f none + ∑' a : α, f (some a) := by
  rw [← (Equiv.optionEquivSumPUnit.{0, _} α).symm.tsum_eq f]
  rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
  rw [add_comm]
  congr 1
  rw [tsum_eq_single (b := (⟨⟩ : PUnit))]
  · rfl
  · rintro ⟨⟩ h; exact (h rfl).elim

/-! ### First-reach mass and trap-corrected normalisation

The previous `pe_of_weak` normalised by `totalMass`, the joint *escape*
probability at observed `e`. That silently conditioned out the
infinite-stutter mass at `e` and redistributed it across the escape
outcomes — incorrect even when each individual stutter probability is
`< 1`, because the infinite product of stutter probabilities can
converge to a positive number.

`FirstReach e` is the *first-visit reach mass*: the joint probability the
algorithm ever has `e` as a prefix. Mathematically `FirstReach e =
(pe_of_weak …).probOf e`. We give it an independent (non-circular)
recursion on `e.trans.toList`:

* base `e.trans = nil`: `FirstReach = pe'.initState e.init`;
* step `e = e_prev ++ [(l_last, s_last)]`:
  `FirstReach e = ∑ μ, jointUnnorm e_prev (some (l_last, μ)) · μ s_last`
  (the per-`(l_last, s_last)` sys-step kernel mass at the shorter prefix
  `e_prev`, which depends only on `pe'`-side machinery).

The trap-mass at `e` is `FirstReach e − totalMass e`; it equals the joint
mass of trajectories that reach `e` and then enter an infinite stutter
without ever escaping. The corrected scheduler routes this mass to
`none` (halt), so the coupling conserves mass on both sides. -/

/-- **First-reach (cylinder) mass at `e`.** See the section docstring. -/
private noncomputable def FirstReach
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e : AlterSeq State Label) : ENNReal :=
  open Classical in
  if h_term : e.trans.Terminates then
    (e.trans.toList h_term).reverseRecOn
      (motive := fun _ => ENNReal)
      (pe'.initState e.init)
      (fun trans_prev last_step _ih =>
        let e_prev : AlterSeq State Label :=
          ⟨e.init, Seq.ofList trans_prev⟩
        ∑' μ : PMF State,
          jointUnnorm sys pe' e_prev (some (last_step.1, μ)) * μ last_step.2)
  else 0

/-- **Escape mass is bounded by first-reach mass**: `totalMass e ≤ FirstReach e`.

The gap `FirstReach e − totalMass e` is the joint mass of trajectories
that reach `e` and never escape (the infinite-stutter event at `e`).
The corrected scheduler in `pe_of_weak` routes that mass to `none`.
Deferred. -/
private lemma totalMass_le_FirstReach
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e : AlterSeq State Label) :
    totalMass sys pe' e ≤ FirstReach sys pe' e := by
  sorry

/-- **`FirstReach` on an execution with empty trans collapses to the initial
mass.** Mirrors `probOf_nil`. -/
private lemma FirstReach_nil
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) (s : State) :
    FirstReach sys pe' ⟨s, Seq.nil⟩ = pe'.initState s := by
  unfold FirstReach
  rw [dif_pos Stream'.Seq.terminates_nil, Stream'.Seq.toList_nil,
      List.reverseRecOn_nil]

/-- **Cons-end factorisation for `FirstReach`** (mirrors `probOf_append_singleton`).
Appending a single transition `last` at the end rewrites `FirstReach` as the
per-`μ` sys-step kernel mass at the truncated prefix. -/
private lemma FirstReach_append_singleton
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (s : State) (sq : Seq (Label × State)) (h_sq : sq.Terminates)
    (last : Label × State)
    (h_app : (sq.append (Seq.cons last Seq.nil)).Terminates) :
    FirstReach sys pe' ⟨s, sq.append (Seq.cons last Seq.nil)⟩ =
      ∑' μ : PMF State,
        jointUnnorm sys pe' ⟨s, sq⟩ (some (last.1, μ)) * μ last.2 := by
  unfold FirstReach
  rw [dif_pos h_app]
  have h_singleton_term : (Seq.cons last Seq.nil : Seq (Label × State)).Terminates :=
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
  have h_toList : (sq.append (Seq.cons last Seq.nil)).toList h_app =
      sq.toList h_sq ++ [last] := by
    rw [Stream'.Seq.toList_append sq (Seq.cons last Seq.nil) h_sq h_singleton_term h_app]
    congr 1
    rw [Stream'.Seq.toList_cons]
    simp [Stream'.Seq.toList_nil]
  rw [show (⟨s, sq.append (Seq.cons last Seq.nil)⟩ : AlterSeq State Label).trans.toList h_app
        = sq.toList h_sq ++ [last] from h_toList]
  rw [List.reverseRecOn_concat]
  -- `Seq.ofList (sq.toList h_sq) = sq`, and outer init `s` matches `e.init`.
  rw [Stream'.Seq.ofList_toList sq h_sq]

/-- **Trap-corrected unnormalised mass** at observed `e`. Differs from
`jointUnnorm` only at `none`, where the infinite-stutter trap mass
`FirstReach e − totalMass e` is added. Used to build `pe_of_weak`'s
marginal scheduler. -/
private noncomputable def correctedMass
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e : AlterSeq State Label) (opt : Option (Label × PMF State)) : ENNReal :=
  jointUnnorm sys pe' e opt +
    opt.elim (FirstReach sys pe' e - totalMass sys pe' e) (fun _ => 0)

/-- **`correctedMass` at a `some`-emission is just `jointUnnorm`** —
the trap correction only touches the `none` summand. -/
private lemma correctedMass_some
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e : AlterSeq State Label) (lμ : Label × PMF State) :
    correctedMass sys pe' e (some lμ) = jointUnnorm sys pe' e (some lμ) := by
  unfold correctedMass; simp

/-- **The corrected mass tsums to `FirstReach`**: the trap contribution
`FirstReach − totalMass` plus the escape mass `totalMass` recover the
full first-reach mass. -/
private lemma correctedMass_tsum_eq_FirstReach
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e : AlterSeq State Label) :
    (∑' opt, correctedMass sys pe' e opt) = FirstReach sys pe' e := by
  unfold correctedMass
  rw [ENNReal.tsum_add]
  have h_tm : (∑' opt, jointUnnorm sys pe' e opt) = totalMass sys pe' e := rfl
  have h_trap :
      (∑' opt : Option (Label × PMF State),
        opt.elim (FirstReach sys pe' e - totalMass sys pe' e) (fun _ => 0)) =
        FirstReach sys pe' e - totalMass sys pe' e := by
    rw [tsum_option_split_none_some]; simp
  rw [h_tm, h_trap, add_comm]
  exact tsub_add_cancel_of_le (totalMass_le_FirstReach sys pe' e)

/-- **Witness pe : ProbabilisticExecution sys.toSystem** constructed
algorithmically from `pe' : ProbabilisticExecution sys^w.toSystem`.

At each observed `e`, the scheduler is the *trap-corrected* marginal of the
joint algorithm's next event conditional on reaching `e`:

* `next e (some (l, μ)) = jointUnnorm e (some (l, μ)) / FirstReach e`;
* `next e (none)        = (jointUnnorm e (none) + trap(e)) / FirstReach e`,

with `trap(e) := FirstReach e − totalMass e` the joint mass of
infinite-stutter trajectories at `e`. The corners `FirstReach e ∈ {0, ⊤}`
fall back to `PMF.pure none` — the first is a vacuous corner with no joint
mass at `e`, and the second (`FirstReach = ⊤`) is precluded by
`FirstReach_ne_top` proven later (the 3-way split avoids a circular
dependency between `pe_of_weak`'s definition and `FirstReach_ne_top`'s
proof, which uses `FirstReach_eq_probOf`). -/
private noncomputable def pe_of_weak (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) :
    ProbabilisticExecution sys.toSystem where
  initState := pe'.initState
  scheduler :=
    { next := fun e =>
        open Classical in
        if h_fr0 : FirstReach sys pe' e = 0 then
          PMF.pure none
        else if h_fr_top : FirstReach sys pe' e = ⊤ then
          PMF.pure none
        else
          PMF.normalize (correctedMass sys pe' e)
            ((correctedMass_tsum_eq_FirstReach sys pe' e).symm ▸ h_fr0)
            ((correctedMass_tsum_eq_FirstReach sys pe' e).symm ▸ h_fr_top)
      valid := by
        intro e n s _h_term _h_state l μ h_supp
        classical
        change some (l, μ) ∈
          ((open Classical in
            if h_fr0 : FirstReach sys pe' e = 0 then
              PMF.pure none
            else if h_fr_top : FirstReach sys pe' e = ⊤ then
              PMF.pure none
            else
              PMF.normalize (correctedMass sys pe' e)
                ((correctedMass_tsum_eq_FirstReach sys pe' e).symm ▸ h_fr0)
                ((correctedMass_tsum_eq_FirstReach sys pe' e).symm ▸ h_fr_top))).support
            at h_supp
        split_ifs at h_supp with h_fr0 h_fr_top
        · -- FirstReach = 0 fallback: support = {none}.
          rw [PMF.support_pure] at h_supp
          exact absurd h_supp (by simp)
        · -- FirstReach = ⊤ fallback: support = {none}.
          rw [PMF.support_pure] at h_supp
          exact absurd h_supp (by simp)
        · -- Main case: support comes from `PMF.normalize correctedMass`.
          rw [PMF.mem_support_iff, PMF.normalize_apply] at h_supp
          rw [correctedMass_some] at h_supp
          have h_ju_ne_zero : jointUnnorm sys pe' e (some (l, μ)) ≠ 0 := by
            intro h_eq
            apply h_supp
            rw [h_eq, zero_mul]
          -- Unfold jointUnnorm at `some (l, μ)`.
          change ∑' e_w : AlterSeq State Label,
              reachProb sys pe' e_w e *
                ∑' d : PMF (Label × PMF State),
                  iterOutcome sys pe' e_w e (.visible d) * d (l, μ) ≠ 0
            at h_ju_ne_zero
          -- Extract a positive e_w, then a positive d.
          rw [Ne, ENNReal.tsum_eq_zero] at h_ju_ne_zero
          push Not at h_ju_ne_zero
          obtain ⟨e_w, h_e_w_pos⟩ := h_ju_ne_zero
          rw [mul_ne_zero_iff] at h_e_w_pos
          obtain ⟨h_reach_pos, h_d_sum_pos⟩ := h_e_w_pos
          rw [Ne, ENNReal.tsum_eq_zero] at h_d_sum_pos
          push Not at h_d_sum_pos
          obtain ⟨d, h_d_pair_pos⟩ := h_d_sum_pos
          rw [mul_ne_zero_iff] at h_d_pair_pos
          obtain ⟨h_iter_pos, h_d_lμ_pos⟩ := h_d_pair_pos
          have h_d_supp : (l, μ) ∈ d.support := h_d_lμ_pos
          -- Get the algorithm's endState invariant: e_w.endState = e.endState.
          have h_e_term : e.trans.Terminates := ⟨n, _h_term⟩
          obtain ⟨h_e_w_term, h_endStates_eq⟩ :=
            reachProb_invariant e_w e h_e_term h_reach_pos
          -- Apply the iterOutcome step-validity lemma.
          have h_step_e_w : sys.step (e_w.endState h_e_w_term) l μ :=
            iterOutcome_visible_implies_step e_w e h_e_w_term d h_iter_pos l μ h_d_supp
          -- The validity goal is `sys.step s l μ`. We need `s = e.endState`.
          rw [h_endStates_eq] at h_step_e_w
          -- From `_h_term : e.trans.TerminatedAt n` and `_h_state : e.stateAt n = some s`,
          -- and the fact that `e.trans.Terminates`, we have `s = e.endState`.
          have h_s_eq : s = e.endState h_e_term := by
            have h_find : Nat.find h_e_term = n := by
              apply le_antisymm (Nat.find_le _h_term)
              by_contra h_lt
              push Not at h_lt
              -- Nat.find < n. Then trans is terminated at Nat.find < n, so
              -- get? (n-1) = none (since once terminated, stay terminated),
              -- contradicting stateAt n = some s.
              rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
              · -- n = 0 and Nat.find < 0: impossible.
                exact absurd h_lt (by omega)
              · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn_pos.ne'
                rw [hk] at _h_state
                change (e.trans.get? k).map Prod.snd = some s at _h_state
                have h_term_k : e.trans.TerminatedAt k := by
                  have : Nat.find h_e_term ≤ k := by omega
                  exact Stream'.Seq.le_stable e.trans this (Nat.find_spec h_e_term)
                change e.trans.get? k = none at h_term_k
                rw [h_term_k] at _h_state
                simp at _h_state
            have h_stateAt := AlterSeq.stateAt_find_eq_endState e h_e_term
            rw [h_find, _h_state] at h_stateAt
            exact Option.some.inj h_stateAt
          rw [h_s_eq]
          exact h_step_e_w }

/-! #### `pe_of_weak_traceProb` — corrected proof strategy

The previous decomposition (sub-lemmas A–D plus `iterHalt_tight_invariant`)
was based on a flawed `iterHalt_tight_invariant` claim and has been removed.
The corrected strategy is documented in the docstring of
`pe_of_weak_traceProb` below; the proof itself is deferred. -/

/-! ##### Main correctness lemma for `pe_of_weak`

The trace-probability under `sys` of the algorithmic witness
`pe_of_weak sys pe'` matches the trace-probability under `sys^w` of
the original `pe'`.

### Corrected proof strategy

The previous attempt decomposed the equality through a `jointHaltMass`
marginalisation chain anchored on `iterHalt_tight_invariant` — the claim
that any positive `iterOutcome … .halt` mass forces `sys^w.IsTight e_w`.
That invariant is *false*: a weak step may legitimately accumulate a
post-`τ` chain of internal transitions inside its witness, so the
`sys^w`-side history `e_w` can halt at a non-tight prefix while still
contributing to the trace-probability cylinder. The whole sub-lemma chain
has been removed; the corrected strategy below should replace it.

### 1. Set alignment (definitional)

Both `sys.trace = sys^w.trace` and `sys.IsTight = sys^w.IsTight` hold by
`rfl`, because the weak closure shares its `internal` predicate with `sys`
and `trace`/`IsTight` are defined in terms of `internal` only. So the two
`traceProb` tsums genuinely range over the *same* subtype
`T_τ := {e | e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e}`
of `AlterSeq State Label`. No subtype reindexing is required at this level;
only the `probOf`-weight identity needs work.

### 2. `probOf` is a prefix-probability, not a halt-probability

`ProbabilisticExecution.probOf e h_term` evaluates to
`init * ∏ kernel(prefix_i, transition_i)` over `e.trans.toList`. The
scheduler's `none`-emission mass never appears in this product. Therefore
`(pe_of_weak …).probOf e` measures the probability that `pe_of_weak`'s
trajectory *passes through* the prefix `e`, regardless of whether/where
that trajectory eventually halts. Equivalently, it is the *cylinder
probability* of the cone `{trajectories : prefix-of-trajectory = e}`.

The user's "non-tight halts are invisible" insight is therefore stronger
than it first appears: `pe_of_weak` is allowed to halt at non-tight `e'`
*later* than the tight prefix `e ∈ T_τ` we are summing — that does NOT
diminish the LHS contribution at `e`, because the contribution is the
prefix-probability of `e`, not a halt-probability at `e`.

### 3. The two time scales of the joint algorithm

The joint coupling has two distinct time scales:

* **Outer-iteration time** (indexed `n`): one tick per `pe'` emission.
  Between iterations, the joint state `(e_w_n, e_n)` is a *boundary
  state*: `e_w_n` is the `sys^w`-prefix after `n` `pe'`-emissions, and
  `e_n` is the cumulative `sys`-prefix after the corresponding `n`
  witness chains have been appended.
* **Inner sys-step time** (indexed within a single outer iteration):
  while the witness sub-loop runs, `e` grows label-by-label through the
  weak-step chain (pre-τ + visible sys-step + post-τ), while `e_w` stays
  frozen at its pre-iteration value until the iteration ends.

**Trace coupling holds exactly at outer-iteration boundaries**, i.e.
`sys^w.trace e_w_n = sys.trace e_n` for every `n`. Inside an iteration,
the labels in `e` may transiently overrun those in `e_w` — the
external sys-step in the chain raises `sys.trace e` by one external
label *before* the boundary update raises `sys^w.trace e_w` to match.

### 4. Locating tight visits

A tight `sys`-prefix `e` (with last label external, say `l`) is visited
by `pe_of_weak` *inside* the outer iteration whose `pe'`-emission was
`(l, μ)`: specifically, at the inner sys-step right after the witness
chain's visible `l`-step and before any post-τ extension. At that
moment, `e_w` is its *pre-iteration* value `e_w_pre` and satisfies
`sys^w.trace e_w_pre ++ [l] = sys.trace e = τ`.

This is the technical bookkeeping that the previous strategy elided. The
appropriate joint quantity for the proof is *not* the boundary mass
`reachProb(e_w, e)` (which only sees post-iteration states), but a
finer quantity tracking *which tight visit* of `pe_of_weak`'s trajectory
we are at:

```
jointTight(e_w_pre, e) :=
    "probability the joint algorithm visits the inner-iteration state
     (e_w_pre, e) where e is tight, e_w_pre is the e_w at the START
     of the iteration that produced e's last external label"
```

By the algorithm's construction (each iteration appends one weak-step
emission to `e_w` after its full chain is sampled), `jointTight`
factorises as `reachProb(e_w_pre, e_prev) * P[next outer-iteration
produces, on sys-side, the chain extending e_prev to e]`, where `e_prev`
is the boundary `sys`-prefix just before this iteration. The "P[…]"
factor in the bracket sums `pe'.scheduler.next e_w_pre (some (l, μ))` and
the witness sub-chain probability over all `μ` and chain decompositions.

### 5. The marginal identities

With `jointTight` so defined, the two marginals are:

* `∑' e_w_pre, jointTight(e_w_pre, e) = (pe_of_weak …).probOf e`
  for every `e ∈ T_τ`. This is sub-lemma A's correct restatement: each
  tight `e` is reached at exactly one inner-iteration moment in any
  joint trajectory, and the marginal over hidden `e_w_pre` recovers
  `pe_of_weak`'s prefix-probability of `e`. Crucially, `e_w_pre`
  ranges over *all* terminating prefixes (no tightness filter), because
  it represents a pre-iteration `sys^w`-state and that state can be
  tight or not depending on whether the previous iteration ended on an
  external or internal label.

* `∑' e ∈ T_τ, jointTight(e_w_pre, e) = (pe'-prefix-probability of
  `e_w_pre ++ [l_next]` for some external next-emission)`
  for every `e_w_pre`. This is sub-lemma B's correct restatement: tight
  visits of `pe_of_weak` correspond to outer iterations whose
  `pe'`-emission was external. Summing those visits over `e ∈ T_τ`
  recovers exactly the `pe'`-mass on *external-emission* extensions of
  `e_w_pre`.

### 6. The Fubini + cancellation argument

Now combine the marginals:

```
LHS = ∑' e ∈ T_τ, (pe_of_weak).probOf e
    = ∑' e ∈ T_τ, ∑' e_w_pre, jointTight(e_w_pre, e)        -- by A
    = ∑' e_w_pre, ∑' e ∈ T_τ, jointTight(e_w_pre, e)        -- Fubini
    = ∑' e_w_pre, P[pe' extends e_w_pre by an external emission        -- by B
                    leading to a τ-trace tight prefix on sys-side]
    = pe'-probability of producing a trajectory whose trace ⊇ τ via
      an external emission at SOME outer iteration.

RHS = sys^w.traceProb pe' τ
    = ∑' e_w ∈ T_τ, pe'.probOf e_w
    = pe'-probability of producing a tight sys^w-prefix with trace τ.
```

These two probabilities are equal because every `pe'`-trajectory that
produces an external-emission sequence with τ as a prefix passes through
a *unique* tight sys^w-prefix with trace τ (at the moment the τ-th
external is emitted; the prefix at that moment is by definition tight
because its last label is external).

That bijection between "first external-emission producing τ" events on
the `pe'` side and "tight τ-prefix" events on the `pe_of_weak` side is
what closes the proof. The tightness asymmetry of §3 (post-τ chain on
sys-side need not be tight while e_w is) is resolved by the
prefix-probability interpretation of §2: even when pe_of_weak's
trajectory subsequently extends `e` into a non-tight post-τ tail, its
`probOf e` for the earlier *tight* visit is unaffected, and that
earlier visit is the unique contributing point.

### 7. Implementation roadmap

The proof in Lean is expected to proceed by:

1. Define `jointTight` (or an equivalent inner-iteration joint mass)
   directly, alongside helper lemmas mirroring §3's two-time-scale
   analysis.
2. Prove the two marginal identities (§5) — these are induction on
   `e.trans.toList` / `e_w.trans.toList`, analogous to the (failed)
   sub-lemmas A and B but now with the corrected joint quantity.
3. Apply Fubini (sub-lemma C's role, via `ENNReal.tsum_comm`).
4. Establish the bijection in §6 between tight-`τ` prefixes on the
   `pe_of_weak` side and external-emission events on the `pe'` side.
   This is a cylinder-decomposition argument, structurally similar to
   the `IsTight` cylinder analysis used in defining `traceProb`.

The argument is conservation of mass along the trace cylinder under a
measure-preserving coupling. The previous strategy failed by trying to
pin the coupling to *boundary* joint states only; the correct coupling
lives at the finer inner-iteration scale where tight visits actually
occur.

Deferred. -/

/-! ##### Joint inner-iteration mass (`jointTight`) and marginal identities

The `pe_of_weak_traceProb` proof is decomposed via the joint
inner-iteration mass `jointTight (e_w_pre, e)`, where:

* `e` is a *tight* terminating `sys`-prefix with trace `τ` (so its last
  label, if any, is external);
* `e_w_pre` is the `sys^w`-side history at the *start* of the outer
  iteration during which `pe_of_weak` produced `e`'s last external
  label.

The mass factorises (intuitively) as
`reachProb (e_w_pre, e_prev) * P[next outer-iteration of pe' at e_w_pre
emits an external (l_last, μ) whose witness chain extends e_prev to e
*through and including the visible sys-step at l_last*, with no post-τ
extension]`, where `e_prev` is `e` with its last transition removed.
The `e.trans = Seq.nil` (empty tight prefix) case is handled separately
as a pure initial-state marginal.

Concretely we use the simple presentation
`jointTight (e_w_pre, e) := reachProb (e_w_pre, e)` in the empty case
and a re-use of the existing `oneIterTransitionProb` factor in the
non-empty case, both restricted to the data appropriate to a *tight*
visit. The exact factor is encapsulated in `tightStepFactor`. -/

/-- **Inner-iteration "tight step" factor** for a tight non-empty `e`:
given the splitting `e = e_prev ++ [(l_last, s_last)]` (the final
transition is the external visible sys-step in the outer iteration),
this is the conditional probability that the iteration starts from
the `sys^w`-side prefix `e_w_pre` and produces exactly the chain
extending `e_prev` to `e` *up to and including* the visible
`l_last`-step (no post-τ continuation). -/
private noncomputable def tightStepFactor
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_pre : AlterSeq State Label) (l_last : Label)
    (e_iter_start e : AlterSeq State Label) : ENNReal :=
  -- **Through-`l_last` iteration probability** from iteration-start
  -- `e_iter_start` to `e`.
  --
  -- Structurally mirrors `oneIterTransitionProb`'s external branch
  -- (`internal l_last` contributes 0, since a tight visit requires a
  -- visible external emission). We omit any σ_post factor: the tight
  -- visit observation is at the moment right after the visible sys-step,
  -- before σ_post runs; integrating over σ_post's future contributes a
  -- factor of 1 by total probability. Together with the requirement that
  -- the chain extending `e_iter_start` to `e` ends with the visible
  -- `(l_last, _)`-step and that all earlier chain entries are internal,
  -- this pins the witness to perform exactly one external-`l_last`
  -- emission at the moment of the tight visit.
  open Classical in
  if h_ewp : e_w_pre.trans.Terminates then
  if h_es : e_iter_start.trans.Terminates then
  if h_e : e.trans.Terminates then
    let s_pre : State := e_w_pre.endState h_ewp
    let e_iter_start_list : List (Label × State) := e_iter_start.trans.toList h_es
    let e_list : List (Label × State) := e.trans.toList h_e
    if h_prefix : e_iter_start.init = e.init ∧
                  e_list.take e_iter_start_list.length = e_iter_start_list then
      let chain : List (Label × State) := e_list.drop e_iter_start_list.length
      ∑' μ : PMF State,
        pe'.scheduler.next e_w_pre (some (l_last, μ)) *
        (if h_supp : some (l_last, μ) ∈ (pe'.scheduler.next e_w_pre).support then
          have h_sw : sys^w.step s_pre l_last μ :=
            pe'.scheduler.valid e_w_pre (Nat.find h_ewp) s_pre
              (Nat.find_spec h_ewp)
              (AlterSeq.stateAt_find_eq_endState e_w_pre h_ewp)
              l_last μ h_supp
          if h_int : sys.internal l_last then
            -- Tight visit requires an external emission; internal contributes 0.
            0
          else
            have h_ws : weakStep sys (PMF.pure s_pre) l_last μ := by
              rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
              · exact absurd h_int' h_int
              · exact h
            let σ_pre := h_ws.weakTau_pre.witness
            let σ_post := h_ws.weakTau_post.witness
            let p := h_ws.hyperStep_mid.kernel
            -- Require chain ends with `(l_last, _)` and `chain.dropLast`
            -- is all-internal, with `σ_post`-halt at the last state.
            match chain.getLast? with
            | none => (0 : ENNReal)
            | some last_pair =>
              haveI : Decidable (last_pair.1 = l_last) := Classical.dec _
              if last_pair.1 = l_last then
                let chain_pre := chain.dropLast
                haveI : Decidable (∀ pair ∈ chain_pre, sys.internal pair.1) :=
                  Classical.dec _
                if (∀ pair ∈ chain_pre, sys.internal pair.1) then
                  let s_chain_last : State := last_pair.2
                  let s_mid_pre : State :=
                    (chain_pre.getLast?.map Prod.snd).getD s_pre
                  -- σ_post factor omitted: the tight visit observation
                  -- is at the moment right after the visible sys-step;
                  -- σ_post hasn't run yet. Integrating over σ_post's
                  -- future contributes 1 by total probability.
                  let _ := σ_post
                  chainProb σ_pre ⟨s_pre, Seq.nil⟩ chain_pre *
                    (∑' μ_l : PMF State, p s_mid_pre μ_l * μ_l s_chain_last)
                else 0
              else 0
        else 0)
    else 0
  else 0
  else 0
  else 0

/-- **Joint inner-iteration mass** `jointTight (e_w_pre, e)`.

Cases:

* `e.trans = Seq.nil`: `jointTight = reachProb (e_w_pre, e)` (i.e.
  `pe'.initState e_w.init` when `e_w_pre = e` and `e_w_pre.trans = nil`,
  zero otherwise; the initial-state marginal).
* `e.trans = trans_prev ++ [(l_last, s_last)]` with `l_last` external
  (the tight non-empty case): `jointTight =
  reachProb (e_w_pre, e_prev) * tightStepFactor (e_w_pre, l_last, e_prev, e)`.
* All other cases (non-terminating `e`, internal `l_last`,
  non-tight `e`): zero.

This is the per-`(e_w_pre, e)` joint mass whose marginals yield the
two identities in §5 of the strategy docstring. -/
private noncomputable def jointTight
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_pre e : AlterSeq State Label) : ENNReal :=
  open Classical in
  if h_e_term : e.trans.Terminates then
    (e.trans.toList h_e_term).reverseRecOn
      (motive := fun _ => ENNReal)
      -- Base case: `e.trans = nil`. Pin to the initial-state marginal
      -- `pe'.initState e_w_pre.init` exactly when `e_w_pre` is the
      -- initial joint state (`e_w_pre.init = e.init` and
      -- `e_w_pre.trans = Seq.nil`); otherwise contribute 0. This is the
      -- key correction over `reachProb`, which would also add stutter
      -- mass over arbitrary `e_w_pre`.
      (if e_w_pre.init = e.init ∧ e_w_pre.trans = Seq.nil then
        pe'.initState e_w_pre.init
       else 0)
      -- Step case: `e.trans = trans_prev ++ [(l_last, s_last)]`. Tight
      -- iff `l_last` is external. Sum over all *iteration-start* prefixes
      -- `e_iter_start` of `e` (the prefix at which the outer iteration
      -- producing `l_last` began): for each, the joint probability is
      --   reachProb (e_w_pre, e_iter_start)
      --     · tightStepFactor (e_w_pre, l_last, e_iter_start, e).
      -- The `tightStepFactor` correctly pins the iteration to extend
      -- `e_iter_start` to `e` through `l_last` with no post-τ
      -- continuation.
      (fun _trans_prev last_step _ih =>
        if sys.internal last_step.1 then 0
        else
          ∑' e_iter_start : AlterSeq State Label,
            reachProb sys pe' e_w_pre e_iter_start *
              tightStepFactor sys pe' e_w_pre last_step.1 e_iter_start e)
  else 0

/-- **Marginal identity B** (the corrected sub-lemma B from §5):
for any pre-iteration `sys^w`-history `e_w_pre`, summing `jointTight`
over tight `τ`-prefixes `e` recovers the `pe'`-mass of trajectories
that extend `e_w_pre` by an external emission whose visible sys-step
completes the trace cylinder of `τ`.

The RHS here is the `pe'`-side cylinder cumulator that equals, after
summation over `e_w_pre`, exactly `sys^w.traceProb pe' τ`. This is
encapsulated as the abstract quantity `extCylinderMass`, and the
matching identity is `extCylinderMass_sum_eq_traceProb` below. -/
private noncomputable def extCylinderMass
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (τ : Seq Label) (e_w_pre : AlterSeq State Label) : ENNReal :=
  ∑' e : {e : AlterSeq State Label //
            e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e},
    jointTight sys pe' e_w_pre e.1

private lemma jointTight_marginal_B
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (τ : Seq Label) (e_w_pre : AlterSeq State Label) :
    (∑' e : {e : AlterSeq State Label //
              e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e},
      jointTight sys pe' e_w_pre e.1) =
      extCylinderMass sys pe' τ e_w_pre := rfl

/-- **Cylinder bijection / mass-conservation identity** (§6 of the
strategy docstring). The total `pe'`-side mass of "first external
emission completing trace `τ`" events equals `sys^w.traceProb pe' τ`.

Intuition: every `pe'`-trajectory whose first `|τ|` external emissions
spell out `τ` passes through a *unique* tight `sys^w`-prefix with trace
`τ` (the prefix at the moment of the `|τ|`-th external emission). The
sum of the joint inner-iteration masses over the hidden pre-iteration
`e_w_pre` therefore equals `sys^w.traceProb pe' τ`.

### Status of the proof (2026-06-04, post-rewrite)

The earlier 2026-06-04 bug analysis identified three overcounting
artefacts in the original `jointTight` / `tightStepFactor` (stutter
mass in the `nil` base case, missing sum over iteration-start
prefixes in the step case, and unrestricted post-τ in
`tightStepFactor`). All three have now been addressed:

* **`jointTight` base case.** Pins to `pe'.initState e_w_pre.init`
  exactly when `e_w_pre = ⟨e.init, Seq.nil⟩`. The stutter contributions
  are gone.
* **`jointTight` step case.** Sums over the iteration-start prefix
  `e_iter_start` (an `AlterSeq State Label`) of `e`, accounting for
  the chain `e_iter_start ⊑ e` that may include pre-`l_last`
  internal labels.
* **`tightStepFactor`.** Mirrors `oneIterTransitionProb`'s external
  branch but pins `chain.getLast = (l_last, _)` and `chain.dropLast`
  all-internal. No σ_post factor: the tight visit is observed at the
  moment right after the visible sys-step, before σ_post runs;
  integrating over σ_post's future contributes 1 by total probability.

With these in place, the `nil`-case sanity check goes through:
`jointTight e_w_pre ⟨s, Seq.nil⟩` is non-zero only at
`e_w_pre = ⟨s, Seq.nil⟩` (value `pe'.initState s`), so
`∑' e_w_pre, ∑' s, jointTight e_w_pre ⟨s, Seq.nil⟩ = ∑' s, pe'.initState s
 = sys^w.traceProb pe' Seq.nil`. The general identity is provable by
a double-tsum manipulation that telescopes the `reachProb`-by-
`tightStepFactor` product against the cons-end recursion of
`pe'.probOf`; the proof is deferred. -/
-- **Trace ≠ nil from any external label**: if `e.trans` has an
-- external label at any position, the trace of `e` is non-`nil`.
private lemma trace_ne_nil_of_external
    (ls : LabelledSystem State Label) :
    ∀ (n : ℕ) (e : AlterSeq State Label) (l : Label) (s : State),
      e.trans.get? n = some (l, s) → ¬ ls.internal l →
        ls.trace e ≠ Seq.nil := by
  intro n
  induction n with
  | zero =>
    intro e l s h_get h_ext
    have h_head : e.trans.head = some (l, s) := h_get
    cases h_destr : e.trans.destruct with
    | none =>
      have h_nil : e.trans = Seq.nil := Seq.destruct_eq_none h_destr
      rw [h_nil] at h_head
      simp [Seq.head] at h_head
    | some pair =>
      obtain ⟨⟨a₁, a₂⟩, tail'⟩ := pair
      have h_head_eq : (a₁, a₂) = (l, s) := by
        have h_head' : e.trans.head = some (a₁, a₂) := by
          rw [Seq.head_eq_destruct, h_destr]; rfl
        rw [h_head] at h_head'
        exact (Option.some.inj h_head').symm
      have h_a1 : l = a₁ := ((Prod.mk.inj h_head_eq).1).symm
      have h_a2 : s = a₂ := ((Prod.mk.inj h_head_eq).2).symm
      subst h_a1; subst h_a2
      have h_e : e.trans = Seq.cons (l, s) tail' := Seq.destruct_eq_cons h_destr
      have h_e' : e = ⟨e.init, Seq.cons (l, s) tail'⟩ := by
        cases e; cases h_e; rfl
      rw [h_e', LabelledSystem.trace_cons_external ls _ _ s tail' h_ext]
      exact Seq.cons_ne_nil
  | succ n ih =>
    intro e l s h_get h_ext
    cases h_destr : e.trans.destruct with
    | none =>
      have h_nil : e.trans = Seq.nil := Seq.destruct_eq_none h_destr
      rw [h_nil] at h_get
      simp at h_get
    | some pair =>
      obtain ⟨⟨l₀, s₀⟩, tail'⟩ := pair
      have h_e : e.trans = Seq.cons (l₀, s₀) tail' := Seq.destruct_eq_cons h_destr
      have h_e' : e = ⟨e.init, Seq.cons (l₀, s₀) tail'⟩ := by
        cases e; cases h_e; rfl
      have h_get_tail : tail'.get? n = some (l, s) := by
        rw [h_e] at h_get
        change (Seq.cons (l₀, s₀) tail').get? (n + 1) = some (l, s) at h_get
        simpa [Seq.get?_cons_succ] using h_get
      have ih' : ls.trace ⟨s₀, tail'⟩ ≠ Seq.nil :=
        ih ⟨s₀, tail'⟩ l s h_get_tail h_ext
      rw [h_e']
      by_cases h_int : ls.internal l₀
      · rw [LabelledSystem.trace_cons_internal ls _ _ s₀ tail' h_int]
        exact ih'
      · rw [LabelledSystem.trace_cons_external ls _ _ s₀ tail' h_int]
        exact Seq.cons_ne_nil

-- **Tight + empty-trace forces empty `trans`**: if a finite-trace `e`
-- under `ls` is tight and has empty trace, then its `trans` is `Seq.nil`.
private lemma trans_nil_of_tight_trace_nil
    (ls : LabelledSystem State Label) (e : AlterSeq State Label)
    (h_trace : ls.trace e = Seq.nil) (h_tight : ls.IsTight e) :
    e.trans = Seq.nil := by
  rcases h_tight with h0 | ⟨n, l, s, h_get, _h_term', h_ext⟩
  · exact Seq.terminatedAt_zero_iff.mp h0
  · exact absurd h_trace (trace_ne_nil_of_external ls n e l s h_get h_ext)

-- **Iff version**: a finite execution has empty trace and is tight
-- iff its `trans` is `Seq.nil`.
private lemma tight_trace_nil_iff
    (ls : LabelledSystem State Label) (e : AlterSeq State Label) :
    (e.trans.Terminates ∧ ls.trace e = Seq.nil ∧ ls.IsTight e) ↔
      e.trans = Seq.nil := by
  constructor
  · rintro ⟨_, h_trace, h_tight⟩
    exact trans_nil_of_tight_trace_nil ls e h_trace h_tight
  · intro h_nil
    refine ⟨?_, ?_, ?_⟩
    · rw [h_nil]; exact Seq.terminates_nil
    · unfold LabelledSystem.trace; rw [h_nil]; simp
    · left; rw [h_nil]; rfl

-- **Equiv** between `State` and the tight `nil`-trace subtype.
private noncomputable def tightNilTraceEquiv
    (ls : LabelledSystem State Label) :
    State ≃ {e : AlterSeq State Label //
              e.trans.Terminates ∧ ls.trace e = Seq.nil ∧ ls.IsTight e} where
  toFun s := ⟨⟨s, Seq.nil⟩, (tight_trace_nil_iff ls ⟨s, Seq.nil⟩).mpr rfl⟩
  invFun e := e.1.init
  left_inv _ := rfl
  right_inv e := by
    apply Subtype.ext
    have h_nil : e.1.trans = Seq.nil := (tight_trace_nil_iff ls e.1).mp e.2
    change (⟨e.1.init, Seq.nil⟩ : AlterSeq State Label) = e.1
    obtain ⟨⟨init, trans⟩, _⟩ := e
    dsimp only at h_nil ⊢
    subst h_nil
    rfl

-- **`jointTight` on `e.trans = Seq.nil`**: collapses to the
-- initial-state indicator.
private lemma jointTight_nil
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_pre : AlterSeq State Label) (s : State) :
    jointTight sys pe' e_w_pre ⟨s, Seq.nil⟩ =
      (open Classical in
       if e_w_pre.init = s ∧ e_w_pre.trans = Seq.nil then
        pe'.initState e_w_pre.init else 0) := by
  unfold jointTight
  simp only [Seq.terminates_nil, dite_true]
  rw [show (⟨s, Seq.nil⟩ : AlterSeq State Label).trans.toList Seq.terminates_nil = [] from
    Seq.toList_nil]
  rw [List.reverseRecOn_nil]

-- **`extCylinderMass` at `τ = Seq.nil`**: reduces to the initial-state
-- indicator at `e_w_pre.init`, conditional on `e_w_pre.trans = Seq.nil`.
private lemma extCylinderMass_nil
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_pre : AlterSeq State Label) :
    extCylinderMass sys pe' Seq.nil e_w_pre =
      (open Classical in
       if e_w_pre.trans = Seq.nil then pe'.initState e_w_pre.init else 0) := by
  classical
  unfold extCylinderMass
  rw [← Equiv.tsum_eq (tightNilTraceEquiv sys)]
  simp only [tightNilTraceEquiv, Equiv.coe_fn_mk]
  -- Inner sum becomes ∑' s, jointTight sys pe' e_w_pre ⟨s, Seq.nil⟩.
  simp only [jointTight_nil sys pe' e_w_pre]
  by_cases h_trans : e_w_pre.trans = Seq.nil
  · simp only [h_trans, and_true, if_true]
    rw [tsum_eq_single e_w_pre.init]
    · simp
    · intro c hc
      simp [Ne.symm hc]
  · simp [h_trans]

-- **`jointTight` step case (external)**: when `e.trans` splits as
-- `trans_prev.append (cons (l_last, s_last) nil)` with `l_last` external,
-- `jointTight` reduces to the `reachProb · tightStepFactor` sum over the
-- iteration-start prefix. This is the "step" companion of `jointTight_nil`.
private lemma jointTight_step_external
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_pre e : AlterSeq State Label) (h_e_term : e.trans.Terminates)
    (trans_prev : Seq (Label × State)) (h_prev_term : trans_prev.Terminates)
    (l_last : Label) (s_last : State)
    (h_struct : e.trans = trans_prev.append (Seq.cons (l_last, s_last) Seq.nil))
    (h_ext : ¬ sys.internal l_last) :
    jointTight sys pe' e_w_pre e =
      ∑' e_iter_start : AlterSeq State Label,
        reachProb sys pe' e_w_pre e_iter_start *
          tightStepFactor sys pe' e_w_pre l_last e_iter_start e := by
  classical
  unfold jointTight
  rw [dif_pos h_e_term]
  -- Expose the concat structure of `e.trans.toList`.
  have h_singleton_term : (Seq.cons (l_last, s_last) Seq.nil).Terminates :=
    Seq.terminates_cons_iff.mpr Seq.terminates_nil
  have h_concat : e.trans.toList h_e_term =
      trans_prev.toList h_prev_term ++ [(l_last, s_last)] := by
    have h_app_term : (trans_prev.append (Seq.cons (l_last, s_last) Seq.nil)).Terminates := by
      rw [← h_struct]; exact h_e_term
    have h_eq := Seq.toList_append trans_prev (Seq.cons (l_last, s_last) Seq.nil)
      h_prev_term h_singleton_term h_app_term
    -- `(cons last nil).toList = [last]`
    have h_singleton_toList :
        (Seq.cons (l_last, s_last) Seq.nil).toList h_singleton_term =
          [(l_last, s_last)] := by
      rw [Seq.toList_cons h_singleton_term]
      congr 1
      exact Seq.toList_nil
    -- Combine.
    have : e.trans.toList h_e_term =
        (trans_prev.append (Seq.cons (l_last, s_last) Seq.nil)).toList h_app_term := by
      congr 1
    rw [this, h_eq, h_singleton_toList]
  rw [h_concat, List.reverseRecOn_concat]
  -- The step branch fires; `internal l_last` is false.
  rw [if_neg h_ext]

-- **Trace factorisation at an external last entry.** When `e.trans` splits as
-- `trans_prev ++ [(l_last, s_last)]` with `l_last` external, the trace of `e`
-- splits as `(trace ⟨e.init, trans_prev⟩) ++ [l_last]`.
private lemma trace_append_singleton_external
    (sys : LabelledSystem State Label) (s_init : State)
    (trans_prev : Seq (Label × State)) (h_prev_term : trans_prev.Terminates)
    (l_last : Label) (s_last : State)
    (h_ext : ¬ sys.internal l_last) :
    sys.trace ⟨s_init, trans_prev.append (Seq.cons (l_last, s_last) Seq.nil)⟩
      = (sys.trace ⟨s_init, trans_prev⟩).append (Seq.cons l_last Seq.nil) := by
  classical
  unfold LabelledSystem.trace
  change ((trans_prev.append (Seq.cons (l_last, s_last) Seq.nil)).filter
            (fun p => ¬ sys.internal p.1)).map Prod.fst
      = ((trans_prev.filter (fun p => ¬ sys.internal p.1)).map Prod.fst).append
          (Seq.cons l_last Seq.nil)
  rw [Seq.filter_append _ _ _ h_prev_term, Seq.map_append]
  congr 1
  rw [Seq.filter_cons_pos (l_last, s_last) _ h_ext, Seq.filter_nil, Seq.map_cons,
      Seq.map_nil]

-- **Trace factorisation at an internal last entry.** When `e.trans` splits as
-- `trans_prev ++ [(l_last, s_last)]` with `l_last` internal, the trace of `e`
-- equals the trace of `⟨e.init, trans_prev⟩` (the internal label is dropped by
-- the trace's filter step).
private lemma trace_append_singleton_internal
    (sys : LabelledSystem State Label) (s_init : State)
    (trans_prev : Seq (Label × State)) (h_prev_term : trans_prev.Terminates)
    (l_last : Label) (s_last : State)
    (h_int : sys.internal l_last) :
    sys.trace ⟨s_init, trans_prev.append (Seq.cons (l_last, s_last) Seq.nil)⟩
      = sys.trace ⟨s_init, trans_prev⟩ := by
  classical
  unfold LabelledSystem.trace
  change ((trans_prev.append (Seq.cons (l_last, s_last) Seq.nil)).filter
            (fun p => ¬ sys.internal p.1)).map Prod.fst
      = (trans_prev.filter (fun p => ¬ sys.internal p.1)).map Prod.fst
  rw [Seq.filter_append _ _ _ h_prev_term,
      Seq.filter_cons_neg (l_last, s_last) _ (not_not_intro h_int),
      Seq.filter_nil, Stream'.Seq.append_nil]

-- **Tight execution's last entry extraction**: when `e` is tight with
-- terminating non-empty `trans`, `e.trans = trans_prev ++ [(l_last, s_last)]`
-- for some terminating `trans_prev`, with `l_last` external. This is the
-- structural counterpart of `IsTight`'s second branch.
private lemma tight_trans_split_last_witness
    (sys : LabelledSystem State Label)
    (e : AlterSeq State Label) (h_e_term : e.trans.Terminates)
    (h_e_tight : sys.IsTight e) (h_ne : e.trans ≠ Seq.nil) :
    ∃ (trans_prev : Seq (Label × State)) (_h_prev_term : trans_prev.Terminates)
      (l_last : Label) (s_last : State),
      e.trans = trans_prev.append (Seq.cons (l_last, s_last) Seq.nil) ∧
      ¬ sys.internal l_last := by
  classical
  rcases h_e_tight with h_term0 | ⟨n, l_last, s_last, h_get, h_term_succ, h_ext⟩
  · exfalso; apply h_ne; exact Seq.terminatedAt_zero_iff.mp h_term0
  have h_toL_ne : e.trans.toList h_e_term ≠ [] := by
    intro h_empty
    apply h_ne
    have h_eq : e.trans = Seq.ofList (e.trans.toList h_e_term) :=
      (Seq.ofList_toList _ _).symm
    rw [h_empty] at h_eq
    rw [h_eq]; rfl
  obtain ⟨trans_prev, last_pair, h_prev_term, h_struct, _, h_last_eq⟩ :=
    Stream'.Seq.exists_split_last e.trans h_e_term h_toL_ne
  have h_not_term_n : ¬ e.trans.TerminatedAt n := by
    intro h_term_n
    have h_none : e.trans.get? n = none := h_term_n
    rw [h_none] at h_get
    simp at h_get
  have h_find_eq : Nat.find h_e_term = n + 1 := by
    apply le_antisymm
    · exact Nat.find_min' h_e_term h_term_succ
    · rcases Nat.lt_or_ge n (Nat.find h_e_term) with h_lt | h_ge
      · exact h_lt
      · exfalso; apply h_not_term_n
        exact Seq.terminated_stable _ h_ge (Nat.find_spec h_e_term)
  have h_getLast?_eq : (e.trans.toList h_e_term).getLast? = e.trans.get? n := by
    rw [Seq.getLast?_toList]
    have h_len : e.trans.length h_e_term = n + 1 := h_find_eq
    rw [h_len, Nat.add_sub_cancel]
  have h_getLast? : (e.trans.toList h_e_term).getLast? = some last_pair :=
    (List.getLast_eq_iff_getLast?_eq_some h_toL_ne).mp h_last_eq.symm
  rw [h_getLast?_eq, h_get] at h_getLast?
  have h_last_pair_eq : (l_last, s_last) = last_pair := Option.some_inj.mp h_getLast?
  refine ⟨trans_prev, h_prev_term, l_last, s_last, ?_, h_ext⟩
  rw [h_last_pair_eq]; exact h_struct

/-- **Marginal identity A — base case.** When `e.trans = Seq.nil`,
`jointTight`'s marginal over `e_w_pre` collapses to the initial-state
indicator and matches `(pe_of_weak …).probOf ⟨s_init, Seq.nil⟩
= pe'.initState s_init`. -/
private lemma jointTight_marginal_A_base
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (s_init : State) :
    (∑' e_w_pre : AlterSeq State Label,
        jointTight sys pe' e_w_pre ⟨s_init, Seq.nil⟩) =
      (pe_of_weak sys pe').probOf ⟨s_init, Seq.nil⟩ Seq.terminates_nil := by
  classical
  -- RHS reduces to `pe'.initState s_init` via `probOf_nil`.
  rw [(pe_of_weak sys pe').probOf_nil]
  -- LHS: every `jointTight ewp ⟨s_init, nil⟩` equals
  -- `if ewp.init = s_init ∧ ewp.trans = nil then pe'.initState ewp.init else 0`.
  rw [tsum_eq_single (⟨s_init, Seq.nil⟩ : AlterSeq State Label)]
  · -- Picked term: ewp = ⟨s_init, nil⟩.
    rw [jointTight_nil]
    -- `(pe_of_weak sys pe').init = pe'.initState` is definitional.
    show (open Classical in
      if ((⟨s_init, Seq.nil⟩ : AlterSeq State Label).init = s_init ∧
          (⟨s_init, Seq.nil⟩ : AlterSeq State Label).trans = Seq.nil) then
        pe'.initState (⟨s_init, Seq.nil⟩ : AlterSeq State Label).init else 0) =
      (pe_of_weak sys pe').init s_init
    simp [pe_of_weak]
  · -- Other terms: zero.
    intro c hc
    rw [jointTight_nil]
    split_ifs with h_eq
    · obtain ⟨h_init, h_trans⟩ := h_eq
      exfalso
      apply hc
      obtain ⟨i, t⟩ := c
      dsimp at h_init h_trans
      subst h_init; subst h_trans
      rfl
    · rfl

/-- **Iteration-split decomposition of a tight execution.**

A `sys`-tight, terminating, non-empty execution `e` decomposes uniquely as

```
e.trans = e_prev.trans ++ chain_pre ++ [(l_last, s_last)]
```

where:
* `e_prev` is a `sys`-tight terminating prefix sharing `e`'s initial state
  (it is the shortest tight prefix ending strictly before the last external
  step — either `Seq.nil` if `e` has only one external step preceded by an
  internal chain, or the prefix ending right after the previous external
  step);
* `chain_pre` is a list of internal-labelled entries (the pre-`l_last`
  internal chain in `e`'s last iteration);
* `(l_last, s_last)` is the final external entry.

This is the iteration-based decomposition needed for the strong induction
in `jointTight_marginal_A`. The previous "drop just the last entry"
decomposition is **not** valid because a tight execution's last entry is
external but the entry before it may be internal, so the prefix
"`e.trans` minus the last entry" can fail to be tight.

The proof finds the last external entry of `e.trans` (which exists by
`tight_trans_split_last_witness`), then within the prefix `trans_prev`
finds the **previous** external entry (or determines there is none, in
which case `e_prev = ⟨e.init, Seq.nil⟩` which is trivially tight via
`Or.inl Seq.terminatedAt_nil_zero`).

Deferred as a focused sub-sorry: it is a purely structural list-search
argument over `trans_prev.toList`. -/
private lemma iteration_split_last_external
    (sys : LabelledSystem State Label)
    (e : AlterSeq State Label) (h_e_term : e.trans.Terminates)
    (h_e_tight : sys.IsTight e) (h_e_nonempty : e.trans ≠ Seq.nil) :
    ∃ (e_prev : AlterSeq State Label) (h_prev_term : e_prev.trans.Terminates)
      (chain_pre : List (Label × State)) (l_last : Label) (s_last : State),
      e.trans = e_prev.trans.append
        (Seq.ofList (chain_pre ++ [(l_last, s_last)])) ∧
      e_prev.init = e.init ∧
      sys.IsTight e_prev ∧
      ¬ sys.internal l_last ∧
      (∀ pair ∈ chain_pre, sys.internal pair.1) ∧
      (e_prev.trans.toList h_prev_term).length < (e.trans.toList h_e_term).length := by
  classical
  -- Step 1: extract `e.trans = trans_prev ++ [(l_last, s_last)]` with `l_last` external.
  obtain ⟨trans_prev, h_prev_term, l_last, s_last, h_struct_last, h_ext_last⟩ :=
    tight_trans_split_last_witness sys e h_e_term h_e_tight h_e_nonempty
  -- Let `L` be the underlying list of `trans_prev`.
  set L : List (Label × State) := trans_prev.toList h_prev_term with hL_def
  -- `trans_prev = Seq.ofList L` via ofList_toList.
  have h_trans_prev_eq : trans_prev = Seq.ofList L :=
    (Seq.ofList_toList trans_prev h_prev_term).symm
  -- The full `toList` of `e.trans`.
  have h_e_toList : e.trans.toList h_e_term = L ++ [(l_last, s_last)] := by
    have h_single_term : (Seq.cons (l_last, s_last) Seq.nil :
        Seq (Label × State)).Terminates :=
      Seq.terminates_cons_iff.mpr Seq.terminates_nil
    have h_app_term : (trans_prev.append (Seq.cons (l_last, s_last) Seq.nil)).Terminates := by
      rw [← h_struct_last]; exact h_e_term
    have h_lhs_eq :
        e.trans.toList h_e_term =
          (trans_prev.append (Seq.cons (l_last, s_last) Seq.nil)).toList h_app_term := by
      congr 1
    rw [h_lhs_eq, Seq.toList_append trans_prev _ h_prev_term h_single_term,
      Seq.toList_cons h_single_term, Seq.toList_nil, ← hL_def]
  -- Step 2: search L for the last external position via reverseRecOn.
  -- We produce either Case A (all internal) or Case B (last external found).
  have h_search : (∀ pair ∈ L, sys.internal pair.1) ∨
      ∃ (L₁ L₂ : List (Label × State)) (ext_prev : Label) (s_ext_prev : State),
        L = L₁ ++ (ext_prev, s_ext_prev) :: L₂ ∧
        ¬ sys.internal ext_prev ∧
        (∀ pair ∈ L₂, sys.internal pair.1) := by
    clear h_e_toList h_trans_prev_eq hL_def
    clear_value L
    induction L using List.reverseRecOn with
    | nil => left; intro x hx; simp at hx
    | append_singleton L' a ih =>
      by_cases ha : sys.internal a.1
      · -- Last element internal; consult IH.
        rcases ih with h_all | ⟨L₁, L₂, ext_prev, s_ext_prev, h_split, h_ext, h_L₂_int⟩
        · left
          intro pair hp
          rcases List.mem_append.mp hp with h | h
          · exact h_all pair h
          · rw [List.mem_singleton.mp h]; exact ha
        · right
          refine ⟨L₁, L₂ ++ [a], ext_prev, s_ext_prev, ?_, h_ext, ?_⟩
          · rw [h_split]; simp [List.append_assoc]
          · intro pair hp
            rcases List.mem_append.mp hp with h | h
            · exact h_L₂_int pair h
            · rw [List.mem_singleton.mp h]; exact ha
      · -- Last element external; we found it.
        right
        refine ⟨L', [], a.1, a.2, ?_, ha, ?_⟩
        · simp
        · intro pair hp; simp at hp
  rcases h_search with h_all_int | ⟨L₁, L₂, ext_prev, s_ext_prev, h_split, h_ext_prev, h_L₂_int⟩
  · -- Case A: every entry of L is internal. Use `e_prev := ⟨e.init, Seq.nil⟩`.
    refine ⟨⟨e.init, Seq.nil⟩, Seq.terminates_nil, L, l_last, s_last, ?_, rfl,
      Or.inl Seq.terminatedAt_nil, h_ext_last, h_all_int, ?_⟩
    · -- e.trans = nil.append (ofList (L ++ [(l_last, s_last)])).
      -- We have e.trans = trans_prev ++ [(l_last, s_last)] = ofList L ++ [(l_last, s_last)].
      have h_e_eq : e.trans = Seq.ofList (L ++ [(l_last, s_last)]) := by
        have h_e_toL_eq : e.trans = Seq.ofList (e.trans.toList h_e_term) :=
          (Seq.ofList_toList e.trans h_e_term).symm
        rw [h_e_toL_eq, h_e_toList]
      change e.trans = (Seq.nil : Seq (Label × State)).append
        (Seq.ofList (L ++ [(l_last, s_last)]))
      rw [h_e_eq, Seq.nil_append]
    · -- Length: 0 < L.length + 1.
      have h_nil_toL : (Seq.nil : Seq (Label × State)).toList Seq.terminates_nil = [] :=
        Seq.toList_nil
      rw [h_nil_toL, h_e_toList]
      simp
  · -- Case B: L = L₁ ++ (ext_prev, s_ext_prev) :: L₂ with the marked entry external
    -- and L₂ all internal. Use `e_prev := ⟨e.init, Seq.ofList (L₁ ++ [(ext_prev, s_ext_prev)])⟩`.
    set P := L₁ ++ [(ext_prev, s_ext_prev)] with hP_def
    have hP_term : (Seq.ofList P).Terminates := Seq.terminates_ofList P
    refine ⟨⟨e.init, Seq.ofList P⟩, hP_term, L₂, l_last, s_last, ?_, rfl, ?_,
      h_ext_last, h_L₂_int, ?_⟩
    · -- e.trans = (ofList P).append (ofList (L₂ ++ [(l_last, s_last)])).
      have h_e_eq : e.trans = Seq.ofList (L ++ [(l_last, s_last)]) := by
        have h_e_toL_eq : e.trans = Seq.ofList (e.trans.toList h_e_term) :=
          (Seq.ofList_toList e.trans h_e_term).symm
        rw [h_e_toL_eq, h_e_toList]
      have h_list_eq : L ++ [(l_last, s_last)] = P ++ (L₂ ++ [(l_last, s_last)]) := by
        rw [h_split, hP_def]; simp [List.append_assoc]
      change e.trans = (Seq.ofList P).append (Seq.ofList (L₂ ++ [(l_last, s_last)]))
      rw [h_e_eq, h_list_eq, Seq.ofList_append]
    · -- Tightness: the trans is non-empty with external last entry ext_prev.
      -- (Seq.ofList P).get? L₁.length = some (ext_prev, s_ext_prev).
      -- (Seq.ofList P).TerminatedAt (L₁.length + 1) since P.length = L₁.length + 1.
      right
      refine ⟨L₁.length, ext_prev, s_ext_prev, ?_, ?_, h_ext_prev⟩
      · -- get? of ofList at L₁.length is the L₁.length-th element of P.
        change (Seq.ofList P).get? L₁.length = some (ext_prev, s_ext_prev)
        have h_seq_get : (Seq.ofList P).get? L₁.length = P[L₁.length]? := rfl
        rw [h_seq_get, hP_def]
        simp
      · -- TerminatedAt (L₁.length + 1): P has exactly L₁.length + 1 elements.
        have hP_len : P.length = L₁.length + 1 := by
          rw [hP_def]; simp
        have h_term_at_len : (Seq.ofList P).TerminatedAt P.length := by
          have h_le : (Seq.ofList P).length hP_term ≤ P.length := by
            rw [← Seq.length_toList, Seq.toList_ofList]
          exact Seq.length_le_iff.mp h_le
        rw [hP_len] at h_term_at_len
        exact h_term_at_len
    · -- Length: ((Seq.ofList P).toList hP_term).length = P.length = L₁.length + 1
      --        < L.length + 1 = (L ++ [(l_last, s_last)]).length.
      rw [h_e_toList]
      rw [Seq.toList_ofList P]
      rw [h_split]
      simp [hP_def]

/-- **Kernel chain product along an iteration chain.**

`pe_of_weak_kernel_chain sys pe' e_prev chain` is the product, along the
entries of `chain`, of the `pe_of_weak`-kernel evaluated at the running
prefix `⟨e_prev.init, e_prev.trans.append (Seq.ofList rest)⟩`, where
`rest` ranges over the proper prefixes of `chain` (as enumerated by
`List.reverseRecOn`).

* `chain = []`: the empty product `1`.
* `chain = rest ++ [last]`: `(product on rest) * kernel⟨…, append rest⟩ last`.

This is the iteration-side counterpart of the cons-end recursion used to
define `ProbabilisticExecution.probOf`. -/
private noncomputable def pe_of_weak_kernel_chain
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_prev : AlterSeq State Label) (chain : List (Label × State)) : ENNReal :=
  chain.reverseRecOn
    (motive := fun _ => ENNReal)
    (1 : ENNReal)
    (fun rest last ih =>
      ih * (pe_of_weak sys pe').kernel
        ⟨e_prev.init, e_prev.trans.append (Seq.ofList rest)⟩ last)

@[simp] private lemma pe_of_weak_kernel_chain_nil
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_prev : AlterSeq State Label) :
    pe_of_weak_kernel_chain sys pe' e_prev [] = 1 := by
  unfold pe_of_weak_kernel_chain
  rw [List.reverseRecOn_nil]

private lemma pe_of_weak_kernel_chain_append_singleton
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_prev : AlterSeq State Label)
    (rest : List (Label × State)) (last : Label × State) :
    pe_of_weak_kernel_chain sys pe' e_prev (rest ++ [last]) =
      pe_of_weak_kernel_chain sys pe' e_prev rest *
        (pe_of_weak sys pe').kernel
          ⟨e_prev.init, e_prev.trans.append (Seq.ofList rest)⟩ last := by
  unfold pe_of_weak_kernel_chain
  rw [List.reverseRecOn_concat]

/-- **`probOf` factorises along an iteration chain.**

For any chain `chain : List (Label × State)`, the `probOf` of the appended
execution `⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩` factors
as `probOf e_prev` times the `pe_of_weak`-kernel product along `chain`.

This is purely structural: it is the iterated `probOf_append_singleton`
along the entries of `chain`. -/
private lemma pe_of_weak_probOf_chain_factorize
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_prev : AlterSeq State Label) (h_prev_term : e_prev.trans.Terminates)
    (chain : List (Label × State))
    (h_term : (e_prev.trans.append (Seq.ofList chain)).Terminates) :
    (pe_of_weak sys pe').probOf
        ⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩ h_term
      = (pe_of_weak sys pe').probOf e_prev h_prev_term *
        pe_of_weak_kernel_chain sys pe' e_prev chain := by
  classical
  -- Helper: termination is preserved under append.
  have h_term_append :
      ∀ (sq : Seq (Label × State)),
        sq.Terminates → (e_prev.trans.append sq).Terminates := by
    intro sq h_sq
    exact ⟨_, Seq.terminatedAt_append_find h_prev_term h_sq.choose_spec⟩
  induction chain using List.reverseRecOn with
  | nil =>
    -- chain = [], so the appended trans equals e_prev.trans (after Seq.nil collapse).
    rw [pe_of_weak_kernel_chain_nil, mul_one]
    -- Rewrite the LHS execution to be definitionally e_prev.
    have h_trans_eq : e_prev.trans.append
        (Seq.ofList ([] : List (Label × State))) = e_prev.trans := by
      simp [Seq.ofList_nil, Seq.append_nil]
    -- Need an AlterSeq-level equality. After destructuring `e_prev`, the goal
    -- and termination witness rewrite cleanly.
    rcases e_prev with ⟨i, t⟩
    -- Now the trans of the LHS execution is `t.append (Seq.ofList [])`,
    -- which equals `t`. Use `subst`-like rewriting via `congr`.
    have h_simp : t.append (Seq.ofList ([] : List (Label × State))) = t := by
      simp [Seq.ofList_nil, Seq.append_nil]
    -- Rewrite `h_term` and the goal simultaneously.
    revert h_term h_prev_term
    rw [h_simp]
    intro h_prev_term h_term
    rfl
  | append_singleton rest last ih =>
    -- chain = rest ++ [last]. Use Seq.ofList_append to expose the cons-end form,
    -- apply probOf_append_singleton, then use ih on rest.
    -- Rewrite the appended Seq into the cons-end form.
    have h_ofL_eq : (Seq.ofList (rest ++ [last]) : Seq (Label × State)) =
        (Seq.ofList rest).append (Seq.cons last Seq.nil) := by
      rw [Seq.ofList_append, Seq.ofList_cons, Seq.ofList_nil]
    have h_rest_term : (Seq.ofList rest : Seq (Label × State)).Terminates :=
      Seq.terminates_ofList rest
    have h_app_rest_term : (e_prev.trans.append (Seq.ofList rest)).Terminates :=
      h_term_append _ h_rest_term
    -- Rewrite the appended trans to expose the cons-end shape.
    have h_trans_eq : e_prev.trans.append (Seq.ofList (rest ++ [last])) =
        (e_prev.trans.append (Seq.ofList rest)).append (Seq.cons last Seq.nil) := by
      rw [h_ofL_eq, ← Seq.append_assoc]
    -- The appended-LHS executions, modulo the trans rewrite, are equal.
    -- Coerce the termination witness through h_trans_eq.
    have h_term' : ((e_prev.trans.append (Seq.ofList rest)).append
        (Seq.cons last Seq.nil)).Terminates := h_trans_eq ▸ h_term
    -- Step 1: replace the chain-appended probOf by the cons-end appended probOf.
    have h_probOf_eq :
        (pe_of_weak sys pe').probOf
            ⟨e_prev.init, e_prev.trans.append (Seq.ofList (rest ++ [last]))⟩ h_term
          = (pe_of_weak sys pe').probOf
            ⟨e_prev.init, (e_prev.trans.append (Seq.ofList rest)).append
                (Seq.cons last Seq.nil)⟩ h_term' := by
      revert h_term
      rw [h_trans_eq]
      intro h_term
      rfl
    rw [h_probOf_eq]
    -- Step 2: apply probOf_append_singleton on the prefix
    -- ⟨e_prev.init, e_prev.trans.append (Seq.ofList rest)⟩ with last entry `last`.
    rw [ProbabilisticExecution.probOf_append_singleton
      (pe := pe_of_weak sys pe') (s₀ := e_prev.init)
      (sq := e_prev.trans.append (Seq.ofList rest)) (h_sq := h_app_rest_term)
      (last := last)]
    -- Step 3: apply the inductive hypothesis on rest, then regroup.
    rw [ih h_app_rest_term]
    rw [pe_of_weak_kernel_chain_append_singleton]
    ring

/-- **Marginal identity A — base case, Sub-claim 1: e_iter_start sum collapse.**

For the base case `chain_pre = []`, the iteration's chain is just
`[(l_last, s_last)]`. The inner `e_iter_start` sum in
`jointTight_step_external`'s expansion collapses to a single contribution at
`e_iter_start = e_prev`: every other `e_iter_start` makes `tightStepFactor`
vanish. The reasoning is structural:
* If `e_iter_start.trans.toList` is strictly shorter than `e_prev.trans.toList`,
  then the `chain.dropLast` portion of `tightStepFactor`'s internal-only
  constraint would have to include `e_prev`'s last entry — which is external
  by tightness of `e_prev` (`tight_trans_split_last_witness`).
* If it is strictly longer (or has the same length but differs), the prefix
  match `e_list.take k = e_iter_start_list` fails, or the chain `e_list.drop k`
  is empty / inconsistent.

**Status:** deferred (focused sub-sorry). Pure structural list manipulation. -/
private lemma tightStepFactor_chain_pre_empty_iter_start_eq_e_prev
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e e_prev : AlterSeq State Label)
    (h_e_term : e.trans.Terminates) (h_prev_term : e_prev.trans.Terminates)
    (h_prev_tight : sys.IsTight e_prev)
    (l_last : Label) (s_last : State) (h_ext : ¬ sys.internal l_last)
    (h_struct : e.trans = e_prev.trans.append (Seq.cons (l_last, s_last) Seq.nil))
    (h_init : e_prev.init = e.init)
    (e_w_pre e_iter_start : AlterSeq State Label)
    (h_iter_ne_prev : e_iter_start ≠ e_prev) :
    tightStepFactor sys pe' e_w_pre l_last e_iter_start e = 0 := by
  classical
  unfold tightStepFactor
  -- Dispatch the three termination conditions.
  by_cases h_ewp : e_w_pre.trans.Terminates
  swap
  · simp [h_ewp]
  by_cases h_es : e_iter_start.trans.Terminates
  swap
  · simp [h_ewp, h_es]
  rw [dif_pos h_ewp, dif_pos h_es, dif_pos h_e_term]
  -- Set up the locals exactly as in the definition.
  set s_pre : State := e_w_pre.endState h_ewp with hs_pre
  set e_iter_start_list : List (Label × State) := e_iter_start.trans.toList h_es
    with h_eis_list
  set e_list : List (Label × State) := e.trans.toList h_e_term with h_e_list
  by_cases h_prefix : e_iter_start.init = e.init ∧
                  e_list.take e_iter_start_list.length = e_iter_start_list
  swap
  · simp [h_prefix]
  rw [dif_pos h_prefix]
  set chain : List (Label × State) := e_list.drop e_iter_start_list.length with h_chain
  -- Reduce to: every summand is 0.
  refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
  by_cases h_supp : some (l_last, μ) ∈ (pe'.scheduler.next e_w_pre).support
  swap
  · simp [h_supp]
  rw [dif_pos h_supp]
  by_cases h_int : sys.internal l_last
  · exact absurd h_int h_ext
  rw [dif_neg h_int]
  -- Compute `e_list = L_prev ++ [(l_last, s_last)]`.
  set L_prev : List (Label × State) := e_prev.trans.toList h_prev_term with hL_prev
  have h_single_term : (Seq.cons (l_last, s_last) Seq.nil :
      Seq (Label × State)).Terminates :=
    Seq.terminates_cons_iff.mpr Seq.terminates_nil
  have h_app_term : (e_prev.trans.append (Seq.cons (l_last, s_last) Seq.nil)).Terminates := by
    rw [← h_struct]; exact h_e_term
  have h_e_toList : e_list = L_prev ++ [(l_last, s_last)] := by
    have h_lhs_eq :
        e.trans.toList h_e_term =
          (e_prev.trans.append (Seq.cons (l_last, s_last) Seq.nil)).toList h_app_term := by
      congr 1
    rw [h_e_list, h_lhs_eq, Seq.toList_append e_prev.trans _ h_prev_term h_single_term,
      Seq.toList_cons h_single_term, Seq.toList_nil, ← hL_prev]
  -- Set `k = e_iter_start_list.length`.
  set k : ℕ := e_iter_start_list.length with hk
  -- Length bound: `k ≤ L_prev.length + 1`.
  have h_k_le : k ≤ L_prev.length + 1 := by
    have h_len_eq : e_list.length = L_prev.length + 1 := by
      rw [h_e_toList]; simp
    have h_take_len : (e_list.take k).length = k := by
      rw [h_prefix.2]
    have h_take_len_le : (e_list.take k).length ≤ e_list.length := by
      rw [List.length_take]; exact Nat.min_le_right _ _
    rw [h_take_len, h_len_eq] at h_take_len_le
    exact h_take_len_le
  -- Case analysis on `k`.
  rcases Nat.lt_or_ge k L_prev.length with h_k_lt | h_k_ge
  · -- Case 1: k < L_prev.length. Show `chain.dropLast` contains `e_prev`'s
    -- last external entry (via tightness), contradicting `all-internal`.
    -- chain = drop k (L_prev ++ [(l_last, s_last)]) = L_prev.drop k ++ [(l_last, s_last)]
    have h_chain_form : chain = L_prev.drop k ++ [(l_last, s_last)] := by
      rw [h_chain, h_e_toList, List.drop_append_of_le_length (le_of_lt h_k_lt)]
    -- chain.dropLast = L_prev.drop k
    have h_drop_ne : L_prev.drop k ≠ [] := by
      intro h_empty
      have h_len : (L_prev.drop k).length = L_prev.length - k := List.length_drop
      rw [h_empty] at h_len
      simp at h_len
      omega
    have h_chain_dropLast : chain.dropLast = L_prev.drop k := by
      rw [h_chain_form, List.dropLast_concat]
    have h_chain_getLast? : chain.getLast? = some (l_last, s_last) := by
      rw [h_chain_form]; simp
    rw [h_chain_getLast?]
    simp only [if_true]
    -- Extract `L_prev`'s last external entry via tightness.
    have h_L_prev_ne : L_prev ≠ [] := by
      intro h_empty
      have h_len : L_prev.length = 0 := by rw [h_empty]; rfl
      omega
    have h_prev_trans_ne : e_prev.trans ≠ Seq.nil := by
      intro h_nil
      apply h_L_prev_ne
      have h_tl_eq : L_prev = (Seq.nil : Seq (Label × State)).toList Seq.terminates_nil := by
        rw [hL_prev]
        congr 1
      rw [h_tl_eq, Seq.toList_nil]
    -- Tightness gives external last entry of `e_prev.trans.toList`.
    obtain ⟨trans_prev', h_prev'_term, l_p, s_p, h_split_prev, h_ext_p⟩ :=
      tight_trans_split_last_witness sys e_prev h_prev_term h_prev_tight h_prev_trans_ne
    -- So `L_prev = trans_prev'.toList ++ [(l_p, s_p)]`.
    have h_single_p_term : (Seq.cons (l_p, s_p) Seq.nil :
        Seq (Label × State)).Terminates :=
      Seq.terminates_cons_iff.mpr Seq.terminates_nil
    have h_app_p_term :
        (trans_prev'.append (Seq.cons (l_p, s_p) Seq.nil)).Terminates := by
      rw [← h_split_prev]; exact h_prev_term
    have h_L_prev_form :
        L_prev = trans_prev'.toList h_prev'_term ++ [(l_p, s_p)] := by
      have h_lhs_eq :
          e_prev.trans.toList h_prev_term =
            (trans_prev'.append (Seq.cons (l_p, s_p) Seq.nil)).toList h_app_p_term := by
        congr 1
      rw [hL_prev, h_lhs_eq,
        Seq.toList_append trans_prev' _ h_prev'_term h_single_p_term,
        Seq.toList_cons h_single_p_term, Seq.toList_nil]
    -- `(l_p, s_p) ∈ L_prev.drop k` since `k < L_prev.length`.
    have h_mem : (l_p, s_p) ∈ L_prev.drop k := by
      rw [h_L_prev_form]
      have h_k_lt' : k < (trans_prev'.toList h_prev'_term ++ [(l_p, s_p)]).length := by
        rw [← h_L_prev_form]; exact h_k_lt
      have h_k_le_tp : k ≤ (trans_prev'.toList h_prev'_term).length := by
        rw [List.length_append, List.length_singleton] at h_k_lt'
        omega
      rw [List.drop_append_of_le_length h_k_le_tp]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    -- Now if all `chain.dropLast = L_prev.drop k` entries are internal,
    -- then `l_p` is internal — contradiction.
    by_cases h_all_int : ∀ pair ∈ chain.dropLast, sys.internal pair.1
    · exfalso
      apply h_ext_p
      have h_p_int : sys.internal (l_p, s_p).1 := by
        apply h_all_int
        rw [h_chain_dropLast]; exact h_mem
      exact h_p_int
    · rw [if_neg h_all_int]; ring
  -- Case 2: k ≥ L_prev.length. Combined with k ≤ L_prev.length + 1, either
  -- k = L_prev.length or k = L_prev.length + 1.
  rcases Nat.eq_or_lt_of_le h_k_ge with h_k_eq | h_k_gt
  · -- Subcase 2a: k = L_prev.length. e_iter_start_list = L_prev, so
    -- e_iter_start.trans = e_prev.trans. Combined with h_init this gives
    -- e_iter_start = e_prev, contradicting h_iter_ne_prev.
    have h_k_val : k = L_prev.length := h_k_eq.symm
    have h_iter_eq_prev_list : e_iter_start_list = L_prev := by
      have h_take : e_list.take k = e_iter_start_list := h_prefix.2
      rw [h_e_toList, h_k_val] at h_take
      rw [List.take_left] at h_take
      exact h_take.symm
    -- So `e_iter_start.trans = e_prev.trans` via `ofList_toList`.
    have h_iter_trans_eq : e_iter_start.trans = e_prev.trans := by
      have h_iter : e_iter_start.trans = Seq.ofList e_iter_start_list := by
        rw [h_eis_list]; exact (Seq.ofList_toList _ _).symm
      have h_prev : e_prev.trans = Seq.ofList L_prev := by
        rw [hL_prev]; exact (Seq.ofList_toList _ _).symm
      rw [h_iter, h_iter_eq_prev_list, ← h_prev]
    -- With `h_prefix.1 : e_iter_start.init = e.init` and `h_init : e_prev.init = e.init`,
    -- we get `e_iter_start.init = e_prev.init`, hence `e_iter_start = e_prev`,
    -- contradicting `h_iter_ne_prev`.
    exfalso
    apply h_iter_ne_prev
    have h_init_eq : e_iter_start.init = e_prev.init := by
      rw [h_prefix.1, ← h_init]
    cases e_iter_start with
    | mk i t =>
      cases e_prev with
      | mk i' t' =>
        dsimp at h_init_eq h_iter_trans_eq
        subst h_init_eq; subst h_iter_trans_eq; rfl
  · -- Subcase 2b: L_prev.length < k, and k ≤ L_prev.length + 1, so k = L_prev.length + 1.
    have h_k_val : k = L_prev.length + 1 := by omega
    -- Then `chain = drop k e_list = drop (L_prev.length + 1) (L_prev ++ [(l_last, s_last)]) = []`.
    have h_chain_nil : chain = [] := by
      rw [h_chain, h_e_toList, h_k_val]
      simp
    rw [h_chain_nil]
    simp

/-- **Helper.** Explicit case-split formula for `pe_of_weak.scheduler.next` at a
`some (l, μ)` argument. Three cases: `FirstReach ∈ {0, ⊤}` vacuous fallbacks,
and the normalised main case dividing by `FirstReach`. The `some`-coefficient
agrees with `jointUnnorm` (only the `none`-coefficient absorbs the trap mass). -/
private lemma pe_of_weak_scheduler_next_some_apply
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (prefix_ : AlterSeq State Label) (l : Label) (μ : PMF State) :
    (pe_of_weak sys pe').scheduler.next prefix_ (some (l, μ)) =
      (open Classical in
       if FirstReach sys pe' prefix_ = 0 then 0
       else if FirstReach sys pe' prefix_ = ⊤ then 0
       else jointUnnorm sys pe' prefix_ (some (l, μ)) /
              FirstReach sys pe' prefix_) := by
  classical
  change (open Classical in
            if h_fr0 : FirstReach sys pe' prefix_ = 0 then
              PMF.pure none
            else if h_fr_top : FirstReach sys pe' prefix_ = ⊤ then
              PMF.pure none
            else
              PMF.normalize (correctedMass sys pe' prefix_)
                ((correctedMass_tsum_eq_FirstReach sys pe' prefix_).symm ▸ h_fr0)
                ((correctedMass_tsum_eq_FirstReach sys pe' prefix_).symm ▸ h_fr_top))
              (some (l, μ)) = _
  split_ifs with h_fr0 h_fr_top
  · rw [PMF.pure_apply]; simp
  · rw [PMF.pure_apply]; simp
  · rw [PMF.normalize_apply, correctedMass_some,
        correctedMass_tsum_eq_FirstReach]
    rw [ENNReal.div_eq_inv_mul, mul_comm]

/-- **Helper.** Explicit case-split formula for `pe_of_weak.kernel` at
`(l_last, s_last)`. Three cases mirroring the scheduler. -/
private lemma pe_of_weak_kernel_eq
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (prefix_ : AlterSeq State Label) (l : Label) (s : State) :
    (pe_of_weak sys pe').kernel prefix_ (l, s) =
      (open Classical in
       if FirstReach sys pe' prefix_ = 0 then 0
       else if FirstReach sys pe' prefix_ = ⊤ then 0
       else (∑' μ : PMF State,
              jointUnnorm sys pe' prefix_ (some (l, μ)) * μ s) /
              FirstReach sys pe' prefix_) := by
  classical
  unfold ProbabilisticExecution.kernel
  simp only [pe_of_weak_scheduler_next_some_apply sys pe' prefix_]
  split_ifs with h_fr0 h_fr_top
  · simp
  · simp
  · rw [ENNReal.div_eq_inv_mul]
    simp_rw [ENNReal.div_eq_inv_mul, mul_assoc]
    rw [← ENNReal.tsum_mul_left]

/-- **`FirstReach` equals `pe_of_weak.probOf`**. By strong induction on
`e.trans.toList.length`, using `FirstReach_nil` / `probOf_nil` at the base
and `FirstReach_append_singleton` / `probOf_append_singleton` /
`pe_of_weak_kernel_eq` at the step (with `FirstReach`-denominator cancellation
via `ENNReal.mul_div_cancel`). The `FirstReach (prefix) = 0` corner is
handled by `totalMass_le_FirstReach + jointUnnorm_eq_zero_of_totalMass_eq_zero`,
which forces both sides to `0`. -/
private lemma FirstReach_eq_probOf
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e : AlterSeq State Label) (h_e_term : e.trans.Terminates) :
    FirstReach sys pe' e = (pe_of_weak sys pe').probOf e h_e_term := by
  classical
  obtain ⟨i, sq⟩ := e
  -- Strong induction on `(sq.toList h_e_term).length`.
  set n : ℕ := (sq.toList h_e_term).length with hn_def
  clear_value n
  induction n using Nat.strong_induction_on generalizing sq with
  | _ n ih =>
    by_cases h_sq_nil : sq = Seq.nil
    · -- Base case.
      subst h_sq_nil
      rw [FirstReach_nil sys pe' i]
      exact ((pe_of_weak sys pe').probOf_nil i).symm
    · -- Step case: split sq at its last entry.
      have h_toL_ne : sq.toList h_e_term ≠ [] := by
        intro h_nil; apply h_sq_nil
        rw [← Stream'.Seq.ofList_toList sq h_e_term, h_nil]; rfl
      obtain ⟨prev, last, h_prev_term, h_struct, h_prev_toList, h_last_eq⟩ :=
        Stream'.Seq.exists_split_last sq h_e_term h_toL_ne
      -- Substitute `sq` by its split form everywhere; this rewrites
      -- `h_e_term` and the strong-induction `ih` against the new shape too.
      subst h_struct
      have h_singleton_term :
          (Seq.cons last Seq.nil : Seq (Label × State)).Terminates :=
        Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
      have h_sq_toList :
          (prev.append (Seq.cons last Seq.nil)).toList h_e_term =
            prev.toList h_prev_term ++ [last] := by
        rw [Stream'.Seq.toList_append prev (Seq.cons last Seq.nil)
              h_prev_term h_singleton_term h_e_term]
        congr 1
        rw [Stream'.Seq.toList_cons]; simp [Stream'.Seq.toList_nil]
      -- IH at the shorter prefix `⟨i, prev⟩`.
      have h_IH :
          FirstReach sys pe' ⟨i, prev⟩ =
            (pe_of_weak sys pe').probOf ⟨i, prev⟩ h_prev_term := by
        refine ih (prev.toList h_prev_term).length ?_ prev h_prev_term rfl
        rw [hn_def, h_sq_toList]; simp
      rw [FirstReach_append_singleton sys pe' i prev h_prev_term last h_e_term,
        (pe_of_weak sys pe').probOf_append_singleton i prev h_prev_term last h_e_term,
        ← h_IH]
      -- Unfold the kernel and case-split on `FirstReach ⟨i, prev⟩`.
      rcases last with ⟨l, s⟩
      rw [pe_of_weak_kernel_eq sys pe' ⟨i, prev⟩ l s]
      split_ifs with h_fr0 h_fr_top
      · -- FirstReach = 0: both sides collapse to 0.
        rw [mul_zero]
        have h_tm0 : totalMass sys pe' ⟨i, prev⟩ = 0 := by
          have h := totalMass_le_FirstReach sys pe' ⟨i, prev⟩
          rw [h_fr0] at h; exact le_antisymm h bot_le
        have h_jU_zero : ∀ opt, jointUnnorm sys pe' ⟨i, prev⟩ opt = 0 := by
          intro opt
          have h_tm0' := h_tm0
          unfold totalMass at h_tm0'
          exact ENNReal.tsum_eq_zero.mp h_tm0' opt
        refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
        rw [h_jU_zero (some (l, μ))]; simp
      · -- FirstReach = ⊤: contradicts IH (probOf ≤ pe.init ≤ 1, so FR ≤ 1).
        exfalso
        have h_le : FirstReach sys pe' ⟨i, prev⟩ ≤ 1 := by
          rw [h_IH]
          exact (ProbabilisticExecution.probOf_le_init _ _ h_prev_term).trans
            (PMF.coe_le_one _ _)
        exact (lt_of_le_of_lt h_le ENNReal.one_lt_top).ne h_fr_top
      · -- Main case: cancel via `ENNReal.mul_div_cancel` using `h_fr_top : FR ≠ ⊤`.
        exact (ENNReal.mul_div_cancel h_fr0 h_fr_top).symm

/-- **`FirstReach` is finite** (in fact `≤ 1`). For terminating `e`,
`FirstReach e = probOf e ≤ pe.init e.init ≤ 1`. For non-terminating `e`,
`FirstReach e = 0`. -/
private lemma FirstReach_ne_top
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e : AlterSeq State Label) :
    FirstReach sys pe' e ≠ ⊤ := by
  classical
  by_cases h_term : e.trans.Terminates
  · rw [FirstReach_eq_probOf sys pe' e h_term]
    have h_le : (pe_of_weak sys pe').probOf e h_term ≤
                (pe_of_weak sys pe').init e.init :=
      ProbabilisticExecution.probOf_le_init _ e h_term
    exact (lt_of_le_of_lt (h_le.trans (PMF.coe_le_one _ _))
      ENNReal.one_lt_top).ne
  · have h_zero : FirstReach sys pe' e = 0 := by
      unfold FirstReach
      rw [dif_neg h_term]
    rw [h_zero]
    exact ENNReal.zero_ne_top

/-- **Identity 1**: `tightStepFactor` at `chain_pre = []` for an external
`l_last` equals the marginal of `iterOutcome.visible(d) · d (l_last, μ) · μ s_last`
over `μ` and `d`.

This is the foundational per-`e_w_pre` correspondence: `tightStepFactor`'s
"σ_pre halts immediately + hyperStep" structure matches the corresponding
visible-outcome integration in `iterOutcome`. Both expressions reduce to:

  ∑' μ_emit, scheduler.next e_w_pre (some (l_last, μ_emit)) ·
    σ_pre^{μ_emit}.next ⟨s_pre, nil⟩ none ·
    ((kernel^{μ_emit} s_pre).bind id) s_last

where `σ_pre := h_ws.weakTau_pre.witness` and `kernel := h_ws.hyperStep_mid.kernel`
are extracted from the same `weakStep` witness
`h_ws : weakStep sys (PMF.pure s_pre) l_last μ_emit` obtained via
`pe'.scheduler.valid` at `e_w_pre`.

### Mathematical proof outline

**LHS** (`tightStepFactor` external case, `chain_pre = []`):
* Unfolds to `∑ μ_emit, scheduler.next (some (l_last, μ_emit)) * χ_supp *
  σ_pre.next ⟨s_pre, nil⟩ none * (∑ μ_l, p s_pre μ_l * μ_l s_last)`.
* `chainProb σ_pre ⟨s_pre, nil⟩ []` equals `σ_pre.next ⟨s_pre, nil⟩ none` by def.
* `∑ μ_l, p s_pre μ_l * μ_l s_last = ((p s_pre).bind id) s_last` by `PMF.bind_apply`.

**RHS** (iterOutcome.visible integration):
* `iterOutcome` at `(e_w_pre, e_prev)` unfolds via `(scheduler.next).bind (...)`.
* For `sub_emit = none` in the σ_pre branch (external case): produces
  `visible((kernel s_pre).map (fun μ_l => (l_last, μ_l)))`.
* For `sub_emit = some sub_lμ`: produces `visible(PMF.pure sub_lμ)`. But σ_pre is
  `internal_only`, so `sub_lμ.1` is internal `≠ l_last` (external). So
  `d (l_last, μ) = 0` for these contributions.

So `∑ d, iter.visible(d) · d (l_last, μ)` reduces to:
```
∑ μ_emit, scheduler.next (some (l_last, μ_emit)) · σ_pre^{μ_emit}.next none ·
  ((kernel^{μ_emit} s_pre).map ...) (l_last, μ)
```

`((kernel s_pre).map (fun μ_l => (l_last, μ_l))) (l_last, μ) = (kernel s_pre) μ`
by `PMF.map_apply` with the injective embedding.

Hence
`∑ μ d, iter.visible · d (l_last, μ) · μ s_last
  = ∑ μ_emit, scheduler.next · σ_pre.next none · ∑ μ, (kernel s_pre) μ · μ s_last`,
and by Fubini and `PMF.bind_apply`, this equals
`∑ μ_emit, scheduler.next · σ_pre.next none · ((kernel s_pre).bind id) s_last`,
matching LHS.

**Status:** statement landed; structural reductions complete. The LHS is
fully unfolded into canonical form (∑' μ, scheduler · σ_pre.next none ·
hyperStep-mass) and the non-terminating-`e_w_pre` case is fully proven on
both sides. The remaining focused sorry is the canonical-form matching of
the RHS via Fubini + σ_pre `internal_only` (to discard internal-σ_pre
side-channels with `d (l_last, μ) = 0`) + `PMF.map_apply` (on the
injective embedding `(fun μ_l ↦ (l_last, μ_l))`) + `PMF.bind_apply` at two
layers (outer scheduler bind and inner σ_pre.next bind). -/
private lemma tightStepFactor_eq_iterOutcome_visible_marginal
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_pre : AlterSeq State Label)
    (l_last : Label) (h_ext : ¬ sys.internal l_last)
    (e_prev : AlterSeq State Label) (h_prev_term : e_prev.trans.Terminates)
    (e : AlterSeq State Label) (h_e_term : e.trans.Terminates)
    (s_last : State)
    (h_struct : e.trans = e_prev.trans.append (Seq.cons (l_last, s_last) Seq.nil))
    (h_init : e_prev.init = e.init) :
    tightStepFactor sys pe' e_w_pre l_last e_prev e
      = ∑' μ : PMF State, ∑' d : PMF (Label × PMF State),
          iterOutcome sys pe' e_w_pre e_prev (AlgoStepOutcome.visible d) *
            d (l_last, μ) * μ s_last := by
  classical
  -- Phase A: Reduce non-terminating `e_w_pre` case on both sides.
  by_cases h_ewp : e_w_pre.trans.Terminates
  swap
  · -- Non-terminating e_w_pre: tightStepFactor = 0 (outer dif fails).
    -- iterOutcome at h_term = false defaults to PMF.pure halt, so its mass
    -- at `visible d` is 0 for every d.
    have h_LHS : tightStepFactor sys pe' e_w_pre l_last e_prev e = 0 := by
      unfold tightStepFactor; rw [dif_neg h_ewp]
    have h_RHS_term :
        ∀ μ : PMF State, ∀ d : PMF (Label × PMF State),
          iterOutcome sys pe' e_w_pre e_prev (AlgoStepOutcome.visible d) = 0 := by
      intro μ d
      unfold iterOutcome
      rw [dif_neg h_ewp]
      simp [PMF.pure_apply]
    rw [h_LHS]
    symm
    refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
    refine ENNReal.tsum_eq_zero.mpr (fun d => ?_)
    rw [h_RHS_term μ d]; ring
  -- Phase B: Terminating `e_w_pre`. The substantive equality is the
  -- algebraic identity matching LHS = RHS via the shared `weakStep` witness
  -- and `internal_only` discarding internal-σ_pre side-channels.
  -- **Phase B.1: LHS reduction.** Unfold tightStepFactor at `e_iter_start = e_prev`,
  -- `chain_pre = []`, external `l_last`. The chain is `[(l_last, s_last)]`.
  set s_pre : State := e_w_pre.endState h_ewp with hs_pre
  have h_LHS_reduced :
      tightStepFactor sys pe' e_w_pre l_last e_prev e =
        ∑' μ : PMF State,
          pe'.scheduler.next e_w_pre (some (l_last, μ)) *
            (if h_supp : some (l_last, μ) ∈ (pe'.scheduler.next e_w_pre).support then
              have h_sw : sys^w.step s_pre l_last μ :=
                pe'.scheduler.valid e_w_pre (Nat.find h_ewp) s_pre
                  (Nat.find_spec h_ewp)
                  (AlterSeq.stateAt_find_eq_endState e_w_pre h_ewp)
                  l_last μ h_supp
              have h_ws : weakStep sys (PMF.pure s_pre) l_last μ := by
                rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
                · exact absurd h_int' h_ext
                · exact h
              h_ws.weakTau_pre.witness.next ⟨s_pre, Seq.nil⟩ none *
                (∑' μ_l : PMF State, h_ws.hyperStep_mid.kernel s_pre μ_l * μ_l s_last)
            else 0) := by
    unfold tightStepFactor
    rw [dif_pos h_ewp, dif_pos h_prev_term, dif_pos h_e_term]
    set e_prev_list : List (Label × State) := e_prev.trans.toList h_prev_term
      with h_eprev_list_def
    set e_list : List (Label × State) := e.trans.toList h_e_term with h_e_list_def
    -- Compute e_list = e_prev_list ++ [(l_last, s_last)].
    have h_single_term : (Seq.cons (l_last, s_last) Seq.nil :
        Seq (Label × State)).Terminates :=
      Seq.terminates_cons_iff.mpr Seq.terminates_nil
    have h_app_term :
        (e_prev.trans.append (Seq.cons (l_last, s_last) Seq.nil)).Terminates := by
      rw [← h_struct]; exact h_e_term
    have h_e_toList :
        e_list = e_prev_list ++ [(l_last, s_last)] := by
      have h_lhs :
          e.trans.toList h_e_term =
            (e_prev.trans.append (Seq.cons (l_last, s_last) Seq.nil)).toList
              h_app_term := by
        congr 1
      rw [h_e_list_def, h_lhs,
        Seq.toList_append e_prev.trans _ h_prev_term h_single_term,
        Seq.toList_cons h_single_term, Seq.toList_nil, ← h_eprev_list_def]
    have h_take_eq : e_list.take e_prev_list.length = e_prev_list := by
      rw [h_e_toList]; simp
    have h_prefix_pos : e_prev.init = e.init ∧
        e_list.take e_prev_list.length = e_prev_list := ⟨h_init, h_take_eq⟩
    rw [dif_pos h_prefix_pos]
    -- The chain is `[(l_last, s_last)]`.
    have h_chain_eq :
        e_list.drop e_prev_list.length = [(l_last, s_last)] := by
      rw [h_e_toList]; simp
    -- Per-μ reduction.
    refine tsum_congr (fun μ => ?_)
    congr 1
    by_cases h_supp : some (l_last, μ) ∈ (pe'.scheduler.next e_w_pre).support
    swap
    · rw [dif_neg h_supp, dif_neg h_supp]
    rw [dif_pos h_supp, dif_pos h_supp]
    rw [dif_neg h_ext]
    rw [h_chain_eq]
    -- The match on `[(l_last, s_last)].getLast? = some (l_last, s_last)`,
    -- the inner `if last_pair.1 = l_last` (true), the inner
    -- `if ∀ pair ∈ [].dropLast, ...` (vacuous), all reduce.
    -- chainProb σ_pre ⟨s_pre, nil⟩ [] = σ_pre.next ⟨s_pre, nil⟩ none by def.
    -- s_mid_pre = (none.map Prod.snd).getD s_pre = s_pre.
    simp only [List.getLast?_singleton, List.dropLast_singleton, List.not_mem_nil,
      IsEmpty.forall_iff, if_true,
      List.getLast?_nil, Option.map_none, Option.getD_none]
    rw [if_pos (fun _ => trivial)]
    -- chainProb σ_pre ⟨s_pre, nil⟩ [] = σ_pre.next ⟨s_pre, nil⟩ none by def.
    rfl
  rw [h_LHS_reduced]
  -- **Phase B.2: RHS reduction.** Unfold iterOutcome at e_w_pre (terminating),
  -- expand the outer bind via PMF.bind_apply, identify the three emit-cases,
  -- and use σ_pre.internal_only to discard the internal-sub_emit contributions
  -- (which have d = PMF.pure sub_lμ with sub_lμ.1 internal ≠ l_last external,
  -- so d (l_last, μ) = 0). The remaining mass is the sub_emit = none branch,
  -- producing visible((kernel s_pre).map (· ↦ (l_last, ·))) — and PMF.map_apply
  -- on the injective embedding recovers `(kernel s_pre) μ`, matching the LHS.
  --
  -- The full reduction requires Fubini (ENNReal.tsum_comm) to swap μ- and
  -- d-/emit-tsums, and PMF.bind_apply applied at two layers (outer scheduler
  -- and inner σ_pre.next ⟨s_pre, nil⟩).
  --
  -- **RHS reduction.** Unfold iterOutcome at terminating e_w_pre.
  -- Step 1: Compute, for fixed `μ`, the inner `d`-sum
  --   `∑' d, iterOutcome ... (visible d) * d (l_last, μ)`
  -- by expanding `iterOutcome` via PMF.bind_apply over the scheduler's emit,
  -- splitting via tsum_option_split_none_some, and identifying which sub-cases
  -- contribute to `d (l_last, μ)` (non-zero).
  --
  -- For each fixed μ, we transform the RHS via:
  --   ∑' d, ((scheduler.next).bind body) (visible d) * d (l_last, μ)
  --     = ∑' emit, scheduler emit * ∑' d, body emit (visible d) * d (l_last, μ)
  -- After splitting on emit:
  -- * emit = none → body none = PMF.pure halt → coordinate at visible d = 0.
  -- * emit = some lμ outside support → body = PMF.pure halt → 0.
  -- * emit = some lμ in support, sys.internal lμ.1 → d = PMF.pure sub_lμ with
  --   sub_lμ.1 internal ≠ l_last (external) → d (l_last, μ) = 0. (Uses
  --   WeakScheduler.internal_only for the σ.emit branch; the σ.halt branch
  --   produces PMF.pure stutter, irrelevant for visible d.)
  -- * emit = some lμ in support, ¬sys.internal lμ.1 → external case.
  --   Within external, expand σ_pre.next.bind:
  --   - sub_emit = none → d = (kernel s_pre).map (fun μ_l ↦ (lμ.1, μ_l)). Mass
  --     at (l_last, μ) is, by PMF.map_apply on the injective embedding,
  --     `[lμ.1 = l_last] · (kernel s_pre) μ`.
  --   - sub_emit = some sub_lμ → d = PMF.pure sub_lμ with sub_lμ.1 internal
  --     (via σ_pre.internal_only) ≠ l_last → mass at (l_last, μ) = 0.
  -- Finally, the surviving (external, sub_emit = none) branch concentrates
  -- on lμ.1 = l_last (the only label where mass is positive), yielding the
  -- canonical form matching LHS.
  set σ_next := pe'.scheduler.next e_w_pre with h_σ_next_def
  -- Step 1: Move tsums under one another and use PMF.bind_apply at iterOutcome.
  -- We first compute for fixed μ the d-sum, then assemble.
  conv_rhs => rw [ENNReal.tsum_comm]
  -- Now: ∑' d, ∑' μ, iter ... (visible d) * d (l_last, μ) * μ s_last
  -- We want to expand `iter (visible d)` via PMF.bind_apply.
  have h_iter_unfold : iterOutcome sys pe' e_w_pre e_prev =
      (σ_next).bind fun emit =>
        emit.elim (PMF.pure AlgoStepOutcome.halt)
          (fun lμ =>
            if h_supp : some lμ ∈ σ_next.support then
              have h_sw : sys^w.step s_pre lμ.1 lμ.2 :=
                pe'.scheduler.valid e_w_pre (Nat.find h_ewp) s_pre
                  (Nat.find_spec h_ewp)
                  (AlterSeq.stateAt_find_eq_endState e_w_pre h_ewp)
                  lμ.1 lμ.2 h_supp
              if h_int : sys.internal lμ.1 then
                have h_wt : weakTau sys (PMF.pure s_pre) lμ.2 := by
                  rcases h_sw with ⟨_, h⟩ | ⟨h_ext, _⟩
                  · exact h
                  · exact absurd h_int h_ext
                (h_wt.witness.next ⟨s_pre, Seq.nil⟩).bind fun sub_emit =>
                  sub_emit.elim
                    (PMF.pure AlgoStepOutcome.stutter)
                    (fun sub_lμ =>
                      PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ)))
              else
                have h_ws : weakStep sys (PMF.pure s_pre) lμ.1 lμ.2 := by
                  rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
                  · exact absurd h_int' h_int
                  · exact h
                (h_ws.weakTau_pre.witness.next ⟨s_pre, Seq.nil⟩).bind fun sub_emit =>
                  sub_emit.elim
                    (PMF.pure (AlgoStepOutcome.visible
                      ((h_ws.hyperStep_mid.kernel s_pre).map (fun μ_l => (lμ.1, μ_l)))))
                    (fun sub_lμ =>
                      PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ)))
            else
              PMF.pure AlgoStepOutcome.halt) := by
    unfold iterOutcome
    rw [dif_pos h_ewp]
  -- Step 2: Define an abbreviation `body` for the bind-body to manage notation.
  -- Then state and prove the canonical reduction goal more concretely.
  set body : Option (Label × PMF State) → PMF (AlgoStepOutcome Label State) := fun emit =>
    emit.elim (PMF.pure AlgoStepOutcome.halt)
      (fun lμ =>
        if h_supp : some lμ ∈ σ_next.support then
          have h_sw : sys^w.step s_pre lμ.1 lμ.2 :=
            pe'.scheduler.valid e_w_pre (Nat.find h_ewp) s_pre
              (Nat.find_spec h_ewp)
              (AlterSeq.stateAt_find_eq_endState e_w_pre h_ewp)
              lμ.1 lμ.2 h_supp
          if h_int : sys.internal lμ.1 then
            have h_wt : weakTau sys (PMF.pure s_pre) lμ.2 := by
              rcases h_sw with ⟨_, h⟩ | ⟨h_ext, _⟩
              · exact h
              · exact absurd h_int h_ext
            (h_wt.witness.next ⟨s_pre, Seq.nil⟩).bind fun sub_emit =>
              sub_emit.elim (PMF.pure AlgoStepOutcome.stutter)
                (fun sub_lμ =>
                  PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ)))
          else
            have h_ws : weakStep sys (PMF.pure s_pre) lμ.1 lμ.2 := by
              rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
              · exact absurd h_int' h_int
              · exact h
            (h_ws.weakTau_pre.witness.next ⟨s_pre, Seq.nil⟩).bind fun sub_emit =>
              sub_emit.elim
                (PMF.pure (AlgoStepOutcome.visible
                  ((h_ws.hyperStep_mid.kernel s_pre).map (fun μ_l => (lμ.1, μ_l)))))
                (fun sub_lμ =>
                  PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ)))
        else PMF.pure AlgoStepOutcome.halt) with h_body_def
  have h_iter_unfold' : iterOutcome sys pe' e_w_pre e_prev = σ_next.bind body :=
    h_iter_unfold
  clear h_iter_unfold
  symm
  conv_lhs => rw [show iterOutcome sys pe' e_w_pre e_prev = _ from h_iter_unfold']
  -- Apply PMF.bind_apply at outer bind. Targeted at σ_next.bind body.
  conv_lhs =>
    rw [show (∑' (b : PMF (Label × PMF State)) (a : PMF State),
        (σ_next.bind body) (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last) =
       ∑' (b : PMF (Label × PMF State)) (a : PMF State),
        (∑' emit, σ_next emit * body emit (AlgoStepOutcome.visible b)) *
          b (l_last, a) * a s_last from
      tsum_congr fun b => tsum_congr fun a => by rw [PMF.bind_apply]]
  -- Pull factors out, swap b and emit sums.
  have h_swap : (∑' (b : PMF (Label × PMF State)) (a : PMF State),
      (∑' emit, σ_next emit * body emit (AlgoStepOutcome.visible b)) *
        b (l_last, a) * a s_last) =
     ∑' (emit : Option (Label × PMF State)),
      σ_next emit * ∑' (b : PMF (Label × PMF State)) (a : PMF State),
        body emit (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last := by
    -- Distribute: pull `b (l_last, a) * a s_last` inside the emit-tsum.
    have h_step1 : (∑' (b : PMF (Label × PMF State)) (a : PMF State),
        (∑' emit, σ_next emit * body emit (AlgoStepOutcome.visible b)) *
          b (l_last, a) * a s_last)
        = ∑' (b : PMF (Label × PMF State)) (a : PMF State) (i : Option (Label × PMF State)),
            σ_next i * body i (AlgoStepOutcome.visible b) *
              (b (l_last, a) * a s_last) := by
      refine tsum_congr (fun b => tsum_congr (fun a => ?_))
      rw [mul_assoc, ENNReal.tsum_mul_right]
    rw [h_step1]
    -- Now swap inner a- and i- tsums (per fixed b).
    have h_swap_inner : ∀ b : PMF (Label × PMF State),
        (∑' (a : PMF State) (i : Option (Label × PMF State)),
            σ_next i * body i (AlgoStepOutcome.visible b) * (b (l_last, a) * a s_last))
          = ∑' (i : Option (Label × PMF State)) (a : PMF State),
            σ_next i * body i (AlgoStepOutcome.visible b) * (b (l_last, a) * a s_last) := by
      intro b
      exact ENNReal.tsum_comm
    simp_rw [h_swap_inner]
    -- Now: ∑' b i a, σ_next i * body i (vis b) * (b(l, a) * a s_last)
    -- Swap b- and i-tsums to get i outermost.
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun i => ?_)
    -- ⊢ ∑' b a, σ_next i * body i (vis b) * (b(l, a) * a s_last)
    --    = σ_next i * ∑' b a, body i (vis b) * b(l, a) * a s_last
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr (fun b => ?_)
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr (fun a => ?_)
    ring
  rw [h_swap]
  -- Step 3: Split emit-sum into none + some lμ via the `Option` partition.
  have tsum_option_split : ∀ (f : Option (Label × PMF State) → ENNReal),
      ∑' o : Option (Label × PMF State), f o = f none + ∑' a, f (some a) := by
    intro f
    rw [← (Equiv.optionEquivSumPUnit.{0, _} (Label × PMF State)).symm.tsum_eq f]
    rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
    rw [add_comm]
    congr 1
    rw [tsum_eq_single (b := (⟨⟩ : PUnit))]
    · rfl
    · rintro ⟨⟩ h; exact (h rfl).elim
  rw [tsum_option_split (fun emit =>
    σ_next emit *
      ∑' (b : PMF (Label × PMF State)) (a : PMF State),
        body emit (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last)]
  -- The none-term: σ_next none * ∑' b a, (PMF.pure halt) (visible b) * b(l, a) * a s_last.
  -- (PMF.pure halt) (visible b) = 0 since halt ≠ visible b. So none-term = 0.
  have h_none_zero : ∀ b : PMF (Label × PMF State),
      (body none) (AlgoStepOutcome.visible b) = 0 := by
    intro b
    rw [h_body_def]
    simp [PMF.pure_apply]
  have h_none_term :
      σ_next none *
        ∑' (b : PMF (Label × PMF State)) (a : PMF State),
          (body none) (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last = 0 := by
    rw [show
      (∑' (b : PMF (Label × PMF State)) (a : PMF State),
          (body none) (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last) = 0 from by
      refine (ENNReal.tsum_eq_zero).mpr (fun b => ?_)
      rw [h_none_zero b]
      simp]
    simp
  rw [h_none_term, zero_add]
  -- Step 4: Split the tsum over `Label × PMF State` into a double tsum, then
  -- for each `(l, μ)` compute the inner d-sum.
  rw [ENNReal.tsum_prod']
  -- ⊢ ∑' l μ, σ_next (some (l, μ)) * (inner d-sum) = ∑' μ, σ_next (some (l_last, μ)) * (LHS inner)
  -- Claim: for each (l, μ), σ_next (some (l, μ)) * (inner d-sum) equals
  -- LHS-inner(μ) if l = l_last, else 0.
  -- Then collapse the l-tsum via `tsum_eq_single` at l_last.
  have h_inner_at_l : ∀ (l : Label) (μ : PMF State),
      σ_next (some (l, μ)) *
        ∑' (b : PMF (Label × PMF State)) (a : PMF State),
          body (some (l, μ)) (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last =
      (if l = l_last then
        σ_next (some (l_last, μ)) *
          (if h_supp : some (l_last, μ) ∈ σ_next.support then
            have h_sw : sys^w.step s_pre l_last μ :=
              pe'.scheduler.valid e_w_pre (Nat.find h_ewp) s_pre
                (Nat.find_spec h_ewp)
                (AlterSeq.stateAt_find_eq_endState e_w_pre h_ewp)
                l_last μ h_supp
            have h_ws : weakStep sys (PMF.pure s_pre) l_last μ := by
              rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
              · exact absurd h_int' h_ext
              · exact h
            h_ws.weakTau_pre.witness.next ⟨s_pre, Seq.nil⟩ none *
              ∑' μ_l : PMF State, h_ws.hyperStep_mid.kernel s_pre μ_l * μ_l s_last
           else 0)
       else 0) := by
    intro l μ
    -- Case-split on support membership.
    by_cases h_supp : some (l, μ) ∈ σ_next.support
    swap
    · -- Not in support: σ_next (some (l, μ)) = 0, so LHS = 0.
      have h_zero : σ_next (some (l, μ)) = 0 :=
        by rwa [PMF.mem_support_iff, not_not] at h_supp
      rw [h_zero, zero_mul]
      -- RHS: if l = l_last then σ_next * Y else 0. If l ≠ l_last, RHS = 0.
      -- If l = l_last, σ_next (some (l_last, μ)) = 0.
      by_cases hl : l = l_last
      · subst hl
        rw [if_pos rfl, h_zero, zero_mul]
      · rw [if_neg hl]
    -- In support: rewrite body (some (l, μ)) (visible b).
    -- body (some (l, μ)) = if h_int then σ.bind(...) else σ_pre.bind(...).
    rw [h_body_def]
    simp only [Option.elim_some, dif_pos h_supp]
    -- Now split on sys.internal l.
    by_cases h_int : sys.internal l
    · -- Internal case: l is internal, so l ≠ l_last (external), so RHS = 0.
      -- LHS: witness produces sub_lμ with sub_lμ.1 internal ≠ l_last,
      -- so d (l_last, μ) = 0 in every branch. Hence d-sum = 0, LHS = 0.
      have hl_ne : l ≠ l_last := fun h => h_ext (h ▸ h_int)
      rw [if_neg hl_ne]
      -- Abstract the witness: extract h_wt out of the case-split.
      have h_sw : sys^w.step s_pre l μ :=
        pe'.scheduler.valid e_w_pre (Nat.find h_ewp) s_pre
          (Nat.find_spec h_ewp)
          (AlterSeq.stateAt_find_eq_endState e_w_pre h_ewp)
          l μ h_supp
      have h_wt : weakTau sys (PMF.pure s_pre) μ := by
        rcases h_sw with ⟨_, h⟩ | ⟨h_ext', _⟩
        · exact h
        · exact absurd h_int h_ext'
      simp only [dif_pos h_int]
      rw [mul_eq_zero]; right
      -- Now show: ∑' b a, ((σ_wt.next ⟨s_pre, nil⟩).bind ...) (vis b) * b(l_last, a) * a s_last =0.
      -- The opaque σ_wt is some WeakScheduler. Use a helper that works for any WeakScheduler.
      have h_aux : ∀ (σ : WeakScheduler sys),
          ∑' (b : PMF (Label × PMF State)) (a : PMF State),
            ((σ.next ⟨s_pre, Seq.nil⟩).bind fun sub_emit =>
              sub_emit.elim (PMF.pure AlgoStepOutcome.stutter)
                (fun sub_lμ => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ))))
              (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last = 0 := by
        intro σ
        -- Reduce ((σ.next).bind ...) (vis b) via PMF.bind_apply per b.
        -- = ∑' sub_emit, σ.next sub_emit * branch sub_emit (vis b)
        -- After splitting and reducing, the d-sum factors as:
        -- ∑' sub_lμ, σ.next (some sub_lμ) * (PMF.pure sub_lμ)(l_last, sub_lμ.2) * sub_lμ.2 s_last
        --   (after collapsing b = PMF.pure sub_lμ and a = sub_lμ.2)
        -- And (PMF.pure sub_lμ)(l_last, sub_lμ.2) = [sub_lμ.1 = l_last]. internal_only ⇒ = 0.
        -- Plan: swap b,a tsum with sub_emit tsum, collapse, use internal_only.
        simp_rw [PMF.bind_apply]
        -- ∑' b a, (∑' sub_emit, σ.next sub_emit * branch sub_emit (vis b)) * b(l_last,a) * a s_last
        -- Swap and pull σ.next (some sub_lμ) out.
        rw [show (∑' (b : PMF (Label × PMF State)) (a : PMF State),
              (∑' sub_emit, σ.next ⟨s_pre, Seq.nil⟩ sub_emit *
                (sub_emit.elim (PMF.pure AlgoStepOutcome.stutter)
                  (fun sub_lμ => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ))))
                (AlgoStepOutcome.visible b)) * b (l_last, a) * a s_last) =
            ∑' (sub_emit : Option (Label × PMF State)),
              σ.next ⟨s_pre, Seq.nil⟩ sub_emit *
                ∑' (b : PMF (Label × PMF State)) (a : PMF State),
                  (sub_emit.elim (PMF.pure AlgoStepOutcome.stutter)
                    (fun sub_lμ => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ))))
                  (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last from by
          -- Same as h_swap pattern.
          have h_step1' : (∑' (b : PMF (Label × PMF State)) (a : PMF State),
              (∑' sub_emit, σ.next ⟨s_pre, Seq.nil⟩ sub_emit *
                (sub_emit.elim (PMF.pure AlgoStepOutcome.stutter)
                  (fun sub_lμ => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ))))
                (AlgoStepOutcome.visible b)) * b (l_last, a) * a s_last) =
              ∑' (b : PMF (Label × PMF State)) (a : PMF State)
                (sub_emit : Option (Label × PMF State)),
                σ.next ⟨s_pre, Seq.nil⟩ sub_emit *
                  (sub_emit.elim (PMF.pure AlgoStepOutcome.stutter)
                    (fun sub_lμ => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ))))
                  (AlgoStepOutcome.visible b) *
                (b (l_last, a) * a s_last) := by
            refine tsum_congr (fun b => tsum_congr (fun a => ?_))
            rw [mul_assoc, ENNReal.tsum_mul_right]
          rw [h_step1']
          have h_swap' : ∀ b : PMF (Label × PMF State),
              (∑' (a : PMF State) (sub_emit : Option (Label × PMF State)),
                σ.next ⟨s_pre, Seq.nil⟩ sub_emit *
                  (sub_emit.elim (PMF.pure AlgoStepOutcome.stutter)
                    (fun sub_lμ => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ))))
                  (AlgoStepOutcome.visible b) *
                (b (l_last, a) * a s_last))
                = ∑' (sub_emit : Option (Label × PMF State)) (a : PMF State),
                  σ.next ⟨s_pre, Seq.nil⟩ sub_emit *
                    (sub_emit.elim (PMF.pure AlgoStepOutcome.stutter)
                      (fun sub_lμ => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ))))
                    (AlgoStepOutcome.visible b) *
                  (b (l_last, a) * a s_last) := by
            intro _; exact ENNReal.tsum_comm
          simp_rw [h_swap']
          rw [ENNReal.tsum_comm]
          refine tsum_congr (fun sub_emit => ?_)
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr (fun b => ?_)
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr (fun a => ?_)
          ring]
        -- After splitting tsum over Option:
        rw [tsum_option_split (fun sub_emit =>
          σ.next ⟨s_pre, Seq.nil⟩ sub_emit *
            ∑' (b : PMF (Label × PMF State)) (a : PMF State),
              (sub_emit.elim (PMF.pure AlgoStepOutcome.stutter)
                (fun sub_lμ => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ))))
              (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last)]
        -- none-term: (PMF.pure stutter)(vis b) = 0, so contributions are 0.
        have h_none_zero' :
            (σ.next ⟨s_pre, Seq.nil⟩) none *
              ∑' (b : PMF (Label × PMF State)) (a : PMF State),
                ((none : Option (Label × PMF State)).elim (PMF.pure AlgoStepOutcome.stutter)
                  (fun sub_lμ => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ))))
                  (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last = 0 := by
          simp [PMF.pure_apply]
        rw [h_none_zero', zero_add]
        -- ∑' sub_lμ, σ.next (some sub_lμ) * ∑ b a, (PMF.pure (vis (PMF.pure sub_lμ)))(vis b)
        --                                 * b(l, a) * a s_last
        -- (PMF.pure (vis (PMF.pure sub_lμ)))(vis b) = [vis b = vis (PMF.pure sub_lμ)]
        --                                           = [b = PMF.pure sub_lμ].
        -- So inner sum = (PMF.pure sub_lμ)(l_last, sub_lμ.2) * sub_lμ.2 s_last (after collapse).
        -- But (PMF.pure sub_lμ)(l_last, sub_lμ.2) = [(l_last, sub_lμ.2) = sub_lμ]
        --                                         = [sub_lμ.1 = l_last ∧ sub_lμ.2 = sub_lμ.2]
        --                                         = [sub_lμ.1 = l_last].
        -- internal_only: sub_lμ.1 internal ≠ l_last (h_ext), so [sub_lμ.1 = l_last] = 0 on support.
        refine (ENNReal.tsum_eq_zero).mpr (fun sub_lμ => ?_)
        rw [mul_eq_zero]
        by_cases h_supp' : σ.next ⟨s_pre, Seq.nil⟩ (some sub_lμ) = 0
        · left; exact h_supp'
        · right
          -- σ.next (some sub_lμ) ≠ 0, so sub_lμ ∈ support, hence sub_lμ.1 internal by internal_only
          have h_sub_supp : some sub_lμ ∈ (σ.next ⟨s_pre, Seq.nil⟩).support :=
            by rwa [PMF.mem_support_iff]
          have h_sub_int : sys.internal sub_lμ.1 :=
            σ.internal_only ⟨s_pre, Seq.nil⟩ sub_lμ.1 sub_lμ.2 h_sub_supp
          have h_sub_ne : sub_lμ.1 ≠ l_last := fun heq => h_ext (heq ▸ h_sub_int)
          -- Now the inner sum: ∑ b a, (PMF.pure (vis (PMF.pure sub_lμ)))(vis b) * b(l, a)
          --                                                                     * a s_last
          -- = (sub_lμ values force b = PMF.pure sub_lμ and a = sub_lμ.2 contribution),
          -- and (PMF.pure sub_lμ)(l_last, sub_lμ.2) = 0 since sub_lμ.1 ≠ l_last.
          refine (ENNReal.tsum_eq_zero).mpr (fun b => ?_)
          refine (ENNReal.tsum_eq_zero).mpr (fun a => ?_)
          -- (PMF.pure (vis (PMF.pure sub_lμ)))(vis b) = [vis b = vis (PMF.pure sub_lμ)].
          -- = [b = PMF.pure sub_lμ].
          change (PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ)) : PMF _)
                  (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last = 0
          rw [PMF.pure_apply]
          by_cases h_b_eq : AlgoStepOutcome.visible b = AlgoStepOutcome.visible (PMF.pure sub_lμ)
          · rw [if_pos h_b_eq]
            have h_b_eq' : b = PMF.pure sub_lμ := by injection h_b_eq
            subst h_b_eq'
            -- (PMF.pure sub_lμ)(l_last, a) = 0
            -- since sub_lμ ≠ (l_last, a) (sub_lμ.1 internal ≠ l_last).
            rw [PMF.pure_apply]
            have : (l_last, a) ≠ sub_lμ := by
              intro heq
              apply h_sub_ne
              rw [← heq]
            rw [if_neg this]
            ring
          · rw [if_neg h_b_eq]; ring
      apply h_aux
    · -- External case.
      simp only [dif_neg h_int]
      -- Extract h_ws and abstract.
      have h_sw : sys^w.step s_pre l μ :=
        pe'.scheduler.valid e_w_pre (Nat.find h_ewp) s_pre
          (Nat.find_spec h_ewp)
          (AlterSeq.stateAt_find_eq_endState e_w_pre h_ewp)
          l μ h_supp
      have h_ws : weakStep sys (PMF.pure s_pre) l μ := by
        rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
        · exact absurd h_int' h_int
        · exact h
      -- Generic helper: ∑' b a, ((σ_pre.next).bind sub_branch_ext) (vis b) * b(l, a) * a s_last
      -- For each label l, this depends on whether l = l_last
      -- which determines if the map-mass is positive.
      -- We compute this generically.
      have h_aux_ext : ∀ (σ_pre : WeakScheduler sys) (kernel : State → PMF (PMF State)),
          ∑' (b : PMF (Label × PMF State)) (a : PMF State),
            ((σ_pre.next ⟨s_pre, Seq.nil⟩).bind fun sub_emit =>
              sub_emit.elim
                (PMF.pure (AlgoStepOutcome.visible
                  ((kernel s_pre).map (fun μ_l => (l, μ_l)))))
                (fun sub_lμ => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ))))
              (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last =
          if l = l_last then σ_pre.next ⟨s_pre, Seq.nil⟩ none *
            ∑' μ_l : PMF State, kernel s_pre μ_l * μ_l s_last
          else 0 := by
        intro σ_pre kernel
        -- Compute via bind_apply, split sub_emit none/some.
        simp_rw [PMF.bind_apply]
        -- Same swap pattern as before.
        rw [show (∑' (b : PMF (Label × PMF State)) (a : PMF State),
              (∑' sub_emit, σ_pre.next ⟨s_pre, Seq.nil⟩ sub_emit *
                (sub_emit.elim
                  (PMF.pure (AlgoStepOutcome.visible
                    ((kernel s_pre).map (fun μ_l => (l, μ_l)))))
                  (fun sub_lμ => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ))))
                (AlgoStepOutcome.visible b)) * b (l_last, a) * a s_last) =
            ∑' (sub_emit : Option (Label × PMF State)),
              σ_pre.next ⟨s_pre, Seq.nil⟩ sub_emit *
                ∑' (b : PMF (Label × PMF State)) (a : PMF State),
                  (sub_emit.elim
                    (PMF.pure (AlgoStepOutcome.visible
                      ((kernel s_pre).map (fun μ_l => (l, μ_l)))))
                    (fun sub_lμ => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ))))
                  (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last from by
          have h_step1'' : (∑' (b : PMF (Label × PMF State)) (a : PMF State),
              (∑' sub_emit, σ_pre.next ⟨s_pre, Seq.nil⟩ sub_emit *
                (sub_emit.elim
                  (PMF.pure (AlgoStepOutcome.visible
                    ((kernel s_pre).map (fun μ_l => (l, μ_l)))))
                  (fun sub_lμ => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ))))
                (AlgoStepOutcome.visible b)) * b (l_last, a) * a s_last) =
              ∑' (b : PMF (Label × PMF State)) (a : PMF State)
                (sub_emit : Option (Label × PMF State)),
                σ_pre.next ⟨s_pre, Seq.nil⟩ sub_emit *
                  (sub_emit.elim
                    (PMF.pure (AlgoStepOutcome.visible
                      ((kernel s_pre).map (fun μ_l => (l, μ_l)))))
                    (fun sub_lμ => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ))))
                  (AlgoStepOutcome.visible b) *
                (b (l_last, a) * a s_last) := by
            refine tsum_congr (fun b => tsum_congr (fun a => ?_))
            rw [mul_assoc, ENNReal.tsum_mul_right]
          rw [h_step1'']
          have h_swap'' : ∀ b : PMF (Label × PMF State),
              (∑' (a : PMF State) (sub_emit : Option (Label × PMF State)),
                σ_pre.next ⟨s_pre, Seq.nil⟩ sub_emit *
                  (sub_emit.elim
                    (PMF.pure (AlgoStepOutcome.visible
                      ((kernel s_pre).map (fun μ_l => (l, μ_l)))))
                    (fun sub_lμ => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ))))
                  (AlgoStepOutcome.visible b) *
                (b (l_last, a) * a s_last))
                = ∑' (sub_emit : Option (Label × PMF State)) (a : PMF State),
                  σ_pre.next ⟨s_pre, Seq.nil⟩ sub_emit *
                    (sub_emit.elim
                      (PMF.pure (AlgoStepOutcome.visible
                        ((kernel s_pre).map (fun μ_l => (l, μ_l)))))
                      (fun sub_lμ => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ))))
                    (AlgoStepOutcome.visible b) *
                  (b (l_last, a) * a s_last) := by
            intro _; exact ENNReal.tsum_comm
          simp_rw [h_swap'']
          rw [ENNReal.tsum_comm]
          refine tsum_congr (fun sub_emit => ?_)
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr (fun b => ?_)
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr (fun a => ?_)
          ring]
        -- Split none/some.
        rw [tsum_option_split (fun sub_emit =>
          σ_pre.next ⟨s_pre, Seq.nil⟩ sub_emit *
            ∑' (b : PMF (Label × PMF State)) (a : PMF State),
              (sub_emit.elim
                (PMF.pure (AlgoStepOutcome.visible
                  ((kernel s_pre).map (fun μ_l => (l, μ_l)))))
                (fun sub_lμ => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ))))
              (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last)]
        -- None-term: σ_pre.next none * ∑' b a, (PMF.pure (vis (kernel.map))) (vis b)
        --                            * b(l_last, a) * a s_last
        -- = σ_pre.next none * ∑' b a, [b = (kernel s_pre).map (fun μ_l => (l, μ_l))]
        --                   * b(l_last, a) * a s_last
        -- For l = l_last: collapse b at the map; (kernel.map ...)(l_last, a) = (kernel s_pre) a.
        -- For l ≠ l_last: (kernel.map ...)(l_last, a) = 0.
        -- Some-term: σ_pre.internal_only ⇒ sub_lμ.1 internal ≠ l_last ⇒ 0 always.
        -- Compute the none-term and the some-term.
        have h_some_zero :
            ∑' (sub_lμ : Label × PMF State),
              σ_pre.next ⟨s_pre, Seq.nil⟩ (some sub_lμ) *
                ∑' (b : PMF (Label × PMF State)) (a : PMF State),
                  ((some sub_lμ).elim
                    (PMF.pure (AlgoStepOutcome.visible
                      ((kernel s_pre).map (fun μ_l => (l, μ_l)))))
                    (fun sub_lμ' => PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ'))))
                  (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last = 0 := by
          refine (ENNReal.tsum_eq_zero).mpr (fun sub_lμ => ?_)
          rw [mul_eq_zero]
          by_cases h_supp' : σ_pre.next ⟨s_pre, Seq.nil⟩ (some sub_lμ) = 0
          · left; exact h_supp'
          · right
            have h_sub_supp : some sub_lμ ∈ (σ_pre.next ⟨s_pre, Seq.nil⟩).support :=
              by rwa [PMF.mem_support_iff]
            have h_sub_int : sys.internal sub_lμ.1 :=
              σ_pre.internal_only ⟨s_pre, Seq.nil⟩ sub_lμ.1 sub_lμ.2 h_sub_supp
            have h_sub_ne : sub_lμ.1 ≠ l_last := fun heq => h_ext (heq ▸ h_sub_int)
            refine (ENNReal.tsum_eq_zero).mpr (fun b => ?_)
            refine (ENNReal.tsum_eq_zero).mpr (fun a => ?_)
            change (PMF.pure (AlgoStepOutcome.visible (PMF.pure sub_lμ)) : PMF _)
                  (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last = 0
            rw [PMF.pure_apply]
            by_cases h_b_eq : AlgoStepOutcome.visible b = AlgoStepOutcome.visible (PMF.pure sub_lμ)
            · rw [if_pos h_b_eq]
              have h_b_eq' : b = PMF.pure sub_lμ := by injection h_b_eq
              subst h_b_eq'
              rw [PMF.pure_apply]
              have : (l_last, a) ≠ sub_lμ := by
                intro heq; apply h_sub_ne; rw [← heq]
              rw [if_neg this]; ring
            · rw [if_neg h_b_eq]; ring
        rw [h_some_zero, add_zero]
        -- None-term: σ_pre.next none * ∑' b a, (PMF.pure (vis (kernel.map))) (vis b)
        --                            * b(l_last, a) * a s_last
        change σ_pre.next ⟨s_pre, Seq.nil⟩ none *
              ∑' (b : PMF (Label × PMF State)) (a : PMF State),
                (PMF.pure
                  (AlgoStepOutcome.visible ((kernel s_pre).map (fun μ_l => (l, μ_l)))) : PMF _)
                  (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last = _
        -- (PMF.pure ...)(vis b) = [b = (kernel s_pre).map ...]. Collapse to b = that PMF.
        have h_inner_eq :
            (∑' (b : PMF (Label × PMF State)) (a : PMF State),
              (PMF.pure
                (AlgoStepOutcome.visible ((kernel s_pre).map (fun μ_l => (l, μ_l)))) : PMF _)
                (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last) =
            ∑' (a : PMF State),
              ((kernel s_pre).map (fun μ_l => (l, μ_l))) (l_last, a) * a s_last := by
          rw [tsum_eq_single (b := (kernel s_pre).map (fun μ_l => (l, μ_l)))]
          · simp [PMF.pure_apply]
          · intro b h_b_ne
            refine (ENNReal.tsum_eq_zero).mpr (fun a => ?_)
            rw [show (PMF.pure
                (AlgoStepOutcome.visible ((kernel s_pre).map (fun μ_l => (l, μ_l)))) : PMF _)
                (AlgoStepOutcome.visible b) = 0 from by
              rw [PMF.pure_apply, if_neg]
              intro heq
              apply h_b_ne
              injection heq]
            ring
        rw [h_inner_eq]
        -- ((kernel s_pre).map (fun μ_l =>
        -- (l, μ_l)))(l_last, a) = [if l = l_last then (kernel s_pre) a else 0]
        -- Actually by PMF.map_apply: ∑' μ_l, if (l_last,a) = (l,μ_l) then (kernel s_pre) μ_l else 0
        -- = if l = l_last then (kernel s_pre) a else 0.
        have h_map_apply : ∀ a : PMF State,
            ((kernel s_pre).map (fun μ_l => (l, μ_l))) (l_last, a) =
            if l = l_last then (kernel s_pre) a else 0 := by
          intro a
          rw [PMF.map_apply]
          by_cases hl : l = l_last
          · subst hl
            rw [if_pos rfl]
            -- ∑' μ_l, if (l, a) = (l, μ_l) then (kernel s_pre) μ_l else 0 = (kernel s_pre) a.
            rw [tsum_eq_single (b := a)]
            · rw [if_pos rfl]
            · intro b h_ne
              rw [if_neg]
              intro heq
              apply h_ne
              exact (Prod.mk.inj heq).2.symm
          · rw [if_neg hl]
            refine (ENNReal.tsum_eq_zero).mpr (fun _ => ?_)
            rw [if_neg]
            intro heq
            apply hl
            exact ((Prod.mk.inj heq).1).symm
        simp_rw [h_map_apply]
        by_cases hl : l = l_last
        · rw [if_pos hl]
          subst hl
          simp
        · rw [if_neg hl]
          simp [hl]
      -- Apply h_aux_ext with σ_pre = h_ws.weakTau_pre.witness
      -- and kernel = h_ws.hyperStep_mid.kernel.
      have h_apply := h_aux_ext h_ws.weakTau_pre.witness h_ws.hyperStep_mid.kernel
      rw [h_apply]
      -- ⊢ σ_next (some (l, μ)) * (if l = l_last then ... else 0) = if l = l_last then ... else 0.
      by_cases hl : l = l_last
      · subst hl
        rw [if_pos rfl, if_pos rfl]
        -- Inner: σ_next (some (l_last, μ)) * (σ_pre.next none * ∑ ...)
        -- = σ_next (some (l_last, μ)) * (if h_supp then ... else 0).
        rw [dif_pos h_supp]
      · rw [if_neg hl, if_neg hl, mul_zero]
  -- Now apply h_inner_at_l and collapse the l-tsum.
  rw [show (∑' (l : Label) (μ : PMF State),
      σ_next (some (l, μ)) *
        ∑' (b : PMF (Label × PMF State)) (a : PMF State),
          body (some (l, μ)) (AlgoStepOutcome.visible b) * b (l_last, a) * a s_last) =
    ∑' (l : Label) (μ : PMF State),
      (if l = l_last then
        σ_next (some (l_last, μ)) *
          (if h_supp : some (l_last, μ) ∈ σ_next.support then
            have h_sw : sys^w.step s_pre l_last μ :=
              pe'.scheduler.valid e_w_pre (Nat.find h_ewp) s_pre
                (Nat.find_spec h_ewp)
                (AlterSeq.stateAt_find_eq_endState e_w_pre h_ewp)
                l_last μ h_supp
            have h_ws : weakStep sys (PMF.pure s_pre) l_last μ := by
              rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
              · exact absurd h_int' h_ext
              · exact h
            h_ws.weakTau_pre.witness.next ⟨s_pre, Seq.nil⟩ none *
              ∑' μ_l : PMF State, h_ws.hyperStep_mid.kernel s_pre μ_l * μ_l s_last
           else 0)
       else 0) from
    tsum_congr (fun l => tsum_congr (fun μ => h_inner_at_l l μ))]
  -- Pull `if l = l_last` outside the inner μ-tsum.
  rw [show (∑' (l : Label) (μ : PMF State),
      (if l = l_last then
        σ_next (some (l_last, μ)) *
          (if h_supp : some (l_last, μ) ∈ σ_next.support then
            have h_sw : sys^w.step s_pre l_last μ :=
              pe'.scheduler.valid e_w_pre (Nat.find h_ewp) s_pre
                (Nat.find_spec h_ewp)
                (AlterSeq.stateAt_find_eq_endState e_w_pre h_ewp)
                l_last μ h_supp
            have h_ws : weakStep sys (PMF.pure s_pre) l_last μ := by
              rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
              · exact absurd h_int' h_ext
              · exact h
            h_ws.weakTau_pre.witness.next ⟨s_pre, Seq.nil⟩ none *
              ∑' μ_l : PMF State, h_ws.hyperStep_mid.kernel s_pre μ_l * μ_l s_last
           else 0)
       else 0)) =
    ∑' (l : Label),
      (if l = l_last then ∑' (μ : PMF State),
        σ_next (some (l_last, μ)) *
          (if h_supp : some (l_last, μ) ∈ σ_next.support then
            have h_sw : sys^w.step s_pre l_last μ :=
              pe'.scheduler.valid e_w_pre (Nat.find h_ewp) s_pre
                (Nat.find_spec h_ewp)
                (AlterSeq.stateAt_find_eq_endState e_w_pre h_ewp)
                l_last μ h_supp
            have h_ws : weakStep sys (PMF.pure s_pre) l_last μ := by
              rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
              · exact absurd h_int' h_ext
              · exact h
            h_ws.weakTau_pre.witness.next ⟨s_pre, Seq.nil⟩ none *
              ∑' μ_l : PMF State, h_ws.hyperStep_mid.kernel s_pre μ_l * μ_l s_last
           else 0)
        else 0) from
    tsum_congr (fun l => by split_ifs with h <;> simp)]
  -- Collapse l-tsum at l = l_last.
  rw [tsum_eq_single l_last (fun l h_ne => by rw [if_neg h_ne])]
  rw [if_pos rfl]

/-- **Helper.** If `totalMass e_prev = 0`, then `jointUnnorm e_prev opt = 0`
for every `opt`. Follows from `totalMass = ∑' opt, jointUnnorm e_prev opt`
and `ENNReal.tsum_eq_zero`. -/
private lemma jointUnnorm_eq_zero_of_totalMass_eq_zero
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_prev : AlterSeq State Label)
    (h_tm0 : totalMass sys pe' e_prev = 0)
    (opt : Option (Label × PMF State)) :
    jointUnnorm sys pe' e_prev opt = 0 := by
  unfold totalMass at h_tm0
  exact ENNReal.tsum_eq_zero.mp h_tm0 opt

/-- **Identity-1 + Fubini reduction** of the `reachProb · tightStepFactor`
sum to the `μ`-tsum of `jointUnnorm e_prev (some (l_last, μ)) · μ s_last`.

This packages the substitution of `tightStepFactor` via Identity 1
(`tightStepFactor_eq_iterOutcome_visible_marginal`) followed by a
`reachProb`-distribution, an `e_w_pre`/`μ` Fubini swap, factoring `μ s_last`
out of the `d`-tsum, and recognising the resulting `e_w_pre`/`d` double-sum
as `jointUnnorm e_prev (some (l_last, μ))` by definition.

The reduction holds without any case split on `totalMass`; it is used by
both the degenerate-vanishing helper (where the resulting `jointUnnorm`-sum
vanishes by `jointUnnorm_eq_zero_of_totalMass_eq_zero`) and the substantive
main-case helper (where the resulting sum is the numerator of the
`pe_of_weak.kernel` value at `(l_last, s_last)`). -/
private lemma sum_reachProb_tightStepFactor_eq_jointUnnorm_sum
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e e_prev : AlterSeq State Label)
    (h_e_term : e.trans.Terminates) (h_prev_term : e_prev.trans.Terminates)
    (l_last : Label) (s_last : State) (h_ext : ¬ sys.internal l_last)
    (h_struct : e.trans = e_prev.trans.append (Seq.cons (l_last, s_last) Seq.nil))
    (h_init : e_prev.init = e.init) :
    (∑' e_w_pre : AlterSeq State Label,
        reachProb sys pe' e_w_pre e_prev *
          tightStepFactor sys pe' e_w_pre l_last e_prev e) =
      ∑' μ : PMF State,
        jointUnnorm sys pe' e_prev (some (l_last, μ)) * μ s_last := by
  classical
  -- Step 1: Apply Identity 1 to substitute `tightStepFactor` with the
  -- `iterOutcome.visible(d) · d(l_last, μ) · μ s_last` marginal.
  have h_Id1 : ∀ e_w_pre : AlterSeq State Label,
      tightStepFactor sys pe' e_w_pre l_last e_prev e =
        ∑' μ : PMF State, ∑' d : PMF (Label × PMF State),
          iterOutcome sys pe' e_w_pre e_prev (AlgoStepOutcome.visible d) *
            d (l_last, μ) * μ s_last := fun e_w_pre =>
    tightStepFactor_eq_iterOutcome_visible_marginal sys pe' e_w_pre l_last h_ext
      e_prev h_prev_term e h_e_term s_last h_struct h_init
  -- Rewrite the LHS via Identity 1.
  conv_lhs => rw [show (∑' e_w_pre : AlterSeq State Label,
      reachProb sys pe' e_w_pre e_prev *
        tightStepFactor sys pe' e_w_pre l_last e_prev e) =
      (∑' e_w_pre : AlterSeq State Label,
        reachProb sys pe' e_w_pre e_prev *
          ∑' μ : PMF State, ∑' d : PMF (Label × PMF State),
            iterOutcome sys pe' e_w_pre e_prev (AlgoStepOutcome.visible d) *
              d (l_last, μ) * μ s_last) from
    tsum_congr (fun e_w_pre => by rw [h_Id1 e_w_pre])]
  -- Step 2: Fubini. Pull out `reachProb` into the inner sums, swap
  -- `e_w_pre` and `μ`, factor out `μ s_last`, and recognise the inner
  -- e_w_pre/d-sum as `jointUnnorm e_prev (some (l_last, μ))`.
  -- Distribute `reachProb e_w_pre *` into the `μ`- and `d`-tsums.
  have h_dist : ∀ e_w_pre : AlterSeq State Label,
      reachProb sys pe' e_w_pre e_prev *
        (∑' μ : PMF State, ∑' d : PMF (Label × PMF State),
          iterOutcome sys pe' e_w_pre e_prev (AlgoStepOutcome.visible d) *
            d (l_last, μ) * μ s_last) =
      ∑' μ : PMF State, ∑' d : PMF (Label × PMF State),
        reachProb sys pe' e_w_pre e_prev *
          (iterOutcome sys pe' e_w_pre e_prev (AlgoStepOutcome.visible d) *
            d (l_last, μ) * μ s_last) := by
    intro e_w_pre
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr (fun μ => ?_)
    rw [← ENNReal.tsum_mul_left]
  simp_rw [h_dist]
  -- Now: ∑' e_w_pre, ∑' μ, ∑' d, reachProb · (iter · d(l,μ) · μ s_last).
  -- Swap e_w_pre and μ.
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun μ => ?_)
  -- Goal: ∑' e_w_pre, ∑' d, reachProb · (iter · d(l,μ) · μ s_last)
  --       = jointUnnorm e_prev (some (l_last, μ)) * μ s_last.
  -- Pull `μ s_last` out (it doesn't depend on e_w_pre or d).
  have h_pull : ∀ e_w_pre : AlterSeq State Label,
      (∑' d : PMF (Label × PMF State),
        reachProb sys pe' e_w_pre e_prev *
          (iterOutcome sys pe' e_w_pre e_prev (AlgoStepOutcome.visible d) *
            d (l_last, μ) * μ s_last)) =
      (∑' d : PMF (Label × PMF State),
        reachProb sys pe' e_w_pre e_prev *
          (iterOutcome sys pe' e_w_pre e_prev (AlgoStepOutcome.visible d) *
            d (l_last, μ))) * μ s_last := by
    intro e_w_pre
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr (fun d => ?_)
    ring
  simp_rw [h_pull]
  rw [ENNReal.tsum_mul_right]
  -- Goal: (∑' e_w_pre, ∑' d, reachProb · (iter · d(l,μ))) * μ s_last
  --        = jointUnnorm e_prev (some (l_last, μ)) * μ s_last.
  congr 1
  -- Goal: ∑' e_w_pre, ∑' d, reachProb · (iter · d(l,μ))
  --        = jointUnnorm e_prev (some (l_last, μ)).
  unfold jointUnnorm
  refine tsum_congr (fun e_w_pre => ?_)
  rw [← ENNReal.tsum_mul_left]

/-- **Degenerate-vanishing helper for the marginal identity A base case.**

When `totalMass e_prev = 0`, the `reachProb · tightStepFactor` LHS of
`sum_reachProb_tightStepFactor_eq_jointTight_kernel` vanishes. The
`totalMass = ⊤` branch is now vacuous: `totalMass ≤ FirstReach ≤ 1 < ⊤`,
so `totalMass = ⊤` is impossible.

**Strategy.** Apply Identity-1 + Fubini to rewrite the LHS as
`∑' μ, jointUnnorm e_prev (some (l_last, μ)) * μ s_last`. In the
`totalMass = 0` branch, every `jointUnnorm` summand vanishes. In the
`totalMass = ⊤` branch, derive a contradiction from
`totalMass_le_FirstReach + FirstReach_ne_top`. -/
private lemma sum_reachProb_tightStepFactor_eq_zero_of_totalMass_degenerate
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e e_prev : AlterSeq State Label)
    (h_e_term : e.trans.Terminates) (h_prev_term : e_prev.trans.Terminates)
    (l_last : Label) (s_last : State) (h_ext : ¬ sys.internal l_last)
    (h_struct : e.trans = e_prev.trans.append (Seq.cons (l_last, s_last) Seq.nil))
    (h_init : e_prev.init = e.init)
    (h_deg : totalMass sys pe' e_prev = 0 ∨ totalMass sys pe' e_prev = ⊤) :
    (∑' e_w_pre : AlterSeq State Label,
        reachProb sys pe' e_w_pre e_prev *
          tightStepFactor sys pe' e_w_pre l_last e_prev e) = 0 := by
  classical
  rw [sum_reachProb_tightStepFactor_eq_jointUnnorm_sum sys pe' e e_prev
    h_e_term h_prev_term l_last s_last h_ext h_struct h_init]
  rcases h_deg with h_tm0 | h_tm_top
  · -- totalMass = 0: every `jointUnnorm e_prev opt = 0`.
    refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
    rw [jointUnnorm_eq_zero_of_totalMass_eq_zero sys pe' e_prev h_tm0]
    ring
  · -- totalMass = ⊤: impossible since `totalMass ≤ FirstReach < ⊤`.
    exfalso
    apply FirstReach_ne_top sys pe' e_prev
    exact le_antisymm le_top (h_tm_top ▸ totalMass_le_FirstReach sys pe' e_prev)

/-! **Retired (Phase 2):** the `totalMass`-denominator conservation chain
(`totalMass_nil_eq_initState`, `sum_jointTight_eq_totalMass_nil`,
`sum_jointTight_eq_totalMass_step`, `sum_jointTight_eq_totalMass`, and the
totalMass-version `sum_reachProb_tightStepFactor_eq_jointTight_kernel_main`)
has been removed. The substantive cancellation in
`sum_reachProb_tightStepFactor_eq_jointTight_kernel` now uses the
marginal-A IH at `e_prev` (`∑ jointTight = probOf`) plus
`FirstReach_eq_probOf` plus `ENNReal.mul_div_cancel`, divided by
`FirstReach e_prev` rather than `totalMass e_prev`. -/

/-- **Marginal identity A — base case, Sub-claim 2: substantive identity at
the collapse.**

After Sub-claim 1 collapses the inner sum, the LHS becomes
`∑' e_w_pre, reachProb e_w_pre e_prev * tightStepFactor e_w_pre l_last e_prev e`,
and the substantive identity is its equality with
`(∑' e_w_prev, jointTight e_w_prev e_prev) *
  (pe_of_weak sys pe').kernel ⟨e_prev.init, e_prev.trans⟩ (l_last, s_last)`.

**Proof outline.** Unfold `pe_of_weak.kernel` to
`∑' μ, (jointUnnorm e_prev (some (l_last, μ)) / totalMass e_prev) * μ s_last`,
unfold `tightStepFactor` (`chain_pre = []`, external case) to
`∑' μ, σ_pre.next e_w_pre (some (l_last, μ)) * (chainProb σ_pre · μ s_last)`,
swap the `μ`- and `e_w_pre`-sums, and use `PMF.normalize`'s definition together
with `reachProb`'s recursion at the last (external) entry of `e_prev` so that
the `totalMass e_prev` denominator cancels.

**Status:** deferred (substantive sub-sorry — the totalMass-denominator
telescoping, the heart of the marginal identity A step). -/
private lemma sum_reachProb_tightStepFactor_eq_jointTight_kernel
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e e_prev : AlterSeq State Label)
    (h_e_term : e.trans.Terminates) (h_prev_term : e_prev.trans.Terminates)
    (_h_prev_tight : sys.IsTight e_prev)
    (l_last : Label) (s_last : State) (h_ext : ¬ sys.internal l_last)
    (h_struct : e.trans = e_prev.trans.append (Seq.cons (l_last, s_last) Seq.nil))
    (h_init : e_prev.init = e.init)
    (h_IH : (∑' e_w_prev : AlterSeq State Label,
              jointTight sys pe' e_w_prev e_prev) =
            (pe_of_weak sys pe').probOf e_prev h_prev_term) :
    (∑' e_w_pre : AlterSeq State Label,
        reachProb sys pe' e_w_pre e_prev *
          tightStepFactor sys pe' e_w_pre l_last e_prev e)
      = (∑' e_w_prev : AlterSeq State Label, jointTight sys pe' e_w_prev e_prev) *
          (pe_of_weak sys pe').kernel
            ⟨e_prev.init, e_prev.trans.append (Seq.ofList [])⟩ (l_last, s_last) := by
  classical
  -- **Phase A: simplify the RHS prefix to `e_prev`.**
  have h_prefix_eq :
      (⟨e_prev.init, e_prev.trans.append (Seq.ofList [])⟩ : AlterSeq State Label) =
        e_prev := by
    rcases e_prev with ⟨i, t⟩
    dsimp
    rw [Stream'.Seq.append_nil]
  rw [h_prefix_eq]
  -- **Phase B: unfold the kernel via `pe_of_weak_kernel_eq` and case-split on
  -- `FirstReach e_prev`.** The `FirstReach = 0` branch collapses both sides
  -- to 0; the main branch is the substantive cancellation, closed via the
  -- marginal-A IH `h_IH` plus `FirstReach_eq_probOf`.
  rw [pe_of_weak_kernel_eq sys pe' e_prev l_last s_last]
  split_ifs with h_fr0 h_fr_top
  · -- Degenerate: FirstReach = 0. RHS collapses; LHS collapses via TM ≤ FR = 0.
    rw [mul_zero]
    have h_tm0 : totalMass sys pe' e_prev = 0 := by
      have h := totalMass_le_FirstReach sys pe' e_prev
      rw [h_fr0] at h
      exact le_antisymm h bot_le
    exact sum_reachProb_tightStepFactor_eq_zero_of_totalMass_degenerate
      sys pe' e e_prev h_e_term h_prev_term l_last s_last h_ext h_struct h_init
      (Or.inl h_tm0)
  · -- Degenerate: FirstReach = ⊤. Vacuous: `FirstReach = probOf ≤ pe.init ≤ 1`.
    exfalso
    have h_le : FirstReach sys pe' e_prev ≤ 1 := by
      rw [FirstReach_eq_probOf sys pe' e_prev h_prev_term]
      exact (ProbabilisticExecution.probOf_le_init _ _ h_prev_term).trans
        (PMF.coe_le_one _ _)
    exact (lt_of_le_of_lt h_le ENNReal.one_lt_top).ne h_fr_top
  · -- Main case: substantive `FirstReach`-denominator cancellation.
    rw [sum_reachProb_tightStepFactor_eq_jointUnnorm_sum sys pe' e e_prev
      h_e_term h_prev_term l_last s_last h_ext h_struct h_init]
    rw [h_IH, ← FirstReach_eq_probOf sys pe' e_prev h_prev_term]
    exact (ENNReal.mul_div_cancel h_fr0 h_fr_top).symm

/-- **Marginal identity A — kernel-chain step identity, base case** (the
substantive "internal chain is empty" identity).

When `chain_pre = []`, the iteration's chain is just `[(l_last, s_last)]`
and the e_iter_start sum in `jointTight_step_external` collapses to a single
contribution at `e_iter_start = e_prev` (tightness of `e_prev` forces this:
no shorter iter_start has the chain "drop" portion all-internal up through
the final external step). The collapsed identity, after recognising the
factor `reachProb · tightStepFactor` at `e_iter_start = e_prev` as the
`pe_of_weak`-kernel times the `jointTight`-marginal at `e_prev`, is the
substantive base case.

Assembled from two sub-claims: structural collapse to `e_iter_start = e_prev`
(`tightStepFactor_chain_pre_empty_iter_start_eq_e_prev`) and the substantive
totalMass-denominator identity at the collapse
(`sum_reachProb_tightStepFactor_eq_jointTight_kernel`). -/
private lemma jointTight_step_kernel_chain_identity_base
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e e_prev : AlterSeq State Label)
    (h_prev_term : e_prev.trans.Terminates) (h_e_term : e.trans.Terminates)
    (_h_prev_tight : sys.IsTight e_prev) (_h_e_tight : sys.IsTight e)
    (l_last : Label) (s_last : State)
    (h_struct : e.trans = e_prev.trans.append
        (Seq.ofList ([] ++ [(l_last, s_last)])))
    (_h_init : e_prev.init = e.init)
    (h_ext : ¬ sys.internal l_last)
    (h_IH : (∑' e_w_prev : AlterSeq State Label,
              jointTight sys pe' e_w_prev e_prev) =
            (pe_of_weak sys pe').probOf e_prev h_prev_term) :
    (∑' e_w_pre : AlterSeq State Label, jointTight sys pe' e_w_pre e) =
      (∑' e_w_prev : AlterSeq State Label, jointTight sys pe' e_w_prev e_prev) *
        pe_of_weak_kernel_chain sys pe' e_prev
          ([] ++ [(l_last, s_last)]) := by
  classical
  -- Simplify the chain `[] ++ [(l_last, s_last)] = [(l_last, s_last)]` and
  -- reduce `Seq.ofList [(l_last, s_last)]` to its cons-end form so we can
  -- align with `jointTight_step_external`.
  simp only [List.nil_append] at h_struct
  -- The `Seq.ofList`-form of `[(l_last, s_last)]` equals `Seq.cons (l_last, s_last) Seq.nil`.
  have h_ofList_singleton :
      (Seq.ofList [(l_last, s_last)] : Seq (Label × State)) =
        Seq.cons (l_last, s_last) Seq.nil := by
    rw [Seq.ofList_cons, Seq.ofList_nil]
  rw [h_ofList_singleton] at h_struct
  -- Apply `jointTight_step_external` to every summand of the LHS.
  have h_LHS_expand : ∀ e_w_pre : AlterSeq State Label,
      jointTight sys pe' e_w_pre e =
        ∑' e_iter_start : AlterSeq State Label,
          reachProb sys pe' e_w_pre e_iter_start *
            tightStepFactor sys pe' e_w_pre l_last e_iter_start e := by
    intro e_w_pre
    exact jointTight_step_external sys pe' e_w_pre e h_e_term
      e_prev.trans h_prev_term l_last s_last h_struct h_ext
  rw [tsum_congr h_LHS_expand]
  -- Simplify the RHS chain product to a single kernel factor.
  have h_RHS_kernel :
      pe_of_weak_kernel_chain sys pe' e_prev ([] ++ [(l_last, s_last)]) =
        (pe_of_weak sys pe').kernel
          ⟨e_prev.init, e_prev.trans.append (Seq.ofList [])⟩ (l_last, s_last) := by
    rw [pe_of_weak_kernel_chain_append_singleton, pe_of_weak_kernel_chain_nil, one_mul]
  rw [h_RHS_kernel]
  -- Goal now:
  --   ∑' e_w_pre, ∑' e_iter_start,
  --     reachProb e_w_pre e_iter_start * tightStepFactor e_w_pre l_last e_iter_start e
  --   = (∑' e_w_prev, jointTight e_w_prev e_prev) *
  --       (pe_of_weak sys pe').kernel ⟨e_prev.init, e_prev.trans.append (Seq.ofList [])⟩
  --         (l_last, s_last)
  --
  -- Sub-claim 1 collapses the inner e_iter_start sum: every contribution with
  -- `e_iter_start ≠ e_prev` has `tightStepFactor = 0` (tightness of `e_prev`
  -- forces the only non-vanishing iter_start to be `e_prev` itself).
  have h_collapse : ∀ e_w_pre : AlterSeq State Label,
      (∑' e_iter_start : AlterSeq State Label,
          reachProb sys pe' e_w_pre e_iter_start *
            tightStepFactor sys pe' e_w_pre l_last e_iter_start e) =
        reachProb sys pe' e_w_pre e_prev *
          tightStepFactor sys pe' e_w_pre l_last e_prev e := by
    intro e_w_pre
    refine tsum_eq_single e_prev (fun e_iter_start h_ne => ?_)
    rw [tightStepFactor_chain_pre_empty_iter_start_eq_e_prev sys pe' e e_prev
          h_e_term h_prev_term _h_prev_tight l_last s_last h_ext h_struct
          _h_init e_w_pre e_iter_start h_ne, mul_zero]
  rw [tsum_congr h_collapse]
  -- Sub-claim 2 closes the substantive identity (FirstReach-denominator
  -- cancellation at the collapsed term), using the marginal-A IH at `e_prev`.
  exact sum_reachProb_tightStepFactor_eq_jointTight_kernel sys pe' e e_prev
    h_e_term h_prev_term _h_prev_tight l_last s_last h_ext h_struct _h_init h_IH

/-- **Marginal identity A — kernel-chain step identity, inductive step**
(extending the internal sub-chain by one entry).

If the kernel-chain step identity holds at `chain_pre = rest`, then it
holds at `chain_pre = rest ++ [(l_int, s_int)]` provided `l_int` is
internal. The proof extracts the additional `pe_of_weak`-kernel factor
at the running prefix `⟨e_prev.init, e_prev.trans.append (Seq.ofList rest)⟩`
applied to `(l_int, s_int)`, and identifies it with the corresponding new
contribution to the e_iter_start sum in `jointTight_step_external`'s
expansion (the iter_start now extends one more internal step into the
chain).

**Status:** deferred (substantive sub-sorry). The proof requires the new
e_iter_start contribution at the extended prefix and `pe_of_weak`-kernel
matching at the same prefix. -/
private lemma jointTight_step_kernel_chain_identity_inductive_step
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e e_prev : AlterSeq State Label)
    (_h_prev_term : e_prev.trans.Terminates) (_h_e_term : e.trans.Terminates)
    (_h_prev_tight : sys.IsTight e_prev) (_h_e_tight : sys.IsTight e)
    (rest : List (Label × State)) (l_int : Label) (s_int : State)
    (l_last : Label) (s_last : State)
    (_h_struct : e.trans = e_prev.trans.append
        (Seq.ofList ((rest ++ [(l_int, s_int)]) ++ [(l_last, s_last)])))
    (_h_init : e_prev.init = e.init)
    (_h_ext : ¬ sys.internal l_last)
    (_h_int : sys.internal l_int)
    (_h_rest_int : ∀ pair ∈ rest, sys.internal pair.1)
    (_h_IH :
      ∀ (e' : AlterSeq State Label) (_ : e'.trans.Terminates)
        (_ : sys.IsTight e')
        (_ : e'.trans = e_prev.trans.append
              (Seq.ofList (rest ++ [(l_last, s_last)])))
        (_ : e_prev.init = e'.init),
      (∑' e_w_pre : AlterSeq State Label, jointTight sys pe' e_w_pre e') =
        (∑' e_w_prev : AlterSeq State Label, jointTight sys pe' e_w_prev e_prev) *
          pe_of_weak_kernel_chain sys pe' e_prev
            (rest ++ [(l_last, s_last)])) :
    (∑' e_w_pre : AlterSeq State Label, jointTight sys pe' e_w_pre e) =
      (∑' e_w_prev : AlterSeq State Label, jointTight sys pe' e_w_prev e_prev) *
        pe_of_weak_kernel_chain sys pe' e_prev
          ((rest ++ [(l_int, s_int)]) ++ [(l_last, s_last)]) := by
  sorry

/-- **Marginal identity A — kernel-chain step identity.**

The joint-tight marginal at `e` factors as the joint-tight marginal at
`e_prev` times the `pe_of_weak`-kernel product along the iteration's
internal chain plus its final external step. This is the substantive
content of the iteration step: the totalMass-denominator telescoping
(Fubini swap, `reachProb` recursion against `chainProb`, `PMF.normalize`
cancellation) packaged as a multiplicative factorisation.

The proof is by induction on `chain_pre` (the internal pre-chain), using:
* `jointTight_step_kernel_chain_identity_base` for `chain_pre = []`
  (the substantive base case);
* `jointTight_step_kernel_chain_identity_inductive_step` for the
  extension by one internal entry.

The IH-applied conclusion of
`jointTight_marginal_A_iteration_step_identity` is recovered by composing
this lemma with the IH and the structural factorisation
`pe_of_weak_probOf_chain_factorize`. -/
private lemma jointTight_step_kernel_chain_identity
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e e_prev : AlterSeq State Label)
    (h_prev_term : e_prev.trans.Terminates) (h_e_term : e.trans.Terminates)
    (h_prev_tight : sys.IsTight e_prev) (h_e_tight : sys.IsTight e)
    (chain_pre : List (Label × State)) (l_last : Label) (s_last : State)
    (h_struct : e.trans = e_prev.trans.append
        (Seq.ofList (chain_pre ++ [(l_last, s_last)])))
    (h_init : e_prev.init = e.init)
    (h_ext : ¬ sys.internal l_last)
    (h_chain_int : ∀ pair ∈ chain_pre, sys.internal pair.1)
    (h_IH : (∑' e_w_prev : AlterSeq State Label,
              jointTight sys pe' e_w_prev e_prev) =
            (pe_of_weak sys pe').probOf e_prev h_prev_term) :
    (∑' e_w_pre : AlterSeq State Label, jointTight sys pe' e_w_pre e) =
      (∑' e_w_prev : AlterSeq State Label, jointTight sys pe' e_w_prev e_prev) *
        pe_of_weak_kernel_chain sys pe' e_prev
          (chain_pre ++ [(l_last, s_last)]) := by
  -- Induct on `chain_pre` from the right.
  induction chain_pre using List.reverseRecOn generalizing e with
  | nil =>
    -- Base case: chain_pre = []. Delegate to the substantive base sub-lemma.
    exact jointTight_step_kernel_chain_identity_base sys pe' e e_prev
      h_prev_term h_e_term h_prev_tight h_e_tight l_last s_last
      h_struct h_init h_ext h_IH
  | append_singleton rest last ih =>
    have h_last_int : sys.internal last.1 := h_chain_int last (by
      rw [List.mem_append]; right; exact List.mem_singleton.mpr rfl)
    have h_rest_int : ∀ pair ∈ rest, sys.internal pair.1 := by
      intro pair hp
      exact h_chain_int pair (by rw [List.mem_append]; left; exact hp)
    obtain ⟨l_int, s_int⟩ := last
    exact jointTight_step_kernel_chain_identity_inductive_step sys pe' e e_prev
      h_prev_term h_e_term h_prev_tight h_e_tight rest l_int s_int l_last s_last
      h_struct h_init h_ext h_last_int h_rest_int
      (fun e' h_e'_term h_e'_tight h_e'_struct h_e'_init =>
        ih e' h_e'_term h_e'_tight h_e'_struct h_e'_init h_rest_int)

/-- **Marginal identity A — substantive iteration-step identity** (the
totalMass-denominator telescoping, iteration-formulated, IH-applied form).

Given:
* a tight, terminating non-empty execution `e`;
* its iteration-split decomposition
  `e.trans = e_prev.trans ++ chain_pre ++ [(l_last, s_last)]`
  (with `e_prev` tight, `chain_pre` all-internal, `l_last` external);
* the inductive hypothesis at `e_prev`:
  `∑' e_w_prev, jointTight e_w_prev e_prev = probOf e_prev`;

the joint-mass marginal at `e` equals `probOf e`.

This combines the substantive `totalMass`-denominator telescoping (Fubini
swap, `reachProb` recursion against `chainProb`, `PMF.normalize`
cancellation) with the `probOf_append` factorisation along
`chain_pre ++ [(l_last, s_last)]`. The current formulation directly
delivers the IH-applied conclusion to keep the strong-induction wrapper
purely structural.

**Status:** deferred as a focused sub-sorry. -/
private lemma jointTight_marginal_A_iteration_step_identity
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e e_prev : AlterSeq State Label)
    (h_e_term : e.trans.Terminates) (h_prev_term : e_prev.trans.Terminates)
    (h_e_tight : sys.IsTight e) (h_prev_tight : sys.IsTight e_prev)
    (chain_pre : List (Label × State)) (l_last : Label) (s_last : State)
    (h_struct : e.trans = e_prev.trans.append
        (Seq.ofList (chain_pre ++ [(l_last, s_last)])))
    (h_init : e_prev.init = e.init)
    (h_ext : ¬ sys.internal l_last)
    (h_chain_int : ∀ pair ∈ chain_pre, sys.internal pair.1)
    (h_IH : (∑' e_w_prev : AlterSeq State Label,
              jointTight sys pe' e_w_prev e_prev) =
          (pe_of_weak sys pe').probOf e_prev h_prev_term) :
    (∑' e_w_pre : AlterSeq State Label, jointTight sys pe' e_w_pre e) =
      (pe_of_weak sys pe').probOf e h_e_term := by
  -- Step 1: rewrite the LHS marginal via the substantive sub-lemma.
  rw [jointTight_step_kernel_chain_identity sys pe' e e_prev h_prev_term h_e_term
        h_prev_tight h_e_tight chain_pre l_last s_last h_struct h_init h_ext h_chain_int
        h_IH]
  -- Step 2: apply the IH to replace the marginal at e_prev.
  rw [h_IH]
  -- Step 3: rewrite RHS so that the appended trans matches the chain factorisation.
  -- We have `e.trans = e_prev.trans.append (Seq.ofList chain)` for
  -- `chain := chain_pre ++ [(l_last, s_last)]`, and `e_prev.init = e.init`,
  -- so `(pe_of_weak).probOf e h_e_term` equals
  -- `(pe_of_weak).probOf ⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩ _`.
  set chain : List (Label × State) := chain_pre ++ [(l_last, s_last)] with h_chain_def
  -- Reshape the RHS execution into the appended form.
  have h_e_eq : e = ⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩ := by
    rcases e with ⟨ei, et⟩
    dsimp at h_init h_struct
    -- h_init : e_prev.init = ei, h_struct : et = e_prev.trans.append (Seq.ofList chain).
    subst h_init
    rw [h_struct]
  -- Coerce the termination witness through `h_e_eq`.
  have h_term_app : (e_prev.trans.append (Seq.ofList chain)).Terminates := by
    have := h_e_term
    rw [h_e_eq] at this
    exact this
  -- Rewrite the RHS probOf using h_e_eq, then apply the factorisation.
  have h_probOf_eq :
      (pe_of_weak sys pe').probOf e h_e_term =
        (pe_of_weak sys pe').probOf
          ⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩ h_term_app := by
    revert h_e_term
    rw [h_e_eq]
    intro h_e_term
    rfl
  rw [h_probOf_eq]
  rw [pe_of_weak_probOf_chain_factorize sys pe' e_prev h_prev_term chain h_term_app]

/-- **Marginal identity A — internal last step is vacuous.**

If `e` is `sys`-tight and `e.trans = trans_prev ++ [(l_last, s_last)]`,
then `l_last` cannot be internal: tightness mandates an external label at
the last entry, contradicting the assumption that `l_last` is internal.

This sub-lemma factors out the "internal last step is vacuous" case from
the main induction. Proof outline: apply `tight_trans_split_last_witness`
to get `e.trans = tp' ++ [(l_ext, s_ext)]` with `¬ internal l_ext`; by
uniqueness of the last entry, `(l_ext, s_ext) = (l_last, s_last)`, so
`¬ internal l_last`. -/
private lemma not_internal_last_of_tight_append
    (sys : LabelledSystem State Label)
    (e : AlterSeq State Label) (h_e_term : e.trans.Terminates)
    (h_e_tight : sys.IsTight e)
    (trans_prev : Seq (Label × State)) (_h_prev_term : trans_prev.Terminates)
    (l_last : Label) (s_last : State)
    (h_struct : e.trans = trans_prev.append (Seq.cons (l_last, s_last) Seq.nil)) :
    ¬ sys.internal l_last := by
  classical
  -- `e.trans ≠ nil`: the RHS of `h_struct` has `(l_last, s_last)` at position
  -- `Nat.find _h_prev_term`, so it cannot be nil.
  have h_ne : e.trans ≠ Seq.nil := by
    intro h_nil
    have h_get_eq :
        e.trans.get? (Nat.find _h_prev_term)
          = some (l_last, s_last) := by
      rw [h_struct]
      have := Seq.get?_append_find _h_prev_term
        (Seq.cons (l_last, s_last) Seq.nil) 0
      simpa using this
    rw [h_nil] at h_get_eq
    simp at h_get_eq
  -- Use `tight_trans_split_last_witness` to get an external splitter.
  obtain ⟨tp', h_tp'_term, l_ext, s_ext, h_struct', h_ext⟩ :=
    tight_trans_split_last_witness sys e h_e_term h_e_tight h_ne
  -- The two appended decompositions of `e.trans` agree on the last entry by
  -- `Seq.append_singleton_inj_right`.
  have h_pair_eq : (l_ext, s_ext) = (l_last, s_last) := by
    apply Seq.append_singleton_inj_right tp' trans_prev h_tp'_term _h_prev_term
    rw [← h_struct']; exact h_struct
  -- Hence `l_ext = l_last`, so `¬ internal l_last`.
  have h_l_eq : l_ext = l_last := (Prod.mk.inj h_pair_eq).1
  rw [h_l_eq] at h_ext
  exact h_ext

/-- **Marginal identity A — strong-induction aux** parametrised by the
length of `e.trans.toList`.

For any tight, terminating execution `e`, `jointTight`'s marginal over
`e_w_pre` equals `(pe_of_weak …).probOf e`. The induction is by strong
induction on `(e.trans.toList h_e_term).length`: at the step, we use
`iteration_split_last_external` to decompose a non-empty tight `e` as
`e_prev + chain_pre + [(l_last, s_last)]` where `e_prev` is tight and
strictly shorter (so the strong IH applies at `e_prev`). The substantive
content of the step case — relating the joint-mass sum at `e` to the joint
mass sum at `e_prev` via the iteration factor — is delegated to
`jointTight_marginal_A_iteration_step_identity`.

The previous formulation using `List.reverseRecOn` on `e.trans.toList`
relied on a *false* "tightness of immediate predecessor" claim (the
prefix obtained by dropping just the last entry of a tight execution is
not generally tight — its last entry can be internal). Strong induction
on length combined with `iteration_split_last_external` is the correct
structure. -/
private lemma jointTight_marginal_A_aux
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (n : ℕ) (e : AlterSeq State Label) (h_e_term : e.trans.Terminates)
    (h_e_tight : sys.IsTight e)
    (h_len : (e.trans.toList h_e_term).length = n) :
    (∑' e_w_pre : AlterSeq State Label, jointTight sys pe' e_w_pre e) =
      (pe_of_weak sys pe').probOf e h_e_term := by
  classical
  induction n using Nat.strong_induction_on generalizing e with
  | _ n ih =>
    -- Case-split on whether `e.trans = Seq.nil`.
    by_cases h_empty : e.trans = Seq.nil
    · -- Base case: `e.trans = nil`. The marginal collapses via
      -- `jointTight_marginal_A_base` applied at `s_init := e.init`.
      have h_e_eq_nil : e = ⟨e.init, Seq.nil⟩ := by
        obtain ⟨init, trans⟩ := e
        simp only at h_empty
        subst h_empty
        rfl
      have h_base := jointTight_marginal_A_base sys pe' e.init
      -- Transport across `h_e_eq_nil`.
      conv_lhs => rw [h_e_eq_nil]
      have h_RHS_eq :
          (pe_of_weak sys pe').probOf e h_e_term =
          (pe_of_weak sys pe').probOf ⟨e.init, Seq.nil⟩ Seq.terminates_nil := by
        congr 1
      rw [h_RHS_eq]
      exact h_base
    · -- Step case: `e.trans ≠ nil`. Decompose via
      -- `iteration_split_last_external` to get a strictly shorter tight
      -- prefix `e_prev`, then apply the strong IH at `e_prev` and the
      -- iteration step identity.
      obtain ⟨e_prev, h_prev_term, chain_pre, l_last, s_last,
              h_struct, h_init, h_prev_tight, h_ext, h_chain_int, h_lt⟩ :=
        iteration_split_last_external sys e h_e_term h_e_tight h_empty
      -- Strong IH at `e_prev`: its `toList` has strictly smaller length.
      have h_IH :
          (∑' e_w_prev : AlterSeq State Label,
              jointTight sys pe' e_w_prev e_prev) =
          (pe_of_weak sys pe').probOf e_prev h_prev_term :=
        ih (e_prev.trans.toList h_prev_term).length
          (by rw [← h_len]; exact h_lt) e_prev h_prev_term h_prev_tight rfl
      -- Apply the iteration step identity in its IH-applied form.
      exact jointTight_marginal_A_iteration_step_identity sys pe' e e_prev
        h_e_term h_prev_term h_e_tight h_prev_tight chain_pre l_last s_last
        h_struct h_init h_ext h_chain_int h_IH

/-- **Marginal identity A** (the corrected sub-lemma A from §5):
summing `jointTight` over the hidden `sys^w`-side pre-iteration history
`e_w_pre` recovers `pe_of_weak`'s prefix probability at every *tight*
terminating `sys`-prefix `e`.

Intuition: every joint trajectory of the coupled algorithm reaches a
given tight `e` at exactly one inner-iteration moment (the moment
right after the visible external step at `e`'s last label, or the
initial moment for the empty `e`). The marginal over the hidden
pre-iteration `e_w_pre` therefore equals `(pe_of_weak …).probOf e`.

Structure of the proof:

1. Reduce directly to the strong-induction aux `jointTight_marginal_A_aux`
   with `n := (e.trans.toList h_e_term).length`.
2. The aux performs **strong induction on `n`**:
   * base (`e.trans = nil`) via `jointTight_marginal_A_base`;
   * step via `iteration_split_last_external` (the structural
     iteration-decomposition of a tight non-empty execution) and
     `jointTight_marginal_A_iteration_step_identity` (the substantive
     totalMass-denominator telescoping plus the chain-`probOf_append`
     factorisation, currently sorried). -/
private lemma jointTight_marginal_A
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e : AlterSeq State Label) (h_e_term : e.trans.Terminates)
    (h_tight : sys.IsTight e) :
    (∑' e_w_pre : AlterSeq State Label, jointTight sys pe' e_w_pre e) =
      (pe_of_weak sys pe').probOf e h_e_term :=
  jointTight_marginal_A_aux sys pe' (e.trans.toList h_e_term).length e h_e_term
    h_tight rfl

-- **Trace of a terminating execution terminates.** This rules out
-- contributions to either side of `extCylinderMass_sum_eq_traceProb` from
-- a non-terminating target trace `τ`.
private theorem trace_terminates_of_trans_terminates
    (ls : LabelledSystem State Label) (e : AlterSeq State Label)
    (h : e.trans.Terminates) : (ls.trace e).Terminates := by
  unfold LabelledSystem.trace
  rw [Seq.terminates_map_iff]
  exact Seq.terminates_filter _ _ h

-- **Tight-trace cylinder is empty for a non-terminating target trace.**
private lemma isEmpty_traceCylinder_of_not_terminates
    (ls : LabelledSystem State Label) (τ : Seq Label) (h_τ : ¬τ.Terminates) :
    IsEmpty {e : AlterSeq State Label //
              e.trans.Terminates ∧ ls.trace e = τ ∧ ls.IsTight e} := by
  rw [isEmpty_subtype]
  rintro e ⟨h_term, h_trace, _⟩
  apply h_τ
  rw [← h_trace]
  exact trace_terminates_of_trans_terminates ls e h_term

/-- **Tight-trace cylinder is empty when the trace ends with an internal label.**
If `τ = τ_prev ++ [l_τ]` with `sys.internal l_τ`, no execution has trace `τ`
(the trace filters out internal labels, so it never ends in one). -/
private lemma isEmpty_traceCylinder_of_internal_last
    (ls : LabelledSystem State Label)
    (τ_prev : Seq Label) (h_τ_prev_term : τ_prev.Terminates)
    (l_τ : Label) (h_l_τ_int : ls.internal l_τ) :
    IsEmpty {e : AlterSeq State Label //
              e.trans.Terminates ∧
              ls.trace e = τ_prev.append (Seq.cons l_τ Seq.nil) ∧
              ls.IsTight e} := by
  rw [isEmpty_subtype]
  rintro e ⟨h_e_term, h_e_trace, h_e_tight⟩
  -- Case-split on `e.trans = Seq.nil`.
  have h_ne : e.trans ≠ Seq.nil := by
    intro h_nil
    have h_trace_nil : ls.trace e = Seq.nil := by
      unfold LabelledSystem.trace
      rw [h_nil]; simp
    rw [h_trace_nil] at h_e_trace
    -- nil ≠ τ_prev ++ [l_τ]: the RHS has `some l_τ` at position `Nat.find h_τ_prev_term`.
    have h_get0 :
        (τ_prev.append (Seq.cons l_τ Seq.nil)).get? (Nat.find h_τ_prev_term)
          = some l_τ := by
      have := Seq.get?_append_find h_τ_prev_term (Seq.cons l_τ Seq.nil) 0
      simpa using this
    rw [← h_e_trace] at h_get0
    simp at h_get0
  -- Structural split of `e.trans` via tightness.
  obtain ⟨trans_prev, h_prev_term, l_last, s_last, h_struct, h_l_last_ext⟩ :=
    tight_trans_split_last_witness ls e h_e_term h_e_tight h_ne
  -- Derive `(trace ⟨e.init, trans_prev⟩) ++ [l_last] = τ_prev ++ [l_τ]`.
  have h_pre_trace_term :
      (ls.trace ⟨e.init, trans_prev⟩).Terminates :=
    trace_terminates_of_trans_terminates ls ⟨e.init, trans_prev⟩ h_prev_term
  have h_trace_split :
      (ls.trace ⟨e.init, trans_prev⟩).append (Seq.cons l_last Seq.nil)
          = τ_prev.append (Seq.cons l_τ Seq.nil) := by
    rw [← trace_append_singleton_external ls e.init trans_prev
          h_prev_term l_last s_last h_l_last_ext]
    have h_e_split : e = ⟨e.init, trans_prev.append
        (Seq.cons (l_last, s_last) Seq.nil)⟩ := by
      obtain ⟨init, trans⟩ := e
      dsimp at h_struct ⊢
      exact congrArg (AlterSeq.mk init) h_struct
    rw [← h_e_split]; exact h_e_trace
  have h_l_last_eq_l_τ : l_last = l_τ :=
    Seq.append_singleton_inj_right _ _ h_pre_trace_term h_τ_prev_term
      l_last l_τ h_trace_split
  -- Contradict `¬ internal l_last` with `internal l_τ`.
  rw [h_l_last_eq_l_τ] at h_l_last_ext
  exact h_l_last_ext h_l_τ_int

-- **`extCylinderMass` vanishes on non-terminating traces.**
private lemma extCylinderMass_eq_zero_of_not_terminates
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (τ : Seq Label) (h_τ : ¬τ.Terminates)
    (e_w_pre : AlterSeq State Label) :
    extCylinderMass sys pe' τ e_w_pre = 0 := by
  unfold extCylinderMass
  haveI := isEmpty_traceCylinder_of_not_terminates sys τ h_τ
  exact tsum_empty

-- **`traceProb` vanishes on non-terminating traces.**
private lemma traceProb_eq_zero_of_not_terminates
    (ls : LabelledSystem State Label)
    (pe : ProbabilisticExecution ls.toSystem)
    (τ : Seq Label) (h_τ : ¬τ.Terminates) :
    ls.traceProb pe τ = 0 := by
  unfold LabelledSystem.traceProb
  haveI := isEmpty_traceCylinder_of_not_terminates ls τ h_τ
  exact tsum_empty

/-! ##### Step 6 sub-claims

Step 6 of the strategy (matching the triple sum

  `∑' e ∈ T_τ, ∑' e_iter_start, ∑' e_w_pre,
     reachProb sys pe' e_w_pre e_iter_start *
       tightStepFactor sys pe' e_w_pre l_τ e_iter_start e.1`

against `sys^w.traceProb pe' τ` for `τ = τ_prev.append (cons l_τ nil)`) is
decomposed into three substantive sub-claims:

1. **Witness-emission marginal** (`witness_emission_marginal`). For each
   `(e_w_pre, e_iter_start)` and external `l_τ`, summing `tightStepFactor`
   over all tight `e ∈ T_τ` whose chain from `e_iter_start` has the right
   structure yields exactly the total `l_τ`-emission mass of `pe'.scheduler`
   at `e_w_pre`, i.e. `∑' μ, pe'.scheduler.next e_w_pre (some (l_τ, μ))`.
   This is the chain-decomposition identity for the weakStep witness's
   `chainProb` and `kernel` factors.

2. **`reachProb` trace-marginal** (`reachProb_marginal_at_trace`). For each
   `e_w_pre`, summing `reachProb sys pe' e_w_pre e_iter_start` over all
   `e_iter_start` with `sys.trace e_iter_start = τ_prev` recovers
   `pe'.probOf e_w_pre` when `sys^w.trace e_w_pre = τ_prev` (and 0
   otherwise). Conceptually: every joint trajectory of the coupled
   algorithm hits the pre-iteration `sys^w`-prefix `e_w_pre` at exactly
   one iteration boundary that aligns the `sys`-side trace with
   `τ_prev`.

3. **`traceProb` cons-end factorisation** (`traceProb_cons_external_factorize`).
   Factor the RHS via `probOf_append_singleton` and the `pe'.kernel`
   definition: `sys^w.traceProb pe' (τ_prev ++ [l_τ])` equals the sum
   over tight `sys^w`-prefixes `e_w_pre` with trace `τ_prev` of
   `pe'.probOf e_w_pre * ∑' μ, pe'.scheduler.next e_w_pre (some (l_τ, μ))`.

These three sub-claims compose, after `ENNReal.tsum_comm` to reorder the
triple sum, into the proof of `_step5`. -/

/-
**Sub-claim 1 (Step 6): witness-emission marginal.**

For fixed `e_w_pre`, `e_iter_start` (terminating, with `e_iter_start`'s
endState matching the `sys^w`-step witness pre-state at `e_w_pre`), and
external `l_τ`, summing `tightStepFactor` over all tight `e ∈ T_τ` that
extend `e_iter_start` (i.e. `e_iter_start.trans` is a prefix of `e.trans`)
yields exactly the total `l_τ`-emission mass of `pe'.scheduler` at
`e_w_pre`.

This is the chain-decomposition identity for the weakStep witness's
`chainProb` and `kernel` factors: summing over all valid chains
extending `e_iter_start` with a final external `(l_τ, _)` reconstitutes
the witness's total mass at `l_τ`.

Status: deferred. -/

/-
**`chainProb` total mass for a bounded-fuel scheduler.**

Running a `boundedFuel n`-bounded weak scheduler from `⟨s, Seq.nil⟩` and
summing the `chainProb` over all possible emission chains gives total
mass `1`. This is the chain-decomposition analogue of `(σ.run n s).tsum_coe`:
every emission outcome of the scheduler (a finite chain followed by a
`none`-halt) is enumerated exactly once by `chainProb`, and the
fuel-bounding guarantees the chain is forced to halt within at most `n`
extensions, so the sum is finite-supported in length.

Proof sketch (inductive on `n`):
* **Base `n = 0`**: `(σ.boundedFuel 0).next ⟨s, Seq.nil⟩ = PMF.pure none`,
  hence `chainProb _ _ List.nil = 1` is the only nonzero summand.
* **Step `n + 1`**: by `boundedFuel_next_of_active`, the head emission
  has the same distribution as `σ.next ⟨s, Seq.nil⟩`. Decompose the
  outer tsum by the head event: the `none`-summand contributes
  `σ.next _ none`, and each `some (l, μ)`-summand contributes
  `(∑' μ', σ.next _ (some (l, μ')) · μ' s') · (chainProb-sum-over-rest)`.
  Apply the IH to the rest-sum, which collapses to `1`, and conclude
  by `(σ.next _).tsum_coe = 1`.

Status: deferred (substantive — ~80-150 lines). Consumed by
`witness_emission_marginal` to evaluate the chain-prefix total mass in
the trace-matching case. -/

/-- Head-tail bijection: a list is either nil or a head followed by a tail. -/
private noncomputable def listEquivOptionHeadTail (α : Type) :
    List α ≃ Option (α × List α) where
  toFun l := l.casesOn none (fun hd tl => some (hd, tl))
  invFun o := o.casesOn [] (fun p => p.1 :: p.2)
  left_inv := fun l => by cases l <;> rfl
  right_inv := fun o => by cases o with | none => rfl | some p => cases p; rfl

/-- Split a tsum over lists into the nil summand and the cons summand. -/
private lemma tsum_list_split_head_tail {α : Type} (f : List α → ENNReal) :
    ∑' chain : List α, f chain
      = f [] + ∑' p : α × List α, f (p.1 :: p.2) := by
  rw [← (listEquivOptionHeadTail α).symm.tsum_eq f]
  rw [← (Equiv.optionEquivSumPUnit.{0, _} (α × List α)).symm.tsum_eq
        (fun o => f ((listEquivOptionHeadTail α).symm o))]
  rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
  rw [add_comm]
  congr 1
  rw [tsum_eq_single (b := (⟨⟩ : PUnit))]
  · rfl
  · rintro ⟨⟩ h; exact (h rfl).elim

/-- **Length of the append of a terminating seq and a singleton.** Auxiliary
for the `boundedFuel`-fuel tracking in the chain-mass induction. -/
private lemma seq_length_append_singleton
    {α : Type} (s : Seq α) (h : s.Terminates) (a : α)
    (h_app : (s.append (Seq.cons a Seq.nil)).Terminates) :
    (s.append (Seq.cons a Seq.nil)).length h_app = s.length h + 1 := by
  have h_single : (Seq.cons a Seq.nil : Seq α).Terminates :=
    ⟨1, show (Seq.cons a Seq.nil : Seq α).TerminatedAt 1 from rfl⟩
  rw [← Seq.length_toList]
  rw [Seq.toList_append s _ h h_single h_app]
  rw [Seq.toList_cons h_single]
  simp [Seq.toList_nil, Seq.length_toList]

/-- **Auxiliary induction for `chainProb_total_mass_of_boundedFuel`.**
Parameter `k` is the "remaining fuel": the prefix `e` is required to have
*exact* length `n - k` (witnessed by `length(e.trans) + k = n`). The main
lemma is recovered at `k = n`, `e = ⟨s, Seq.nil⟩` (length 0). -/
private lemma chainProb_total_mass_of_boundedFuel_aux
    {sys : LabelledSystem State Label} (σ : WeakScheduler sys) (n : ℕ) :
    ∀ (k : ℕ) (e : AlterSeq State Label) (h : e.trans.Terminates),
      e.trans.length h + k = n →
      (∑' chain : List (Label × State),
        chainProb (σ.boundedFuel n) e chain) = 1 := by
  classical
  intro k
  induction k with
  | zero =>
    -- Base case: `e.trans.length h = n`, so no `k' < n` satisfies
    -- `e.trans.TerminatedAt k'` (which would mean `length ≤ k' < n`).
    -- Hence the scheduler is inactive and emits `PMF.pure none`.
    intro e h h_len
    rw [Nat.add_zero] at h_len
    -- Inactive: `¬ ∃ k', k' < n ∧ e.trans.TerminatedAt k'`.
    have h_inactive : ¬ ∃ k', k' < n ∧ e.trans.TerminatedAt k' := by
      rintro ⟨k', hk_lt, hk_term⟩
      have : e.trans.length h ≤ k' := Seq.length_le_iff.mpr hk_term
      omega
    have h_next_eq : (σ.boundedFuel n).next e = PMF.pure none := by
      change (if (∃ k', k' < n ∧ e.trans.TerminatedAt k') then σ.next e
                else PMF.pure none) = PMF.pure none
      exact if_neg h_inactive
    -- Split the tsum over chain into the nil chain and the cons chain via
    -- the head-tail bijection.
    rw [tsum_list_split_head_tail (f := fun chain =>
      chainProb (σ.boundedFuel n) e chain)]
    -- Nil-chain summand: chainProb _ _ [] = (σ.boundedFuel n).next e none = 1.
    -- Cons-chain summand: chainProb _ _ (hd :: rest) starts with a factor
    --   ∑' μ, (σ.boundedFuel n).next e (some (hd.1, μ)) * μ hd.2
    -- which is 0 because (σ.boundedFuel n).next e = PMF.pure none and
    -- PMF.pure none (some _) = 0.
    have h_nil : chainProb (σ.boundedFuel n) e [] = 1 := by
      change (σ.boundedFuel n).next e none = 1
      rw [h_next_eq, PMF.pure_apply, if_pos rfl]
    have h_cons_zero : ∀ p : (Label × State) × List (Label × State),
        chainProb (σ.boundedFuel n) e (p.1 :: p.2) = 0 := by
      intro p
      change (∑' μ : PMF State,
        (σ.boundedFuel n).next e (some (p.1.1, μ)) * μ p.1.2) * _ = 0
      have h_factor : ∀ μ : PMF State,
          (σ.boundedFuel n).next e (some (p.1.1, μ)) * μ p.1.2 = 0 := by
        intro μ
        rw [h_next_eq, PMF.pure_apply, if_neg (by simp)]
        ring
      rw [tsum_congr h_factor, tsum_zero, zero_mul]
    rw [h_nil]
    rw [tsum_congr h_cons_zero, tsum_zero, add_zero]
  | succ m ih =>
    intro e h h_len
    -- `length + (m+1) = n`, so `length < n`, hence active.
    have h_len_lt : e.trans.length h < n := by omega
    have h_term_at : e.trans.TerminatedAt (e.trans.length h) :=
      Seq.length_le_iff.mp (le_refl _)
    have h_active : ∃ k', k' < n ∧ e.trans.TerminatedAt k' :=
      ⟨e.trans.length h, h_len_lt, h_term_at⟩
    have h_next_eq : (σ.boundedFuel n).next e = σ.next e :=
      WeakScheduler.boundedFuel_next_of_active σ n e h_active
    -- Split via head-tail bijection.
    rw [tsum_list_split_head_tail (f := fun chain =>
      chainProb (σ.boundedFuel n) e chain)]
    -- Nil-chain summand: (σ.boundedFuel n).next e none = σ.next e none.
    have h_nil : chainProb (σ.boundedFuel n) e [] = σ.next e none := by
      change (σ.boundedFuel n).next e none = σ.next e none
      rw [h_next_eq]
    -- Cons-chain summand: ∑' p, factor(p.1) * chainProb σ' e'(p.1) p.2
    -- where factor(hd) := ∑' μ, σ.next e (some (hd.1, μ)) * μ hd.2
    -- and e'(hd) := ⟨e.init, e.trans.append (cons hd nil)⟩.
    -- Apply IH at k = m on e'(hd), to get tsum over rest = 1.
    have h_cons : ∀ p : (Label × State) × List (Label × State),
        chainProb (σ.boundedFuel n) e (p.1 :: p.2) =
          (∑' μ : PMF State, σ.next e (some (p.1.1, μ)) * μ p.1.2) *
            chainProb (σ.boundedFuel n)
              ⟨e.init, e.trans.append (Seq.cons p.1 Seq.nil)⟩ p.2 := by
      intro p
      change (∑' μ : PMF State,
          (σ.boundedFuel n).next e (some (p.1.1, μ)) * μ p.1.2) *
          chainProb (σ.boundedFuel n)
            ⟨e.init, e.trans.append (Seq.cons p.1 Seq.nil)⟩ p.2 = _
      rw [h_next_eq]
    rw [tsum_congr h_cons]
    -- For each head `hd`, the IH gives tsum over rest of
    -- chainProb σ' (e'(hd)) rest = 1. The extended prefix terminates at
    -- length (e.trans.length + 1), which when added to m equals n.
    have h_inner : ∀ hd : Label × State,
        ∑' rest : List (Label × State),
          chainProb (σ.boundedFuel n)
            ⟨e.init, e.trans.append (Seq.cons hd Seq.nil)⟩ rest = 1 := by
      intro hd
      -- e'.trans = e.trans.append (cons hd nil) terminates and has length
      -- e.trans.length + 1.
      have h_single_term : (Seq.cons hd Seq.nil : Seq (Label × State)).Terminates :=
        ⟨1, show (Seq.cons hd Seq.nil : Seq (Label × State)).TerminatedAt 1
              from rfl⟩
      have h_app_term : (e.trans.append (Seq.cons hd Seq.nil)).Terminates :=
        ⟨_, Seq.terminatedAt_append_find h h_single_term.choose_spec⟩
      have h_e'_len :
          (e.trans.append (Seq.cons hd Seq.nil)).length h_app_term
            = e.trans.length h + 1 :=
        seq_length_append_singleton e.trans h hd h_app_term
      have h_e'_len_plus :
          (e.trans.append (Seq.cons hd Seq.nil)).length h_app_term + m = n := by
        omega
      exact ih ⟨e.init, e.trans.append (Seq.cons hd Seq.nil)⟩ h_app_term
        h_e'_len_plus
    -- Use the inner equality and tsum_mul/Fubini.
    -- ∑' p, factor(p.1) * (chainProb_sum-over-p.2) = ∑' hd, factor(hd) * 1
    -- = ∑' hd, factor(hd).
    have h_step1 :
        ∑' p : (Label × State) × List (Label × State),
          (∑' μ : PMF State, σ.next e (some (p.1.1, μ)) * μ p.1.2) *
            chainProb (σ.boundedFuel n)
              ⟨e.init, e.trans.append (Seq.cons p.1 Seq.nil)⟩ p.2
          = ∑' hd : Label × State,
              ∑' μ : PMF State, σ.next e (some (hd.1, μ)) * μ hd.2 := by
      rw [ENNReal.tsum_prod']
      apply tsum_congr
      intro hd
      -- `(hd, _).1 = hd` and `(hd, b).2 = b` definitionally; we still need
      -- `simp only` to reduce the projections inside binders so that
      -- `ENNReal.tsum_mul_left` and `h_inner` can fire.
      simp only
      rw [ENNReal.tsum_mul_left]
      rw [h_inner hd, mul_one]
    rw [h_step1, h_nil]
    -- Now we need σ.next e none + ∑' hd, ∑' μ, σ.next e (some (hd.1, μ)) * μ hd.2
    -- = 1 by `(σ.next e).tsum_coe`.
    -- Rewrite the inner sum: ∑' hd : Label × State, ∑' μ, ...
    --   = ∑' l : Label, ∑' s : State, ∑' μ, σ.next e (some (l, μ)) * μ s
    --   = ∑' l, ∑' μ, ∑' s, σ.next e (some (l, μ)) * μ s
    --   = ∑' l, ∑' μ, σ.next e (some (l, μ)) * (∑' s, μ s)
    --   = ∑' l, ∑' μ, σ.next e (some (l, μ)) * 1
    --   = ∑' l, ∑' μ, σ.next e (some (l, μ))
    --   = ∑' (l, μ), σ.next e (some (l, μ))
    --   = ∑' a : Label × PMF State, σ.next e (some a).
    have h_step2 :
        (∑' hd : Label × State,
          ∑' μ : PMF State, σ.next e (some (hd.1, μ)) * μ hd.2)
        = ∑' a : Label × PMF State, σ.next e (some a) := by
      rw [ENNReal.tsum_prod (f := fun l s =>
        ∑' μ : PMF State, σ.next e (some (l, μ)) * μ s)]
      -- ∑' l, ∑' s, ∑' μ, ... = ∑' l, ∑' μ, ∑' s, ... = ∑' l, ∑' μ, ... * 1
      have h_swap : ∀ l : Label,
          (∑' s : State, ∑' μ : PMF State, σ.next e (some (l, μ)) * μ s)
            = ∑' μ : PMF State, σ.next e (some (l, μ)) := by
        intro l
        rw [ENNReal.tsum_comm]
        apply tsum_congr; intro μ
        rw [ENNReal.tsum_mul_left, μ.tsum_coe, mul_one]
      rw [tsum_congr h_swap]
      rw [ENNReal.tsum_prod (f := fun l μ => σ.next e (some (l, μ)))]
    rw [h_step2]
    -- σ.next e none + ∑' a, σ.next e (some a) = ∑' o, σ.next e o = 1.
    have h_pmf_total : ∑' o : Option (Label × PMF State), σ.next e o = 1 :=
      (σ.next e).tsum_coe
    -- Split the PMF total via Option.
    have h_opt_split :
        ∑' o : Option (Label × PMF State), σ.next e o
          = σ.next e none
            + ∑' a : Label × PMF State, σ.next e (some a) := by
      -- Reuse the same split machinery as for lists.
      rw [← (Equiv.optionEquivSumPUnit.{0, _} (Label × PMF State)).symm.tsum_eq
            (fun o => σ.next e o)]
      rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
      rw [add_comm]
      congr 1
      rw [tsum_eq_single (b := (⟨⟩ : PUnit))]
      · rfl
      · rintro ⟨⟩ h_ne; exact (h_ne rfl).elim
    rw [← h_opt_split]
    exact h_pmf_total

/-- **`chainProb` vanishes on a chain whose head label is non-internal.**
A `WeakScheduler` only emits internal labels (`internal_only`), so the
factor `σ.next sub_prefix (some (l, μ))` is zero for every `μ` when
`¬ sys.internal l`. -/
private lemma chainProb_eq_zero_of_head_not_internal
    {sys : LabelledSystem State Label} (σ : WeakScheduler sys)
    (sub_prefix : AlterSeq State Label) (hd : Label × State)
    (h_not_int : ¬ sys.internal hd.1)
    (rest : List (Label × State)) :
    chainProb σ sub_prefix (hd :: rest) = 0 := by
  unfold chainProb
  have h_zero : ∀ μ : PMF State,
      σ.next sub_prefix (some (hd.1, μ)) * μ hd.2 = 0 := by
    intro μ
    have h_not_supp : some (hd.1, μ) ∉ (σ.next sub_prefix).support := by
      intro h_supp
      exact h_not_int (σ.internal_only sub_prefix hd.1 μ h_supp)
    have h_eq_zero : σ.next sub_prefix (some (hd.1, μ)) = 0 := by
      simpa [PMF.mem_support_iff] using h_not_supp
    rw [h_eq_zero, zero_mul]
  rw [tsum_congr h_zero, tsum_zero, zero_mul]

/-- **`chainProb` vanishes on any chain that contains a non-internal label.**
Direct induction on the chain. -/
private lemma chainProb_eq_zero_of_not_all_internal
    {sys : LabelledSystem State Label} (σ : WeakScheduler sys)
    (sub_prefix : AlterSeq State Label) (chain : List (Label × State))
    (h_not_int : ¬ ∀ pair ∈ chain, sys.internal pair.1) :
    chainProb σ sub_prefix chain = 0 := by
  induction chain generalizing sub_prefix with
  | nil =>
    exfalso; apply h_not_int; intro _ h; cases h
  | cons hd rest ih =>
    -- Either hd.1 is non-internal (head zero) or rest has a non-internal pair.
    by_cases h_hd_int : sys.internal hd.1
    · -- Non-internal entry must be in rest.
      have h_rest_not_int : ¬ ∀ pair ∈ rest, sys.internal pair.1 := by
        intro h_all
        apply h_not_int
        intro pair h_mem
        rcases List.mem_cons.mp h_mem with h_eq | h_in_rest
        · rw [h_eq]; exact h_hd_int
        · exact h_all pair h_in_rest
      -- Reduce chainProb of (hd :: rest) and induct.
      unfold chainProb
      have h_rest_zero :
          chainProb σ ⟨sub_prefix.init,
              sub_prefix.trans.append (Seq.cons hd Seq.nil)⟩ rest = 0 :=
        ih _ h_rest_not_int
      rw [h_rest_zero, mul_zero]
    · -- Head non-internal: use head-zero lemma.
      exact chainProb_eq_zero_of_head_not_internal σ sub_prefix hd h_hd_int rest

private lemma chainProb_total_mass_of_boundedFuel
    {sys : LabelledSystem State Label} (σ : WeakScheduler sys) (n : ℕ) (s : State) :
    (∑' chain : List (Label × State),
      chainProb (σ.boundedFuel n) ⟨s, Seq.nil⟩ chain) = 1 := by
  refine chainProb_total_mass_of_boundedFuel_aux σ n n ⟨s, Seq.nil⟩
    ⟨0, rfl⟩ ?_
  -- length of Seq.nil = 0, so 0 + n = n.
  rw [Seq.length_nil, Nat.zero_add]

/-- **Auxiliary endState-marginal induction for `chainProb_endState_marginal_of_boundedFuel`.**
Parameter `k` is the "remaining fuel": the prefix `e` is required to have *exact*
length `n - k` (witnessed by `length(e.trans) + k = n`). The current state `s`
threads through the run; the "endState-of-chain" predicate measures the chain's
last state (or `s` if the chain is empty). The main lemma is recovered at
`k = n`, `e = ⟨s, Seq.nil⟩` (length 0). The statement says the σ.boundedFuel
run from `(e, s)` for `k` steps puts mass `s_end` exactly on the sum of
chainProbs over chains whose endState (relative to `s`) is `s_end`. -/
private lemma chainProb_endState_marginal_of_boundedFuel_aux
    {sys : LabelledSystem State Label} (σ : WeakScheduler sys) (n : ℕ) :
    ∀ (k : ℕ) (e : AlterSeq State Label) (h : e.trans.Terminates)
      (s s_end : State), e.trans.length h + k = n →
      (∑' chain : List (Label × State),
        (open Classical in
          if (chain.getLast?.map Prod.snd).getD s = s_end then
            chainProb (σ.boundedFuel n) e chain
          else 0)) = ((σ.boundedFuel n).runFromState k e s) s_end := by
  classical
  intro k
  induction k with
  | zero =>
    -- Base case: `e.trans.length h = n`, so no `k' < n` satisfies
    -- `e.trans.TerminatedAt k'`. Hence the bounded scheduler is inactive and
    -- emits `PMF.pure none`. Only the nil-chain summand survives, equaling
    -- `[s = s_end]`. Meanwhile, runFromState 0 _ s = PMF.pure s, whose value
    -- at s_end is also `[s_end = s]`.
    intro e h s s_end h_len
    rw [Nat.add_zero] at h_len
    have h_inactive : ¬ ∃ k', k' < n ∧ e.trans.TerminatedAt k' := by
      rintro ⟨k', hk_lt, hk_term⟩
      have : e.trans.length h ≤ k' := Seq.length_le_iff.mpr hk_term
      omega
    have h_next_eq : (σ.boundedFuel n).next e = PMF.pure none := by
      change (if (∃ k', k' < n ∧ e.trans.TerminatedAt k') then σ.next e
                else PMF.pure none) = PMF.pure none
      exact if_neg h_inactive
    -- Split the tsum over chain into the nil chain and the cons chain via
    -- the head-tail bijection.
    rw [tsum_list_split_head_tail (f := fun chain =>
      if (chain.getLast?.map Prod.snd).getD s = s_end then
        chainProb (σ.boundedFuel n) e chain
      else 0)]
    -- Nil-chain summand: (getLast? []).map = none, getD = s.
    have h_nil_indicator : ((([] : List (Label × State)).getLast?).map Prod.snd).getD s = s := by
      simp
    have h_nil : (if (([] : List (Label × State)).getLast?.map Prod.snd).getD s = s_end then
        chainProb (σ.boundedFuel n) e [] else 0) =
        (if s = s_end then (σ.boundedFuel n).next e none else 0) := by
      rw [h_nil_indicator]
      rfl
    -- Cons-chain summand: chainProb of (hd :: rest) factors as
    --   (∑' μ, (σ.boundedFuel n).next e (some (hd.1, μ)) * μ hd.2) * ...
    -- which is 0 because (σ.boundedFuel n).next e = PMF.pure none.
    have h_cons_zero : ∀ p : (Label × State) × List (Label × State),
        (if ((p.1 :: p.2).getLast?.map Prod.snd).getD s = s_end then
          chainProb (σ.boundedFuel n) e (p.1 :: p.2) else 0) = 0 := by
      intro p
      by_cases h_ind : ((p.1 :: p.2).getLast?.map Prod.snd).getD s = s_end
      · rw [if_pos h_ind]
        change (∑' μ : PMF State,
          (σ.boundedFuel n).next e (some (p.1.1, μ)) * μ p.1.2) * _ = 0
        have h_factor : ∀ μ : PMF State,
            (σ.boundedFuel n).next e (some (p.1.1, μ)) * μ p.1.2 = 0 := by
          intro μ
          rw [h_next_eq, PMF.pure_apply, if_neg (by simp)]
          ring
        rw [tsum_congr h_factor, tsum_zero, zero_mul]
      · exact if_neg h_ind
    rw [h_nil, tsum_congr h_cons_zero, tsum_zero, add_zero]
    -- LHS = if s = s_end then σ.next e none else 0
    -- RHS = (PMF.pure s) s_end = [s_end = s]
    -- σ.next e none with (σ.bF n).next e = PMF.pure none gives 1 (at none).
    have h_next_none_one : (σ.boundedFuel n).next e none = 1 := by
      rw [h_next_eq, PMF.pure_apply, if_pos rfl]
    -- Reduce LHS
    change (if s = s_end then (σ.boundedFuel n).next e none else 0)
      = ((σ.boundedFuel n).runFromState 0 e s) s_end
    rw [h_next_none_one]
    -- runFromState 0 _ s = PMF.pure s
    change (if s = s_end then 1 else 0) = (PMF.pure s : PMF State) s_end
    rw [PMF.pure_apply]
    by_cases hse : s = s_end
    · rw [if_pos hse, if_pos hse.symm]
    · rw [if_neg hse, if_neg (fun h => hse h.symm)]
  | succ m ih =>
    intro e h s s_end h_len
    -- `length + (m+1) = n`, so `length < n`, hence active.
    have h_len_lt : e.trans.length h < n := by omega
    have h_term_at : e.trans.TerminatedAt (e.trans.length h) :=
      Seq.length_le_iff.mp (le_refl _)
    have h_active : ∃ k', k' < n ∧ e.trans.TerminatedAt k' :=
      ⟨e.trans.length h, h_len_lt, h_term_at⟩
    have h_next_eq : (σ.boundedFuel n).next e = σ.next e :=
      WeakScheduler.boundedFuel_next_of_active σ n e h_active
    -- Split the tsum over chain via head-tail.
    rw [tsum_list_split_head_tail (f := fun chain =>
      if (chain.getLast?.map Prod.snd).getD s = s_end then
        chainProb (σ.boundedFuel n) e chain
      else 0)]
    -- Nil-chain summand value: (getLast?[]).map.getD = s, indicator [s = s_end],
    -- chainProb σ' e [] = σ'.next e none = σ.next e none.
    have h_nil_indicator : ((([] : List (Label × State)).getLast?).map Prod.snd).getD s = s := by
      simp
    have h_nil_val : (if (([] : List (Label × State)).getLast?.map Prod.snd).getD s = s_end then
        chainProb (σ.boundedFuel n) e [] else 0)
        = if s = s_end then σ.next e none else 0 := by
      rw [h_nil_indicator]
      by_cases hse : s = s_end
      · rw [if_pos hse, if_pos hse]
        change (σ.boundedFuel n).next e none = σ.next e none
        rw [h_next_eq]
      · rw [if_neg hse, if_neg hse]
    -- Cons-chain summand: factor out the head and apply IH to rest.
    -- ChainProb (hd :: rest) = (∑' μ, σ.next e (some (hd.1, μ)) * μ hd.2) *
    --   chainProb (σ.bF n) ⟨e.init, e.trans + cons hd nil⟩ rest.
    -- (getLast? of (hd :: rest)).map.getD s = (getLast? rest with default hd.2).
    have h_cons_val : ∀ p : (Label × State) × List (Label × State),
        (if ((p.1 :: p.2).getLast?.map Prod.snd).getD s = s_end then
          chainProb (σ.boundedFuel n) e (p.1 :: p.2) else 0)
        =
        (∑' μ : PMF State, σ.next e (some (p.1.1, μ)) * μ p.1.2) *
          (if (p.2.getLast?.map Prod.snd).getD p.1.2 = s_end then
            chainProb (σ.boundedFuel n)
              ⟨e.init, e.trans.append (Seq.cons p.1 Seq.nil)⟩ p.2
            else 0) := by
      intro p
      -- The indicator only depends on rest+hd.2 (not on s), since hd :: rest is non-nil.
      have h_ind_eq : ((p.1 :: p.2).getLast?.map Prod.snd).getD s
          = (p.2.getLast?.map Prod.snd).getD p.1.2 := by
        cases hp2 : p.2 with
        | nil => simp
        | cons hd' rest' =>
          have h_some : (hd' :: rest').getLast? =
              some ((hd' :: rest').getLast (by simp)) := by
            rw [List.getLast?_eq_getLast_of_ne_nil]
          rw [List.getLast?_cons_cons]
          rw [h_some]
          simp
      rw [h_ind_eq]
      by_cases h_ind : (p.2.getLast?.map Prod.snd).getD p.1.2 = s_end
      · rw [if_pos h_ind, if_pos h_ind]
        change (∑' μ : PMF State,
          (σ.boundedFuel n).next e (some (p.1.1, μ)) * μ p.1.2) *
          chainProb (σ.boundedFuel n) _ p.2 = _
        rw [h_next_eq]
      · rw [if_neg h_ind, if_neg h_ind, mul_zero]
    rw [h_nil_val, tsum_congr h_cons_val]
    -- For each head hd, the IH on the extended prefix (which terminates at
    -- length+1, so length+1+m = n) gives the tsum over rest equals runFromState m.
    have h_inner : ∀ hd : Label × State,
        ∑' rest : List (Label × State),
          (if (rest.getLast?.map Prod.snd).getD hd.2 = s_end then
            chainProb (σ.boundedFuel n)
              ⟨e.init, e.trans.append (Seq.cons hd Seq.nil)⟩ rest
            else 0)
          = ((σ.boundedFuel n).runFromState m
              ⟨e.init, e.trans.append (Seq.cons hd Seq.nil)⟩ hd.2) s_end := by
      intro hd
      have h_single_term : (Seq.cons hd Seq.nil : Seq (Label × State)).Terminates :=
        ⟨1, show (Seq.cons hd Seq.nil : Seq (Label × State)).TerminatedAt 1 from rfl⟩
      have h_app_term : (e.trans.append (Seq.cons hd Seq.nil)).Terminates :=
        ⟨_, Seq.terminatedAt_append_find h h_single_term.choose_spec⟩
      have h_e'_len :
          (e.trans.append (Seq.cons hd Seq.nil)).length h_app_term
            = e.trans.length h + 1 :=
        seq_length_append_singleton e.trans h hd h_app_term
      have h_e'_len_plus :
          (e.trans.append (Seq.cons hd Seq.nil)).length h_app_term + m = n := by
        omega
      exact ih ⟨e.init, e.trans.append (Seq.cons hd Seq.nil)⟩ h_app_term hd.2 s_end
        h_e'_len_plus
    -- Combine: ∑' p, factor(p.1) * IH-on-p.2 = ∑' hd, factor(hd) * runFromState m ...
    have h_step1 :
        ∑' p : (Label × State) × List (Label × State),
          (∑' μ : PMF State, σ.next e (some (p.1.1, μ)) * μ p.1.2) *
            (if (p.2.getLast?.map Prod.snd).getD p.1.2 = s_end then
              chainProb (σ.boundedFuel n)
                ⟨e.init, e.trans.append (Seq.cons p.1 Seq.nil)⟩ p.2
              else 0)
          = ∑' hd : Label × State,
              (∑' μ : PMF State, σ.next e (some (hd.1, μ)) * μ hd.2) *
                ((σ.boundedFuel n).runFromState m
                  ⟨e.init, e.trans.append (Seq.cons hd Seq.nil)⟩ hd.2) s_end := by
      rw [ENNReal.tsum_prod']
      apply tsum_congr
      intro hd
      simp only
      rw [ENNReal.tsum_mul_left]
      rw [h_inner hd]
    rw [h_step1]
    -- Now LHS = (if s = s_end then σ.next e none else 0) +
    --   ∑' hd, (∑' μ, σ.next e (some (hd.1, μ)) * μ hd.2) * runFromState m _ hd.2 s_end.
    -- And RHS = runFromState (m+1) e s s_end. Unfold runFromState (m+1):
    --   = ((σ.bF n).next e).bind (...) s_end via PMF.bind_apply.
    change (if s = s_end then σ.next e none else 0) +
        ∑' hd : Label × State,
          (∑' μ : PMF State, σ.next e (some (hd.1, μ)) * μ hd.2) *
            ((σ.boundedFuel n).runFromState m
              ⟨e.init, e.trans.append (Seq.cons hd Seq.nil)⟩ hd.2) s_end
        = ((σ.boundedFuel n).runFromState (m + 1) e s) s_end
    -- Unfold runFromState (m+1)
    change _ = ((σ.boundedFuel n).next e).bind (fun
        | none => PMF.pure s
        | some (l, μ_q) => μ_q.bind fun s' =>
            (σ.boundedFuel n).runFromState m
              ⟨e.init, e.trans.append (Seq.cons (l, s') Seq.nil)⟩ s') s_end
    rw [PMF.bind_apply]
    rw [h_next_eq]
    -- ∑' a, σ.next e a * (...) s_end. Split via Option.
    rw [tsum_option_split_none_some (f := fun o =>
      σ.next e o *
        ((open Classical in match o with
          | none => PMF.pure s
          | some (l, μ_q) =>
            μ_q.bind fun s' =>
              (σ.boundedFuel n).runFromState m
                ⟨e.init, e.trans.append (Seq.cons (l, s') Seq.nil)⟩ s') : PMF State) s_end)]
    -- The none term: σ.next e none * (PMF.pure s) s_end = σ.next e none * [s_end = s].
    -- The some term: ∑' (l, μ_q), σ.next e (some (l, μ_q)) * (μ_q.bind ...) s_end.
    -- Match LHS structure.
    -- For none:
    have h_none_term : σ.next e none * ((PMF.pure s : PMF State) s_end)
        = if s = s_end then σ.next e none else 0 := by
      rw [PMF.pure_apply]
      by_cases hse : s = s_end
      · rw [if_pos hse, if_pos hse.symm, mul_one]
      · rw [if_neg hse, if_neg (fun h => hse h.symm), mul_zero]
    -- For some: rewrite the some-piece into the chain form.
    have h_some_term : ∀ a : Label × PMF State,
        σ.next e (some a) *
          (a.2.bind fun s' =>
            (σ.boundedFuel n).runFromState m
              ⟨e.init, e.trans.append (Seq.cons (a.1, s') Seq.nil)⟩ s') s_end
        =
        σ.next e (some a) * ∑' s' : State, a.2 s' *
          ((σ.boundedFuel n).runFromState m
            ⟨e.init, e.trans.append (Seq.cons (a.1, s') Seq.nil)⟩ s') s_end := by
      intro a
      rw [PMF.bind_apply]
    -- For the some-sum, we need to convert to a (hd : Label × State)-indexed sum
    -- matching the LHS structure: ∑' hd, (∑' μ_q, σ.next e (some (hd.1, μ_q)) * μ_q hd.2) *
    --   runFromState m _ hd.2 s_end.
    -- LHS-some indexed by hd = (l, s'): the inner ∑' μ collapses with μ_q s' (specific s').
    -- RHS-some indexed by a = (l, μ_q): the inner ∑' s' picks up runFromState m _ s'.
    -- These are equal by Fubini: swap (l, s', μ_q) order.
    change (if s = s_end then σ.next e none else 0) +
        (∑' hd : Label × State,
          (∑' μ : PMF State, σ.next e (some (hd.1, μ)) * μ hd.2) *
            ((σ.boundedFuel n).runFromState m
              ⟨e.init, e.trans.append (Seq.cons hd Seq.nil)⟩ hd.2) s_end) =
        σ.next e none *
          (PMF.pure s : PMF State) s_end +
        ∑' a : Label × PMF State,
          σ.next e (some a) *
            (a.2.bind fun s' =>
              (σ.boundedFuel n).runFromState m
                ⟨e.init, e.trans.append (Seq.cons (a.1, s') Seq.nil)⟩ s') s_end
    rw [h_none_term]
    congr 1
    -- Need: ∑' hd : Label × State, (∑' μ_q, σ.next e (some (hd.1, μ_q)) * μ_q hd.2) *
    --   runFromState m _ hd.2 s_end
    -- = ∑' a : Label × PMF State, σ.next e (some a) * ∑' s', a.2 s' * runFromState m _ s' s_end.
    rw [tsum_congr h_some_term]
    -- Expand both sides into nested sums via tsum_prod' (Label × _).
    -- LHS: ∑' hd : Label × State, f₁(hd.1)(hd.2)
    --   = ∑' l, ∑' s', f₁(l)(s')
    -- RHS: ∑' a : Label × PMF State, f₂(a.1)(a.2)
    --   = ∑' l, ∑' μ_q, f₂(l)(μ_q)
    -- Then Fubini swap inside.
    have h_lhs_split :
        ∑' hd : Label × State,
          (∑' μ : PMF State, σ.next e (some (hd.1, μ)) * μ hd.2) *
            ((σ.boundedFuel n).runFromState m
              ⟨e.init, e.trans.append (Seq.cons hd Seq.nil)⟩ hd.2) s_end
        = ∑' l : Label, ∑' s' : State,
            (∑' μ : PMF State, σ.next e (some (l, μ)) * μ s') *
              ((σ.boundedFuel n).runFromState m
                ⟨e.init, e.trans.append (Seq.cons (l, s') Seq.nil)⟩ s') s_end := by
      rw [ENNReal.tsum_prod (f := fun l s' =>
        (∑' μ : PMF State, σ.next e (some (l, μ)) * μ s') *
          ((σ.boundedFuel n).runFromState m
            ⟨e.init, e.trans.append (Seq.cons (l, s') Seq.nil)⟩ s') s_end)]
    have h_rhs_split :
        ∑' a : Label × PMF State,
          σ.next e (some a) * ∑' s' : State, a.2 s' *
            ((σ.boundedFuel n).runFromState m
              ⟨e.init, e.trans.append (Seq.cons (a.1, s') Seq.nil)⟩ s') s_end
        = ∑' l : Label, ∑' μ_q : PMF State,
            σ.next e (some (l, μ_q)) * ∑' s' : State, μ_q s' *
              ((σ.boundedFuel n).runFromState m
                ⟨e.init, e.trans.append (Seq.cons (l, s') Seq.nil)⟩ s') s_end := by
      rw [ENNReal.tsum_prod (f := fun l μ_q =>
        σ.next e (some (l, μ_q)) * ∑' s' : State, μ_q s' *
          ((σ.boundedFuel n).runFromState m
            ⟨e.init, e.trans.append (Seq.cons (l, s') Seq.nil)⟩ s') s_end)]
    rw [h_lhs_split, h_rhs_split]
    apply tsum_congr
    intro l
    -- LHS: ∑' s', (∑' μ, σ.next e (some (l, μ)) * μ s') * runFromState m _ s' s_end.
    -- RHS: ∑' μ, σ.next e (some (l, μ)) * ∑' s', μ s' * runFromState m _ s' s_end.
    -- Push inner ∑' μ outside (tsum_mul_right with constant in s'):
    have h_l_lhs :
        ∑' s' : State,
          (∑' μ : PMF State, σ.next e (some (l, μ)) * μ s') *
            ((σ.boundedFuel n).runFromState m
              ⟨e.init, e.trans.append (Seq.cons (l, s') Seq.nil)⟩ s') s_end
        = ∑' s' : State, ∑' μ : PMF State,
            σ.next e (some (l, μ)) * μ s' *
              ((σ.boundedFuel n).runFromState m
                ⟨e.init, e.trans.append (Seq.cons (l, s') Seq.nil)⟩ s') s_end := by
      apply tsum_congr; intro s'
      rw [ENNReal.tsum_mul_right]
    have h_l_rhs :
        ∑' μ : PMF State,
          σ.next e (some (l, μ)) * ∑' s' : State, μ s' *
            ((σ.boundedFuel n).runFromState m
              ⟨e.init, e.trans.append (Seq.cons (l, s') Seq.nil)⟩ s') s_end
        = ∑' μ : PMF State, ∑' s' : State,
            σ.next e (some (l, μ)) * μ s' *
              ((σ.boundedFuel n).runFromState m
                ⟨e.init, e.trans.append (Seq.cons (l, s') Seq.nil)⟩ s') s_end := by
      apply tsum_congr; intro μ
      rw [show ((σ.next e) (some (l, μ)) * ∑' s' : State, μ s' *
            ((σ.boundedFuel n).runFromState m
              ⟨e.init, e.trans.append (Seq.cons (l, s') Seq.nil)⟩ s') s_end)
            = ∑' s' : State, (σ.next e) (some (l, μ)) * (μ s' *
              ((σ.boundedFuel n).runFromState m
                ⟨e.init, e.trans.append (Seq.cons (l, s') Seq.nil)⟩ s') s_end) from
        (ENNReal.tsum_mul_left).symm]
      apply tsum_congr; intro s'
      ring
    rw [h_l_lhs, h_l_rhs]
    -- Now swap order of (s', μ).
    rw [ENNReal.tsum_comm (f := fun s' μ =>
      σ.next e (some (l, μ)) * μ s' *
        ((σ.boundedFuel n).runFromState m
          ⟨e.init, e.trans.append (Seq.cons (l, s') Seq.nil)⟩ s') s_end)]

/-- **EndState-marginal of `chainProb` for a `boundedFuel` scheduler.**
Marginalising `chainProb (σ.boundedFuel n) ⟨s_init, Seq.nil⟩ chain` over
all chains whose end-state (last `Prod.snd`, defaulting to `s_init` for the
empty chain) equals `s_end` recovers `((σ.boundedFuel n).run n s_init) s_end`,
the probability of ending at `s_end` after running `σ.boundedFuel n` for `n`
outer steps from `s_init`. This is the per-end-state refinement of
`chainProb_total_mass_of_boundedFuel`. -/
private lemma chainProb_endState_marginal_of_boundedFuel
    {sys : LabelledSystem State Label} (σ : WeakScheduler sys) (n : ℕ)
    (s_init s_end : State) :
    (∑' chain : List (Label × State),
      (open Classical in
        if (chain.getLast?.map Prod.snd).getD s_init = s_end then
          chainProb (σ.boundedFuel n) ⟨s_init, Seq.nil⟩ chain
        else 0)) = ((σ.boundedFuel n).run n s_init) s_end := by
  refine chainProb_endState_marginal_of_boundedFuel_aux σ n n
    ⟨s_init, Seq.nil⟩ ⟨0, rfl⟩ s_init s_end ?_
  rw [Seq.length_nil, Nat.zero_add]

/-- **`weakTau` witness pointwise evaluation.** Combines `weakTau.witness_run`
with `PMF.pure_bind` to give that running the extracted witness scheduler from
a specific state `s_pre` (Dirac at `s_pre`) gives back `μ` pointwise. -/
private lemma weakTau_witness_run_at_state
    {sys : LabelledSystem State Label} {s_pre : State} {μ : PMF State}
    (h_wt : weakTau sys (PMF.pure s_pre) μ) (s_last : State) :
    h_wt.witness.run h_wt.witness_fuel s_pre s_last = μ s_last := by
  have h_run : (PMF.pure s_pre).bind (h_wt.witness.run h_wt.witness_fuel) = μ :=
    h_wt.witness_run
  rw [PMF.pure_bind] at h_run
  exact congrArg (fun f => f s_last) h_run

/-- **Marginal collapse via `weakTau` witness.** The chain-end-state marginal
of `chainProb` over the witness scheduler equals the target distribution `μ`
evaluated at the end state. This combines
`chainProb_endState_marginal_of_boundedFuel` with the witness pointwise eval
(`weakTau_witness_run_at_state`).

Note: `h_wt.witness` IS `σ.boundedFuel`-wrapped by construction, so the
boundedFuel marginal lemma applies directly. -/
private lemma chainProb_witness_endState_marginal
    {sys : LabelledSystem State Label} {s_pre : State} {μ : PMF State}
    (h_wt : weakTau sys (PMF.pure s_pre) μ) (s_last : State) :
    (∑' chain : List (Label × State),
      (open Classical in
        if (chain.getLast?.map Prod.snd).getD s_pre = s_last then
          chainProb h_wt.witness ⟨s_pre, Seq.nil⟩ chain
        else 0)) = μ s_last := by
  -- Unfold witness as `σ.boundedFuel n`.
  unfold weakTau.witness
  -- Apply the boundedFuel marginal lemma.
  rw [chainProb_endState_marginal_of_boundedFuel h_wt.choose h_wt.witness_fuel s_pre s_last]
  -- Now show ((h_wt.choose.boundedFuel h_wt.witness_fuel).run h_wt.witness_fuel s_pre) s_last
  --   = μ s_last via witness_run + pure_bind.
  have h_eq : (h_wt.choose.boundedFuel h_wt.witness_fuel).run h_wt.witness_fuel s_pre
      = h_wt.witness.run h_wt.witness_fuel s_pre := rfl
  rw [h_eq]
  exact weakTau_witness_run_at_state h_wt s_last

-- **`tightStepFactor` is zero when `e_w_pre.trans` does not terminate.**
private lemma tightStepFactor_eq_zero_of_e_w_pre_not_terminates
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_pre : AlterSeq State Label) (l : Label)
    (e_iter_start e : AlterSeq State Label)
    (h : ¬ e_w_pre.trans.Terminates) :
    tightStepFactor sys pe' e_w_pre l e_iter_start e = 0 := by
  classical
  unfold tightStepFactor
  simp [h]

-- **`tightStepFactor` is zero when `e_iter_start.trans` does not terminate.**
private lemma tightStepFactor_eq_zero_of_iter_start_not_terminates
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_pre : AlterSeq State Label) (l : Label)
    (e_iter_start e : AlterSeq State Label)
    (h : ¬ e_iter_start.trans.Terminates) :
    tightStepFactor sys pe' e_w_pre l e_iter_start e = 0 := by
  classical
  unfold tightStepFactor
  by_cases h1 : e_w_pre.trans.Terminates
  · simp [h1, h]
  · simp [h1]

-- **`tightStepFactor` is zero when `e.trans` does not terminate.**
private lemma tightStepFactor_eq_zero_of_e_not_terminates
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_pre : AlterSeq State Label) (l : Label)
    (e_iter_start e : AlterSeq State Label)
    (h : ¬ e.trans.Terminates) :
    tightStepFactor sys pe' e_w_pre l e_iter_start e = 0 := by
  classical
  unfold tightStepFactor
  by_cases h1 : e_w_pre.trans.Terminates
  · by_cases h2 : e_iter_start.trans.Terminates
    · simp [h1, h2, h]
    · simp [h1, h2]
  · simp [h1]

-- **Filtering an all-internal list yields the nil seq.** Auxiliary for the
-- chain trace computation: an all-internal `chain_pre` contributes no entries
-- to the external trace.
private lemma seq_filter_internal_list_eq_nil
    (sys : LabelledSystem State Label)
    (chain_pre : List (Label × State))
    (h_chain_int : ∀ pair ∈ chain_pre, sys.internal pair.1) :
    (Seq.ofList chain_pre).filter (fun p => ¬ sys.internal p.1) = Seq.nil := by
  classical
  induction chain_pre with
  | nil => rw [Seq.ofList_nil, Seq.filter_nil]
  | cons a t ih =>
    have h_a : sys.internal a.1 := h_chain_int a (List.mem_cons_self)
    have h_t : ∀ pair ∈ t, sys.internal pair.1 :=
      fun p hp => h_chain_int p (List.mem_cons_of_mem _ hp)
    rw [Seq.ofList_cons, Seq.filter_cons_neg a _ (fun h => h h_a)]
    exact ih h_t

-- **Trace factorisation through an all-internal chain ending with an
-- external step.** When `e.trans = trans_prev ++ Seq.ofList chain_pre
-- ++ [(l_τ, s_last)]` with `chain_pre` all-internal and `l_τ` external,
-- the trace splits as `(trace ⟨e.init, trans_prev⟩) ++ [l_τ]`.
private lemma trace_append_internal_chain_external
    (sys : LabelledSystem State Label) (s_init : State)
    (trans_prev : Seq (Label × State)) (h_prev_term : trans_prev.Terminates)
    (chain_pre : List (Label × State))
    (h_chain_int : ∀ pair ∈ chain_pre, sys.internal pair.1)
    (l_τ : Label) (s_last : State) (h_ext : ¬ sys.internal l_τ) :
    sys.trace ⟨s_init, trans_prev.append
        ((Seq.ofList chain_pre).append (Seq.cons (l_τ, s_last) Seq.nil))⟩
      = (sys.trace ⟨s_init, trans_prev⟩).append (Seq.cons l_τ Seq.nil) := by
  classical
  unfold LabelledSystem.trace
  change ((trans_prev.append
            ((Seq.ofList chain_pre).append (Seq.cons (l_τ, s_last) Seq.nil))).filter
            (fun p => ¬ sys.internal p.1)).map Prod.fst
      = ((trans_prev.filter (fun p => ¬ sys.internal p.1)).map Prod.fst).append
          (Seq.cons l_τ Seq.nil)
  have h_chain_term : (Seq.ofList chain_pre).Terminates :=
    Seq.terminates_ofList chain_pre
  rw [Seq.filter_append _ _ _ h_prev_term,
      Seq.filter_append _ _ _ h_chain_term,
      seq_filter_internal_list_eq_nil sys chain_pre h_chain_int,
      Seq.nil_append,
      Seq.filter_cons_pos (l_τ, s_last) _ h_ext,
      Seq.filter_nil,
      Seq.map_append, Seq.map_cons, Seq.map_nil]

/-
**Trace-mismatch zero:** when `sys.trace e_iter_start ≠ τ_prev`, every
`e` in the tight-cylinder `T_τ` (with `τ = τ_prev ++ [l_τ]`) that
extends `e_iter_start` has `tightStepFactor _ _ _ l_τ e_iter_start e = 0`.

Reason: `tightStepFactor` is supported only on `e` whose chain (from
`e_iter_start`) is *all-internal* before the final external `(l_τ, _)`.
For such `e`, `sys.trace e = sys.trace e_iter_start ++ [l_τ]`. If
`sys.trace e_iter_start ≠ τ_prev`, then no such `e` can have
`sys.trace e = τ_prev ++ [l_τ]`, forcing the factor to vanish.
-/
private lemma tightStepFactor_eq_zero_of_trace_mismatch
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (τ_prev : Seq Label) (l_τ : Label)
    (e_w_pre e_iter_start e : AlterSeq State Label)
    (h_e_term : e.trans.Terminates)
    (h_e_trace : sys.trace e = τ_prev.append (Seq.cons l_τ Seq.nil))
    (_h_e_tight : sys.IsTight e)
    (h_trace_mismatch : sys.trace e_iter_start ≠ τ_prev) :
    tightStepFactor sys pe' e_w_pre l_τ e_iter_start e = 0 := by
  classical
  unfold tightStepFactor
  by_cases h_ewp : e_w_pre.trans.Terminates
  swap
  · simp [h_ewp]
  by_cases h_es : e_iter_start.trans.Terminates
  swap
  · simp [h_ewp, h_es]
  rw [dif_pos h_ewp, dif_pos h_es, dif_pos h_e_term]
  -- Set up the locals exactly as in the definition.
  set s_pre : State := e_w_pre.endState h_ewp with hs_pre
  set e_iter_start_list : List (Label × State) := e_iter_start.trans.toList h_es
    with h_eis_list
  set e_list : List (Label × State) := e.trans.toList h_e_term with h_e_list
  by_cases h_prefix : e_iter_start.init = e.init ∧
                  e_list.take e_iter_start_list.length = e_iter_start_list
  swap
  · simp [h_prefix]
  rw [dif_pos h_prefix]
  set chain : List (Label × State) := e_list.drop e_iter_start_list.length with h_chain
  -- Reduce to: every summand is 0.
  refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
  by_cases h_supp : some (l_τ, μ) ∈ (pe'.scheduler.next e_w_pre).support
  swap
  · simp [h_supp]
  rw [dif_pos h_supp]
  by_cases h_int : sys.internal l_τ
  · -- Internal: the visible branch is zero by construction.
    simp [h_int]
  rw [dif_neg h_int]
  -- Now we are in the deep external branch with a match on `chain.getLast?`.
  cases h_last : chain.getLast? with
  | none => simp
  | some last_pair =>
    simp only [] -- reduce the match.
    -- If `last_pair.1 ≠ l_τ` the value is 0 by the inner `if`.
    by_cases h_l_eq : last_pair.1 = l_τ
    swap
    · simp [h_l_eq]
    rw [if_pos h_l_eq]
    -- All-internal condition for `chain.dropLast`.
    by_cases h_all_int : ∀ pair ∈ chain.dropLast, sys.internal pair.1
    swap
    · rw [if_neg h_all_int]; ring
    rw [if_pos h_all_int]
    -- All structural conditions hold: derive the contradiction.
    exfalso
    -- Extract the list structure: `e_list = e_iter_start_list ++ chain` and
    -- `chain = chain.dropLast ++ [last_pair]`.
    have h_take_drop : e_iter_start_list ++ chain = e_list := by
      conv_rhs => rw [← List.take_append_drop e_iter_start_list.length e_list]
      rw [h_prefix.2]
    have h_chain_ne : chain ≠ [] := by
      intro h_empty
      rw [h_empty, List.getLast?_nil] at h_last
      exact absurd h_last (by intro h; cases h)
    have h_chain_split : chain = chain.dropLast ++ [last_pair] := by
      have hL : chain.getLast h_chain_ne = last_pair := by
        rw [← Option.some_inj, ← List.getLast?_eq_some_getLast]
        exact h_last
      conv_lhs => rw [← List.dropLast_append_getLast h_chain_ne, hL]
    -- Reconstruct `e.trans` as a Seq-level append.
    have h_e_trans_split :
        e.trans = e_iter_start.trans.append
          ((Seq.ofList chain.dropLast).append (Seq.cons last_pair Seq.nil)) := by
      have h_e_eq : e.trans = Seq.ofList e_list := by
        rw [h_e_list]; exact (Seq.ofList_toList _ _).symm
      have h_eis_eq : e_iter_start.trans = Seq.ofList e_iter_start_list := by
        rw [h_eis_list]; exact (Seq.ofList_toList _ _).symm
      rw [h_e_eq, ← h_take_drop]
      conv_lhs => rw [show chain = chain.dropLast ++ [last_pair] from h_chain_split]
      rw [← List.append_assoc,
          Seq.ofList_append, Seq.ofList_append, Seq.ofList_cons, Seq.ofList_nil,
          ← h_eis_eq, Seq.append_assoc]
    -- Compute `sys.trace e` via the helper.
    have h_last_pair_form : last_pair = (l_τ, last_pair.2) := by
      ext
      · exact h_l_eq
      · rfl
    have h_trace_e :
        sys.trace e = (sys.trace e_iter_start).append (Seq.cons l_τ Seq.nil) := by
      -- Unfold `LabelledSystem.trace` at `e` and use the trans split.
      change ((e.trans.filter (fun p => ¬ sys.internal p.1)).map Prod.fst : Seq Label)
          = _
      rw [h_e_trans_split]
      have h_l_eq' : (last_pair.1, last_pair.2) = (l_τ, last_pair.2) := by
        rw [h_l_eq]
      have h_last_pair_form' : last_pair = (l_τ, last_pair.2) := by
        conv_lhs => rw [← Prod.mk.eta (p := last_pair)]
        exact h_l_eq'
      have h_iter_form :
          (⟨e_iter_start.init, e_iter_start.trans⟩ : AlterSeq State Label)
            = e_iter_start := by
        rcases e_iter_start with ⟨a, b⟩; rfl
      rw [h_last_pair_form']
      change ((e_iter_start.trans.append
                ((Seq.ofList chain.dropLast).append
                  (Seq.cons (l_τ, last_pair.2) Seq.nil))).filter
            (fun p => ¬ sys.internal p.1)).map Prod.fst
          = _
      have h_via_helper :=
        trace_append_internal_chain_external sys e_iter_start.init e_iter_start.trans
          h_es chain.dropLast h_all_int l_τ last_pair.2 h_int
      change sys.trace ⟨e_iter_start.init, _⟩ = _ at h_via_helper
      rw [show ((e_iter_start.trans.append ((Seq.ofList chain.dropLast).append
                (Seq.cons (l_τ, last_pair.2) Seq.nil))).filter
            (fun p => ¬ sys.internal p.1)).map Prod.fst
          = sys.trace ⟨e_iter_start.init, e_iter_start.trans.append
              ((Seq.ofList chain.dropLast).append
                (Seq.cons (l_τ, last_pair.2) Seq.nil))⟩ from rfl,
          h_via_helper, h_iter_form]
    -- Combine with `h_e_trace` and `append_singleton_inj_left`.
    have h_trace_eq :
        (sys.trace e_iter_start).append (Seq.cons l_τ Seq.nil)
          = τ_prev.append (Seq.cons l_τ Seq.nil) := by
      rw [← h_trace_e]; exact h_e_trace
    have h_trace_iter_term : (sys.trace e_iter_start).Terminates :=
      trace_terminates_of_trans_terminates sys e_iter_start h_es
    have h_trace_prev_term : τ_prev.Terminates := by
      -- `τ_prev.Terminates` follows from `sys.trace e_iter_start` terminating
      -- (which it does, by `trace_terminates_of_trans_terminates`), since both
      -- equal one another up to a trailing `[l_τ]`. We extract it from
      -- `h_trace_eq` via a direct `get?`-based argument.
      have h_trace_e_term : (sys.trace e).Terminates :=
        trace_terminates_of_trans_terminates sys e h_e_term
      rw [h_e_trace] at h_trace_e_term
      obtain ⟨n, hn⟩ := h_trace_e_term
      by_contra h_not
      have h_all_not : ∀ k, ¬ τ_prev.TerminatedAt k := by
        intro k h_term_k
        exact h_not ⟨k, h_term_k⟩
      have h_get_eq : (τ_prev.append (Seq.cons l_τ Seq.nil)).get? n = τ_prev.get? n :=
        Seq.get?_append_before_length (h_all_not n)
      have h_τ_term_n : τ_prev.TerminatedAt n := by
        change τ_prev.get? n = none
        rw [← h_get_eq]; exact hn
      exact h_all_not n h_τ_term_n
    exact h_trace_mismatch
      (Seq.append_singleton_inj_left _ _ h_trace_iter_term h_trace_prev_term
        l_τ l_τ h_trace_eq)

/-- **Mass-collapse helper.** The chain/kernel/state triple sum that
appears in `tightStepFactor`'s value formula after the bijection step
collapses to `1`:

`∑' chain_pre, ∑' s_chain_last, chainProb (σ₀.boundedFuel n) _ chain_pre *`
  `(∑' μ_l, p (s_mid_pre chain_pre) μ_l * μ_l s_chain_last) = 1`

where `s_mid_pre chain_pre = (chain_pre.getLast?.map Prod.snd).getD s_pre`.

This is the Step-3 mass collapse from the docstring of
`tightStepFactor_sum_eq_witness_emission_of_trace_match`. The collapses
are: (i) inner `s_chain_last`-sum via `PMF.tsum_coe` for each `μ_l`,
(ii) the resulting `μ_l`-sum collapses via `PMF.tsum_coe` on `p _`,
(iii) the remaining `chain_pre`-sum collapses via
`chainProb_total_mass_of_boundedFuel`. -/
private lemma chainProb_kernel_state_mass_collapse
    {sys : LabelledSystem State Label}
    (σ : WeakScheduler sys) (n : ℕ) (s_pre : State)
    (p : State → PMF (PMF State)) :
    (∑' chain_pre : List (Label × State), ∑' s_chain_last : State,
        chainProb (σ.boundedFuel n) ⟨s_pre, Seq.nil⟩ chain_pre *
          (∑' μ_l : PMF State,
            p ((chain_pre.getLast?.map Prod.snd).getD s_pre) μ_l *
              μ_l s_chain_last)) = 1 := by
  classical
  -- Step 1: For each `chain_pre`, the inner `(s_chain_last, μ_l)` double sum
  -- collapses to `1`.
  have h_inner : ∀ chain_pre : List (Label × State),
      (∑' s_chain_last : State, ∑' μ_l : PMF State,
          p ((chain_pre.getLast?.map Prod.snd).getD s_pre) μ_l *
            μ_l s_chain_last) = 1 := by
    intro chain_pre
    set s_mid := (chain_pre.getLast?.map Prod.snd).getD s_pre with h_s_mid
    -- Swap order: ∑' s, ∑' μ_l ... = ∑' μ_l, ∑' s ...
    rw [ENNReal.tsum_comm]
    -- For each μ_l: ∑' s, p s_mid μ_l * μ_l s = p s_mid μ_l * (∑' s, μ_l s)
    --                                          = p s_mid μ_l * 1 = p s_mid μ_l
    have h_per_μ_l : ∀ μ_l : PMF State,
        (∑' s_chain_last : State, p s_mid μ_l * μ_l s_chain_last)
          = p s_mid μ_l := by
      intro μ_l
      rw [ENNReal.tsum_mul_left, μ_l.tsum_coe, mul_one]
    rw [tsum_congr h_per_μ_l]
    -- Now: ∑' μ_l, p s_mid μ_l = 1 by PMF.tsum_coe.
    exact (p s_mid).tsum_coe
  -- Step 2: Push the `chain_pre` factor out and apply the inner collapse.
  -- For each chain_pre:
  --   ∑' s, chainProb _ chain_pre * (∑' μ_l, ...)
  --     = chainProb _ chain_pre * (∑' s, ∑' μ_l, ...)
  --     = chainProb _ chain_pre * 1
  --     = chainProb _ chain_pre.
  have h_per_chain : ∀ chain_pre : List (Label × State),
      (∑' s_chain_last : State,
          chainProb (σ.boundedFuel n) ⟨s_pre, Seq.nil⟩ chain_pre *
            (∑' μ_l : PMF State,
              p ((chain_pre.getLast?.map Prod.snd).getD s_pre) μ_l *
                μ_l s_chain_last))
        = chainProb (σ.boundedFuel n) ⟨s_pre, Seq.nil⟩ chain_pre := by
    intro chain_pre
    rw [ENNReal.tsum_mul_left, h_inner chain_pre, mul_one]
  rw [tsum_congr h_per_chain]
  -- Step 3: Sum chainProb over all chains via `chainProb_total_mass_of_boundedFuel`.
  exact chainProb_total_mass_of_boundedFuel σ n s_pre

-- **Forward map of the tight-cylinder chain bijection.** Given an
-- `(e_iter_start, chain_pre : List _ all-internal, s_chain_last : State)`
-- triple plus the external `l_τ`, builds the AlterSeq `e` whose `trans`
-- factors as
--   `e_iter_start.trans ++ Seq.ofList chain_pre ++ [(l_τ, s_chain_last)]`
-- and whose `init = e_iter_start.init`. This `e` is tight (final step
-- external) and has trace `(sys.trace e_iter_start).append [l_τ]`.
--
-- Used as the forward direction of the bijection underpinning
-- `tightStepFactor_sum_eq_witness_emission_of_trace_match`. The
-- corresponding backward direction is `tight_trans_split_last_witness`
-- combined with `trace_append_internal_chain_external` (extracts
-- `(chain_pre, s_chain_last)` from a tight `e` extending `e_iter_start`
-- with the right trace).
private def tightChainExtFwd
    (sys : LabelledSystem State Label)
    (l_τ : Label) (_h_l_τ_ext : ¬ sys.internal l_τ)
    (e_iter_start : AlterSeq State Label)
    (_h_iter_term : e_iter_start.trans.Terminates)
    (chain_pre : List (Label × State)) (s_chain_last : State) :
    AlterSeq State Label :=
  ⟨e_iter_start.init,
    e_iter_start.trans.append
      ((Seq.ofList chain_pre).append (Seq.cons (l_τ, s_chain_last) Seq.nil))⟩

-- **Forward map yields a terminating `trans`.** The chain prefix is finite
-- and the final entry is a singleton, so the appended `trans` terminates.
private lemma tightChainExtFwd_trans_terminates
    (sys : LabelledSystem State Label)
    (l_τ : Label) (h_l_τ_ext : ¬ sys.internal l_τ)
    (e_iter_start : AlterSeq State Label)
    (h_iter_term : e_iter_start.trans.Terminates)
    (chain_pre : List (Label × State)) (s_chain_last : State) :
    (tightChainExtFwd sys l_τ h_l_τ_ext e_iter_start h_iter_term
        chain_pre s_chain_last).trans.Terminates := by
  unfold tightChainExtFwd
  change (e_iter_start.trans.append
    ((Seq.ofList chain_pre).append (Seq.cons (l_τ, s_chain_last) Seq.nil))).Terminates
  have h_chain_term : (Seq.ofList chain_pre).Terminates :=
    Seq.terminates_ofList chain_pre
  have h_singleton_term : (Seq.cons (l_τ, s_chain_last) Seq.nil :
      Seq (Label × State)).TerminatedAt 1 := by
    change (Seq.cons (l_τ, s_chain_last) Seq.nil :
      Seq (Label × State)).get? 1 = none
    rw [Seq.get?_cons_succ]; rfl
  have h_tail_term :
      ((Seq.ofList chain_pre).append (Seq.cons (l_τ, s_chain_last) Seq.nil)).Terminates :=
    ⟨_, Seq.terminatedAt_append_find h_chain_term h_singleton_term⟩
  exact ⟨_, Seq.terminatedAt_append_find h_iter_term (Nat.find_spec h_tail_term)⟩

-- **Forward map yields a tight execution with trace `τ_prev ++ [l_τ]`.**
-- The final step is the external `l_τ`-emission, so `IsTight` holds; the
-- trace splits via `trace_append_internal_chain_external`.
private lemma tightChainExtFwd_trace
    (sys : LabelledSystem State Label)
    (l_τ : Label) (h_l_τ_ext : ¬ sys.internal l_τ)
    (e_iter_start : AlterSeq State Label)
    (h_iter_term : e_iter_start.trans.Terminates)
    (chain_pre : List (Label × State))
    (h_chain_int : ∀ pair ∈ chain_pre, sys.internal pair.1)
    (s_chain_last : State) :
    sys.trace (tightChainExtFwd sys l_τ h_l_τ_ext e_iter_start h_iter_term
        chain_pre s_chain_last)
      = (sys.trace e_iter_start).append (Seq.cons l_τ Seq.nil) := by
  unfold tightChainExtFwd
  exact trace_append_internal_chain_external sys e_iter_start.init
    e_iter_start.trans h_iter_term chain_pre h_chain_int l_τ s_chain_last
    h_l_τ_ext

-- **Forward map yields a tight execution.** The final step is external.
private lemma tightChainExtFwd_isTight
    (sys : LabelledSystem State Label)
    (l_τ : Label) (h_l_τ_ext : ¬ sys.internal l_τ)
    (e_iter_start : AlterSeq State Label)
    (h_iter_term : e_iter_start.trans.Terminates)
    (chain_pre : List (Label × State)) (s_chain_last : State) :
    sys.IsTight (tightChainExtFwd sys l_τ h_l_τ_ext e_iter_start h_iter_term
        chain_pre s_chain_last) := by
  classical
  right
  -- We need to exhibit an index `n` and the final-step external structure.
  -- The index is the length of `e_iter_start.trans ++ Seq.ofList chain_pre`.
  set e := tightChainExtFwd sys l_τ h_l_τ_ext e_iter_start h_iter_term
    chain_pre s_chain_last with h_e_def
  have h_chain_term : (Seq.ofList chain_pre).Terminates :=
    Seq.terminates_ofList chain_pre
  have h_singleton_term : (Seq.cons (l_τ, s_chain_last) Seq.nil :
      Seq (Label × State)).TerminatedAt 1 := by
    change (Seq.cons (l_τ, s_chain_last) Seq.nil :
      Seq (Label × State)).get? 1 = none
    rw [Seq.get?_cons_succ]; rfl
  have h_pre_chain_term :
      (e_iter_start.trans.append (Seq.ofList chain_pre)).Terminates :=
    ⟨_, Seq.terminatedAt_append_find h_iter_term (Nat.find_spec h_chain_term)⟩
  set n := Nat.find h_pre_chain_term with h_n_def
  refine ⟨n, l_τ, s_chain_last, ?_, ?_, h_l_τ_ext⟩
  · -- `e.trans.get? n = some (l_τ, s_chain_last)`.
    have h_e_trans :
        e.trans = e_iter_start.trans.append
          ((Seq.ofList chain_pre).append (Seq.cons (l_τ, s_chain_last) Seq.nil)) := rfl
    rw [h_e_trans, ← Seq.append_assoc]
    have := Seq.get?_append_find h_pre_chain_term (Seq.cons (l_τ, s_chain_last) Seq.nil) 0
    simpa using this
  · -- `e.trans.TerminatedAt (n + 1)`.
    have h_e_trans :
        e.trans = e_iter_start.trans.append
          ((Seq.ofList chain_pre).append (Seq.cons (l_τ, s_chain_last) Seq.nil)) := rfl
    rw [h_e_trans, ← Seq.append_assoc]
    exact Seq.terminatedAt_append_find h_pre_chain_term h_singleton_term

-- **Forward map injectivity.** Two `(chain_pre, s_chain_last)` pairs mapping
-- to the same `e` agree pointwise. Proof: `tightChainExtFwd`'s `.trans` field
-- is `e_iter_start.trans ++ (Seq.ofList chain_pre ++ [(l_τ, s_chain_last)])`.
-- Splitting at the final external step gives `Seq.ofList chain_pre = Seq.ofList
-- chain_pre'` (hence `chain_pre = chain_pre'` by `Seq.ofList_injective`) and
-- `s_chain_last = s_chain_last'`.
private lemma tightChainExtFwd_injective
    (sys : LabelledSystem State Label)
    (l_τ : Label) (h_l_τ_ext : ¬ sys.internal l_τ)
    (e_iter_start : AlterSeq State Label)
    (h_iter_term : e_iter_start.trans.Terminates) :
    Function.Injective (fun (p : List (Label × State) × State) =>
      tightChainExtFwd sys l_τ h_l_τ_ext e_iter_start h_iter_term p.1 p.2) := by
  rintro ⟨cp1, s1⟩ ⟨cp2, s2⟩ h_eq
  unfold tightChainExtFwd at h_eq
  have h_trans_eq :
      e_iter_start.trans.append
          ((Seq.ofList cp1).append (Seq.cons (l_τ, s1) Seq.nil))
        = e_iter_start.trans.append
            ((Seq.ofList cp2).append (Seq.cons (l_τ, s2) Seq.nil)) := by
    have := congrArg AlterSeq.trans h_eq; exact this
  -- Reassociate and use `Seq.append_singleton_inj_left/right`.
  rw [← Seq.append_assoc, ← Seq.append_assoc] at h_trans_eq
  have h_cp1_term : (Seq.ofList cp1).Terminates := Seq.terminates_ofList cp1
  have h_cp2_term : (Seq.ofList cp2).Terminates := Seq.terminates_ofList cp2
  have h_pre1_term :
      (e_iter_start.trans.append (Seq.ofList cp1)).Terminates :=
    ⟨_, Seq.terminatedAt_append_find h_iter_term (Nat.find_spec h_cp1_term)⟩
  have h_pre2_term :
      (e_iter_start.trans.append (Seq.ofList cp2)).Terminates :=
    ⟨_, Seq.terminatedAt_append_find h_iter_term (Nat.find_spec h_cp2_term)⟩
  have h_pair_eq : (l_τ, s1) = (l_τ, s2) :=
    Seq.append_singleton_inj_right _ _ h_pre1_term h_pre2_term (l_τ, s1) (l_τ, s2)
      h_trans_eq
  have h_s_eq : s1 = s2 := (Prod.mk.inj h_pair_eq).2
  have h_pre_eq :
      e_iter_start.trans.append (Seq.ofList cp1)
        = e_iter_start.trans.append (Seq.ofList cp2) :=
    Seq.append_singleton_inj_left _ _ h_pre1_term h_pre2_term (l_τ, s1) (l_τ, s2)
      h_trans_eq
  -- From `e_iter_start.trans ++ X = e_iter_start.trans ++ Y`, derive `X = Y` via
  -- `Seq.toList_append` and `List.append_cancel_left`.
  have h_pre_toList_eq :
      (e_iter_start.trans.append (Seq.ofList cp1)).toList h_pre1_term
        = (e_iter_start.trans.append (Seq.ofList cp2)).toList h_pre2_term := by
    congr 1
  rw [Seq.toList_append _ _ h_iter_term h_cp1_term h_pre1_term,
      Seq.toList_append _ _ h_iter_term h_cp2_term h_pre2_term] at h_pre_toList_eq
  have h_cp_list_eq :
      (Seq.ofList cp1).toList h_cp1_term = (Seq.ofList cp2).toList h_cp2_term :=
    List.append_cancel_left h_pre_toList_eq
  have h_cp_eq : cp1 = cp2 := by
    have := h_cp_list_eq
    rw [Seq.toList_ofList cp1, Seq.toList_ofList cp2] at this
    exact this
  exact Prod.ext h_cp_eq h_s_eq

-- **Forward-map `trans.toList` factorisation.**
private lemma tightChainExtFwd_trans_toList
    (sys : LabelledSystem State Label)
    (l_τ : Label) (h_l_τ_ext : ¬ sys.internal l_τ)
    (e_iter_start : AlterSeq State Label)
    (h_iter_term : e_iter_start.trans.Terminates)
    (chain_pre : List (Label × State)) (s_chain_last : State) :
    let e := tightChainExtFwd sys l_τ h_l_τ_ext e_iter_start h_iter_term
      chain_pre s_chain_last
    let h_e_term : e.trans.Terminates :=
      tightChainExtFwd_trans_terminates sys l_τ h_l_τ_ext e_iter_start
        h_iter_term chain_pre s_chain_last
    e.trans.toList h_e_term
      = e_iter_start.trans.toList h_iter_term ++ chain_pre ++
        [(l_τ, s_chain_last)] := by
  classical
  simp only
  have h_chain_term : (Seq.ofList chain_pre).Terminates :=
    Seq.terminates_ofList chain_pre
  have h_singleton_term :
      (Seq.cons (l_τ, s_chain_last) Seq.nil : Seq (Label × State)).Terminates := by
    refine ⟨1, ?_⟩
    change (Seq.cons (l_τ, s_chain_last) Seq.nil : Seq (Label × State)).get? 1 = none
    rw [Seq.get?_cons_succ]; rfl
  have h_tail_term :
      ((Seq.ofList chain_pre).append (Seq.cons (l_τ, s_chain_last) Seq.nil)).Terminates :=
    ⟨_, Seq.terminatedAt_append_find h_chain_term (Nat.find_spec h_singleton_term)⟩
  have h_combined :
      (e_iter_start.trans.append
        ((Seq.ofList chain_pre).append (Seq.cons (l_τ, s_chain_last) Seq.nil))).Terminates :=
    ⟨_, Seq.terminatedAt_append_find h_iter_term (Nat.find_spec h_tail_term)⟩
  -- Rewrite via `change` to avoid the dependent-proof rewrite issue.
  have h_single_list : (Seq.cons (l_τ, s_chain_last) Seq.nil :
      Seq (Label × State)).toList h_singleton_term = [(l_τ, s_chain_last)] := by
    rw [Seq.toList_cons h_singleton_term]
    congr 1
    exact Seq.toList_nil
  change (e_iter_start.trans.append
      ((Seq.ofList chain_pre).append (Seq.cons (l_τ, s_chain_last) Seq.nil))).toList
        h_combined
      = e_iter_start.trans.toList h_iter_term ++ chain_pre ++ [(l_τ, s_chain_last)]
  rw [Seq.toList_append _ _ h_iter_term h_tail_term]
  rw [Seq.toList_append _ _ h_chain_term h_singleton_term]
  rw [Seq.toList_ofList chain_pre]
  rw [h_single_list]
  rw [List.append_assoc]

/-
**Trace-match witness-emission identity.** When `e_iter_start.trans`
terminates and `sys.trace e_iter_start = τ_prev`, summing
`tightStepFactor sys pe' e_w_pre l_τ e_iter_start e` over all tight `e`
with trace `τ_prev ++ [l_τ]` equals the total `l_τ`-emission mass
`∑' μ, pe'.scheduler.next e_w_pre (some (l_τ, μ))`.

Proof sketch (deferred):
1. Establish a bijection between
     `{e ∈ T_{τ_prev ++ [l_τ]} // e_iter_start prefix of e, tightStepFactor ≠ 0}`
   and
     `(chain_pre : List (Label × State)) × State`
   where `chain_pre` is the all-internal prefix and the state is
   `s_chain_last` (the second component of the final external
   `(l_τ, _)` step). Each chain ends with `(l_τ, s_chain_last)`.
2. Under this bijection, `tightStepFactor` evaluates to
     `∑' μ, pe'.scheduler.next e_w_pre (some (l_τ, μ)) *
              chainProb σ_pre ⟨s_pre, Seq.nil⟩ chain_pre *
              (∑' μ_l, p s_mid_pre μ_l * μ_l s_chain_last)`
   where `σ_pre = h_ws.weakTau_pre.witness` (now a `boundedFuel`
   bounded scheduler) and `p = h_ws.hyperStep_mid.kernel`.
3. Sum first over `(chain_pre, s_chain_last)`. The `s_chain_last`-sum
   collapses `∑' s_chain_last, μ_l s_chain_last = 1` (by
   `PMF.tsum_coe`) for each `μ_l`. The remaining `chain_pre`-sum
   collapses by `chainProb_total_mass_of_boundedFuel σ_pre witness_fuel`
   to `1`. The `μ_l`-sum collapses by `PMF.tsum_coe` on `p s_mid_pre`
   to `1`. What remains is the outer `μ`-sum over
   `pe'.scheduler.next e_w_pre (some (l_τ, μ))`.

The Step-3 collapse is encapsulated as the proven helper
`chainProb_kernel_state_mass_collapse` above.

**Available bijection scaffolding** (proved above):

* `tightChainExtFwd sys l_τ h_l_τ_ext e_iter_start h_iter_term chain_pre
   s_chain_last` — the forward map building `e` from
   `(chain_pre, s_chain_last)`.
* `tightChainExtFwd_trans_terminates` — `e.trans` terminates.
* `tightChainExtFwd_trace` — `sys.trace e = (sys.trace e_iter_start) ++ [l_τ]`.
* `tightChainExtFwd_isTight` — `sys.IsTight e` (final step external).

The forward map is injective on `(chain_pre, s_chain_last)` (modulo
the all-internal constraint on `chain_pre`) and surjective onto the
tight-cylinder subtype of `e` extending `e_iter_start` with the right
chain structure; the backward direction is `tight_trans_split_last_witness`
(splits `e.trans` at the final external step) plus
`trace_append_internal_chain_external` (recovers the trace factorisation).

Status: deferred (the substantive content — ~150+ lines of bijection
and mass-assembly work). The forward-map scaffolding above reduces
the remaining work to: (i) prove forward-map injectivity, (ii) prove
surjectivity onto the support of `tightStepFactor`, (iii) apply
`Equiv.tsum_eq` and `chainProb_kernel_state_mass_collapse`.
-/

/-- **Per-`μ` inner factor of `tightStepFactor`** when the external label `l_τ`
fires through scheduler-output `(l_τ, μ)`. Encapsulates the dependent-typing
weakStep-witness extraction inside one definition, so the unfolding lemma
`tightStepFactor_unfold_external` can express `tightStepFactor` as a clean
`∑' μ, scheduler.next * perMu_inner` form.

When `(l_τ, μ) ∈ support` and `chain_pre = e.trans.toList.drop iter_list.length`
(after stripping the final external entry, so `chain_pre` is the all-internal
prefix of the chain between `e_iter_start` and `e`), the value is

  `chainProb σ_pre ⟨s_pre, Seq.nil⟩ chain_pre *
     (∑' μ_l, p s_mid_pre μ_l * μ_l s_chain_last)`

with `σ_pre = h_ws.weakTau_pre.witness` and `p = h_ws.hyperStep_mid.kernel`. -/
private noncomputable def tightStepFactor_perMu_inner
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_pre : AlterSeq State Label) (h_ewp : e_w_pre.trans.Terminates)
    (l_τ : Label) (h_l_τ_external : ¬ sys.internal l_τ)
    (chain_pre : List (Label × State)) (s_chain_last : State)
    (μ : PMF State) : ENNReal :=
  open Classical in
  if h_supp : some (l_τ, μ) ∈ (pe'.scheduler.next e_w_pre).support then
    let s_pre : State := e_w_pre.endState h_ewp
    have h_sw : sys^w.step s_pre l_τ μ :=
      pe'.scheduler.valid e_w_pre (Nat.find h_ewp) s_pre
        (Nat.find_spec h_ewp)
        (AlterSeq.stateAt_find_eq_endState e_w_pre h_ewp)
        l_τ μ h_supp
    have h_ws : weakStep sys (PMF.pure s_pre) l_τ μ := by
      rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
      · exact absurd h_int' h_l_τ_external
      · exact h
    let s_mid_pre : State :=
      (chain_pre.getLast?.map Prod.snd).getD s_pre
    chainProb h_ws.weakTau_pre.witness ⟨s_pre, Seq.nil⟩ chain_pre *
      (∑' μ_l : PMF State,
        h_ws.hyperStep_mid.kernel s_mid_pre μ_l * μ_l s_chain_last)
  else 0

/-- **Per-`μ` total-mass identity.** For `μ ∈ support`, summing
`tightStepFactor_perMu_inner` over all `(chain_pre, s_chain_last)` collapses
to `1` via `chainProb_kernel_state_mass_collapse` (the `weakTau_pre.witness` is
a `boundedFuel`-bounded scheduler). -/
private lemma tightStepFactor_perMu_inner_total_mass
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_pre : AlterSeq State Label) (h_ewp : e_w_pre.trans.Terminates)
    (l_τ : Label) (h_l_τ_external : ¬ sys.internal l_τ)
    (μ : PMF State)
    (h_supp : some (l_τ, μ) ∈ (pe'.scheduler.next e_w_pre).support) :
    (∑' (chain_pre : List (Label × State)) (s_chain_last : State),
      tightStepFactor_perMu_inner sys pe' e_w_pre h_ewp l_τ h_l_τ_external
        chain_pre s_chain_last μ) = 1 := by
  classical
  -- Unfold the per-μ inner.
  unfold tightStepFactor_perMu_inner
  -- The `h_supp` branch fires.
  simp only [dif_pos h_supp]
  -- Set up the locals exactly as in the definition.
  set s_pre : State := e_w_pre.endState h_ewp with hs_pre
  have h_sw : sys^w.step s_pre l_τ μ :=
    pe'.scheduler.valid e_w_pre (Nat.find h_ewp) s_pre
      (Nat.find_spec h_ewp)
      (AlterSeq.stateAt_find_eq_endState e_w_pre h_ewp)
      l_τ μ h_supp
  have h_ws : weakStep sys (PMF.pure s_pre) l_τ μ := by
    rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
    · exact absurd h_int' h_l_τ_external
    · exact h
  -- Apply the mass-collapse helper.
  -- `weakTau_pre.witness = h_ws.weakTau_pre.choose.boundedFuel _`, exactly the
  -- form `chainProb_kernel_state_mass_collapse` expects.
  exact
    chainProb_kernel_state_mass_collapse
      h_ws.weakTau_pre.choose h_ws.weakTau_pre.witness_fuel s_pre
      h_ws.hyperStep_mid.kernel

/-- **Forward-map evaluation of `tightStepFactor` (zero on non-internal chain).**
If `chain_pre` has a non-internal entry, `tightStepFactor` evaluated on
`tightChainExtFwd ... chain_pre s_chain_last` is zero (forced by the inner
all-internal check). -/
private lemma tightStepFactor_eval_at_fwd_eq_zero_of_not_internal
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_pre : AlterSeq State Label) (h_ewp : e_w_pre.trans.Terminates)
    (l_τ : Label) (h_l_τ_external : ¬ sys.internal l_τ)
    (e_iter_start : AlterSeq State Label)
    (h_iter_term : e_iter_start.trans.Terminates)
    (chain_pre : List (Label × State))
    (h_chain_not_int : ¬ ∀ pair ∈ chain_pre, sys.internal pair.1)
    (s_chain_last : State) :
    tightStepFactor sys pe' e_w_pre l_τ e_iter_start
      (tightChainExtFwd sys l_τ h_l_τ_external e_iter_start h_iter_term
        chain_pre s_chain_last) = 0 := by
  classical
  set e := tightChainExtFwd sys l_τ h_l_τ_external e_iter_start h_iter_term
    chain_pre s_chain_last with h_e_def
  have h_e_term : e.trans.Terminates :=
    tightChainExtFwd_trans_terminates sys l_τ h_l_τ_external e_iter_start
      h_iter_term chain_pre s_chain_last
  unfold tightStepFactor
  rw [dif_pos h_ewp, dif_pos h_iter_term, dif_pos h_e_term]
  have h_init_eq : e.init = e_iter_start.init := rfl
  have h_toList :=
    tightChainExtFwd_trans_toList sys l_τ h_l_τ_external e_iter_start
      h_iter_term chain_pre s_chain_last
  simp only at h_toList
  set iter_list : List (Label × State) := e_iter_start.trans.toList h_iter_term
    with h_iter_list_def
  have h_prefix : e_iter_start.init = e.init ∧
      (e.trans.toList h_e_term).take iter_list.length = iter_list := by
    refine ⟨h_init_eq.symm, ?_⟩
    rw [h_toList]
    rw [List.append_assoc, List.take_left]
  rw [dif_pos h_prefix]
  have h_chain_eq :
      (e.trans.toList h_e_term).drop iter_list.length
        = chain_pre ++ [(l_τ, s_chain_last)] := by
    rw [h_toList]
    rw [List.append_assoc, List.drop_left]
  refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
  by_cases h_supp : some (l_τ, μ) ∈ (pe'.scheduler.next e_w_pre).support
  swap
  · simp [h_supp]
  rw [dif_pos h_supp, dif_neg h_l_τ_external]
  rw [h_chain_eq]
  have h_last_some : (chain_pre ++ [(l_τ, s_chain_last)]).getLast? =
      some (l_τ, s_chain_last) := by
    simp
  rw [h_last_some]
  have h_dropLast :
      (chain_pre ++ [(l_τ, s_chain_last)]).dropLast = chain_pre := by
    simp
  simp only [h_dropLast, if_true]
  rw [if_neg h_chain_not_int]
  simp

/-- **Forward-map evaluation of `tightStepFactor`.** When `chain_pre` is all
internal, `tightStepFactor` evaluated on `tightChainExtFwd ... chain_pre
s_chain_last` equals the per-μ inner factor summed against the scheduler
output. When `chain_pre` has a non-internal entry, the value is zero (forced
by the `all-internal` check inside `tightStepFactor`).

This is the cleanest unfolding through the forward map: dependent-typing
through `weakStep` extraction is hidden inside `tightStepFactor_perMu_inner`. -/
private lemma tightStepFactor_eval_at_fwd
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_pre : AlterSeq State Label) (h_ewp : e_w_pre.trans.Terminates)
    (l_τ : Label) (h_l_τ_external : ¬ sys.internal l_τ)
    (e_iter_start : AlterSeq State Label)
    (h_iter_term : e_iter_start.trans.Terminates)
    (chain_pre : List (Label × State))
    (h_chain_int : ∀ pair ∈ chain_pre, sys.internal pair.1)
    (s_chain_last : State) :
    tightStepFactor sys pe' e_w_pre l_τ e_iter_start
      (tightChainExtFwd sys l_τ h_l_τ_external e_iter_start h_iter_term
        chain_pre s_chain_last)
    = ∑' μ : PMF State,
        pe'.scheduler.next e_w_pre (some (l_τ, μ)) *
        tightStepFactor_perMu_inner sys pe' e_w_pre h_ewp l_τ h_l_τ_external
          chain_pre s_chain_last μ := by
  classical
  set e := tightChainExtFwd sys l_τ h_l_τ_external e_iter_start h_iter_term
    chain_pre s_chain_last with h_e_def
  have h_e_term : e.trans.Terminates :=
    tightChainExtFwd_trans_terminates sys l_τ h_l_τ_external e_iter_start
      h_iter_term chain_pre s_chain_last
  -- Unfold `tightStepFactor` and discharge guards.
  unfold tightStepFactor
  rw [dif_pos h_ewp, dif_pos h_iter_term, dif_pos h_e_term]
  -- `e.init = e_iter_start.init` by definition of the forward map.
  have h_init_eq : e.init = e_iter_start.init := rfl
  -- Use the toList factorisation.
  have h_toList :=
    tightChainExtFwd_trans_toList sys l_τ h_l_τ_external e_iter_start
      h_iter_term chain_pre s_chain_last
  simp only at h_toList
  -- `e_list = iter_list ++ chain_pre ++ [(l_τ, s_chain_last)]`.
  set iter_list : List (Label × State) := e_iter_start.trans.toList h_iter_term
    with h_iter_list_def
  -- The prefix check: `e_list.take iter_list.length = iter_list`.
  have h_prefix : e_iter_start.init = e.init ∧
      (e.trans.toList h_e_term).take iter_list.length = iter_list := by
    refine ⟨h_init_eq.symm, ?_⟩
    rw [h_toList]
    rw [List.append_assoc, List.take_left]
  rw [dif_pos h_prefix]
  -- The chain after the prefix: `chain_pre ++ [(l_τ, s_chain_last)]`.
  have h_chain_eq :
      (e.trans.toList h_e_term).drop iter_list.length
        = chain_pre ++ [(l_τ, s_chain_last)] := by
    rw [h_toList]
    rw [List.append_assoc, List.drop_left]
  -- Per-μ analysis.
  apply tsum_congr
  intro μ
  congr 1
  by_cases h_supp : some (l_τ, μ) ∈ (pe'.scheduler.next e_w_pre).support
  swap
  · -- Outside support: both sides reduce to `0`.
    simp only [dif_neg h_supp]
    unfold tightStepFactor_perMu_inner
    simp only [dif_neg h_supp]
  rw [dif_pos h_supp]
  -- Internal-case for `l_τ` is excluded.
  rw [dif_neg h_l_τ_external]
  -- The chain match: last entry is `(l_τ, s_chain_last)`, all earlier entries
  -- are internal (by `h_chain_int`), so both inner ifs fire to `pos`.
  rw [h_chain_eq]
  -- chain.getLast? = some (l_τ, s_chain_last).
  have h_last_some : (chain_pre ++ [(l_τ, s_chain_last)]).getLast? =
      some (l_τ, s_chain_last) := by
    simp
  rw [h_last_some]
  -- The match-block on `some (l_τ, s_chain_last)`: inner `if last.1 = l_τ` fires.
  -- dropLast = chain_pre.
  have h_dropLast :
      (chain_pre ++ [(l_τ, s_chain_last)]).dropLast = chain_pre := by
    simp
  simp only [h_dropLast, if_true]
  rw [if_pos h_chain_int]
  -- Now unfold tightStepFactor_perMu_inner.
  unfold tightStepFactor_perMu_inner
  rw [dif_pos h_supp]

/-- **Sum-rearrangement via the forward map.**

Asserts the LHS sum over the tight-cylinder subtype equals the sum over
`(chain_pre, s_chain_last)` pairs via `tightChainExtFwd`. The forward map's
image covers the structural locus where `tightStepFactor` is non-zero;
outside this image, `tightStepFactor` is zero. -/
private lemma tightStepFactor_sum_via_fwd
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (τ_prev : Seq Label) (l_τ : Label)
    (h_l_τ_external : ¬ sys.internal l_τ)
    (e_w_pre e_iter_start : AlterSeq State Label)
    (h_iter_term : e_iter_start.trans.Terminates)
    (h_trace_match : sys.trace e_iter_start = τ_prev) :
    (∑' e : {e : AlterSeq State Label //
              e.trans.Terminates ∧
              sys.trace e = τ_prev.append (Seq.cons l_τ Seq.nil) ∧
              sys.IsTight e},
      tightStepFactor sys pe' e_w_pre l_τ e_iter_start e.1)
      = ∑' p : List (Label × State) × State,
          tightStepFactor sys pe' e_w_pre l_τ e_iter_start
            (tightChainExtFwd sys l_τ h_l_τ_external e_iter_start h_iter_term
              p.1 p.2) := by
  classical
  -- **Bijection step.** We apply `tsum_eq_tsum_of_ne_zero_bij` with the
  -- backward map sending each `e` in the support of LHS-sum to the pair
  -- `(chain_pre, s_chain_last)` extracted from the structural guards of
  -- `tightStepFactor`.
  --
  -- Concretely: if `tightStepFactor sys pe' e_w_pre l_τ e_iter_start e ≠ 0`,
  -- then all the `dif`/`if`/`match` guards inside `tightStepFactor` fire to
  -- the positive branch, forcing
  --   (a) `e.trans.Terminates`, `e_iter_start.init = e.init`,
  --   (b) `(e.trans.toList).take iter_list.length = iter_list`,
  --   (c) `chain := (e.trans.toList).drop iter_list.length`
  --       satisfies `chain.getLast? = some (l_τ, s_chain_last)` for some
  --       `s_chain_last`,
  --   (d) `chain.dropLast` is all-internal.
  -- Setting `chain_pre := chain.dropLast` and using (a)-(d), we recover
  --   `e = tightChainExtFwd sys l_τ h_l_τ_external e_iter_start h_iter_term
  --          chain_pre s_chain_last`,
  -- exactly the FWD-image structure. Injectivity follows from
  -- `tightChainExtFwd_injective`; the eval-step
  -- `f (i e) = g e` follows from this AlterSeq-equality.
  --
  -- Range-coverage: for `p = (chain_pre, s_chain_last)` with
  -- `f p ≠ 0`, by `tightStepFactor_eval_at_fwd_eq_zero_of_not_internal`'s
  -- contrapositive, `chain_pre` is all-internal, and then
  -- `tightChainExtFwd_trans_terminates`, `tightChainExtFwd_trace` (combined
  -- with `h_trace_match`), and `tightChainExtFwd_isTight` give the cylinder
  -- subtype membership of `FWD p`. The pair `(chain_pre, s_chain_last)`
  -- equals `i (FWD p)` by direct computation via `tightChainExtFwd_trans_toList`.
  --
  -- Apply `tsum_eq_tsum_of_ne_zero_bij` with the forward map (lifted into
  -- the subtype) as `i`.
  set FWD := fun (p : List (Label × State) × State) =>
    tightChainExtFwd sys l_τ h_l_τ_external e_iter_start h_iter_term p.1 p.2
    with hFWD_def
  set f : {e : AlterSeq State Label //
            e.trans.Terminates ∧
            sys.trace e = τ_prev.append (Seq.cons l_τ Seq.nil) ∧
            sys.IsTight e} → ENNReal :=
    fun e => tightStepFactor sys pe' e_w_pre l_τ e_iter_start e.1
    with hf_def
  set g : List (Label × State) × State → ENNReal :=
    fun p => tightStepFactor sys pe' e_w_pre l_τ e_iter_start (FWD p)
    with hg_def
  -- The lifted forward map: takes `p` in `support g` to the subtype.
  -- Membership in the subtype requires `chain_pre` all-internal, which
  -- we extract from `g p ≠ 0` via the contrapositive.
  have h_ewp_of_supp : ∀ p : List (Label × State) × State,
      g p ≠ 0 → e_w_pre.trans.Terminates := by
    intro p hp
    by_contra h_neg
    apply hp
    simp only [hg_def, FWD]
    exact tightStepFactor_eq_zero_of_e_w_pre_not_terminates sys pe' e_w_pre l_τ
      e_iter_start (FWD p) h_neg
  have h_chain_int_of_supp : ∀ p : List (Label × State) × State,
      g p ≠ 0 → ∀ pair ∈ p.1, sys.internal pair.1 := by
    intro p hp
    by_contra h_not
    apply hp
    exact tightStepFactor_eval_at_fwd_eq_zero_of_not_internal sys pe' e_w_pre
      (h_ewp_of_supp p hp) l_τ h_l_τ_external
      e_iter_start h_iter_term p.1 h_not p.2
  -- The map `i`.
  let i : Function.support g → {e : AlterSeq State Label //
            e.trans.Terminates ∧
            sys.trace e = τ_prev.append (Seq.cons l_τ Seq.nil) ∧
            sys.IsTight e} :=
    fun x => ⟨FWD x.1,
      tightChainExtFwd_trans_terminates sys l_τ h_l_τ_external e_iter_start
        h_iter_term x.1.1 x.1.2,
      by
        have h_int := h_chain_int_of_supp x.1 x.2
        rw [tightChainExtFwd_trace sys l_τ h_l_τ_external e_iter_start
          h_iter_term x.1.1 h_int x.1.2, h_trace_match],
      tightChainExtFwd_isTight sys l_τ h_l_τ_external e_iter_start
        h_iter_term x.1.1 x.1.2⟩
  -- Injectivity of `i` follows from `tightChainExtFwd_injective`.
  have hi : Function.Injective i := by
    rintro ⟨p1, hp1⟩ ⟨p2, hp2⟩ h_eq
    have h_FWD_eq : FWD p1 = FWD p2 := by
      have := congrArg Subtype.val h_eq
      exact this
    have h_p_eq : p1 = p2 :=
      tightChainExtFwd_injective sys l_τ h_l_τ_external e_iter_start
        h_iter_term h_FWD_eq
    exact Subtype.ext h_p_eq
  -- Range coverage: for every `e` in `support f`, exhibit `p` with `i ⟨p, _⟩ = e`.
  have hf_sub : Function.support f ⊆ Set.range i := by
    rintro ⟨e, h_e_term, h_e_trace, h_e_tight⟩ h_fe_ne
    simp only [Function.mem_support, hf_def] at h_fe_ne
    -- Extract structural data from `tightStepFactor ≠ 0`.
    -- Step 1: From `tightStepFactor ... e ≠ 0`, the outer `dif`s fire.
    have h_ewp : e_w_pre.trans.Terminates := by
      by_contra h_neg
      apply h_fe_ne
      unfold tightStepFactor; rw [dif_neg h_neg]
    -- Step 2: All inner guards fire. Unfold to extract.
    -- Get the chain structure from `tightStepFactor`'s definition.
    have h_unfold : tightStepFactor sys pe' e_w_pre l_τ e_iter_start e =
        (if h_prefix : e_iter_start.init = e.init ∧
            (e.trans.toList h_e_term).take
              (e_iter_start.trans.toList h_iter_term).length
              = e_iter_start.trans.toList h_iter_term then
          let s_pre : State := e_w_pre.endState h_ewp
          let chain : List (Label × State) :=
            (e.trans.toList h_e_term).drop
              (e_iter_start.trans.toList h_iter_term).length
          ∑' μ : PMF State,
            pe'.scheduler.next e_w_pre (some (l_τ, μ)) *
            (if h_supp : some (l_τ, μ) ∈ (pe'.scheduler.next e_w_pre).support then
              have h_sw : sys^w.step s_pre l_τ μ :=
                pe'.scheduler.valid e_w_pre (Nat.find h_ewp) s_pre
                  (Nat.find_spec h_ewp)
                  (AlterSeq.stateAt_find_eq_endState e_w_pre h_ewp)
                  l_τ μ h_supp
              if h_int : sys.internal l_τ then 0
              else
                have h_ws : weakStep sys (PMF.pure s_pre) l_τ μ := by
                  rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
                  · exact absurd h_int' h_int
                  · exact h
                let σ_pre := h_ws.weakTau_pre.witness
                let σ_post := h_ws.weakTau_post.witness
                let p := h_ws.hyperStep_mid.kernel
                match chain.getLast? with
                | none => (0 : ENNReal)
                | some last_pair =>
                  haveI : Decidable (last_pair.1 = l_τ) := Classical.dec _
                  if last_pair.1 = l_τ then
                    let chain_pre := chain.dropLast
                    haveI : Decidable (∀ pair ∈ chain_pre, sys.internal pair.1) :=
                      Classical.dec _
                    if (∀ pair ∈ chain_pre, sys.internal pair.1) then
                      let s_chain_last : State := last_pair.2
                      let s_mid_pre : State :=
                        (chain_pre.getLast?.map Prod.snd).getD s_pre
                      let _ := σ_post
                      chainProb σ_pre ⟨s_pre, Seq.nil⟩ chain_pre *
                        (∑' μ_l : PMF State, p s_mid_pre μ_l * μ_l s_chain_last)
                    else 0
                  else 0
            else 0)
        else 0) := by
      unfold tightStepFactor
      rw [dif_pos h_ewp, dif_pos h_iter_term, dif_pos h_e_term]
    have h_fe_ne_orig : tightStepFactor sys pe' e_w_pre l_τ e_iter_start e ≠ 0 :=
      h_fe_ne
    rw [h_unfold] at h_fe_ne
    have h_prefix : e_iter_start.init = e.init ∧
        (e.trans.toList h_e_term).take
          (e_iter_start.trans.toList h_iter_term).length
          = e_iter_start.trans.toList h_iter_term := by
      by_contra h_neg
      apply h_fe_ne
      rw [dif_neg h_neg]
    rw [dif_pos h_prefix] at h_fe_ne
    -- Set up locals.
    set iter_list : List (Label × State) := e_iter_start.trans.toList h_iter_term
      with h_iter_list_def
    set chain : List (Label × State) := (e.trans.toList h_e_term).drop iter_list.length
      with h_chain_def
    -- From `h_fe_ne ≠ 0`, the `∑' μ` is non-zero, so some μ in support contributes
    -- non-trivially. Extract `chain.getLast? = some (l_τ, s)` and chain.dropLast
    -- all-internal.
    have h_exists_μ : ∃ μ : PMF State,
        some (l_τ, μ) ∈ (pe'.scheduler.next e_w_pre).support ∧
        ∃ last_pair : Label × State, chain.getLast? = some last_pair ∧
          last_pair.1 = l_τ ∧
          (∀ pair ∈ chain.dropLast, sys.internal pair.1) := by
      by_contra h_no
      push Not at h_no
      apply h_fe_ne
      refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
      by_cases h_supp : some (l_τ, μ) ∈ (pe'.scheduler.next e_w_pre).support
      swap
      · simp [h_supp]
      rw [dif_pos h_supp]
      by_cases h_int_l : sys.internal l_τ
      · simp [h_int_l]
      rw [dif_neg h_int_l]
      -- match on chain.getLast?
      cases h_last : chain.getLast? with
      | none => simp
      | some last_pair =>
        simp only []
        by_cases h_l_eq : last_pair.1 = l_τ
        swap
        · simp [h_l_eq]
        rw [if_pos h_l_eq]
        by_cases h_all_int : ∀ pair ∈ chain.dropLast, sys.internal pair.1
        · -- Contradicts h_no.
          exfalso
          obtain ⟨pair, h_mem, h_not_int⟩ := h_no μ h_supp last_pair h_last h_l_eq
          exact h_not_int (h_all_int pair h_mem)
        · rw [if_neg h_all_int]; ring
    obtain ⟨_μ_witness, _h_supp, last_pair, h_last, h_l_eq, h_all_int⟩ := h_exists_μ
    -- The chain is non-empty, with last `(l_τ, s_chain_last)`.
    have h_chain_ne : chain ≠ [] := by
      intro h_empty
      rw [h_empty, List.getLast?_nil] at h_last
      exact absurd h_last (by intro h; cases h)
    set s_chain_last : State := last_pair.2 with h_scl_def
    set chain_pre : List (Label × State) := chain.dropLast with h_cp_def
    -- `chain = chain_pre ++ [(l_τ, s_chain_last)]`.
    have h_chain_split : chain = chain_pre ++ [(l_τ, s_chain_last)] := by
      have hL : chain.getLast h_chain_ne = last_pair := by
        rw [← Option.some_inj, ← List.getLast?_eq_some_getLast]
        exact h_last
      have h_lp_form : last_pair = (l_τ, s_chain_last) := by
        ext
        · exact h_l_eq
        · rfl
      conv_lhs => rw [← List.dropLast_append_getLast h_chain_ne, hL, h_lp_form]
    -- Show `e = FWD (chain_pre, s_chain_last)`.
    have h_e_eq : e = FWD (chain_pre, s_chain_last) := by
      -- AlterSeq is determined by `init` and `trans`.
      have h_init_eq : e.init = e_iter_start.init := h_prefix.1.symm
      -- Reconstruct `e.trans`.
      have h_e_list_split :
          e.trans.toList h_e_term = iter_list ++ chain_pre ++ [(l_τ, s_chain_last)] := by
        have h_take_drop :
            iter_list ++ chain = e.trans.toList h_e_term := by
          conv_rhs => rw [← List.take_append_drop iter_list.length (e.trans.toList h_e_term)]
          rw [h_prefix.2]
        rw [← h_take_drop, h_chain_split, ← List.append_assoc]
      -- Now reconstruct `e.trans` as a Seq.
      have h_e_trans_eq :
          e.trans = e_iter_start.trans.append
            ((Seq.ofList chain_pre).append (Seq.cons (l_τ, s_chain_last) Seq.nil)) := by
        have h_e_to_ofL : e.trans = Seq.ofList (e.trans.toList h_e_term) :=
          (Seq.ofList_toList _ _).symm
        have h_iter_to_ofL : e_iter_start.trans = Seq.ofList iter_list := by
          rw [h_iter_list_def]; exact (Seq.ofList_toList _ _).symm
        rw [h_e_to_ofL, h_e_list_split]
        rw [Seq.ofList_append, Seq.ofList_append, Seq.ofList_cons, Seq.ofList_nil]
        rw [← h_iter_to_ofL, Seq.append_assoc]
      -- Combine into AlterSeq equality (structure with two fields).
      have h_struct : e = ⟨e_iter_start.init, e_iter_start.trans.append
          ((Seq.ofList chain_pre).append (Seq.cons (l_τ, s_chain_last) Seq.nil))⟩ := by
        obtain ⟨ei, et⟩ := e
        dsimp at h_init_eq h_e_trans_eq
        exact congrArg₂ AlterSeq.mk h_init_eq h_e_trans_eq
      rw [h_struct]
      rfl
    -- Now `(chain_pre, s_chain_last) ∈ support g` because `g (chain_pre, s_chain_last)
    -- = tightStepFactor ... (FWD ...) = tightStepFactor ... e ≠ 0`.
    have h_g_ne : g (chain_pre, s_chain_last) ≠ 0 := by
      change tightStepFactor sys pe' e_w_pre l_τ e_iter_start
        (FWD (chain_pre, s_chain_last)) ≠ 0
      rw [← h_e_eq]
      exact h_fe_ne_orig
    -- Build the range membership.
    refine ⟨⟨(chain_pre, s_chain_last), h_g_ne⟩, ?_⟩
    -- `i ⟨(chain_pre, s_chain_last), _⟩ = ⟨e, _⟩`.
    apply Subtype.ext
    simp only [i]
    exact h_e_eq.symm
  -- Evaluation equality.
  have h_fi : ∀ x : Function.support g, f (i x) = g x.1 := by
    intro x
    simp only [hf_def, hg_def, i, FWD]
  -- Apply the bijection lemma.
  exact tsum_eq_tsum_of_ne_zero_bij i hi hf_sub h_fi

private lemma tightStepFactor_sum_eq_witness_emission_of_trace_match
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (τ_prev : Seq Label) (l_τ : Label)
    (_h_τ_prev_term : τ_prev.Terminates)
    (h_l_τ_external : ¬ sys.internal l_τ)
    (e_w_pre e_iter_start : AlterSeq State Label)
    (h_e_w_pre_term : e_w_pre.trans.Terminates)
    (h_iter_term : e_iter_start.trans.Terminates)
    (h_trace_match : sys.trace e_iter_start = τ_prev) :
    (∑' e : {e : AlterSeq State Label //
              e.trans.Terminates ∧
              sys.trace e = τ_prev.append (Seq.cons l_τ Seq.nil) ∧
              sys.IsTight e},
      tightStepFactor sys pe' e_w_pre l_τ e_iter_start e.1) =
      ∑' μ : PMF State, pe'.scheduler.next e_w_pre (some (l_τ, μ)) := by
  classical
  -- Step 1: rewrite the LHS via the forward map (bijection step).
  rw [tightStepFactor_sum_via_fwd sys pe' τ_prev l_τ h_l_τ_external e_w_pre
    e_iter_start h_iter_term h_trace_match]
  -- Step 2: rewrite each `(chain_pre, s_chain_last)` summand via the
  -- unified eval — note that for non-all-internal chain_pre the value is
  -- zero by `chainProb`'s vanishing (via `WeakScheduler.internal_only`),
  -- AND it matches the eval_at_fwd RHS, so a single rewrite works.
  have h_summand : ∀ p : List (Label × State) × State,
      tightStepFactor sys pe' e_w_pre l_τ e_iter_start
        (tightChainExtFwd sys l_τ h_l_τ_external e_iter_start h_iter_term
          p.1 p.2)
      = ∑' μ : PMF State,
          pe'.scheduler.next e_w_pre (some (l_τ, μ)) *
            tightStepFactor_perMu_inner sys pe' e_w_pre h_e_w_pre_term l_τ
              h_l_τ_external p.1 p.2 μ := by
    intro p
    by_cases h_int : ∀ pair ∈ p.1, sys.internal pair.1
    · exact tightStepFactor_eval_at_fwd sys pe' e_w_pre h_e_w_pre_term l_τ
        h_l_τ_external e_iter_start h_iter_term p.1 h_int p.2
    · -- Non-all-internal: LHS = 0 by eval_zero, and RHS = 0 because every
      -- summand factors through `chainProb perMu_inner ... = 0` (via
      -- `chainProb_eq_zero_of_not_all_internal`).
      rw [tightStepFactor_eval_at_fwd_eq_zero_of_not_internal sys pe' e_w_pre
        h_e_w_pre_term l_τ h_l_τ_external e_iter_start h_iter_term p.1 h_int p.2]
      -- RHS = 0.
      symm
      refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
      -- perMu_inner is zero for non-all-internal chain_pre.
      have h_perMu_zero :
          tightStepFactor_perMu_inner sys pe' e_w_pre h_e_w_pre_term l_τ
            h_l_τ_external p.1 p.2 μ = 0 := by
        unfold tightStepFactor_perMu_inner
        by_cases h_supp : some (l_τ, μ) ∈ (pe'.scheduler.next e_w_pre).support
        swap
        · simp [h_supp]
        rw [dif_pos h_supp]
        -- chainProb factor is 0 by `chainProb_eq_zero_of_not_all_internal`.
        simp only [chainProb_eq_zero_of_not_all_internal _ _ p.1 h_int,
                   zero_mul]
      rw [h_perMu_zero, mul_zero]
  rw [tsum_congr h_summand]
  -- Step 3: convert pair-sum to nested sums.
  rw [ENNReal.tsum_prod (f := fun chain_pre s_chain_last =>
    ∑' μ : PMF State,
      pe'.scheduler.next e_w_pre (some (l_τ, μ)) *
        tightStepFactor_perMu_inner sys pe' e_w_pre h_e_w_pre_term l_τ
          h_l_τ_external chain_pre s_chain_last μ)]
  -- Step 4: swap inner `∑' s_chain_last, ∑' μ ↦ ∑' μ, c_μ * ∑' s, perMu_inner`.
  have h_inner_swap : ∀ chain_pre : List (Label × State),
      (∑' s_chain_last : State, ∑' μ : PMF State,
        pe'.scheduler.next e_w_pre (some (l_τ, μ)) *
          tightStepFactor_perMu_inner sys pe' e_w_pre h_e_w_pre_term l_τ
            h_l_τ_external chain_pre s_chain_last μ)
      = ∑' μ : PMF State, pe'.scheduler.next e_w_pre (some (l_τ, μ)) *
          ∑' s_chain_last : State,
            tightStepFactor_perMu_inner sys pe' e_w_pre h_e_w_pre_term l_τ
              h_l_τ_external chain_pre s_chain_last μ := by
    intro chain_pre
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro μ
    rw [ENNReal.tsum_mul_left]
  rw [tsum_congr h_inner_swap]
  -- Now: ∑' chain_pre, ∑' μ, c_μ · ∑' s, perMu_inner. Swap outer two.
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro μ
  -- Factor c_μ out of the chain_pre sum.
  rw [ENNReal.tsum_mul_left]
  -- For each μ, split on whether μ ∈ support.
  by_cases h_supp : some (l_τ, μ) ∈ (pe'.scheduler.next e_w_pre).support
  swap
  · have h_zero : pe'.scheduler.next e_w_pre (some (l_τ, μ)) = 0 := by
      simpa [PMF.mem_support_iff] using h_supp
    rw [h_zero, zero_mul]
  -- In-support: use perMu_inner_total_mass.
  rw [tightStepFactor_perMu_inner_total_mass sys pe' e_w_pre h_e_w_pre_term l_τ
    h_l_τ_external μ h_supp, mul_one]

private lemma witness_emission_marginal
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (τ_prev : Seq Label) (l_τ : Label) (_h_τ_prev_term : τ_prev.Terminates)
    (_h_l_τ_external : ¬ sys.internal l_τ)
    (e_w_pre e_iter_start : AlterSeq State Label)
    (h_e_w_pre_term : e_w_pre.trans.Terminates) :
    (∑' e : {e : AlterSeq State Label //
              e.trans.Terminates ∧
              sys.trace e = τ_prev.append (Seq.cons l_τ Seq.nil) ∧
              sys.IsTight e},
      tightStepFactor sys pe' e_w_pre l_τ e_iter_start e.1) =
      (open Classical in
       if sys.trace e_iter_start = τ_prev ∧ e_iter_start.trans.Terminates then
        ∑' μ : PMF State, pe'.scheduler.next e_w_pre (some (l_τ, μ))
      else 0) := by
  classical
  by_cases h_iter_term : e_iter_start.trans.Terminates
  · -- `e_iter_start.trans` terminates: dispatch on the trace match.
    by_cases h_trace_match : sys.trace e_iter_start = τ_prev
    · -- Trace match: apply the witness-emission identity sub-lemma.
      rw [if_pos ⟨h_trace_match, h_iter_term⟩]
      exact tightStepFactor_sum_eq_witness_emission_of_trace_match sys pe' τ_prev l_τ
        _h_τ_prev_term _h_l_τ_external e_w_pre e_iter_start h_e_w_pre_term h_iter_term
        h_trace_match
    · -- Trace mismatch: every `tightStepFactor` summand is zero, so the sum is zero.
      rw [if_neg (by intro h; exact h_trace_match h.1)]
      convert tsum_zero with e
      exact tightStepFactor_eq_zero_of_trace_mismatch sys pe' τ_prev l_τ e_w_pre
        e_iter_start e.1 e.2.1 e.2.2.1 e.2.2.2 h_trace_match
  · -- `e_iter_start.trans` does not terminate: every `tightStepFactor` summand is zero.
    rw [if_neg (by intro h; exact h_iter_term h.2)]
    convert tsum_zero with e
    exact tightStepFactor_eq_zero_of_iter_start_not_terminates sys pe' e_w_pre l_τ
      e_iter_start e.1 h_iter_term

-- **Trace factorisation through an all-internal chain (no external suffix).**
-- When `chain_pre` is all-internal, appending it to `trans_prev` leaves the
-- trace unchanged.
private lemma trace_append_all_internal
    (sys : LabelledSystem State Label) (s_init : State)
    (trans_prev : Seq (Label × State)) (h_prev_term : trans_prev.Terminates)
    (chain_pre : List (Label × State))
    (h_chain_int : ∀ pair ∈ chain_pre, sys.internal pair.1) :
    sys.trace ⟨s_init, trans_prev.append (Seq.ofList chain_pre)⟩
      = sys.trace ⟨s_init, trans_prev⟩ := by
  classical
  unfold LabelledSystem.trace
  change ((trans_prev.append (Seq.ofList chain_pre)).filter
            (fun p => ¬ sys.internal p.1)).map Prod.fst
      = (trans_prev.filter (fun p => ¬ sys.internal p.1)).map Prod.fst
  rw [Seq.filter_append _ _ _ h_prev_term,
      seq_filter_internal_list_eq_nil sys chain_pre h_chain_int,
      Stream'.Seq.append_nil]

-- **`splitAtLabel` reconstruction.** When `splitAtLabel l chain` returns
-- `(chain_pre, some (s_mid, chain_post))`, the chain reconstructs as
-- `chain_pre ++ (l, s_mid) :: chain_post` and `chain_pre` contains no entry
-- with label `l`.
private lemma splitAtLabel_some_reconstruct (l : Label)
    (chain : List (Label × State)) (chain_pre : List (Label × State))
    (s_mid : State) (chain_post : List (Label × State))
    (h_split : splitAtLabel l chain = (chain_pre, some (s_mid, chain_post))) :
    chain = chain_pre ++ (l, s_mid) :: chain_post ∧
      ∀ pair ∈ chain_pre, pair.1 ≠ l := by
  classical
  induction chain generalizing chain_pre with
  | nil => simp [splitAtLabel] at h_split
  | cons hd tl ih =>
    unfold splitAtLabel at h_split
    by_cases h_l : hd.1 = l
    · rw [if_pos h_l] at h_split
      simp only [Prod.mk.injEq, List.nil_eq, Option.some.injEq] at h_split
      obtain ⟨h_cp, h_sm, h_cs⟩ := h_split
      subst h_cp; subst h_sm; subst h_cs
      refine ⟨?_, ?_⟩
      · rw [List.nil_append]
        have hd_eq : hd = (l, hd.2) := Prod.ext h_l rfl
        rw [hd_eq]
      · intro pair h_mem; cases h_mem
    · rw [if_neg h_l] at h_split
      simp only [Prod.mk.injEq] at h_split
      obtain ⟨h_cp_eq, h_rest⟩ := h_split
      cases h_cp_eq' : (splitAtLabel l tl) with
      | mk cp' opt' =>
        rw [h_cp_eq'] at h_cp_eq h_rest
        simp only at h_cp_eq
        subst h_cp_eq
        subst h_rest
        have ih' := ih cp' h_cp_eq'
        obtain ⟨h_eq, h_no_l⟩ := ih'
        refine ⟨?_, ?_⟩
        · simp only [List.cons_append, List.cons.injEq, true_and]; exact h_eq
        · intro pair h_mem
          cases h_mem with
          | head => exact h_l
          | tail _ h_mem' => exact h_no_l _ h_mem'

-- **One-iteration trace-extension identity.** When `oneIterTransitionProb` is
-- nonzero at `(e_w_prev, l_last, e_prev, e_iter_start)`, the structural data
-- forces a specific trace relationship: `sys.trace e_iter_start` extends
-- `sys.trace e_prev` by `[l_last]` if `l_last` is external, and matches it
-- exactly if `l_last` is internal.
private lemma oneIterTransitionProb_trace_extension
    {sys : LabelledSystem State Label}
    {pe' : ProbabilisticExecution sys^w.toSystem}
    (e_w_prev : AlterSeq State Label) (l_last : Label)
    (e_prev e_iter_start : AlterSeq State Label)
    (h_nonzero :
      oneIterTransitionProb sys pe' e_w_prev l_last e_prev e_iter_start ≠ 0) :
    e_prev.trans.Terminates ∧ e_iter_start.trans.Terminates ∧
      sys.trace e_iter_start = (sys.trace e_prev).append
        (open Classical in
          if sys.internal l_last then (Seq.nil : Seq Label)
          else Seq.cons l_last Seq.nil) := by
  classical
  -- Unfold oneIterTransitionProb. Each `dif_*` guard, if false, would make
  -- the whole expression 0, contradicting h_nonzero.
  unfold oneIterTransitionProb at h_nonzero
  by_cases h_ewp : e_w_prev.trans.Terminates
  swap
  · rw [dif_neg h_ewp] at h_nonzero; exact absurd rfl h_nonzero
  rw [dif_pos h_ewp] at h_nonzero
  by_cases h_ep : e_prev.trans.Terminates
  swap
  · rw [dif_neg h_ep] at h_nonzero; exact absurd rfl h_nonzero
  rw [dif_pos h_ep] at h_nonzero
  by_cases h_es : e_iter_start.trans.Terminates
  swap
  · rw [dif_neg h_es] at h_nonzero; exact absurd rfl h_nonzero
  rw [dif_pos h_es] at h_nonzero
  refine ⟨h_ep, h_es, ?_⟩
  -- Set up locals (mirroring the def).
  set s_pre : State := e_w_prev.endState h_ewp with hs_pre
  set e_prev_list : List (Label × State) := e_prev.trans.toList h_ep with h_epl
  set e_list : List (Label × State) := e_iter_start.trans.toList h_es with h_eil
  -- The prefix condition must hold.
  by_cases h_prefix :
      e_prev.init = e_iter_start.init ∧ e_list.take e_prev_list.length = e_prev_list
  swap
  · rw [dif_neg h_prefix] at h_nonzero; exact absurd rfl h_nonzero
  rw [dif_pos h_prefix] at h_nonzero
  set chain : List (Label × State) := e_list.drop e_prev_list.length with h_chain
  -- e_iter_start.trans factors as e_prev.trans.append (Seq.ofList chain).
  have h_take_drop : e_prev_list ++ chain = e_list := by
    conv_rhs => rw [← List.take_append_drop e_prev_list.length e_list]
    rw [h_prefix.2]
  have h_e_to_ofL : e_iter_start.trans = Seq.ofList e_list := by
    rw [h_eil]; exact (Seq.ofList_toList _ _).symm
  have h_ep_to_ofL : e_prev.trans = Seq.ofList e_prev_list := by
    rw [h_epl]; exact (Seq.ofList_toList _ _).symm
  have h_iter_trans_split :
      e_iter_start.trans = e_prev.trans.append (Seq.ofList chain) := by
    rw [h_e_to_ofL, ← h_take_drop, Seq.ofList_append, ← h_ep_to_ofL]
  have h_ei_form : e_iter_start = ⟨e_prev.init, e_iter_start.trans⟩ := by
    rcases e_iter_start with ⟨a, b⟩
    obtain ⟨h_init, _⟩ := h_prefix
    dsimp at h_init
    subst h_init; rfl
  -- Extract a μ from the tsum.
  rw [Ne, ENNReal.tsum_eq_zero] at h_nonzero
  push Not at h_nonzero
  obtain ⟨μ, h_mu_ne⟩ := h_nonzero
  rw [mul_ne_zero_iff] at h_mu_ne
  obtain ⟨_h_sched_ne, h_inner_ne⟩ := h_mu_ne
  -- The support guard must hold.
  by_cases h_supp : some (l_last, μ) ∈ (pe'.scheduler.next e_w_prev).support
  swap
  · rw [dif_neg h_supp] at h_inner_ne; exact absurd rfl h_inner_ne
  rw [dif_pos h_supp] at h_inner_ne
  -- Establish sys^w.step s_pre l_last μ (needed in both branches).
  have h_sw : sys^w.step s_pre l_last μ :=
    pe'.scheduler.valid e_w_prev (Nat.find h_ewp) s_pre
      (Nat.find_spec h_ewp)
      (AlterSeq.stateAt_find_eq_endState e_w_prev h_ewp)
      l_last μ h_supp
  -- Now case-split on internal/external.
  by_cases h_int : sys.internal l_last
  · -- Internal case: inner reduces to chainProb σ ⟨s_pre, nil⟩ chain.
    rw [if_pos h_int]
    rw [dif_pos h_int] at h_inner_ne
    -- chainProb σ chain ≠ 0 ⟹ chain is all-internal.
    have h_all_int : ∀ pair ∈ chain, sys.internal pair.1 := by
      by_contra h_not
      apply h_inner_ne
      exact chainProb_eq_zero_of_not_all_internal _ ⟨s_pre, Seq.nil⟩ chain h_not
    -- Apply the trace-append all-internal lemma.
    rw [Seq.append_nil]
    have h_eprev_form :
        sys.trace ⟨e_prev.init, e_prev.trans⟩ = sys.trace e_prev := by
      rcases e_prev with ⟨a, b⟩; rfl
    conv_lhs => rw [h_ei_form, h_iter_trans_split]
    rw [trace_append_all_internal sys e_prev.init e_prev.trans h_ep chain h_all_int,
        h_eprev_form]
  · -- External case: split chain via splitAtLabel.
    rw [if_neg h_int]
    rw [dif_neg h_int] at h_inner_ne
    -- Extract h_ws : weakStep ... from h_sw.
    have h_ws : weakStep sys (PMF.pure s_pre) l_last μ := by
      rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
      · exact absurd h_int' h_int
      · exact h
    -- Case-analysis on splitAtLabel l_last chain.
    rcases h_spl_eq : splitAtLabel l_last chain
      with ⟨chain_pre, _ | ⟨s_mid, chain_post⟩⟩
    · -- split.2 = none: the match returns 0, contradiction.
      exfalso; apply h_inner_ne
      -- Rewrite the definition explicitly.
      have h_eq : (splitAtLabel l_last chain).2 = none := by rw [h_spl_eq]
      simp only [h_eq]
    · -- split.2 = some (s_mid, chain_post).
      have h_cp_def : (splitAtLabel l_last chain).1 = chain_pre := by rw [h_spl_eq]
      have h_cs_def : (splitAtLabel l_last chain).2 = some (s_mid, chain_post) := by
        rw [h_spl_eq]
      -- The `h_inner_ne` has the form `(...match (splitAtLabel l_last chain).2 ...) ≠ 0`.
      -- Rewrite using h_spl_eq to expose the some-branch.
      have h_inner_ne' :
          (chainProb h_ws.weakTau_pre.witness ⟨s_pre, Seq.nil⟩ chain_pre *
              (∑' μ_l : PMF State,
                h_ws.hyperStep_mid.kernel
                  ((chain_pre.getLast?.map Prod.snd).getD s_pre) μ_l * μ_l s_mid)) *
            chainProb h_ws.weakTau_post.witness ⟨s_mid, Seq.nil⟩ chain_post ≠ 0 := by
        convert h_inner_ne using 1
        rw [show splitAtLabel l_last chain = (chain_pre, some (s_mid, chain_post))
              from h_spl_eq]
      rw [mul_ne_zero_iff, mul_ne_zero_iff] at h_inner_ne'
      obtain ⟨⟨h_cp_ne, _h_mid⟩, h_cs_ne⟩ := h_inner_ne'
      -- splitAtLabel reconstruction.
      obtain ⟨h_chain_eq, _h_no_l⟩ :=
        splitAtLabel_some_reconstruct l_last chain chain_pre s_mid chain_post h_spl_eq
      -- chain_pre is all-internal.
      have h_cp_int : ∀ pair ∈ chain_pre, sys.internal pair.1 := by
        by_contra h_not
        exact h_cp_ne
          (chainProb_eq_zero_of_not_all_internal _ ⟨s_pre, Seq.nil⟩ chain_pre h_not)
      -- chain_post is all-internal.
      have h_cs_int : ∀ pair ∈ chain_post, sys.internal pair.1 := by
        by_contra h_not
        exact h_cs_ne
          (chainProb_eq_zero_of_not_all_internal _ ⟨s_mid, Seq.nil⟩ chain_post h_not)
      -- Reconstruct the trans.
      have h_iter_trans_split2 :
          e_iter_start.trans = e_prev.trans.append
            ((Seq.ofList chain_pre).append
              ((Seq.ofList chain_post).cons (l_last, s_mid))) := by
        rw [h_iter_trans_split]
        congr 1
        rw [h_chain_eq, Seq.ofList_append, Seq.ofList_cons]
      -- Now compute the trace via filter manipulation.
      have h_eprev_form :
          sys.trace ⟨e_prev.init, e_prev.trans⟩ = sys.trace e_prev := by
        rcases e_prev with ⟨a, b⟩; rfl
      conv_lhs => rw [h_ei_form, h_iter_trans_split2]
      unfold LabelledSystem.trace
      change ((e_prev.trans.append
                ((Seq.ofList chain_pre).append
                  ((Seq.ofList chain_post).cons (l_last, s_mid)))).filter
                (fun p => ¬ sys.internal p.1)).map Prod.fst
          = ((e_prev.trans.filter (fun p => ¬ sys.internal p.1)).map Prod.fst).append
              (Seq.cons l_last Seq.nil)
      have h_cp_term : (Seq.ofList chain_pre).Terminates := Seq.terminates_ofList _
      have h_cs_term : (Seq.ofList chain_post).Terminates := Seq.terminates_ofList _
      rw [Seq.filter_append _ _ _ h_ep]
      rw [Seq.filter_append _ _ _ h_cp_term]
      rw [seq_filter_internal_list_eq_nil sys chain_pre h_cp_int]
      rw [Stream'.Seq.nil_append]
      rw [Seq.filter_cons_pos (l_last, s_mid) _ h_int]
      rw [seq_filter_internal_list_eq_nil sys chain_post h_cs_int]
      rw [Seq.map_append, Seq.map_cons, Seq.map_nil]

/-- **Aux: trace coupling parametrised by the trans-list.** Strong-induction
form of `reachProb_trace_coupling`. Induction on `L`. -/
private lemma reachProb_trace_coupling_aux
    {sys : LabelledSystem State Label}
    {pe' : ProbabilisticExecution sys^w.toSystem}
    (L : List (Label × State)) (s_init : State) :
    ∀ (e_iter_start : AlterSeq State Label)
      (_h_reach : reachProb sys pe' ⟨s_init, Seq.ofList L⟩ e_iter_start ≠ 0),
      e_iter_start.trans.Terminates ∧
        sys^w.trace ⟨s_init, Seq.ofList L⟩ = sys.trace e_iter_start := by
  classical
  -- Induction on L.
  induction L using List.reverseRecOn with
  | nil =>
    intro e_iter_start h_reach
    -- Extract the reverseRecOn body of reachProb.
    have h_e_w_term : (⟨s_init, Seq.ofList []⟩ : AlterSeq State Label).trans.Terminates :=
      Seq.terminates_ofList []
    have h_toList :
        (⟨s_init, Seq.ofList []⟩ : AlterSeq State Label).trans.toList h_e_w_term = [] := by
      change (Seq.ofList []).toList h_e_w_term = []
      exact Seq.toList_ofList []
    have h_reach' : (open Classical in
        if s_init = e_iter_start.init ∧ e_iter_start.trans = Seq.nil then
          pe'.initState s_init
        else 0) ≠ 0 := by
      intro h_zero
      apply h_reach
      unfold reachProb
      rw [dif_pos h_e_w_term, h_toList, List.reverseRecOn_nil]
      exact h_zero
    by_cases h_cond : s_init = e_iter_start.init ∧ e_iter_start.trans = Seq.nil
    · obtain ⟨_h_init_eq, h_e_nil⟩ := h_cond
      have h_iter_term : e_iter_start.trans.Terminates := by
        rw [h_e_nil]; exact Stream'.Seq.terminates_nil
      refine ⟨h_iter_term, ?_⟩
      have h_trace_w :
          sys^w.trace (⟨s_init, Seq.ofList []⟩ : AlterSeq State Label) = Seq.nil := by
        unfold LabelledSystem.trace
        rw [Seq.ofList_nil]; simp
      have h_trace_s : sys.trace e_iter_start = Seq.nil := by
        unfold LabelledSystem.trace
        rw [h_e_nil]; simp
      rw [h_trace_w, h_trace_s]
    · rw [if_neg h_cond] at h_reach'
      exact absurd rfl h_reach'
  | append_singleton previous_list last_step ih =>
    intro e_iter_start h_reach
    -- Setup termination + toList for the concat list.
    have h_e_w_term :
        (⟨s_init, Seq.ofList (previous_list ++ [last_step])⟩
          : AlterSeq State Label).trans.Terminates :=
      Seq.terminates_ofList _
    have h_toList :
        (⟨s_init, Seq.ofList (previous_list ++ [last_step])⟩
          : AlterSeq State Label).trans.toList h_e_w_term
          = previous_list ++ [last_step] := by
      change (Seq.ofList (previous_list ++ [last_step])).toList h_e_w_term
          = previous_list ++ [last_step]
      exact Seq.toList_ofList _
    -- Helper: the reverseRecOn applied to previous_list = reachProb.
    have h_prev_term :
        (⟨s_init, Seq.ofList previous_list⟩ : AlterSeq State Label).trans.Terminates :=
      Seq.terminates_ofList previous_list
    have h_prev_toList :
        (⟨s_init, Seq.ofList previous_list⟩ : AlterSeq State Label).trans.toList
          h_prev_term = previous_list := by
      change (Seq.ofList previous_list).toList h_prev_term = previous_list
      exact Seq.toList_ofList _
    have h_prev_unfold : ∀ e_prev : AlterSeq State Label,
        reachProb sys pe' ⟨s_init, Seq.ofList previous_list⟩ e_prev =
        (open Classical in
          previous_list.reverseRecOn
            (motive := fun _ => AlterSeq State Label → ENNReal)
            (fun e' =>
              if s_init = e'.init ∧ e'.trans = Seq.nil then
                pe'.initState s_init
              else 0)
            (fun trans_prev last_step ih_function e' =>
              if h_e'_term : e'.trans.Terminates then
                if e'.endState h_e'_term = last_step.2 then
                  let e_w_prev : AlterSeq State Label :=
                    ⟨s_init, Seq.ofList trans_prev⟩
                  ∑' e_prev : AlterSeq State Label,
                    ih_function e_prev *
                      oneIterTransitionProb sys pe' e_w_prev last_step.1 e_prev e'
                else 0
              else 0)
            e_prev) := by
      intro e_prev
      unfold reachProb
      rw [dif_pos h_prev_term, h_prev_toList]
    -- Extract the step branch of reachProb.
    have h_reach' : (open Classical in
        (if h_e'_term : e_iter_start.trans.Terminates then
          if e_iter_start.endState h_e'_term = last_step.2 then
            ∑' e_prev : AlterSeq State Label,
              reachProb sys pe' ⟨s_init, Seq.ofList previous_list⟩ e_prev *
                oneIterTransitionProb sys pe'
                  ⟨s_init, Seq.ofList previous_list⟩ last_step.1 e_prev e_iter_start
          else 0
        else 0)) ≠ 0 := by
      intro h_zero
      apply h_reach
      unfold reachProb
      rw [dif_pos h_e_w_term, h_toList, List.reverseRecOn_concat]
      -- Convert the inner reverseRecOn-on-previous_list back to reachProb,
      -- then apply h_zero.
      have h_swap :
          (open Classical in
            if h_e'_term : e_iter_start.trans.Terminates then
              if e_iter_start.endState h_e'_term = last_step.2 then
                ∑' e_prev : AlterSeq State Label,
                  (previous_list.reverseRecOn
                    (motive := fun _ => AlterSeq State Label → ENNReal)
                    (fun e' =>
                      if s_init = e'.init ∧ e'.trans = Seq.nil then
                        pe'.initState s_init
                      else 0)
                    (fun trans_prev last_step_inner ih_function e' =>
                      if h_e'_term : e'.trans.Terminates then
                        if e'.endState h_e'_term = last_step_inner.2 then
                          let e_w_prev : AlterSeq State Label :=
                            ⟨s_init, Seq.ofList trans_prev⟩
                          ∑' e_prev : AlterSeq State Label,
                            ih_function e_prev *
                              oneIterTransitionProb sys pe' e_w_prev
                                last_step_inner.1 e_prev e'
                        else 0
                      else 0)
                    e_prev) *
                    oneIterTransitionProb sys pe'
                      ⟨s_init, Seq.ofList previous_list⟩ last_step.1 e_prev e_iter_start
              else 0
            else 0) = 0 := by
        split_ifs with h_t h_e
        · apply (ENNReal.tsum_eq_zero).mpr
          intro e_prev
          have := h_prev_unfold e_prev
          rw [← this]
          have h_zero' : ∑' e_prev : AlterSeq State Label,
              reachProb sys pe' ⟨s_init, Seq.ofList previous_list⟩ e_prev *
                oneIterTransitionProb sys pe'
                  ⟨s_init, Seq.ofList previous_list⟩ last_step.1 e_prev e_iter_start
              = 0 := by
            have := h_zero
            simp only [dif_pos h_t, if_pos h_e] at this
            exact this
          exact (ENNReal.tsum_eq_zero.mp h_zero') e_prev
        · rfl
        · rfl
      exact h_swap
    -- Unpack the guards in h_reach'.
    by_cases h_iter_term : e_iter_start.trans.Terminates
    swap
    · rw [dif_neg h_iter_term] at h_reach'; exact absurd rfl h_reach'
    rw [dif_pos h_iter_term] at h_reach'
    by_cases h_end_eq : e_iter_start.endState h_iter_term = last_step.2
    swap
    · rw [if_neg h_end_eq] at h_reach'; exact absurd rfl h_reach'
    rw [if_pos h_end_eq] at h_reach'
    -- Extract e_prev from the tsum.
    rw [Ne, ENNReal.tsum_eq_zero] at h_reach'
    push Not at h_reach'
    obtain ⟨e_prev, h_prev_ne⟩ := h_reach'
    rw [mul_ne_zero_iff] at h_prev_ne
    obtain ⟨h_prev_reach, h_oneIter_ne⟩ := h_prev_ne
    -- Apply IH on (e_prev, h_prev_reach).
    obtain ⟨_h_prev_iter_term, h_prev_trace⟩ := ih e_prev h_prev_reach
    -- Apply oneIterTransitionProb_trace_extension.
    obtain ⟨_h_ep_term, h_es_term, h_trace_ext⟩ :=
      oneIterTransitionProb_trace_extension
        ⟨s_init, Seq.ofList previous_list⟩ last_step.1 e_prev e_iter_start h_oneIter_ne
    refine ⟨h_es_term, ?_⟩
    -- Combine: sys^w.trace e_w split via internal/external case.
    have h_seq_split :
        (Seq.ofList (previous_list ++ [last_step]) : Seq (Label × State))
          = (Seq.ofList previous_list).append
              (Seq.cons last_step Seq.nil) := by
      rw [Seq.ofList_append, Seq.ofList_cons, Seq.ofList_nil]
    have h_prev_term :
        (Seq.ofList previous_list : Seq (Label × State)).Terminates :=
      Seq.terminates_ofList _
    have h_w_trace_split :
        sys^w.trace ⟨s_init, Seq.ofList (previous_list ++ [last_step])⟩
          = (sys^w.trace ⟨s_init, Seq.ofList previous_list⟩).append
              (open Classical in
                if sys.internal last_step.1 then (Seq.nil : Seq Label)
                else Seq.cons last_step.1 Seq.nil) := by
      rw [h_seq_split]
      by_cases h_int : sys.internal last_step.1
      · rw [if_pos h_int, Seq.append_nil]
        exact trace_append_singleton_internal sys^w s_init (Seq.ofList previous_list)
          h_prev_term last_step.1 last_step.2 h_int
      · rw [if_neg h_int]
        exact trace_append_singleton_external sys^w s_init (Seq.ofList previous_list)
          h_prev_term last_step.1 last_step.2 h_int
    rw [h_w_trace_split, h_prev_trace, ← h_trace_ext]

/-- **Sub-claim A (joint trace coupling).** Whenever `reachProb sys pe' e_w_pre
e_iter_start ≠ 0`, the prefix `e_w_pre` terminates, `e_iter_start.trans`
terminates, and the two traces agree: `sys^w.trace e_w_pre = sys.trace
e_iter_start`. This is the trace-side analogue of `reachProb_invariant`
(which gives endState equality). -/
private lemma reachProb_trace_coupling
    {sys : LabelledSystem State Label}
    {pe' : ProbabilisticExecution sys^w.toSystem}
    (e_w_pre e_iter_start : AlterSeq State Label)
    (h_reach : reachProb sys pe' e_w_pre e_iter_start ≠ 0) :
    ∃ (_ : e_w_pre.trans.Terminates),
      e_iter_start.trans.Terminates ∧
        sys^w.trace e_w_pre = sys.trace e_iter_start := by
  classical
  -- (a) e_w_pre.trans.Terminates: from the outer `if` in reachProb.
  have h_e_w_term : e_w_pre.trans.Terminates := by
    by_contra h_neg
    apply h_reach
    unfold reachProb
    exact dif_neg h_neg
  refine ⟨h_e_w_term, ?_⟩
  -- Reduce to the aux lemma via `e_w_pre = ⟨e_w_pre.init, Seq.ofList (toList _)⟩`.
  set L : List (Label × State) := e_w_pre.trans.toList h_e_w_term with hL
  have h_trans_eq : e_w_pre.trans = Seq.ofList L := by
    rw [hL]; exact (Seq.ofList_toList _ _).symm
  have h_reach_canon :
      reachProb sys pe' ⟨e_w_pre.init, Seq.ofList L⟩ e_iter_start ≠ 0 := by
    have h_ewp_eq : (⟨e_w_pre.init, Seq.ofList L⟩ : AlterSeq State Label) = e_w_pre := by
      conv_rhs => rw [show e_w_pre = ⟨e_w_pre.init, e_w_pre.trans⟩ from by
        rcases e_w_pre with ⟨a, b⟩; rfl]
      rw [← h_trans_eq]
    rw [h_ewp_eq]; exact h_reach
  obtain ⟨h_es_term, h_trace⟩ :=
    reachProb_trace_coupling_aux L e_w_pre.init e_iter_start h_reach_canon
  refine ⟨h_es_term, ?_⟩
  -- Translate trace identity back to e_w_pre.
  have h_ewp_eq : (⟨e_w_pre.init, Seq.ofList L⟩ : AlterSeq State Label) = e_w_pre := by
    conv_rhs => rw [show e_w_pre = ⟨e_w_pre.init, e_w_pre.trans⟩ from by
      rcases e_w_pre with ⟨a, b⟩; rfl]
    rw [← h_trans_eq]
  rw [← h_ewp_eq]
  exact h_trace

/-- **Terminates of an `append`** when both parts terminate. -/
private lemma terminates_append_of_terminates
    {α : Type*} {s s' : Seq α} (h : s.Terminates) (h' : s'.Terminates) :
    (s.append s').Terminates :=
  ⟨_, Seq.terminatedAt_append_find h h'.choose_spec⟩

/-- **`endState` of `⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩`** is
the last state of `chain`, or `e_prev.endState` if `chain = []`.

Stated as a forall over the Terminates proof for proof-irrelevance flexibility. -/
private lemma endState_append_ofList_eq
    (e_prev : AlterSeq State Label) (h_ep : e_prev.trans.Terminates)
    (chain : List (Label × State))
    (h_term : (e_prev.trans.append (Seq.ofList chain)).Terminates) :
    (⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩ :
        AlterSeq State Label).endState h_term
      = (chain.getLast?.map Prod.snd).getD (e_prev.endState h_ep) := by
  classical
  induction chain using List.reverseRecOn with
  | nil =>
    -- chain = [], Seq.ofList [] = Seq.nil, append Seq.nil = self.
    show (⟨e_prev.init, e_prev.trans.append (Seq.ofList ([] : List (Label × State)))⟩ :
            AlterSeq State Label).endState h_term
        = (([] : List (Label × State)).getLast?.map Prod.snd).getD (e_prev.endState h_ep)
    simp only [List.getLast?_nil, Option.map_none, Option.getD_none, Seq.ofList_nil,
                Seq.append_nil]
  | append_singleton previous_chain last_pair ih =>
    -- chain = previous_chain ++ [last_pair]. last entry of chain = last_pair.
    simp only [List.getLast?_concat, Option.map_some, Option.getD_some]
    -- Step 1: Rewrite Seq.ofList (previous_chain ++ [last_pair]) =
    --   (Seq.ofList previous_chain).append (Seq.cons last_pair Seq.nil).
    -- Step 2: Associativity.
    -- Goal becomes endState ⟨e_prev.init, prefix.append (cons last_pair nil)⟩ = last_pair.2
    set prefix_seq : Seq (Label × State) :=
      e_prev.trans.append (Seq.ofList previous_chain) with hps_def
    have h_prefix_term : prefix_seq.Terminates :=
      terminates_append_of_terminates h_ep (Seq.terminates_ofList _)
    have h_eq_seq :
        e_prev.trans.append (Seq.ofList (previous_chain ++ [last_pair]))
          = prefix_seq.append (Seq.cons last_pair Seq.nil) := by
      rw [Seq.ofList_append, Seq.ofList_cons, Seq.ofList_nil, ← Seq.append_assoc]
    -- Combine into AlterSeq equality.
    have h_alter_eq :
        (⟨e_prev.init, e_prev.trans.append (Seq.ofList (previous_chain ++ [last_pair]))⟩ :
            AlterSeq State Label)
          = ⟨e_prev.init, prefix_seq.append (Seq.cons last_pair Seq.nil)⟩ := by
      congr 1
    -- Now apply endState_append_singleton.
    have h_es :=
      AlterSeq.endState_append_singleton
        (⟨e_prev.init, prefix_seq⟩ : AlterSeq State Label)
        h_prefix_term last_pair.1 last_pair.2
    -- Use proof-irrelevance to align.
    rw [show (⟨e_prev.init, e_prev.trans.append (Seq.ofList (previous_chain ++ [last_pair]))⟩ :
              AlterSeq State Label).endState h_term
          = (⟨e_prev.init, prefix_seq.append (Seq.cons last_pair Seq.nil)⟩ :
              AlterSeq State Label).endState
              (h_alter_eq ▸ h_term) from by
      congr 1]
    exact h_es

/-- **`oneIterTransitionProb` evaluation at `⟨e_prev.init, e_prev.trans.append
(Seq.ofList chain)⟩`** in the internal case. The prefix-condition is
automatically satisfied. -/
private lemma oneIterTransitionProb_internal_at_fromChain
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_prev : AlterSeq State Label) (h_ewp : e_w_prev.trans.Terminates)
    (l_last : Label) (h_int : sys.internal l_last)
    (e_prev : AlterSeq State Label) (h_ep : e_prev.trans.Terminates)
    (chain : List (Label × State)) :
    oneIterTransitionProb sys pe' e_w_prev l_last e_prev
        ⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩ =
      ∑' μ : PMF State,
        pe'.scheduler.next e_w_prev (some (l_last, μ)) *
        (open Classical in
          if h_supp : some (l_last, μ) ∈ (pe'.scheduler.next e_w_prev).support then
            have h_sw : sys^w.step (e_w_prev.endState h_ewp) l_last μ :=
              pe'.scheduler.valid e_w_prev (Nat.find h_ewp) (e_w_prev.endState h_ewp)
                (Nat.find_spec h_ewp)
                (AlterSeq.stateAt_find_eq_endState e_w_prev h_ewp)
                l_last μ h_supp
            have h_wt : weakTau sys (PMF.pure (e_w_prev.endState h_ewp)) μ := by
              rcases h_sw with ⟨_, h⟩ | ⟨h_ext, _⟩
              · exact h
              · exact absurd h_int h_ext
            chainProb h_wt.witness ⟨e_w_prev.endState h_ewp, Seq.nil⟩ chain
          else 0) := by
  classical
  -- Set up the canonical e_iter_start := ⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩
  set e_iter_start : AlterSeq State Label :=
    ⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩ with h_ei_def
  have h_es_term : e_iter_start.trans.Terminates :=
    terminates_append_of_terminates h_ep (Seq.terminates_ofList _)
  -- Unfold and verify the prefix condition.
  unfold oneIterTransitionProb
  rw [dif_pos h_ewp, dif_pos h_ep, dif_pos h_es_term]
  have h_iter_toList :
      e_iter_start.trans.toList h_es_term
        = e_prev.trans.toList h_ep ++ chain := by
    change (e_prev.trans.append (Seq.ofList chain)).toList h_es_term
          = e_prev.trans.toList h_ep ++ chain
    rw [Seq.toList_append e_prev.trans (Seq.ofList chain) h_ep (Seq.terminates_ofList _)]
    congr 1
    exact Seq.toList_ofList _
  have h_prefix_cond :
      e_prev.init = e_iter_start.init ∧
        (e_iter_start.trans.toList h_es_term).take (e_prev.trans.toList h_ep).length
          = e_prev.trans.toList h_ep := by
    refine ⟨rfl, ?_⟩
    rw [h_iter_toList]
    exact List.take_left
  rw [dif_pos h_prefix_cond]
  -- The chain extracted is `(e_iter_start.toList).drop e_prev.toList.length = chain`.
  have h_chain_eq :
      (e_iter_start.trans.toList h_es_term).drop (e_prev.trans.toList h_ep).length = chain := by
    rw [h_iter_toList]
    exact List.drop_left
  simp only [h_chain_eq, dif_pos h_int]

/-- **`oneIterTransitionProb` evaluation at `⟨e_prev.init, e_prev.trans.append
(Seq.ofList chain)⟩`** in the external case. The prefix-condition is
automatically satisfied; the result expresses the inner factor in terms of
`splitAtLabel l_last chain`. -/
private lemma oneIterTransitionProb_external_at_fromChain
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_prev : AlterSeq State Label) (h_ewp : e_w_prev.trans.Terminates)
    (l_last : Label) (h_ext : ¬ sys.internal l_last)
    (e_prev : AlterSeq State Label) (h_ep : e_prev.trans.Terminates)
    (chain : List (Label × State)) :
    oneIterTransitionProb sys pe' e_w_prev l_last e_prev
        ⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩ =
      ∑' μ : PMF State,
        pe'.scheduler.next e_w_prev (some (l_last, μ)) *
        (open Classical in
          if h_supp : some (l_last, μ) ∈ (pe'.scheduler.next e_w_prev).support then
            have h_sw : sys^w.step (e_w_prev.endState h_ewp) l_last μ :=
              pe'.scheduler.valid e_w_prev (Nat.find h_ewp) (e_w_prev.endState h_ewp)
                (Nat.find_spec h_ewp)
                (AlterSeq.stateAt_find_eq_endState e_w_prev h_ewp)
                l_last μ h_supp
            have h_ws : weakStep sys (PMF.pure (e_w_prev.endState h_ewp)) l_last μ := by
              rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
              · exact absurd h_int' h_ext
              · exact h
            (match splitAtLabel l_last chain with
              | (_, none) => (0 : ENNReal)
              | (chain_pre, some (s_mid, chain_post)) =>
                let s_mid_pre : State :=
                  (chain_pre.getLast?.map Prod.snd).getD (e_w_prev.endState h_ewp)
                chainProb h_ws.weakTau_pre.witness
                    ⟨e_w_prev.endState h_ewp, Seq.nil⟩ chain_pre *
                  (∑' μ_l : PMF State,
                    h_ws.hyperStep_mid.kernel s_mid_pre μ_l * μ_l s_mid) *
                  chainProb h_ws.weakTau_post.witness ⟨s_mid, Seq.nil⟩ chain_post)
          else 0) := by
  classical
  set e_iter_start : AlterSeq State Label :=
    ⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩ with h_ei_def
  have h_es_term : e_iter_start.trans.Terminates :=
    terminates_append_of_terminates h_ep (Seq.terminates_ofList _)
  unfold oneIterTransitionProb
  rw [dif_pos h_ewp, dif_pos h_ep, dif_pos h_es_term]
  have h_iter_toList :
      e_iter_start.trans.toList h_es_term
        = e_prev.trans.toList h_ep ++ chain := by
    change (e_prev.trans.append (Seq.ofList chain)).toList h_es_term
          = e_prev.trans.toList h_ep ++ chain
    rw [Seq.toList_append e_prev.trans (Seq.ofList chain) h_ep (Seq.terminates_ofList _)]
    congr 1
    exact Seq.toList_ofList _
  have h_prefix_cond :
      e_prev.init = e_iter_start.init ∧
        (e_iter_start.trans.toList h_es_term).take (e_prev.trans.toList h_ep).length
          = e_prev.trans.toList h_ep := by
    refine ⟨rfl, ?_⟩
    rw [h_iter_toList]
    exact List.take_left
  rw [dif_pos h_prefix_cond]
  have h_chain_eq :
      (e_iter_start.trans.toList h_es_term).drop (e_prev.trans.toList h_ep).length = chain := by
    rw [h_iter_toList]
    exact List.drop_left
  simp only [h_chain_eq, dif_neg h_ext]
  -- Both sides now match-over `splitAtLabel l_last chain` (LHS) vs its `.2` (RHS).
  -- Align by destructing the split tuple.
  congr 1; funext μ; congr 1
  by_cases h_supp : some (l_last, μ) ∈ (pe'.scheduler.next e_w_prev).support
  · rw [dif_pos h_supp, dif_pos h_supp]
    rcases h_spl : splitAtLabel l_last chain with ⟨cp, opt⟩
    rcases opt with _ | ⟨sm, cpost⟩
    · simp
    · simp
  · rw [dif_neg h_supp, dif_neg h_supp]

/-- **Forward direction of `splitAtLabel`.** When `chain_pre` contains no entry
with label `l`, the split of `chain_pre ++ (l, s_mid) :: chain_post` at the
first `l`-position gives back `(chain_pre, some (s_mid, chain_post))`. -/
private lemma splitAtLabel_append_cons_of_not_mem (l : Label)
    (chain_pre : List (Label × State)) (s_mid : State)
    (chain_post : List (Label × State))
    (h_no_l : ∀ pair ∈ chain_pre, pair.1 ≠ l) :
    splitAtLabel l (chain_pre ++ (l, s_mid) :: chain_post)
      = (chain_pre, some (s_mid, chain_post)) := by
  classical
  induction chain_pre with
  | nil =>
    simp [splitAtLabel]
  | cons hd tl ih =>
    have h_hd : hd.1 ≠ l := h_no_l hd (List.mem_cons_self)
    have h_tl : ∀ pair ∈ tl, pair.1 ≠ l := fun p hp =>
      h_no_l p (List.mem_cons_of_mem _ hp)
    unfold splitAtLabel
    rw [List.cons_append]
    simp only
    rw [if_neg h_hd]
    have ih' := ih h_tl
    simp only [ih']

/-- **Endstate of an `(l, s_mid)`-pierced chain.** The endstate of
`chain_pre ++ (l, s_mid) :: chain_post` (relative to any default) is the
endstate of `(l, s_mid) :: chain_post`, which is `(chain_post.getLast?.map
Prod.snd).getD s_mid`. -/
private lemma getLast_map_snd_append_cons (l : Label)
    (chain_pre : List (Label × State)) (s_mid : State)
    (chain_post : List (Label × State)) (default : State) :
    ((chain_pre ++ (l, s_mid) :: chain_post).getLast?.map Prod.snd).getD default
      = (chain_post.getLast?.map Prod.snd).getD s_mid := by
  rw [List.getLast?_append_cons, List.getLast?_cons]
  simp only [Option.map_some, Option.getD_some]
  rcases h : chain_post.getLast? with _ | ⟨l', s'⟩
  · simp
  · simp

/-- **Chain decomposition marginal for the external case.** For a `weakStep`
witness, summing the chain-decomposed factor over all chains whose end-state
equals `s_last` collapses to `μ s_last`.

The factor is:
```
match splitAtLabel l_last chain with
| (_, none) => (0 : ENNReal)
| (chain_pre, some (s_mid, chain_post)) =>
  chainProb σ_pre ⟨s_pre, nil⟩ chain_pre *
    (∑' μ_l, p s_mid_pre μ_l * μ_l s_mid) *
    chainProb σ_post ⟨s_mid, nil⟩ chain_post
```
gated by the `(chain.getLast?.map Prod.snd).getD s_pre = s_last` condition.

Proof: reorganize via a chain ↔ (cp, sm, cpost) bijection (using
`splitAtLabel_append_cons_of_not_mem` / `splitAtLabel_some_reconstruct`),
marginalize chain_post via `chainProb_witness_endState_marginal`,
marginalize chain_pre similarly, then use `hyperStep_mid.post_eq_bind` plus
`weakTau_pre.witness_run` / `weakTau_post.witness_run` to combine into
`μ s_last`. -/
private lemma weakStep_chain_marginal
    {sys : LabelledSystem State Label}
    {s_pre : State} {l_last : Label} {μ : PMF State}
    (h_ext : ¬ sys.internal l_last)
    (h_ws : weakStep sys (PMF.pure s_pre) l_last μ)
    (s_last : State) :
    (∑' chain : List (Label × State),
      (open Classical in
        if (chain.getLast?.map Prod.snd).getD s_pre = s_last then
          (match splitAtLabel l_last chain with
            | (_, none) => (0 : ENNReal)
            | (chain_pre, some (s_mid, chain_post)) =>
              let s_mid_pre : State :=
                (chain_pre.getLast?.map Prod.snd).getD s_pre
              chainProb h_ws.weakTau_pre.witness ⟨s_pre, Seq.nil⟩ chain_pre *
                (∑' μ_l : PMF State,
                  h_ws.hyperStep_mid.kernel s_mid_pre μ_l * μ_l s_mid) *
                chainProb h_ws.weakTau_post.witness ⟨s_mid, Seq.nil⟩ chain_post)
        else 0)) = μ s_last := by
  classical
  -- Local abbreviations.
  set σ_pre := h_ws.weakTau_pre.witness with hσ_pre_def
  set σ_post := h_ws.weakTau_post.witness with hσ_post_def
  set p := h_ws.hyperStep_mid.kernel with hp_def
  -- **Step 1: Bijection.** Re-index the chain-sum via
  -- `chain ↔ (chain_pre, s_mid, chain_post)` with `chain_pre` containing no
  -- `l_last`. Chains with no `l_last` contribute 0 (the match returns 0).
  -- Forward direction: forward (cp, sm, cpost) = cp ++ (l_last, sm) :: cpost.
  -- Use `tsum_eq_tsum_of_ne_zero_bij` with i = forward (restricted to support).
  set F : List (Label × State) → ENNReal := fun chain =>
    (if (chain.getLast?.map Prod.snd).getD s_pre = s_last then
      (match splitAtLabel l_last chain with
        | (_, none) => (0 : ENNReal)
        | (chain_pre, some (s_mid, chain_post)) =>
          let s_mid_pre : State :=
            (chain_pre.getLast?.map Prod.snd).getD s_pre
          chainProb σ_pre ⟨s_pre, Seq.nil⟩ chain_pre *
            (∑' μ_l : PMF State, p s_mid_pre μ_l * μ_l s_mid) *
            chainProb σ_post ⟨s_mid, Seq.nil⟩ chain_post)
    else 0) with hF_def
  set G : List (Label × State) × State × List (Label × State) → ENNReal :=
    fun t =>
      (if (t.2.2.getLast?.map Prod.snd).getD t.2.1 = s_last then
        (let s_mid_pre : State :=
          (t.1.getLast?.map Prod.snd).getD s_pre
        chainProb σ_pre ⟨s_pre, Seq.nil⟩ t.1 *
          (∑' μ_l : PMF State, p s_mid_pre μ_l * μ_l t.2.1) *
          chainProb σ_post ⟨t.2.1, Seq.nil⟩ t.2.2)
      else 0) with hG_def
  -- Forward map: triple → chain.
  set forward : List (Label × State) × State × List (Label × State) →
                List (Label × State) :=
    fun t => t.1 ++ (l_last, t.2.1) :: t.2.2 with hfwd_def
  -- σ_pre.internal_only: any pair emitted has internal label.
  have h_no_l_of_supp : ∀ t : List (Label × State) × State × List (Label × State),
      G t ≠ 0 → ∀ pair ∈ t.1, pair.1 ≠ l_last := by
    intro t ht pair h_mem h_eq_l
    apply ht
    simp only [hG_def]
    have h_chain_zero : chainProb σ_pre ⟨s_pre, Seq.nil⟩ t.1 = 0 := by
      apply chainProb_eq_zero_of_not_all_internal
      intro h_all
      have h_int_pair : sys.internal pair.1 := h_all pair h_mem
      rw [h_eq_l] at h_int_pair
      exact h_ext h_int_pair
    rw [h_chain_zero]
    split_ifs <;> ring
  -- Forward map is injective on support of G.
  have h_forward_inj : ∀ t₁ t₂ : List (Label × State) × State × List (Label × State),
      G t₁ ≠ 0 → G t₂ ≠ 0 → forward t₁ = forward t₂ → t₁ = t₂ := by
    intro t₁ t₂ h1 h2 h_eq
    -- forward t₁ = forward t₂ means: t₁.1 ++ (l_last, t₁.2.1) :: t₁.2.2
    --                              = t₂.1 ++ (l_last, t₂.2.1) :: t₂.2.2
    -- Both t₁.1 and t₂.1 have no l_last (by h_no_l_of_supp), so they're the
    -- prefix before first l_last. splitAtLabel reconstruction yields t₁ = t₂.
    have h_no_l_1 := h_no_l_of_supp t₁ h1
    have h_no_l_2 := h_no_l_of_supp t₂ h2
    have h_split_1 : splitAtLabel l_last (forward t₁) =
        (t₁.1, some (t₁.2.1, t₁.2.2)) := by
      simp only [hfwd_def]
      exact splitAtLabel_append_cons_of_not_mem l_last t₁.1 t₁.2.1 t₁.2.2 h_no_l_1
    have h_split_2 : splitAtLabel l_last (forward t₂) =
        (t₂.1, some (t₂.2.1, t₂.2.2)) := by
      simp only [hfwd_def]
      exact splitAtLabel_append_cons_of_not_mem l_last t₂.1 t₂.2.1 t₂.2.2 h_no_l_2
    rw [h_eq] at h_split_1
    rw [h_split_1] at h_split_2
    simp only [Prod.mk.injEq, Option.some.injEq] at h_split_2
    obtain ⟨h_a, h_b, h_c⟩ := h_split_2
    obtain ⟨t₁_1, t₁_2_1, t₁_2_2⟩ := t₁
    obtain ⟨t₂_1, t₂_2_1, t₂_2_2⟩ := t₂
    dsimp at h_a h_b h_c
    subst h_a; subst h_b; subst h_c; rfl
  -- F vanishes outside the range of forward.
  have h_F_in_range : ∀ chain : List (Label × State), F chain ≠ 0 →
      ∃ t, G t ≠ 0 ∧ forward t = chain := by
    intro chain hF
    simp only [hF_def] at hF
    by_cases h_match : (chain.getLast?.map Prod.snd).getD s_pre = s_last
    swap
    · rw [if_neg h_match] at hF; exact absurd rfl hF
    rw [if_pos h_match] at hF
    -- match on splitAtLabel chain.
    rcases h_spl : splitAtLabel l_last chain with ⟨cp, opt⟩
    rcases opt with _ | ⟨sm, cpost⟩
    · rw [h_spl] at hF; exact absurd rfl hF
    -- Reconstruct chain = cp ++ (l_last, sm) :: cpost; cp has no l_last.
    have h_recon := splitAtLabel_some_reconstruct l_last chain cp sm cpost h_spl
    refine ⟨(cp, sm, cpost), ?_, ?_⟩
    · simp only [hG_def]
      -- Show G (cp, sm, cpost) ≠ 0.
      -- Endstate condition: by h_match and the recon.
      have h_end_eq : (cpost.getLast?.map Prod.snd).getD sm = s_last := by
        have hL := getLast_map_snd_append_cons l_last cp sm cpost s_pre
        rw [← h_recon.1] at hL
        rw [← hL]; exact h_match
      rw [if_pos h_end_eq]
      rw [h_spl] at hF
      convert hF using 1
    · simp only [hfwd_def]; exact h_recon.1.symm
  -- F at forward = G on the support of G (where t.1 has no l_last).
  have h_F_at_fwd_supp : ∀ t : List (Label × State) × State × List (Label × State),
      G t ≠ 0 → F (forward t) = G t := by
    intro t ht
    have h_no_l := h_no_l_of_supp t ht
    simp only [hF_def, hG_def, hfwd_def]
    have h_spl := splitAtLabel_append_cons_of_not_mem l_last t.1 t.2.1 t.2.2 h_no_l
    have hL := getLast_map_snd_append_cons l_last t.1 t.2.1 t.2.2 s_pre
    rw [hL, h_spl]
  -- Apply tsum_eq_tsum_of_ne_zero_bij.
  let i : Function.support G → List (Label × State) :=
    fun x => forward x.1
  have hi : Function.Injective i := by
    rintro ⟨t₁, h1⟩ ⟨t₂, h2⟩ h_eq
    simp only [i] at h_eq
    have h_t_eq := h_forward_inj t₁ t₂ h1 h2 h_eq
    exact Subtype.ext h_t_eq
  have h_supp_sub : Function.support F ⊆ Set.range i := by
    intro chain h_chain
    obtain ⟨t, ht, h_fwd_eq⟩ := h_F_in_range chain h_chain
    refine ⟨⟨t, ht⟩, ?_⟩
    simp only [i]; exact h_fwd_eq
  have h_eval : ∀ x : Function.support G, F (i x) = G x.1 := by
    rintro ⟨t, ht⟩
    simp only [i]
    exact h_F_at_fwd_supp t ht
  have h_phaseA :
      (∑' chain : List (Label × State), F chain) =
      ∑' t : List (Label × State) × State × List (Label × State), G t :=
    tsum_eq_tsum_of_ne_zero_bij i hi h_supp_sub h_eval
  -- Convert the goal LHS to ∑' F.
  change (∑' chain : List (Label × State), F chain) = μ s_last
  rw [h_phaseA]
  -- **Step 2: Re-order sum.** ∑' t, G t = ∑' cp sm cpost, G (cp,sm,cpost).
  rw [show (∑' t : List (Label × State) × State × List (Label × State), G t)
      = ∑' (cp : List (Label × State)) (sm : State) (cpost : List (Label × State)),
        G (cp, sm, cpost) from by
    rw [ENNReal.tsum_prod']
    apply tsum_congr; intro cp
    rw [ENNReal.tsum_prod']]
  -- Pull out chain_pre and "kernel" factor from the cpost sum.
  have h_cpost_marginal : ∀ cp sm,
      (∑' cpost : List (Label × State), G (cp, sm, cpost))
        = (let s_mid_pre := (cp.getLast?.map Prod.snd).getD s_pre
           chainProb σ_pre ⟨s_pre, Seq.nil⟩ cp *
             (∑' μ_l : PMF State, p s_mid_pre μ_l * μ_l sm)) *
          (∑' cpost : List (Label × State),
            (if (cpost.getLast?.map Prod.snd).getD sm = s_last then
              chainProb σ_post ⟨sm, Seq.nil⟩ cpost
            else 0)) := by
    intro cp sm
    simp only [hG_def]
    rw [show (∑' cpost : List (Label × State),
          if (Option.map Prod.snd cpost.getLast?).getD sm = s_last then
            (let s_mid_pre := (cp.getLast?.map Prod.snd).getD s_pre
             (chainProb σ_pre ⟨s_pre, Seq.nil⟩ cp *
                ∑' μ_l : PMF State, p s_mid_pre μ_l * μ_l sm) *
              chainProb σ_post ⟨sm, Seq.nil⟩ cpost)
          else 0)
        = ∑' cpost : List (Label × State),
          (let s_mid_pre := (cp.getLast?.map Prod.snd).getD s_pre
           chainProb σ_pre ⟨s_pre, Seq.nil⟩ cp *
            (∑' μ_l : PMF State, p s_mid_pre μ_l * μ_l sm)) *
          (if (Option.map Prod.snd cpost.getLast?).getD sm = s_last then
            chainProb σ_post ⟨sm, Seq.nil⟩ cpost
          else 0) from by
      apply tsum_congr; intro cpost
      split_ifs <;> [ring; ring]]
    rw [ENNReal.tsum_mul_left]
  -- chain_post marginal: ∑ cpost (with endstate = s_last), chainProb σ_post · cpost
  --   = (σ_post.run witness_fuel sm) s_last.
  have h_post_marg : ∀ sm,
      (∑' cpost : List (Label × State),
        (if (cpost.getLast?.map Prod.snd).getD sm = s_last then
          chainProb σ_post ⟨sm, Seq.nil⟩ cpost
        else 0)) = σ_post.run h_ws.weakTau_post.witness_fuel sm s_last := by
    intro sm
    simp only [hσ_post_def, weakTau.witness]
    rw [chainProb_endState_marginal_of_boundedFuel
      h_ws.weakTau_post.choose h_ws.weakTau_post.witness_fuel sm s_last]
  -- Apply the marginal to the inner sums.
  rw [show (∑' (cp : List (Label × State)) (sm : State) (cpost : List (Label × State)),
        G (cp, sm, cpost))
      = ∑' (cp : List (Label × State)) (sm : State),
          (let s_mid_pre := (cp.getLast?.map Prod.snd).getD s_pre
           chainProb σ_pre ⟨s_pre, Seq.nil⟩ cp *
             (∑' μ_l : PMF State, p s_mid_pre μ_l * μ_l sm)) *
          σ_post.run h_ws.weakTau_post.witness_fuel sm s_last from by
        apply tsum_congr; intro cp
        apply tsum_congr; intro sm
        rw [h_cpost_marginal cp sm, h_post_marg sm]]
  -- Phase 3: cp marginal. Let H(s) := ∑' sm, (∑' μ_l, p s μ_l * μ_l sm) *
  --                              σ_post.run · sm s_last.
  set H : State → ENNReal := fun s =>
    ∑' sm : State,
      (∑' μ_l : PMF State, p s μ_l * μ_l sm) *
      σ_post.run h_ws.weakTau_post.witness_fuel sm s_last with hH_def
  -- Rewrite goal: pull H out.
  have h_use_H : (∑' (cp : List (Label × State)) (sm : State),
          (let s_mid_pre := (cp.getLast?.map Prod.snd).getD s_pre
           chainProb σ_pre ⟨s_pre, Seq.nil⟩ cp *
             (∑' μ_l : PMF State, p s_mid_pre μ_l * μ_l sm)) *
          σ_post.run h_ws.weakTau_post.witness_fuel sm s_last)
      = ∑' cp : List (Label × State),
          chainProb σ_pre ⟨s_pre, Seq.nil⟩ cp *
          H ((cp.getLast?.map Prod.snd).getD s_pre) := by
    apply tsum_congr; intro cp
    simp only [hH_def]
    rw [show (∑' sm : State,
          (chainProb σ_pre ⟨s_pre, Seq.nil⟩ cp *
            ∑' μ_l : PMF State,
              p ((cp.getLast?.map Prod.snd).getD s_pre) μ_l * μ_l sm) *
          σ_post.run h_ws.weakTau_post.witness_fuel sm s_last)
        = ∑' sm : State,
          chainProb σ_pre ⟨s_pre, Seq.nil⟩ cp *
          ((∑' μ_l : PMF State,
              p ((cp.getLast?.map Prod.snd).getD s_pre) μ_l * μ_l sm) *
            σ_post.run h_ws.weakTau_post.witness_fuel sm s_last) from by
      apply tsum_congr; intro sm; ring]
    rw [ENNReal.tsum_mul_left]
  rw [h_use_H]
  -- chain_pre marginal: ∑' cp (with endstate = s), chainProb σ_pre cp = preDist s.
  have h_cp_marg : ∀ s : State,
      (∑' cp : List (Label × State),
        (if (cp.getLast?.map Prod.snd).getD s_pre = s then
          chainProb σ_pre ⟨s_pre, Seq.nil⟩ cp
        else 0)) = h_ws.preDist s := by
    intro s
    simp only [hσ_pre_def, weakTau.witness]
    rw [chainProb_endState_marginal_of_boundedFuel
      h_ws.weakTau_pre.choose h_ws.weakTau_pre.witness_fuel s_pre s]
    have h_eq : (h_ws.weakTau_pre.choose.boundedFuel
        h_ws.weakTau_pre.witness_fuel).run h_ws.weakTau_pre.witness_fuel s_pre
        = h_ws.weakTau_pre.witness.run h_ws.weakTau_pre.witness_fuel s_pre := rfl
    rw [h_eq]
    exact weakTau_witness_run_at_state h_ws.weakTau_pre s
  -- ∑' cp, chainProb cp · H(end cp) = ∑' s, preDist s · H s.
  rw [show (∑' cp : List (Label × State),
          chainProb σ_pre ⟨s_pre, Seq.nil⟩ cp *
          H ((cp.getLast?.map Prod.snd).getD s_pre))
        = ∑' s : State, h_ws.preDist s * H s from by
      have h_intermediate : (∑' cp : List (Label × State),
              chainProb σ_pre ⟨s_pre, Seq.nil⟩ cp *
              H ((cp.getLast?.map Prod.snd).getD s_pre))
          = ∑' (cp : List (Label × State)) (s : State),
            (if (cp.getLast?.map Prod.snd).getD s_pre = s then
              chainProb σ_pre ⟨s_pre, Seq.nil⟩ cp * H s
            else 0) := by
        apply tsum_congr; intro cp
        rw [tsum_eq_single ((cp.getLast?.map Prod.snd).getD s_pre)]
        · rw [if_pos rfl]
        · intro s' h_ne
          rw [if_neg (Ne.symm h_ne)]
      rw [h_intermediate]
      rw [ENNReal.tsum_comm]
      apply tsum_congr; intro s
      rw [show (∑' cp : List (Label × State),
            (if (cp.getLast?.map Prod.snd).getD s_pre = s then
              chainProb σ_pre ⟨s_pre, Seq.nil⟩ cp * H s
            else 0))
          = H s * ∑' cp : List (Label × State),
            (if (cp.getLast?.map Prod.snd).getD s_pre = s then
              chainProb σ_pre ⟨s_pre, Seq.nil⟩ cp
            else 0) from by
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr; intro cp
          split_ifs <;> ring]
      rw [h_cp_marg s]
      ring]
  -- Phase 4: combine.
  -- μ s_last = (postDist.bind σ_post.run) s_last
  --          = ∑' s', postDist s' · σ_post.run · s' s_last
  --          = ∑' s', (∑' s, preDist s · ((p s).bind id) s') · σ_post.run · s' s_last
  --          = ∑' s, preDist s · ∑' s', ((p s).bind id) s' · σ_post.run · s' s_last
  --          = ∑' s, preDist s · H s.
  -- σ_post and σ_post.run depend on h_ws.weakTau_post which fixes h_ws.postDist's
  -- target; rewriting h_ws.postDist in σ_post.run's *target arg* fails. So instead
  -- of rewriting h_postD globally, we use h_postD only in the part of the
  -- expression where it lives unambiguously.
  --
  -- Strategy: compute μ s_last via h_ws.weakTau_post.witness_run, then PMF.bind_apply,
  -- and finally use h_postD with the bind-bind associativity.
  -- We work backwards: show LHS = ∑' s, preDist s * H s = μ s_last via:
  --   μ s_last = (postDist.bind σ_post.run) s_last  (witness_run)
  --            = ∑' s', postDist s' * σ_post.run s' s_last      (bind_apply)
  --            = ∑' s', (preDist.bind ...) s' * σ_post.run s' s_last  (post_eq)
  --            = ∑' s' s, preDist s * ((p s).bind id) s'
  --                                 * σ_post.run s' s_last (bind_apply + Fubini)
  --            = ∑' s, preDist s * ∑' s', ((p s).bind id) s' * σ_post.run s' s_last
  --            = ∑' s, preDist s * H s.
  have h_mu_eq : μ s_last =
      (h_ws.postDist.bind (σ_post.run h_ws.weakTau_post.witness_fuel)) s_last := by
    rw [show (h_ws.postDist.bind (σ_post.run h_ws.weakTau_post.witness_fuel))
        = μ from h_ws.weakTau_post.witness_run]
  rw [h_mu_eq, PMF.bind_apply]
  -- Now: ∑' s, preDist s * H s = ∑' s', postDist s' * σ_post.run · s' s_last.
  have h_postD : h_ws.postDist =
      h_ws.preDist.bind (fun s => (p s).bind id) := h_ws.hyperStep_mid.post_eq_bind
  -- Replace each h_ws.postDist s' on the RHS via h_postD.
  -- The issue with rewrite is that σ_post.run's TYPE depends on h_ws.postDist.
  -- Solution: rewrite only the value (h_ws.postDist s'), not the type.
  -- Use `Eq.mpr`-free: simply compute the RHS via a pointwise tsum_congr.
  rw [show (∑' s' : State,
        h_ws.postDist s' * σ_post.run h_ws.weakTau_post.witness_fuel s' s_last)
      = ∑' s' : State,
        (h_ws.preDist.bind (fun s => (p s).bind id)) s' *
          σ_post.run h_ws.weakTau_post.witness_fuel s' s_last from by
    apply tsum_congr; intro s'
    rw [show h_ws.postDist s' = (h_ws.preDist.bind (fun s => (p s).bind id)) s' from
      congrArg (fun ρ => ρ s') h_postD]]
  -- Apply bind_apply on the preDist term.
  rw [show (∑' s' : State,
        (h_ws.preDist.bind (fun s => (p s).bind id)) s' *
          σ_post.run h_ws.weakTau_post.witness_fuel s' s_last)
      = ∑' s' : State,
        (∑' s : State, h_ws.preDist s * ((p s).bind id) s') *
          σ_post.run h_ws.weakTau_post.witness_fuel s' s_last from by
    apply tsum_congr; intro s'; rw [PMF.bind_apply]]
  -- Distribute.
  rw [show (∑' s' : State,
        (∑' s : State, h_ws.preDist s * ((p s).bind id) s') *
          σ_post.run h_ws.weakTau_post.witness_fuel s' s_last)
      = ∑' (s' : State) (s : State),
        h_ws.preDist s * ((p s).bind id) s' *
          σ_post.run h_ws.weakTau_post.witness_fuel s' s_last from by
    apply tsum_congr; intro s'; rw [ENNReal.tsum_mul_right]]
  rw [ENNReal.tsum_comm]
  apply tsum_congr; intro s
  rw [show (∑' s' : State,
        h_ws.preDist s * ((p s).bind id) s' *
          σ_post.run h_ws.weakTau_post.witness_fuel s' s_last)
      = h_ws.preDist s * ∑' s' : State,
        ((p s).bind id) s' *
          σ_post.run h_ws.weakTau_post.witness_fuel s' s_last from by
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr; intro s'; ring]
  apply congrArg
  simp only [hH_def]
  apply tsum_congr; intro s'
  rw [PMF.bind_apply]
  rfl

/-- **Per-iteration endState-marginal identity for `oneIterTransitionProb`.**
Marginalising `oneIterTransitionProb sys pe' e_w_prev l_last e_prev e_iter_start`
over all `e_iter_start` whose `trans` terminates and whose `endState` equals
`s_last` recovers the one-step kernel `pe'.kernel e_w_prev (l_last, s_last)`.

In symbols (with terminating `e_w_prev` and `e_prev`):
  ∑' e_iter_start, (if e_iter_start.trans.Terminates then
                      if e_iter_start.endState = s_last then
                        oneIterTransitionProb ... else 0
                    else 0)
    = pe'.kernel e_w_prev (l_last, s_last).

The hypotheses `h_ewp`/`h_ep` are needed because `oneIterTransitionProb`'s
outer guards make the LHS identically 0 when either prefix doesn't terminate,
while the kernel `pe'.kernel e_w_prev (l_last, s_last)` is well-defined for
any prefix and can be nonzero.

Status: deferred — case-split on `sys.internal l_last`. In the internal case
the inner `chainProb` factor sums (over chains ending at `s_last`) to
`(h_wt.witness.run witness_fuel s_pre) s_last`, which equals `μ s_last` via
`weakTau.witness_run` and `(PMF.pure s).bind f = f s`. The external case is
analogous via `weakStep.weakTau_pre.witness_run` and a chain-decomposition
marginal. -/
private lemma oneIterTransitionProb_endState_marginal
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_prev : AlterSeq State Label) (h_ewp : e_w_prev.trans.Terminates)
    (l_last : Label)
    (e_prev : AlterSeq State Label) (h_ep : e_prev.trans.Terminates)
    (s_last : State)
    (h_match : e_prev.endState h_ep = e_w_prev.endState h_ewp) :
    (∑' e_iter_start : AlterSeq State Label,
      (open Classical in
        if h : e_iter_start.trans.Terminates then
          if e_iter_start.endState h = s_last then
            oneIterTransitionProb sys pe' e_w_prev l_last e_prev e_iter_start
          else 0
        else 0)) =
      pe'.kernel e_w_prev (l_last, s_last) := by
  classical
  -- Case-split on whether `l_last` is internal or external.
  by_cases h_int : sys.internal l_last
  · -- INTERNAL CASE.
    -- With `h_match : e_prev.endState h_ep = e_w_prev.endState h_ewp`, we proceed
    -- by bijection `chain ↔ e_iter_start := ⟨e_prev.init, e_prev.trans.append
    -- (Seq.ofList chain)⟩` and apply the helpers
    -- `oneIterTransitionProb_internal_at_fromChain` and
    -- `chainProb_witness_endState_marginal`.
    set s_pre : State := e_w_prev.endState h_ewp with hs_pre_def
    -- STEP A: Replace the e_iter_start sum by a chain sum using the forward map.
    -- Forward map: chain ↦ ⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩.
    -- This map is injective and covers the support of the summand.
    let forward : List (Label × State) → AlterSeq State Label :=
      fun chain => ⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩
    -- Summand as a function of e_iter_start.
    let F : AlterSeq State Label → ENNReal := fun e_iter_start =>
      (open Classical in
        if h : e_iter_start.trans.Terminates then
          if e_iter_start.endState h = s_last then
            oneIterTransitionProb sys pe' e_w_prev l_last e_prev e_iter_start
          else 0
        else 0)
    -- Show that for e_iter_start not in the image of `forward`, F(e_iter_start) = 0.
    -- More precisely, if e_iter_start.init ≠ e_prev.init or e_prev's trans-list
    -- is not a prefix of e_iter_start's, then oneIterTransitionProb = 0.
    -- The summand inside oneIterTransitionProb's body uses `dif_pos h_prefix_cond`,
    -- and `dif_neg` gives 0.
    -- We bound this via the rewrite `f x = F(forward(chain)) for chain ∈ support_g`.
    -- We define g : List (Label × State) → ENNReal as F ∘ forward.
    set G : List (Label × State) → ENNReal := fun chain => F (forward chain) with hG_def
    -- Apply tsum_eq_tsum_of_ne_zero_bij:
    --   ∑' e_iter_start, F e_iter_start = ∑' chain, G chain.
    have h_forward_inj : Function.Injective forward := by
      intro c₁ c₂ h_eq
      -- e_prev.init = e_prev.init trivially, so we get
      -- e_prev.trans.append (Seq.ofList c₁) = e_prev.trans.append (Seq.ofList c₂)
      have h_trans : e_prev.trans.append (Seq.ofList c₁)
          = e_prev.trans.append (Seq.ofList c₂) := by
        have := h_eq
        change (⟨e_prev.init, e_prev.trans.append (Seq.ofList c₁)⟩ : AlterSeq State Label) =
              ⟨e_prev.init, e_prev.trans.append (Seq.ofList c₂)⟩ at this
        exact (AlterSeq.mk.injEq _ _ _ _).mp this |>.2
      -- Take .toList of both sides at a common Terminates witness.
      have h_term1 : (e_prev.trans.append (Seq.ofList c₁)).Terminates :=
        terminates_append_of_terminates h_ep (Seq.terminates_ofList _)
      have h_term2 : (e_prev.trans.append (Seq.ofList c₂)).Terminates := by
        rw [← h_trans]; exact h_term1
      have h_list_eq :
          (e_prev.trans.append (Seq.ofList c₁)).toList h_term1
            = (e_prev.trans.append (Seq.ofList c₂)).toList h_term2 := by
        congr 1
      rw [Seq.toList_append e_prev.trans (Seq.ofList c₁) h_ep (Seq.terminates_ofList _),
        Seq.toList_append e_prev.trans (Seq.ofList c₂) h_ep (Seq.terminates_ofList _)] at h_list_eq
      have h_chain_lists : (Seq.ofList c₁).toList (Seq.terminates_ofList _)
          = (Seq.ofList c₂).toList (Seq.terminates_ofList _) :=
        List.append_cancel_left h_list_eq
      rw [Seq.toList_ofList c₁, Seq.toList_ofList c₂] at h_chain_lists
      exact h_chain_lists
    -- Show: support F ⊆ range forward.
    have h_support_subset : Function.support F ⊆ Set.range forward := by
      intro e_iter_start h_F_ne
      -- h_F_ne : F e_iter_start ≠ 0, i.e., the if-then-else is non-zero.
      -- So e_iter_start.trans.Terminates and endState = s_last and oneIter ≠ 0.
      change F e_iter_start ≠ 0 at h_F_ne
      simp only [F] at h_F_ne
      by_cases h_t : e_iter_start.trans.Terminates
      swap
      · exact absurd (by simp [dif_neg h_t]) h_F_ne
      by_cases h_es : e_iter_start.endState h_t = s_last
      swap
      · exact absurd (by simp [dif_pos h_t, if_neg h_es]) h_F_ne
      rw [dif_pos h_t, if_pos h_es] at h_F_ne
      -- h_F_ne : oneIterTransitionProb sys pe' e_w_prev l_last e_prev e_iter_start ≠ 0.
      -- Unfold to extract the prefix condition.
      unfold oneIterTransitionProb at h_F_ne
      rw [dif_pos h_ewp, dif_pos h_ep, dif_pos h_t] at h_F_ne
      by_cases h_prefix : e_prev.init = e_iter_start.init ∧
          (e_iter_start.trans.toList h_t).take (e_prev.trans.toList h_ep).length
            = e_prev.trans.toList h_ep
      swap
      · rw [dif_neg h_prefix] at h_F_ne; exact absurd rfl h_F_ne
      -- Now extract chain and show forward chain = e_iter_start.
      obtain ⟨h_init_eq, h_take_eq⟩ := h_prefix
      let chain : List (Label × State) :=
        (e_iter_start.trans.toList h_t).drop (e_prev.trans.toList h_ep).length
      refine ⟨chain, ?_⟩
      -- Show forward chain = e_iter_start.
      -- forward chain = ⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩
      -- e_iter_start = ⟨e_iter_start.init, e_iter_start.trans⟩
      -- e_prev.init = e_iter_start.init via h_init_eq.
      -- e_prev.trans.append (Seq.ofList chain) = e_iter_start.trans:
      --   Take toList of both: e_prev.toList ++ chain.toList
      --     = take ++ drop = e_iter_start.toList (via h_take_eq).
      have h_append_term : (e_prev.trans.append (Seq.ofList chain)).Terminates :=
        terminates_append_of_terminates h_ep (Seq.terminates_ofList _)
      -- Show .toList equality, then use ofList_toList for Seq equality.
      have h_toList_app :
          (e_prev.trans.append (Seq.ofList chain)).toList h_append_term
            = e_iter_start.trans.toList h_t := by
        rw [Seq.toList_append e_prev.trans (Seq.ofList chain) h_ep
              (Seq.terminates_ofList _)]
        rw [Seq.toList_ofList chain]
        -- e_prev.toList ++ chain = take ++ drop = full list.
        change e_prev.trans.toList h_ep ++
            (e_iter_start.trans.toList h_t).drop (e_prev.trans.toList h_ep).length
              = e_iter_start.trans.toList h_t
        calc e_prev.trans.toList h_ep ++
              (e_iter_start.trans.toList h_t).drop (e_prev.trans.toList h_ep).length
            = (e_iter_start.trans.toList h_t).take (e_prev.trans.toList h_ep).length ++
                (e_iter_start.trans.toList h_t).drop (e_prev.trans.toList h_ep).length := by
              rw [h_take_eq]
          _ = e_iter_start.trans.toList h_t :=
              List.take_append_drop (e_prev.trans.toList h_ep).length
                (e_iter_start.trans.toList h_t)
      -- From .toList equality at terminates witnesses, get Seq equality via ofList_toList.
      have h_seq_eq : e_prev.trans.append (Seq.ofList chain) = e_iter_start.trans := by
        have h1 := Seq.ofList_toList (e_prev.trans.append (Seq.ofList chain)) h_append_term
        have h2 := Seq.ofList_toList e_iter_start.trans h_t
        rw [h_toList_app] at h1
        exact h1.symm.trans h2
      -- Combine.
      change forward chain = e_iter_start
      simp only [forward]
      obtain ⟨ei_init, ei_trans⟩ := e_iter_start
      simp only at h_init_eq h_seq_eq
      subst h_init_eq
      rw [h_seq_eq]
    -- Apply tsum_eq_tsum_of_ne_zero_bij.
    have h_tsum_eq :
        (∑' e_iter_start : AlterSeq State Label, F e_iter_start)
          = ∑' chain : List (Label × State), G chain := by
      -- We need an injection from support G to AlterSeq with the right properties.
      refine tsum_eq_tsum_of_ne_zero_bij (i := fun c => forward c.val) ?_ ?_ ?_
      · -- Injectivity
        intro a b h_eq
        exact Subtype.ext (h_forward_inj h_eq)
      · -- support F ⊆ range
        intro e_iter_start h_supp
        obtain ⟨chain, h_fc⟩ := h_support_subset h_supp
        refine ⟨⟨chain, ?_⟩, h_fc⟩
        -- G chain ≠ 0 because G chain = F (forward chain) = F e_iter_start ≠ 0.
        change F (forward chain) ≠ 0
        rw [h_fc]
        exact h_supp
      · -- f (i x) = g x.
        intro ⟨c, _⟩
        rfl
    -- Now: LHS = ∑' chain, G chain.
    -- Goal: (∑' e_iter_start, F e_iter_start) = pe'.kernel e_w_prev (l_last, s_last).
    change (∑' e_iter_start, F e_iter_start) = pe'.kernel e_w_prev (l_last, s_last)
    rw [h_tsum_eq]
    -- STEP B: Simplify G chain = F (forward chain) using endState_append_ofList_eq
    -- and oneIterTransitionProb_internal_at_fromChain. Apply h_match to substitute
    -- e_prev.endState h_ep = s_pre.
    have h_forward_term : ∀ chain : List (Label × State),
        (forward chain).trans.Terminates := fun chain =>
      terminates_append_of_terminates h_ep (Seq.terminates_ofList _)
    have h_G_eq : ∀ chain : List (Label × State),
        G chain = (open Classical in
          if (chain.getLast?.map Prod.snd).getD s_pre = s_last then
            ∑' μ : PMF State,
              pe'.scheduler.next e_w_prev (some (l_last, μ)) *
              (open Classical in
                if h_supp : some (l_last, μ) ∈
                    (pe'.scheduler.next e_w_prev).support then
                  have h_sw : sys^w.step (e_w_prev.endState h_ewp) l_last μ :=
                    pe'.scheduler.valid e_w_prev (Nat.find h_ewp)
                      (e_w_prev.endState h_ewp)
                      (Nat.find_spec h_ewp)
                      (AlterSeq.stateAt_find_eq_endState e_w_prev h_ewp)
                      l_last μ h_supp
                  have h_wt : weakTau sys (PMF.pure (e_w_prev.endState h_ewp)) μ := by
                    rcases h_sw with ⟨_, h⟩ | ⟨h_ext, _⟩
                    · exact h
                    · exact absurd h_int h_ext
                  chainProb h_wt.witness ⟨e_w_prev.endState h_ewp, Seq.nil⟩ chain
                else 0)
          else 0) := by
      intro chain
      change F (forward chain) = _
      simp only [F]
      rw [dif_pos (h_forward_term chain)]
      -- Replace endState (forward chain) by
      -- (chain.getLast?.map Prod.snd).getD (e_prev.endState h_ep).
      have h_es := endState_append_ofList_eq e_prev h_ep chain (h_forward_term chain)
      -- h_es: endState (forward chain) = (chain.getLast?.map Prod.snd).getD (e_prev.endState h_ep)
      -- but forward chain is defined as ⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩.
      change (if (⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩ :
                    AlterSeq State Label).endState (h_forward_term chain) = s_last then
                  oneIterTransitionProb sys pe' e_w_prev l_last e_prev (forward chain)
              else 0) = _
      rw [h_es]
      -- Use h_match to rewrite e_prev.endState h_ep = s_pre.
      rw [h_match]
      by_cases h_es_match : (chain.getLast?.map Prod.snd).getD s_pre = s_last
      · rw [if_pos h_es_match, if_pos h_es_match]
        -- Now apply oneIterTransitionProb_internal_at_fromChain to substitute.
        change oneIterTransitionProb sys pe' e_w_prev l_last e_prev
            ⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩ = _
        exact oneIterTransitionProb_internal_at_fromChain sys pe' e_w_prev h_ewp
          l_last h_int e_prev h_ep chain
      · rw [if_neg h_es_match, if_neg h_es_match]
    rw [tsum_congr h_G_eq]
    -- STEP C: Now goal is
    --   (∑' chain, if endState_match then ∑' μ, scheduler.next * (if h_supp then chainProb else 0)
    --              else 0)
    --   = pe'.kernel e_w_prev (l_last, s_last).
    -- Pull out the if-then-else into the inner μ-sum via if/mul distribution.
    have h_distrib : ∀ chain : List (Label × State),
        (open Classical in
          if (chain.getLast?.map Prod.snd).getD s_pre = s_last then
            ∑' μ : PMF State,
              pe'.scheduler.next e_w_prev (some (l_last, μ)) *
              (open Classical in
                if h_supp : some (l_last, μ) ∈
                    (pe'.scheduler.next e_w_prev).support then
                  have h_sw : sys^w.step (e_w_prev.endState h_ewp) l_last μ :=
                    pe'.scheduler.valid e_w_prev (Nat.find h_ewp)
                      (e_w_prev.endState h_ewp)
                      (Nat.find_spec h_ewp)
                      (AlterSeq.stateAt_find_eq_endState e_w_prev h_ewp)
                      l_last μ h_supp
                  have h_wt : weakTau sys (PMF.pure (e_w_prev.endState h_ewp)) μ := by
                    rcases h_sw with ⟨_, h⟩ | ⟨h_ext, _⟩
                    · exact h
                    · exact absurd h_int h_ext
                  chainProb h_wt.witness ⟨e_w_prev.endState h_ewp, Seq.nil⟩ chain
                else 0)
          else 0)
        = ∑' μ : PMF State,
            pe'.scheduler.next e_w_prev (some (l_last, μ)) *
            (open Classical in
              if h_supp : some (l_last, μ) ∈
                  (pe'.scheduler.next e_w_prev).support then
                have h_sw : sys^w.step (e_w_prev.endState h_ewp) l_last μ :=
                  pe'.scheduler.valid e_w_prev (Nat.find h_ewp)
                    (e_w_prev.endState h_ewp)
                    (Nat.find_spec h_ewp)
                    (AlterSeq.stateAt_find_eq_endState e_w_prev h_ewp)
                    l_last μ h_supp
                have h_wt : weakTau sys (PMF.pure (e_w_prev.endState h_ewp)) μ := by
                  rcases h_sw with ⟨_, h⟩ | ⟨h_ext, _⟩
                  · exact h
                  · exact absurd h_int h_ext
                (if (chain.getLast?.map Prod.snd).getD s_pre = s_last then
                  chainProb h_wt.witness ⟨e_w_prev.endState h_ewp, Seq.nil⟩ chain
                else 0)
              else 0) := by
      intro chain
      classical
      by_cases h_match2 : (chain.getLast?.map Prod.snd).getD s_pre = s_last
      · rw [if_pos h_match2]
        congr 1; funext μ; congr 1
        by_cases h_supp : some (l_last, μ) ∈ (pe'.scheduler.next e_w_prev).support
        · rw [dif_pos h_supp, dif_pos h_supp, if_pos h_match2]
        · rw [dif_neg h_supp, dif_neg h_supp]
      · rw [if_neg h_match2]
        symm
        -- All μ-summands are zero: inside dif, if h_match2 is false the value is 0.
        rw [ENNReal.tsum_eq_zero]
        intro μ
        by_cases h_supp : some (l_last, μ) ∈ (pe'.scheduler.next e_w_prev).support
        · rw [dif_pos h_supp, if_neg h_match2, mul_zero]
        · rw [dif_neg h_supp, mul_zero]
    rw [tsum_congr h_distrib]
    -- STEP D: Apply Fubini (tsum_comm) to swap chain and μ.
    rw [ENNReal.tsum_comm]
    -- Now goal: ∑' μ, ∑' chain, ... = pe'.kernel.
    -- Pull scheduler.next outside the chain-sum via tsum_mul_left.
    have h_per_mu : ∀ μ : PMF State,
        (∑' chain : List (Label × State),
          pe'.scheduler.next e_w_prev (some (l_last, μ)) *
          (open Classical in
            if h_supp : some (l_last, μ) ∈
                (pe'.scheduler.next e_w_prev).support then
              have h_sw : sys^w.step (e_w_prev.endState h_ewp) l_last μ :=
                pe'.scheduler.valid e_w_prev (Nat.find h_ewp)
                  (e_w_prev.endState h_ewp)
                  (Nat.find_spec h_ewp)
                  (AlterSeq.stateAt_find_eq_endState e_w_prev h_ewp)
                  l_last μ h_supp
              have h_wt : weakTau sys (PMF.pure (e_w_prev.endState h_ewp)) μ := by
                rcases h_sw with ⟨_, h⟩ | ⟨h_ext, _⟩
                · exact h
                · exact absurd h_int h_ext
              (if (chain.getLast?.map Prod.snd).getD s_pre = s_last then
                chainProb h_wt.witness ⟨e_w_prev.endState h_ewp, Seq.nil⟩ chain
              else 0)
            else 0))
        = pe'.scheduler.next e_w_prev (some (l_last, μ)) * μ s_last := by
      intro μ
      rw [ENNReal.tsum_mul_left]
      -- Inner sum: case on h_supp.
      by_cases h_supp : some (l_last, μ) ∈ (pe'.scheduler.next e_w_prev).support
      · -- h_supp holds: extract h_wt and apply chainProb_witness_endState_marginal.
        have h_sw : sys^w.step (e_w_prev.endState h_ewp) l_last μ :=
          pe'.scheduler.valid e_w_prev (Nat.find h_ewp)
            (e_w_prev.endState h_ewp)
            (Nat.find_spec h_ewp)
            (AlterSeq.stateAt_find_eq_endState e_w_prev h_ewp)
            l_last μ h_supp
        have h_wt : weakTau sys (PMF.pure (e_w_prev.endState h_ewp)) μ := by
          rcases h_sw with ⟨_, h⟩ | ⟨h_ext, _⟩
          · exact h
          · exact absurd h_int h_ext
        congr 1
        rw [show (∑' chain : List (Label × State),
            (open Classical in
              if h_supp' : some (l_last, μ) ∈
                  (pe'.scheduler.next e_w_prev).support then
                have h_sw' : sys^w.step (e_w_prev.endState h_ewp) l_last μ :=
                  pe'.scheduler.valid e_w_prev (Nat.find h_ewp)
                    (e_w_prev.endState h_ewp)
                    (Nat.find_spec h_ewp)
                    (AlterSeq.stateAt_find_eq_endState e_w_prev h_ewp)
                    l_last μ h_supp'
                have h_wt' : weakTau sys (PMF.pure (e_w_prev.endState h_ewp)) μ := by
                  rcases h_sw' with ⟨_, h⟩ | ⟨h_ext, _⟩
                  · exact h
                  · exact absurd h_int h_ext
                (if (chain.getLast?.map Prod.snd).getD s_pre = s_last then
                  chainProb h_wt'.witness ⟨e_w_prev.endState h_ewp, Seq.nil⟩ chain
                else 0)
              else 0))
          = (∑' chain : List (Label × State),
              if (chain.getLast?.map Prod.snd).getD s_pre = s_last then
                chainProb h_wt.witness ⟨e_w_prev.endState h_ewp, Seq.nil⟩ chain
              else 0) from by
          apply tsum_congr; intro chain
          rw [dif_pos h_supp]]
        -- Now apply chainProb_witness_endState_marginal with the right substitution.
        -- The marginal lemma uses s_pre = e_w_prev.endState h_ewp (which IS our s_pre).
        exact chainProb_witness_endState_marginal h_wt s_last
      · -- h_supp false: scheduler.next = 0, so both sides are 0 by zero_mul.
        have h_zero : pe'.scheduler.next e_w_prev (some (l_last, μ)) = 0 := by
          by_contra h_ne
          exact h_supp h_ne
        rw [h_zero, zero_mul, zero_mul]
    rw [tsum_congr h_per_mu]
    -- STEP F: This is exactly pe'.kernel e_w_prev (l_last, s_last).
    unfold ProbabilisticExecution.kernel
    rfl
  · -- EXTERNAL CASE: mirrors the internal case but with a chain decomposition
    -- inside the inner factor. The chain ↔ e_iter_start bijection (Steps A-D)
    -- is identical; only the per-μ inner identity changes.
    set s_pre : State := e_w_prev.endState h_ewp with hs_pre_def
    -- STEP A (identical to internal): bijection `chain ↔ e_iter_start`.
    let forward : List (Label × State) → AlterSeq State Label :=
      fun chain => ⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩
    let F : AlterSeq State Label → ENNReal := fun e_iter_start =>
      (open Classical in
        if h : e_iter_start.trans.Terminates then
          if e_iter_start.endState h = s_last then
            oneIterTransitionProb sys pe' e_w_prev l_last e_prev e_iter_start
          else 0
        else 0)
    set G : List (Label × State) → ENNReal := fun chain => F (forward chain) with hG_def
    have h_forward_inj : Function.Injective forward := by
      intro c₁ c₂ h_eq
      have h_trans : e_prev.trans.append (Seq.ofList c₁)
          = e_prev.trans.append (Seq.ofList c₂) := by
        have := h_eq
        change (⟨e_prev.init, e_prev.trans.append (Seq.ofList c₁)⟩ : AlterSeq State Label) =
              ⟨e_prev.init, e_prev.trans.append (Seq.ofList c₂)⟩ at this
        exact (AlterSeq.mk.injEq _ _ _ _).mp this |>.2
      have h_term1 : (e_prev.trans.append (Seq.ofList c₁)).Terminates :=
        terminates_append_of_terminates h_ep (Seq.terminates_ofList _)
      have h_term2 : (e_prev.trans.append (Seq.ofList c₂)).Terminates := by
        rw [← h_trans]; exact h_term1
      have h_list_eq :
          (e_prev.trans.append (Seq.ofList c₁)).toList h_term1
            = (e_prev.trans.append (Seq.ofList c₂)).toList h_term2 := by
        congr 1
      rw [Seq.toList_append e_prev.trans (Seq.ofList c₁) h_ep (Seq.terminates_ofList _),
        Seq.toList_append e_prev.trans (Seq.ofList c₂) h_ep (Seq.terminates_ofList _)] at h_list_eq
      have h_chain_lists : (Seq.ofList c₁).toList (Seq.terminates_ofList _)
          = (Seq.ofList c₂).toList (Seq.terminates_ofList _) :=
        List.append_cancel_left h_list_eq
      rw [Seq.toList_ofList c₁, Seq.toList_ofList c₂] at h_chain_lists
      exact h_chain_lists
    have h_support_subset : Function.support F ⊆ Set.range forward := by
      intro e_iter_start h_F_ne
      change F e_iter_start ≠ 0 at h_F_ne
      simp only [F] at h_F_ne
      by_cases h_t : e_iter_start.trans.Terminates
      swap
      · exact absurd (by simp [dif_neg h_t]) h_F_ne
      by_cases h_es : e_iter_start.endState h_t = s_last
      swap
      · exact absurd (by simp [dif_pos h_t, if_neg h_es]) h_F_ne
      rw [dif_pos h_t, if_pos h_es] at h_F_ne
      unfold oneIterTransitionProb at h_F_ne
      rw [dif_pos h_ewp, dif_pos h_ep, dif_pos h_t] at h_F_ne
      by_cases h_prefix : e_prev.init = e_iter_start.init ∧
          (e_iter_start.trans.toList h_t).take (e_prev.trans.toList h_ep).length
            = e_prev.trans.toList h_ep
      swap
      · rw [dif_neg h_prefix] at h_F_ne; exact absurd rfl h_F_ne
      obtain ⟨h_init_eq, h_take_eq⟩ := h_prefix
      let chain : List (Label × State) :=
        (e_iter_start.trans.toList h_t).drop (e_prev.trans.toList h_ep).length
      refine ⟨chain, ?_⟩
      have h_append_term : (e_prev.trans.append (Seq.ofList chain)).Terminates :=
        terminates_append_of_terminates h_ep (Seq.terminates_ofList _)
      have h_toList_app :
          (e_prev.trans.append (Seq.ofList chain)).toList h_append_term
            = e_iter_start.trans.toList h_t := by
        rw [Seq.toList_append e_prev.trans (Seq.ofList chain) h_ep
              (Seq.terminates_ofList _)]
        rw [Seq.toList_ofList chain]
        change e_prev.trans.toList h_ep ++
            (e_iter_start.trans.toList h_t).drop (e_prev.trans.toList h_ep).length
              = e_iter_start.trans.toList h_t
        calc e_prev.trans.toList h_ep ++
              (e_iter_start.trans.toList h_t).drop (e_prev.trans.toList h_ep).length
            = (e_iter_start.trans.toList h_t).take (e_prev.trans.toList h_ep).length ++
                (e_iter_start.trans.toList h_t).drop (e_prev.trans.toList h_ep).length := by
              rw [h_take_eq]
          _ = e_iter_start.trans.toList h_t :=
              List.take_append_drop (e_prev.trans.toList h_ep).length
                (e_iter_start.trans.toList h_t)
      have h_seq_eq : e_prev.trans.append (Seq.ofList chain) = e_iter_start.trans := by
        have h1 := Seq.ofList_toList (e_prev.trans.append (Seq.ofList chain)) h_append_term
        have h2 := Seq.ofList_toList e_iter_start.trans h_t
        rw [h_toList_app] at h1
        exact h1.symm.trans h2
      change forward chain = e_iter_start
      simp only [forward]
      obtain ⟨ei_init, ei_trans⟩ := e_iter_start
      simp only at h_init_eq h_seq_eq
      subst h_init_eq
      rw [h_seq_eq]
    have h_tsum_eq :
        (∑' e_iter_start : AlterSeq State Label, F e_iter_start)
          = ∑' chain : List (Label × State), G chain := by
      refine tsum_eq_tsum_of_ne_zero_bij (i := fun c => forward c.val) ?_ ?_ ?_
      · intro a b h_eq
        exact Subtype.ext (h_forward_inj h_eq)
      · intro e_iter_start h_supp
        obtain ⟨chain, h_fc⟩ := h_support_subset h_supp
        refine ⟨⟨chain, ?_⟩, h_fc⟩
        change F (forward chain) ≠ 0
        rw [h_fc]
        exact h_supp
      · intro ⟨c, _⟩
        rfl
    change (∑' e_iter_start, F e_iter_start) = pe'.kernel e_w_prev (l_last, s_last)
    rw [h_tsum_eq]
    -- STEP B: Simplify G chain = F (forward chain) using endState_append_ofList_eq
    -- and oneIterTransitionProb_external_at_fromChain.
    have h_forward_term : ∀ chain : List (Label × State),
        (forward chain).trans.Terminates := fun chain =>
      terminates_append_of_terminates h_ep (Seq.terminates_ofList _)
    have h_G_eq : ∀ chain : List (Label × State),
        G chain = (open Classical in
          if (chain.getLast?.map Prod.snd).getD s_pre = s_last then
            ∑' μ : PMF State,
              pe'.scheduler.next e_w_prev (some (l_last, μ)) *
              (open Classical in
                if h_supp : some (l_last, μ) ∈
                    (pe'.scheduler.next e_w_prev).support then
                  have h_sw : sys^w.step (e_w_prev.endState h_ewp) l_last μ :=
                    pe'.scheduler.valid e_w_prev (Nat.find h_ewp)
                      (e_w_prev.endState h_ewp)
                      (Nat.find_spec h_ewp)
                      (AlterSeq.stateAt_find_eq_endState e_w_prev h_ewp)
                      l_last μ h_supp
                  have h_ws : weakStep sys (PMF.pure (e_w_prev.endState h_ewp))
                      l_last μ := by
                    rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
                    · exact absurd h_int' h_int
                    · exact h
                  (match splitAtLabel l_last chain with
                    | (_, none) => (0 : ENNReal)
                    | (chain_pre, some (s_mid, chain_post)) =>
                      let s_mid_pre : State :=
                        (chain_pre.getLast?.map Prod.snd).getD (e_w_prev.endState h_ewp)
                      chainProb h_ws.weakTau_pre.witness
                          ⟨e_w_prev.endState h_ewp, Seq.nil⟩ chain_pre *
                        (∑' μ_l : PMF State,
                          h_ws.hyperStep_mid.kernel s_mid_pre μ_l * μ_l s_mid) *
                        chainProb h_ws.weakTau_post.witness
                          ⟨s_mid, Seq.nil⟩ chain_post)
                else 0)
          else 0) := by
      intro chain
      change F (forward chain) = _
      simp only [F]
      rw [dif_pos (h_forward_term chain)]
      have h_es := endState_append_ofList_eq e_prev h_ep chain (h_forward_term chain)
      change (if (⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩ :
                    AlterSeq State Label).endState (h_forward_term chain) = s_last then
                  oneIterTransitionProb sys pe' e_w_prev l_last e_prev (forward chain)
              else 0) = _
      rw [h_es]
      rw [h_match]
      by_cases h_es_match : (chain.getLast?.map Prod.snd).getD s_pre = s_last
      · rw [if_pos h_es_match, if_pos h_es_match]
        change oneIterTransitionProb sys pe' e_w_prev l_last e_prev
            ⟨e_prev.init, e_prev.trans.append (Seq.ofList chain)⟩ = _
        exact oneIterTransitionProb_external_at_fromChain sys pe' e_w_prev h_ewp
          l_last h_int e_prev h_ep chain
      · rw [if_neg h_es_match, if_neg h_es_match]
    rw [tsum_congr h_G_eq]
    -- STEP C: pull `if (endState = s_last)` into the inner μ-sum (mirror of internal).
    have h_distrib : ∀ chain : List (Label × State),
        (open Classical in
          if (chain.getLast?.map Prod.snd).getD s_pre = s_last then
            ∑' μ : PMF State,
              pe'.scheduler.next e_w_prev (some (l_last, μ)) *
              (open Classical in
                if h_supp : some (l_last, μ) ∈
                    (pe'.scheduler.next e_w_prev).support then
                  have h_sw : sys^w.step (e_w_prev.endState h_ewp) l_last μ :=
                    pe'.scheduler.valid e_w_prev (Nat.find h_ewp)
                      (e_w_prev.endState h_ewp)
                      (Nat.find_spec h_ewp)
                      (AlterSeq.stateAt_find_eq_endState e_w_prev h_ewp)
                      l_last μ h_supp
                  have h_ws : weakStep sys (PMF.pure (e_w_prev.endState h_ewp))
                      l_last μ := by
                    rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
                    · exact absurd h_int' h_int
                    · exact h
                  (match splitAtLabel l_last chain with
                    | (_, none) => (0 : ENNReal)
                    | (chain_pre, some (s_mid, chain_post)) =>
                      let s_mid_pre : State :=
                        (chain_pre.getLast?.map Prod.snd).getD (e_w_prev.endState h_ewp)
                      chainProb h_ws.weakTau_pre.witness
                          ⟨e_w_prev.endState h_ewp, Seq.nil⟩ chain_pre *
                        (∑' μ_l : PMF State,
                          h_ws.hyperStep_mid.kernel s_mid_pre μ_l * μ_l s_mid) *
                        chainProb h_ws.weakTau_post.witness
                          ⟨s_mid, Seq.nil⟩ chain_post)
                else 0)
          else 0)
        = ∑' μ : PMF State,
            pe'.scheduler.next e_w_prev (some (l_last, μ)) *
            (open Classical in
              if h_supp : some (l_last, μ) ∈
                  (pe'.scheduler.next e_w_prev).support then
                have h_sw : sys^w.step (e_w_prev.endState h_ewp) l_last μ :=
                  pe'.scheduler.valid e_w_prev (Nat.find h_ewp)
                    (e_w_prev.endState h_ewp)
                    (Nat.find_spec h_ewp)
                    (AlterSeq.stateAt_find_eq_endState e_w_prev h_ewp)
                    l_last μ h_supp
                have h_ws : weakStep sys (PMF.pure (e_w_prev.endState h_ewp))
                    l_last μ := by
                  rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
                  · exact absurd h_int' h_int
                  · exact h
                (if (chain.getLast?.map Prod.snd).getD s_pre = s_last then
                  (match splitAtLabel l_last chain with
                    | (_, none) => (0 : ENNReal)
                    | (chain_pre, some (s_mid, chain_post)) =>
                      let s_mid_pre : State :=
                        (chain_pre.getLast?.map Prod.snd).getD (e_w_prev.endState h_ewp)
                      chainProb h_ws.weakTau_pre.witness
                          ⟨e_w_prev.endState h_ewp, Seq.nil⟩ chain_pre *
                        (∑' μ_l : PMF State,
                          h_ws.hyperStep_mid.kernel s_mid_pre μ_l * μ_l s_mid) *
                        chainProb h_ws.weakTau_post.witness
                          ⟨s_mid, Seq.nil⟩ chain_post)
                else 0)
              else 0) := by
      intro chain
      classical
      by_cases h_match2 : (chain.getLast?.map Prod.snd).getD s_pre = s_last
      · rw [if_pos h_match2]
        congr 1; funext μ; congr 1
        by_cases h_supp : some (l_last, μ) ∈ (pe'.scheduler.next e_w_prev).support
        · rw [dif_pos h_supp, dif_pos h_supp, if_pos h_match2]
        · rw [dif_neg h_supp, dif_neg h_supp]
      · rw [if_neg h_match2]
        symm
        rw [ENNReal.tsum_eq_zero]
        intro μ
        by_cases h_supp : some (l_last, μ) ∈ (pe'.scheduler.next e_w_prev).support
        · rw [dif_pos h_supp, if_neg h_match2, mul_zero]
        · rw [dif_neg h_supp, mul_zero]
    rw [tsum_congr h_distrib]
    -- STEP D: Fubini swap, then collapse via `weakStep_chain_marginal`.
    rw [ENNReal.tsum_comm]
    have h_per_mu : ∀ μ : PMF State,
        (∑' chain : List (Label × State),
          pe'.scheduler.next e_w_prev (some (l_last, μ)) *
          (open Classical in
            if h_supp : some (l_last, μ) ∈
                (pe'.scheduler.next e_w_prev).support then
              have h_sw : sys^w.step (e_w_prev.endState h_ewp) l_last μ :=
                pe'.scheduler.valid e_w_prev (Nat.find h_ewp)
                  (e_w_prev.endState h_ewp)
                  (Nat.find_spec h_ewp)
                  (AlterSeq.stateAt_find_eq_endState e_w_prev h_ewp)
                  l_last μ h_supp
              have h_ws : weakStep sys (PMF.pure (e_w_prev.endState h_ewp))
                  l_last μ := by
                rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
                · exact absurd h_int' h_int
                · exact h
              (if (chain.getLast?.map Prod.snd).getD s_pre = s_last then
                (match splitAtLabel l_last chain with
                  | (_, none) => (0 : ENNReal)
                  | (chain_pre, some (s_mid, chain_post)) =>
                    let s_mid_pre : State :=
                      (chain_pre.getLast?.map Prod.snd).getD (e_w_prev.endState h_ewp)
                    chainProb h_ws.weakTau_pre.witness
                        ⟨e_w_prev.endState h_ewp, Seq.nil⟩ chain_pre *
                      (∑' μ_l : PMF State,
                        h_ws.hyperStep_mid.kernel s_mid_pre μ_l * μ_l s_mid) *
                      chainProb h_ws.weakTau_post.witness
                        ⟨s_mid, Seq.nil⟩ chain_post)
              else 0)
            else 0))
        = pe'.scheduler.next e_w_prev (some (l_last, μ)) * μ s_last := by
      intro μ
      rw [ENNReal.tsum_mul_left]
      by_cases h_supp : some (l_last, μ) ∈ (pe'.scheduler.next e_w_prev).support
      · have h_sw : sys^w.step (e_w_prev.endState h_ewp) l_last μ :=
          pe'.scheduler.valid e_w_prev (Nat.find h_ewp)
            (e_w_prev.endState h_ewp)
            (Nat.find_spec h_ewp)
            (AlterSeq.stateAt_find_eq_endState e_w_prev h_ewp)
            l_last μ h_supp
        have h_ws : weakStep sys (PMF.pure (e_w_prev.endState h_ewp)) l_last μ := by
          rcases h_sw with ⟨h_int', _⟩ | ⟨_, h⟩
          · exact absurd h_int' h_int
          · exact h
        congr 1
        rw [show (∑' chain : List (Label × State),
            (open Classical in
              if h_supp' : some (l_last, μ) ∈
                  (pe'.scheduler.next e_w_prev).support then
                have h_sw' : sys^w.step (e_w_prev.endState h_ewp) l_last μ :=
                  pe'.scheduler.valid e_w_prev (Nat.find h_ewp)
                    (e_w_prev.endState h_ewp)
                    (Nat.find_spec h_ewp)
                    (AlterSeq.stateAt_find_eq_endState e_w_prev h_ewp)
                    l_last μ h_supp'
                have h_ws' : weakStep sys (PMF.pure (e_w_prev.endState h_ewp))
                    l_last μ := by
                  rcases h_sw' with ⟨h_int', _⟩ | ⟨_, h⟩
                  · exact absurd h_int' h_int
                  · exact h
                ((if (chain.getLast?.map Prod.snd).getD s_pre = s_last then
                  (match splitAtLabel l_last chain with
                    | (_, none) => (0 : ENNReal)
                    | (chain_pre, some (s_mid, chain_post)) =>
                      let s_mid_pre : State :=
                        (chain_pre.getLast?.map Prod.snd).getD (e_w_prev.endState h_ewp)
                      chainProb h_ws'.weakTau_pre.witness
                          ⟨e_w_prev.endState h_ewp, Seq.nil⟩ chain_pre *
                        (∑' μ_l : PMF State,
                          h_ws'.hyperStep_mid.kernel s_mid_pre μ_l * μ_l s_mid) *
                        chainProb h_ws'.weakTau_post.witness
                          ⟨s_mid, Seq.nil⟩ chain_post)
                else 0) : ENNReal)
              else 0))
          = (∑' chain : List (Label × State),
              ((if (chain.getLast?.map Prod.snd).getD s_pre = s_last then
                (match splitAtLabel l_last chain with
                  | (_, none) => (0 : ENNReal)
                  | (chain_pre, some (s_mid, chain_post)) =>
                    let s_mid_pre : State :=
                      (chain_pre.getLast?.map Prod.snd).getD (e_w_prev.endState h_ewp)
                    chainProb h_ws.weakTau_pre.witness
                        ⟨e_w_prev.endState h_ewp, Seq.nil⟩ chain_pre *
                      (∑' μ_l : PMF State,
                        h_ws.hyperStep_mid.kernel s_mid_pre μ_l * μ_l s_mid) *
                      chainProb h_ws.weakTau_post.witness
                        ⟨s_mid, Seq.nil⟩ chain_post)
              else 0) : ENNReal)) from by
          apply tsum_congr; intro chain
          rw [dif_pos h_supp]]
        exact weakStep_chain_marginal h_int h_ws s_last
      · have h_zero : pe'.scheduler.next e_w_prev (some (l_last, μ)) = 0 := by
          by_contra h_ne
          exact h_supp h_ne
        rw [h_zero, zero_mul, zero_mul]
    rw [tsum_congr h_per_mu]
    unfold ProbabilisticExecution.kernel
    rfl

/-- **Aux: unconditional marginal parametrised by the trans-list.** Strong
induction form of `reachProb_marginal_unconditional`. Induction on `L`. -/
private lemma reachProb_marginal_unconditional_aux
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (L : List (Label × State)) (s_init : State) :
    (∑' e_iter_start : AlterSeq State Label,
      reachProb sys pe' ⟨s_init, Seq.ofList L⟩ e_iter_start) =
      pe'.probOf ⟨s_init, Seq.ofList L⟩ (Seq.terminates_ofList L) := by
  classical
  induction L using List.reverseRecOn with
  | nil =>
    -- Base: Seq.ofList [] = Seq.nil, reachProb's base branch fires.
    have h_e_w_term : (⟨s_init, Seq.ofList []⟩ : AlterSeq State Label).trans.Terminates :=
      Seq.terminates_ofList []
    have h_toList :
        (⟨s_init, Seq.ofList []⟩ : AlterSeq State Label).trans.toList h_e_w_term = [] := by
      change (Seq.ofList []).toList h_e_w_term = []
      exact Seq.toList_ofList []
    -- Each summand reduces to the base if-form.
    have h_summand : ∀ e_iter_start : AlterSeq State Label,
        reachProb sys pe' ⟨s_init, Seq.ofList []⟩ e_iter_start =
          (if s_init = e_iter_start.init ∧ e_iter_start.trans = Seq.nil
           then pe'.initState s_init else 0) := by
      intro e_iter_start
      unfold reachProb
      rw [dif_pos h_e_w_term, h_toList, List.reverseRecOn_nil]
    rw [tsum_congr h_summand]
    rw [tsum_eq_single (⟨s_init, Seq.nil⟩ : AlterSeq State Label)]
    · have h_eq :
          (⟨s_init, Seq.nil⟩ : AlterSeq State Label).init = s_init ∧
            (⟨s_init, Seq.nil⟩ : AlterSeq State Label).trans = Seq.nil :=
        ⟨rfl, rfl⟩
      rw [if_pos h_eq]
      -- pe'.probOf ⟨s_init, Seq.ofList []⟩ = pe'.init s_init via the toList
      -- being [] and reverseRecOn_nil.
      unfold ProbabilisticExecution.probOf
      rw [h_toList, List.reverseRecOn_nil]
      rfl
    · intro c hc
      rw [if_neg]
      rintro ⟨h_init_eq, h_trans_nil⟩
      apply hc
      obtain ⟨c_init, c_trans⟩ := c
      simp only at h_init_eq h_trans_nil
      subst h_init_eq; subst h_trans_nil
      rfl
  | append_singleton previous_list last_step ih =>
    -- Step: Seq.ofList (previous_list ++ [last_step]) is a cons-end.
    -- Strategy: Fubini between e_iter_start and the inner reachProb tsum,
    -- then `oneIterTransitionProb_endState_marginal` collapses the
    -- e_iter_start marginal to `pe'.kernel`, then `probOf_append_singleton`
    -- assembles the final answer.
    -- Local abbreviation; not a `let` because we want this to be unfoldable.
    have h_e_w_term :
        (⟨s_init, Seq.ofList (previous_list ++ [last_step])⟩ :
          AlterSeq State Label).trans.Terminates := Seq.terminates_ofList _
    have h_e_w_prev_term :
        (⟨s_init, Seq.ofList previous_list⟩ : AlterSeq State Label).trans.Terminates :=
      Seq.terminates_ofList _
    have h_toList :
        (⟨s_init, Seq.ofList (previous_list ++ [last_step])⟩ :
          AlterSeq State Label).trans.toList h_e_w_term = previous_list ++ [last_step] := by
      change (Seq.ofList (previous_list ++ [last_step])).toList h_e_w_term
          = previous_list ++ [last_step]
      exact Seq.toList_ofList _
    have h_prev_toList :
        (⟨s_init, Seq.ofList previous_list⟩ :
          AlterSeq State Label).trans.toList h_e_w_prev_term = previous_list := by
      change (Seq.ofList previous_list).toList h_e_w_prev_term = previous_list
      exact Seq.toList_ofList _
    -- Rewrite each summand using the step branch of reachProb.
    have h_summand : ∀ e_iter_start : AlterSeq State Label,
        reachProb sys pe' ⟨s_init, Seq.ofList (previous_list ++ [last_step])⟩
            e_iter_start =
          (open Classical in
            if h_e'_term : e_iter_start.trans.Terminates then
              if e_iter_start.endState h_e'_term = last_step.2 then
                ∑' e_prev : AlterSeq State Label,
                  reachProb sys pe' ⟨s_init, Seq.ofList previous_list⟩ e_prev *
                    oneIterTransitionProb sys pe'
                      ⟨s_init, Seq.ofList previous_list⟩ last_step.1 e_prev e_iter_start
              else 0
            else 0) := by
      intro e_iter_start
      unfold reachProb
      rw [dif_pos h_e_w_term, h_toList, List.reverseRecOn_concat]
      -- The inner reverseRecOn(previous_list) equals reachProb on e_w_prev.
      -- Extract the dif/if guards explicitly.
      by_cases h_t : e_iter_start.trans.Terminates
      swap
      · simp [dif_neg h_t]
      by_cases h_e : e_iter_start.endState h_t = last_step.2
      swap
      · simp [dif_pos h_t, if_neg h_e]
      simp only [dif_pos h_t, if_pos h_e]
      apply tsum_congr; intro e_prev
      congr 1
      -- Goal: reverseRecOn previous_list (...) e_prev = reachProb ... e_prev.
      -- Rewrite the RHS using the def of reachProb on the previous_list prefix.
      conv_rhs => unfold reachProb
      rw [dif_pos h_e_w_prev_term, h_prev_toList]
    rw [tsum_congr h_summand]
    -- Fubini: pull the if-then-else into the inner sum and swap.
    -- First, rewrite each summand using `mul_ite`-style distribution to push
    -- the if-block into the tsum.
    have h_distrib_if : ∀ e_iter_start : AlterSeq State Label,
        (open Classical in
          if h_e'_term : e_iter_start.trans.Terminates then
            if e_iter_start.endState h_e'_term = last_step.2 then
              ∑' e_prev : AlterSeq State Label,
                reachProb sys pe' ⟨s_init, Seq.ofList previous_list⟩ e_prev *
                  oneIterTransitionProb sys pe'
                    ⟨s_init, Seq.ofList previous_list⟩ last_step.1 e_prev e_iter_start
            else 0
          else 0) =
        ∑' e_prev : AlterSeq State Label,
          reachProb sys pe' ⟨s_init, Seq.ofList previous_list⟩ e_prev *
            (open Classical in
              if h_e'_term : e_iter_start.trans.Terminates then
                if e_iter_start.endState h_e'_term = last_step.2 then
                  oneIterTransitionProb sys pe'
                    ⟨s_init, Seq.ofList previous_list⟩ last_step.1 e_prev e_iter_start
                else 0
              else 0) := by
      intro e_iter_start
      classical
      by_cases h_t : e_iter_start.trans.Terminates
      swap
      · simp [dif_neg h_t]
      by_cases h_e : e_iter_start.endState h_t = last_step.2
      swap
      · simp [dif_pos h_t, if_neg h_e]
      simp [dif_pos h_t, if_pos h_e]
    rw [tsum_congr h_distrib_if]
    -- Now we have ∑' e_iter_start, ∑' e_prev, reachProb * (if-block oneIter).
    -- Swap order via ENNReal.tsum_comm.
    rw [ENNReal.tsum_comm]
    -- Now: ∑' e_prev, ∑' e_iter_start, reachProb * (if-block oneIter)
    -- Pull reachProb (constant in e_iter_start) outside.
    have h_per_eprev : ∀ e_prev : AlterSeq State Label,
        (∑' e_iter_start : AlterSeq State Label,
          reachProb sys pe' ⟨s_init, Seq.ofList previous_list⟩ e_prev *
            (open Classical in
              if h_e'_term : e_iter_start.trans.Terminates then
                if e_iter_start.endState h_e'_term = last_step.2 then
                  oneIterTransitionProb sys pe'
                    ⟨s_init, Seq.ofList previous_list⟩ last_step.1 e_prev e_iter_start
                else 0
              else 0)) =
          reachProb sys pe' ⟨s_init, Seq.ofList previous_list⟩ e_prev *
            pe'.kernel ⟨s_init, Seq.ofList previous_list⟩ (last_step.1, last_step.2) := by
      intro e_prev
      rw [ENNReal.tsum_mul_left]
      -- Case split on whether e_prev terminates.
      by_cases h_ep : e_prev.trans.Terminates
      · -- Case-split on whether reachProb is zero: if zero, both sides collapse to 0.
        -- Otherwise, reachProb_invariant supplies the h_match hypothesis required
        -- by oneIterTransitionProb_endState_marginal.
        by_cases h_reach_zero :
            reachProb sys pe' ⟨s_init, Seq.ofList previous_list⟩ e_prev = 0
        · rw [h_reach_zero, zero_mul, zero_mul]
        · -- Extract h_match via reachProb_invariant; note the direction is reversed.
          obtain ⟨_, h_inv⟩ := reachProb_invariant
            (⟨s_init, Seq.ofList previous_list⟩ : AlterSeq State Label)
            e_prev h_ep h_reach_zero
          have h_match : e_prev.endState h_ep
              = (⟨s_init, Seq.ofList previous_list⟩ :
                  AlterSeq State Label).endState h_e_w_prev_term := h_inv.symm
          congr 1
          exact oneIterTransitionProb_endState_marginal sys pe'
            ⟨s_init, Seq.ofList previous_list⟩ h_e_w_prev_term last_step.1 e_prev h_ep
              last_step.2 h_match
      · -- When e_prev doesn't terminate, oneIterTransitionProb is 0 and
        -- reachProb e_w_prev e_prev is also 0 (because reachProb at the step
        -- branch requires the inner e' to terminate, and the base branch
        -- requires Seq.nil which terminates). So both sides are 0.
        have h_reach_zero :
            reachProb sys pe' ⟨s_init, Seq.ofList previous_list⟩ e_prev = 0 := by
          unfold reachProb
          rw [dif_pos h_e_w_prev_term]
          have h_pl_toList :
              (⟨s_init, Seq.ofList previous_list⟩ :
                AlterSeq State Label).trans.toList h_e_w_prev_term = previous_list := by
            change (Seq.ofList previous_list).toList h_e_w_prev_term = previous_list
            exact Seq.toList_ofList _
          rw [h_pl_toList]
          induction previous_list using List.reverseRecOn with
          | nil =>
            rw [List.reverseRecOn_nil]
            rw [if_neg]
            rintro ⟨_, h_nil⟩
            exact h_ep (h_nil ▸ Stream'.Seq.terminates_nil)
          | append_singleton _ _ _ =>
            rw [List.reverseRecOn_concat]
            rw [dif_neg h_ep]
        rw [h_reach_zero, zero_mul, zero_mul]
    rw [tsum_congr h_per_eprev]
    -- Now: ∑' e_prev, reachProb e_w_prev e_prev * pe'.kernel
    --    = pe'.kernel * ∑' e_prev, reachProb e_w_prev e_prev (by tsum_mul_right)
    --    = pe'.kernel * pe'.probOf e_w_prev (by IH on previous_list).
    rw [ENNReal.tsum_mul_right]
    -- Apply IH.
    rw [ih]
    -- Final step: pe'.probOf ⟨s_init, Seq.ofList previous_list⟩ *
    --   pe'.kernel ⟨s_init, Seq.ofList previous_list⟩ (last_step.1, last_step.2)
    --   = pe'.probOf ⟨s_init, Seq.ofList (previous_list ++ [last_step])⟩.
    -- Use probOf_append_singleton, accounting for `last_step = (last_step.1, last_step.2)`.
    have h_last_eq : last_step = (last_step.1, last_step.2) := by
      rcases last_step with ⟨a, b⟩; rfl
    -- Rewrite the kernel argument from (last_step.1, last_step.2) to last_step.
    rw [show pe'.kernel (⟨s_init, Seq.ofList previous_list⟩ : AlterSeq State Label)
            (last_step.1, last_step.2)
          = pe'.kernel (⟨s_init, Seq.ofList previous_list⟩ : AlterSeq State Label)
              last_step from by rw [← h_last_eq]]
    -- Rewrite Seq.ofList (previous_list ++ [last_step]) as the appended form.
    have h_seq_split :
        Seq.ofList (previous_list ++ [last_step])
          = (Seq.ofList previous_list).append
              (Seq.cons last_step Seq.nil) := by
      rw [Seq.ofList_append, Seq.ofList_cons, Seq.ofList_nil]
    have h_prev_term_seq :
        (Seq.ofList previous_list : Seq (Label × State)).Terminates :=
      Seq.terminates_ofList _
    -- Apply probOf_append_singleton on (s_init, Seq.ofList previous_list, last_step).
    -- The goal has `pe'.probOf ⟨s_init, Seq.ofList (previous_list ++ [last_step])⟩`
    -- on the RHS. Rewrite that to the append form.
    have h_app_term :
        ((Seq.ofList previous_list).append
            (Seq.cons last_step Seq.nil) : Seq (Label × State)).Terminates := by
      rw [← h_seq_split]; exact Seq.terminates_ofList _
    -- Use `congr` + proof-irrelevance to align the two probOf calls.
    have h_alter_eq :
        (⟨s_init, Seq.ofList (previous_list ++ [last_step])⟩ : AlterSeq State Label)
          = ⟨s_init, (Seq.ofList previous_list).append
              (Seq.cons last_step Seq.nil)⟩ := by
      congr 1
    have h_probOf_eq :
        pe'.probOf ⟨s_init, Seq.ofList (previous_list ++ [last_step])⟩
            (Seq.terminates_ofList _) =
        pe'.probOf ⟨s_init, (Seq.ofList previous_list).append
              (Seq.cons last_step Seq.nil)⟩ h_app_term := by
      congr 1
    rw [h_probOf_eq]
    -- Now apply probOf_append_singleton.
    exact (ProbabilisticExecution.probOf_append_singleton
      pe' s_init (Seq.ofList previous_list) h_prev_term_seq last_step h_app_term).symm

private lemma reachProb_marginal_unconditional
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e_w_pre : AlterSeq State Label)
    (h_e_w_pre_term : e_w_pre.trans.Terminates) :
    (∑' e_iter_start : AlterSeq State Label,
      reachProb sys pe' e_w_pre e_iter_start) =
      pe'.probOf e_w_pre h_e_w_pre_term := by
  classical
  -- Structural case split on `e_w_pre.trans.toList`.
  by_cases h_empty : e_w_pre.trans.toList h_e_w_pre_term = []
  · -- Base case: e_w_pre.trans = Seq.nil. Only the singleton
    -- e_iter_start = ⟨e_w_pre.init, Seq.nil⟩ contributes; its mass equals
    -- pe'.initState e_w_pre.init, and pe'.probOf at a nil-trans execution
    -- collapses to the initial mass (via probOf_nil after canonical rewrite).
    have h_e_w_nil : e_w_pre.trans = Seq.nil := by
      have := Stream'.Seq.ofList_toList e_w_pre.trans h_e_w_pre_term
      rw [h_empty] at this
      exact this.symm
    -- Rewrite each summand using the base case of reachProb.
    have h_summand : ∀ e_iter_start : AlterSeq State Label,
        reachProb sys pe' e_w_pre e_iter_start =
          (if e_w_pre.init = e_iter_start.init ∧ e_iter_start.trans = Seq.nil
           then pe'.initState e_w_pre.init else 0) := by
      intro e_iter_start
      unfold reachProb
      rw [dif_pos h_e_w_pre_term, h_empty, List.reverseRecOn_nil]
    rw [tsum_congr h_summand]
    -- Collapse the sum: only e_iter_start = ⟨e_w_pre.init, Seq.nil⟩ contributes.
    rw [tsum_eq_single (⟨e_w_pre.init, Seq.nil⟩ : AlterSeq State Label)]
    · -- Singleton value: pe'.initState e_w_pre.init.
      have h_eq :
          (⟨e_w_pre.init, Seq.nil⟩ : AlterSeq State Label).init = e_w_pre.init ∧
            (⟨e_w_pre.init, Seq.nil⟩ : AlterSeq State Label).trans = Seq.nil :=
        ⟨rfl, rfl⟩
      rw [if_pos h_eq]
      -- pe'.probOf on a nil-trans execution = pe'.init at its init state.
      -- We need to align e_w_pre with ⟨e_w_pre.init, Seq.nil⟩ using h_e_w_nil.
      obtain ⟨ew_init, ew_trans⟩ := e_w_pre
      subst h_e_w_nil
      -- Now e_w_pre = ⟨ew_init, Seq.nil⟩.
      simp only [ProbabilisticExecution.probOf_nil]
      rfl
    · -- Off-singleton: summand is zero.
      intro c hc
      rw [if_neg]
      rintro ⟨h_init_eq, h_trans_nil⟩
      apply hc
      -- c.init = e_w_pre.init and c.trans = Seq.nil ⇒ c = ⟨e_w_pre.init, Seq.nil⟩.
      obtain ⟨c_init, c_trans⟩ := c
      simp only at h_init_eq h_trans_nil
      subst h_init_eq
      subst h_trans_nil
      rfl
  · -- Step case: reduce to the strong-induction aux via
    -- e_w_pre = ⟨e_w_pre.init, Seq.ofList (toList ...)⟩. The key trick is
    -- to introduce `L` and rewrite the trans component to `Seq.ofList L`
    -- before we have anything depending on it.
    set L : List (Label × State) := e_w_pre.trans.toList h_e_w_pre_term with hL
    -- Use the aux to get the result for the canonical form.
    have h_aux : (∑' e_iter_start : AlterSeq State Label,
        reachProb sys pe' ⟨e_w_pre.init, Seq.ofList L⟩ e_iter_start) =
        pe'.probOf ⟨e_w_pre.init, Seq.ofList L⟩ (Seq.terminates_ofList L) :=
      reachProb_marginal_unconditional_aux sys pe' L e_w_pre.init
    -- Transport the result via h_can : e_w_pre = ⟨e_w_pre.init, Seq.ofList L⟩.
    have h_can : (⟨e_w_pre.init, Seq.ofList L⟩ : AlterSeq State Label) = e_w_pre := by
      rcases e_w_pre with ⟨a, b⟩
      simp only at hL
      simp only
      congr 1
      rw [hL]; exact Seq.ofList_toList _ _
    -- Transport via h_can. Both sides become the goal by congr/proof-irrelevance.
    have h_lhs_eq : (∑' e_iter_start : AlterSeq State Label,
        reachProb sys pe' ⟨e_w_pre.init, Seq.ofList L⟩ e_iter_start) =
      ∑' e_iter_start : AlterSeq State Label,
        reachProb sys pe' e_w_pre e_iter_start := by rw [h_can]
    have h_rhs_eq : pe'.probOf ⟨e_w_pre.init, Seq.ofList L⟩ (Seq.terminates_ofList L)
        = pe'.probOf e_w_pre h_e_w_pre_term := by
      congr 1
    rw [← h_lhs_eq, ← h_rhs_eq]
    exact h_aux

/-- **Sub-claim 2 (Step 6): `reachProb` trace-marginal.**

For each `sys^w`-side `e_w_pre`, summing `reachProb sys pe' e_w_pre
e_iter_start` over all `sys`-side `e_iter_start` with `sys.trace
e_iter_start = τ_prev` recovers `pe'.probOf e_w_pre` exactly when
`sys^w.trace e_w_pre = τ_prev` (and yields 0 otherwise).

Conceptually: the coupled algorithm's joint trajectory visits the
hidden `sys^w`-prefix `e_w_pre` at exactly one iteration boundary that
also aligns the visible `sys`-side trace with `τ_prev` (this is the
core invariant of `reachProb`'s definition — it tracks pairs
`(e_w_pre, e)` with `e_w_pre.endState = e.endState` at iteration
boundaries).

The body factors through two helper sub-claims: `reachProb_trace_coupling`
(forces trace alignment whenever `reachProb ≠ 0`) and
`reachProb_marginal_unconditional` (total mass equals `probOf`). -/
private lemma reachProb_marginal_at_trace
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (τ_prev : Seq Label) (_h_τ_prev_term : τ_prev.Terminates)
    (e_w_pre : AlterSeq State Label) :
    (∑' e_iter_start : AlterSeq State Label,
      reachProb sys pe' e_w_pre e_iter_start *
        (open Classical in
         if sys.trace e_iter_start = τ_prev ∧ e_iter_start.trans.Terminates
         then (1 : ENNReal) else 0)) =
      (open Classical in
       if h : e_w_pre.trans.Terminates ∧ sys^w.trace e_w_pre = τ_prev then
        pe'.probOf e_w_pre h.1
      else 0) := by
  classical
  -- Strategy: rewrite each summand using sub-claim A (the trace coupling
  -- invariant), then dispatch on the two conditions in the RHS.
  -- When `reachProb ≠ 0`, the indicator's truth value is independent of
  -- `e_iter_start` once `sys^w.trace e_w_pre` is fixed:
  -- it is `1` iff `e_iter_start.trans.Terminates` (forced by A) ∧
  -- `sys.trace e_iter_start = τ_prev` (which by A equals
  -- `sys^w.trace e_w_pre = τ_prev`).
  have h_summand : ∀ e_iter_start : AlterSeq State Label,
      reachProb sys pe' e_w_pre e_iter_start *
          (if sys.trace e_iter_start = τ_prev ∧ e_iter_start.trans.Terminates
           then (1 : ENNReal) else 0) =
        reachProb sys pe' e_w_pre e_iter_start *
          (if e_w_pre.trans.Terminates ∧ sys^w.trace e_w_pre = τ_prev
           then (1 : ENNReal) else 0) := by
    intro e_iter_start
    by_cases h_reach : reachProb sys pe' e_w_pre e_iter_start = 0
    · simp [h_reach]
    · obtain ⟨h_e_w_term, h_iter_term, h_traces_eq⟩ :=
        reachProb_trace_coupling e_w_pre e_iter_start h_reach
      -- Rewrite both indicators to a single condition on
      -- `sys^w.trace e_w_pre = τ_prev`.
      by_cases h_trace_eq : sys^w.trace e_w_pre = τ_prev
      · have h_sys_trace : sys.trace e_iter_start = τ_prev := h_traces_eq ▸ h_trace_eq
        rw [if_pos ⟨h_sys_trace, h_iter_term⟩, if_pos ⟨h_e_w_term, h_trace_eq⟩]
      · have h_sys_trace_ne : sys.trace e_iter_start ≠ τ_prev := by
          intro h; exact h_trace_eq (h_traces_eq.trans h)
        rw [if_neg (fun h => h_sys_trace_ne h.1),
            if_neg (fun h => h_trace_eq h.2)]
  rw [tsum_congr h_summand]
  -- Now factor the constant indicator out of the tsum.
  rw [ENNReal.tsum_mul_right]
  -- Split on the RHS condition.
  by_cases h_cond : e_w_pre.trans.Terminates ∧ sys^w.trace e_w_pre = τ_prev
  · rw [if_pos h_cond, dif_pos h_cond, mul_one]
    -- Sub-claim B closes the goal.
    exact reachProb_marginal_unconditional sys pe' e_w_pre h_cond.1
  · rw [if_neg h_cond, dif_neg h_cond, mul_zero]

/-- **Sub-claim 3 (Step 6): `traceProb` cons-end factorisation.**

The RHS `sys^w.traceProb pe' (τ_prev ++ [l_τ])` factors via
`probOf_append_singleton` and the `pe'.kernel` definition. Every tight
`sys^w`-execution with trace `τ_prev ++ [l_τ]` decomposes uniquely as
the cons-end extension of a tight `sys^w`-prefix with trace `τ_prev`
by a final external `(l_τ, s)` transition. Marginalising the final
state `s` via `pe'.kernel`'s definition yields the total `l_τ`-emission
mass at `e_w_pre`.

Status: deferred. The proof uses `probOf_append_singleton` to factor
each summand and reorganises the cylinder sum into an outer sum over
tight `τ_prev`-prefixes times an inner sum over the final external
emission. -/
-- **Forward map for `traceProb_cons_external_factorize`'s bijection.** Given a
-- pair `((e_w_pre, h_term, h_trace), s_w_last)`, produces the tight execution
-- `⟨e_w_pre.init, e_w_pre.trans ++ [(l_τ, s_w_last)]⟩` with trace `τ_prev ++ [l_τ]`.
private def consExtFwd
    (sys : LabelledSystem State Label) (τ_prev : Seq Label) (l_τ : Label)
    (h_l_τ_ext : ¬ sys.internal l_τ)
    (p : {e_w_pre : AlterSeq State Label //
            e_w_pre.trans.Terminates ∧ sys.trace e_w_pre = τ_prev} × State) :
    {e : AlterSeq State Label //
      e.trans.Terminates ∧
      sys.trace e = τ_prev.append (Seq.cons l_τ Seq.nil) ∧
      sys.IsTight e} :=
  let h_tail_term1 : (Seq.cons (l_τ, p.2) Seq.nil :
                       Seq (Label × State)).TerminatedAt 1 := by
    change (Seq.cons (l_τ, p.2) Seq.nil :
              Seq (Label × State)).get? 1 = none
    rw [Seq.get?_cons_succ]; rfl
  ⟨⟨p.1.1.init, p.1.1.trans.append (Seq.cons (l_τ, p.2) Seq.nil)⟩,
    ⟨_, Seq.terminatedAt_append_find p.1.2.1 h_tail_term1⟩,
    by
      rw [show (⟨p.1.1.init, p.1.1.trans.append (Seq.cons (l_τ, p.2) Seq.nil)⟩
            : AlterSeq State Label) =
            ⟨p.1.1.init, p.1.1.trans.append (Seq.cons (l_τ, p.2) Seq.nil)⟩ from rfl]
      rw [trace_append_singleton_external sys p.1.1.init p.1.1.trans
            p.1.2.1 l_τ p.2 h_l_τ_ext]
      congr 1
      exact p.1.2.2,
    by
      right
      refine ⟨Nat.find p.1.2.1, l_τ, p.2, ?_, ?_, h_l_τ_ext⟩
      · have := Seq.get?_append_find p.1.2.1
          (Seq.cons (l_τ, p.2) Seq.nil) 0
        simpa using this
      · exact Seq.terminatedAt_append_find p.1.2.1 h_tail_term1⟩

-- **Trace prefix from a tight extension.** Helper for `consExtBwd` (and used in
-- the right_inv proof): if a tight `e` has trace `τ_prev ++ [l_τ]`, then
-- `tight_trans_split_last_witness` decomposes `e.trans` and the prefix's trace
-- recovers `τ_prev` exactly.
private lemma traceProb_cons_external_factorize
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (τ_prev : Seq Label) (l_τ : Label) (_h_τ_prev_term : τ_prev.Terminates)
    (_h_l_τ_external : ¬ sys.internal l_τ) :
    sys^w.traceProb pe' (τ_prev.append (Seq.cons l_τ Seq.nil)) =
      ∑' e_w_pre : {e_w_pre : AlterSeq State Label //
                      e_w_pre.trans.Terminates ∧
                      sys^w.trace e_w_pre = τ_prev},
        pe'.probOf e_w_pre.1 e_w_pre.2.1 *
          (∑' μ : PMF State, pe'.scheduler.next e_w_pre.1 (some (l_τ, μ))) := by
  classical
  -- `sys^w` shares `internal` with `sys`, so the external hypothesis transfers.
  have h_l_τ_ext_w : ¬ sys^w.internal l_τ := _h_l_τ_external
  -- We construct a surjective injection from the prefix-product type
  -- onto the tight-cylinder subtype using `tsum_eq_tsum_of_ne_zero_bij`,
  -- packaging the forward map and its left-inverse purely via tactic blocks
  -- so we avoid term-level destructuring of existential witnesses.
  -- It is simpler to use the forward map alone and prove it bijective via an
  -- inverse map built with `Classical.choose`. To avoid that, we prove the
  -- identity by going through an intermediate symbolic expansion of both
  -- sides as suprema, then matching.
  -- Concretely: unfold `traceProb`, push the forward map's image into a tsum,
  -- and use the right-inverse: every tight `e ∈ T_τ` is uniquely the forward
  -- image of some prefix-pair.
  -- Use `Equiv.tsum_eq` with an explicit equivalence built via Classical.
  -- For the inverse map, we use `Classical.choose` on the existence witness
  -- from `tight_trans_split_last_witness`.
  -- ===
  -- Step (a): Use the surjection-bijection lemma directly. Build `E.toFun`
  -- (forward) and show it is bijective.
  set fwd := fun p =>
    (consExtFwd sys^w τ_prev l_τ h_l_τ_ext_w p : _)
  -- The forward map's image equals the whole tight-cylinder, and it is
  -- injective on the prefix-pair type. Once that's done, we use
  -- `Equiv.ofBijective` to package it.
  have h_inj : Function.Injective fwd := by
    rintro ⟨⟨⟨a_init, a_trans⟩, h_a_term, h_a_trace⟩, s_a⟩
           ⟨⟨⟨b_init, b_trans⟩, h_b_term, h_b_trace⟩, s_b⟩ h_eq
    -- h_eq : fwd p₁ = fwd p₂, i.e. the underlying AlterSeqs match.
    have h_subtype : Subtype.mk
        (⟨a_init, a_trans.append (Seq.cons (l_τ, s_a) Seq.nil)⟩ :
            AlterSeq State Label) _
        = Subtype.mk
        (⟨b_init, b_trans.append (Seq.cons (l_τ, s_b) Seq.nil)⟩ :
            AlterSeq State Label) _ :=
      Subtype.ext (Subtype.ext_iff.mp h_eq)
    have h_inner : (⟨a_init, a_trans.append (Seq.cons (l_τ, s_a) Seq.nil)⟩ :
            AlterSeq State Label)
        = ⟨b_init, b_trans.append (Seq.cons (l_τ, s_b) Seq.nil)⟩ :=
      Subtype.ext_iff.mp h_subtype
    have h_init_eq : a_init = b_init := by
      have := congrArg AlterSeq.init h_inner; exact this
    have h_trans_eq :
        a_trans.append (Seq.cons (l_τ, s_a) Seq.nil)
          = b_trans.append (Seq.cons (l_τ, s_b) Seq.nil) := by
      have := congrArg AlterSeq.trans h_inner; exact this
    -- From `h_trans_eq`, derive `a_trans = b_trans` and `s_a = s_b`.
    have h_pair_eq : (l_τ, s_a) = (l_τ, s_b) :=
      Seq.append_singleton_inj_right a_trans b_trans h_a_term h_b_term
        (l_τ, s_a) (l_τ, s_b) h_trans_eq
    have h_s_eq : s_a = s_b := (Prod.mk.inj h_pair_eq).2
    have h_at_eq : a_trans = b_trans :=
      Seq.append_singleton_inj_left a_trans b_trans h_a_term h_b_term
        (l_τ, s_a) (l_τ, s_b) h_trans_eq
    -- Combine.
    apply Prod.ext
    · apply Subtype.ext
      change (⟨a_init, a_trans⟩ : AlterSeq State Label) = ⟨b_init, b_trans⟩
      rw [h_init_eq, h_at_eq]
    · exact h_s_eq
  have h_surj : Function.Surjective fwd := by
    rintro ⟨e, h_e_term, h_e_trace, h_e_tight⟩
    -- Split e.trans via tightness.
    have h_ne : e.trans ≠ Seq.nil := by
      intro h_nil
      have h_trace_nil : sys^w.trace e = Seq.nil := by
        unfold LabelledSystem.trace
        rw [h_nil]; simp
      rw [h_trace_nil] at h_e_trace
      -- nil ≠ τ_prev ++ [l_τ]
      have h_get0 :
          (τ_prev.append (Seq.cons l_τ Seq.nil)).get? (Nat.find _h_τ_prev_term)
            = some l_τ := by
        have := Seq.get?_append_find _h_τ_prev_term
          (Seq.cons l_τ Seq.nil) 0
        simpa using this
      rw [← h_e_trace] at h_get0
      simp at h_get0
    obtain ⟨trans_prev, h_prev_term, l_last, s_last, h_struct, h_l_last_ext⟩ :=
      tight_trans_split_last_witness sys^w e h_e_term h_e_tight h_ne
    -- Derive l_last = l_τ.
    have h_pre_trace_term :
        (sys^w.trace ⟨e.init, trans_prev⟩).Terminates :=
      trace_terminates_of_trans_terminates sys^w ⟨e.init, trans_prev⟩ h_prev_term
    have h_trace_split :
        (sys^w.trace ⟨e.init, trans_prev⟩).append (Seq.cons l_last Seq.nil)
            = τ_prev.append (Seq.cons l_τ Seq.nil) := by
      rw [← trace_append_singleton_external sys^w e.init trans_prev
            h_prev_term l_last s_last h_l_last_ext]
      have h_e_split : e = ⟨e.init, trans_prev.append
          (Seq.cons (l_last, s_last) Seq.nil)⟩ := by
        obtain ⟨init, trans⟩ := e
        dsimp at h_struct ⊢
        exact congrArg (AlterSeq.mk init) h_struct
      rw [← h_e_split]; exact h_e_trace
    have h_l_last_eq_l_τ : l_last = l_τ :=
      Seq.append_singleton_inj_right _ _ h_pre_trace_term _h_τ_prev_term
        l_last l_τ h_trace_split
    have h_pre_trace_eq : sys^w.trace ⟨e.init, trans_prev⟩ = τ_prev :=
      Seq.append_singleton_inj_left _ _ h_pre_trace_term _h_τ_prev_term
        l_last l_τ (by rw [h_l_last_eq_l_τ] at h_trace_split ⊢; exact h_trace_split)
    refine ⟨⟨⟨⟨e.init, trans_prev⟩, h_prev_term, h_pre_trace_eq⟩, s_last⟩, ?_⟩
    apply Subtype.ext
    change (⟨e.init, trans_prev.append (Seq.cons (l_τ, s_last) Seq.nil)⟩
            : AlterSeq State Label) = e
    have h_e_split : e = ⟨e.init, trans_prev.append
        (Seq.cons (l_last, s_last) Seq.nil)⟩ := by
      obtain ⟨init, trans⟩ := e
      dsimp at h_struct ⊢
      exact congrArg (AlterSeq.mk init) h_struct
    rw [h_e_split, h_l_last_eq_l_τ]
  let E := Equiv.ofBijective fwd ⟨h_inj, h_surj⟩
  unfold LabelledSystem.traceProb
  rw [← Equiv.tsum_eq E]
  rw [ENNReal.tsum_prod']
  refine tsum_congr ?_
  intro e_w_pre_sub
  obtain ⟨e_w_pre, h_pre_term, h_pre_trace⟩ := e_w_pre_sub
  -- The summand at fixed `e_w_pre` becomes:
  --   ∑' s, probOf ⟨e_w_pre.init, e_w_pre.trans ++ [(l_τ, s)]⟩
  --   = probOf e_w_pre * ∑' s, pe'.kernel e_w_pre (l_τ, s)
  --   = probOf e_w_pre * ∑' μ, scheduler.next e_w_pre (some (l_τ, μ))
  have h_app : ∀ s : State,
      (Seq.append e_w_pre.trans (Seq.cons (l_τ, s) Seq.nil)).Terminates :=
    fun s =>
      ⟨_, Seq.terminatedAt_append_find h_pre_term
        (show (Seq.cons (l_τ, s) Seq.nil :
                Seq (Label × State)).TerminatedAt 1 by
          change (Seq.cons (l_τ, s) Seq.nil :
                    Seq (Label × State)).get? 1 = none
          rw [Seq.get?_cons_succ]; rfl)⟩
  have h_summand : ∀ s : State,
      pe'.probOf
          (⟨e_w_pre.init,
            e_w_pre.trans.append (Seq.cons (l_τ, s) Seq.nil)⟩ : AlterSeq State Label)
          (h_app s) =
        pe'.probOf e_w_pre h_pre_term * pe'.kernel e_w_pre (l_τ, s) := by
    intro s
    obtain ⟨init, trans⟩ := e_w_pre
    exact ProbabilisticExecution.probOf_append_singleton (pe := pe')
      init trans h_pre_term (l_τ, s) (h_app s)
  -- The summand on the LHS is `pe'.probOf (fwd ⟨..., s⟩).1 _`, which by
  -- definition of `fwd` is `pe'.probOf ⟨init, trans ++ [(l_τ, s)]⟩ _`.
  rw [show (∑' (s : State), pe'.probOf (E (⟨e_w_pre, h_pre_term, h_pre_trace⟩, s)).1
              (E (⟨e_w_pre, h_pre_term, h_pre_trace⟩, s)).2.1)
        = ∑' (s : State),
            pe'.probOf e_w_pre h_pre_term * pe'.kernel e_w_pre (l_τ, s) from
      tsum_congr h_summand]
  rw [ENNReal.tsum_mul_left]
  congr 1
  unfold ProbabilisticExecution.kernel
  rw [ENNReal.tsum_comm]
  refine tsum_congr ?_; intro μ
  -- Normalise `(l_τ, a).1`/`.2` so the kernel's `step` projections evaluate.
  change ∑' (a : State), (pe'.scheduler.next e_w_pre) (some (l_τ, μ)) * μ a =
        (pe'.scheduler.next e_w_pre) (some (l_τ, μ))
  rw [ENNReal.tsum_mul_left, μ.tsum_coe, mul_one]

/-- **Post-Step-5 form of the telescoping sub-lemma.**

After Step 5 of the strategy (per-`e` rewriting via `jointTight_step_external`
plus a second `tsum_comm` to swap the `e_w_pre` and `e_iter_start` sums), the
LHS of `extCylinderMass_sum_eq_traceProb_terminating_swapped` reduces to the
triple sum

  `∑' e ∈ T_τ, ∑' e_iter_start, ∑' e_w_pre,
     reachProb sys pe' e_w_pre e_iter_start *
       tightStepFactor sys pe' e_w_pre l_τ e_iter_start e.1`

where `τ = τ_prev.append (cons l_τ nil)`. Step 6 assembles the proof from
three sub-claims: `witness_emission_marginal` (chain-decomposition of the
weakStep witness yields the scheduler-emission mass at `l_τ`),
`reachProb_marginal_at_trace` (the `reachProb` marginal at trace `τ_prev`
recovers `pe'.probOf` on the `sys^w`-side), and
`traceProb_cons_external_factorize` (cons-end factorisation of
`sys^w.traceProb` via `probOf_append_singleton`). The body of this
lemma is currently deferred pending the assembly tactics — see the
`Status` paragraph in the docstring of each sub-claim. -/
private lemma extCylinderMass_sum_eq_traceProb_terminating_step5
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (τ_prev : Seq Label) (l_τ : Label) (_h_τ_prev_term : τ_prev.Terminates) :
    (∑' e : {e : AlterSeq State Label //
              e.trans.Terminates ∧
              sys.trace e = τ_prev.append (Seq.cons l_τ Seq.nil) ∧
              sys.IsTight e},
      ∑' e_iter_start : AlterSeq State Label,
      ∑' e_w_pre : AlterSeq State Label,
        reachProb sys pe' e_w_pre e_iter_start *
          tightStepFactor sys pe' e_w_pre l_τ e_iter_start e.1) =
      sys^w.traceProb pe' (τ_prev.append (Seq.cons l_τ Seq.nil)) := by
  -- Case-split on whether `l_τ` is internal. If internal, both sides vanish
  -- (the cylinder is empty on both sides — `sys.trace`/`sys^w.trace` filter
  -- out internal labels).
  by_cases h_l_τ_ext : sys.internal l_τ
  · -- Internal: both sides equal 0. The LHS sums over the empty subtype
    -- `T_τ`; the RHS is `sys^w.traceProb` of an internal-terminated trace,
    -- also 0 by the same cylinder-empty argument (`sys^w` shares `internal`
    -- with `sys`).
    haveI hE_sys : IsEmpty {e : AlterSeq State Label //
                e.trans.Terminates ∧
                sys.trace e = τ_prev.append (Seq.cons l_τ Seq.nil) ∧
                sys.IsTight e} :=
      isEmpty_traceCylinder_of_internal_last sys τ_prev _h_τ_prev_term l_τ h_l_τ_ext
    rw [tsum_empty]
    -- `sys^w.internal = sys.internal`, so `sys^w.trace = sys.trace` and
    -- `sys^w.IsTight = sys.IsTight` definitionally; reuse the same lemma.
    have h_sys_w_empty : IsEmpty {e : AlterSeq State Label //
                e.trans.Terminates ∧
                sys^w.trace e = τ_prev.append (Seq.cons l_τ Seq.nil) ∧
                sys^w.IsTight e} := by
      exact isEmpty_traceCylinder_of_internal_last sys^w τ_prev _h_τ_prev_term l_τ
        h_l_τ_ext
    unfold LabelledSystem.traceProb
    haveI := h_sys_w_empty
    exact tsum_empty.symm
  -- `¬ sys.internal l_τ`: the substantive case. Apply sub-claims 1-3.
  -- **Assembly outline** (using `witness_emission_marginal`,
  -- `reachProb_marginal_at_trace`, `traceProb_cons_external_factorize`):
  --
  --   LHS
  -- = ∑' e ∈ T_τ, ∑' e_iter_start, ∑' e_w_pre, reachProb · tightStepFactor
  -- = ∑' e_iter_start, ∑' e_w_pre, reachProb · (∑' e ∈ T_τ, tightStepFactor)
  --                                                       -- ENNReal.tsum_comm twice
  -- = ∑' e_iter_start, ∑' e_w_pre,
  --     reachProb · (if sys.trace e_iter_start = τ_prev then
  --                    ∑' μ, scheduler.next (some (l_τ, μ)) else 0)
  --                                                       -- witness_emission_marginal
  -- = ∑' e_w_pre, (∑' e_iter_start (trace = τ_prev), reachProb)
  --     · (∑' μ, scheduler.next (some (l_τ, μ)))
  --                                                       -- swap + collect if
  -- = ∑' e_w_pre (trace = τ_prev), pe'.probOf e_w_pre · (∑' μ, ...)
  --                                                       -- reachProb_marginal_at_trace
  -- = sys^w.traceProb pe' (τ_prev ++ [l_τ])
  --                                  -- traceProb_cons_external_factorize, backwards
  --
  -- Step A: swap the outer e-sum past the e_iter_start and e_w_pre sums via
  -- two applications of `ENNReal.tsum_comm`.
  rw [show
        (∑' e : {e : AlterSeq State Label //
                  e.trans.Terminates ∧
                  sys.trace e = τ_prev.append (Seq.cons l_τ Seq.nil) ∧
                  sys.IsTight e},
          ∑' e_iter_start : AlterSeq State Label,
          ∑' e_w_pre : AlterSeq State Label,
            reachProb sys pe' e_w_pre e_iter_start *
              tightStepFactor sys pe' e_w_pre l_τ e_iter_start e.1) =
        ∑' e_iter_start : AlterSeq State Label,
        ∑' e_w_pre : AlterSeq State Label,
        ∑' e : {e : AlterSeq State Label //
                  e.trans.Terminates ∧
                  sys.trace e = τ_prev.append (Seq.cons l_τ Seq.nil) ∧
                  sys.IsTight e},
          reachProb sys pe' e_w_pre e_iter_start *
            tightStepFactor sys pe' e_w_pre l_τ e_iter_start e.1 from by
    rw [ENNReal.tsum_comm]
    refine tsum_congr ?_; intro e_iter_start
    rw [ENNReal.tsum_comm]]
  -- Step B: pull `reachProb` (independent of `e`) out of the inner e-sum,
  -- then apply `witness_emission_marginal` to compute the e-sum.
  have h_step_B :
      (∑' e_iter_start : AlterSeq State Label,
       ∑' e_w_pre : AlterSeq State Label,
       ∑' e : {e : AlterSeq State Label //
                 e.trans.Terminates ∧
                 sys.trace e = τ_prev.append (Seq.cons l_τ Seq.nil) ∧
                 sys.IsTight e},
         reachProb sys pe' e_w_pre e_iter_start *
           tightStepFactor sys pe' e_w_pre l_τ e_iter_start e.1) =
      ∑' e_iter_start : AlterSeq State Label,
      ∑' e_w_pre : AlterSeq State Label,
        reachProb sys pe' e_w_pre e_iter_start *
          (open Classical in
           if sys.trace e_iter_start = τ_prev ∧ e_iter_start.trans.Terminates then
            ∑' μ : PMF State, pe'.scheduler.next e_w_pre (some (l_τ, μ))
           else 0) := by
    refine tsum_congr ?_; intro e_iter_start
    refine tsum_congr ?_; intro e_w_pre
    by_cases h_e_w_pre_term : e_w_pre.trans.Terminates
    · rw [ENNReal.tsum_mul_left]
      congr 1
      exact witness_emission_marginal sys pe' τ_prev l_τ _h_τ_prev_term h_l_τ_ext
        e_w_pre e_iter_start h_e_w_pre_term
    · -- `e_w_pre.trans` does not terminate: `reachProb sys pe' e_w_pre _ = 0`
      -- by the outer `if h_e_w_term` guard in `reachProb`'s definition. Both
      -- sides collapse to zero.
      have h_reach_zero : reachProb sys pe' e_w_pre e_iter_start = 0 := by
        unfold reachProb
        simp [h_e_w_pre_term]
      rw [h_reach_zero, zero_mul]
      refine ENNReal.tsum_eq_zero.mpr (fun _ => ?_)
      rw [zero_mul]
  rw [h_step_B]
  -- Step C: swap e_iter_start ↔ e_w_pre. The conditional's value (when
  -- non-zero) `∑' μ, scheduler.next (some (l_τ, μ))` depends only on
  -- e_w_pre, so it factors out of the inner e_iter_start-sum.
  rw [ENNReal.tsum_comm]
  -- Step D: for each e_w_pre, factor the e_w_pre-independent emission
  -- factor out of the e_iter_start-sum. After this, the inner sum is
  --   ∑' e_iter_start, reachProb · (if sys.trace e_iter_start = τ_prev
  --                                  ∧ e_iter_start.trans.Terminates then 1 else 0).
  -- This is the indicator-restricted marginal of `reachProb` at trace
  -- `τ_prev`.
  have h_step_D :
      (∑' e_w_pre : AlterSeq State Label, ∑' e_iter_start : AlterSeq State Label,
        reachProb sys pe' e_w_pre e_iter_start *
          (open Classical in
           if sys.trace e_iter_start = τ_prev ∧ e_iter_start.trans.Terminates then
            ∑' μ : PMF State, pe'.scheduler.next e_w_pre (some (l_τ, μ))
           else 0)) =
      ∑' e_w_pre : AlterSeq State Label,
        (∑' e_iter_start : AlterSeq State Label,
          reachProb sys pe' e_w_pre e_iter_start *
            (open Classical in
             if sys.trace e_iter_start = τ_prev ∧ e_iter_start.trans.Terminates then
              (1 : ENNReal)
             else 0)) *
          (∑' μ : PMF State, pe'.scheduler.next e_w_pre (some (l_τ, μ))) := by
    refine tsum_congr ?_; intro e_w_pre
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr ?_; intro e_iter_start
    by_cases h_cond : sys.trace e_iter_start = τ_prev ∧
                       e_iter_start.trans.Terminates
    · classical
      rw [if_pos h_cond, if_pos h_cond, mul_one]
    · classical
      rw [if_neg h_cond, if_neg h_cond, mul_zero, zero_mul]
  rw [h_step_D]
  -- Step E: apply `reachProb_marginal_at_trace` (sub-claim 2) per e_w_pre to
  -- collapse the inner e_iter_start-sum to a guarded `pe'.probOf` term.
  have h_step_E :
      (∑' e_w_pre : AlterSeq State Label,
        (∑' e_iter_start : AlterSeq State Label,
          reachProb sys pe' e_w_pre e_iter_start *
            (open Classical in
             if sys.trace e_iter_start = τ_prev ∧ e_iter_start.trans.Terminates
             then (1 : ENNReal) else 0)) *
          (∑' μ : PMF State, pe'.scheduler.next e_w_pre (some (l_τ, μ)))) =
      ∑' e_w_pre : AlterSeq State Label,
        (open Classical in
         if h : e_w_pre.trans.Terminates ∧ sys^w.trace e_w_pre = τ_prev then
          pe'.probOf e_w_pre h.1
         else 0) *
          (∑' μ : PMF State, pe'.scheduler.next e_w_pre (some (l_τ, μ))) := by
    refine tsum_congr ?_; intro e_w_pre
    rw [reachProb_marginal_at_trace sys pe' τ_prev _h_τ_prev_term e_w_pre]
  rw [h_step_E]
  -- Step F: convert the indicator-restricted tsum to a tsum over the tight
  -- `sys^w`-prefix subtype, then close via `traceProb_cons_external_factorize`
  -- (sub-claim 3) backwards.
  · classical
    rw [traceProb_cons_external_factorize sys pe' τ_prev l_τ _h_τ_prev_term h_l_τ_ext]
    -- Convert the LHS indicator-tsum to the RHS subtype-tsum directly via
    -- `tsum_subtype`.
    set S : Set (AlterSeq State Label) :=
      {e_w_pre | e_w_pre.trans.Terminates ∧ sys^w.trace e_w_pre = τ_prev}
      with hS_def
    have hindicator :
        (fun e_w_pre : AlterSeq State Label =>
            (if h : e_w_pre.trans.Terminates ∧
                    sys^w.trace e_w_pre = τ_prev then
              pe'.probOf e_w_pre h.1
            else 0) *
              (∑' μ : PMF State, pe'.scheduler.next e_w_pre (some (l_τ, μ)))) =
        S.indicator (fun x =>
            (if h : x.trans.Terminates ∧
                    sys^w.trace x = τ_prev then
              pe'.probOf x h.1
            else 0) *
              (∑' μ : PMF State, pe'.scheduler.next x (some (l_τ, μ)))) := by
      funext e_w_pre
      by_cases h_mem : e_w_pre.trans.Terminates ∧
                       sys^w.trace e_w_pre = τ_prev
      · have h_mem_S : e_w_pre ∈ S := h_mem
        simp only [Set.indicator_of_mem h_mem_S]
      · have h_mem_S : e_w_pre ∉ S := h_mem
        simp only [Set.indicator_of_notMem h_mem_S, dif_neg h_mem, zero_mul]
    rw [hindicator, ← tsum_subtype S]
    refine tsum_congr ?_
    rintro ⟨e_w_pre, h_mem⟩
    have h_mem' : e_w_pre.trans.Terminates ∧
                  sys^w.trace e_w_pre = τ_prev := h_mem
    simp only [dif_pos h_mem']

private lemma extCylinderMass_sum_eq_traceProb_terminating_swapped
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (τ_prev : Seq Label) (l_τ : Label) (h_τ_prev_term : τ_prev.Terminates) :
    (∑' e : {e : AlterSeq State Label //
              e.trans.Terminates ∧
              sys.trace e = τ_prev.append (Seq.cons l_τ Seq.nil) ∧
              sys.IsTight e},
      ∑' e_w_pre : AlterSeq State Label,
        jointTight sys pe' e_w_pre e.1) =
      sys^w.traceProb pe' (τ_prev.append (Seq.cons l_τ Seq.nil)) := by
  -- **Step 5(a):** per `e ∈ T_τ`, decompose `e.trans` via tightness +
  -- `exists_split_last` (giving `e.trans = trans_prev ++ [(l_last, s_last)]`
  -- with `l_last` external), identify `l_last = l_τ` via the trace, then
  -- rewrite `jointTight` to the `reachProb · tightStepFactor` factorisation.
  -- **Step 5(b):** apply `ENNReal.tsum_comm` to swap the inner `e_w_pre` and
  -- `e_iter_start` sums.
  -- After Step 5, the goal matches `_step5` exactly.
  refine Eq.trans ?_
    (extCylinderMass_sum_eq_traceProb_terminating_step5 sys pe' τ_prev l_τ h_τ_prev_term)
  refine tsum_congr ?_
  rintro ⟨e, h_e_term, h_e_trace, h_e_tight⟩
  -- `e.trans` is non-empty (its trace `τ_prev ++ [l_τ]` is non-nil).
  have h_trans_ne : e.trans ≠ Seq.nil := by
    intro h_nil
    have h_trace_nil : sys.trace e = Seq.nil := by
      unfold LabelledSystem.trace; rw [h_nil]; simp
    rw [h_e_trace] at h_trace_nil
    -- `τ_prev.append (cons l_τ nil) = nil`: take toLists.
    have h_cons_term : (Seq.cons l_τ Seq.nil).Terminates :=
      Seq.terminates_cons_iff.mpr Seq.terminates_nil
    have h_app_term : (τ_prev.append (Seq.cons l_τ Seq.nil)).Terminates :=
      ⟨_, Seq.terminatedAt_append_find h_τ_prev_term h_cons_term.choose_spec⟩
    have h_toL_app := Seq.toList_append τ_prev (Seq.cons l_τ Seq.nil) h_τ_prev_term
      h_cons_term h_app_term
    have h_cons_toL : (Seq.cons l_τ Seq.nil).toList h_cons_term = [l_τ] := by
      rw [Seq.toList_cons]; congr 1; exact Seq.toList_nil
    rw [h_cons_toL] at h_toL_app
    -- Combine: τ_prev.toList ++ [l_τ] = (append).toList = nil.toList = []
    have h_app_eq_nil : τ_prev.append (Seq.cons l_τ Seq.nil) = Seq.nil := h_trace_nil
    have h_app_nil_toL : τ_prev.toList h_τ_prev_term ++ [l_τ] = [] := by
      rw [← h_toL_app]
      -- Use proof irrelevance and h_app_eq_nil to reduce to nil.toList = [].
      have h_nil_term : (Seq.nil : Seq Label).Terminates := Seq.terminates_nil
      calc (τ_prev.append (Seq.cons l_τ Seq.nil)).toList h_app_term
          = (Seq.nil : Seq Label).toList h_nil_term := by congr 1
        _ = [] := Seq.toList_nil
    exact (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)) h_app_nil_toL
  -- Decompose `e.trans = trans_prev ++ [(l_last, s_last)]` with `l_last` external.
  obtain ⟨trans_prev, h_prev_term, l_last, s_last, h_struct, h_ext⟩ :=
    tight_trans_split_last_witness sys e h_e_term h_e_tight h_trans_ne
  -- Identify `l_last = l_τ` via the trace.
  have h_trace_split : sys.trace e
      = (sys.trace ⟨e.init, trans_prev⟩).append (Seq.cons l_last Seq.nil) := by
    have h_e_eq : e = ⟨e.init, trans_prev.append (Seq.cons (l_last, s_last) Seq.nil)⟩ := by
      rcases e with ⟨init, trans⟩; dsimp at h_struct ⊢; subst h_struct; rfl
    rw [h_e_eq]
    exact trace_append_singleton_external sys e.init trans_prev h_prev_term l_last s_last h_ext
  have h_trace_prev_term : (sys.trace ⟨e.init, trans_prev⟩).Terminates :=
    trace_terminates_of_trans_terminates sys ⟨e.init, trans_prev⟩ h_prev_term
  have h_l_eq : l_last = l_τ :=
    Seq.append_singleton_inj_right _ _ h_trace_prev_term h_τ_prev_term l_last l_τ
      (by rw [← h_trace_split, h_e_trace])
  -- Now rewrite using `jointTight_step_external` with `l_last := l_τ`.
  have h_struct' : e.trans = trans_prev.append (Seq.cons (l_τ, s_last) Seq.nil) := by
    rw [← h_l_eq]; exact h_struct
  have h_ext' : ¬ sys.internal l_τ := h_l_eq ▸ h_ext
  -- Per `e_w_pre`, rewrite `jointTight` to the step factorisation.
  have h_per_e : (∑' e_w_pre : AlterSeq State Label, jointTight sys pe' e_w_pre e) =
      ∑' e_w_pre : AlterSeq State Label, ∑' e_iter_start : AlterSeq State Label,
        reachProb sys pe' e_w_pre e_iter_start *
          tightStepFactor sys pe' e_w_pre l_τ e_iter_start e := by
    refine tsum_congr ?_
    intro e_w_pre
    exact jointTight_step_external sys pe' e_w_pre e h_e_term
      trans_prev h_prev_term l_τ s_last h_struct' h_ext'
  rw [h_per_e]
  -- Swap inner tsums.
  exact ENNReal.tsum_comm

/-- **Telescoping sub-lemma at a fixed non-nil terminating trace.**

Given the cons-end splitting `τ = τ_prev.append (cons l_τ nil)` via
`Stream'.Seq.exists_split_last` (steps 1–2 of the strategy), the
LHS-side double sum over `(e_w_pre, e ∈ T_τ)` of `jointTight`
factorises through the iteration-start prefix `e_iter_start` and the
weak-step witness chain extending `e_iter_start` to `e` through the
final external label `l_τ`. The RHS-side tight cylinder for `τ`
factorises (via `probOf_append_singleton`) into the tight cylinder for
`τ_prev` times the kernel emitting the final external transition.

The matching identity equates the two factorisations after a Fubini
swap. The witness-side identity (sum of `tightStepFactor` chain
decompositions equals the scheduler emission mass at `(l_τ, μ)`) and
the reachProb-marginal identity at trace `τ_prev` are the two
substantive intermediates.

Deferred — see steps 4–6 of the strategy docstring above
`pe_of_weak_traceProb`. -/
private lemma extCylinderMass_sum_eq_traceProb_terminating_aux
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (τ_prev : Seq Label) (l_τ : Label) (h_τ_prev_term : τ_prev.Terminates) :
    (∑' e_w_pre : AlterSeq State Label,
      extCylinderMass sys pe' (τ_prev.append (Seq.cons l_τ Seq.nil)) e_w_pre) =
      sys^w.traceProb pe' (τ_prev.append (Seq.cons l_τ Seq.nil)) := by
  -- See the strategy docstring above `pe_of_weak_traceProb` for the full
  -- argument. The proof telescopes the joint inner-iteration mass through
  -- the cons-end split of `τ` and applies Fubini to swap the
  -- `(e_w_pre, e)` summation order.
  --
  -- **Step 4 (mechanical, performed below):** unfold `extCylinderMass` to its
  -- defining inner sum `∑' e ∈ T_τ, jointTight e_w_pre e.1` and apply
  -- `ENNReal.tsum_comm` to swap the outer `e_w_pre` sum with the inner sum
  -- over the tight cylinder `T_τ`. After this swap the LHS reads
  --
  --     ∑' e ∈ T_τ, ∑' e_w_pre, jointTight sys pe' e_w_pre e.1.
  --
  -- The remaining substantive work (Steps 5–6 of the strategy) is to
  -- (a) reduce `jointTight` for each `e ∈ T_τ` to its step-case form using
  -- `jointTight_step_external` (this exposes the `∑' e_iter_start, reachProb ·
  -- tightStepFactor` factorisation), and (b) match against the cons-end
  -- recursion of `traceProb`. See `extCylinderMass_sum_eq_traceProb_terminating_swapped`.
  set τ : Seq Label := τ_prev.append (Seq.cons l_τ Seq.nil) with h_τ_def
  -- Unfold `extCylinderMass` and swap the order of summation. Since both
  -- summands are in `ENNReal`, `ENNReal.tsum_comm` applies unconditionally.
  have h_swap :
      (∑' e_w_pre : AlterSeq State Label,
        extCylinderMass sys pe' τ e_w_pre) =
        ∑' e : {e : AlterSeq State Label //
                e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e},
          ∑' e_w_pre : AlterSeq State Label,
            jointTight sys pe' e_w_pre e.1 := by
    unfold extCylinderMass
    exact ENNReal.tsum_comm
  rw [h_swap]
  exact extCylinderMass_sum_eq_traceProb_terminating_swapped
    sys pe' τ_prev l_τ h_τ_prev_term

-- **Inductive-case sub-lemma**: when `τ` terminates and is non-empty,
-- the inductive identity holds. Splits `τ` via `exists_split_last` and
-- delegates to `extCylinderMass_sum_eq_traceProb_terminating_aux`.
private lemma extCylinderMass_sum_eq_traceProb_terminating
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (τ : Seq Label) (h_τ_term : τ.Terminates) (h_τ_nil : τ ≠ Seq.nil) :
    (∑' e_w_pre : AlterSeq State Label,
      extCylinderMass sys pe' τ e_w_pre) =
      sys^w.traceProb pe' τ := by
  -- Step 1: split τ as τ_prev ++ [l_τ] via `exists_split_last`.
  have h_toList_ne : τ.toList h_τ_term ≠ [] := by
    intro h_empty
    apply h_τ_nil
    have h_ofList : Seq.ofList (τ.toList h_τ_term) = τ := Seq.ofList_toList τ h_τ_term
    rw [h_empty] at h_ofList
    rw [← h_ofList]
    rfl
  obtain ⟨τ_prev, l_τ, h_τ_prev_term, h_τ_split, _, _⟩ :=
    Stream'.Seq.exists_split_last τ h_τ_term h_toList_ne
  -- Step 2: rewrite both sides via the split and apply the aux lemma.
  rw [h_τ_split]
  exact extCylinderMass_sum_eq_traceProb_terminating_aux sys pe' τ_prev l_τ h_τ_prev_term

private lemma extCylinderMass_sum_eq_traceProb
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (τ : Seq Label) :
    (∑' e_w_pre : AlterSeq State Label,
      extCylinderMass sys pe' τ e_w_pre) =
      sys^w.traceProb pe' τ := by
  classical
  by_cases h_τ_nil : τ = Seq.nil
  · -- **Base case** `τ = Seq.nil`. Both sides reduce to
    -- `∑' s, pe'.initState s` (which is `1` by PMF total mass).
    subst h_τ_nil
    -- LHS: rewrite via `extCylinderMass_nil`, then re-index against
    -- the `State ≃ {trans = nil}` equiv to peel off the indicator.
    have h_LHS :
        (∑' e_w_pre : AlterSeq State Label,
          extCylinderMass sys pe' Seq.nil e_w_pre) =
          ∑' s : State, pe'.initState s := by
      simp only [extCylinderMass_nil sys pe']
      -- Bijection on supports: the indicator is non-zero only at
      -- `e_w_pre = ⟨s, Seq.nil⟩`, matching State exactly.
      refine tsum_eq_tsum_of_ne_zero_bij (g := fun s : State => pe'.initState s)
        (f := fun e_w_pre : AlterSeq State Label =>
          if e_w_pre.trans = Seq.nil then pe'.initState e_w_pre.init else 0)
        (fun s : Function.support (fun s : State => pe'.initState s) =>
          (⟨s.1, Seq.nil⟩ : AlterSeq State Label))
        ?_ ?_ ?_
      · intro x y h
        have : x.1 = y.1 := by
          have := congrArg AlterSeq.init h
          exact this
        exact Subtype.ext this
      · intro e_w_pre h_supp
        simp only [Function.mem_support] at h_supp
        by_cases h_trans : e_w_pre.trans = Seq.nil
        · refine ⟨⟨e_w_pre.init, ?_⟩, ?_⟩
          · simp only [Function.mem_support]
            intro h_eq
            apply h_supp
            simp [h_trans, h_eq]
          · change (⟨e_w_pre.init, Seq.nil⟩ : AlterSeq State Label) = e_w_pre
            cases e_w_pre with
            | mk init trans =>
              dsimp at h_trans; subst h_trans; rfl
        · exfalso; apply h_supp; simp [h_trans]
      · intro s
        change (if (⟨s.1, Seq.nil⟩ : AlterSeq State Label).trans = Seq.nil then
                pe'.initState (⟨s.1, Seq.nil⟩ : AlterSeq State Label).init else 0) =
              pe'.initState s.1
        simp
    rw [h_LHS]
    -- RHS: unfold traceProb, re-index via the `State ≃ T_nil` equiv,
    -- and reduce `probOf ⟨s, nil⟩ = pe'.initState s`.
    unfold LabelledSystem.traceProb
    rw [← Equiv.tsum_eq (tightNilTraceEquiv sys^w)]
    refine tsum_congr ?_
    intro s
    simp only [tightNilTraceEquiv, Equiv.coe_fn_mk]
    change pe'.initState s = pe'.probOf ⟨s, Seq.nil⟩ Seq.terminates_nil
    rw [ProbabilisticExecution.probOf_nil]
    rfl
  · -- **Inductive case** `τ ≠ Seq.nil`. First reduce to the case where
    -- `τ` terminates: when `τ` is non-terminating, both sides are `0`
    -- because the underlying trace-cylinder subtype is empty (every
    -- finite execution has a terminating trace).
    by_cases h_τ_term : τ.Terminates
    · -- Terminating non-empty case: discharge via the inductive
      -- sub-lemma below.
      exact extCylinderMass_sum_eq_traceProb_terminating sys pe' τ h_τ_term h_τ_nil
    · -- Non-terminating case: both sides are `0`.
      rw [traceProb_eq_zero_of_not_terminates _ pe' τ h_τ_term]
      rw [ENNReal.tsum_eq_zero]
      intro e_w_pre
      exact extCylinderMass_eq_zero_of_not_terminates sys pe' τ h_τ_term e_w_pre

/-- **Main correctness lemma for `pe_of_weak`**: the trace-probability under
`sys` of the algorithmic witness `pe_of_weak sys pe'` matches the
trace-probability under `sys^w` of the original `pe'`. See the
strategy docstring above and the sub-lemmas `jointTight_marginal_A`,
`jointTight_marginal_B`, `extCylinderMass_sum_eq_traceProb`. -/
theorem pe_of_weak_traceProb (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (τ : Seq Label) :
    sys.traceProb (pe_of_weak sys pe') τ = sys^w.traceProb pe' τ := by
  -- LHS unfolding: `traceProb` sums `probOf` over the tight `τ`-cylinder.
  unfold LabelledSystem.traceProb
  -- Replace each summand `probOf e` by the `e_w_pre`-marginal of
  -- `jointTight` via Marginal A.
  have h_LHS_eq :
      (∑' e : {e : AlterSeq State Label //
                e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e},
          (pe_of_weak sys pe').probOf e.1 e.2.1) =
      (∑' e : {e : AlterSeq State Label //
                e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e},
          ∑' e_w_pre : AlterSeq State Label,
            jointTight sys pe' e_w_pre e.1) := by
    refine tsum_congr ?_
    rintro ⟨e, h_term, _h_trace, h_tight⟩
    exact (jointTight_marginal_A sys pe' e h_term h_tight).symm
  rw [h_LHS_eq]
  -- Apply Fubini (`ENNReal.tsum_comm`) to swap the two tsums.
  rw [ENNReal.tsum_comm]
  -- Inner sum is `extCylinderMass` by Marginal B (rfl).
  -- Outer sum is `traceProb` by the cylinder-bijection identity.
  exact extCylinderMass_sum_eq_traceProb sys pe' τ

/-- **Hard direction of `weakClosure_traceProb_eq`**: every trace distribution
achievable by `sys^w` is achievable by `sys`, via the algorithmic witness
`pe_of_weak sys pe'`. Reduces to `pe_of_weak_traceProb`. -/
theorem weakClosure_traceProb_superset (sys : LabelledSystem State Label) :
    achievableTraceDists sys^w ⊆ achievableTraceDists sys := by
  rintro D ⟨pe', hpe'⟩
  refine ⟨pe_of_weak sys pe', ?_⟩
  intro τ
  rw [pe_of_weak_traceProb sys pe' τ]
  exact hpe' τ

/-- **Weak-closure construction preserves trace distributions.** -/
theorem weakClosure_traceProb_eq (sys : LabelledSystem State Label) :
    achievableTraceDists sys = achievableTraceDists sys^w :=
  Set.Subset.antisymm
    (weakClosure_traceProb_subset sys)
    (weakClosure_traceProb_superset sys)

end PLTS
