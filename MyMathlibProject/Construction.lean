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

/-- **Witness pe : ProbabilisticExecution sys.toSystem** constructed
algorithmically from `pe' : ProbabilisticExecution sys^w.toSystem`. -/
private noncomputable def pe_of_weak (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem) :
    ProbabilisticExecution sys.toSystem where
  initState := pe'.initState
  scheduler :=
    { next := fun e =>
        open Classical in
        if h_tm0 : totalMass sys pe' e = 0 then
          -- **Stutter-trap fallback.** From observed `e`, the algorithm
          -- enters infinite stutter with probability 1 (no future visible
          -- action and pe' never halts). We default to `PMF.pure none`,
          -- treating the trap as a halt at `e`.
          --
          -- NOTE: this fallback choice is plausible but not 100% verified.
          -- If trace-coupling proofs fail at the trap case, revisit.
          PMF.pure none
        else
          -- Normalised marginalised PMF:
          --   scheduler.next e (X) := jointUnnorm e X / totalMass e
          -- using `PMF.normalize` on `jointUnnorm sys pe' e`. The function's
          -- tsum equals `totalMass` by construction (mass at `none` is the
          -- joint mass of halt outcomes; mass at `some (l, μ)` integrates
          -- `visible d` outcomes against `d (l, μ)`).
          if h_tm_top : totalMass sys pe' e = ⊤ then
            -- Degenerate `⊤`-mass fallback (also annotated as unverified).
            PMF.pure none
          else
            -- `totalMass` is by definition `∑' opt, jointUnnorm opt`, so the
            -- precondition `(jointUnnorm e).tsum ≠ 0` is `h_tm0`'s negation
            -- (we are in the `else` branch), and similarly for `⊤`.
            PMF.normalize (jointUnnorm sys pe' e) h_tm0 h_tm_top
      valid := by
        intro e n s _h_term _h_state l μ h_supp
        -- `h_supp : some (l, μ) ∈ (next e).support`.
        -- Beta-reduce the lambda and split the if-then-else cases.
        classical
        change some (l, μ) ∈
          ((open Classical in
            if h_tm0 : totalMass sys pe' e = 0 then
              PMF.pure none
            else if h_tm_top : totalMass sys pe' e = ⊤ then
              PMF.pure none
            else
              PMF.normalize (jointUnnorm sys pe' e) h_tm0 h_tm_top)).support at h_supp
        split_ifs at h_supp with h_tm0 h_tm_top
        · -- Stutter-trap fallback: support = {none}, so `some (l, μ)` ∉ support.
          rw [PMF.support_pure] at h_supp
          exact absurd h_supp (by simp)
        · -- ⊤-mass fallback: same.
          rw [PMF.support_pure] at h_supp
          exact absurd h_supp (by simp)
        · -- Main case: support comes from `PMF.normalize jointUnnorm`.
          -- Extract a witness (e_w, d) with positive contribution, then
          -- apply the two helper lemmas.
          rw [PMF.mem_support_iff, PMF.normalize_apply] at h_supp
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
            | none => 0
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

/-- **Marginal identity A** (the corrected sub-lemma A from §5):
summing `jointTight` over the hidden `sys^w`-side pre-iteration history
`e_w_pre` recovers `pe_of_weak`'s prefix probability at every *tight*
terminating `sys`-prefix `e`.

Intuition: every joint trajectory of the coupled algorithm reaches a
given tight `e` at exactly one inner-iteration moment (the moment
right after the visible external step at `e`'s last label, or the
initial moment for the empty `e`). The marginal over the hidden
pre-iteration `e_w_pre` therefore equals `(pe_of_weak …).probOf e`.

(Currently deferred — the proof requires unfolding `pe_of_weak`'s
normalised scheduler, applying `reachProb`'s recursion, and matching
factor-by-factor with `probOf`'s cons-end recursion.) -/
private lemma jointTight_marginal_A
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (e : AlterSeq State Label) (h_e_term : e.trans.Terminates)
    (_h_tight : sys.IsTight e) :
    (∑' e_w_pre : AlterSeq State Label, jointTight sys pe' e_w_pre e) =
      (pe_of_weak sys pe').probOf e h_e_term := by
  sorry

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

/-- **Sub-claim 1 (Step 6): witness-emission marginal.**

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

private lemma witness_emission_marginal
    (sys : LabelledSystem State Label)
    (pe' : ProbabilisticExecution sys^w.toSystem)
    (τ_prev : Seq Label) (l_τ : Label) (_h_τ_prev_term : τ_prev.Terminates)
    (_h_l_τ_external : ¬ sys.internal l_τ)
    (e_w_pre e_iter_start : AlterSeq State Label) :
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
  · -- e_iter_start.trans terminates: proceed to trace case.
    sorry
  · -- e_iter_start.trans doesn't terminate: every tightStepFactor = 0.
    rw [if_neg (by intro h; exact h_iter_term h.2)]
    convert tsum_zero with e
    exact tightStepFactor_eq_zero_of_iter_start_not_terminates sys pe' e_w_pre l_τ
      e_iter_start e.1 h_iter_term

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

Status: deferred. -/
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
  sorry

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
    rw [ENNReal.tsum_mul_left]
    congr 1
    exact witness_emission_marginal sys pe' τ_prev l_τ _h_τ_prev_term h_l_τ_ext
      e_w_pre e_iter_start
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
