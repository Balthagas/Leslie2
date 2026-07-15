/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.DistMonad.DistMonad
import Leslie2.Other.Pmf
import Leslie2.Weak.Step
import Leslie2.Simulation.TraceMap

/-!
# Inverting the distribution-monad lift: the disintegration kernel

The first stage of `dist_traceProb_eq` (`DistMonad/DistTrace.lean`): the kernel
`ProbabilisticExecution.distHyperKernel` that turns a `𝒟(sys)`-execution back into a
`sys`-hyperstep, and its marginal decomposition. Used by the belief-cone construction in
`DistTraceBelief.lean`.
-/

open Stream'

namespace PLTS

variable {α β State State_C State_A Label : Type}

/-! ### Inverting the lift: from `𝒟(sys)`-execution back to `sys`-execution

The superset direction converts a `𝒟(sys)`-probabilistic execution `pe'` into a
`sys`-probabilistic execution with the same trace distribution.

A `𝒟(sys)`-transition `μ -[l]→ ω` is a `hyperStep sys μ l (ω.bind id)`, which
decomposes — via a witness `p : State → PMF (PMF State)` — into per-state
`sys`-steps: for `s ∈ μ.support`, every `μ' ∈ (p s).support` satisfies
`sys.step s l μ'` (no internal stutter). `distHyperKernel` selects such a `p`.

The `sys`-witness `ProbabilisticExecution.lower` runs the decomposition: at
`sys`-state `s` it samples a `𝒟(sys)`-history `E` from the **trace-cone belief**
`beliefTC` (conditioned only on the current trace and on `s`), draws
`(l, ω) ∼ pe'.scheduler.next E`, and steps by `distHyperKernel E l ω s`. Trace
preservation rests on the invariant `ρ_σ = (Ω_σ).bind id`, preserved one step at
a time by `hyperStep_marginal_decomp` (see `lower_traceProb_eq`).

A naive witness conditioning on the *full* `sys`-history instead of the
trace-cone fails: it over-conditions on intermediate states and does not
preserve trace distributions. -/

/-- The per-state hyperStep kernel of `pe'.scheduler.next E` at emission
`(l, ω)`. When `(l, ω)` lies in the support of `pe'.scheduler.next E` and
`E` terminates, `pe'.scheduler.valid` yields
`hyperStep sys (E.endState) l (ω.bind id)`; we classically choose a per-state
successor kernel from this witness. Outside that case the value is irrelevant
(downstream uses are multiplied by zero). -/
noncomputable def ProbabilisticExecution.distHyperKernel
    {sys : System State Label}
    (_pe' : ProbabilisticExecution 𝒟(sys))
    (E : AlterSeq (PMF State) Label) (l : Label) (ω : PMF (PMF State)) :
    State → PMF (PMF State) :=
  open Classical in
  if h : ∃ hE : E.trans.Terminates,
      hyperStep sys (E.endState hE) l (ω.bind id) then
    (h.choose_spec).kernel
  else
    fun _ => PMF.pure (ω.bind id)

/-- **Validity of `distHyperKernel`.** At an emission `(l, ω)` in the
support of `pe'.scheduler.next E` (with `E` finite), every distribution
in `(distHyperKernel pe' E l ω s).support` for `s ∈ (E.endState hE).support`
is a valid `sys.step` post-distribution from `s`. This is the per-state
`hyperStep.kernel_step` repackaged for the constructed scheduler's
validity proof. -/
theorem ProbabilisticExecution.distHyperKernel_step
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys))
    {E : AlterSeq (PMF State) Label} (hE : E.trans.Terminates)
    {l : Label} {ω : PMF (PMF State)}
    (h_supp : some (l, ω) ∈ (pe'.scheduler.next E).support)
    {s : State} (h_s : s ∈ (E.endState hE).support)
    {μ : PMF State}
    (h_μ : μ ∈ (pe'.distHyperKernel E l ω s).support) :
    sys.step s l μ := by
  classical
  -- Invoke `pe'.scheduler.valid` at canonical termination position to extract
  -- `𝒟(sys).step (E.endState hE) l ω = hyperStep sys (E.endState hE) l (ω.bind id)`.
  have h_hyper : hyperStep sys (E.endState hE) l (ω.bind id) := by
    have := pe'.scheduler.valid E (Nat.find hE) (E.endState hE)
      (Nat.find_spec hE) (AlterSeq.stateAt_find_eq_endState E hE) l ω h_supp
    -- `this : 𝒟(sys).step (E.endState hE) l ω`
    -- By definition `𝒟(sys).step = fun μ l ω => hyperStep sys μ l (ω.bind id)`.
    exact this
  -- The existential in `distHyperKernel` holds; the value is `h_hyper'.kernel`
  -- for some classically chosen `h_hyper'`. The kernel_step lemma applies.
  have hex : ∃ hE' : E.trans.Terminates,
      hyperStep sys (E.endState hE') l (ω.bind id) := ⟨hE, h_hyper⟩
  have h_def : pe'.distHyperKernel E l ω = hex.choose_spec.kernel := by
    unfold ProbabilisticExecution.distHyperKernel
    rw [dif_pos hex]
  rw [h_def] at h_μ
  -- Now `h_μ : μ ∈ (hex.choose_spec.kernel s).support`. Need `s ∈ μ_pre.support`
  -- where `μ_pre = E.endState hex.choose`. Since `hex.choose` and `hE` are both
  -- proofs of `E.trans.Terminates`, they're propositionally equal (Prop).
  have h_choose : hex.choose = hE := Subsingleton.elim _ _
  -- Apply `hyperStep.kernel_step`.
  have h_kstep := hex.choose_spec.kernel_step
  -- `h_kstep : ∀ s' ∈ (E.endState hex.choose).support, ∀ μ' ∈ (kernel s').support,
  --              sys.step s' l μ'`
  rw [h_choose] at h_kstep
  exact h_kstep s h_s μ h_μ

/-- **Hyperstep marginal decomposition.** For a 𝒟(sys)-scheduler emission
`(l, ω)` at a terminating history `E`, the post-state marginal of `ω`
decomposes as the state-wise mixture of the per-state hyperStep-kernel
bind:
```
(ω.bind id) q = ∑' s, (E.endState hE) s · ((distHyperKernel E l ω s).bind id) q
```
This is the `μ_post = μ_pre.bind (fun s => (p s).bind id)` conjunct of the
hyperStep witness, restated in terms of `distHyperKernel`. It is the bridge
identity behind the one-step trace-cone invariant (`lower_traceProb_eq`).

Proof outline: from `pe'.scheduler.valid` extract a hyperStep witness for
`hyperStep sys (E.endState hE) l (ω.bind id)`. The witness's
`post_eq_bind` conjunct gives the equality. Reconcile the
classically-chosen `distHyperKernel` with the scheduler-extracted kernel
via `Subsingleton.elim` on `Terminates` proofs (as in
`distHyperKernel_step`). -/
theorem ProbabilisticExecution.hyperStep_marginal_decomp
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys))
    {E : AlterSeq (PMF State) Label} (hE : E.trans.Terminates)
    {l : Label} {ω : PMF (PMF State)}
    (h_supp : some (l, ω) ∈ (pe'.scheduler.next E).support)
    (q : State) :
    (ω.bind id) q
      = ∑' s : State, (E.endState hE) s *
          ((pe'.distHyperKernel E l ω s).bind id) q := by
  classical
  -- Extract hyperStep witness from `pe'.scheduler.valid`.
  have h_hyper : hyperStep sys (E.endState hE) l (ω.bind id) := by
    have := pe'.scheduler.valid E (Nat.find hE) (E.endState hE)
      (Nat.find_spec hE) (AlterSeq.stateAt_find_eq_endState E hE) l ω h_supp
    change hyperStep sys (E.endState hE) l (ω.bind id) at this
    exact this
  -- The existential in `distHyperKernel` holds; expose the classical kernel.
  have hex : ∃ hE' : E.trans.Terminates,
      hyperStep sys (E.endState hE') l (ω.bind id) := ⟨hE, h_hyper⟩
  have h_def : pe'.distHyperKernel E l ω = hex.choose_spec.kernel := by
    unfold ProbabilisticExecution.distHyperKernel
    rw [dif_pos hex]
  -- post_eq_bind: `(ω.bind id) = (E.endState hex.choose).bind (fun s => (kernel s).bind id)`.
  have h_post := hex.choose_spec.post_eq_bind
  have h_choose : hex.choose = hE := Subsingleton.elim _ _
  -- Evaluate at q.
  conv_lhs => rw [h_post]
  rw [PMF.bind_apply]
  -- Goal: `∑' s, (E.endState hex.choose) s * ((kernel s).bind id) q
  --     = ∑' s, (E.endState hE) s * ((distHyperKernel E l ω s).bind id) q`.
  apply tsum_congr
  intro s
  rw [h_choose, h_def]


end PLTS
