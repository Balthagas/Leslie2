/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Model.Trace

/-!
# Fairness

Fairness assumptions on a PLTS, in the **sure** reading. A *fairness marking* (`Fairness sys`)
designates some transitions of `sys` as *fair*, subject to the constraint that only internal
(`τ`) transitions may be unfair — every external transition is automatically fair.

## Resolved-history schedulers are the model for fairness

Fairness of a run depends on *which transition the scheduler chose*, not only on the visited
states and labels: two transitions `(s, l, μ₁)` (fair) and `(s, l, μ₂)` (unfair) can produce the
very same plain step `(l, s')` when their supports overlap. Fairness is therefore stated on
**resolved executions** (`ResolvedExec`), whose steps record the full chosen transition `(l, μ)`
alongside the sampled next state.

More is true: even the *set of achievable fair trace distributions* depends on whether the
scheduler is allowed to consult the chosen `μ`s. Plain schedulers (consulted on the visited
states/labels only) and **resolved-history** schedulers (consulted on the full `μ`-history) induce
**different** sure-fair achievable sets, and this already happens for image-finite systems (the
worked separator lives in `Model/ResolvedGap.lean`). The resolved-history scheduler is the correct
notion, so **the canonical fair achievable set `fairAchievableTraceDists` is defined here in terms
of resolved-history schedulers** (`ResolvedScheduler` / `ResolvedProbabilisticExecution`). The
weaker plain-scheduler notion is retained, only for the comparison, in
`Model/ResolvedScheduler.lean` (`fairAchievableTraceDistsPlain`).

## Contents

* A **resolved-history scheduler** (`ResolvedScheduler`) is consulted on the full resolved history
  `ResolvedExec State Label`; a `ResolvedProbabilisticExecution` pairs it with an initial
  distribution. `probOfR` / `traceProbR` are its path-measure and trace distribution.
* A **fair deadlock** (`Fairness.FairDeadlock`) is a state from which no fair transition is enabled.
* A resolved execution is **fair** (`Fairness.IsFairExec`) when either it is finite and its last
  state is a fair deadlock, or it is infinite and infinitely many of its steps take a fair
  transition.
* A resolved execution is **consistent** with a resolved probabilistic execution
  (`ResolvedProbabilisticExecution.Consistent`) when its start state has positive initial mass and
  each chosen transition lies in the support of the scheduler at the preceding resolved prefix, with
  the sampled next state in the support of the chosen distribution.
* A resolved probabilistic execution is **fair** (`ResolvedProbabilisticExecution.IsFair`) when
  it schedules `none` only from a fair deadlock and every consistent (maximal) run is fair.
* `fairAchievableTraceDists` is the fairness-constrained analogue of `achievableTraceDists`.
-/

open Stream'

namespace PLTS

variable {State Label : Type}

/-! ### Finite prefixes and resolved executions -/

/-- The finite prefix of an execution consisting of its first `n` transitions. -/
def AlterSeq.take (e : AlterSeq State Label) (n : ℕ) : AlterSeq State Label :=
  ⟨e.init, Seq.ofList (e.trans.take n)⟩

/-- A **resolved execution**: an execution whose steps record the full transition `(l, μ)` chosen
by the scheduler alongside the sampled next state. This is the object on which fairness of a run
is well defined — a plain execution does not remember *which* transition produced each step, and
the same `(l, s')` step can come from both a fair and an unfair transition. -/
abbrev ResolvedExec (State Label : Type) : Type := AlterSeq State (Label × PMF State)

/-- The plain execution underlying a resolved execution: forget the chosen distributions, keeping
the `(label, next state)` pairs. This is the history the plain scheduler is consulted on. -/
def ResolvedExec.toExec (r : ResolvedExec State Label) : AlterSeq State Label :=
  ⟨r.init, r.trans.map fun p => (p.1.1, p.2)⟩

/-! ### The resolved-history scheduler

The default `Scheduler` (`Model/System.lean`) is consulted on the **plain** history
`AlterSeq State Label` — the visited states and labels, but *not* the transition distributions
`μ` that were actually sampled. The **resolved-history** scheduler is consulted on the full
`ResolvedExec State Label` (states, labels, *and* the chosen `μ`s). This is the notion of scheduler
used to define the fair achievable set below. -/

/-- A **resolved-history** scheduler: like `Scheduler`, but its `next` sees the full resolved
history `ResolvedExec State Label` (recording the chosen `μ`s), not just the plain history. The
validity obligation is the analogue of `Scheduler.valid`, phrased on the resolved history's current
state (`r.stateAt`). -/
structure ResolvedScheduler (sys : System State Label) where
  /-- The next-step distribution given the full resolved history. -/
  next : ResolvedExec State Label → PMF (Option (Label × PMF State))
  /-- Emissions in the support of a `some` output are valid `sys`-steps from the current state. -/
  valid : ∀ (r : ResolvedExec State Label) (n : ℕ) (s : State),
    r.trans.TerminatedAt n → r.stateAt n = some s →
    ∀ (l : Label) (μ : PMF State),
      some (l, μ) ∈ (next r).support → sys.step s l μ

/-- A probabilistic execution driven by a resolved-history scheduler. -/
structure ResolvedProbabilisticExecution (sys : System State Label) where
  /-- The unique initial distribution. -/
  initState : PMF State
  /-- The resolved-history scheduler. -/
  scheduler : ResolvedScheduler sys

namespace ResolvedProbabilisticExecution

variable {sys : System State Label}

/-- The one-step **resolved** kernel: unlike the plain kernel this does *not* sum over `μ` (the
resolved step `((l, μ), s')` names `μ` explicitly). -/
noncomputable def rkernel (pe : ResolvedProbabilisticExecution sys)
    (r : ResolvedExec State Label) (step : (Label × PMF State) × State) : ENNReal :=
  pe.scheduler.next r (some step.1) * step.1.2 step.2

/-- The probability that the resolved execution `pe` produces the finite **resolved** execution `r`,
in the same cons-end recursion as `ProbabilisticExecution.probOf` but with `rkernel`. -/
noncomputable def probOfR (pe : ResolvedProbabilisticExecution sys)
    (r : ResolvedExec State Label) (hFin : r.trans.Terminates) : ENNReal :=
  (r.trans.toList hFin).reverseRecOn
    (motive := fun _ => ENNReal)
    (pe.initState r.init)
    (fun rest last ih => ih * pe.rkernel ⟨r.init, Seq.ofList rest⟩ last)

@[simp] theorem probOfR_nil (pe : ResolvedProbabilisticExecution sys) (s₀ : State) :
    pe.probOfR ⟨s₀, Seq.nil⟩ Stream'.Seq.terminates_nil = pe.initState s₀ := by
  unfold probOfR
  simp [Stream'.Seq.toList_nil]

/-- **Cons-end factorisation** for `probOfR` (mirrors `probOf_append_singleton`). -/
theorem probOfR_append_singleton (pe : ResolvedProbabilisticExecution sys)
    (s₀ : State) (sq : Seq ((Label × PMF State) × State)) (h_sq : sq.Terminates)
    (last : (Label × PMF State) × State)
    (h_app : (sq.append (Seq.cons last Seq.nil)).Terminates) :
    pe.probOfR ⟨s₀, sq.append (Seq.cons last Seq.nil)⟩ h_app =
      pe.probOfR ⟨s₀, sq⟩ h_sq * pe.rkernel ⟨s₀, sq⟩ last := by
  unfold probOfR
  have h_singleton_term : (Seq.cons last Seq.nil : Seq ((Label × PMF State) × State)).Terminates :=
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
  have h_toList : (sq.append (Seq.cons last Seq.nil)).toList h_app =
      sq.toList h_sq ++ [last] := by
    rw [Stream'.Seq.toList_append sq (Seq.cons last Seq.nil) h_sq h_singleton_term h_app]
    congr 1
    rw [Stream'.Seq.toList_cons]
    simp [Stream'.Seq.toList_nil]
  rw [show (⟨s₀, sq.append (Seq.cons last Seq.nil)⟩ :
        ResolvedExec State Label).trans.toList h_app = sq.toList h_sq ++ [last] from h_toList]
  rw [List.reverseRecOn_concat]
  rw [Stream'.Seq.ofList_toList sq h_sq]

variable [Silent Label]

/-- The set of trace distributions produced by resolved executions, summing `probOfR` over the
resolved executions whose *plain image* `r.toExec` is a tight, terminating execution with trace `τ`.
The mirror of `System.traceProb`. -/
noncomputable def traceProbR (pe : ResolvedProbabilisticExecution sys) (τ : Seq Label) : ENNReal :=
  ∑' r : {r : ResolvedExec State Label //
      r.trans.Terminates ∧ sys.trace r.toExec = τ ∧ sys.IsTight r.toExec},
    pe.probOfR r.1 r.2.1

end ResolvedProbabilisticExecution

/-! ### Fairness markings -/

variable [Silent Label]

/-- A **fairness marking** on `sys`: a set of transitions designated *fair* (a map from
transitions to `Prop`, so `fair` implies `step`), subject to the constraint that only internal
(`τ`) transitions can be unfair — every external transition is fair. -/
structure Fairness (sys : System State Label) where
  /-- The transitions of `sys` marked as fair. -/
  fair : State → Label → PMF State → Prop
  /-- Fair transitions are transitions of `sys`. -/
  step_of_fair : ∀ s l μ, fair s l μ → sys.step s l μ
  /-- Only internal (`τ`) transitions can be unfair: every external transition is fair. -/
  fair_of_external : ∀ s l μ, sys.step s l μ → l ≠ Silent.τ → fair s l μ

namespace Fairness

variable {sys : System State Label} (F : Fairness sys)

/-- A fair transition is **enabled** at `s`: some fair transition leaves `s`. -/
def FairEnabled (s : State) : Prop := ∃ l μ, F.fair s l μ

/-- A **fair deadlock**: a state from which no fair transition is enabled. -/
def FairDeadlock (s : State) : Prop := ¬ F.FairEnabled s

/-- The `n`-th step of the resolved execution `r` takes a **fair** transition: the transition
`(l, μ)` recorded at position `n` is fair from the state at position `n`. -/
def FairStepAt (r : ResolvedExec State Label) (n : ℕ) : Prop :=
  ∃ (s : State) (l : Label) (μ : PMF State) (s' : State),
    r.stateAt n = some s ∧ r.trans.get? n = some ((l, μ), s') ∧ F.fair s l μ

/-- A resolved execution is **fair** when either
* it is finite and its last state is a fair deadlock, or
* it is infinite and infinitely many of its steps take a fair transition. -/
def IsFairExec (r : ResolvedExec State Label) : Prop :=
  (∃ h : r.trans.Terminates, F.FairDeadlock (r.endState h)) ∨
    (¬ r.trans.Terminates ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ F.FairStepAt r n)

end Fairness

/-! ### Consistency and fair resolved schedulers -/

namespace ResolvedProbabilisticExecution

variable {sys : System State Label}

/-- A resolved execution `r` is **consistent** with `pe`: positive initial mass, and each recorded
transition lies in the support of `pe.scheduler.next` at the *resolved* prefix. Consistent resolved
executions are exactly the runs `pe` can produce, with the scheduler's choices spelled out. -/
def Consistent (pe : ResolvedProbabilisticExecution sys) (r : ResolvedExec State Label) : Prop :=
  pe.initState r.init ≠ 0 ∧
    ∀ (n : ℕ) (l : Label) (μ : PMF State) (s' : State),
      r.trans.get? n = some ((l, μ), s') →
        pe.scheduler.next (r.take n) (some (l, μ)) ≠ 0 ∧ μ s' ≠ 0

variable [Silent Label]

/-- A resolved probabilistic execution `pe` is **fair** for the marking `F` when
* (`halt_fairDeadlock`) it schedules `none` (halts) only from a fair deadlock — so every finite
  consistent run at which it halts ends at a fair deadlock, and
* (`inf_fair`) every infinite consistent run takes infinitely many fair transitions.

Together these say: every *maximal* consistent run of `pe` (infinite, or finite and halted) is a
fair resolved execution (`Fairness.IsFairExec`). -/
structure IsFair (F : Fairness sys) (pe : ResolvedProbabilisticExecution sys) : Prop where
  /-- Halting (`none`) happens only from a fair deadlock. -/
  halt_fairDeadlock : ∀ (r : ResolvedExec State Label) (h : r.trans.Terminates),
    pe.Consistent r → pe.scheduler.next r none ≠ 0 → F.FairDeadlock (r.endState h)
  /-- Every infinite consistent run takes infinitely many fair transitions. -/
  inf_fair : ∀ r : ResolvedExec State Label, ¬ r.trans.Terminates → pe.Consistent r →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ F.FairStepAt r n

end ResolvedProbabilisticExecution

/-! ### Fair achievable trace distributions -/

/-- The set of trace distributions achievable by some **fair** resolved-history probabilistic
execution of `sys` started from the Dirac initial distribution — the fairness-constrained analogue
of `achievableTraceDists`. This is *the* fair achievable set: it is defined via resolved-history
schedulers, which strictly extend the plain-scheduler notion
(`fairAchievableTraceDistsPlain`, in `Model/ResolvedScheduler.lean`) even for image-finite systems
(see `Model/ResolvedGap.lean`). -/
def fairAchievableTraceDists {sys : System State Label} (F : Fairness sys) :
    Set (Seq Label → ENNReal) :=
  {D | ∃ pe : ResolvedProbabilisticExecution sys,
    pe.initState = PMF.pure sys.init ∧ pe.IsFair F ∧ ∀ τ, pe.traceProbR τ = D τ}

end PLTS
