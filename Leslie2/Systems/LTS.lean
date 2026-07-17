/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Systems.Trace

/-!
# Labelled transition systems (LTS) as non-probabilistic PLTS

A **labelled transition system (LTS)** is the non-probabilistic special case of a
`PLTS.System`: a system in which every transition leads to a *Dirac* (point-mass)
distribution. Rather than introducing a separate structure — which would force a
`.toSystem` coercion everywhere and duplicate the entire trace / simulation
machinery — we model an LTS as a `System` together with the *predicate*
`System.IsLTS`. Every existing result about `System` (traces,
`achievableTraceDists`, the three simulations) then applies to an LTS with no
coercion.

* `System.IsLTS sys` asserts that each step `s -[l]→ μ` of `sys` has
  `μ = PMF.pure s'` for some target state `s'`.
* `System.LStep sys s l s'` is the induced *non-probabilistic* one-step relation
  `s -[l]→ s'` (reaching the point mass on `s'`). Under `IsLTS` the probabilistic
  `step` and this relation carry the same information (`System.IsLTS.step_iff`).
* `System.weakLStep sys q l q'` is the **weak** transition `q =l=> q'`: a finite
  execution from `q` to `q'` whose observable trace is the single label `l` (the
  usual `τ*·l·τ*` transition, phrased on states). It is deliberately distinct from
  the PLTS `weakStep` / `weakTau`, which act on distributions.

Note that an LTS may still be *nondeterministic*: a state can have several
outgoing `LStep`s for the same label. What `IsLTS` rules out is only genuine
*randomness* — the target of each individual transition is a single state.

## Roadmap

The point of singling out LTS is to compare the two forms of forward simulation
on them. The eventual goal is:

> for LTS `sys_C` and `sys_A`, a (non-probabilistic) forward simulation exists iff
> a `ProbabilisticForwardSimulation` (`Simulation/SimDefs.lean`) exists.

This file lays out the LTS definition, its induced weak transition, and their
immediate API; the forward-simulation equivalence is developed on top of it.
-/

open Stream'

namespace PLTS

variable {State Label : Type}

/-- A `System` is a **labelled transition system (LTS)** — i.e. non-probabilistic
— when every transition leads to a Dirac (point-mass) distribution: each step
`s -[l]→ μ` satisfies `μ = PMF.pure s'` for some target state `s'`.

Modelled as a predicate on `System` (rather than a bundled structure) so that the
whole `System` toolbox — traces, `achievableTraceDists`, the simulations — carries
over to an LTS with no coercion. -/
def System.IsLTS (sys : System State Label) : Prop :=
  ∀ s l μ, sys.step s l μ → ∃ s', μ = PMF.pure s'

/-- The **non-probabilistic one-step relation** of a system: `sys.LStep s l s'`
holds iff `sys` has a transition `s -[l]→ PMF.pure s'` to the point mass on `s'`.

This is the natural transition relation of an LTS. It is defined for an arbitrary
`System`, but only captures *all* of `sys`'s behaviour when `sys.IsLTS` (see
`System.IsLTS.step_iff`). -/
def System.LStep (sys : System State Label) (s : State) (l : Label) (s' : State) : Prop :=
  sys.step s l (PMF.pure s')

/-- An `LStep` is, unfolded, a `step` to the corresponding Dirac distribution.
A definitional repackaging, provided so downstream code can read off the
underlying probabilistic transition by name. -/
theorem System.LStep.step {sys : System State Label} {s : State} {l : Label} {s' : State}
    (h : sys.LStep s l s') : sys.step s l (PMF.pure s') := h

/-- **Interchange of the two views under `IsLTS`.** For an LTS, a transition
`s -[l]→ μ` is exactly an `LStep` to some target `s'` with `μ` the Dirac on `s'`:
the probabilistic `step` and the non-probabilistic `LStep` carry the same
information. -/
theorem System.IsLTS.step_iff {sys : System State Label} (h : sys.IsLTS)
    (s : State) (l : Label) (μ : PMF State) :
    sys.step s l μ ↔ ∃ s', μ = PMF.pure s' ∧ sys.LStep s l s' := by
  constructor
  · intro hstep
    obtain ⟨s', rfl⟩ := h s l μ hstep
    exact ⟨s', rfl, hstep⟩
  · rintro ⟨s', rfl, hL⟩
    exact hL

/-! ### Weak transitions of an LTS -/

section WeakTransition

variable [Silent Label]

/-- A **weak transition** `q =l=> q'` of a system `sys`: a *finite* execution of
`sys` from `q` to `q'` whose observable trace is the single label `l`. Concretely
there is a terminating `AlterSeq` `e` with

* `is_partial_exec e sys` — every transition of `e` is a genuine `sys`-step;
* `e.init = q` and `e.endState = q'` — the run goes from `q` to `q'`;
* `sys.trace e = [l]` — after dropping the internal (`τ`) labels exactly `l`
  remains.

So `q =l=> q'` is the usual `τ*·l·τ*` weak transition of transition-system
theory, phrased directly on states (no distributions). Although stated for an
arbitrary `System`, it is intended for an LTS (`sys.IsLTS`).

**Not to be confused with the PLTS weak transitions.** `PLTS.weakStep` and
`PLTS.weakTau` (`Weak/WeakTransition.lean`) act on *distributions* `PMF State`
via halting-mass schedulers; `weakLStep` acts on *states* and merely asserts that
a finite trace-`l` run exists. On an LTS these are meant to agree under the Dirac
identification, but they are kept as separate notions.

For an internal label `l = Silent.τ` this is unsatisfiable, since `trace` omits
`τ`; internal steps are instead matched by the *silent* weak transition
`q =ε=> q'` (`System.weakLSilent`, below). -/
def System.weakLStep (sys : System State Label) (q : State) (l : Label) (q' : State) : Prop :=
  ∃ (e : AlterSeq State Label) (h : e.trans.Terminates),
    is_partial_exec e sys ∧ e.init = q ∧ e.endState h = q' ∧
      sys.trace e = (Seq.cons l Seq.nil : Seq Label)

/-- The **silent weak transition** `q =ε=> q'` of a system `sys`: a *finite*
execution of `sys` from `q` to `q'` whose observable trace is **empty** — a pure
`τ*`-run (any number, possibly zero, of internal steps). It is the internal-label
counterpart of `System.weakLStep`, and the state-level analogue of `PLTS.weakTau`.

Unlike `weakLStep`, it is always satisfiable: it is **reflexive**
(`System.weakLSilent_refl`), the empty execution `⟨q, nil⟩` witnessing `q =ε=> q`.
This reflexivity is exactly what lets a forward simulation match a concrete
internal step by leaving the abstract state put (stuttering). -/
def System.weakLSilent (sys : System State Label) (q : State) (q' : State) : Prop :=
  ∃ (e : AlterSeq State Label) (h : e.trans.Terminates),
    is_partial_exec e sys ∧ e.init = q ∧ e.endState h = q' ∧
      sys.trace e = (Seq.nil : Seq Label)

/-- The silent weak transition is **reflexive**: `q =ε=> q`, witnessed by the
empty execution `⟨q, nil⟩` (no transitions, empty trace). -/
theorem System.weakLSilent_refl (sys : System State Label) (q : State) :
    sys.weakLSilent q q := by
  refine ⟨⟨q, Seq.nil⟩, Stream'.Seq.terminates_nil, ?_, rfl, ?_, ?_⟩
  · intro n l s' hn
    rw [Stream'.Seq.get?_nil] at hn
    exact absurd hn (by simp)
  · exact AlterSeq.endState_of_trans_nil _ rfl _
  · exact sys.trace_init q

end WeakTransition

end PLTS
