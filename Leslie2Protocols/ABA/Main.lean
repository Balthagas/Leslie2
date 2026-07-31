/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.FlatSpec

/-!
# The main theorems of the ABA case study

The subject is the deployed protocol `Net.netFlat P`: `n` corruption-blind
programs, one per process, beside two boxes that are not processes — the
network adversary, which owns the message pools, the DECIDED pools and the
corrupted set with its budget, and the common-coin oracle, the only factor
whose transitions are not Dirac. A program reads nothing but its own records
and its own inbox; whether a process may be driven off-protocol is decided by
the network's `k ∈ F` guard, never by the program.

The abstract side is `ABA.spec P`, the single-automaton reading of agreement,
whose traces satisfy Validity and Agreement (`spec_safe`, `SpecSafety.lean`).

## The chain

Four probabilistic forward simulations carry the deployed protocol to the
specification:

1. `explodedSim` (`Exploded.lean`) — re-cut the deployed state so that a
   *layer* boundary is a *component* boundary: the family of graded-agreement
   round subsystems, the `n` round loops, the DECIDED layer beside the
   corrupted set, and the coin oracle. The re-cut is exact in both directions
   (`exploded_atd`).
2. `substSimX` (`FlatSpec.lean`) — replace each round's graded-agreement
   subsystem by its specification, the other three factors untouched: the
   family substitution carried by four congruences (`parallel_right`,
   `abstract`, `relabel`, `abstract`).
3. `flatSpecSim` (`FlatSpec.lean`) — repartition the two ABA-side factors into
   the monolithic coordinator state, reaching `hybridSpec`.
4. `coreSim` (`CoreSim.lean`) — the hand-built simulation of the coordinator
   against the specification.

`refines` chains the soundness inclusions of the four (Result 1) by
`Set.Subset.trans`; `simComposed` composes the four simulations themselves by
`ProbabilisticForwardSimulation.trans` (Result 2). The two routes are
independent — the inclusion never invokes transitivity of simulation.

## Scope of the headline

Graded agreement is carried to implementation level: each round is a group of
stage programs beside that round's own message fabric, driven by the same
network adversary. The **common coin is held at specification level** — the
ε-coin is `Params.wccPMF`, not a Gather/SRSD implementation — so the honest
reading is *graded agreement verified to implementation level; the coin
assumed at specification level*.

`ValidityTrace` (`SpecSafety.lean`) is the paper-form predicate: a decided bit
must carry a provenance clause witnessed by a *never-corrupted*
(`NeverCorrupted`) supporter, matching the papers' correct-process Validity.
What is proven is safety — Validity and Agreement for every
positive-probability trace. Termination, liveness, unpredictability and
fairness are not claimed.

The `#guard_msgs`/`#print axioms` blocks below are the mechanical firewall:
the headlines, and the framework results the chain rests on, are pinned to the
clean axiom list `[propext, Classical.choice, Quot.sound]`.
-/

namespace PLTS
namespace ABA

open Net

/-- **Trace-distribution refinement** (blueprint `thm:aba-main`, safety
fragment): every trace distribution achievable by the deployed protocol is
achievable by the ABA specification. The explosion and the substitution give
the first inclusion, the repartition and the core simulation the second. -/
theorem refines (P : Params) :
    achievableTraceDists (netFlat P) ⊆ achievableTraceDists (spec P) :=
  Set.Subset.trans (netFlat_flatSpec P) (flatSpec_spec P)

/-- **Correctness of ABA** (blueprint `thm:aba-main`, safety fragment):
every positive-probability trace of the deployed protocol satisfies Validity
and Agreement. No side condition on the traces: the corruption budget is a
guard of the network adversary's own `fail` row, so every deployed execution
is in budget by construction. -/
theorem main (P : Params) :
    ∀ D ∈ achievableTraceDists (netFlat P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace t :=
  safety_transfer (refines P) (spec_safe P)

/-- **The composed simulation** `netFlat ⊑ ABA.spec`: the four simulations of
the chain joined by Result 2 (`ProbabilisticForwardSimulation.trans`), along
the composite of their four relations — the graph of the regrouping, the
pointwise round substitution, the graph of the spec-side repartition, and the
core relation. -/
noncomputable def simComposed (P : Params) :
    ProbabilisticForwardSimulation (netFlat P) (spec P)
      (compRel (fun s ν => ν = PMF.pure (regroup s))
        (compRel (parallelRel (diracRel (RsubAll P)))
          (compRel (fun s ν => ν = PMF.pure (flatSpecDefl P s)) (coreRel P)))) :=
  (explodedSim P).trans ((substSimX P).trans ((flatSpecSim P).trans (coreSim P)))

/-! ### Mechanical axiom firewall

Neither the headlines nor the framework results the chain rests on may acquire
a `sorryAx` dependence. -/

/-- info: 'PLTS.ABA.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main

/-- info: 'PLTS.ABA.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refines

/-- info: 'PLTS.ABA.simComposed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms simComposed

/-- info: 'PLTS.ProbabilisticForwardSimulation.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ProbabilisticForwardSimulation.trans

/-- info: 'PLTS.weakTau_lift_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weakTau_lift_pure

/-- info: 'PLTS.weakTau_flatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weakTau_flatten

end ABA
end PLTS
