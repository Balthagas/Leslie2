/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.CoreSim
import Leslie2Protocols.ABA.DeployedSim
import Leslie2Protocols.ABA.LayeredSpec

/-!
# The main theorems of the ABA case study

The subject is the deployed protocol `Net.deployed P`: `n` corruption-blind
programs, one per process, beside two boxes that are not processes — the
network adversary, which owns the message pools, the DECIDED pools and the
corrupted set with its budget, and the common-coin oracle, the only factor
whose transitions are not Dirac. A program reads nothing but its own records
and its own inbox; whether a process may be driven off-protocol is decided by
the network's `k ∈ F` guard, never by the program. A program holds one
graded-agreement stage record, that of the round its round loop is in, and the
round advance resets it (D20).

The abstract side is `ABA.spec P`, the single-automaton reading of agreement,
whose traces satisfy Validity and Agreement (`spec_safe`, `SpecSafety.lean`).

## The chain

Three probabilistic forward simulations carry the deployed protocol to the
specification:

1. `deployedSim` (`DeployedSim.lean`) — the deployed protocol into the layered
   presentation, along the Dirac lift of `DepRel`. A layered state carries one
   graded-agreement subsystem per round at every moment, where a deployed
   process node carries only the stage record of the round it is in (D20), so
   the layered side holds strictly more state and the two are related by a
   relation rather than by a map.
2. `substSim` (`LayeredSpec.lean`) — replace each round's graded-agreement
   subsystem by its specification, the other three factors untouched: the
   family substitution carried by four congruences (`parallel_right`,
   `abstract`, `relabel`, `abstract`).
3. `coreSim` (`CoreSim.lean`) — the hand-built simulation of the
   deployment-shaped specification against the ABA specification, read in the
   layered coordinates: the round specifications, the `n` round loops, the
   ABA-side network and the coin oracle, each still a factor of the state the
   relation is defined on.

`refines` chains the soundness inclusions of the three (Result 1) by
`Set.Subset.trans`; `simComposed` composes the three simulations themselves by
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

open Net Layer

/-! ### The chain, link by link

Carry the deployed reading into the layered presentation (`deployed_layered`),
substitute each round's graded-agreement subsystem by its specification at the
deployed shape (`substitution`), then take the core simulation (`coreSim`).
Every step is a simulation between systems the deployed reading itself
names. -/

/-- **The deployment-shaped specification refines the ABA specification**: the
soundness of the core simulation. -/
theorem layeredSpec_spec (P : Params) :
    achievableTraceDists (layeredSpec P) ⊆ achievableTraceDists (spec P) :=
  (coreSim P).achievableTraceDists_subset

/-- **The deployed protocol refines the ABA specification**: the layering, then
the substitution at the deployed shape, then the core simulation. -/
theorem deployed_spec (P : Params) :
    achievableTraceDists (deployed P) ⊆ achievableTraceDists (spec P) :=
  Set.Subset.trans (deployed_layered P)
    (Set.Subset.trans (substitution P) (layeredSpec_spec P))

/-- **Safety of the deployed reading**: every positive-probability trace of
every achievable trace distribution of the `n` programs beside the network
adversary and the coin oracle satisfies Validity and Agreement. The corruption
budget is a guard of the network adversary's own `fail` row, so every deployed
execution is in budget by construction and nothing is assumed of the
traces. -/
theorem deployed_safe (P : Params) :
    ∀ D ∈ achievableTraceDists (deployed P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace t :=
  safety_transfer (deployed_spec P) (spec_safe P)

/-- **Trace conservativity of the deployed reading**: every
positive-probability trace of the deployed protocol has positive probability
under an achievable trace distribution of the deployment-shaped
specification. -/
theorem deployed_traces (P : Params) :
    ∀ D ∈ achievableTraceDists (deployed P), ∀ t, D t ≠ 0 →
      ∃ D' ∈ achievableTraceDists (layeredSpec P), D' t ≠ 0 :=
  fun D hD _ ht => ⟨D, Set.Subset.trans (deployed_layered P) (substitution P) hD, ht⟩

/-- **Safety of the layered presentation**: the substitution and the core
simulation carry the layered reading to the specification, so it inherits the
same guarantee. -/
theorem layered_safe (P : Params) :
    ∀ D ∈ achievableTraceDists (layered P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace t :=
  safety_transfer (Set.Subset.trans (substitution P) (layeredSpec_spec P)) (spec_safe P)

/-! ### The two routes -/

/-- **Trace-distribution refinement** (blueprint `thm:aba-main`, safety
fragment): every trace distribution achievable by the deployed protocol is
achievable by the ABA specification. The layering and the substitution give
the first inclusion, the core simulation the second. -/
theorem refines (P : Params) :
    achievableTraceDists (deployed P) ⊆ achievableTraceDists (spec P) :=
  Set.Subset.trans (deployed_layered P)
    (Set.Subset.trans (substitution P) (layeredSpec_spec P))

/-- **Correctness of ABA** (blueprint `thm:aba-main`, safety fragment):
every positive-probability trace of the deployed protocol satisfies Validity
and Agreement. No side condition on the traces: the corruption budget is a
guard of the network adversary's own `fail` row, so every deployed execution
is in budget by construction. -/
theorem main (P : Params) :
    ∀ D ∈ achievableTraceDists (deployed P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace t :=
  safety_transfer (refines P) (spec_safe P)

/-- **The composed simulation** `deployed ⊑ ABA.spec`: the three simulations of
the chain joined by Result 2 (`ProbabilisticForwardSimulation.trans`), along
the composite of their three relations — the Dirac lift of the layering
relation, the pointwise round substitution, and the core relation. -/
noncomputable def simComposed (P : Params) :
    ProbabilisticForwardSimulation (deployed P) (spec P)
      (compRel (diracRel (DepRel P))
        (compRel (parallelRel (diracRel (RsubAll P))) (coreRel P))) :=
  (deployedSim P).trans ((substSim P).trans (coreSim P))

/-! ### Mechanical axiom firewall

Neither the headlines nor the framework results the chain rests on may acquire
a `sorryAx` dependence. -/

/-- info: 'PLTS.ProbabilisticForwardSimulation.relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ProbabilisticForwardSimulation.relabel

/-- info: 'PLTS.ABA.substitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms substitution

/-- info: 'PLTS.ABA.layeredSpec_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms layeredSpec_spec

/-- info: 'PLTS.ABA.deployed_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deployed_spec

/-- info: 'PLTS.ABA.deployed_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deployed_safe

/-- info: 'PLTS.ABA.deployed_traces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deployed_traces

/-- info: 'PLTS.ABA.layered_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms layered_safe

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
