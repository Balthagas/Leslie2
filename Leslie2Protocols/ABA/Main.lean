/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.CoreSim
import Leslie2Protocols.ABA.SpecSafety

/-!
# The main theorems of the ABA case study

The final deliverables, assembled from the substitution step (`Hybrid.lean`),
the core simulation (`CoreSim.lean`), and spec safety (`SpecSafety.lean`):

* `ABA.refines` — trace-distribution inclusion of the implementation-side
  hybrid in the ABA specification: Result 1 applied to each of the two
  simulations separately, chained by transitivity of `⊆` (independent of the
  transitivity of probabilistic forward simulation).
* `ABA.main` — every trace in the support of every achievable trace
  distribution of the implementation-side hybrid satisfies Validity and
  Agreement.
* `ABA.simComposed` — the single composed simulation
  `hybridImpl ⊑ ABA.spec`, via `ProbabilisticForwardSimulation.trans`
  (Result 2). Originally this routed through the repo's one `sorry`
  (`weakTau_lift_pure`); that lemma is now closed upstream
  (`WeakTauFlatten.lean`), so `simComposed` is **fully proven and
  axiom-clean** with zero changes to its definition here.

The `#guard_msgs`/`#print axioms` checks below are the mechanical firewall:
`main` must never acquire a `sorryAx` dependence.
-/

namespace PLTS
namespace ABA

/-- **Trace-distribution refinement** (blueprint `thm:ABASim`, safety
fragment): every trace distribution achievable by the implementation-side
hybrid is achievable by the ABA specification: the two
simulation soundness inclusions are chained by `Set.Subset.trans`. -/
theorem refines (P : Params) :
    achievableTraceDists (hybridImpl P) ⊆ achievableTraceDists (spec P) :=
  Set.Subset.trans (substitution P) (coreSim P).achievableTraceDists_subset

/-- **Correctness of ABA** (blueprint `thm:ABACorrect`, safety fragment):
every positive-probability trace of the implementation-side hybrid satisfies
Validity and Agreement. -/
theorem main (P : Params) :
    ∀ D ∈ achievableTraceDists (hybridImpl P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace t :=
  safety_transfer (refines P) (spec_safe P)

/-- **The composed simulation** `hybridImpl ⊑ ABA.spec` along the composite
relation, via Result 2 (`ProbabilisticForwardSimulation.trans`). Fully proven:
`weakTau_lift_pure` is closed upstream, so this carries no `sorryAx`
(see the axiom guard below). -/
noncomputable def simComposed (P : Params) :
    ProbabilisticForwardSimulation (hybridImpl P) (spec P)
      (compRel
        (parallelRel (diracRel (fun s t => ∀ r, GBCA.instRel P r (s r) (t r))))
        (coreRel P)) :=
  (substSim P).trans (coreSim P)

/-! ### Mechanical axiom firewall

`main` (and the whole safety chain) must never acquire a `sorryAx`
dependence; `simComposed` is likewise pinned to the clean axiom list now
that `weakTau_lift_pure` is closed upstream. -/

/-- info: 'PLTS.ABA.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main

/-- info: 'PLTS.ABA.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refines

/-- info: 'PLTS.ABA.simComposed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms simComposed

end ABA
end PLTS
