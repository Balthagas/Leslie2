/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2Protocols.ABA.CoreSim
import Leslie2Protocols.ABA.SpecSafety

/-!
# The main theorems of the ABA case study

The final deliverables, assembled from the substitution step (`Hybrid.lean`),
the core simulation (`CoreSim.lean`), and spec safety (`SpecSafety.lean`):

* `ABA.refines` — trace-distribution inclusion of the implementation-side
  hybrid in the ABA specification. **Sorry-free**: Result 1 applied to each of
  the two simulations separately, chained by transitivity of `⊆` — the
  (sorried) transitivity of probabilistic forward simulation is never used.
* `ABA.main` — every trace in the support of every achievable trace
  distribution of the implementation-side hybrid satisfies Validity and
  Agreement. **Sorry-free.**
* `ABA.simComposed` — the single composed simulation
  `hybridImpl ⊑ ABA.spec`, via `ProbabilisticForwardSimulation.trans`
  (Result 2). This deliberately routes through the repo's one `sorry`
  (`weakTau_lift_pure`); it will become fully proven, with zero changes here,
  when that lemma is closed. The axiom guard below documents the dependence
  (and will pleasantly fail the build when the `sorry` disappears — update it
  to the clean list then).

The `#guard_msgs`/`#print axioms` checks below are the mechanical firewall:
`main` must never acquire a `sorryAx` dependence.
-/

namespace PLTS
namespace ABA

/-- **Trace-distribution refinement** (blueprint `thm:ABASim`, safety
fragment): every trace distribution achievable by the implementation-side
hybrid is achievable by the ABA specification. Sorry-free: the two
simulation soundness inclusions are chained by `Set.Subset.trans`. -/
theorem refines (P : Params) :
    achievableTraceDists (hybridImpl P) ⊆ achievableTraceDists (spec P) :=
  Set.Subset.trans (substitution P) (coreSim P).achievableTraceDists_subset

/-- **Correctness of ABA** (blueprint `thm:ABACorrect`, safety fragment):
every positive-probability trace of the implementation-side hybrid satisfies
Validity and Agreement. Sorry-free. -/
theorem main (P : Params) :
    ∀ D ∈ achievableTraceDists (hybridImpl P), ∀ t, D t ≠ 0 →
      ValidityTrace t ∧ AgreementTrace t :=
  safety_transfer (refines P) (spec_safe P)

/-- **The composed simulation** `hybridImpl ⊑ ABA.spec` along the composite
relation, via Result 2 (`ProbabilisticForwardSimulation.trans`). Currently
inherits the `weakTau_lift_pure` `sorry` (see the module docstring). -/
noncomputable def simComposed (P : Params) :
    ProbabilisticForwardSimulation (hybridImpl P) (spec P)
      (compRel
        (parallelRel (diracRel (fun s t => ∀ r, GBCA.instRel P r (s r) (t r))))
        (coreRel P)) :=
  (substSim P).trans (coreSim P)

/-! ### Mechanical axiom firewall

`main` (and the whole safety chain) must never acquire a `sorryAx`
dependence; `simComposed`'s expected `sorryAx` is pinned so that closing
`weakTau_lift_pure` upstream flags this file for the (welcome) update. -/

/-- info: 'PLTS.ABA.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main

/-- info: 'PLTS.ABA.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refines

/-- info: 'PLTS.ABA.simComposed' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms simComposed

end ABA
end PLTS
