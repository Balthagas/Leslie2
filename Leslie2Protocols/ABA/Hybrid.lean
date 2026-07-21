/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Results
import Leslie2Protocols.ABA.Core
import Leslie2Protocols.ABA.GBCAFamily
import Leslie2Protocols.ABA.WCCSpec

/-!
# The ABA hybrids and the substitution step

The two composed systems of the case study and the substitution inclusion
between them:

* `hybridImpl` — `GBCA.implFamily ∥ (ABA.core ∥ WCC.specFamily)`, sub-protocol
  API hidden. The "real" system (up to WCC being held at spec level).
* `hybridSpec` — the same with `GBCA.implFamily` replaced by
  `GBCA.specFamily`. The system the hand-built core simulation (M6) relates
  to `ABA.spec`.

GBCA sits in the **left** (refinable) slot of `System.parallel`, so the
substitution is literally the composition of the three precongruence results:
`GBCA.familyRefines` lifted by `parallel_right` (Result 3) under the fixed
context, then by `abstract` (Result 5), then soundness (Result 1) yields the
trace-distribution inclusion. No transitivity of simulations is involved.
-/

namespace PLTS
namespace ABA

/-- The fixed composition context: the ABA coordinator alongside the
spec-level WCC family. -/
noncomputable def context (P : Params) :
    System (CoreState P.n × (ℕ → WCC.SpecState P.n)) (Lab P.n) :=
  (core P).parallel (WCC.specFamily P)

/-- The implementation-side hybrid: GBCA at implementation level, WCC at spec
level, sub-protocol API hidden. -/
noncomputable def hybridImpl (P : Params) :
    System ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))
      (Lab P.n) :=
  ((GBCA.implFamily P).parallel (context P)).abstract (Lab.hiddenAPI P.n)

/-- The specification-side hybrid: GBCA replaced by its specification. -/
noncomputable def hybridSpec (P : Params) :
    System ((ℕ → GBCA.SpecState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))
      (Lab P.n) :=
  ((GBCA.specFamily P).parallel (context P)).abstract (Lab.hiddenAPI P.n)

/-- **The substitution simulation** (blueprint `lem:ABASubst`, minus
fairness): replacing `GBCA.implFamily` by `GBCA.specFamily` under the fixed
context is a probabilistic forward simulation — precongruence for `parallel`
(Result 3) and `abstract` (Result 5) applied to the GBCA family refinement. -/
noncomputable def substSim (P : Params) :
    ProbabilisticForwardSimulation (hybridImpl P) (hybridSpec P)
      (parallelRel (diracRel (fun s t => ∀ r, GBCA.instRel P r (s r) (t r)))) :=
  ((GBCA.familyRefines P).parallel_right (context P)).abstract (Lab.hiddenAPI P.n)

/-- **The substitution inclusion**: every trace distribution achievable by
the implementation-side hybrid is achievable by the spec-side hybrid
(Result 1 applied to `substSim`). -/
theorem substitution (P : Params) :
    achievableTraceDists (hybridImpl P) ⊆ achievableTraceDists (hybridSpec P) :=
  (substSim P).achievableTraceDists_subset

end ABA
end PLTS
