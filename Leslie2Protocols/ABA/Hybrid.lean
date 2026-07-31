/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2.Results
import Leslie2Protocols.ABA.Core
import Leslie2Protocols.ABA.GBCAFamily
import Leslie2Protocols.ABA.WCCSpec

/-!
# The analysis-side composition

The system the hand-built core simulation takes as its subject:

* `context` — the ABA coordinator `core` alongside the spec-level WCC family:
  the two factors the graded-agreement side is composed with, fixed once.
* `hybridSpec` — `GBCA.specFamily ∥ context` with the sub-protocol API hidden.
  Both sub-protocols are read at specification level, so the round loop's
  environment is exactly the two oracles it calls — the graded-agreement
  oracle and the common coin — and the composite speaks the shared alphabet
  `Lab n`.

`CoreSim.lean` relates `hybridSpec` to the ABA specification `spec`; the
deployed protocol reaches `hybridSpec` from the deployment-shaped
specification by a repartition of state (`flatSpecSim`, `ABA/FlatSpec.lean`).
Nothing here mentions the deployed coordinates: those are
`ABA/FlatNetwork.lean`'s.

The graded-agreement family sits in the **left** (refinable) slot of
`System.parallel`, so a substitution under this fixed context is the
composition of the precongruence results — `parallel_right` (Result 3) then
`abstract` (Result 5) — with soundness (Result 1) turning the resulting
simulation into a trace-distribution inclusion. No transitivity of simulations
is involved.
-/

namespace PLTS
namespace ABA

/-- The fixed composition context: the ABA coordinator alongside the
spec-level WCC family. -/
noncomputable def context (P : Params) :
    System (CoreState P.n × (ℕ → WCC.SpecState P.n)) (Lab P.n) :=
  (core P).parallel (WCC.specFamily P)

/-- **The analysis-side composition**: the graded-agreement family at
specification level beside the context, sub-protocol API hidden. -/
noncomputable def hybridSpec (P : Params) :
    System ((ℕ → GBCA.SpecState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))
      (Lab P.n) :=
  ((GBCA.specFamily P).parallel (context P)).abstract (Lab.hiddenAPI P.n)

end ABA
end PLTS
