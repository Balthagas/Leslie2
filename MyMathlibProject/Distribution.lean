/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.WeakStep

/-!
# Distribution-monad construction

Lift a labelled PLTS `sys` to a new labelled PLTS whose state space is
`PMF State` (the free PMF on `State`) and whose steps are exactly the
`hyperStep`s of `sys`. The construction is denoted `𝒟(sys)`, and it is
designed to leave the set of achievable trace distributions invariant.
-/

open Stream'

namespace PLTS

variable {α β State State_C State_A Label : Type}

/-! ## The distribution-monad construction

Lift a labelled PLTS `sys` to a new labelled PLTS whose state space is
`PMF State` (the free PMF on `State`) and whose steps are exactly the
`hyperStep`s of `sys`. -/

/-- The **distribution-monad construction** on a labelled PLTS.

Given `sys : LabelledSystem State Label`, lift the state space to `PMF State`.
The lifted system has:

* `init := PMF.pure sys.init` — a Dirac on the original initial state;
* `step μ l ω := hyperStep sys μ l (ω.bind id)` — a transition from
  the pre-distribution `μ` at label `l` to a `PMF (PMF State)` outcome `ω`
  is valid iff the flattened destination `ω.bind id : PMF State` is reachable
  from `μ` via a `hyperStep`;
* `internal := sys.internal` — the label classification is inherited.

The PMF wrapper on the post-state slot of `System.step` is "absorbed" by
flattening with `bind id`; the lifted step thus identifies any two
post-state-of-post-state distributions that agree after one bind, which is
the natural identification under the PMF-monad multiplication
`μ : PMF (PMF α) ↦ μ.bind id : PMF α`. -/
noncomputable def LabelledSystem.dist (sys : LabelledSystem State Label) :
    LabelledSystem (PMF State) Label where
  init := PMF.pure sys.init
  step μ l ω := hyperStep sys μ l (ω.bind id)
  internal := sys.internal

/-- `𝒟(sys)` is sugar for `LabelledSystem.dist sys`, the distribution-monad
construction lifting `sys` to a labelled system over `PMF State`. -/
scoped notation:max "𝒟(" sys ")" => LabelledSystem.dist sys

/-! ### The distribution-monad construction preserves trace distributions

Both directions are non-trivial: lifting a `pe` over `sys` to `𝒟(sys)`
requires reshaping `pe`'s scheduler signature to operate on histories over
`PMF State` (with Dirac-state lifts of each transition), while the reverse
direction requires flattening genuine `PMF (PMF State)`-randomness from
`𝒟(sys)` back into `pe`-on-`sys`. Both are deferred. -/

/-- **Subset direction of `dist_traceProb_eq`** (deferred). -/
theorem dist_traceProb_subset (sys : LabelledSystem State Label) :
    achievableTraceDists sys ⊆ achievableTraceDists 𝒟(sys) := by
  sorry

/-- **Superset direction of `dist_traceProb_eq`** (deferred). -/
theorem dist_traceProb_superset (sys : LabelledSystem State Label) :
    achievableTraceDists 𝒟(sys) ⊆ achievableTraceDists sys := by
  sorry

/-- **Distribution-monad construction preserves trace distributions.** -/
theorem dist_traceProb_eq (sys : LabelledSystem State Label) :
    achievableTraceDists sys = achievableTraceDists 𝒟(sys) :=
  Set.Subset.antisymm
    (dist_traceProb_subset sys)
    (dist_traceProb_superset sys)

end PLTS
