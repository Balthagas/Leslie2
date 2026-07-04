/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Util.Pmf
import MyMathlibProject.Weak.Step
import MyMathlibProject.Construction.TraceMap

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

Given `sys : System State Label`, lift the state space to `PMF State`.
The lifted system has:

* `init := PMF.pure sys.init` — a Dirac on the original initial state;
* `step μ l ω := hyperStep sys μ l (ω.bind id)` — a transition from
  the pre-distribution `μ` at label `l` to a `PMF (PMF State)` outcome `ω`
  is valid iff the flattened destination `ω.bind id : PMF State` is reachable
  from `μ` via a `hyperStep`.

The internal/external label classification is canonical (the silent label `τ`
from the `Silent Label` instance), shared with `sys` since both are over `Label`.

The PMF wrapper on the post-state slot of `System.step` is "absorbed" by
flattening with `bind id`; the lifted step thus identifies any two
post-state-of-post-state distributions that agree after one bind, which is
the natural identification under the PMF-monad multiplication
`μ : PMF (PMF α) ↦ μ.bind id : PMF α`. -/
noncomputable def System.dist (sys : System State Label) :
    System (PMF State) Label where
  init := PMF.pure sys.init
  step μ l ω := hyperStep sys μ l (ω.bind id)

/-- `𝒟(sys)` is sugar for `System.dist sys`, the distribution-monad
construction lifting `sys` to a labelled system over `PMF State`. -/
scoped notation:max "𝒟(" sys ")" => System.dist sys

/-! ### The distribution-monad construction preserves trace distributions

The subset direction is the functional simulation `s ↦ PMF.pure s` (each
`sys`-step lifts to the corresponding `𝒟(sys)` hyper-step), discharged by
`achievableTraceDists_map`. The reverse (superset) direction is harder: it
flattens genuine `PMF (PMF State)`-randomness from `𝒟(sys)` back into
`pe`-on-`sys` (see `ProbabilisticExecution.lower`). -/

/-- **Subset direction of `dist_traceProb_eq`.** The Dirac embedding
`s ↦ PMF.pure s` is a functional simulation of `sys` by `𝒟(sys)`, hence
preserves achievable trace distributions (`achievableTraceDists_map`). -/
theorem dist_traceProb_subset [Silent Label] (sys : System State Label) :
    achievableTraceDists sys ⊆ achievableTraceDists 𝒟(sys) :=
  achievableTraceDists_map (sys_X := sys) (sys_Y := 𝒟(sys)) PMF.pure rfl
    (fun s l μ h => by
      have hbm : (μ.map PMF.pure).bind id = μ := by rw [PMF.bind_map]; exact PMF.bind_pure μ
      change hyperStep sys (PMF.pure s) l ((μ.map PMF.pure).bind id)
      rw [hbm]; exact hyperStep_pure_of_step h)

end PLTS
