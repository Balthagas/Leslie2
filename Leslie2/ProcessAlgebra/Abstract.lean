/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.ProcessAlgebra.Composition
import Leslie2.Simulation.Defs

/-!
# Simulation-congruence machinery for abstraction

Support lemmas for the precongruence `ProbabilisticForwardSimulation.abstract` (in `Results.lean`).
The abstraction operator `System.abstract` itself lives in `ProcessAlgebra/Composition.lean`; since
abstraction preserves states, the crux is three **lift lemmas** (currently `sorry`) describing how a
`sys` weak transition transports through the relabeling `l ↦ if l ∈ L then τ else l`:

* `weakTau_abstract` — a τ-closure stays a τ-closure (the abstract system has *more* τ-steps);
* `weakTau_of_weakStep_mem` — a weak `l`-step with `l ∈ L` (now hidden) becomes a τ-closure;
* `weakStep_abstract` — a weak `l`-step with `l ∉ L` stays a weak `l`-step.
-/

namespace PLTS

section Abstract

variable {State Label : Type} [Silent Label]

/-- A τ-closure of `sys` is still a τ-closure of `sys.abstract L`: abstraction only adds
`τ`-transitions. -/
theorem weakTau_abstract (sys : System State Label) (L : Set Label) {μ ν : PMF State}
    (h : weakTau sys μ ν) : weakTau (sys.abstract L) μ ν := by
  sorry

/-- A weak `l`-step of `sys` with `l ∈ L` becomes a τ-closure of `sys.abstract L`: the hidden
visible step is relabeled to `τ`, so the whole weak step collapses into the internal closure. -/
theorem weakTau_of_weakStep_mem (sys : System State Label) (L : Set Label) {μ ν : PMF State}
    {l : Label} (hl : l ∈ L) (h : weakStep sys μ l ν) : weakTau (sys.abstract L) μ ν := by
  sorry

/-- A weak `l`-step of `sys` with `l ∉ L` is still a weak `l`-step of `sys.abstract L`: the visible
label survives the relabeling. -/
theorem weakStep_abstract (sys : System State Label) (L : Set Label) {μ ν : PMF State}
    {l : Label} (hl : l ∉ L) (h : weakStep sys μ l ν) : weakStep (sys.abstract L) μ l ν := by
  sorry

end Abstract

end PLTS
