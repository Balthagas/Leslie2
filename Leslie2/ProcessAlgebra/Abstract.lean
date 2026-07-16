/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.ProcessAlgebra.Composition
import Leslie2.Simulation.Defs
import Leslie2.Weak.WeakChar

/-!
# Simulation-congruence machinery for abstraction

Support lemmas for the precongruence `ProbabilisticForwardSimulation.abstract` (in `Results.lean`).
The abstraction operator `System.abstract` itself lives in `ProcessAlgebra/Composition.lean`; since
abstraction preserves states, the three **lift lemmas** describe how a `sys` weak transition
transports through the relabeling `l ↦ if l ∈ L then τ else l`:

* `weakTau_abstract` — a τ-closure stays a τ-closure (the abstract system has *more* τ-steps);
* `weakTau_of_weakStep_mem` — a weak `l`-step with `l ∈ L` (now hidden) becomes a τ-closure;
* `weakStep_abstract` — a weak `l`-step with `l ∉ L` stays a weak `l`-step.

Because abstraction keeps the same state space, all three follow by *step-relation monotonicity*
(`weakTau_mono`, `hyperStep_mono`, `weakTau_of_hyperStep` in `Weak/WeakChar.lean`) — the witnessing
scheduler is reused verbatim — rather than any scheduler reconstruction.
-/

namespace PLTS

section Abstract

variable {State Label : Type} [Silent Label]

/-- Every `τ`-step of `sys` is a `τ`-step of `sys.abstract L`: if `τ ∉ L` it survives untouched
(right disjunct); if `τ ∈ L` it is a hidden `L`-step relabeled to `τ` (left disjunct). -/
private theorem abstract_tau_step (sys : System State Label) (L : Set Label) {s : State}
    {μ : PMF State} (h : sys.step s Silent.τ μ) : (sys.abstract L).step s Silent.τ μ := by
  by_cases hτ : Silent.τ ∈ L
  · exact Or.inl ⟨rfl, Silent.τ, hτ, h⟩
  · exact Or.inr ⟨hτ, h⟩

/-- A τ-closure of `sys` is still a τ-closure of `sys.abstract L`: abstraction only adds
`τ`-transitions. -/
theorem weakTau_abstract (sys : System State Label) (L : Set Label) {μ ν : PMF State}
    (h : weakTau sys μ ν) : weakTau (sys.abstract L) μ ν :=
  weakTau_mono (fun _ _ hs => abstract_tau_step sys L hs) h

/-- A weak `l`-step of `sys` with `l ∈ L` becomes a τ-closure of `sys.abstract L`: the hidden
visible step is relabeled to `τ`, so the whole weak step collapses into the internal closure. -/
theorem weakTau_of_weakStep_mem (sys : System State Label) (L : Set Label) {μ ν : PMF State}
    {l : Label} (hl : l ∈ L) (h : weakStep sys μ l ν) : weakTau (sys.abstract L) μ ν := by
  obtain ⟨m, m', h1, h2, h3⟩ := h
  have H1 := weakTau_mono (fun _ _ hs => abstract_tau_step sys L hs) h1
  have H2 : weakTau (sys.abstract L) m m' :=
    weakTau_of_hyperStep (hyperStep_mono (fun _ _ hs => Or.inl ⟨rfl, l, hl, hs⟩) h2)
  have H3 := weakTau_mono (fun _ _ hs => abstract_tau_step sys L hs) h3
  exact weakTau_trans (weakTau_trans H1 H2) H3

/-- A weak `l`-step of `sys` with `l ∉ L` is still a weak `l`-step of `sys.abstract L`: the visible
label survives the relabeling. -/
theorem weakStep_abstract (sys : System State Label) (L : Set Label) {μ ν : PMF State}
    {l : Label} (hl : l ∉ L) (h : weakStep sys μ l ν) : weakStep (sys.abstract L) μ l ν := by
  obtain ⟨m, m', h1, h2, h3⟩ := h
  exact ⟨m, m',
    weakTau_mono (fun _ _ hs => abstract_tau_step sys L hs) h1,
    hyperStep_mono (fun _ _ hs => Or.inr ⟨hl, hs⟩) h2,
    weakTau_mono (fun _ _ hs => abstract_tau_step sys L hs) h3⟩

end Abstract

end PLTS
