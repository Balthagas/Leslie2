/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2.ProcessAlgebra.Abstract
import Leslie2.Systems.LTS

/-!
# Extended alphabets and restriction along the left summand

A composition often needs labels that only exist to make its components
rendezvous — round tags, per-process handshakes, internal acknowledgements —
which the composite is not meant to expose. The idiom is to build the components
over the **extended alphabet** `Label ⊕ Extra`, where `Label` is the alphabet the
composite shares with everything else and `Extra` carries the auxiliary labels;
`System.abstract` (in `ProcessAlgebra/Composition.lean`) then hides the `Sum.inr`
labels as `τ`, and `System.relabel` transports the result back to `Label`:

* `System.relabel sys : System State Label` keeps the state space of
  `sys : System State (Label ⊕ Extra)` and retains exactly its `Sum.inl`-labelled
  transitions.

For that pipeline to typecheck, the extended alphabet needs its own silent label.
The instance `PLTS.instSilentSum` takes it to be `Sum.inl τ`, so that `τ` on
`Label ⊕ Extra` and `τ` on `Label` name the same transitions across `relabel`,
and every auxiliary label `Sum.inr e` is observable (hence hideable by
`abstract`).

Restriction discards transitions rather than states, so it preserves
`System.IsLTS` (`System.relabel_isLTS`).
-/

namespace PLTS

variable {State Label Extra : Type}

/-- The silent label of an extended alphabet `Label ⊕ Extra` is the silent label
of the base alphabet, injected on the left. Every auxiliary label `Sum.inr e` is
therefore observable. -/
instance instSilentSum [Silent Label] : Silent (Label ⊕ Extra) := ⟨Sum.inl Silent.τ⟩

namespace System

/-- **Restriction along the left embedding.** `sys.relabel` reads a system over
the extended alphabet `Label ⊕ Extra` as a system over `Label`: the state space
and the initial state are unchanged, and the transitions on `l` are exactly the
`Sum.inl l`-transitions of `sys`. Transitions labelled by an auxiliary
`Sum.inr e` are discarded — abstract them to `τ` first if they are to survive. -/
def relabel (sys : System State (Label ⊕ Extra)) : System State Label where
  init := sys.init
  step s l μ := sys.step s (Sum.inl l) μ

@[simp] theorem relabel_init (sys : System State (Label ⊕ Extra)) :
    (sys.relabel).init = sys.init := rfl

@[simp] theorem relabel_step (sys : System State (Label ⊕ Extra))
    (s : State) (l : Label) (μ : PMF State) :
    (sys.relabel).step s l μ ↔ sys.step s (Sum.inl l) μ := Iff.rfl

/-- Restriction preserves the LTS property: its transitions are a sub-collection
of those of `sys`, so they still all lead to Diracs. -/
theorem relabel_isLTS {sys : System State (Label ⊕ Extra)} (h : sys.IsLTS) :
    (sys.relabel).IsLTS :=
  fun s l μ hstep => h s (Sum.inl l) μ hstep

end System

/-- Abstraction preserves the LTS property: it relabels transitions and keeps
each one's distribution. -/
theorem System.abstract_isLTS {State Label : Type} [Silent Label]
    {sys : System State Label} (h : sys.IsLTS) (L : Set Label) :
    (sys.abstract L).IsLTS := by
  rintro s l μ (⟨-, l', -, hstep⟩ | ⟨-, hstep⟩) <;> exact h s _ μ hstep

end PLTS
