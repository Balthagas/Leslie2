/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Model.System

/-!
# Parallel composition of PLTS (CSP-style)

Given two systems `sys₁ : System State₁ Label` and `sys₂ : System State₂ Label`
over a common label alphabet, together with a synchronization set
`sync : Set Label`, this file defines the CSP-style parallel composition
`sys₁.parallel sys₂ sync : System (State₁ × State₂) Label`.

Semantics:
* A joint state `(s₁, s₂)` is initial iff `sys₁.init s₁ ∧ sys₂.init s₂`.
* On a label `l ∈ sync`, both components must step simultaneously with the same
  label; the joint next-state distribution is the independent product of the
  two component distributions.
* On a label `l ∉ sync`, exactly one component steps; the other stays put
  (its state is held by a Dirac distribution).

When `sync = Set.univ`, this is fully synchronous lockstep composition; when
`sync = ∅`, this is pure interleaving.
-/

namespace PLTS

variable {State₁ State₂ Label : Type}

/-- The independent product of two PMFs. -/
noncomputable def prodPMF (μ₁ : PMF State₁) (μ₂ : PMF State₂) :
    PMF (State₁ × State₂) :=
  μ₁.bind fun s₁ => μ₂.bind fun s₂ => PMF.pure (s₁, s₂)

namespace System

/-- CSP-style parallel composition of two PLTS over a common label alphabet,
synchronising on labels in `sync ⊆ Label`. -/
def parallel (sys₁ : System State₁ Label) (sys₂ : System State₂ Label)
    (sync : Set Label) : System (State₁ × State₂) Label where
  init := (sys₁.init, sys₂.init)
  step p l μ :=
    -- Synchronised step: `l ∈ sync` and both components step.
    (l ∈ sync ∧
      ∃ μ₁ μ₂, sys₁.step p.1 l μ₁ ∧ sys₂.step p.2 l μ₂ ∧ μ = prodPMF μ₁ μ₂) ∨
    -- Left interleaved step: `l ∉ sync`, only `sys₁` steps.
    (l ∉ sync ∧
      ∃ μ₁, sys₁.step p.1 l μ₁ ∧ μ = prodPMF μ₁ (PMF.pure p.2)) ∨
    -- Right interleaved step: `l ∉ sync`, only `sys₂` steps.
    (l ∉ sync ∧
      ∃ μ₂, sys₂.step p.2 l μ₂ ∧ μ = prodPMF (PMF.pure p.1) μ₂)

end System

end PLTS
