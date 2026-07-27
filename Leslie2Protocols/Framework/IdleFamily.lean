/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2.Systems.LTS

/-!
# Idle-padding and ℕ-indexed instance families

The two combinators that make the full-synchronisation `System.parallel`
emulate the blueprint's sync-set composition `∥_S`:

* `System.withIdle sys busy` — `sys` plus idle self-loops `s —l→ δ_s` on every
  label outside `busy`. Under full synchronisation, a non-participant then
  answers every foreign handshake by standing still.

* `System.family inst owns glob act` — the ℕ-indexed family of instances
  `inst r` over a shared alphabet, with **three** step disjuncts (plus idling):
  1. *silent or owned*: on `τ`, or on a label owned by round `r`
     (`owns l = some r`), exactly the one instance moves; the joint successor
     distribution is `μr.map (Function.update s r ·)` — no product PMFs arise.
  2. *global broadcast* (`glob l`, e.g. corruption `fail id`): every instance
     applies the deterministic transform `act l` simultaneously (a Dirac
     step). This is what keeps per-instance copies of shared bookkeeping (the
     corrupted set) in lockstep — a single-coordinate step could not.
  3. *foreign* (unowned, non-global): a global idle self-loop.

  The broadcast disjunct applies `act` unconditionally (it is not required to
  be justified by instance steps); the intended `act`s are total corruption
  functions in the style of deviation D1.

Both combinators preserve `System.IsLTS`, so an LTS instance family is again
an LTS and the `ForwardLTS` bridge applies at family level.
-/

namespace PLTS

variable {State σ Label : Type}

/-! ### Idle padding -/

/-- `sys` with idle self-loops on every label outside `busy`. -/
def System.withIdle (sys : System State Label) (busy : Label → Prop) :
    System State Label where
  init := sys.init
  step s l μ := sys.step s l μ ∨ (¬ busy l ∧ μ = PMF.pure s)

@[simp] theorem System.withIdle_init (sys : System State Label) (busy : Label → Prop) :
    (sys.withIdle busy).init = sys.init := rfl

theorem System.withIdle_step_iff (sys : System State Label) (busy : Label → Prop)
    {s : State} {l : Label} {μ : PMF State} :
    (sys.withIdle busy).step s l μ ↔
      sys.step s l μ ∨ (¬ busy l ∧ μ = PMF.pure s) := Iff.rfl

/-- Idle padding preserves the LTS property. -/
theorem System.IsLTS.withIdle {sys : System State Label} (h : sys.IsLTS)
    (busy : Label → Prop) : (sys.withIdle busy).IsLTS := by
  rintro s l μ (hstep | ⟨-, rfl⟩)
  · exact h s l μ hstep
  · exact ⟨s, rfl⟩

/-! ### ℕ-indexed instance families -/

variable [Silent Label]

/-- The ℕ-indexed family of the instances `inst r` over a shared alphabet.
`owns` assigns API labels to their instance, `glob` marks broadcast labels
(corruption), `act` is the deterministic broadcast transform. -/
def System.family (inst : ℕ → System σ Label)
    (owns : Label → Option ℕ) (glob : Label → Prop) (act : Label → σ → σ) :
    System (ℕ → σ) Label where
  init := fun r => (inst r).init
  step s l μ :=
    (l = Silent.τ ∧ ∃ r μr, (inst r).step (s r) l μr ∧
      μ = μr.map (Function.update s r)) ∨
    ((∃ r, owns l = some r ∧ ∃ μr, (inst r).step (s r) l μr ∧
      μ = μr.map (Function.update s r))) ∨
    (¬ l = Silent.τ ∧ owns l = none ∧ glob l ∧
      μ = PMF.pure (fun r => act l (s r))) ∨
    (¬ l = Silent.τ ∧ owns l = none ∧ ¬ glob l ∧ μ = PMF.pure s)

@[simp] theorem System.family_init (inst : ℕ → System σ Label)
    (owns : Label → Option ℕ) (glob : Label → Prop) (act : Label → σ → σ) :
    (System.family inst owns glob act).init = fun r => (inst r).init := rfl

/-- The step disjunction of `System.family`, by name. -/
theorem System.family_step_iff (inst : ℕ → System σ Label)
    (owns : Label → Option ℕ) (glob : Label → Prop) (act : Label → σ → σ)
    {s : ℕ → σ} {l : Label} {μ : PMF (ℕ → σ)} :
    (System.family inst owns glob act).step s l μ ↔
      (l = Silent.τ ∧ ∃ r μr, (inst r).step (s r) l μr ∧
        μ = μr.map (Function.update s r)) ∨
      ((∃ r, owns l = some r ∧ ∃ μr, (inst r).step (s r) l μr ∧
        μ = μr.map (Function.update s r))) ∨
      (¬ l = Silent.τ ∧ owns l = none ∧ glob l ∧
        μ = PMF.pure (fun r => act l (s r))) ∨
      (¬ l = Silent.τ ∧ owns l = none ∧ ¬ glob l ∧ μ = PMF.pure s) := Iff.rfl

/-- A family of LTS instances is an LTS: every disjunct's successor
distribution is a Dirac (single-coordinate updates of Diracs included). -/
theorem System.family_isLTS {inst : ℕ → System σ Label}
    (h : ∀ r, (inst r).IsLTS)
    (owns : Label → Option ℕ) (glob : Label → Prop) (act : Label → σ → σ) :
    (System.family inst owns glob act).IsLTS := by
  rintro s l μ (⟨-, r, μr, hstep, rfl⟩ | ⟨r, -, μr, hstep, rfl⟩ |
    ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩)
  · obtain ⟨x, rfl⟩ := h r _ _ _ hstep
    exact ⟨Function.update s r x, by rw [PMF.pure_map]⟩
  · obtain ⟨x, rfl⟩ := h r _ _ _ hstep
    exact ⟨Function.update s r x, by rw [PMF.pure_map]⟩
  · exact ⟨_, rfl⟩
  · exact ⟨s, rfl⟩

end PLTS
