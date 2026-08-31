/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.Framework.TraceSupport
import Leslie2.Systems.LTS

/-!
# Idle padding, label pullbacks and ℕ-indexed instance families

The three combinators that make the full-synchronisation `System.parallel`
emulate the blueprint's sync-set composition `∥_S`:

* `System.withIdle sys busy` — `sys` plus idle self-loops `s —l→ δ_s` on every
  label outside `busy`. Under full synchronisation, a non-participant then
  answers every foreign handshake by standing still.

* `System.mapIdle φ sys` — `sys` read over a finer alphabet `L'` along the
  partial label map `φ : L' → Option L`: a label `l'` with `φ l' = some l`
  delegates to the `l`-transitions, and a label outside the image of `φ`
  leaves the system idle. This is how a component that speaks a coarser
  alphabet joins a composition over a finer one.

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

All three combinators preserve `System.IsLTS`, so an LTS instance family is
again an LTS and the `ForwardLTS` bridge applies at family level.

Both weak transitions of a system are carried along `mapIdle` by any *section*
`g` of `φ` that respects the silent label. A section is what makes the
transport trivial on transitions: `φ (g x) = some x` turns every `x`-step into
a `g x`-step of the read-back system, with no condition on which labels occur
in the witness execution. The second hypothesis, `g x = τ ↔ x = τ`, is what
makes it trivial on traces: the transported execution hides exactly the
transitions the original hid, so its trace is the original trace relabelled by
`g` (`System.trace_mapLab`, in `Framework/TraceSupport.lean`).
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

/-- Idle padding preserves the LTS property. -/
theorem System.IsLTS.withIdle {sys : System State Label} (h : sys.IsLTS)
    (busy : Label → Prop) : (sys.withIdle busy).IsLTS := by
  rintro s l μ (hstep | ⟨-, rfl⟩)
  · exact h s l μ hstep
  · exact ⟨s, rfl⟩

/-! ### Pulling a system back along a partial label map -/

/-- Read a system over `L` as a system over `L'`: a label `l'` with
`φ l' = some l` delegates to the `l`-transitions, and a label outside the
image of `φ` leaves the system idle. -/
def System.mapIdle {S L L' : Type} (φ : L' → Option L) (sys : System S L) :
    System S L' where
  init := sys.init
  step s l' μ :=
    match φ l' with
    | some l => sys.step s l μ
    | none => μ = PMF.pure s

@[simp] theorem System.mapIdle_init {S L L' : Type} (φ : L' → Option L)
    (sys : System S L) : (sys.mapIdle φ).init = sys.init := rfl

theorem System.mapIdle_step {S L L' : Type} (φ : L' → Option L) (sys : System S L)
    (s : S) (l' : L') (μ : PMF S) :
    (sys.mapIdle φ).step s l' μ ↔
      (∃ l, φ l' = some l ∧ sys.step s l μ) ∨ (φ l' = none ∧ μ = PMF.pure s) := by
  change (match φ l' with
        | some l => sys.step s l μ
        | none => μ = PMF.pure s) ↔ _
  cases hφ : φ l' with
  | none => simp
  | some l => simp

/-- Delegated labels read off the underlying system. -/
theorem System.mapIdle_step_some {S L L' : Type} {φ : L' → Option L}
    {sys : System S L} {s : S} {l' : L'} {l : L} (hφ : φ l' = some l)
    (μ : PMF S) : (sys.mapIdle φ).step s l' μ ↔ sys.step s l μ := by
  rw [System.mapIdle_step]
  simp [hφ]

/-- Unmapped labels are idle self-loops. -/
theorem System.mapIdle_step_none {S L L' : Type} {φ : L' → Option L}
    {sys : System S L} {s : S} {l' : L'} (hφ : φ l' = none) (μ : PMF S) :
    (sys.mapIdle φ).step s l' μ ↔ μ = PMF.pure s := by
  rw [System.mapIdle_step]
  simp [hφ]

/-- **`mapIdle` preserves the LTS property**: a delegated label keeps the
underlying system's distribution, an idle one is a Dirac by construction. -/
theorem System.mapIdle_isLTS {S L L' : Type} (φ : L' → Option L)
    {sys : System S L} (h : sys.IsLTS) : (sys.mapIdle φ).IsLTS := by
  intro s l' μ hstep
  rw [System.mapIdle_step] at hstep
  rcases hstep with ⟨l, -, hs⟩ | ⟨-, rfl⟩
  · exact h s l μ hs
  · exact ⟨s, rfl⟩

section MapIdleWeak

variable {S L L' : Type} [Silent L] [Silent L'] {sys : System S L}
  {φ : L' → Option L} {s s' : S}

/-- **A silent weak run survives the read-back**: `q =ε=> q'` of `sys` is
`q =ε=> q'` of `sys.mapIdle φ`, the witness execution relabelled along a
section `g` of `φ`. -/
theorem System.weakLSilent_mapIdle (g : L → L') (hsec : ∀ x, φ (g x) = some x)
    (hgτ : ∀ x, g x = (Silent.τ : L') ↔ x = (Silent.τ : L))
    (h : sys.weakLSilent s s') : (sys.mapIdle φ).weakLSilent s s' := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := h
  refine ⟨e.mapLab g, (AlterSeq.mapLab_trans_terminates_iff g e).mpr hterm,
    is_partial_exec_mapLab g
      (fun _ x _ hx => (System.mapIdle_step_some (hsec x) _).mpr hx) hpe,
    hinit, ?_, ?_⟩
  · rw [AlterSeq.endState_mapLab g e hterm]; exact hend
  · rw [System.trace_mapLab _ sys g hgτ, htr, Stream'.Seq.map_nil]

/-- **A labelled weak run survives the read-back**: `q =l=> q'` of `sys` is
`q =l'=> q'` of `sys.mapIdle φ` at any label `l'` the section `g` puts over
`l`. -/
theorem System.weakLStep_mapIdle (g : L → L') (hsec : ∀ x, φ (g x) = some x)
    (hgτ : ∀ x, g x = (Silent.τ : L') ↔ x = (Silent.τ : L))
    {l : L} {l' : L'} (hgl : g l = l') (h : sys.weakLStep s l s') :
    (sys.mapIdle φ).weakLStep s l' s' := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := h
  refine ⟨e.mapLab g, (AlterSeq.mapLab_trans_terminates_iff g e).mpr hterm,
    is_partial_exec_mapLab g
      (fun _ x _ hx => (System.mapIdle_step_some (hsec x) _).mpr hx) hpe,
    hinit, ?_, ?_⟩
  · rw [AlterSeq.endState_mapLab g e hterm]; exact hend
  · rw [System.trace_mapLab _ sys g hgτ, htr, Stream'.Seq.map_cons,
      Stream'.Seq.map_nil, hgl]

end MapIdleWeak

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
