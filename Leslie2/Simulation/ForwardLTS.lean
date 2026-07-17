/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Systems.LTS
import Leslie2.Simulation.SimDefs

/-!
# Forward simulation of an LTS is a probabilistic forward simulation

The "easy" direction of the LTS forward-simulation equivalence: if two LTS
`sys_1`, `sys_2` are related by a (non-probabilistic) `ForwardSimulation` `R`
(`Systems/LTS.lean`) whose initial states are related, then the Dirac lift of `R`
is a `ProbabilisticForwardSimulation` (`Simulation/SimDefs.lean`).

The content is a bridge between the two *weak-transition* notions:

* the LTS state-level `System.weakLStep` / `System.weakLSilent`, defined as finite
  executions, and
* the PLTS distribution-level `weakStep` / `weakTau`, defined via halting-mass
  schedulers.

On an LTS every step is a Dirac, so a finite execution `q =l=> q'` decomposes into
single Dirac steps that compose — through `weakTau_of_step`, `weakTau_trans`, and
`hyperStep_pure_of_step` — into `weakStep sys (pure q) l (pure q')` (and likewise
`weakLSilent` into `weakTau`). These bridges (`weakStep_of_weakLStep`,
`weakTau_of_weakLSilent`) are proved by induction on the execution's transition
list.

This file lives in the `Simulation` layer (it imports `Simulation/SimDefs`); the
LTS definitions themselves stay in the base-layer `Systems/LTS.lean`.
-/

open Stream'

namespace PLTS

variable {State Label : Type} [Silent Label]

/-! ### Forward simulation between PLTS -/

section ForwardSimulation

variable {State_1 State_2 : Type} [Silent Label]

/-- A **forward simulation of `sys_1` by `sys_2`** along a state relation
`R : State_1 → State_2 → Prop`. Stated between arbitrary PLTS for generality,
though it is meant to be used between LTS (`System.IsLTS`).

`R` is a forward simulation when every concrete transition is matched by an
abstract **weak** transition preserving `R`: for every `R`-related pair
`(q_1, q_2)`, every concrete step `q_1 -[l]→ μ_1`, and every outcome
`q_1' ∈ μ_1.support`, there is an abstract target `q_2'` with `R q_1' q_2'`
reached by

* the silent weak transition `q_2 =ε=> q_2'` (`System.weakLSilent`) when `l` is
  internal (`l = Silent.τ`) — in particular the abstract side may stay put; or
* the labelled weak transition `q_2 =l=> q_2'` (`System.weakLStep`) when `l` is
  external.

The case split on `(l = Silent.τ)` is essential: a τ-step must be matched by an
*empty*-trace run, not by a trace-`[l]` run (which is impossible, as `trace`
drops τ). It mirrors the internal/external split of
`ProbabilisticForwardSimulation` (`Simulation/SimDefs.lean`), which chooses
between `weakTau` and `weakStep`.

Note the asymmetry: the concrete side ranges over the *support* of the
distribution `μ_1` — each individual outcome must be matched — while the abstract
side answers with a single state-to-state weak transition. This is the
non-probabilistic ("forward") simulation; contrast
`ProbabilisticForwardSimulation`, whose matching is a coupling of distributions.
The eventual goal is that, on LTS, the two notions coincide.

Following the stated definition, this records only the transfer (`step`)
condition; relating the initial states is left as a separate requirement. -/
structure ForwardSimulation
    (sys_1 : System State_1 Label) (sys_2 : System State_2 Label)
    (R : State_1 → State_2 → Prop) where
  step : ∀ q_1 q_2, R q_1 q_2 →
    ∀ l μ_1, sys_1.step q_1 l μ_1 →
    ∀ q_1' ∈ μ_1.support,
      ∃ q_2',
        (((l = Silent.τ) ∧ sys_2.weakLSilent q_2 q_2') ∨
         (¬ (l = Silent.τ) ∧ sys_2.weakLStep q_2 l q_2')) ∧
        R q_1' q_2'

end ForwardSimulation

/-! ### Execution-surgery helpers (front-cons decomposition) -/

omit [Silent Label] in
/-- `Option.elim` of `getLast?` peels the head: the last element of `x :: M` is
read from `M` (falling back to `x`'s second component when `M` is empty). -/
private theorem getLast?_elim_cons (x : Label × State) (M : List (Label × State)) (d : State) :
    ((x :: M).getLast?).elim d Prod.snd = (M.getLast?).elim x.2 Prod.snd := by
  induction M generalizing x d with
  | nil => rfl
  | cons a rest ih => rw [List.getLast?_cons_cons, ih a d, ih a x.2]

omit [Silent Label] in
/-- Prepending a transition does not change the end state: the run
`⟨q, (l₀,q₁) :: rest⟩` ends where `⟨q₁, rest⟩` ends. -/
private theorem endState_ofList_cons (q q₁ : State) (l₀ : Label)
    (rest : List (Label × State)) :
    (⟨q, Seq.ofList ((l₀, q₁) :: rest)⟩ : AlterSeq State Label).endState
        (Stream'.Seq.terminates_ofList _)
      = (⟨q₁, Seq.ofList rest⟩ : AlterSeq State Label).endState
        (Stream'.Seq.terminates_ofList _) := by
  simp only [AlterSeq.endState_eq_getLast?, Stream'.Seq.toList_ofList]
  exact getLast?_elim_cons (l₀, q₁) rest q

omit [Silent Label] in
/-- Dropping the first transition preserves validity: the tail `⟨q₁, T⟩` of a valid
partial execution `⟨q, cons (l₀, q₁) T⟩` is again a valid partial execution. -/
private theorem isPartialExec_tail (sys : System State Label)
    {q q₁ : State} {l₀ : Label} {T : Seq (Label × State)}
    (hpe : is_partial_exec ⟨q, Seq.cons (l₀, q₁) T⟩ sys) :
    is_partial_exec ⟨q₁, T⟩ sys := by
  intro n l s' hn
  have hn1 : (Seq.cons (l₀, q₁) T).get? (n + 1) = some (l, s') := by
    rw [Stream'.Seq.get?_cons_succ]; exact hn
  obtain ⟨s, μ, hst, hstep, hmem⟩ := hpe (n + 1) l s' hn1
  refine ⟨s, μ, ?_, hstep, hmem⟩
  rw [← hst]
  cases n with
  | zero =>
    change (some q₁ : Option State) = ((Seq.cons (l₀, q₁) T).get? 0).map Prod.snd
    simp [Stream'.Seq.get?_cons_zero]
  | succ k =>
    change (T.get? k).map Prod.snd = ((Seq.cons (l₀, q₁) T).get? (k + 1)).map Prod.snd
    rw [Stream'.Seq.get?_cons_succ]

omit [Silent Label] in
/-- The first transition of a valid partial execution of an LTS is a Dirac step:
`⟨q, cons (l₀, q₁) T⟩` valid ⇒ `sys.step q l₀ (pure q₁)`. -/
private theorem firstStep (sys : System State Label) (hLTS : sys.IsLTS)
    {q q₁ : State} {l₀ : Label} {T : Seq (Label × State)}
    (hpe : is_partial_exec ⟨q, Seq.cons (l₀, q₁) T⟩ sys) :
    sys.step q l₀ (PMF.pure q₁) := by
  have h0 : (Seq.cons (l₀, q₁) T).get? 0 = some (l₀, q₁) := Stream'.Seq.get?_cons_zero (l₀, q₁) T
  obtain ⟨s, μ, hst, hstep, hmem⟩ := hpe 0 l₀ q₁ h0
  have hs0 : (⟨q, Seq.cons (l₀, q₁) T⟩ : AlterSeq State Label).stateAt 0 = some q := rfl
  rw [hs0] at hst
  obtain rfl : q = s := Option.some.inj hst
  obtain ⟨s'', hμ⟩ := hLTS q l₀ μ hstep
  subst hμ
  rw [PMF.mem_support_pure_iff] at hmem
  rw [hmem]; exact hstep

/-- Prepending a `τ`-transition does not change the observable trace. -/
private theorem trace_cons_internal (sys : System State Label) (q q₁ : State)
    (T : Seq (Label × State)) :
    sys.trace ⟨q, Seq.cons (Silent.τ, q₁) T⟩ = sys.trace ⟨q₁, T⟩ := by
  unfold System.trace
  rw [Stream'.Seq.filter_cons_neg (Silent.τ, q₁) T (by simp)]

/-! ### Bridging the two weak-transition notions on an LTS -/

/-- **Silent bridge (list form).** A valid, empty-trace (all-`τ`) execution
`⟨q, ofList L⟩` of an LTS yields the distribution-level `weakTau` between the
Diracs on its endpoints. -/
private theorem weakTau_of_silent_ofList (sys : System State Label) (hLTS : sys.IsLTS) :
    ∀ (L : List (Label × State)) (q : State),
      is_partial_exec ⟨q, Seq.ofList L⟩ sys →
      sys.trace ⟨q, Seq.ofList L⟩ = (Seq.nil : Seq Label) →
      weakTau sys (PMF.pure q)
        (PMF.pure ((⟨q, Seq.ofList L⟩ : AlterSeq State Label).endState
          (Stream'.Seq.terminates_ofList L))) := by
  intro L
  induction L with
  | nil =>
    intro q _ _
    have he : (⟨q, Seq.ofList ([] : List (Label × State))⟩ : AlterSeq State Label).endState
        (Stream'.Seq.terminates_ofList _) = q :=
      AlterSeq.endState_of_trans_nil _ Stream'.Seq.ofList_nil _
    rw [he]; exact weakTau_refl sys (PMF.pure q)
  | cons p rest ih =>
    intro q hpe htr
    obtain ⟨l₀, q₁⟩ := p
    rw [Stream'.Seq.ofList_cons] at hpe htr
    have hl0 : l₀ = Silent.τ := by
      by_contra hne
      rw [System.trace_cons_external sys q l₀ q₁ (Seq.ofList rest) hne] at htr
      exact absurd htr Stream'.Seq.cons_ne_nil
    subst hl0
    have hstep : sys.step q Silent.τ (PMF.pure q₁) := firstStep sys hLTS hpe
    have hpe' : is_partial_exec ⟨q₁, Seq.ofList rest⟩ sys := isPartialExec_tail sys hpe
    have htr' : sys.trace ⟨q₁, Seq.ofList rest⟩ = (Seq.nil : Seq Label) := by
      rw [trace_cons_internal sys q q₁ (Seq.ofList rest)] at htr; exact htr
    have hfirst : weakTau sys (PMF.pure q) (PMF.pure q₁) := weakTau_of_step rfl hstep
    rw [endState_ofList_cons q q₁ Silent.τ rest]
    exact weakTau_trans hfirst (ih q₁ hpe' htr')

/-- **Labelled bridge (list form).** A valid execution `⟨q, ofList L⟩` of an LTS
with trace exactly `[l]` (an external `l`) yields the distribution-level
`weakStep` between the Diracs on its endpoints. -/
private theorem weakStep_of_labelled_ofList (sys : System State Label) (hLTS : sys.IsLTS)
    (l : Label) (_hl : ¬ l = Silent.τ) :
    ∀ (L : List (Label × State)) (q : State),
      is_partial_exec ⟨q, Seq.ofList L⟩ sys →
      sys.trace ⟨q, Seq.ofList L⟩ = Seq.cons l Seq.nil →
      weakStep sys (PMF.pure q) l
        (PMF.pure ((⟨q, Seq.ofList L⟩ : AlterSeq State Label).endState
          (Stream'.Seq.terminates_ofList L))) := by
  intro L
  induction L with
  | nil =>
    intro q _ htr
    rw [Stream'.Seq.ofList_nil, System.trace_init] at htr
    exact absurd htr.symm Stream'.Seq.cons_ne_nil
  | cons p rest ih =>
    intro q hpe htr
    obtain ⟨l₀, q₁⟩ := p
    rw [Stream'.Seq.ofList_cons] at hpe htr
    by_cases hl0 : l₀ = Silent.τ
    · subst hl0
      have hstep : sys.step q Silent.τ (PMF.pure q₁) := firstStep sys hLTS hpe
      have hpe' : is_partial_exec ⟨q₁, Seq.ofList rest⟩ sys := isPartialExec_tail sys hpe
      have htr' : sys.trace ⟨q₁, Seq.ofList rest⟩ = Seq.cons l Seq.nil := by
        rw [trace_cons_internal sys q q₁ (Seq.ofList rest)] at htr; exact htr
      have hfirst : weakTau sys (PMF.pure q) (PMF.pure q₁) := weakTau_of_step rfl hstep
      rw [endState_ofList_cons q q₁ Silent.τ rest]
      obtain ⟨ν, ν', hpre, hhyper, hpost⟩ := ih q₁ hpe' htr'
      exact ⟨ν, ν', weakTau_trans hfirst hpre, hhyper, hpost⟩
    · rw [System.trace_cons_external sys q l₀ q₁ (Seq.ofList rest) hl0] at htr
      obtain ⟨hl0l, htail⟩ := Stream'.Seq.cons_eq_cons.mp htr
      have hstep : sys.step q l₀ (PMF.pure q₁) := firstStep sys hLTS hpe
      rw [hl0l] at hstep
      have hpe' : is_partial_exec ⟨q₁, Seq.ofList rest⟩ sys := isPartialExec_tail sys hpe
      have hsilent := weakTau_of_silent_ofList sys hLTS rest q₁ hpe' htail
      rw [endState_ofList_cons q q₁ l₀ rest]
      exact ⟨PMF.pure q, PMF.pure q₁, weakTau_refl sys (PMF.pure q),
        hyperStep_pure_of_step hstep, hsilent⟩

/-- **Silent bridge.** On an LTS, an `ε`-weak transition `q =ε=> q'`
(`System.weakLSilent`) lifts to `weakTau sys (pure q) (pure q')`. -/
theorem weakTau_of_weakLSilent (sys : System State Label) (hLTS : sys.IsLTS)
    {q q' : State} (h : sys.weakLSilent q q') :
    weakTau sys (PMF.pure q) (PMF.pure q') := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := h
  have he : (⟨e.init, Seq.ofList (e.trans.toList hterm)⟩ : AlterSeq State Label) = e := by
    rw [Stream'.Seq.ofList_toList]
  have hpe' : is_partial_exec ⟨e.init, Seq.ofList (e.trans.toList hterm)⟩ sys := by
    rw [he]; exact hpe
  have htr' : sys.trace ⟨e.init, Seq.ofList (e.trans.toList hterm)⟩ = (Seq.nil : Seq Label) := by
    rw [he]; exact htr
  have hbridge := weakTau_of_silent_ofList sys hLTS (e.trans.toList hterm) e.init hpe' htr'
  have hend' : (⟨e.init, Seq.ofList (e.trans.toList hterm)⟩ : AlterSeq State Label).endState
      (Stream'.Seq.terminates_ofList _) = q' := by
    rw [AlterSeq.endState_congr_pub he (Stream'.Seq.terminates_ofList _) hterm]; exact hend
  rw [hend', hinit] at hbridge
  exact hbridge

/-- **Labelled bridge.** On an LTS, an external weak transition `q =l=> q'`
(`System.weakLStep`, `l ≠ τ`) lifts to `weakStep sys (pure q) l (pure q')`. -/
theorem weakStep_of_weakLStep (sys : System State Label) (hLTS : sys.IsLTS)
    {q q' : State} {l : Label} (hl : ¬ l = Silent.τ) (h : sys.weakLStep q l q') :
    weakStep sys (PMF.pure q) l (PMF.pure q') := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := h
  have he : (⟨e.init, Seq.ofList (e.trans.toList hterm)⟩ : AlterSeq State Label) = e := by
    rw [Stream'.Seq.ofList_toList]
  have hpe' : is_partial_exec ⟨e.init, Seq.ofList (e.trans.toList hterm)⟩ sys := by
    rw [he]; exact hpe
  have htr' : sys.trace ⟨e.init, Seq.ofList (e.trans.toList hterm)⟩ = Seq.cons l Seq.nil := by
    rw [he]; exact htr
  have hbridge :=
    weakStep_of_labelled_ofList sys hLTS l hl (e.trans.toList hterm) e.init hpe' htr'
  have hend' : (⟨e.init, Seq.ofList (e.trans.toList hterm)⟩ : AlterSeq State Label).endState
      (Stream'.Seq.terminates_ofList _) = q' := by
    rw [AlterSeq.endState_congr_pub he (Stream'.Seq.terminates_ofList _) hterm]; exact hend
  rw [hend', hinit] at hbridge
  exact hbridge

/-! ### Forward simulation ⟹ probabilistic forward simulation -/

/-- The **Dirac lift** of a state relation `R : S → T → Prop` to a
state-to-distribution relation: `diracRel R s μ` holds iff `μ` is the point mass
on an `R`-image of `s`. This is `R` re-typed for `ProbabilisticForwardSimulation`. -/
def diracRel {S T : Type} (R : S → T → Prop) : S → PMF T → Prop :=
  fun s μ => ∃ t, μ = PMF.pure t ∧ R s t

/-- **A forward simulation between LTS is a probabilistic forward simulation.**

If `sys_1`, `sys_2` are LTS (`System.IsLTS`), `R` is a `ForwardSimulation` of
`sys_1` by `sys_2`, and `R` relates the initial states, then the Dirac lift
`diracRel R` is a `ProbabilisticForwardSimulation` of `sys_1` by `sys_2`.

Both `IsLTS` hypotheses are essential: `sys_1.IsLTS` collapses each concrete step
`s_C -[l]→ μ_C` to a single Dirac outcome (so no probability-matching is needed —
the very reason the equivalence holds only for LTS), and `sys_2.IsLTS` powers the
weak-transition bridges. The hypothesis `hinit` supplies the
`ProbabilisticForwardSimulation.init` clause, which the bare `ForwardSimulation`
(transfer-only) does not carry. -/
theorem ForwardSimulation.toProbabilistic
    {State_1 State_2 : Type} {sys_1 : System State_1 Label} {sys_2 : System State_2 Label}
    {R : State_1 → State_2 → Prop}
    (h1 : sys_1.IsLTS) (h2 : sys_2.IsLTS) (hinit : R sys_1.init sys_2.init)
    (fs : ForwardSimulation sys_1 sys_2 R) :
    ProbabilisticForwardSimulation sys_1 sys_2 (diracRel R) := by
  refine ⟨?_, ?_⟩
  · -- init
    refine ⟨PMF.pure sys_2.init, ?_, ⟨sys_2.init, rfl, hinit⟩⟩
    intro s_A hs_A
    rw [PMF.mem_support_pure_iff] at hs_A
    exact hs_A
  · -- step
    intro s_C μ_A hR l μ_C hstep
    obtain ⟨q₂, hμA, hRq⟩ := hR
    obtain ⟨s_C', hμC⟩ := h1 s_C l μ_C hstep
    have hmem : s_C' ∈ μ_C.support := by rw [hμC, PMF.mem_support_pure_iff]
    obtain ⟨q₂', hdisj, hRq'⟩ := fs.step s_C q₂ hRq l μ_C hstep s_C' hmem
    refine ⟨PMF.pure (PMF.pure q₂'), ?_, ?_⟩
    · -- coupling
      refine ⟨PMF.pure (s_C', PMF.pure q₂'), ?_, ?_, ?_⟩
      · rw [PMF.pure_map]; exact hμC.symm
      · rw [PMF.pure_map]
      · intro p hp
        rw [PMF.mem_support_pure_iff] at hp
        subst hp
        exact ⟨q₂', rfl, hRq'⟩
    · -- abstract weak transition on `(pure (pure q₂')).bind id = pure q₂'`
      simp only [hμA, PMF.pure_bind, id_eq]
      rcases hdisj with ⟨hτ, hsil⟩ | ⟨hext, hlab⟩
      · exact Or.inl ⟨hτ, weakTau_of_weakLSilent sys_2 h2 hsil⟩
      · exact Or.inr ⟨hext, weakStep_of_weakLStep sys_2 h2 hext hlab⟩

end PLTS
