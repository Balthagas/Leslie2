/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.ProcessAlgebra.Composition
import Leslie2.Simulation.SimDefs
import Leslie2.Weak.Embed

/-!
# Simulation-congruence machinery for `interleave`

Support for the precongruence `ProbabilisticForwardSimulation.interleaveCofin` (in `Results.lean`)
over an *arbitrary* `[DecidableEq ι]` index, with the finite `interleave` as a corollary. The
abstract belief is carried by a `CofinPMF` (a cofinitely-Dirac family, `ProcessAlgebra/Composition`):

* `interleaveRelCofin` — the composite coupling relation (belief = `c.toPMF`);
* `pmfRel_interleaveCofin` — its `PMFRel` coupling lift;
* `weakTau_interleaveCofin` / `weakStep_interleaveCofin` — the weak-transition lift lemmas,
  transporting one component's weak transition into the fully-asynchronous product via the
  scheduler-map primitives `weakTau_embed` / `hyperStep_embed` (per held-config point, along the
  injective embedding `Function.update s i`), mixed over the held beliefs with `weakTau_mix` /
  `hyperStep_mix`, and glued by the resample identities `CofinPMF.toPMF_self_bind` /
  `toPMF_update_eq_bind`.

The finite relation `interleaveRel` (belief = `piPMF μ_`) is kept only to state the finite
corollary; over `[Fintype ι]` it equals `interleaveRelCofin` (`interleaveRelCofin_eq_interleaveRel`).
-/

open scoped BigOperators

namespace PLTS

section Interleave

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {State_C State_A : ι → Type} {Label : Type} [Silent Label]
  {sysC : ∀ i, System (State_C i) Label} {sysA : ∀ i, System (State_A i) Label}
  {R : ∀ i, State_C i → PMF (State_A i) → Prop}

/-- The composite relation for the interleave precongruence: the abstract distribution is the
independent product `piPMF μ_` of per-component beliefs, each `R`-related to the concrete state. -/
def interleaveRel (R : ∀ i, State_C i → PMF (State_A i) → Prop) :
    (∀ i, State_C i) → PMF (∀ i, State_A i) → Prop :=
  fun s ν => ∃ μ_ : ∀ i, PMF (State_A i), (∀ i, R i (s i) (μ_ i)) ∧ ν = piPMF μ_

omit [Fintype ι] in
/-- The per-config embedding `ι_s := Function.update s i ·` is injective (read coordinate `i`). -/
private theorem update_inj (i : ι) (s : ∀ j, State_A j) :
    Function.Injective (fun c : State_A i => Function.update s i c) := by
  intro c₁ c₂ h
  have := congrFun h i
  simp only [Function.update_self] at this
  exact this

end Interleave

/-! ### Cofinite (infinite-index) interleave: the `CofinPMF` coupling and lift lemmas

The same construction as `section Interleave` but over an *arbitrary* `[DecidableEq ι]` index (no
`Fintype`): the abstract belief is carried by a `CofinPMF` (a cofinitely-Dirac family), whose
product `toPMF` is a genuine `PMF` even for infinite `ι`. The lift lemmas are the direct analogues
of `weakTau_interleave`/`hyperStep_interleave`/`weakStep_interleave`, driven by the resample
identities `CofinPMF.toPMF_self_bind` / `toPMF_update_eq_bind` in place of `piPMF_bind_update`; the
per-config embedding (`weakTau_embed`/`hyperStep_embed` along `Function.update s i`, mixed with
`weakTau_mix`/`hyperStep_mix`) is reused verbatim. -/

section InterleaveCofin

variable {ι : Type} [DecidableEq ι]
  {State_C State_A : ι → Type} {Label : Type} [Silent Label]
  {sysC : ∀ i, System (State_C i) Label} {sysA : ∀ i, System (State_A i) Label}
  {R : ∀ i, State_C i → PMF (State_A i) → Prop}

/-- The interleave coupling relation, cofinite form: the abstract distribution is the product
`c.toPMF` of a cofinitely-Dirac family `c` whose every coordinate marginal `c.coord i` is
`R i`-related to the concrete state.

The cofiniteness constraint lives *here*, structurally: the witness `c : CofinPMF State_A` has a
finite `active` set by construction, so this relation only couples to abstract beliefs that factor
as a cofinitely-Dirac product. This is what carries the finiteness that the finite `interleaveRel`
gets from `[Fintype ι]` — but only *per state* (one coordinate is activated per interleave step, so
`active` stays finite along any finite run without a uniform bound). See
`ProbabilisticForwardSimulation.interleaveCofin` for why this needs no hypothesis on the components
and is strictly looser than assuming cofinitely many of them are LTS. -/
def interleaveRelCofin (R : ∀ i, State_C i → PMF (State_A i) → Prop) :
    (∀ i, State_C i) → PMF (∀ i, State_A i) → Prop :=
  fun s ν => ∃ c : CofinPMF State_A, (∀ i, R i (s i) (c.coord i)) ∧ ν = c.toPMF

/-- Lift a component `PMFRel (R i)` coupling to an `interleaveRelCofin R` coupling, holding the
other coordinates at their current marginals via `c` (bundled analogue of `pmfRel_interleave`). -/
theorem pmfRel_interleaveCofin (i : ι) (s : ∀ j, State_C j) (c : CofinPMF State_A)
    (hR : ∀ j, R j (s j) (c.coord j)) {μ_Ci : PMF (State_C i)} {ω_Ai : PMF (PMF (State_A i))}
    (h : PMFRel (R i) μ_Ci ω_Ai) :
    PMFRel (interleaveRelCofin R) (μ_Ci.map (Function.update s i))
      (ω_Ai.map (fun ρ => (c.update i ρ).toPMF)) := by
  obtain ⟨Ω_Ai, hfst, hsnd, hsupp⟩ := h
  refine ⟨Ω_Ai.map (fun q => (Function.update s i q.1, (c.update i q.2).toPMF)), ?_, ?_, ?_⟩
  · simp only [PMF.map_comp, Function.comp_def, ← hfst]
  · simp only [PMF.map_comp, Function.comp_def, ← hsnd]
  · intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨c.update i q.2, ?_, rfl⟩
    intro j
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self, CofinPMF.coord_update_self]; exact hsupp q hq
    · simp only [Function.update_of_ne hj, CofinPMF.coord_update_ne c i q.2 hj]; exact hR j

omit [Silent Label] in
/-- Per config `s`, the interleave step that moves coordinate `i` from `Function.update s i x`. -/
private theorem interleave_step_at {sys : ∀ i, System (State_A i) Label} (i : ι)
    (s : ∀ j, State_A j) (l : Label) (x : State_A i) (κ : PMF (State_A i))
    (hst : (sys i).step x l κ) :
    (System.interleave sys).step (Function.update s i x) l (κ.map (Function.update s i)) := by
  rw [System.interleave_step_map]
  refine ⟨i, κ, ?_, ?_⟩
  · rw [Function.update_self]; exact hst
  · congr 1; funext d; rw [Function.update_idem]

/-- A `sysA i` τ-closure lifts to a cofinite interleave τ-closure, holding the other coordinates
at `c`. Bundled analogue of `weakTau_interleave`. -/
theorem weakTau_interleaveCofin (c : CofinPMF State_A) (i : ι) {ν : PMF (State_A i)}
    (h : weakTau (sysA i) (c.coord i) ν) :
    weakTau (System.interleave sysA) c.toPMF (c.update i ν).toPMF := by
  classical
  rw [CofinPMF.toPMF_self_bind c i, CofinPMF.toPMF_update_eq_bind c i ν]
  refine weakTau_mix c.toPMF _ _ (fun s _ => ?_)
  exact weakTau_embed (fun d => Function.update s i d) (update_inj i s)
    (fun x κ hst => interleave_step_at i s Silent.τ x κ hst) h

omit [Silent Label] in
/-- A `sysA i` hyper-step lifts to a cofinite interleave hyper-step. Bundled analogue of
`hyperStep_interleave`. -/
private theorem hyperStep_interleaveCofin (c : CofinPMF State_A) (i : ι) (l : Label)
    {m m' : PMF (State_A i)} (h : hyperStep (sysA i) m l m') :
    hyperStep (System.interleave sysA) (c.update i m).toPMF l (c.update i m').toPMF := by
  classical
  rw [CofinPMF.toPMF_update_eq_bind c i m, CofinPMF.toPMF_update_eq_bind c i m']
  refine hyperStep_mix c.toPMF _ _ (fun s _ => ?_)
  exact hyperStep_embed (fun d => Function.update s i d) (update_inj i s)
    (fun x κ hst => interleave_step_at i s l x κ hst) h

/-- A `sysA i` weak `l`-step lifts to a cofinite interleave weak `l`-step. Bundled analogue of
`weakStep_interleave`. -/
theorem weakStep_interleaveCofin (c : CofinPMF State_A) (i : ι) (l : Label)
    {ν : PMF (State_A i)} (h : weakStep (sysA i) (c.coord i) l ν) :
    weakStep (System.interleave sysA) c.toPMF l (c.update i ν).toPMF := by
  obtain ⟨m, m', h1, h2, h3⟩ := h
  refine ⟨(c.update i m).toPMF, (c.update i m').toPMF, weakTau_interleaveCofin c i h1,
    hyperStep_interleaveCofin c i l h2, ?_⟩
  have h3' : weakTau (sysA i) ((c.update i m').coord i) ν := by
    rw [CofinPMF.coord_update_self]; exact h3
  have hlayer := weakTau_interleaveCofin (c.update i m') i h3'
  have hidem : (c.update i m').update i ν = c.update i ν := by
    simp only [CofinPMF.update, Finset.insert_idem, Function.update_idem]
  rw [hidem] at hlayer
  exact hlayer

end InterleaveCofin

/-! ### The finite coupling relation is a special case

Over a `[Fintype ι]` index the two coupling relations coincide, so the finite precongruence
(`ProbabilisticForwardSimulation.interleave`, Result 4) is a corollary of the cofinite one. -/

section InterleaveRelEq

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {State_C State_A : ι → Type}
  {R : ∀ i, State_C i → PMF (State_A i) → Prop}

/-- Over a finite index, the cofinite coupling relation `interleaveRelCofin R` and the finite one
`interleaveRel R` are equal: a `CofinPMF` marginalises to `interleaveRel`'s per-coordinate beliefs
(`CofinPMF.toPMF_eq_piPMF_coord`), and conversely any belief family is the `active = univ`
`CofinPMF`. -/
theorem interleaveRelCofin_eq_interleaveRel :
    interleaveRelCofin R = interleaveRel R := by
  funext s ν
  refine propext ⟨?_, ?_⟩
  · rintro ⟨c, hR, rfl⟩
    exact ⟨c.coord, hR, c.toPMF_eq_piPMF_coord⟩
  · rintro ⟨μ_, hR, rfl⟩
    refine ⟨⟨fun i => (μ_ i).support_nonempty.some, Finset.univ, μ_⟩, ?_, ?_⟩
    · intro i
      have : (⟨fun i => (μ_ i).support_nonempty.some, Finset.univ, μ_⟩
          : CofinPMF State_A).coord i = μ_ i := by simp [CofinPMF.coord]
      rw [this]; exact hR i
    · rw [CofinPMF.toPMF_eq_piPMF_coord]
      congr 1
      funext i
      simp [CofinPMF.coord]

end InterleaveRelEq

end PLTS
