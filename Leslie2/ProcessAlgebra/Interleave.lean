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

Support lemmas for the precongruence `ProbabilisticForwardSimulation.interleave` (in
`Results.lean`): the composite relation `interleaveRel`, its `PMFRel` coupling
(`pmfRel_interleave`), and the two
**weak-transition lift lemmas** that transport a single component's weak
transition into the fully-asynchronous product (via the scheduler-map primitive `weakTau_embed` /
`hyperStep_embed` per held-config point, mixed over the held beliefs with `weakTau_mix` /
`hyperStep_mix`):

* `weakTau_interleave` — a `sysA i` τ-closure ⟹ an interleave τ-closure;
* `weakStep_interleave` — a `sysA i` weak `l`-step ⟹ an interleave weak `l`-step (still interleaved,
  never synchronised).

The `piPMF`/`Function.update` algebra these build on lives in `ProcessAlgebra/Composition.lean`.
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

/-- Lift a component `PMFRel (R i)` coupling to an `interleaveRel R` coupling, holding the other
components at their beliefs `μ_ j` (which are `R j`-related to `s j` by `hR`). -/
theorem pmfRel_interleave (i : ι) (s : ∀ j, State_C j) (μ_ : ∀ j, PMF (State_A j))
    (hR : ∀ j, R j (s j) (μ_ j)) {μ_Ci : PMF (State_C i)} {ω_Ai : PMF (PMF (State_A i))}
    (h : PMFRel (R i) μ_Ci ω_Ai) :
    PMFRel (interleaveRel R) (piPMF (Function.update (fun j => PMF.pure (s j)) i μ_Ci))
      (ω_Ai.map (fun ρ => piPMF (Function.update μ_ i ρ))) := by
  obtain ⟨Ω_Ai, hfst, hsnd, hsupp⟩ := h
  refine ⟨Ω_Ai.map (fun q => (Function.update s i q.1, piPMF (Function.update μ_ i q.2))),
    ?_, ?_, ?_⟩
  · rw [PMF.map_comp, piPMF_update_pure, ← hfst, PMF.map_comp]; rfl
  · rw [PMF.map_comp, ← hsnd, PMF.map_comp]; rfl
  · intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨Function.update μ_ i q.2, ?_, rfl⟩
    intro j
    dsimp only
    by_cases hj : j = i
    · subst hj; rw [Function.update_self, Function.update_self]; exact hsupp q hq
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]; exact hR j

/-! ### The two weak-transition lift lemmas (the crux)

Both are lifted from a single component through the reusable embedding primitives
(`weakTau_embed` / `hyperStep_embed`, in `Weak/Embed.lean`) mixed over the held-config
distribution `piPMF μ_` (`weakTau_mix` / `hyperStep_mix`, in `Weak/WeakChar.lean`), and glued
back together by the collapse identity `piPMF_bind_update`. Per held config `s`, the embedding is
`ι_s := Function.update s i ·` (injective — read coordinate `i`), which sends a `sysA i`-step at
`c` to the interleave step that moves coordinate `i` (leaving the others as the Diracs of `s`). -/

/-- **The collapse identity.** Mixing over the held-config distribution `piPMF μ_` the family
`s ↦ piPMF (update (fun j ↦ pure (s j)) i κ)` (the moved coordinate `i` re-sampled from `κ`, the
others held at the Diracs of `s`) collapses back to the single independent product
`piPMF (update μ_ i κ)`. Proven pointwise by marginalizing coordinate `i`. -/
private theorem piPMF_bind_update (i : ι) {α : ι → Type} (μ_ : ∀ j, PMF (α j)) (κ : PMF (α i)) :
    (piPMF μ_).bind (fun s => piPMF (Function.update (fun j => PMF.pure (s j)) i κ))
      = piPMF (Function.update μ_ i κ) := by
  classical
  refine PMF.ext (fun f => ?_)
  rw [PMF.bind_apply]
  simp only [piPMF_update_pure]
  rw [piPMF_update_apply]
  rw [show (∑' s : ∀ j, α j, (piPMF μ_) s
        * (PMF.map (fun c => Function.update s i c) κ) f)
      = ∑' s : ∀ j, α j, (piPMF μ_) s
        * (if (∀ x ∈ Finset.univ.erase i, s x = f x) then κ (f i) else 0) from
    tsum_congr (fun s => by
      congr 1
      rw [PMF.map_apply]
      by_cases hC : ∀ x ∈ Finset.univ.erase i, s x = f x
      · rw [if_pos hC]
        have hpos : f = Function.update s i (f i) := by
          funext x
          by_cases hx : x = i
          · subst hx; rw [Function.update_self]
          · rw [Function.update_of_ne hx]
            exact (hC x (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩)).symm
        rw [tsum_eq_single (f i)]
        · rw [if_pos hpos]
        · intro c hc
          apply if_neg
          intro heq
          apply hc
          have h := congrFun heq i
          rw [Function.update_self] at h
          exact h.symm
      · rw [if_neg hC]
        push Not at hC
        obtain ⟨x, hx, hne⟩ := hC
        refine ENNReal.tsum_eq_zero.mpr (fun c => if_neg ?_)
        intro heq
        apply hne
        have h := congrFun heq x
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)] at h
        exact h.symm)]
  rw [show (∑' s : ∀ j, α j, (piPMF μ_) s
        * (if (∀ x ∈ Finset.univ.erase i, s x = f x) then κ (f i) else 0))
      = κ (f i) * ∑' s : ∀ j, α j, (piPMF μ_) s
        * (if (∀ x ∈ Finset.univ.erase i, s x = f x) then (1 : ENNReal) else 0) from by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr (fun s => ?_)
    by_cases hC : ∀ x ∈ Finset.univ.erase i, s x = f x
    · rw [if_pos hC, if_pos hC]; ring
    · rw [if_neg hC, if_neg hC]; ring]
  congr 1
  rw [show (∑' s : ∀ j, α j, (piPMF μ_) s
        * (if (∀ x ∈ Finset.univ.erase i, s x = f x) then (1 : ENNReal) else 0))
      = ∑' c : α i, (piPMF μ_) (Function.update f i c) from
    tsum_eq_tsum_of_ne_zero_bij
      (i := fun (c : Function.support (fun c : α i => (piPMF μ_) (Function.update f i c))) =>
        Function.update f i (c : α i)) ?_ ?_ ?_]
  · have hval : ∀ c : α i, (piPMF μ_) (Function.update f i c)
        = μ_ i c * ∏ x ∈ Finset.univ.erase i, μ_ x (f x) := by
      intro c
      rw [piPMF_apply, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
        Function.update_self]
      congr 1
      exact Finset.prod_congr rfl (fun x hx => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)])
    rw [tsum_congr hval, ENNReal.tsum_mul_right, (μ_ i).tsum_coe, one_mul]
  · rintro ⟨c₁, _⟩ ⟨c₂, _⟩ heq
    simp only [Subtype.mk.injEq]
    have h := congrFun heq i
    simp only at h
    rw [Function.update_self, Function.update_self] at h
    exact h
  · intro s hs
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hs
    obtain ⟨hpi, hind⟩ := hs
    have hcond : ∀ x ∈ Finset.univ.erase i, s x = f x := by
      by_contra hc
      exact hind (by rw [if_neg hc])
    have hs_eq : s = Function.update f i (s i) := by
      funext x
      by_cases hx : x = i
      · subst hx; rw [Function.update_self]
      · rw [Function.update_of_ne hx]
        exact hcond x (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩)
    refine ⟨⟨s i, ?_⟩, ?_⟩
    · simp only [Function.mem_support, ne_eq]
      rw [← hs_eq]; exact hpi
    · exact hs_eq.symm
  · rintro ⟨c, hc⟩
    simp only
    rw [if_pos ?_, mul_one]
    intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]

omit [Fintype ι] in
/-- The per-config embedding `ι_s := Function.update s i ·` is injective (read coordinate `i`). -/
private theorem update_inj (i : ι) (s : ∀ j, State_A j) :
    Function.Injective (fun c : State_A i => Function.update s i c) := by
  intro c₁ c₂ h
  have := congrFun h i
  simp only [Function.update_self] at this
  exact this

/-- A `sysA i` τ-closure lifts to an interleave τ-closure, holding all the other components at their
beliefs `μ_ j`. Per held config `s`, `weakTau_embed` along `ι_s` transports the component closure;
mixing over `s ~ piPMF μ_` (`weakTau_mix`) and collapsing with `piPMF_bind_update` gives the
interleave closure. -/
theorem weakTau_interleave (i : ι) (μ_ : ∀ j, PMF (State_A j)) {ν : PMF (State_A i)}
    (h : weakTau (sysA i) (μ_ i) ν) :
    weakTau (System.interleave sysA) (piPMF μ_) (piPMF (Function.update μ_ i ν)) := by
  classical
  rw [show piPMF μ_ = (piPMF μ_).bind
      (fun s => piPMF (Function.update (fun j => PMF.pure (s j)) i (μ_ i))) from by
    rw [piPMF_bind_update i μ_ (μ_ i), Function.update_eq_self]]
  rw [show piPMF (Function.update μ_ i ν)
      = (piPMF μ_).bind (fun s => piPMF (Function.update (fun j => PMF.pure (s j)) i ν)) from
    (piPMF_bind_update i μ_ ν).symm]
  refine weakTau_mix (piPMF μ_) _ _ (fun s _ => ?_)
  have hstep_s : ∀ (c : State_A i) (κ : PMF (State_A i)),
      (sysA i).step c Silent.τ κ →
      (System.interleave sysA).step ((fun d => Function.update s i d) c) Silent.τ
        (κ.map (fun d => Function.update s i d)) := by
    intro c κ hst
    rw [System.interleave_step]
    refine ⟨i, κ, ?_, ?_⟩
    · change (sysA i).step (Function.update s i c i) Silent.τ κ
      rw [Function.update_self]; exact hst
    · rw [piPMF_update_pure]; congr 1; funext d; rw [Function.update_idem]
  have hembed := weakTau_embed (fun d => Function.update s i d) (update_inj i s) hstep_s h
  rw [← piPMF_update_pure s i (μ_ i), ← piPMF_update_pure s i ν] at hembed
  exact hembed

omit [Silent Label] in
/-- A `sysA i` hyper-step at label `l` lifts to an interleave hyper-step, holding the other
components at their beliefs `μ_ j`. Same recipe as `weakTau_interleave` but with the structural
`hyperStep_embed` / `hyperStep_mix` in place of the τ-closure lifts. -/
private theorem hyperStep_interleave (i : ι) (l : Label) (μ_ : ∀ j, PMF (State_A j))
    {m m' : PMF (State_A i)} (h : hyperStep (sysA i) m l m') :
    hyperStep (System.interleave sysA) (piPMF (Function.update μ_ i m)) l
      (piPMF (Function.update μ_ i m')) := by
  classical
  rw [← piPMF_bind_update i μ_ m, ← piPMF_bind_update i μ_ m']
  refine hyperStep_mix (piPMF μ_) _ _ (fun s _ => ?_)
  have hstep_s : ∀ (c : State_A i) (κ : PMF (State_A i)),
      (sysA i).step c l κ →
      (System.interleave sysA).step ((fun d => Function.update s i d) c) l
        (κ.map (fun d => Function.update s i d)) := by
    intro c κ hst
    rw [System.interleave_step]
    refine ⟨i, κ, ?_, ?_⟩
    · change (sysA i).step (Function.update s i c i) l κ
      rw [Function.update_self]; exact hst
    · rw [piPMF_update_pure]; congr 1; funext d; rw [Function.update_idem]
  have hembed := hyperStep_embed (fun d => Function.update s i d) (update_inj i s) hstep_s h
  rw [← piPMF_update_pure s i m, ← piPMF_update_pure s i m'] at hembed
  exact hembed

/-- A `sysA i` weak `l`-step lifts to an interleave weak `l`-step (still interleaved: the other
components are held), holding all the other components at their beliefs `μ_ j`. The three layers
(τ-closure, hyper-step, τ-closure) are lifted by `weakTau_interleave` (twice) and
`hyperStep_interleave` (once). -/
theorem weakStep_interleave (i : ι) (l : Label) (μ_ : ∀ j, PMF (State_A j))
    {ν : PMF (State_A i)} (h : weakStep (sysA i) (μ_ i) l ν) :
    weakStep (System.interleave sysA) (piPMF μ_) l (piPMF (Function.update μ_ i ν)) := by
  classical
  obtain ⟨m, m', h1, h2, h3⟩ := h
  refine ⟨piPMF (Function.update μ_ i m), piPMF (Function.update μ_ i m'), ?_, ?_, ?_⟩
  · exact weakTau_interleave i μ_ h1
  · exact hyperStep_interleave i l μ_ h2
  · have h3' : weakTau (sysA i) ((Function.update μ_ i m') i) ν := by
      rw [Function.update_self]; exact h3
    have hlayer := weakTau_interleave i (Function.update μ_ i m') h3'
    rw [Function.update_idem] at hlayer
    exact hlayer

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

end PLTS
