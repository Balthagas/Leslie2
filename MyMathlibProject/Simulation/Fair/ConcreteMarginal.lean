/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Simulation.Fair.AbstractMarginal

/-!
# The concrete marginal of the coupled resolved execution (the `Prod.fst` mirror)

The exact `Prod.fst` analogue of `Simulation/Fair/AbstractMarginal`: marginalise the coupled
resolved execution of `simProd sys_C sys_A R` onto `sys_C` via `Prod.fst`. This file develops the
concrete belief weight `cWeight` (with its `concreteProjR`-fibre reindexing: base `cWeight_nil`,
cons-end `cWeight_append_singleton`, bound `cWeight_le_init`), the concrete marginal
`concreteMarginal`, its value telescoping `concreteMarginal_probOfR`, and the trace-preservation
result `concreteMarginal_traceProbR`. Every declaration mirrors its `Prod.snd` twin verbatim,
adjusting the projection to `Prod.fst`, the target factor to `sys_C`, and the recorded coupling
marginal to `ω.map Prod.fst`.
-/

open Stream'

namespace PLTS

variable {State_C State_A Label : Type} [Silent Label]

namespace FairStrongProbabilisticSimulation

variable {sys_C : System State_C Label} {sys_A : System State_A Label}
  {F_C : Fairness sys_C} {F_A : Fairness sys_A} {R : State_C → State_A → Prop}

/-! ### The concrete marginal (the `Prod.fst` mirror of the abstract marginal)

The exact `Prod.fst` analogue of the `Prod.snd` development above: marginalise a resolved execution
`peJ` of the coupled product onto `sys_C` (via `Prod.fst`), producing `concreteMarginal peJ`, and
prove it preserves `traceProbR` (`concreteMarginal_traceProbR`). Every declaration below mirrors its
`Prod.snd` twin verbatim, adjusting the projection to `Prod.fst`, the target factor to `sys_C`, and
the recorded coupling marginal to `ω.map Prod.fst`. The projection `concreteProjR` (used to drive
the concrete scheduler) is already defined above; only its lemmas are added here. -/

omit [Silent Label] in
/-- `concreteProjR` preserves termination at each index (it is a `Seq.map`). -/
theorem concreteProjR_terminatedAt_iff (r : ResolvedExec (State_C × State_A) Label) (n : ℕ) :
    (concreteProjR r).trans.TerminatedAt n ↔ r.trans.TerminatedAt n := by
  unfold Stream'.Seq.TerminatedAt
  change ((r.trans.map _).get? n = none) ↔ _
  rw [Stream'.Seq.map_get?, Option.map_eq_none_iff]

omit [Silent Label] in
/-- `concreteProjR` preserves termination. -/
theorem concreteProjR_terminates_iff (r : ResolvedExec (State_C × State_A) Label) :
    (concreteProjR r).trans.Terminates ↔ r.trans.Terminates :=
  Stream'.Seq.terminates_map_iff

omit [Silent Label] in
/-- A product decoration of a terminating concrete history terminates. -/
theorem terminates_of_concreteProjR_eq {e_C : ResolvedExec State_C Label}
    (he : e_C.trans.Terminates) {r : ResolvedExec (State_C × State_A) Label}
    (hr : concreteProjR r = e_C) : r.trans.Terminates :=
  (concreteProjR_terminates_iff r).mp (by rw [hr]; exact he)

/-! ### The `concreteProjR`-fibre reindexing (for `cWeight_le_init`)

The `concreteProjR` analogue of the `toExec` `snocDecoration`/`exists_snocDecoration` machinery of
`Model/ResolvedScheduler.lean`. Extending a concrete history `e_C'` by a final concrete step
`((l, ν), s_C')` corresponds, on the product side, to extending a decoration `r'` of `e_C'` by a
final product step `((l, ω), (s_C', s_A'))` with `ω.map Prod.fst = ν` (a *coupling* over the
recorded concrete distribution `ν`) and a chosen abstract successor `s_A'`. The decoration is thus
indexed by
`(r', ω, s_A')` with `ω` ranging over the `Prod.fst`-fibre of `ν`. -/

omit [Silent Label] in
@[simp] theorem concreteProjR_init (r : ResolvedExec (State_C × State_A) Label) :
    (concreteProjR r).init = r.init.1 := rfl

omit [Silent Label] in
/-- The concrete projection's state at `n` is the `Prod.fst`-image of the product state at `n`.
Concrete analogue of `ResolvedExec.toExec_stateAt`. -/
theorem concreteProjR_stateAt (r : ResolvedExec (State_C × State_A) Label) (n : ℕ) :
    (concreteProjR r).stateAt n = (r.stateAt n).map Prod.fst := by
  cases n with
  | zero => rfl
  | succ k =>
    change ((r.trans.map (fun p => ((p.1.1, p.1.2.map Prod.fst), p.2.1))).get? k).map Prod.snd
        = ((r.trans.get? k).map Prod.snd).map Prod.fst
    rw [Stream'.Seq.map_get?]
    cases r.trans.get? k <;> rfl

omit [Silent Label] in
/-- `concreteProjR` commutes with appending a final product transition `((l, ω), (s_C', s_A'))`:
projecting the extended history is extending the projected history by `((l, ω.map Prod.fst), s_C')`.
The concrete analogue of `ResolvedExec.toExec_append_singleton`. -/
theorem concreteProjR_append_singleton (r' : ResolvedExec (State_C × State_A) Label)
    (l : Label) (ω : PMF (State_C × State_A)) (s' : State_C × State_A) :
    concreteProjR ⟨r'.init, r'.trans.append (Seq.cons ((l, ω), s') Seq.nil)⟩
      = ⟨(concreteProjR r').init,
          (concreteProjR r').trans.append (Seq.cons ((l, ω.map Prod.fst), s'.1) Seq.nil)⟩ := by
  unfold concreteProjR
  simp only [Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil]

omit [Silent Label] in
/-- A product decoration of the empty concrete history `⟨s₀, nil⟩` is itself `⟨(s₀, s_A), nil⟩` for
some abstract `s_A`; in particular its `trans` is empty. Concrete analogue of
`eq_nil_of_toExec_nil`. -/
theorem trans_nil_of_concreteProjR_nil {r : ResolvedExec (State_C × State_A) Label} {s₀ : State_C}
    (hr : concreteProjR r = ⟨s₀, Seq.nil⟩) : r.trans = Seq.nil := by
  have hz : (concreteProjR r).trans.TerminatedAt 0 := by
    rw [hr]; exact Stream'.Seq.terminatedAt_zero_iff.mpr rfl
  exact Stream'.Seq.terminatedAt_zero_iff.mp ((concreteProjR_terminatedAt_iff r 0).mp hz)

/-- Extend a decoration `r'` of `e_C'` by a coupling `ω` over `ν` and an abstract successor `s_A'`,
yielding a decoration of `e_C' ++ ((l, ν), s_C')`. The forward object of the fibre reindexing. -/
def cSnocDecoration (e_C' : ResolvedExec State_C Label) (l : Label) (ν : PMF State_C)
    (s_C' : State_C)
    (p : {r' : ResolvedExec (State_C × State_A) Label // concreteProjR r' = e_C'} ×
      {ω : PMF (State_C × State_A) // ω.map Prod.fst = ν} × State_A) :
    {r : ResolvedExec (State_C × State_A) Label //
      concreteProjR r = ⟨e_C'.init, e_C'.trans.append (Seq.cons ((l, ν), s_C') Seq.nil)⟩} :=
  ⟨⟨p.1.1.init, p.1.1.trans.append (Seq.cons ((l, p.2.1.1), (s_C', p.2.2)) Seq.nil)⟩, by
    rw [concreteProjR_append_singleton, p.2.1.2, p.1.2]⟩

omit [Silent Label] in
theorem cSnocDecoration_injective {e_C' : ResolvedExec State_C Label}
    (he' : e_C'.trans.Terminates) (l : Label) (ν : PMF State_C) (s_C' : State_C) :
    Function.Injective (@cSnocDecoration State_C State_A Label e_C' l ν s_C') := by
  rintro ⟨⟨r₁, hr₁⟩, ⟨ω₁, hω₁⟩, sA₁⟩ ⟨⟨r₂, hr₂⟩, ⟨ω₂, hω₂⟩, sA₂⟩ h
  have hAlt :
      (⟨r₁.init, r₁.trans.append (Seq.cons ((l, ω₁), (s_C', sA₁)) Seq.nil)⟩ :
          ResolvedExec (State_C × State_A) Label)
        = ⟨r₂.init, r₂.trans.append (Seq.cons ((l, ω₂), (s_C', sA₂)) Seq.nil)⟩ :=
    congrArg Subtype.val h
  rw [AlterSeq.mk.injEq] at hAlt
  obtain ⟨h_init, h_trans⟩ := hAlt
  have ht₁ : r₁.trans.Terminates := terminates_of_concreteProjR_eq he' hr₁
  have ht₂ : r₂.trans.Terminates := terminates_of_concreteProjR_eq he' hr₂
  have hlast : ((l, ω₁), (s_C', sA₁)) = ((l, ω₂), (s_C', sA₂)) :=
    Stream'.Seq.append_singleton_inj_right r₁.trans r₂.trans ht₁ ht₂ _ _ h_trans
  have htr : r₁.trans = r₂.trans :=
    Stream'.Seq.append_singleton_inj_left r₁.trans r₂.trans ht₁ ht₂ _ _ h_trans
  have hω : ω₁ = ω₂ := congrArg (fun x => x.1.2) hlast
  have hsA : sA₁ = sA₂ := congrArg (fun x => x.2.2) hlast
  have hr : r₁ = r₂ := by
    cases r₁ with | mk i₁ t₁ => cases r₂ with | mk i₂ t₂ => cases h_init; cases htr; rfl
  subst hr; subst hω; subst hsA
  rfl

omit [Silent Label] in
theorem exists_cSnocDecoration {e_C' : ResolvedExec State_C Label}
    (he' : e_C'.trans.Terminates) (l : Label) (ν : PMF State_C) (s_C' : State_C)
    (r : {r : ResolvedExec (State_C × State_A) Label //
      concreteProjR r = ⟨e_C'.init, e_C'.trans.append (Seq.cons ((l, ν), s_C') Seq.nil)⟩}) :
    ∃ p, cSnocDecoration e_C' l ν s_C' p = r := by
  have hmap : r.1.trans.map (fun p => ((p.1.1, p.1.2.map Prod.fst), p.2.1))
      = e_C'.trans.append (Seq.cons ((l, ν), s_C') Seq.nil) := by
    have := congrArg AlterSeq.trans r.2
    rwa [show (concreteProjR r.1).trans = _ from rfl] at this
  have hs1 : (Seq.cons ((l, ν), s_C') Seq.nil : Seq ((Label × PMF State_C) × State_C)).Terminates :=
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
  have hE : (e_C'.trans.append (Seq.cons ((l, ν), s_C') Seq.nil)).Terminates :=
    ⟨_, Stream'.Seq.terminatedAt_append_find he' hs1.choose_spec⟩
  have hRterm : r.1.trans.Terminates := terminates_of_concreteProjR_eq hE r.2
  have hne : r.1.trans.toList hRterm ≠ [] := by
    intro hnil
    have htrans_nil : r.1.trans = Seq.nil := by
      have h := Stream'.Seq.ofList_toList r.1.trans hRterm
      rw [hnil, Stream'.Seq.ofList_nil] at h
      exact h.symm
    rw [htrans_nil, Stream'.Seq.map_nil] at hmap
    have h0 : (e_C'.trans.append (Seq.cons ((l, ν), s_C') Seq.nil)).get? (Nat.find he')
        = some ((l, ν), s_C') := by
      have := Stream'.Seq.get?_append_find he' (Seq.cons ((l, ν), s_C') Seq.nil) 0
      rw [Nat.add_zero] at this
      rw [this]; rfl
    rw [← hmap] at h0
    simp at h0
  obtain ⟨prev, last, hprev, hsplit, _, _⟩ := Stream'.Seq.exists_split_last r.1.trans hRterm hne
  have hmap' : (prev.map (fun p => ((p.1.1, p.1.2.map Prod.fst), p.2.1))).append
        (Seq.cons ((fun p => ((p.1.1, p.1.2.map Prod.fst), p.2.1)) last) Seq.nil)
      = e_C'.trans.append (Seq.cons ((l, ν), s_C') Seq.nil) := by
    have h1 : (prev.append (Seq.cons last Seq.nil)).map
          (fun p => ((p.1.1, p.1.2.map Prod.fst), p.2.1))
        = e_C'.trans.append (Seq.cons ((l, ν), s_C') Seq.nil) := by rw [← hsplit]; exact hmap
    rwa [Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil] at h1
  have htprevmap : (prev.map (fun p => ((p.1.1, p.1.2.map Prod.fst), p.2.1))).Terminates :=
    Stream'.Seq.terminates_map_iff.mpr hprev
  have hprevmap : prev.map (fun p => ((p.1.1, p.1.2.map Prod.fst), p.2.1)) = e_C'.trans :=
    Stream'.Seq.append_singleton_inj_left _ _ htprevmap he' _ _ hmap'
  have hlast : (fun p => ((p.1.1, p.1.2.map Prod.fst), p.2.1)) last = ((l, ν), s_C') :=
    Stream'.Seq.append_singleton_inj_right _ _ htprevmap he' _ _ hmap'
  -- decompose the found `last` product step
  have hlab : last.1.1 = l := congrArg (fun x => x.1.1) hlast
  have hmapfst : last.1.2.map Prod.fst = ν := congrArg (fun x => x.1.2) hlast
  have hsC : last.2.1 = s_C' := congrArg (fun x => x.2) hlast
  have hlast_eq : last = ((l, last.1.2), (s_C', last.2.2)) := by
    obtain ⟨⟨ll, ωω⟩, ⟨sc, sa⟩⟩ := last
    simp only at hlab hsC
    subst hlab; subst hsC; rfl
  have h_init : r.1.init.1 = e_C'.init := by
    have := congrArg AlterSeq.init r.2
    rwa [show (concreteProjR r.1).init = r.1.init.1 from rfl] at this
  refine ⟨(⟨⟨r.1.init, prev⟩, ?_⟩, ⟨last.1.2, hmapfst⟩, last.2.2), ?_⟩
  · unfold concreteProjR
    rw [hprevmap]
    change (⟨r.1.init.1, e_C'.trans⟩ : ResolvedExec State_C Label) = e_C'
    rw [h_init]
  · apply Subtype.ext
    change (⟨r.1.init, prev.append (Seq.cons ((l, last.1.2), (s_C', last.2.2)) Seq.nil)⟩ :
      ResolvedExec (State_C × State_A) Label) = r.1
    rw [← hlast_eq, ← hsplit]

/-- The **concrete belief weight**: total `peJ`-mass over the `concreteProjR`-fibre of a concrete
resolved history `e_C`. The normalising denominator of the concrete scheduler; resolved analogue of
`avgWeight`. -/
noncomputable def cWeight (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (e_C : ResolvedExec State_C Label) (he : e_C.trans.Terminates) : ENNReal :=
  ∑' r : {r : ResolvedExec (State_C × State_A) Label // concreteProjR r = e_C},
    peJ.probOfR r.1 (terminates_of_concreteProjR_eq he r.2)

omit [Silent Label] in
/-- `cWeight` depends only on the history, not the termination proof. Concrete analogue of
`avgWeight_congr`. -/
theorem cWeight_congr (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (e e' : ResolvedExec State_C Label) (h : e = e')
    (he : e.trans.Terminates) (he' : e'.trans.Terminates) :
    cWeight peJ e he = cWeight peJ e' he' := by subst h; rfl

omit [Silent Label] in
/-- The un-normalised concrete emission has total mass `cWeight` (each pushforward emission is a
`PMF`, so summing over the emission variable collapses it to `1`). Resolved analogue of
`avgWeight_eq_tsum`. -/
theorem cWeight_eq_tsum (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (e_C : ResolvedExec State_C Label) (hT : e_C.trans.Terminates) :
    (∑' x : Option (Label × PMF State_C), ∑' r : {r : ResolvedExec (State_C × State_A) Label //
        concreteProjR r = e_C}, peJ.probOfR r.1 (terminates_of_concreteProjR_eq hT r.2)
          * ((peJ.scheduler.next r.1).map (mapEmit Prod.fst)) x)
      = cWeight peJ e_C hT := by
  rw [ENNReal.tsum_comm]
  unfold cWeight
  refine tsum_congr (fun r => ?_)
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

omit [Silent Label] in
/-- **Base of the fibre reindexing.** The empty concrete history's fibre is the abstract states
over `s₀`; its marginal is the pushed-forward initial mass. Concrete analogue of `avgWeight_nil`. -/
theorem cWeight_nil (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (s₀ : State_C) :
    cWeight peJ ⟨s₀, Seq.nil⟩ Stream'.Seq.terminates_nil
      = (peJ.initState.map Prod.fst) s₀ := by
  classical
  unfold cWeight
  -- reduce the fibre element's `probOfR` to the initial mass, then reindex by the abstract state.
  have hval : ∀ r : {r : ResolvedExec (State_C × State_A) Label // concreteProjR r = ⟨s₀, Seq.nil⟩},
      peJ.probOfR r.1 (terminates_of_concreteProjR_eq Stream'.Seq.terminates_nil r.2)
        = peJ.initState (s₀, r.1.init.2) := by
    rintro ⟨⟨ri, rt⟩, hr0⟩
    have htr : rt = Seq.nil := trans_nil_of_concreteProjR_nil hr0
    have hinit1 : ri.1 = s₀ := congrArg (fun x => x.init) hr0
    subst htr
    change peJ.probOfR ⟨ri, Seq.nil⟩ _ = peJ.initState (s₀, ri.2)
    rw [peJ.probOfR_nil ri, show ri = (s₀, ri.2) from by rw [← hinit1]]
  rw [tsum_congr hval, PMF.map_apply]
  -- the fibre `{r // concreteProjR r = ⟨s₀, nil⟩}` bijects with `State_A` via
  -- `s_A ↦ ⟨(s₀, s_A), nil⟩`.
  rw [show (∑' q : State_C × State_A, if s₀ = q.1 then peJ.initState q else 0)
        = ∑' s_A : State_A, peJ.initState (s₀, s_A) from by
      rw [ENNReal.tsum_prod']
      rw [tsum_eq_single s₀ (fun b hb => by
        simp only [show (s₀ = b) = False from eq_false (fun h => hb h.symm), if_false, tsum_zero])]
      refine tsum_congr (fun s_A => ?_)
      rw [if_pos rfl]]
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun s_A => ⟨⟨(s₀, s_A.1), Seq.nil⟩, by unfold concreteProjR; rw [Stream'.Seq.map_nil]⟩)
    ?_ ?_ ?_
  · intro a b hab
    have : ((s₀, a.1) : State_C × State_A) = (s₀, b.1) := congrArg (fun x => x.1.init) hab
    exact Subtype.ext (congrArg Prod.snd this)
  · intro r hr
    refine ⟨⟨r.1.init.2, ?_⟩, ?_⟩
    · rw [Function.mem_support] at hr ⊢; exact hr
    · apply Subtype.ext
      have htr : r.1.trans = Seq.nil := trans_nil_of_concreteProjR_nil r.2
      have hinit1 : r.1.init.1 = s₀ := congrArg (fun x => x.init) r.2
      change (⟨(s₀, r.1.init.2), Seq.nil⟩ : ResolvedExec (State_C × State_A) Label) = r.1
      rw [AlterSeq.mk.injEq]
      exact ⟨Prod.ext hinit1.symm rfl, htr.symm⟩
  · intro s_A; rfl

omit [Silent Label] in
/-- **Value identity** for the fibre reindexing: producing the `cSnocDecoration` of `p` is
producing `p.1` then the resolved step `((l, ω), (s_C', s_A'))`. Concrete analogue of
`probOfR_snocDecoration`. -/
theorem probOfR_cSnocDecoration (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    {e_C' : ResolvedExec State_C Label} (l : Label) (ν : PMF State_C) (s_C' : State_C)
    (p : {r' : ResolvedExec (State_C × State_A) Label // concreteProjR r' = e_C'} ×
      {ω : PMF (State_C × State_A) // ω.map Prod.fst = ν} × State_A)
    (h1 : (cSnocDecoration e_C' l ν s_C' p).1.trans.Terminates)
    (h2 : p.1.1.trans.Terminates) :
    peJ.probOfR (cSnocDecoration e_C' l ν s_C' p).1 h1
      = peJ.probOfR p.1.1 h2
        * (peJ.scheduler.next p.1.1 (some (l, p.2.1.1)) * p.2.1.1 (s_C', p.2.2)) := by
  change peJ.probOfR ⟨p.1.1.init,
      p.1.1.trans.append (Seq.cons ((l, p.2.1.1), (s_C', p.2.2)) Seq.nil)⟩ h1 = _
  rw [peJ.probOfR_append_singleton p.1.1.init p.1.1.trans h2 ((l, p.2.1.1), (s_C', p.2.2)) h1]
  rfl

omit [Silent Label] in
/-- The one-step concrete belief-kernel, summed over the coupling `ω` (in the `ν`-fibre) and
abstract successor `s_A'`, is bounded by `1`. Concrete analogue of `resolved_step_le_one`. -/
theorem c_step_le_one (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (r' : ResolvedExec (State_C × State_A) Label) (l : Label) (ν : PMF State_C) (s_C' : State_C) :
    (∑' p : {ω : PMF (State_C × State_A) // ω.map Prod.fst = ν} × State_A,
        peJ.scheduler.next r' (some (l, p.1.1)) * p.1.1 (s_C', p.2)) ≤ 1 := by
  calc (∑' p : {ω : PMF (State_C × State_A) // ω.map Prod.fst = ν} × State_A,
          peJ.scheduler.next r' (some (l, p.1.1)) * p.1.1 (s_C', p.2))
      ≤ ∑' p : PMF (State_C × State_A) × (State_C × State_A),
          peJ.scheduler.next r' (some (l, p.1)) * p.1 p.2 := by
        refine ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun p : {ω : PMF (State_C × State_A) // ω.map Prod.fst = ν} × State_A =>
            (p.1.1, (s_C', p.2)))
          (fun a b hab => ?_)
          (fun p : PMF (State_C × State_A) × (State_C × State_A) =>
            peJ.scheduler.next r' (some (l, p.1)) * p.1 p.2)
        obtain ⟨⟨ωa, hωa⟩, sa⟩ := a
        obtain ⟨⟨ωb, hωb⟩, sb⟩ := b
        simp only [Prod.mk.injEq] at hab
        obtain ⟨hω, -, hs⟩ := hab
        subst hω; subst hs; rfl
    _ = ∑' ω : PMF (State_C × State_A),
          peJ.scheduler.next r' (some (l, ω)) * ∑' q : State_C × State_A, ω q := by
        rw [ENNReal.tsum_prod']
        refine tsum_congr (fun ω => ?_)
        simp only
        rw [ENNReal.tsum_mul_left]
    _ = ∑' ω : PMF (State_C × State_A), peJ.scheduler.next r' (some (l, ω)) := by
        refine tsum_congr (fun ω => ?_)
        rw [PMF.tsum_coe, mul_one]
    _ ≤ ∑' lω : Label × PMF (State_C × State_A), peJ.scheduler.next r' (some lω) :=
        ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun ω => (l, ω)) (fun ω₁ ω₂ h_eq => (Prod.mk.inj h_eq).2)
          (fun lω => peJ.scheduler.next r' (some lω))
    _ ≤ ∑' opt, peJ.scheduler.next r' opt :=
        ENNReal.tsum_comp_le_tsum_of_injective
          (f := some) (fun _ _ h => Option.some.inj h) (fun opt => peJ.scheduler.next r' opt)
    _ = 1 := (peJ.scheduler.next r').tsum_coe

omit [Silent Label] in
/-- **Cons-end step of the fibre reindexing.** The marginal of `e_C' ++ ((l, ν), s_C')` is the
`probOfR`-weighted average, over decorations `r'` of `e_C'`, couplings `ω` (over `ν`) and abstract
successors, of one more resolved step. Concrete analogue of `avgWeight_append_singleton`. -/
theorem cWeight_append_singleton (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (e_C' : ResolvedExec State_C Label) (he' : e_C'.trans.Terminates)
    (l : Label) (ν : PMF State_C) (s_C' : State_C)
    (hE : (e_C'.trans.append (Seq.cons ((l, ν), s_C') Seq.nil)).Terminates) :
    cWeight peJ ⟨e_C'.init, e_C'.trans.append (Seq.cons ((l, ν), s_C') Seq.nil)⟩ hE
      = ∑' r' : {r' : ResolvedExec (State_C × State_A) Label // concreteProjR r' = e_C'},
          ∑' p : {ω : PMF (State_C × State_A) // ω.map Prod.fst = ν} × State_A,
            peJ.probOfR r'.1 (terminates_of_concreteProjR_eq he' r'.2)
              * (peJ.scheduler.next r'.1 (some (l, p.1.1)) * p.1.1 (s_C', p.2)) := by
  unfold cWeight
  have key : (∑' r : {r : ResolvedExec (State_C × State_A) Label //
        concreteProjR r = ⟨e_C'.init, e_C'.trans.append (Seq.cons ((l, ν), s_C') Seq.nil)⟩},
        peJ.probOfR r.1 (terminates_of_concreteProjR_eq hE r.2))
      = ∑' p : {r' : ResolvedExec (State_C × State_A) Label // concreteProjR r' = e_C'} ×
          {ω : PMF (State_C × State_A) // ω.map Prod.fst = ν} × State_A,
          peJ.probOfR p.1.1 (terminates_of_concreteProjR_eq he' p.1.2)
            * (peJ.scheduler.next p.1.1 (some (l, p.2.1.1)) * p.2.1.1 (s_C', p.2.2)) := by
    refine tsum_eq_tsum_of_ne_zero_bij
      (fun x => cSnocDecoration e_C' l ν s_C' x.1) ?_ ?_ ?_
    · exact fun x y hxy => Subtype.ext (cSnocDecoration_injective he' l ν s_C' hxy)
    · intro r hr
      obtain ⟨p, hp⟩ := exists_cSnocDecoration he' l ν s_C' r
      have hval : peJ.probOfR p.1.1 (terminates_of_concreteProjR_eq he' p.1.2)
            * (peJ.scheduler.next p.1.1 (some (l, p.2.1.1)) * p.2.1.1 (s_C', p.2.2))
          = peJ.probOfR r.1 (terminates_of_concreteProjR_eq hE r.2) := by
        rw [← hp]
        exact (probOfR_cSnocDecoration peJ l ν s_C' p _ _).symm
      exact ⟨⟨p, by rw [Function.mem_support, hval]; exact hr⟩, hp⟩
    · intro x
      exact probOfR_cSnocDecoration peJ l ν s_C' x.1 _ _
  rw [key]
  exact ENNReal.tsum_prod'

omit [Silent Label] in
/-- The belief weight is bounded by the (pushed-forward) initial mass, hence by `1`. Resolved
analogue of `avgWeight_le_init`; needed so the concrete emission normalises. -/
theorem cWeight_le_init (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (e_C : ResolvedExec State_C Label) (he : e_C.trans.Terminates) :
    cWeight peJ e_C he ≤ (peJ.initState.map Prod.fst) e_C.init := by
  suffices H : ∀ n (e_C : ResolvedExec State_C Label) (he : e_C.trans.Terminates),
      (e_C.trans.toList he).length = n →
        cWeight peJ e_C he ≤ (peJ.initState.map Prod.fst) e_C.init from H _ e_C he rfl
  intro n
  induction n with
  | zero =>
    intro e_C he hlen
    have htoList : e_C.trans.toList he = [] := List.length_eq_zero_iff.mp hlen
    obtain ⟨i, t⟩ := e_C
    have h_nil : t = Seq.nil := by
      have h := Stream'.Seq.ofList_toList t he
      rw [htoList, Stream'.Seq.ofList_nil] at h
      exact h.symm
    subst h_nil
    exact le_of_eq (cWeight_nil peJ i)
  | succ k ih =>
    intro e_C he hlen
    have hne : e_C.trans.toList he ≠ [] := by
      intro h; rw [h, List.length_nil] at hlen; exact Nat.succ_ne_zero k hlen.symm
    obtain ⟨prev, last, hprev, hsplit, hprevlist, -⟩ :=
      Stream'.Seq.exists_split_last e_C.trans he hne
    obtain ⟨lν, s_C'⟩ := last
    obtain ⟨l, ν⟩ := lν
    have happ : (prev.append (Seq.cons ((l, ν), s_C') Seq.nil)).Terminates := hsplit ▸ he
    have he_eq : e_C = ⟨e_C.init, prev.append (Seq.cons ((l, ν), s_C') Seq.nil)⟩ := by
      obtain ⟨ei, et⟩ := e_C; exact congrArg (AlterSeq.mk ei) hsplit
    have hlen_prev : (prev.toList hprev).length = k := by
      have h1 : (prev.toList hprev).length = (e_C.trans.toList he).length - 1 := by
        rw [hprevlist, List.length_dropLast]
      omega
    -- rewrite `cWeight e_C` as the cons-end sum.
    have h1 : cWeight peJ e_C he
        = ∑' r' : {r' : ResolvedExec (State_C × State_A) Label //
              concreteProjR r' = ⟨e_C.init, prev⟩},
            ∑' p : {ω : PMF (State_C × State_A) // ω.map Prod.fst = ν} × State_A,
              peJ.probOfR r'.1 (terminates_of_concreteProjR_eq hprev r'.2)
                * (peJ.scheduler.next r'.1 (some (l, p.1.1)) * p.1.1 (s_C', p.2)) := by
      rw [cWeight_congr peJ e_C ⟨e_C.init, prev.append (Seq.cons ((l, ν), s_C') Seq.nil)⟩
            he_eq he happ]
      exact cWeight_append_singleton peJ ⟨e_C.init, prev⟩ hprev l ν s_C' happ
    -- bound the inner coupling/successor sum by `1`.
    have h2 : (∑' r' : {r' : ResolvedExec (State_C × State_A) Label //
                  concreteProjR r' = ⟨e_C.init, prev⟩},
                ∑' p : {ω : PMF (State_C × State_A) // ω.map Prod.fst = ν} × State_A,
                  peJ.probOfR r'.1 (terminates_of_concreteProjR_eq hprev r'.2)
                    * (peJ.scheduler.next r'.1 (some (l, p.1.1)) * p.1.1 (s_C', p.2)))
          ≤ ∑' r' : {r' : ResolvedExec (State_C × State_A) Label //
                concreteProjR r' = ⟨e_C.init, prev⟩},
              peJ.probOfR r'.1 (terminates_of_concreteProjR_eq hprev r'.2) := by
      refine ENNReal.tsum_le_tsum (fun r' => ?_)
      rw [ENNReal.tsum_mul_left]
      calc peJ.probOfR r'.1 (terminates_of_concreteProjR_eq hprev r'.2)
            * ∑' p : {ω : PMF (State_C × State_A) // ω.map Prod.fst = ν} × State_A,
                peJ.scheduler.next r'.1 (some (l, p.1.1)) * p.1.1 (s_C', p.2)
          ≤ peJ.probOfR r'.1 (terminates_of_concreteProjR_eq hprev r'.2) * 1 := by
            gcongr
            exact c_step_le_one peJ r'.1 l ν s_C'
        _ = peJ.probOfR r'.1 (terminates_of_concreteProjR_eq hprev r'.2) := mul_one _
    rw [h1]
    refine h2.trans ?_
    have hinit_eq : (⟨e_C.init, prev⟩ : ResolvedExec State_C Label).init = e_C.init := rfl
    rw [show (peJ.initState.map Prod.fst) e_C.init
          = (peJ.initState.map Prod.fst) (⟨e_C.init, prev⟩ : ResolvedExec State_C Label).init
        from by rw [hinit_eq]]
    exact ih ⟨e_C.init, prev⟩ hprev hlen_prev

open Classical in
/-- The **concrete marginal**: the resolved execution on `sys_C` obtained by pushing `peJ` forward
along `Prod.fst` and averaging over the abstract fibres. Applied to `simJointExecR pe_C sim` this is
the concrete witness. Resolved analogue of `ResolvedProbabilisticExecution.average`. -/
noncomputable def concreteMarginal
    (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R)) :
    ResolvedProbabilisticExecution sys_C where
  initState := peJ.initState.map Prod.fst
  scheduler :=
    { next := fun r_C =>
        if hT : r_C.trans.Terminates then
          if h0 : cWeight peJ r_C hT ≠ 0 then
            PMF.normalize
              (fun x => ∑' r : {r : ResolvedExec (State_C × State_A) Label //
                  concreteProjR r = r_C},
                peJ.probOfR r.1 (terminates_of_concreteProjR_eq hT r.2)
                  * ((peJ.scheduler.next r.1).map (mapEmit Prod.fst)) x)
              (by rw [cWeight_eq_tsum peJ r_C hT]; exact h0)
              (by rw [cWeight_eq_tsum peJ r_C hT]
                  exact (((cWeight_le_init peJ r_C hT).trans (PMF.coe_le_one _ _)).trans_lt
                    ENNReal.one_lt_top).ne)
          else PMF.pure none
        else PMF.pure none
      valid := by
        classical
        intro r_C n s hterm hstate l ν hmem
        have hT : r_C.trans.Terminates := ⟨n, hterm⟩
        simp only [dif_pos hT] at hmem
        by_cases h0 : cWeight peJ r_C hT ≠ 0
        · rw [dif_pos h0, PMF.mem_support_iff, PMF.normalize_apply] at hmem
          have hN := (mul_ne_zero_iff.mp hmem).1
          -- extract a fibre element `r` whose pushforward emission carries mass on `some (l, ν)`.
          obtain ⟨r, hr⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hN)
          have hmapne : ((peJ.scheduler.next r.1).map (mapEmit Prod.fst)) (some (l, ν)) ≠ 0 :=
            fun h => hr (by rw [h, mul_zero])
          -- unpick the pushforward: some coupling `ω` over `ν` with `next r.1 (some (l, ω)) ≠ 0`.
          obtain ⟨ω, hωne, hνeq⟩ :
              ∃ ω : PMF (State_C × State_A),
                peJ.scheduler.next r.1 (some (l, ω)) ≠ 0 ∧ ν = ω.map Prod.fst := by
            rw [mapEmit, PMF.map_apply] at hmapne
            have hex2 := mt ENNReal.tsum_eq_zero.mpr hmapne
            push Not at hex2
            obtain ⟨o, ho⟩ := hex2
            by_cases hc : some (l, ν)
                = Option.map
                    (fun lμ : Label × PMF (State_C × State_A) => (lμ.1, lμ.2.map Prod.fst)) o
            · cases o with
              | none => simp at hc
              | some lμ =>
                obtain ⟨l', ω⟩ := lμ
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
                obtain ⟨rfl, rfl⟩ := hc
                exact ⟨ω, fun h0 => by rw [h0] at ho; simp at ho, rfl⟩
            · rw [if_neg hc] at ho; exact absurd rfl ho
          -- the current product state at `n` projects to `s`.
          have hstateP : (r.1.stateAt n).map Prod.fst = some s := by
            rw [← concreteProjR_stateAt r.1, r.2]; exact hstate
          obtain ⟨sP, hsPn, hfst⟩ :
              ∃ sP : State_C × State_A, r.1.stateAt n = some sP ∧ sP.1 = s := by
            cases hc : r.1.stateAt n with
            | none => rw [hc] at hstateP; simp at hstateP
            | some sP => rw [hc] at hstateP; exact ⟨sP, rfl, by simpa using hstateP⟩
          have htermP : r.1.trans.TerminatedAt n :=
            (concreteProjR_terminatedAt_iff r.1 n).mp (by rw [r.2]; exact hterm)
          -- `peJ.scheduler.valid` yields a `simProd`-step; project to the concrete factor.
          have hstepP : (simProd sys_C sys_A R).step sP l ω :=
            peJ.scheduler.valid r.1 n sP htermP hsPn l ω ((PMF.mem_support_iff _ _).mpr hωne)
          have hres : sys_C.step sP.1 l (ω.map Prod.fst) := hstepP.1
          rw [hfst, ← hνeq] at hres
          exact hres
        · rw [dif_neg h0] at hmem
          simp at hmem }

omit [Silent Label] in
/-- The functional label-preserving simulation `Prod.fst : simProd → sys_C` (a named `h_step` so the
`mapBeliefExec Prod.fst _` occurrences below are the *same* term, letting `rw` fire). -/
theorem simProd_hstep_fst :
    ∀ s l μ, (simProd sys_C sys_A R).step s l μ → sys_C.step (Prod.fst s) l (μ.map Prod.fst) :=
  fun _ _ _ h => h.1

omit [Silent Label] in
/-- The per-fibre identity powering `concreteMarginal_probOfR`'s cons-end step: for one product
decoration `r`, the pushforward emission on `(l, ν)` times the concrete successor mass `ν s_C'`
expands as the sum, over couplings `ω` over `ν` and abstract successors `s_A`, of the resolved
emission `peJ.next r (some (l, ω))` times `ω (s_C', s_A)`. The `mapEmit`/`PMF.map_apply` reindexing
mirrors `mappedKernel_eq` (`Construction/TraceMap.lean`). -/
theorem mapEmit_fst_mul
    (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (r : ResolvedExec (State_C × State_A) Label) (l : Label) (ν : PMF State_C) (s_C' : State_C) :
    ((peJ.scheduler.next r).map (mapEmit Prod.fst)) (some (l, ν)) * ν s_C'
      = ∑' p : {ω : PMF (State_C × State_A) // ω.map Prod.fst = ν} × State_A,
          peJ.scheduler.next r (some (l, p.1.1)) * p.1.1 (s_C', p.2) := by
  classical
  -- `((next r).map (mapEmit fst)) (some (l, ν))` unpicks to a sum over couplings `ω` with
  -- `ω.map fst = ν`, and `ν s_C' = ∑' s_A, ω (s_C', s_A)` for each such `ω`.
  have hstep1 : ((peJ.scheduler.next r).map (mapEmit Prod.fst)) (some (l, ν))
      = ∑' ω : {ω : PMF (State_C × State_A) // ω.map Prod.fst = ν},
          peJ.scheduler.next r (some (l, ω.1)) := by
    rw [mapEmit, PMF.map_apply]
    rw [← Function.Injective.tsum_eq
          (g := fun ω : {ω : PMF (State_C × State_A) // ω.map Prod.fst = ν} => some (l, ω.1))
        (fun a b hab => Subtype.ext (by simpa using hab)) ?supp]
    · refine tsum_congr (fun ω => ?_)
      rw [if_pos (show some (l, ν) = Option.map
          (fun lμ : Label × PMF (State_C × State_A) => (lμ.1, lμ.2.map Prod.fst)) (some (l, ω.1))
          from by rw [Option.map_some, ω.2])]
    case supp =>
      intro o ho
      rw [Function.mem_support] at ho
      by_contra hcon
      apply ho
      by_cases hc : some (l, ν)
          = Option.map (fun lμ : Label × PMF (State_C × State_A) => (lμ.1, lμ.2.map Prod.fst)) o
      · exfalso; apply hcon
        cases o with
        | none => simp at hc
        | some lμ =>
          obtain ⟨l', ω⟩ := lμ
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, hν⟩ := hc
          exact ⟨⟨ω, hν.symm⟩, rfl⟩
      · rw [if_neg hc]
  rw [hstep1, ← ENNReal.tsum_mul_right, ENNReal.tsum_prod']
  refine tsum_congr (fun ω => ?_)
  have hν : ν s_C' = ∑' s_A : State_A, ω.1 (s_C', s_A) := by
    have h2 : (ω.1.map Prod.fst) s_C' = ∑' s_A : State_A, ω.1 (s_C', s_A) := by
      rw [PMF.map_apply, ENNReal.tsum_prod']
      rw [tsum_eq_single s_C' (fun b hb => by
        simp only [show (s_C' = b) = False from eq_false (fun h => hb h.symm), if_false,
          tsum_zero])]
      refine tsum_congr (fun sa => ?_)
      rw [if_pos rfl]
    rw [← h2, ω.2]
  rw [hν, ← ENNReal.tsum_mul_left]

omit [Silent Label] in
/-- The concrete-marginal emission on a `some (l, ν)` step: the (normalised) `probOfR`-weighted
pushforward mixture of `peJ`'s emissions over the `concreteProjR`-fibre of `r_C`. Concrete analogue
of `ResolvedProbabilisticExecution.average_next_some`. Holds in both branches: when `cWeight = 0`
both sides are `0` (using `0 * ⊤ = 0`). -/
private theorem concreteMarginal_next_some
    (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (r_C : ResolvedExec State_C Label) (hT : r_C.trans.Terminates) (l : Label) (ν : PMF State_C) :
    (concreteMarginal peJ).scheduler.next r_C (some (l, ν))
      = (∑' r : {r : ResolvedExec (State_C × State_A) Label // concreteProjR r = r_C},
            peJ.probOfR r.1 (terminates_of_concreteProjR_eq hT r.2)
              * ((peJ.scheduler.next r.1).map (mapEmit Prod.fst)) (some (l, ν)))
          * (cWeight peJ r_C hT)⁻¹ := by
  classical
  by_cases hW : cWeight peJ r_C hT ≠ 0
  · change (if hT' : r_C.trans.Terminates then _ else PMF.pure none) (some (l, ν)) = _
    rw [dif_pos hT, dif_pos hW, PMF.normalize_apply, cWeight_eq_tsum peJ r_C hT]
  · rw [not_not] at hW
    have hN : (∑' r : {r : ResolvedExec (State_C × State_A) Label // concreteProjR r = r_C},
        peJ.probOfR r.1 (terminates_of_concreteProjR_eq hT r.2)
          * ((peJ.scheduler.next r.1).map (mapEmit Prod.fst)) (some (l, ν))) = 0 := by
      refine ENNReal.tsum_eq_zero.mpr (fun r => ?_)
      have hz : peJ.probOfR r.1 (terminates_of_concreteProjR_eq hT r.2) = 0 := by
        have := ENNReal.tsum_eq_zero.mp (show cWeight peJ r_C hT = 0 from hW) r
        exact this
      rw [hz, zero_mul]
    rw [hN, zero_mul]
    change (if hT' : r_C.trans.Terminates then _ else PMF.pure none) (some (l, ν)) = 0
    rw [dif_pos hT, dif_neg (fun h => h hW)]
    simp

omit [Silent Label] in
/-- **Value telescoping** for `concreteMarginal`: its `probOfR` of a resolved concrete history `r_C`
collapses to the belief weight `cWeight peJ r_C`. Concrete analogue of
`ResolvedProbabilisticExecution.probOf_average` (here landing on `cWeight`, using the
already-built `cWeight_nil` / `cWeight_append_singleton` cons-end machinery). -/
theorem concreteMarginal_probOfR
    (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (r_C : ResolvedExec State_C Label) (hT : r_C.trans.Terminates) :
    (concreteMarginal peJ).probOfR r_C hT = cWeight peJ r_C hT := by
  suffices H : ∀ n (r_C : ResolvedExec State_C Label) (hT : r_C.trans.Terminates),
      (r_C.trans.toList hT).length = n →
      (concreteMarginal peJ).probOfR r_C hT = cWeight peJ r_C hT from H _ r_C hT rfl
  intro n
  induction n with
  | zero =>
    intro r_C hT hlen
    have htoList : r_C.trans.toList hT = [] := List.length_eq_zero_iff.mp hlen
    obtain ⟨i, t⟩ := r_C
    have h_nil : t = Seq.nil := by
      have h := Stream'.Seq.ofList_toList t hT
      rw [htoList, Stream'.Seq.ofList_nil] at h
      exact h.symm
    subst h_nil
    rw [(concreteMarginal peJ).probOfR_nil i, cWeight_nil peJ i]
    rfl
  | succ k ih =>
    intro r_C hT hlen
    have hne : r_C.trans.toList hT ≠ [] := by
      intro h; rw [h, List.length_nil] at hlen; exact Nat.succ_ne_zero k hlen.symm
    obtain ⟨prev, last, hprev, hsplit, hprevlist, -⟩ :=
      Stream'.Seq.exists_split_last r_C.trans hT hne
    obtain ⟨lν, s_C'⟩ := last
    obtain ⟨l, ν⟩ := lν
    have happ : (prev.append (Seq.cons ((l, ν), s_C') Seq.nil)).Terminates := hsplit ▸ hT
    have hr_eq : r_C = ⟨r_C.init, prev.append (Seq.cons ((l, ν), s_C') Seq.nil)⟩ := by
      obtain ⟨ri, rt⟩ := r_C; exact congrArg (AlterSeq.mk ri) hsplit
    have hlen_prev : (prev.toList hprev).length = k := by
      have h1 : (prev.toList hprev).length = (r_C.trans.toList hT).length - 1 := by
        rw [hprevlist, List.length_dropLast]
      omega
    -- LHS: cons-end factorisation of `probOfR` + IH.
    have hLcongr : (concreteMarginal peJ).probOfR r_C hT
        = (concreteMarginal peJ).probOfR
            ⟨r_C.init, prev.append (Seq.cons ((l, ν), s_C') Seq.nil)⟩ happ := by
      congr 1
    rw [hLcongr,
        (concreteMarginal peJ).probOfR_append_singleton r_C.init prev hprev ((l, ν), s_C') happ,
        ih ⟨r_C.init, prev⟩ hprev hlen_prev]
    -- RHS: cons-end sum for `cWeight` of the extended history.
    rw [cWeight_congr peJ r_C ⟨r_C.init, prev.append (Seq.cons ((l, ν), s_C') Seq.nil)⟩ hr_eq
          hT happ,
        cWeight_append_singleton peJ ⟨r_C.init, prev⟩ hprev l ν s_C' happ]
    -- Reduce the emission and cancel the belief-weight denominator.
    unfold ResolvedProbabilisticExecution.rkernel
    rw [concreteMarginal_next_some peJ ⟨r_C.init, prev⟩ hprev l ν]
    -- Both sides are sums over the `concreteProjR`-fibre of `⟨r_C.init, prev⟩`; abbreviate the
    -- belief weight `W` and the emission numerator `Num`, and reduce the RHS per fibre element.
    set W := cWeight peJ ⟨r_C.init, prev⟩ hprev with hWdef
    set Num := ∑' r : {r : ResolvedExec (State_C × State_A) Label //
          concreteProjR r = ⟨r_C.init, prev⟩},
        peJ.probOfR r.1 (terminates_of_concreteProjR_eq hprev r.2)
          * ((peJ.scheduler.next r.1).map (mapEmit Prod.fst)) (some (l, ν)) with hNumdef
    -- The RHS equals `Num * ν s_C'` (push the successor mass into each fibre summand).
    have hRHS : (∑' r' : {r' : ResolvedExec (State_C × State_A) Label //
            concreteProjR r' = ⟨r_C.init, prev⟩}, ∑' p : {ω : PMF (State_C × State_A) //
              ω.map Prod.fst = ν} × State_A,
            peJ.probOfR r'.1 (terminates_of_concreteProjR_eq hprev r'.2)
              * (peJ.scheduler.next r'.1 (some (l, p.1.1)) * p.1.1 (s_C', p.2)))
        = Num * ((l, ν), s_C').1.2 ((l, ν), s_C').2 := by
      simp only
      rw [hNumdef, ← ENNReal.tsum_mul_right]
      refine tsum_congr (fun r' => ?_)
      rw [ENNReal.tsum_mul_left, mul_assoc, mapEmit_fst_mul peJ r'.1 l ν s_C']
    rw [hRHS]
    -- Cancel `W * (Num * W⁻¹ * c) = Num * c`, handling the `W = 0` branch.
    by_cases hW : W = 0
    · have hNum0 : Num = 0 := by
        rw [hNumdef]
        refine ENNReal.tsum_eq_zero.mpr (fun r => ?_)
        have : peJ.probOfR r.1 (terminates_of_concreteProjR_eq hprev r.2) = 0 :=
          ENNReal.tsum_eq_zero.mp (show W = 0 from hW) r
        rw [this, zero_mul]
      rw [hW, hNum0]; simp
    · have hWtop : W ≠ ⊤ := by
        rw [hWdef]
        exact (((cWeight_le_init peJ ⟨r_C.init, prev⟩ hprev).trans (PMF.coe_le_one _ _)).trans_lt
          ENNReal.one_lt_top).ne
      rw [show W * (Num * W⁻¹ * ((l, ν), s_C').1.2 ((l, ν), s_C').2)
            = W * W⁻¹ * (Num * ((l, ν), s_C').1.2 ((l, ν), s_C').2) from by ring,
          ENNReal.mul_inv_cancel hW hWtop, one_mul]

omit [Silent Label] in
/-- The plain image of the concrete projection is the `Prod.fst`-image of the plain image:
forgetting the recorded `μ`s of `concreteProjR r` agrees with `Prod.fst`-mapping the forgotten plain
history `r.toExec`. -/
private theorem concreteProjR_toExec (r : ResolvedExec (State_C × State_A) Label) :
    (concreteProjR r).toExec = (r.toExec).map Prod.fst := by
  unfold concreteProjR ResolvedExec.toExec AlterSeq.map
  congr 1
  simp only [← Stream'.Seq.map_comp]
  rfl

omit [Silent Label] in
/-- Termination transfer: if the `Prod.fst`-image of `r.toExec` is a terminating concrete history,
then `r` itself terminates. -/
private theorem terminates_of_toExec_map_fst
    {r : ResolvedExec (State_C × State_A) Label} {E_C : AlterSeq State_C Label}
    (hE : E_C.trans.Terminates) (hr : (r.toExec).map Prod.fst = E_C) : r.trans.Terminates :=
  (ResolvedExec.toExec_terminates_iff r).mp
    ((AlterSeq.map_trans_terminates_iff Prod.fst r.toExec).mp (by rw [hr]; exact hE))

/-- **[unconditional core]** The concrete marginal's marginal weight equals the total
`peJ.average`-mass over the `Prod.fst`-fibre of `E_C`, i.e. `mapWeight Prod.fst peJ.average E_C`.
Both sides regroup to `∑' (r with (r.toExec).map Prod.fst = E_C), peJ.probOfR r`: the LHS via
`concreteMarginal_probOfR` + the `concreteProjR`-fibre grouping, the RHS via `probOf_average` + the
`Prod.fst`-fibre grouping. No init hypothesis is used here (it enters only when turning `mapWeight`
back into `mapBeliefExec.probOf`). -/
private theorem avgWeight_concreteMarginal_eq_mapWeight
    (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (E_C : AlterSeq State_C Label) (hE : E_C.trans.Terminates) :
    (concreteMarginal peJ).avgWeight E_C hE = mapWeight Prod.fst peJ.average E_C := by
  classical
  -- **LHS = ∑' (r with (r.toExec).map fst = E_C), peJ.probOfR r.**
  have hLHS : (concreteMarginal peJ).avgWeight E_C hE
      = ∑' r : {r : ResolvedExec (State_C × State_A) Label // (r.toExec).map Prod.fst = E_C},
          peJ.probOfR r.1 (terminates_of_toExec_map_fst hE r.2) := by
    unfold ResolvedProbabilisticExecution.avgWeight
    rw [show (∑' r_C : {r_C : ResolvedExec State_C Label // r_C.toExec = E_C},
          (concreteMarginal peJ).probOfR r_C.1 (ResolvedExec.terminates_of_toExec_eq hE r_C.2))
        = ∑' r_C : {r_C : ResolvedExec State_C Label // r_C.toExec = E_C},
          cWeight peJ r_C.1 (ResolvedExec.terminates_of_toExec_eq hE r_C.2) from
        tsum_congr (fun r_C => concreteMarginal_probOfR peJ r_C.1
          (ResolvedExec.terminates_of_toExec_eq hE r_C.2))]
    unfold cWeight
    rw [← ENNReal.tsum_sigma' (f := fun p : Σ r_C : {r_C : ResolvedExec State_C Label //
        r_C.toExec = E_C}, {r : ResolvedExec (State_C × State_A) Label //
          concreteProjR r = r_C.1} =>
          peJ.probOfR p.2.1 (terminates_of_concreteProjR_eq
            (ResolvedExec.terminates_of_toExec_eq hE p.1.2) p.2.2))]
    refine tsum_eq_tsum_of_ne_zero_bij
      (fun r => ⟨⟨concreteProjR r.1.1, by rw [concreteProjR_toExec r.1.1]; exact r.1.2⟩,
        ⟨r.1.1, rfl⟩⟩) ?_ ?_ ?_
    · intro a b hh
      exact Subtype.ext (Subtype.ext (congrArg (fun q => (q.2.1 : _)) hh))
    · intro p hp
      have hmemsupp : (⟨p.2.1, by rw [← concreteProjR_toExec p.2.1, p.2.2]; exact p.1.2⟩ :
          {r : ResolvedExec (State_C × State_A) Label // (r.toExec).map Prod.fst = E_C})
          ∈ Function.support fun r => peJ.probOfR r.1
            (terminates_of_toExec_map_fst hE r.2) := by
        rw [Function.mem_support] at hp ⊢
        change peJ.probOfR p.2.1 _ ≠ 0 at hp; exact hp
      refine ⟨⟨_, hmemsupp⟩, ?_⟩
      apply Sigma.subtype_ext
      · exact Subtype.ext p.2.2
      · rfl
    · intro r; rfl
  -- **RHS = the same fibre sum**, via `probOf_average` and the `Prod.fst`-fibre grouping.
  have hRHS : mapWeight Prod.fst peJ.average E_C
      = ∑' r : {r : ResolvedExec (State_C × State_A) Label // (r.toExec).map Prod.fst = E_C},
          peJ.probOfR r.1 (terminates_of_toExec_map_fst hE r.2) := by
    unfold mapWeight
    -- Group the `dite` over the `Prod.fst`-fibre subtype, and rewrite `probOf → avgWeight`.
    rw [show (∑' E_X : AlterSeq (State_C × State_A) Label,
          dite (E_X.trans.Terminates ∧ E_X.map Prod.fst = E_C)
            (fun h => peJ.average.probOf E_X h.1) (fun _ => 0))
        = ∑' E_X : {E_X : AlterSeq (State_C × State_A) Label // E_X.map Prod.fst = E_C},
            peJ.avgWeight E_X.1 ((AlterSeq.map_trans_terminates_iff Prod.fst E_X.1).mp
              (by rw [E_X.2]; exact hE)) from ?grp]
    · -- Regroup `∑' E_X ∑' (r with r.toExec = E_X)` into `∑' (r with (r.toExec).map fst = E_C)`.
      unfold ResolvedProbabilisticExecution.avgWeight
      rw [← ENNReal.tsum_sigma' (f := fun p : Σ E_X : {E_X : AlterSeq (State_C × State_A) Label //
          E_X.map Prod.fst = E_C},
            {r : ResolvedExec (State_C × State_A) Label // r.toExec = E_X.1} =>
            peJ.probOfR p.2.1 (ResolvedExec.terminates_of_toExec_eq
              ((AlterSeq.map_trans_terminates_iff Prod.fst p.1.1).mp (by rw [p.1.2]; exact hE))
              p.2.2))]
      refine tsum_eq_tsum_of_ne_zero_bij
        (fun r => ⟨⟨r.1.1.toExec, r.1.2⟩, ⟨r.1.1, rfl⟩⟩) ?_ ?_ ?_
      · intro a b hh
        exact Subtype.ext (Subtype.ext (congrArg (fun q => (q.2.1 : _)) hh))
      · intro p hp
        have hmemsupp : (⟨p.2.1, by rw [p.2.2]; exact p.1.2⟩ :
            {r : ResolvedExec (State_C × State_A) Label // (r.toExec).map Prod.fst = E_C})
            ∈ Function.support fun r => peJ.probOfR r.1
              (terminates_of_toExec_map_fst hE r.2) := by
          rw [Function.mem_support] at hp ⊢
          change peJ.probOfR p.2.1 _ ≠ 0 at hp; exact hp
        refine ⟨⟨_, hmemsupp⟩, ?_⟩
        apply Sigma.subtype_ext
        · exact Subtype.ext p.2.2
        · rfl
      · intro r; rfl
    case grp =>
      refine tsum_eq_tsum_of_ne_zero_bij (fun E_X => E_X.1.1) ?_ ?_ ?_
      · intro a b hh; exact Subtype.ext (Subtype.ext hh)
      · intro E_X hE_X
        rw [Function.mem_support] at hE_X
        have hc : E_X.trans.Terminates ∧ E_X.map Prod.fst = E_C := by
          by_contra hcon; exact hE_X (dif_neg hcon)
        refine ⟨⟨⟨E_X, hc.2⟩, ?_⟩, rfl⟩
        rw [Function.mem_support]
        intro h0
        rw [show peJ.avgWeight E_X _ = peJ.average.probOf E_X hc.1 from
            (peJ.probOf_average E_X hc.1).symm] at h0
        exact hE_X (by rw [dif_pos hc, h0])
      · intro E_X
        rw [dif_pos ⟨(AlterSeq.map_trans_terminates_iff Prod.fst E_X.1.1).mp
              (by rw [E_X.1.2]; exact hE), E_X.1.2⟩,
            peJ.probOf_average E_X.1.1 _]
  rw [hLHS, hRHS]

/-- **[technical, cons-end induction]** The concrete marginal's marginal weight over the
`μ`-decorations of a concrete history equals the plain belief-map's path measure — i.e.
`concreteMarginal peJ` *de-resolves* to `mapBeliefExec Prod.fst _ peJ.average`. Resolved analogue of
the `mapBeliefExec_probOf` cons-end induction fused with `probOf_average`.

The unconditional content is `avgWeight_concreteMarginal_eq_mapWeight`
(`avgWeight = mapWeight Prod.fst`); turning `mapWeight` back into the belief-map path measure needs
`peJ` to start from the Dirac joint-initial distribution (`h_init`) — without it the two sides
disagree at the empty history, since `mapBeliefExec` is built with a Dirac init. Every call site
supplies `h_init` (`simJointExecR` has `PMF.pure (simProd …).init` by construction). -/
theorem avgWeight_concreteMarginal
    (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (h_init : peJ.initState = PMF.pure (simProd sys_C sys_A R).init)
    (E_C : AlterSeq State_C Label) (hE : E_C.trans.Terminates) :
    (concreteMarginal peJ).avgWeight E_C hE
      = (mapBeliefExec Prod.fst simProd_hstep_fst peJ.average).probOf E_C hE := by
  -- The unconditional content: `avgWeight` de-resolves to the fibre mass `mapWeight Prod.fst`.
  rw [avgWeight_concreteMarginal_eq_mapWeight peJ E_C hE]
  -- Turn `mapWeight` back into the belief-map path measure via `mapBeliefExec_probOf`, whose
  -- initial-mass hypotheses are `Prod.fst (simProd …).init = sys_C.init` (definitional, `rfl`) and
  -- `peJ.average.initState = PMF.pure (simProd …).init` (from `h_init`, since `average` keeps the
  -- initial distribution: `peJ.average.initState` is `peJ.initState` definitionally).
  exact (mapBeliefExec_probOf Prod.fst simProd_hstep_fst peJ.average rfl h_init E_C hE).symm

/-- **The concrete marginal preserves `traceProbR`.** Assembled from `avgWeight_concreteMarginal`
and the existing plain results `mapBeliefExec_traceProb`, `traceProb_average`. No finiteness. -/
theorem concreteMarginal_traceProbR
    (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (h_init : peJ.initState = PMF.pure (simProd sys_C sys_A R).init) (τ : Seq Label) :
    (concreteMarginal peJ).traceProbR τ = peJ.traceProbR τ := by
  rw [← (concreteMarginal peJ).traceProbR_eq_sum_avgWeight τ,
    show (∑' e : {e : AlterSeq State_C Label //
          e.trans.Terminates ∧ sys_C.trace e = τ ∧ sys_C.IsTight e},
        (concreteMarginal peJ).avgWeight e.1 e.2.1)
      = ∑' e : {e : AlterSeq State_C Label //
          e.trans.Terminates ∧ sys_C.trace e = τ ∧ sys_C.IsTight e},
        (mapBeliefExec Prod.fst simProd_hstep_fst peJ.average).probOf e.1 e.2.1 from
      tsum_congr (fun e => avgWeight_concreteMarginal peJ h_init e.1 e.2.1)]
  change sys_C.traceProb (mapBeliefExec Prod.fst simProd_hstep_fst peJ.average) τ
    = peJ.traceProbR τ
  rw [mapBeliefExec_traceProb Prod.fst simProd_hstep_fst peJ.average rfl h_init τ]
  exact peJ.traceProb_average τ

end FairStrongProbabilisticSimulation

end PLTS
