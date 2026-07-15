/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2Extra.Fairness.Simulation.Defs

/-!
# The abstract marginal of the coupled resolved execution (step 2, `Prod.snd`)

Marginalise the coupled resolved execution of `simProd sys_C sys_A R` onto `sys_A` via `Prod.snd`.
On an abstract resolved history `r_A` the scheduler emits the (normalised) `probOfR`-weighted
pushforward (`mapEmit Prod.snd`) of the coupled emissions over the `absProjR`-fibre of product
histories; the total fibre mass is the belief weight `absWeight`. This file develops `absWeight`
(with its `absProjR`-fibre reindexing: base `absWeight_nil`, cons-end `absWeight_append_singleton`,
bound `absWeight_le_init`), the abstract marginal `abstractMarginal`, and the value-telescoping
identity culminating in `avgWeight_abstractMarginal` (the abstract marginal *de-resolves* to
`mapBeliefExec Prod.snd _ peJ.average`). The `Prod.fst` mirror is
`Simulation/Fair/ConcreteMarginal`.
-/

open Stream'

namespace PLTS

variable {State_C State_A Label : Type} [Silent Label]

namespace FairStrongProbabilisticSimulation

variable {sys_C : System State_C Label} {sys_A : System State_A Label}
  {F_C : Fairness sys_C} {F_A : Fairness sys_A} {R : State_C → State_A → Prop}

/-! ### The abstract marginal (the projection, step 2 of the construction)

The resolved analogue of `ResolvedProbabilisticExecution.average` combined with
`mapBeliefExec` along `Prod.snd`: marginalise a resolved execution `peJ` of the coupled product onto
`sys_A`. On an abstract resolved history `r_A` the scheduler emits the (normalised)
`probOfR`-weighted **pushforward** (`mapEmit Prod.snd`) of `peJ`'s emissions over the
`absProjR`-fibre `{r // absProjR r = r_A}` of product histories. The total fibre mass is
`absWeight`. -/

/-- The **belief weight**: total `peJ`-mass over the `absProjR`-fibre of an abstract resolved
history `e_A`. The normalising denominator of the abstract scheduler; resolved analogue of
`avgWeight`. -/
noncomputable def absWeight (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (e_A : ResolvedExec State_A Label) (he : e_A.trans.Terminates) : ENNReal :=
  ∑' r : {r : ResolvedExec (State_C × State_A) Label // absProjR r = e_A},
    peJ.probOfR r.1 (terminates_of_absProjR_eq he r.2)

omit [Silent Label] in
/-- `absWeight` depends only on the history, not the termination proof. Abstract analogue of
`avgWeight_congr`. -/
theorem absWeight_congr (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (e e' : ResolvedExec State_A Label) (h : e = e')
    (he : e.trans.Terminates) (he' : e'.trans.Terminates) :
    absWeight peJ e he = absWeight peJ e' he' := by subst h; rfl

omit [Silent Label] in
/-- The un-normalised abstract emission has total mass `absWeight` (each pushforward emission is a
`PMF`, so summing over the emission variable collapses it to `1`). Resolved analogue of
`avgWeight_eq_tsum`. -/
theorem absWeight_eq_tsum (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (e_A : ResolvedExec State_A Label) (hT : e_A.trans.Terminates) :
    (∑' x : Option (Label × PMF State_A), ∑' r : {r : ResolvedExec (State_C × State_A) Label //
        absProjR r = e_A}, peJ.probOfR r.1 (terminates_of_absProjR_eq hT r.2)
          * ((peJ.scheduler.next r.1).map (mapEmit Prod.snd)) x)
      = absWeight peJ e_A hT := by
  rw [ENNReal.tsum_comm]
  unfold absWeight
  refine tsum_congr (fun r => ?_)
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

omit [Silent Label] in
/-- **Base of the fibre reindexing.** The empty abstract history's fibre is the concrete states
over `s₀`; its marginal is the pushed-forward initial mass. Abstract analogue of `avgWeight_nil`. -/
theorem absWeight_nil (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (s₀ : State_A) :
    absWeight peJ ⟨s₀, Seq.nil⟩ Stream'.Seq.terminates_nil
      = (peJ.initState.map Prod.snd) s₀ := by
  classical
  unfold absWeight
  -- reduce the fibre element's `probOfR` to the initial mass, then reindex by the concrete state.
  have hval : ∀ r : {r : ResolvedExec (State_C × State_A) Label // absProjR r = ⟨s₀, Seq.nil⟩},
      peJ.probOfR r.1 (terminates_of_absProjR_eq Stream'.Seq.terminates_nil r.2)
        = peJ.initState (r.1.init.1, s₀) := by
    rintro ⟨⟨ri, rt⟩, hr0⟩
    have htr : rt = Seq.nil := trans_nil_of_absProjR_nil hr0
    have hinit2 : ri.2 = s₀ := congrArg (fun x => x.init) hr0
    subst htr
    change peJ.probOfR ⟨ri, Seq.nil⟩ _ = peJ.initState (ri.1, s₀)
    rw [peJ.probOfR_nil ri, show ri = (ri.1, s₀) from by rw [← hinit2]]
  rw [tsum_congr hval, PMF.map_apply]
  -- the fibre `{r // absProjR r = ⟨s₀, nil⟩}` bijects with `State_C` via `s_C ↦ ⟨(s_C, s₀), nil⟩`.
  rw [show (∑' q : State_C × State_A, if s₀ = q.2 then peJ.initState q else 0)
        = ∑' s_C : State_C, peJ.initState (s_C, s₀) from by
      rw [ENNReal.tsum_prod']
      refine tsum_congr (fun s_C => ?_)
      rw [tsum_eq_single s₀ (fun b hb => by rw [if_neg (fun h => hb h.symm)]), if_pos rfl]]
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun s_C => ⟨⟨(s_C.1, s₀), Seq.nil⟩, by unfold absProjR; rw [Stream'.Seq.map_nil]⟩) ?_ ?_ ?_
  · intro a b hab
    have : ((a.1, s₀) : State_C × State_A) = (b.1, s₀) := congrArg (fun x => x.1.init) hab
    exact Subtype.ext (congrArg Prod.fst this)
  · intro r hr
    refine ⟨⟨r.1.init.1, ?_⟩, ?_⟩
    · rw [Function.mem_support] at hr ⊢; exact hr
    · apply Subtype.ext
      have htr : r.1.trans = Seq.nil := trans_nil_of_absProjR_nil r.2
      have hinit2 : r.1.init.2 = s₀ := congrArg (fun x => x.init) r.2
      change (⟨(r.1.init.1, s₀), Seq.nil⟩ : ResolvedExec (State_C × State_A) Label) = r.1
      rw [AlterSeq.mk.injEq]
      exact ⟨Prod.ext rfl hinit2.symm, htr.symm⟩
  · intro s_C; rfl

omit [Silent Label] in
/-- **Value identity** for the fibre reindexing: producing the `absSnocDecoration` of `p` is
producing `p.1` then the resolved step `((l, ω), (s_C', s_A'))`. Abstract analogue of
`probOfR_snocDecoration`. -/
theorem probOfR_absSnocDecoration (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    {e_A' : ResolvedExec State_A Label} (l : Label) (ν : PMF State_A) (s_A' : State_A)
    (p : {r' : ResolvedExec (State_C × State_A) Label // absProjR r' = e_A'} ×
      {ω : PMF (State_C × State_A) // ω.map Prod.snd = ν} × State_C)
    (h1 : (absSnocDecoration e_A' l ν s_A' p).1.trans.Terminates)
    (h2 : p.1.1.trans.Terminates) :
    peJ.probOfR (absSnocDecoration e_A' l ν s_A' p).1 h1
      = peJ.probOfR p.1.1 h2
        * (peJ.scheduler.next p.1.1 (some (l, p.2.1.1)) * p.2.1.1 (p.2.2, s_A')) := by
  change peJ.probOfR ⟨p.1.1.init,
      p.1.1.trans.append (Seq.cons ((l, p.2.1.1), (p.2.2, s_A')) Seq.nil)⟩ h1 = _
  rw [peJ.probOfR_append_singleton p.1.1.init p.1.1.trans h2 ((l, p.2.1.1), (p.2.2, s_A')) h1]
  rfl

omit [Silent Label] in
/-- The one-step abstract belief-kernel, summed over the coupling `ω` (in the `ν`-fibre) and
concrete successor `s_C'`, is bounded by `1`. Abstract analogue of `resolved_step_le_one`. -/
theorem abs_step_le_one (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (r' : ResolvedExec (State_C × State_A) Label) (l : Label) (ν : PMF State_A) (s_A' : State_A) :
    (∑' p : {ω : PMF (State_C × State_A) // ω.map Prod.snd = ν} × State_C,
        peJ.scheduler.next r' (some (l, p.1.1)) * p.1.1 (p.2, s_A')) ≤ 1 := by
  calc (∑' p : {ω : PMF (State_C × State_A) // ω.map Prod.snd = ν} × State_C,
          peJ.scheduler.next r' (some (l, p.1.1)) * p.1.1 (p.2, s_A'))
      ≤ ∑' p : PMF (State_C × State_A) × (State_C × State_A),
          peJ.scheduler.next r' (some (l, p.1)) * p.1 p.2 := by
        refine ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun p : {ω : PMF (State_C × State_A) // ω.map Prod.snd = ν} × State_C =>
            (p.1.1, (p.2, s_A')))
          (fun a b hab => ?_)
          (fun p : PMF (State_C × State_A) × (State_C × State_A) =>
            peJ.scheduler.next r' (some (l, p.1)) * p.1 p.2)
        obtain ⟨⟨ωa, hωa⟩, sa⟩ := a
        obtain ⟨⟨ωb, hωb⟩, sb⟩ := b
        simp only [Prod.mk.injEq] at hab
        obtain ⟨hω, hs, -⟩ := hab
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
/-- **Cons-end step of the fibre reindexing.** The marginal of `e_A' ++ ((l, ν), s_A')` is the
`probOfR`-weighted average, over decorations `r'` of `e_A'`, couplings `ω` (over `ν`) and concrete
successors, of one more resolved step. Abstract analogue of `avgWeight_append_singleton`. -/
theorem absWeight_append_singleton (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (e_A' : ResolvedExec State_A Label) (he' : e_A'.trans.Terminates)
    (l : Label) (ν : PMF State_A) (s_A' : State_A)
    (hE : (e_A'.trans.append (Seq.cons ((l, ν), s_A') Seq.nil)).Terminates) :
    absWeight peJ ⟨e_A'.init, e_A'.trans.append (Seq.cons ((l, ν), s_A') Seq.nil)⟩ hE
      = ∑' r' : {r' : ResolvedExec (State_C × State_A) Label // absProjR r' = e_A'},
          ∑' p : {ω : PMF (State_C × State_A) // ω.map Prod.snd = ν} × State_C,
            peJ.probOfR r'.1 (terminates_of_absProjR_eq he' r'.2)
              * (peJ.scheduler.next r'.1 (some (l, p.1.1)) * p.1.1 (p.2, s_A')) := by
  unfold absWeight
  have key : (∑' r : {r : ResolvedExec (State_C × State_A) Label //
        absProjR r = ⟨e_A'.init, e_A'.trans.append (Seq.cons ((l, ν), s_A') Seq.nil)⟩},
        peJ.probOfR r.1 (terminates_of_absProjR_eq hE r.2))
      = ∑' p : {r' : ResolvedExec (State_C × State_A) Label // absProjR r' = e_A'} ×
          {ω : PMF (State_C × State_A) // ω.map Prod.snd = ν} × State_C,
          peJ.probOfR p.1.1 (terminates_of_absProjR_eq he' p.1.2)
            * (peJ.scheduler.next p.1.1 (some (l, p.2.1.1)) * p.2.1.1 (p.2.2, s_A')) := by
    refine tsum_eq_tsum_of_ne_zero_bij
      (fun x => absSnocDecoration e_A' l ν s_A' x.1) ?_ ?_ ?_
    · exact fun x y hxy => Subtype.ext (absSnocDecoration_injective he' l ν s_A' hxy)
    · intro r hr
      obtain ⟨p, hp⟩ := exists_absSnocDecoration he' l ν s_A' r
      have hval : peJ.probOfR p.1.1 (terminates_of_absProjR_eq he' p.1.2)
            * (peJ.scheduler.next p.1.1 (some (l, p.2.1.1)) * p.2.1.1 (p.2.2, s_A'))
          = peJ.probOfR r.1 (terminates_of_absProjR_eq hE r.2) := by
        rw [← hp]
        exact (probOfR_absSnocDecoration peJ l ν s_A' p _ _).symm
      exact ⟨⟨p, by rw [Function.mem_support, hval]; exact hr⟩, hp⟩
    · intro x
      exact probOfR_absSnocDecoration peJ l ν s_A' x.1 _ _
  rw [key]
  exact ENNReal.tsum_prod'

omit [Silent Label] in
/-- The belief weight is bounded by the (pushed-forward) initial mass, hence by `1`. Resolved
analogue of `avgWeight_le_init`; needed so the abstract emission normalises. -/
theorem absWeight_le_init (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (e_A : ResolvedExec State_A Label) (he : e_A.trans.Terminates) :
    absWeight peJ e_A he ≤ (peJ.initState.map Prod.snd) e_A.init := by
  suffices H : ∀ n (e_A : ResolvedExec State_A Label) (he : e_A.trans.Terminates),
      (e_A.trans.toList he).length = n →
        absWeight peJ e_A he ≤ (peJ.initState.map Prod.snd) e_A.init from H _ e_A he rfl
  intro n
  induction n with
  | zero =>
    intro e_A he hlen
    have htoList : e_A.trans.toList he = [] := List.length_eq_zero_iff.mp hlen
    obtain ⟨i, t⟩ := e_A
    have h_nil : t = Seq.nil := by
      have h := Stream'.Seq.ofList_toList t he
      rw [htoList, Stream'.Seq.ofList_nil] at h
      exact h.symm
    subst h_nil
    exact le_of_eq (absWeight_nil peJ i)
  | succ k ih =>
    intro e_A he hlen
    have hne : e_A.trans.toList he ≠ [] := by
      intro h; rw [h, List.length_nil] at hlen; exact Nat.succ_ne_zero k hlen.symm
    obtain ⟨prev, last, hprev, hsplit, hprevlist, -⟩ :=
      Stream'.Seq.exists_split_last e_A.trans he hne
    obtain ⟨lν, s_A'⟩ := last
    obtain ⟨l, ν⟩ := lν
    have happ : (prev.append (Seq.cons ((l, ν), s_A') Seq.nil)).Terminates := hsplit ▸ he
    have he_eq : e_A = ⟨e_A.init, prev.append (Seq.cons ((l, ν), s_A') Seq.nil)⟩ := by
      obtain ⟨ei, et⟩ := e_A; exact congrArg (AlterSeq.mk ei) hsplit
    have hlen_prev : (prev.toList hprev).length = k := by
      have h1 : (prev.toList hprev).length = (e_A.trans.toList he).length - 1 := by
        rw [hprevlist, List.length_dropLast]
      omega
    -- rewrite `absWeight e_A` as the cons-end sum.
    have h1 : absWeight peJ e_A he
        = ∑' r' : {r' : ResolvedExec (State_C × State_A) Label // absProjR r' = ⟨e_A.init, prev⟩},
            ∑' p : {ω : PMF (State_C × State_A) // ω.map Prod.snd = ν} × State_C,
              peJ.probOfR r'.1 (terminates_of_absProjR_eq hprev r'.2)
                * (peJ.scheduler.next r'.1 (some (l, p.1.1)) * p.1.1 (p.2, s_A')) := by
      rw [absWeight_congr peJ e_A ⟨e_A.init, prev.append (Seq.cons ((l, ν), s_A') Seq.nil)⟩
            he_eq he happ]
      exact absWeight_append_singleton peJ ⟨e_A.init, prev⟩ hprev l ν s_A' happ
    -- bound the inner coupling/successor sum by `1`.
    have h2 : (∑' r' : {r' : ResolvedExec (State_C × State_A) Label //
                  absProjR r' = ⟨e_A.init, prev⟩},
                ∑' p : {ω : PMF (State_C × State_A) // ω.map Prod.snd = ν} × State_C,
                  peJ.probOfR r'.1 (terminates_of_absProjR_eq hprev r'.2)
                    * (peJ.scheduler.next r'.1 (some (l, p.1.1)) * p.1.1 (p.2, s_A')))
          ≤ ∑' r' : {r' : ResolvedExec (State_C × State_A) Label // absProjR r' = ⟨e_A.init, prev⟩},
              peJ.probOfR r'.1 (terminates_of_absProjR_eq hprev r'.2) := by
      refine ENNReal.tsum_le_tsum (fun r' => ?_)
      rw [ENNReal.tsum_mul_left]
      calc peJ.probOfR r'.1 (terminates_of_absProjR_eq hprev r'.2)
            * ∑' p : {ω : PMF (State_C × State_A) // ω.map Prod.snd = ν} × State_C,
                peJ.scheduler.next r'.1 (some (l, p.1.1)) * p.1.1 (p.2, s_A')
          ≤ peJ.probOfR r'.1 (terminates_of_absProjR_eq hprev r'.2) * 1 := by
            gcongr
            exact abs_step_le_one peJ r'.1 l ν s_A'
        _ = peJ.probOfR r'.1 (terminates_of_absProjR_eq hprev r'.2) := mul_one _
    rw [h1]
    refine h2.trans ?_
    have hinit_eq : (⟨e_A.init, prev⟩ : ResolvedExec State_A Label).init = e_A.init := rfl
    rw [show (peJ.initState.map Prod.snd) e_A.init
          = (peJ.initState.map Prod.snd) (⟨e_A.init, prev⟩ : ResolvedExec State_A Label).init
        from by rw [hinit_eq]]
    exact ih ⟨e_A.init, prev⟩ hprev hlen_prev

open Classical in
/-- The **abstract marginal**: the resolved execution on `sys_A` obtained by pushing `peJ` forward
along `Prod.snd` and averaging over the concrete fibres. Applied to `simJointExecR pe_C sim` this is
the abstract witness `pe_A`. Resolved analogue of `ResolvedProbabilisticExecution.average`. -/
noncomputable def abstractMarginal
    (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R)) :
    ResolvedProbabilisticExecution sys_A where
  initState := peJ.initState.map Prod.snd
  scheduler :=
    { next := fun r_A =>
        if hT : r_A.trans.Terminates then
          if h0 : absWeight peJ r_A hT ≠ 0 then
            PMF.normalize
              (fun x => ∑' r : {r : ResolvedExec (State_C × State_A) Label // absProjR r = r_A},
                peJ.probOfR r.1 (terminates_of_absProjR_eq hT r.2)
                  * ((peJ.scheduler.next r.1).map (mapEmit Prod.snd)) x)
              (by rw [absWeight_eq_tsum peJ r_A hT]; exact h0)
              (by rw [absWeight_eq_tsum peJ r_A hT]
                  exact (((absWeight_le_init peJ r_A hT).trans (PMF.coe_le_one _ _)).trans_lt
                    ENNReal.one_lt_top).ne)
          else PMF.pure none
        else PMF.pure none
      valid := by
        classical
        intro r_A n s hterm hstate l ν hmem
        have hT : r_A.trans.Terminates := ⟨n, hterm⟩
        simp only [dif_pos hT] at hmem
        by_cases h0 : absWeight peJ r_A hT ≠ 0
        · rw [dif_pos h0, PMF.mem_support_iff, PMF.normalize_apply] at hmem
          have hN := (mul_ne_zero_iff.mp hmem).1
          -- extract a fibre element `r` whose pushforward emission carries mass on `some (l, ν)`.
          obtain ⟨r, hr⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hN)
          have hmapne : ((peJ.scheduler.next r.1).map (mapEmit Prod.snd)) (some (l, ν)) ≠ 0 :=
            fun h => hr (by rw [h, mul_zero])
          -- unpick the pushforward: some coupling `ω` over `ν` with `next r.1 (some (l, ω)) ≠ 0`.
          obtain ⟨ω, hωne, hνeq⟩ :
              ∃ ω : PMF (State_C × State_A),
                peJ.scheduler.next r.1 (some (l, ω)) ≠ 0 ∧ ν = ω.map Prod.snd := by
            rw [mapEmit, PMF.map_apply] at hmapne
            have hex2 := mt ENNReal.tsum_eq_zero.mpr hmapne
            push Not at hex2
            obtain ⟨o, ho⟩ := hex2
            by_cases hc : some (l, ν)
                = Option.map
                    (fun lμ : Label × PMF (State_C × State_A) => (lμ.1, lμ.2.map Prod.snd)) o
            · cases o with
              | none => simp at hc
              | some lμ =>
                obtain ⟨l', ω⟩ := lμ
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
                obtain ⟨rfl, rfl⟩ := hc
                exact ⟨ω, fun h0 => by rw [h0] at ho; simp at ho, rfl⟩
            · rw [if_neg hc] at ho; exact absurd rfl ho
          -- the current product state at `n` projects to `s`.
          have hstateP : (r.1.stateAt n).map Prod.snd = some s := by
            rw [← absProjR_stateAt r.1, r.2]; exact hstate
          obtain ⟨sP, hsPn, hsnd⟩ :
              ∃ sP : State_C × State_A, r.1.stateAt n = some sP ∧ sP.2 = s := by
            cases hc : r.1.stateAt n with
            | none => rw [hc] at hstateP; simp at hstateP
            | some sP => rw [hc] at hstateP; exact ⟨sP, rfl, by simpa using hstateP⟩
          have htermP : r.1.trans.TerminatedAt n :=
            (absProjR_terminatedAt_iff r.1 n).mp (by rw [r.2]; exact hterm)
          -- `peJ.scheduler.valid` yields a `simProd`-step; project to the abstract factor.
          have hstepP : (simProd sys_C sys_A R).step sP l ω :=
            peJ.scheduler.valid r.1 n sP htermP hsPn l ω ((PMF.mem_support_iff _ _).mpr hωne)
          have hres : sys_A.step sP.2 l (ω.map Prod.snd) := hstepP.2.1
          rw [hsnd, ← hνeq] at hres
          exact hres
        · rw [dif_neg h0] at hmem
          simp at hmem }

omit [Silent Label] in
/-- The functional label-preserving simulation `Prod.snd : simProd → sys_A` (a named `h_step` so the
`mapBeliefExec Prod.snd _` occurrences below are the *same* term, letting `rw` fire). -/
theorem simProd_hstep_snd :
    ∀ s l μ, (simProd sys_C sys_A R).step s l μ → sys_A.step (Prod.snd s) l (μ.map Prod.snd) :=
  fun _ _ _ h => h.2.1

/-! ### Trace preservation (Phase 3)

The construction preserves `traceProbR`, with **no finiteness assumption**, in two halves relayed by
`abstractMarginal_simJointExecR_traceProbR`:

* **Abstract-marginal half — DONE (axiom-clean):** `abstractMarginal_traceProbR`
  (`pe_A.traceProbR = simJointExecR.traceProbR`). Here the abstract marginal *does* de-resolve
  per-history to the plain belief map (`avgWeight_abstractMarginal`:
  `avgWeight = (mapBeliefExec Prod.snd _ peJ.average).probOf`), reducing to the existing plain
  `mapBeliefExec_traceProb` + `traceProb_average`.

* **Coupled-lift half:** `simJointExecR_traceProbR`
  (`simJointExecR.traceProbR = pe_C.traceProbR`). This one does **not** de-resolve per-history (see
  the ⚠ note below); it needs the abstract successor marginalised within each label class (the plain
  `simExecMarginal`/`simKernelMarginal` route, or the concrete-marginal packaging). -/

/-! ### ⚠ The coupled lift does NOT de-resolve per-history

One might hope, mirroring the abstract-marginal side, that the coupled resolved lift de-resolves
*per plain product history* to the plain coupled execution, i.e.
`(simJointExecR pe_C sim).avgWeight E = (simJointExec pe_C.average sim.toStrong).probOf E`.
**This is false.** `PMFRel`/`simCouple` may split one concrete successor's mass across several
abstract successors, so on a fixed product history `E` (which pins the *joint* successor
`(s_C', s_A')`) the joint fibre weight uses `ω (s_C', s_A')`, strictly below the concrete marginal
`μ_C s_C'`, by a deficit that varies across decorations. Concrete length-2 counterexample:
`pe_C` emits `μ_A = δ_{c1}` / `μ_B = ½δ_{c1}+½δ_{c2}` (each w.p. ½) with couplings
`ω_A = δ_{(c1,d1)}`, `ω_B = ¼δ_{(c1,d1)}+¼δ_{(c1,d2)}+½δ_{(c2,d1)}`: the two sides give `35/72` vs
`13/24`. The *trace* equality `simJointExecR.traceProbR = pe_C.traceProbR` still holds — the deficit
sums out over abstract successors — but its proof must marginalise the abstract successor **before**
comparing (the plain `simExecMarginal`/`simKernelMarginal` argument), not compare per history. See
`simJointExecR_traceProbR` (proven in `Simulation/Fair/Trace.lean`). -/

omit [Silent Label] in
/-- The per-fibre identity powering `abstractMarginal_probOfR`'s cons-end step: for one product
decoration `r`, the pushforward emission on `(l, ν)` times the abstract successor mass `ν s_A'`
expands as the sum, over couplings `ω` over `ν` and concrete successors `s_C`, of the resolved
emission `peJ.next r (some (l, ω))` times `ω (s_C, s_A')`. The `mapEmit`/`PMF.map_apply` reindexing
mirrors `mappedKernel_eq` (`Construction/TraceMap.lean`). -/
private theorem mapEmit_snd_mul
    (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (r : ResolvedExec (State_C × State_A) Label) (l : Label) (ν : PMF State_A) (s_A' : State_A) :
    ((peJ.scheduler.next r).map (mapEmit Prod.snd)) (some (l, ν)) * ν s_A'
      = ∑' p : {ω : PMF (State_C × State_A) // ω.map Prod.snd = ν} × State_C,
          peJ.scheduler.next r (some (l, p.1.1)) * p.1.1 (p.2, s_A') := by
  classical
  -- `((next r).map (mapEmit snd)) (some (l, ν))` unpicks to a sum over couplings `ω` with
  -- `ω.map snd = ν`, and `ν s_A' = ∑' s_C, ω (s_C, s_A')` for each such `ω`.
  have hstep1 : ((peJ.scheduler.next r).map (mapEmit Prod.snd)) (some (l, ν))
      = ∑' ω : {ω : PMF (State_C × State_A) // ω.map Prod.snd = ν},
          peJ.scheduler.next r (some (l, ω.1)) := by
    rw [mapEmit, PMF.map_apply]
    rw [← Function.Injective.tsum_eq
          (g := fun ω : {ω : PMF (State_C × State_A) // ω.map Prod.snd = ν} => some (l, ω.1))
        (fun a b hab => Subtype.ext (by simpa using hab)) ?supp]
    · refine tsum_congr (fun ω => ?_)
      rw [if_pos (show some (l, ν) = Option.map
          (fun lμ : Label × PMF (State_C × State_A) => (lμ.1, lμ.2.map Prod.snd)) (some (l, ω.1))
          from by rw [Option.map_some, ω.2])]
    case supp =>
      intro o ho
      rw [Function.mem_support] at ho
      by_contra hcon
      apply ho
      by_cases hc : some (l, ν)
          = Option.map (fun lμ : Label × PMF (State_C × State_A) => (lμ.1, lμ.2.map Prod.snd)) o
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
  have hν : ν s_A' = ∑' s_C : State_C, ω.1 (s_C, s_A') := by
    have h2 : (ω.1.map Prod.snd) s_A' = ∑' s_C : State_C, ω.1 (s_C, s_A') := by
      rw [PMF.map_apply, ENNReal.tsum_prod']
      refine tsum_congr (fun sc => ?_)
      rw [tsum_eq_single s_A' (fun b hb => by rw [if_neg (fun h => hb h.symm)]), if_pos rfl]
    rw [← h2, ω.2]
  rw [hν, ← ENNReal.tsum_mul_left]

omit [Silent Label] in
/-- The abstract-marginal emission on a `some (l, ν)` step: the (normalised) `probOfR`-weighted
pushforward mixture of `peJ`'s emissions over the `absProjR`-fibre of `r_A`. Abstract analogue of
`ResolvedProbabilisticExecution.average_next_some`. Holds in both branches: when `absWeight = 0`
both sides are `0` (using `0 * ⊤ = 0`). -/
theorem abstractMarginal_next_some
    (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (r_A : ResolvedExec State_A Label) (hT : r_A.trans.Terminates) (l : Label) (ν : PMF State_A) :
    (abstractMarginal peJ).scheduler.next r_A (some (l, ν))
      = (∑' r : {r : ResolvedExec (State_C × State_A) Label // absProjR r = r_A},
            peJ.probOfR r.1 (terminates_of_absProjR_eq hT r.2)
              * ((peJ.scheduler.next r.1).map (mapEmit Prod.snd)) (some (l, ν)))
          * (absWeight peJ r_A hT)⁻¹ := by
  classical
  by_cases hW : absWeight peJ r_A hT ≠ 0
  · change (if hT' : r_A.trans.Terminates then _ else PMF.pure none) (some (l, ν)) = _
    rw [dif_pos hT, dif_pos hW, PMF.normalize_apply, absWeight_eq_tsum peJ r_A hT]
  · rw [not_not] at hW
    have hN : (∑' r : {r : ResolvedExec (State_C × State_A) Label // absProjR r = r_A},
        peJ.probOfR r.1 (terminates_of_absProjR_eq hT r.2)
          * ((peJ.scheduler.next r.1).map (mapEmit Prod.snd)) (some (l, ν))) = 0 := by
      refine ENNReal.tsum_eq_zero.mpr (fun r => ?_)
      have hz : peJ.probOfR r.1 (terminates_of_absProjR_eq hT r.2) = 0 := by
        have := ENNReal.tsum_eq_zero.mp (show absWeight peJ r_A hT = 0 from hW) r
        exact this
      rw [hz, zero_mul]
    rw [hN, zero_mul]
    change (if hT' : r_A.trans.Terminates then _ else PMF.pure none) (some (l, ν)) = 0
    rw [dif_pos hT, dif_neg (fun h => h hW)]
    simp

omit [Silent Label] in
/-- **Value telescoping** for `abstractMarginal`: its `probOfR` of a resolved abstract history `r_A`
collapses to the belief weight `absWeight peJ r_A`. Abstract analogue of
`ResolvedProbabilisticExecution.probOf_average` (here landing on `absWeight`, using the
already-built `absWeight_nil` / `absWeight_append_singleton` cons-end machinery). -/
theorem abstractMarginal_probOfR
    (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (r_A : ResolvedExec State_A Label) (hT : r_A.trans.Terminates) :
    (abstractMarginal peJ).probOfR r_A hT = absWeight peJ r_A hT := by
  suffices H : ∀ n (r_A : ResolvedExec State_A Label) (hT : r_A.trans.Terminates),
      (r_A.trans.toList hT).length = n →
      (abstractMarginal peJ).probOfR r_A hT = absWeight peJ r_A hT from H _ r_A hT rfl
  intro n
  induction n with
  | zero =>
    intro r_A hT hlen
    have htoList : r_A.trans.toList hT = [] := List.length_eq_zero_iff.mp hlen
    obtain ⟨i, t⟩ := r_A
    have h_nil : t = Seq.nil := by
      have h := Stream'.Seq.ofList_toList t hT
      rw [htoList, Stream'.Seq.ofList_nil] at h
      exact h.symm
    subst h_nil
    rw [(abstractMarginal peJ).probOfR_nil i, absWeight_nil peJ i]
    rfl
  | succ k ih =>
    intro r_A hT hlen
    have hne : r_A.trans.toList hT ≠ [] := by
      intro h; rw [h, List.length_nil] at hlen; exact Nat.succ_ne_zero k hlen.symm
    obtain ⟨prev, last, hprev, hsplit, hprevlist, -⟩ :=
      Stream'.Seq.exists_split_last r_A.trans hT hne
    obtain ⟨lν, s_A'⟩ := last
    obtain ⟨l, ν⟩ := lν
    have happ : (prev.append (Seq.cons ((l, ν), s_A') Seq.nil)).Terminates := hsplit ▸ hT
    have hr_eq : r_A = ⟨r_A.init, prev.append (Seq.cons ((l, ν), s_A') Seq.nil)⟩ := by
      obtain ⟨ri, rt⟩ := r_A; exact congrArg (AlterSeq.mk ri) hsplit
    have hlen_prev : (prev.toList hprev).length = k := by
      have h1 : (prev.toList hprev).length = (r_A.trans.toList hT).length - 1 := by
        rw [hprevlist, List.length_dropLast]
      omega
    -- LHS: cons-end factorisation of `probOfR` + IH.
    have hLcongr : (abstractMarginal peJ).probOfR r_A hT
        = (abstractMarginal peJ).probOfR
            ⟨r_A.init, prev.append (Seq.cons ((l, ν), s_A') Seq.nil)⟩ happ := by
      congr 1
    rw [hLcongr,
        (abstractMarginal peJ).probOfR_append_singleton r_A.init prev hprev ((l, ν), s_A') happ,
        ih ⟨r_A.init, prev⟩ hprev hlen_prev]
    -- RHS: cons-end sum for `absWeight` of the extended history.
    rw [absWeight_congr peJ r_A ⟨r_A.init, prev.append (Seq.cons ((l, ν), s_A') Seq.nil)⟩ hr_eq
          hT happ,
        absWeight_append_singleton peJ ⟨r_A.init, prev⟩ hprev l ν s_A' happ]
    -- Reduce the emission and cancel the belief-weight denominator.
    unfold ResolvedProbabilisticExecution.rkernel
    rw [abstractMarginal_next_some peJ ⟨r_A.init, prev⟩ hprev l ν]
    -- Both sides are sums over the `absProjR`-fibre of `⟨r_A.init, prev⟩`; abbreviate the belief
    -- weight `W` and the emission numerator `Num`, and reduce the RHS per fibre element.
    set W := absWeight peJ ⟨r_A.init, prev⟩ hprev with hWdef
    set Num := ∑' r : {r : ResolvedExec (State_C × State_A) Label // absProjR r = ⟨r_A.init, prev⟩},
        peJ.probOfR r.1 (terminates_of_absProjR_eq hprev r.2)
          * ((peJ.scheduler.next r.1).map (mapEmit Prod.snd)) (some (l, ν)) with hNumdef
    -- The RHS equals `Num * ν s_A'` (push the successor mass into each fibre summand).
    have hRHS : (∑' r' : {r' : ResolvedExec (State_C × State_A) Label //
            absProjR r' = ⟨r_A.init, prev⟩}, ∑' p : {ω : PMF (State_C × State_A) //
              ω.map Prod.snd = ν} × State_C,
            peJ.probOfR r'.1 (terminates_of_absProjR_eq hprev r'.2)
              * (peJ.scheduler.next r'.1 (some (l, p.1.1)) * p.1.1 (p.2, s_A')))
        = Num * ((l, ν), s_A').1.2 ((l, ν), s_A').2 := by
      simp only
      rw [hNumdef, ← ENNReal.tsum_mul_right]
      refine tsum_congr (fun r' => ?_)
      rw [ENNReal.tsum_mul_left, mul_assoc, mapEmit_snd_mul peJ r'.1 l ν s_A']
    rw [hRHS]
    -- Cancel `W * (Num * W⁻¹ * c) = Num * c`, handling the `W = 0` branch.
    by_cases hW : W = 0
    · have hNum0 : Num = 0 := by
        rw [hNumdef]
        refine ENNReal.tsum_eq_zero.mpr (fun r => ?_)
        have : peJ.probOfR r.1 (terminates_of_absProjR_eq hprev r.2) = 0 :=
          ENNReal.tsum_eq_zero.mp (show W = 0 from hW) r
        rw [this, zero_mul]
      rw [hW, hNum0]; simp
    · have hWtop : W ≠ ⊤ := by
        rw [hWdef]
        exact (((absWeight_le_init peJ ⟨r_A.init, prev⟩ hprev).trans (PMF.coe_le_one _ _)).trans_lt
          ENNReal.one_lt_top).ne
      rw [show W * (Num * W⁻¹ * ((l, ν), s_A').1.2 ((l, ν), s_A').2)
            = W * W⁻¹ * (Num * ((l, ν), s_A').1.2 ((l, ν), s_A').2) from by ring,
          ENNReal.mul_inv_cancel hW hWtop, one_mul]

omit [Silent Label] in
/-- The plain image of the abstract projection is the `Prod.snd`-image of the plain image:
forgetting the recorded `μ`s of `absProjR r` agrees with `Prod.snd`-mapping the forgotten plain
history `r.toExec`. -/
private theorem absProjR_toExec (r : ResolvedExec (State_C × State_A) Label) :
    (absProjR r).toExec = (r.toExec).map Prod.snd := by
  unfold absProjR ResolvedExec.toExec AlterSeq.map
  congr 1
  simp only [← Stream'.Seq.map_comp]
  rfl

omit [Silent Label] in
/-- Termination transfer: if the `Prod.snd`-image of `r.toExec` is a terminating abstract history,
then `r` itself terminates. -/
private theorem terminates_of_toExec_map_snd
    {r : ResolvedExec (State_C × State_A) Label} {E_A : AlterSeq State_A Label}
    (hE : E_A.trans.Terminates) (hr : (r.toExec).map Prod.snd = E_A) : r.trans.Terminates :=
  (ResolvedExec.toExec_terminates_iff r).mp
    ((AlterSeq.map_trans_terminates_iff Prod.snd r.toExec).mp (by rw [hr]; exact hE))

/-- **[unconditional core]** The abstract marginal's marginal weight equals the total
`peJ.average`-mass over the `Prod.snd`-fibre of `E_A`, i.e. `mapWeight Prod.snd peJ.average E_A`.
Both sides regroup to `∑' (r with (r.toExec).map Prod.snd = E_A), peJ.probOfR r`: the LHS via
`abstractMarginal_probOfR` + the `absProjR`-fibre grouping, the RHS via `probOf_average` + the
`Prod.snd`-fibre grouping. No init hypothesis is used here (it enters only when turning `mapWeight`
back into `mapBeliefExec.probOf`). -/
private theorem avgWeight_abstractMarginal_eq_mapWeight
    (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (E_A : AlterSeq State_A Label) (hE : E_A.trans.Terminates) :
    (abstractMarginal peJ).avgWeight E_A hE = mapWeight Prod.snd peJ.average E_A := by
  classical
  -- **LHS = ∑' (r with (r.toExec).map snd = E_A), peJ.probOfR r.**
  have hLHS : (abstractMarginal peJ).avgWeight E_A hE
      = ∑' r : {r : ResolvedExec (State_C × State_A) Label // (r.toExec).map Prod.snd = E_A},
          peJ.probOfR r.1 (terminates_of_toExec_map_snd hE r.2) := by
    unfold ResolvedProbabilisticExecution.avgWeight
    rw [show (∑' r_A : {r_A : ResolvedExec State_A Label // r_A.toExec = E_A},
          (abstractMarginal peJ).probOfR r_A.1 (ResolvedExec.terminates_of_toExec_eq hE r_A.2))
        = ∑' r_A : {r_A : ResolvedExec State_A Label // r_A.toExec = E_A},
          absWeight peJ r_A.1 (ResolvedExec.terminates_of_toExec_eq hE r_A.2) from
        tsum_congr (fun r_A => abstractMarginal_probOfR peJ r_A.1
          (ResolvedExec.terminates_of_toExec_eq hE r_A.2))]
    unfold absWeight
    rw [← ENNReal.tsum_sigma' (f := fun p : Σ r_A : {r_A : ResolvedExec State_A Label //
        r_A.toExec = E_A}, {r : ResolvedExec (State_C × State_A) Label // absProjR r = r_A.1} =>
          peJ.probOfR p.2.1 (terminates_of_absProjR_eq
            (ResolvedExec.terminates_of_toExec_eq hE p.1.2) p.2.2))]
    refine tsum_eq_tsum_of_ne_zero_bij
      (fun r => ⟨⟨absProjR r.1.1, by rw [absProjR_toExec r.1.1]; exact r.1.2⟩,
        ⟨r.1.1, rfl⟩⟩) ?_ ?_ ?_
    · intro a b hh
      exact Subtype.ext (Subtype.ext (congrArg (fun q => (q.2.1 : _)) hh))
    · intro p hp
      have hmemsupp : (⟨p.2.1, by rw [← absProjR_toExec p.2.1, p.2.2]; exact p.1.2⟩ :
          {r : ResolvedExec (State_C × State_A) Label // (r.toExec).map Prod.snd = E_A})
          ∈ Function.support fun r => peJ.probOfR r.1
            (terminates_of_toExec_map_snd hE r.2) := by
        rw [Function.mem_support] at hp ⊢
        change peJ.probOfR p.2.1 _ ≠ 0 at hp; exact hp
      refine ⟨⟨_, hmemsupp⟩, ?_⟩
      apply Sigma.subtype_ext
      · exact Subtype.ext p.2.2
      · rfl
    · intro r; rfl
  -- **RHS = the same fibre sum**, via `probOf_average` and the `Prod.snd`-fibre grouping.
  have hRHS : mapWeight Prod.snd peJ.average E_A
      = ∑' r : {r : ResolvedExec (State_C × State_A) Label // (r.toExec).map Prod.snd = E_A},
          peJ.probOfR r.1 (terminates_of_toExec_map_snd hE r.2) := by
    unfold mapWeight
    -- Group the `dite` over the `Prod.snd`-fibre subtype, and rewrite `probOf → avgWeight`.
    rw [show (∑' E_X : AlterSeq (State_C × State_A) Label,
          dite (E_X.trans.Terminates ∧ E_X.map Prod.snd = E_A)
            (fun h => peJ.average.probOf E_X h.1) (fun _ => 0))
        = ∑' E_X : {E_X : AlterSeq (State_C × State_A) Label // E_X.map Prod.snd = E_A},
            peJ.avgWeight E_X.1 ((AlterSeq.map_trans_terminates_iff Prod.snd E_X.1).mp
              (by rw [E_X.2]; exact hE)) from ?grp]
    · -- Regroup `∑' E_X ∑' (r with r.toExec = E_X)` into `∑' (r with (r.toExec).map snd = E_A)`.
      unfold ResolvedProbabilisticExecution.avgWeight
      rw [← ENNReal.tsum_sigma' (f := fun p : Σ E_X : {E_X : AlterSeq (State_C × State_A) Label //
          E_X.map Prod.snd = E_A},
            {r : ResolvedExec (State_C × State_A) Label // r.toExec = E_X.1} =>
            peJ.probOfR p.2.1 (ResolvedExec.terminates_of_toExec_eq
              ((AlterSeq.map_trans_terminates_iff Prod.snd p.1.1).mp (by rw [p.1.2]; exact hE))
              p.2.2))]
      refine tsum_eq_tsum_of_ne_zero_bij
        (fun r => ⟨⟨r.1.1.toExec, r.1.2⟩, ⟨r.1.1, rfl⟩⟩) ?_ ?_ ?_
      · intro a b hh
        exact Subtype.ext (Subtype.ext (congrArg (fun q => (q.2.1 : _)) hh))
      · intro p hp
        have hmemsupp : (⟨p.2.1, by rw [p.2.2]; exact p.1.2⟩ :
            {r : ResolvedExec (State_C × State_A) Label // (r.toExec).map Prod.snd = E_A})
            ∈ Function.support fun r => peJ.probOfR r.1
              (terminates_of_toExec_map_snd hE r.2) := by
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
        have hc : E_X.trans.Terminates ∧ E_X.map Prod.snd = E_A := by
          by_contra hcon; exact hE_X (dif_neg hcon)
        refine ⟨⟨⟨E_X, hc.2⟩, ?_⟩, rfl⟩
        rw [Function.mem_support]
        intro h0
        rw [show peJ.avgWeight E_X _ = peJ.average.probOf E_X hc.1 from
            (peJ.probOf_average E_X hc.1).symm] at h0
        exact hE_X (by rw [dif_pos hc, h0])
      · intro E_X
        rw [dif_pos ⟨(AlterSeq.map_trans_terminates_iff Prod.snd E_X.1.1).mp
              (by rw [E_X.1.2]; exact hE), E_X.1.2⟩,
            peJ.probOf_average E_X.1.1 _]
  rw [hLHS, hRHS]

/-- **[technical, cons-end induction]** The abstract marginal's marginal weight over the
`μ`-decorations of an abstract history equals the plain belief-map's path measure — i.e.
`abstractMarginal peJ` *de-resolves* to `mapBeliefExec Prod.snd _ peJ.average`. Resolved analogue of
the `mapBeliefExec_probOf` cons-end induction fused with `probOf_average`.

The unconditional content is `avgWeight_abstractMarginal_eq_mapWeight`
(`avgWeight = mapWeight Prod.snd`); turning `mapWeight` back into the belief-map path measure needs
`peJ` to start from the Dirac joint-initial distribution (`h_init`) — without it the two sides
disagree at the empty history, since `mapBeliefExec` is built with a Dirac init. Every call site
supplies `h_init` (`simJointExecR` has `PMF.pure (simProd …).init` by construction). -/
theorem avgWeight_abstractMarginal
    (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (h_init : peJ.initState = PMF.pure (simProd sys_C sys_A R).init)
    (E_A : AlterSeq State_A Label) (hE : E_A.trans.Terminates) :
    (abstractMarginal peJ).avgWeight E_A hE
      = (mapBeliefExec Prod.snd simProd_hstep_snd peJ.average).probOf E_A hE := by
  -- The unconditional content: `avgWeight` de-resolves to the fibre mass `mapWeight Prod.snd`.
  rw [avgWeight_abstractMarginal_eq_mapWeight peJ E_A hE]
  -- Turn `mapWeight` back into the belief-map path measure via `mapBeliefExec_probOf`, whose
  -- initial-mass hypotheses are `Prod.snd (simProd …).init = sys_A.init` (definitional, `rfl`) and
  -- `peJ.average.initState = PMF.pure (simProd …).init` (from `h_init`, since `average` keeps the
  -- initial distribution: `peJ.average.initState` is `peJ.initState` definitionally).
  exact (mapBeliefExec_probOf Prod.snd simProd_hstep_snd peJ.average rfl h_init E_A hE).symm

end FairStrongProbabilisticSimulation

end PLTS
