/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Simulation.StrongSoundness

/-!
# Lifting a `weakTau` through a strong probabilistic simulation

Stage 1 of the plan for `weakTau_lift_pure` (the last remaining crux of forward-simulation
transitivity): a *strong* (lockstep) probabilistic simulation transports an internal weak
transition out of a single concrete state to an internal weak transition out of a single related
abstract state, matching **end-state distributions** by a coupling.

  `StrongProbabilisticSimulation.weakTau_lift` :
    `R q_C x → weakTau sys_C (pure q_C) ν_C → ∃ Ν, weakTau sys_X (pure x) Ν ∧ PMFRel R ν_C Ν`

This is the `weakTau`/end-state analogue of trace-distribution soundness
(`StrongProbabilisticSimulation.achievableTraceDists_subset`). It factors, exactly like soundness,
into a **lift** to the coupled
product and a **project** onto the abstract factor:

* `StrongProbabilisticSimulation.weakTau_joint` — run the joint execution `simJointExec` (driven by
  the concrete `weakTau` witness) as a `weakTau` on `simProd sys_C sys_X R`. Reuses the soundness
  machinery (`simExecMarginal`, `simJointExec_probOf_R`); the arbitrary starting state is handled
  by the record-update `{sys with init := ·}` (all of `weakTau`/`simProd`/the scheduler machinery
  is `init`-agnostic in its step-based definitions).
* `weakTau_map` — push a `weakTau` forward through a *functional* label-preserving simulation `f`
  (here `f = Prod.snd`), the end-state analogue of `achievableTraceDists_map`.

The final glue below assembles the two; `weakTau_joint` reuses the soundness joint-execution
machinery at the `haltMass`/end-state level, and `weakTau_map` reuses the `mapBeliefSched`
fibre-posterior disintegration of `achievableTraceDists_map`, lifted to `haltMass`/`endState`.
-/

open Stream'

namespace PLTS

variable {State_C State_X Label : Type} [Silent Label]

/-! ### Fibre-posterior weak scheduler for `weakTau_map`

The witnessing `sysY`-scheduler for the functional pushforward of a `weakTau` is the
fibre-posterior disintegration of the `sysX`-scheduler — the same belief scheduler
`mapBeliefSched` used for `achievableTraceDists_map`, but assembled here as a genuine
`WeakScheduler` (its `internal_only` follows from `σX`'s, since the belief scheduler only ever
re-emits `σX`'s labels). We only need the τ-version of the step-lift hypothesis: the belief
scheduler emits `(l, ·)` solely where `σX` did, and `σX.internal_only` forces `l = τ`. -/

/-- The **fibre-posterior weak scheduler**. Same `next` as `mapBeliefSched`; assembled as a
`WeakScheduler` from the τ-only step-lift hypothesis using `σX.internal_only`. -/
noncomputable def mapWeakBeliefSched {X Y : Type} {sysX : System X Label} {sysY : System Y Label}
    (f : X → Y)
    (hstep : ∀ s μ, sysX.step s Silent.τ μ → sysY.step (f s) Silent.τ (μ.map f))
    (μ0 : PMF X) (σX : WeakScheduler sysX) : WeakScheduler sysY where
  next := fun E_Y => if hW0 : mapWeight f ⟨μ0, σX.toScheduler⟩ E_Y = 0 then PMF.pure none
      else PMF.normalize (mapBeliefNum f ⟨μ0, σX.toScheduler⟩ E_Y)
        (by rw [mapBeliefNum_tsum]; exact hW0)
        (by rw [mapBeliefNum_tsum]; exact mapWeight_ne_top f ⟨μ0, σX.toScheduler⟩ E_Y)
  valid := by
    classical
    intro E_Y n s hterm hstate l ν hsupp
    set pe_X : ProbabilisticExecution sysX := ⟨μ0, σX.toScheduler⟩ with hpeX
    by_cases hW0 : mapWeight f pe_X E_Y = 0
    · rw [dif_pos hW0, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
      exact absurd rfl hsupp
    · simp only [dif_neg hW0, PMF.mem_support_normalize_iff] at hsupp
      have hgne : mapBeliefNum f pe_X E_Y (some (l, ν)) ≠ 0 := hsupp
      rw [mapBeliefNum] at hgne
      have hex := mt ENNReal.tsum_eq_zero.mpr hgne
      push Not at hex
      obtain ⟨E_X, hEX⟩ := hex
      have hguard : E_X.trans.Terminates ∧ E_X.map f = E_Y := by
        by_contra hc
        rw [dif_neg hc, zero_mul] at hEX; exact hEX rfl
      have hmapne : ((pe_X.scheduler.next E_X).map (mapEmit f)) (some (l, ν)) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hEX; exact hEX rfl
      obtain ⟨μ, hμne, hνeq⟩ :
          ∃ μ : PMF X, pe_X.scheduler.next E_X (some (l, μ)) ≠ 0 ∧ ν = μ.map f := by
        rw [mapEmit, PMF.map_apply] at hmapne
        have hex2 := mt ENNReal.tsum_eq_zero.mpr hmapne
        push Not at hex2
        obtain ⟨o, ho⟩ := hex2
        by_cases hc : some (l, ν) = Option.map (fun lμ : Label × PMF X => (lμ.1, lμ.2.map f)) o
        · cases o with
          | none => simp at hc
          | some lμ =>
            obtain ⟨l', μ⟩ := lμ
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
            obtain ⟨rfl, rfl⟩ := hc
            exact ⟨μ, fun h0 => by rw [h0] at ho; simp at ho, rfl⟩
        · rw [if_neg hc] at ho; exact absurd rfl ho
      have hlτ : l = Silent.τ := σX.internal_only E_X l μ ((PMF.mem_support_iff _ _).mpr hμne)
      subst hlτ
      have hstateX : (E_X.stateAt n).map f = some s := by
        rw [← AlterSeq.mapFib_stateAt f E_X n, hguard.2, hstate]
      obtain ⟨x, hxn, hfx⟩ : ∃ x : X, E_X.stateAt n = some x ∧ f x = s := by
        cases hc : E_X.stateAt n with
        | none => rw [hc] at hstateX; simp at hstateX
        | some x => rw [hc] at hstateX; exact ⟨x, rfl, by simpa using hstateX⟩
      have htermX : E_X.trans.TerminatedAt n :=
        (AlterSeq.mapFib_terminatedAt f E_X n).mp (hguard.2 ▸ hterm)
      have hstepX : sysX.step x Silent.τ μ :=
        pe_X.scheduler.valid E_X n x htermX hxn Silent.τ μ ((PMF.mem_support_iff _ _).mpr hμne)
      have hres := hstep x μ hstepX
      rw [hfx, ← hνeq] at hres
      exact hres
  internal_only := by
    classical
    intro E_Y l ν hsupp
    set pe_X : ProbabilisticExecution sysX := ⟨μ0, σX.toScheduler⟩ with hpeX
    by_cases hW0 : mapWeight f pe_X E_Y = 0
    · rw [dif_pos hW0, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
      exact absurd rfl hsupp
    · simp only [dif_neg hW0, PMF.mem_support_normalize_iff] at hsupp
      have hgne : mapBeliefNum f pe_X E_Y (some (l, ν)) ≠ 0 := hsupp
      rw [mapBeliefNum] at hgne
      have hex := mt ENNReal.tsum_eq_zero.mpr hgne
      push Not at hex
      obtain ⟨E_X, hEX⟩ := hex
      have hmapne : ((pe_X.scheduler.next E_X).map (mapEmit f)) (some (l, ν)) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hEX; exact hEX rfl
      rw [mapEmit, PMF.map_apply] at hmapne
      have hex2 := mt ENNReal.tsum_eq_zero.mpr hmapne
      push Not at hex2
      obtain ⟨o, ho⟩ := hex2
      by_cases hc : some (l, ν) = Option.map (fun lμ : Label × PMF X => (lμ.1, lμ.2.map f)) o
      · cases o with
        | none => simp at hc
        | some lμ =>
          obtain ⟨l', μ⟩ := lμ
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          have hne : σX.toScheduler.next E_X (some (l, μ)) ≠ 0 := by
            intro h0; rw [h0] at ho; simp at ho
          exact σX.internal_only E_X l μ ((PMF.mem_support_iff _ _).mpr hne)
      · rw [if_neg hc] at ho; exact absurd rfl ho

/-- **Cancellation:** `mapWeight · belief-scheduler-emission = mapBeliefNum` for the weak
belief scheduler (the `mapWeight_mul_next` analogue, phrased over `mapWeakBeliefSched`). -/
theorem mapWeakBeliefSched_cancel {X Y : Type} {sysX : System X Label} {sysY : System Y Label}
    (f : X → Y)
    (hstep : ∀ s μ, sysX.step s Silent.τ μ → sysY.step (f s) Silent.τ (μ.map f))
    (μ0 : PMF X) (σX : WeakScheduler sysX) (E_Y : AlterSeq Y Label)
    (o : Option (Label × PMF Y)) :
    mapWeight f ⟨μ0, σX.toScheduler⟩ E_Y * (mapWeakBeliefSched f hstep μ0 σX).next E_Y o
      = mapBeliefNum f ⟨μ0, σX.toScheduler⟩ E_Y o := by
  classical
  set pe_X : ProbabilisticExecution sysX := ⟨μ0, σX.toScheduler⟩ with hpeX
  by_cases hW0 : mapWeight f pe_X E_Y = 0
  · have hnext : (mapWeakBeliefSched f hstep μ0 σX).next E_Y = PMF.pure none := by
      exact dif_pos hW0
    rw [hnext, hW0, zero_mul]
    have hall : ∀ o', mapBeliefNum f pe_X E_Y o' = 0 := by
      rw [← ENNReal.tsum_eq_zero, mapBeliefNum_tsum]; exact hW0
    exact (hall o).symm
  · have hnext : (mapWeakBeliefSched f hstep μ0 σX).next E_Y o
        = mapBeliefNum f pe_X E_Y o * (mapWeight f pe_X E_Y)⁻¹ := by
      have h1 : (mapWeakBeliefSched f hstep μ0 σX).next E_Y
          = PMF.normalize (mapBeliefNum f pe_X E_Y) (by rw [mapBeliefNum_tsum]; exact hW0)
            (by rw [mapBeliefNum_tsum]; exact mapWeight_ne_top f pe_X E_Y) := by
        exact dif_neg hW0
      rw [h1, PMF.normalize_apply, mapBeliefNum_tsum]
    rw [hnext, ← mul_assoc, mul_comm (mapWeight f pe_X E_Y) (mapBeliefNum f pe_X E_Y o),
      mul_assoc, ENNReal.mul_inv_cancel hW0 (mapWeight_ne_top f pe_X E_Y), mul_one]

open Classical in
/-- **General-source path measure.** The `mapWeakBeliefSched`-probability of a terminating
`Y`-history collapses to the total `f`-fibre mass `mapWeight`, for an arbitrary source `μ0`
(the source-`μ0.map f`/Dirac-`μ0` split is handled in the `nil` base case via
`AlterSeq.map_apply_fibre`). The `weakTau`/`haltMass`-source analogue of `mapBeliefExec_probOf`. -/
theorem mapWeakBeliefSched_probOf {X Y : Type} {sysX : System X Label} {sysY : System Y Label}
    (f : X → Y)
    (hstep : ∀ s μ, sysX.step s Silent.τ μ → sysY.step (f s) Silent.τ (μ.map f))
    (μ0 : PMF X) (σX : WeakScheduler sysX)
    (E_Y : AlterSeq Y Label) (hFin : E_Y.trans.Terminates) :
    (⟨μ0.map f, (mapWeakBeliefSched f hstep μ0 σX).toScheduler⟩
        : ProbabilisticExecution sysY).probOf E_Y hFin
      = mapWeight f ⟨μ0, σX.toScheduler⟩ E_Y := by
  classical
  set pe_X : ProbabilisticExecution sysX := ⟨μ0, σX.toScheduler⟩ with hpeX
  set gnum : AlterSeq Y Label → AlterSeq X Label → ENNReal := fun E_Y E_X =>
    dite (E_X.trans.Terminates ∧ E_X.map f = E_Y) (fun h => pe_X.probOf E_X h.1) (fun _ => 0)
    with hgnum
  set g : AlterSeq Y Label → Option (Label × PMF Y) → ENNReal := fun E_Y o =>
    ∑' E_X : AlterSeq X Label, gnum E_Y E_X * ((pe_X.scheduler.next E_X).map (mapEmit f)) o with hg
  set W : AlterSeq Y Label → ENNReal := fun E_Y => ∑' E_X : AlterSeq X Label, gnum E_Y E_X with hW
  set σ_Y : Scheduler sysY := (mapWeakBeliefSched f hstep μ0 σX).toScheduler with hσ
  set pe_Y : ProbabilisticExecution sysY := ⟨μ0.map f, σ_Y⟩ with hpe_Y
  have hcancel : ∀ E_Y o, W E_Y * σ_Y.next E_Y o = g E_Y o :=
    fun E_Y o => mapWeakBeliefSched_cancel f hstep μ0 σX E_Y o
  change pe_Y.probOf E_Y hFin = W E_Y
  suffices hgen : ∀ (LY : List (Label × Y)) (y₀ : Y)
      (hFin : (Seq.ofList LY : Seq (Label × Y)).Terminates),
      pe_Y.probOf ⟨y₀, Seq.ofList LY⟩ hFin = W ⟨y₀, Seq.ofList LY⟩ by
    have hofl : (Seq.ofList (E_Y.trans.toList hFin) : Seq (Label × Y)) = E_Y.trans :=
      Stream'.Seq.ofList_toList E_Y.trans hFin
    have hFin' : (Seq.ofList (E_Y.trans.toList hFin) : Seq (Label × Y)).Terminates := by
      rw [hofl]; exact hFin
    have hEeq : (⟨E_Y.init, Seq.ofList (E_Y.trans.toList hFin)⟩ : AlterSeq Y Label) = E_Y := by
      cases E_Y; simp only [hofl]
    have hkey := hgen (E_Y.trans.toList hFin) E_Y.init hFin'
    rw [pe_Y.probOf_congr ⟨E_Y.init, Seq.ofList (E_Y.trans.toList hFin)⟩ E_Y hEeq hFin' hFin]
      at hkey
    rw [hkey, hEeq]
  intro LY
  induction LY using List.reverseRecOn with
  | nil =>
    intro y₀ hFin
    rw [pe_Y.probOf_congr ⟨y₀, Seq.ofList ([] : List (Label × Y))⟩ ⟨y₀, Seq.nil⟩
      (by rw [Stream'.Seq.ofList_nil]) hFin Stream'.Seq.terminates_nil,
      ProbabilisticExecution.probOf_nil]
    change (μ0.map f) y₀
      = ∑' E_X : AlterSeq X Label, gnum ⟨y₀, Seq.ofList ([] : List (Label × Y))⟩ E_X
    rw [tsum_congr (fun E_X => by rw [hgnum]), Stream'.Seq.ofList_nil]
    rw [← Function.Injective.tsum_eq (g := fun x : {x : X // f x = y₀} =>
        (⟨x.1, Seq.nil⟩ : AlterSeq X Label))
        (fun a b hab => by
          have := congr_arg (·.init) hab; simp only at this; exact Subtype.ext this)
        (f := fun E_X : AlterSeq X Label =>
          dite (E_X.trans.Terminates ∧ E_X.map f = (⟨y₀, Seq.nil⟩ : AlterSeq Y Label))
            (fun h => pe_X.probOf E_X h.1) (fun _ => 0)) ?suppNil]
    · rw [AlterSeq.map_apply_fibre f μ0 y₀]
      refine tsum_congr (fun x => ?_)
      rw [dif_pos ⟨Stream'.Seq.terminates_nil, by
        change (⟨f x.1, Stream'.Seq.map _ Seq.nil⟩ : AlterSeq Y Label) = ⟨y₀, Seq.nil⟩
        rw [Stream'.Seq.map_nil, x.2]⟩,
        ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState, hpeX]
    case suppNil =>
      intro E_X hE
      rw [Function.mem_support] at hE
      have hc : E_X.trans.Terminates ∧ E_X.map f = (⟨y₀, Seq.nil⟩ : AlterSeq Y Label) := by
        by_contra hcon; exact hE (dif_neg hcon)
      obtain ⟨hT, hmap⟩ := hc
      have hinit : f E_X.init = y₀ := congr_arg (·.init) hmap
      have htrans : E_X.trans.map (fun lq => (lq.1, f lq.2)) = Seq.nil :=
        congr_arg (·.trans) hmap
      have hEtrans : E_X.trans = Seq.nil := by
        have hlen := congr_arg Stream'.Seq.length' htrans
        rw [Stream'.Seq.length'_map, Stream'.Seq.length'_nil] at hlen
        exact (Stream'.Seq.length'_eq_zero_iff_nil E_X.trans).mp hlen
      refine ⟨⟨E_X.init, hinit⟩, ?_⟩
      obtain ⟨ei, et⟩ := E_X; simp only at hEtrans ⊢; rw [hEtrans]
  | append_singleton rest last ih =>
    intro y₀ hFin
    obtain ⟨l, y'⟩ := last
    have hsplit : (Seq.ofList (rest ++ [(l, y')]) : Seq (Label × Y))
        = (Seq.ofList rest).append (Seq.cons (l, y') Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have hrest_fin : (Seq.ofList rest : Seq (Label × Y)).Terminates :=
      Stream'.Seq.terminates_ofList _
    have hFinS : ((Seq.ofList rest).append (Seq.cons (l, y') Seq.nil)).Terminates := by
      rw [← hsplit]; exact hFin
    set E_Y' : AlterSeq Y Label := ⟨y₀, Seq.ofList rest⟩ with hE_Y'
    set Mid : ENNReal := ∑' E_X' : AlterSeq X Label,
      gnum E_Y' E_X' * ∑' x' : {x : X // f x = y'}, pe_X.kernel E_X' (l, x'.1) with hMid
    have hLHS : pe_Y.probOf ⟨y₀, Seq.ofList (rest ++ [(l, y')])⟩ hFin = Mid := by
      rw [pe_Y.probOf_congr ⟨y₀, Seq.ofList (rest ++ [(l, y')])⟩
          ⟨y₀, (Seq.ofList rest).append (Seq.cons (l, y') Seq.nil)⟩ (by rw [hsplit]) hFin hFinS,
        pe_Y.probOf_append_singleton y₀ (Seq.ofList rest) hrest_fin (l, y') hFinS,
        show pe_Y.probOf E_Y' hrest_fin = W E_Y' from ih y₀ hrest_fin]
      rw [ProbabilisticExecution.kernel]
      change W E_Y' * (∑' ν, σ_Y.next E_Y' (some (l, ν)) * ν y') = Mid
      rw [← ENNReal.tsum_mul_left]
      rw [tsum_congr (fun ν => by rw [← mul_assoc, hcancel E_Y' (some (l, ν))])]
      rw [tsum_congr (fun ν => by rw [hg]), hMid]
      rw [tsum_congr (fun ν => ENNReal.tsum_mul_right.symm), ENNReal.tsum_comm]
      refine tsum_congr (fun E_X' => ?_)
      rw [tsum_congr (fun ν => mul_assoc _ _ _), ENNReal.tsum_mul_left,
        mappedKernel_eq pe_X f E_X' l y']
    have hRHS : W ⟨y₀, Seq.ofList (rest ++ [(l, y')])⟩ = Mid := by
      rw [hW]
      change (∑' E_X, gnum ⟨y₀, Seq.ofList (rest ++ [(l, y')])⟩ E_X) = Mid
      rw [tsum_congr (fun E_X => by rw [hgnum]), hsplit]
      rw [fibre_append_reindex pe_X f y₀ rest l y', ENNReal.tsum_prod']
      rw [hMid]
      refine tsum_congr (fun E_X' => ?_)
      simp only
      by_cases hc : E_X'.trans.Terminates ∧ E_X'.map f = ⟨y₀, Seq.ofList rest⟩
      · rw [tsum_congr (fun x' => dif_pos hc)]
        rw [tsum_congr (fun x' : {x : X // f x = y'} =>
            ProbabilisticExecution.probOf_append_singleton pe_X E_X'.init
              E_X'.trans hc.1 (l, x'.1) _), ENNReal.tsum_mul_left]
        rw [show gnum E_Y' E_X' = pe_X.probOf E_X' hc.1 from by rw [hgnum]; exact dif_pos hc]
      · rw [tsum_congr (fun x' => dif_neg hc), tsum_zero]
        rw [show gnum E_Y' E_X' = 0 from by rw [hgnum]; exact dif_neg hc, zero_mul]
    rw [hLHS, hRHS]

open Classical in
/-- The halting mass of `mapWeakBeliefSched` at the `⊥`-emission, as a sum over the `f`-fibre of
terminating `X`-histories of the `σX`-halting mass. -/
theorem mapWeakBeliefSched_haltMass_fibre {X Y : Type} {sysX : System X Label}
    {sysY : System Y Label} (f : X → Y)
    (hstep : ∀ s μ, sysX.step s Silent.τ μ → sysY.step (f s) Silent.τ (μ.map f))
    (μ0 : PMF X) (σX : WeakScheduler sysX)
    (E_Y : {e : AlterSeq Y Label // e.trans.Terminates}) :
    (mapWeakBeliefSched f hstep μ0 σX).haltMass (μ0.map f) E_Y
      = ∑' E_X : {e : AlterSeq X Label // e.trans.Terminates ∧ e.map f = E_Y.1},
          σX.haltMass μ0 ⟨E_X.1, E_X.2.1⟩ := by
  classical
  set pe_X : ProbabilisticExecution sysX := ⟨μ0, σX.toScheduler⟩ with hpeX
  -- Step 1: haltMass = mapWeight * next ⊥ = mapBeliefNum ⊥ (cancellation).
  have hnum : (mapWeakBeliefSched f hstep μ0 σX).haltMass (μ0.map f) E_Y
      = mapBeliefNum f pe_X E_Y.1 none := by
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [mapWeakBeliefSched_probOf f hstep μ0 σX E_Y.1 E_Y.2]
    exact mapWeakBeliefSched_cancel f hstep μ0 σX E_Y.1 none
  rw [hnum, mapBeliefNum]
  -- Step 2: ((next E_X).map (mapEmit f)) ⊥ = next E_X ⊥.
  have hnone : ∀ E_X : AlterSeq X Label,
      ((pe_X.scheduler.next E_X).map (mapEmit f)) none = pe_X.scheduler.next E_X none := by
    intro E_X
    rw [PMF.map_apply]
    rw [tsum_eq_single none (fun o ho => by
      rw [mapEmit]; cases o with
      | none => exact absurd rfl ho
      | some lμ => rw [if_neg (by simp)])]
    rw [mapEmit]; simp
  simp only [hnone]
  -- Step 3: reindex the guarded `AlterSeq X`-sum onto the fibre subtype.
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun E_X =>
      (E_X : {e : AlterSeq X Label // e.trans.Terminates ∧ e.map f = E_Y.1}).1) ?_ ?_ ?_
  · rintro ⟨⟨a, ha⟩, _⟩ ⟨⟨b, hb⟩, _⟩ hab
    simp only at hab
    exact Subtype.ext (Subtype.ext hab)
  · intro E_X hE
    rw [Function.mem_support] at hE
    have hguard : E_X.trans.Terminates ∧ E_X.map f = E_Y.1 := by
      by_contra hc; rw [dif_neg hc, zero_mul] at hE; exact hE rfl
    have hhm : σX.haltMass μ0 ⟨E_X, hguard.1⟩ ≠ 0 := by
      unfold WeakScheduler.haltMass Scheduler.haltMass
      intro h0; apply hE; rw [dif_pos hguard]; exact h0
    exact ⟨⟨⟨E_X, hguard⟩, hhm⟩, rfl⟩
  · rintro ⟨⟨E_X, hguard⟩, hhm⟩
    simp only
    rw [dif_pos hguard]
    change pe_X.probOf E_X hguard.1 * pe_X.scheduler.next E_X none = _
    rw [hpeX]; rfl

open Classical in
/-- **`g`-integration identity for the pushforward.** Integrating a test `gg` over the halting
end-state of `mapWeakBeliefSched` (from `μ0.map f`) equals integrating `gg ∘ f` over the halting
end-state of `σX` (from `μ0`): the fibre regrouping `ENNReal.tsum_fiberwise`, with `gg` constant on
each `f`-fibre by `AlterSeq.map_endState`. Taking `gg = 1` gives a.s.-halting; `gg = [· = t]` gives
the end-state pushforward. -/
theorem mapWeakBeliefSched_integrate {X Y : Type} {sysX : System X Label} {sysY : System Y Label}
    (f : X → Y)
    (hstep : ∀ s μ, sysX.step s Silent.τ μ → sysY.step (f s) Silent.τ (μ.map f))
    (μ0 : PMF X) (σX : WeakScheduler sysX) (gg : Y → ENNReal) :
    (∑' E_Y : {e : AlterSeq Y Label // e.trans.Terminates},
        (mapWeakBeliefSched f hstep μ0 σX).haltMass (μ0.map f) E_Y
          * gg (E_Y.1.endState E_Y.2))
      = ∑' E_X : {e : AlterSeq X Label // e.trans.Terminates},
          σX.haltMass μ0 E_X * gg (f (E_X.1.endState E_X.2)) := by
  classical
  set gmap : {e : AlterSeq X Label // e.trans.Terminates}
      → {e : AlterSeq Y Label // e.trans.Terminates} :=
    fun E_X => ⟨E_X.1.map f, (AlterSeq.map_trans_terminates_iff f E_X.1).mpr E_X.2⟩ with hgmap
  rw [← ENNReal.tsum_fiberwise
      (f := fun E_X : {e : AlterSeq X Label // e.trans.Terminates} =>
        σX.haltMass μ0 E_X * gg (f (E_X.1.endState E_X.2))) gmap]
  refine tsum_congr (fun E_Y => ?_)
  rw [mapWeakBeliefSched_haltMass_fibre f hstep μ0 σX E_Y, ← ENNReal.tsum_mul_right]
  -- for `E_X` in the fibre, `f (endState E_X) = endState E_Y.1`.
  have hconst : ∀ (E_X : AlterSeq X Label) (hT : E_X.trans.Terminates), E_X.map f = E_Y.1 →
      gg (f (E_X.endState hT)) = gg (E_Y.1.endState E_Y.2) := by
    intro E_X hT hm
    congr 1
    rw [← AlterSeq.map_endState f E_X hT]
    exact AlterSeq.endState_congr_pub hm _ _
  refine (tsum_eq_tsum_of_ne_zero_bij
    (i := fun E_X =>
      (⟨⟨(E_X : {e : AlterSeq X Label // e.trans.Terminates ∧ e.map f = E_Y.1}).1,
        (E_X : {e : AlterSeq X Label // e.trans.Terminates ∧ e.map f = E_Y.1}).2.1⟩,
        by
          simp only [Set.mem_preimage, Set.mem_singleton_iff, hgmap]
          exact Subtype.ext
            (E_X : {e : AlterSeq X Label // e.trans.Terminates ∧ e.map f = E_Y.1}).2.2⟩
        : ↑(gmap ⁻¹' {E_Y}))) ?_ ?_ ?_).symm
  · rintro ⟨⟨a, ha⟩, _⟩ ⟨⟨b, hb⟩, _⟩ hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext (Subtype.ext hab)
  · intro b hb
    rcases b with ⟨⟨E_X, hT⟩, hmem⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hgmap] at hmem
    have hmapeq : E_X.map f = E_Y.1 := congr_arg Subtype.val hmem
    refine ⟨⟨⟨E_X, ⟨hT, hmapeq⟩⟩, ?_⟩, ?_⟩
    · simp only [Function.mem_support] at hb ⊢
      rw [hconst E_X hT hmapeq] at hb
      exact hb
    · rfl
  · rintro ⟨⟨E_X, ⟨hT, hmapeq⟩⟩, hne⟩
    simp only
    rw [hconst E_X hT hmapeq]


/-- **Functional pushforward of `weakTau`.** A label-preserving functional simulation `f : X → Y`
(each internal `sysX`-step maps to an internal `sysY`-step of the `f`-image) pushes an internal
weak transition forward: `weakTau sys_X μ ν → weakTau sys_Y (μ.map f) (ν.map f)`.

The end-state analogue of `achievableTraceDists_map`; for non-injective `f` (such as `Prod.snd`)
the witnessing `sys_Y`-scheduler is the fibre-posterior disintegration of the `sys_X`-scheduler
(`mapWeakBeliefSched`), whose `haltMass`/`endState` fidelity is established below. -/
theorem weakTau_map {X Y : Type} {sysX : System X Label} {sysY : System Y Label} (f : X → Y)
    (hstep : ∀ s μ, sysX.step s Silent.τ μ → sysY.step (f s) Silent.τ (μ.map f))
    {μ ν : PMF X} (h : weakTau sysX μ ν) :
    weakTau sysY (μ.map f) (ν.map f) := by
  classical
  refine ⟨mapWeakBeliefSched f hstep μ h.witnessScheduler, ?_, ?_⟩
  · -- a.s.-halting: integrate the constant `1`.
    have hone := mapWeakBeliefSched_integrate f hstep μ h.witnessScheduler (fun _ => 1)
    simp only [mul_one] at hone
    rw [hone]
    have := h.witness_halts
    simpa only [mul_one] using this
  · -- end-state pushforward: integrate the indicator `[· = t]`.
    intro t
    have hind := mapWeakBeliefSched_integrate f hstep μ h.witnessScheduler
      (fun s => if s = t then (1 : ENNReal) else 0)
    rw [hind]
    -- the RHS is `∑' E_X, σX.haltMass μ E_X * [f (endState E_X) = t]`,
    -- which by `weakTau.integrate` equals `∑' s, ν s * [f s = t] = (ν.map f) t`.
    rw [h.integrate (fun s => if f s = t then (1 : ENNReal) else 0)]
    rw [PMF.map_apply]
    refine tsum_congr (fun s => ?_)
    by_cases hc : f s = t
    · rw [if_pos hc, if_pos hc.symm, mul_one]
    · rw [if_neg hc, if_neg (fun heq => hc heq.symm), mul_zero]

variable {sys_C : System State_C Label} {sys_X : System State_X Label}
  {R : State_C → State_X → Prop}

private theorem weakTau_step_congr {State : Type} {sys sys' : System State Label}
    (hstep : sys.step = sys'.step) {μ_init μ : PMF State} (h : weakTau sys μ_init μ) :
    weakTau sys' μ_init μ := by
  obtain ⟨σ, hhalt, hpush⟩ := h
  let σ' : Scheduler sys' :=
    { next := σ.next
      valid := by intro e n s ht hs l ν hsupp; rw [← hstep]; exact σ.valid e n s ht hs l ν hsupp }
  let τ' : WeakScheduler sys' := { toScheduler := σ', internal_only := σ.internal_only }
  have hhm : ∀ e, τ'.haltMass μ_init e = σ.haltMass μ_init e := fun _ => rfl
  exact ⟨τ', by simp only [hhm]; exact hhalt, fun s => by simp only [hhm]; exact hpush s⟩


open Classical in
private theorem simJointExec_halt_factor (pe_C : ProbabilisticExecution sys_C)
    (sim : StrongProbabilisticSimulation sys_C sys_X R)
    (E : AlterSeq (State_C × State_X) Label) (hT : E.trans.Terminates)
    (hprob : (simJointExec pe_C sim).probOf E hT ≠ 0) :
    (simJointExec pe_C sim).probOf E hT * (simJointSched pe_C sim).next E none
      = (simJointExec pe_C sim).probOf E hT * pe_C.scheduler.next (E.map Prod.fst) none := by
  classical
  congr 1
  have hR : R (simLastState E).1 (simLastState E).2 := by
    have := simJointExec_probOf_R pe_C sim E hT hprob
    rwa [simLastState, dif_pos hT]
  have hC_term : (E.map Prod.fst).trans.Terminates := (AlterSeq.map_trans_terminates_iff _ _).mpr hT
  have hlast1 : (simLastState E).1 = (E.map Prod.fst).endState hC_term := by
    rw [simLastState, dif_pos hT, AlterSeq.map_endState Prod.fst E hT]
  have hvalid : ∀ (l : Label) (μ_C : PMF State_C),
      pe_C.scheduler.next (E.map Prod.fst) (some (l, μ_C)) ≠ 0 →
      sys_C.step (simLastState E).1 l μ_C := by
    intro l μ_C hne
    rw [hlast1]
    exact pe_C.scheduler.valid (E.map Prod.fst) (Nat.find hC_term)
      ((E.map Prod.fst).endState hC_term) (Nat.find_spec hC_term)
      (AlterSeq.stateAt_find_eq_endState _ hC_term) l μ_C ((PMF.mem_support_iff _ _).mpr hne)
  change ((pe_C.scheduler.next (E.map Prod.fst)).bind _) none = _
  rw [PMF.bind_apply, ENNReal.tsum_option']
  rw [show (fun o : Label × PMF State_C =>
      (pe_C.scheduler.next (E.map Prod.fst)) (some o) *
        ((match some o with
          | none => PMF.pure none
          | some (l, μ_C) =>
            if _ : R (simLastState E).1 (simLastState E).2 ∧
                sys_C.step (simLastState E).1 l μ_C then
              PMF.pure (some (l, simCouple sim (simLastState E) l μ_C))
            else PMF.pure none) :
              PMF (Option (Label × PMF (State_C × State_X)))) none) = fun _ => 0 from by
    funext o
    obtain ⟨l, μ_C⟩ := o
    simp only
    by_cases hg : R (simLastState E).1 (simLastState E).2 ∧ sys_C.step (simLastState E).1 l μ_C
    · rw [dif_pos hg, PMF.pure_apply_of_ne _ _ (by simp), mul_zero]
    · have hz : pe_C.scheduler.next (E.map Prod.fst) (some (l, μ_C)) = 0 := by
        by_contra hne; exact hg ⟨hR, hvalid l μ_C hne⟩
      rw [hz, zero_mul]]
  rw [tsum_zero, add_zero]
  change _ * (PMF.pure none : PMF (Option (Label × PMF (State_C × State_X)))) none = _
  rw [PMF.pure_apply_self, mul_one]

open Classical in
private theorem simExecMarginal_weighted (pe_C : ProbabilisticExecution sys_C)
    (sim : StrongProbabilisticSimulation sys_C sys_X R)
    (h_init : pe_C.initState = PMF.pure sys_C.init)
    (K : AlterSeq State_C Label → ENNReal) :
    (∑' E : AlterSeq (State_C × State_X) Label,
        dite E.trans.Terminates
          (fun h => (simJointExec pe_C sim).probOf E h * K (E.map Prod.fst)) (fun _ => 0))
      = ∑' e_C : AlterSeq State_C Label,
          dite e_C.trans.Terminates (fun h => pe_C.probOf e_C h * K e_C) (fun _ => 0) := by
  classical
  rw [← ENNReal.tsum_fiberwise
    (f := fun E : AlterSeq (State_C × State_X) Label =>
      dite E.trans.Terminates
        (fun h => (simJointExec pe_C sim).probOf E h * K (E.map Prod.fst)) (fun _ => 0))
    (g := fun E : AlterSeq (State_C × State_X) Label => E.map Prod.fst)]
  refine tsum_congr (fun e_C => ?_)
  by_cases hcond : e_C.trans.Terminates
  · rw [dif_pos hcond]
    rw [show (∑' (b : ↑((fun E : AlterSeq (State_C × State_X) Label => E.map Prod.fst) ⁻¹' {e_C})),
          dite (b : AlterSeq (State_C × State_X) Label).trans.Terminates
            (fun h => (simJointExec pe_C sim).probOf (b : AlterSeq (State_C × State_X) Label) h
              * K ((b : AlterSeq (State_C × State_X) Label).map Prod.fst)) (fun _ => 0))
        = ∑' (b : ↑((fun E : AlterSeq (State_C × State_X) Label => E.map Prod.fst) ⁻¹' {e_C})),
          dite (b : AlterSeq (State_C × State_X) Label).trans.Terminates
            (fun h => (simJointExec pe_C sim).probOf (b : AlterSeq (State_C × State_X) Label) h)
            (fun _ => 0) * K e_C from by
      refine tsum_congr (fun b => ?_)
      have hb : (b : AlterSeq (State_C × State_X) Label).map Prod.fst = e_C := b.2
      by_cases hT : (b : AlterSeq (State_C × State_X) Label).trans.Terminates
      · rw [dif_pos hT, dif_pos hT, hb]
      · rw [dif_neg hT, dif_neg hT, zero_mul]]
    rw [ENNReal.tsum_mul_right]
    congr 1
    rw [show (∑' (b : ↑((fun E : AlterSeq (State_C × State_X) Label => E.map Prod.fst) ⁻¹' {e_C})),
          dite (b : AlterSeq (State_C × State_X) Label).trans.Terminates
            (fun h => (simJointExec pe_C sim).probOf (b : AlterSeq (State_C × State_X) Label) h)
            (fun _ => 0))
        = ∑' E : AlterSeq (State_C × State_X) Label,
            dite (E.trans.Terminates ∧ E.map Prod.fst = e_C)
              (fun h => (simJointExec pe_C sim).probOf E h.1) (fun _ => 0) from by
      rw [← tsum_subtype_eq_of_support_subset
        (s := {E : AlterSeq (State_C × State_X) Label | E.map Prod.fst = e_C})
        (f := fun E => dite (E.trans.Terminates ∧ E.map Prod.fst = e_C)
          (fun h => (simJointExec pe_C sim).probOf E h.1) (fun _ => 0)) ?_]
      · refine tsum_congr (fun b => ?_)
        have hb : (b : AlterSeq (State_C × State_X) Label).map Prod.fst = e_C := b.2
        by_cases hT : (b : AlterSeq (State_C × State_X) Label).trans.Terminates
        · rw [dif_pos hT, dif_pos ⟨hT, hb⟩]
        · rw [dif_neg hT, dif_neg (fun h => hT h.1)]
      · intro E hE
        rw [Function.mem_support] at hE
        by_contra hc
        exact hE (dif_neg (fun h => hc h.2))]
    have heq :
        (⟨e_C.init, Seq.ofList (e_C.trans.toList hcond)⟩ : AlterSeq State_C Label) = e_C := by
      cases e_C; simp only [Stream'.Seq.ofList_toList]
    have hmarg := simExecMarginal pe_C sim h_init (e_C.trans.toList hcond) e_C.init
    rw [ProbabilisticExecution.probOf_congr pe_C ⟨e_C.init, Seq.ofList (e_C.trans.toList hcond)⟩
      e_C heq (Stream'.Seq.terminates_ofList _) hcond] at hmarg
    rw [← hmarg]
    refine tsum_congr (fun E => ?_)
    by_cases hc2 : E.trans.Terminates ∧ E.map Prod.fst = e_C
    · rw [dif_pos hc2, dif_pos ⟨hc2.1, by rw [hc2.2]; exact heq.symm⟩]
    · rw [dif_neg hc2, dif_neg (fun h => hc2 ⟨h.1, by rw [h.2]; exact heq⟩)]
  · rw [dif_neg hcond]
    refine ENNReal.tsum_eq_zero.mpr (fun b => ?_)
    have hb : (b : AlterSeq (State_C × State_X) Label).map Prod.fst = e_C := b.2
    by_cases hT : (b : AlterSeq (State_C × State_X) Label).trans.Terminates
    · exfalso; apply hcond
      rw [← hb]; exact (AlterSeq.map_trans_terminates_iff _ _).mpr hT
    · rw [dif_neg hT]

omit [Silent Label] in
open Classical in
private theorem bundled_halt_to_dite {State : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys) (σ : Scheduler sys) (μ : PMF State)
    (g : State → ENNReal)
    (hpe : (⟨μ, σ⟩ : ProbabilisticExecution sys) = pe) :
    (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        σ.haltMass μ e * g (e.1.endState e.2))
      = ∑' E : AlterSeq State Label,
          dite E.trans.Terminates
            (fun h => pe.probOf E h * (σ.next E none *
              dite E.trans.Terminates (fun h' => g (E.endState h')) (fun _ => 0)))
            (fun _ => 0) := by
  classical
  rw [← tsum_subtype_eq_of_support_subset (s := {E : AlterSeq State Label | E.trans.Terminates})
    (f := fun E => dite E.trans.Terminates
      (fun h => pe.probOf E h * (σ.next E none *
        dite E.trans.Terminates (fun h' => g (E.endState h')) (fun _ => 0))) (fun _ => 0)) ?_]
  · refine tsum_congr (fun e => ?_)
    rw [dif_pos e.2]; unfold Scheduler.haltMass; rw [hpe, dif_pos e.2]; ring
  · intro E hE
    rw [Function.mem_support] at hE
    by_contra hc; exact hE (dif_neg hc)

open Classical in
private theorem halt_integrate (pe_C : ProbabilisticExecution sys_C)
    (sim : StrongProbabilisticSimulation sys_C sys_X R)
    (h_init : pe_C.initState = PMF.pure sys_C.init) (g : State_C → ENNReal) :
    (∑' e : {e : AlterSeq (State_C × State_X) Label // e.trans.Terminates},
        (simJointSched pe_C sim).haltMass (PMF.pure (simProd sys_C sys_X R).init) e
          * g ((e.1.endState e.2).1))
      = ∑' e_C : {e : AlterSeq State_C Label // e.trans.Terminates},
        pe_C.scheduler.haltMass pe_C.initState e_C * g (e_C.1.endState e_C.2) := by
  classical
  set K : AlterSeq State_C Label → ENNReal :=
    fun e_C => pe_C.scheduler.next e_C none *
      dite e_C.trans.Terminates (fun h => g (e_C.endState h)) (fun _ => 0) with hK
  rw [bundled_halt_to_dite (simJointExec pe_C sim) (simJointSched pe_C sim)
    (PMF.pure (simProd sys_C sys_X R).init) (fun p => g p.1) rfl]
  rw [show (∑' E : AlterSeq (State_C × State_X) Label,
        dite E.trans.Terminates
          (fun h => (simJointExec pe_C sim).probOf E h * ((simJointSched pe_C sim).next E none *
            dite E.trans.Terminates (fun h' => (fun p => g p.1) (E.endState h')) (fun _ => 0)))
          (fun _ => 0))
      = ∑' E : AlterSeq (State_C × State_X) Label,
          dite E.trans.Terminates
            (fun h => (simJointExec pe_C sim).probOf E h * K (E.map Prod.fst)) (fun _ => 0) from by
    classical
    refine tsum_congr (fun E => ?_)
    by_cases hT : E.trans.Terminates
    · simp only [dif_pos hT]
      by_cases hp : (simJointExec pe_C sim).probOf E hT = 0
      · rw [hp, zero_mul, zero_mul]
      · rw [← mul_assoc, simJointExec_halt_factor pe_C sim E hT hp, mul_assoc]
        congr 1
        simp only [hK]
        have hCT : (E.map Prod.fst).trans.Terminates :=
          (AlterSeq.map_trans_terminates_iff _ _).mpr hT
        rw [dif_pos hCT, AlterSeq.map_endState Prod.fst E hT]
    · simp only [dif_neg hT]]
  rw [simExecMarginal_weighted pe_C sim h_init K]
  rw [bundled_halt_to_dite pe_C pe_C.scheduler pe_C.initState g (by cases pe_C; rfl)]

private theorem simJointSched_internal (pe_C : ProbabilisticExecution sys_C)
    (σ_C : WeakScheduler sys_C) (hsched : pe_C.scheduler = σ_C.toScheduler)
    (sim : StrongProbabilisticSimulation sys_C sys_X R) :
    ∀ (E : AlterSeq (State_C × State_X) Label) (l : Label) (ω : PMF (State_C × State_X)),
      some (l, ω) ∈ ((simJointSched pe_C sim).next E).support → l = Silent.τ := by
  classical
  intro E l ω h_supp
  change some (l, ω) ∈ ((pe_C.scheduler.next (E.map Prod.fst)).bind (fun o =>
    match o with
    | none => PMF.pure none
    | some (l', μ_C) =>
      if h : R (simLastState E).1 (simLastState E).2 ∧
          sys_C.step (simLastState E).1 l' μ_C then
        PMF.pure (some (l', simCouple sim (simLastState E) l' μ_C))
      else PMF.pure none)).support at h_supp
  rw [PMF.mem_support_bind_iff] at h_supp
  obtain ⟨o, ho_mem, h_supp⟩ := h_supp
  cases o with
  | none =>
    rw [PMF.mem_support_pure_iff] at h_supp
    exact absurd h_supp.symm (by simp)
  | some lμ =>
    obtain ⟨l', μ_C⟩ := lμ
    simp only at h_supp
    by_cases hg : R (simLastState E).1 (simLastState E).2 ∧ sys_C.step (simLastState E).1 l' μ_C
    · rw [dif_pos hg, PMF.mem_support_pure_iff] at h_supp
      rw [Option.some.injEq, Prod.mk.injEq] at h_supp
      rw [hsched] at ho_mem
      rw [h_supp.1]
      exact σ_C.internal_only (E.map Prod.fst) l' μ_C ho_mem
    · rw [dif_neg hg, PMF.mem_support_pure_iff] at h_supp
      exact absurd h_supp (by simp)

/-- **Coupled-product lift of a single-state `weakTau`.** Driving the joint execution `simJointExec`
by the witness of `weakTau sys_C (pure q_C) ν_C` gives a `weakTau` on the coupled product
`simProd sys_C sys_X R`, whose concrete end-state marginal is `ν_C` and whose end-states are
`R`-related (the R-invariant `simJointExec_probOf_R`).

Reuses `simExecMarginal` + the R-invariant; the arbitrary start state is moved into the systems
by record-update (`{sys with init := ·}`), and the joint halting distribution is read via
`halt_integrate`. -/
theorem StrongProbabilisticSimulation.weakTau_joint
    (sim : StrongProbabilisticSimulation sys_C sys_X R)
    {q_C : State_C} {x : State_X} (hR : R q_C x)
    {ν_C : PMF State_C} (h : weakTau sys_C (PMF.pure q_C) ν_C) :
    ∃ Ξ : PMF (State_C × State_X),
      weakTau (simProd sys_C sys_X R) (PMF.pure (q_C, x)) Ξ ∧
      PMF.map Prod.fst Ξ = ν_C ∧
      ∀ p ∈ Ξ.support, R p.1 p.2 := by
  classical
  set sys_C' : System State_C Label := { sys_C with init := q_C } with hsysC'
  set sys_X' : System State_X Label := { sys_X with init := x } with hsysX'
  let sim' : StrongProbabilisticSimulation sys_C' sys_X' R := ⟨hR, sim.step⟩
  set σ_C : WeakScheduler sys_C' :=
    (weakTau_step_congr (sys := sys_C) (sys' := sys_C') rfl h).witnessScheduler with hσC
  let pe_C : ProbabilisticExecution sys_C' := ⟨PMF.pure q_C, σ_C.toScheduler⟩
  have hpeinit : pe_C.initState = PMF.pure sys_C'.init := rfl
  set σ_J : Scheduler (simProd sys_C' sys_X' R) := simJointSched pe_C sim' with hσJ
  let wσ_J : WeakScheduler (simProd sys_C' sys_X' R) :=
    { toScheduler := σ_J
      internal_only := simJointSched_internal pe_C σ_C rfl sim' }
  have hwtC : weakTau sys_C' (PMF.pure q_C) ν_C :=
    weakTau_step_congr (sys := sys_C) (sys' := sys_C') rfl h
  have hσChalts : (∑' e, σ_C.haltMass (PMF.pure q_C) e) = 1 := hwtC.witness_halts
  have hσCpush : ∀ s, ν_C s
      = ∑' e, σ_C.haltMass (PMF.pure q_C) e * (if e.1.endState e.2 = s then (1:ENNReal) else 0) :=
    hwtC.witness_pushforward
  -- a.s. halting of the joint scheduler from (q_C, x)
  have hjhalt : (∑' e, wσ_J.haltMass (PMF.pure (q_C, x)) e) = 1 := by
    have key := halt_integrate pe_C sim' hpeinit (fun _ => 1)
    simp only [mul_one] at key
    have heq : (∑' e, wσ_J.haltMass (PMF.pure (q_C, x)) e)
        = ∑' e : {e : AlterSeq (State_C × State_X) Label // e.trans.Terminates},
          (simJointSched pe_C sim').haltMass (PMF.pure (simProd sys_C' sys_X' R).init) e := rfl
    rw [heq, key]; exact hσChalts
  -- the concrete-state marginal of the joint halt-pushforward
  have hjpush : ∀ s : State_C, (∑' e, wσ_J.haltMass (PMF.pure (q_C, x)) e
        * (if (e.1.endState e.2).1 = s then (1:ENNReal) else 0)) = ν_C s := by
    intro s
    have key := halt_integrate pe_C sim' hpeinit (fun c => if c = s then (1:ENNReal) else 0)
    have heq : (∑' e, wσ_J.haltMass (PMF.pure (q_C, x)) e
          * (if (e.1.endState e.2).1 = s then (1:ENNReal) else 0))
        = ∑' e : {e : AlterSeq (State_C × State_X) Label // e.trans.Terminates},
          (simJointSched pe_C sim').haltMass (PMF.pure (simProd sys_C' sys_X' R).init) e
            * (fun c => if c = s then (1:ENNReal) else 0) ((e.1.endState e.2).1) := rfl
    rw [heq, key]
    exact (hσCpush s).symm
  -- R-support of the joint halt-pushforward
  have hRsupp : ∀ e : {e : AlterSeq (State_C × State_X) Label // e.trans.Terminates},
      wσ_J.haltMass (PMF.pure (q_C, x)) e ≠ 0 →
      R (e.1.endState e.2).1 (e.1.endState e.2).2 := by
    intro e hne
    have hprob : (simJointExec pe_C sim').probOf e.1 e.2 ≠ 0 := by
      intro h0; apply hne
      change (simJointExec pe_C sim').probOf e.1 e.2 * (simJointSched pe_C sim').next e.1 none = 0
      rw [h0, zero_mul]
    exact simJointExec_probOf_R pe_C sim' e.1 e.2 hprob
  -- assemble Ξ as the halting end-state pushforward PMF
  set F : (State_C × State_X) → ENNReal :=
    fun p => ∑' e, wσ_J.haltMass (PMF.pure (q_C, x)) e
      * (if e.1.endState e.2 = p then (1:ENNReal) else 0) with hF
  have hFsum : (∑' p, F p) = 1 := by
    simp only [hF]
    rw [ENNReal.tsum_comm]
    rw [show (∑' e, ∑' p, wσ_J.haltMass (PMF.pure (q_C, x)) e
          * (if e.1.endState e.2 = p then (1:ENNReal) else 0))
        = ∑' e, wσ_J.haltMass (PMF.pure (q_C, x)) e from by
      refine tsum_congr (fun e => ?_)
      rw [ENNReal.tsum_mul_left,
        tsum_eq_single (e.1.endState e.2) (fun p hp => by rw [if_neg (Ne.symm hp)]),
        if_pos rfl, mul_one]]
    exact hjhalt
  let Ξ : PMF (State_C × State_X) := ⟨F, by rw [← hFsum]; exact ENNReal.summable.hasSum⟩
  have hΞ : ∀ p, Ξ p = F p := fun _ => rfl
  -- the weak transition on the primed product, then transfer to the goal system
  have hwtJ : weakTau (simProd sys_C' sys_X' R) (PMF.pure (q_C, x)) Ξ := by
    refine ⟨wσ_J, hjhalt, fun p => ?_⟩
    rw [hΞ p, hF]
    exact tsum_congr (fun e => by convert rfl)
  refine ⟨Ξ, weakTau_step_congr (sys := simProd sys_C' sys_X' R) (sys' := simProd sys_C sys_X R)
    rfl hwtJ, ?_, ?_⟩
  · -- concrete marginal: Ξ.map fst = ν_C
    refine PMF.ext (fun s => ?_)
    rw [PMF.map_apply]
    rw [show (∑' p, (if s = p.1 then Ξ p else 0))
        = ∑' p, Ξ p * (if p.1 = s then (1:ENNReal) else 0) from
      tsum_congr (fun p => by by_cases hc : s = p.1 <;> simp [hc, eq_comm, mul_comm])]
    simp only [hΞ, hF]
    rw [show (∑' p, (∑' e, wσ_J.haltMass (PMF.pure (q_C, x)) e
            * (if e.1.endState e.2 = p then (1:ENNReal) else 0))
            * (if p.1 = s then (1:ENNReal) else 0))
        = ∑' p, ∑' e, wσ_J.haltMass (PMF.pure (q_C, x)) e
            * (if e.1.endState e.2 = p then (1:ENNReal) else 0)
            * (if p.1 = s then (1:ENNReal) else 0) from
      tsum_congr (fun p => by rw [ENNReal.tsum_mul_right])]
    rw [ENNReal.tsum_comm]
    rw [show (∑' e, ∑' p, wσ_J.haltMass (PMF.pure (q_C, x)) e
            * (if e.1.endState e.2 = p then (1:ENNReal) else 0)
            * (if p.1 = s then (1:ENNReal) else 0))
        = ∑' e, wσ_J.haltMass (PMF.pure (q_C, x)) e
            * (if (e.1.endState e.2).1 = s then (1:ENNReal) else 0) from by
      refine tsum_congr (fun e => ?_)
      rw [tsum_eq_single (e.1.endState e.2)
        (fun p hp => by rw [if_neg (Ne.symm hp), mul_zero, zero_mul]), if_pos rfl, mul_one]]
    exact hjpush s
  · -- R-support of Ξ
    intro p hp
    rw [PMF.mem_support_iff, hΞ] at hp
    simp only [hF] at hp
    have hex := mt ENNReal.tsum_eq_zero.mpr hp
    push Not at hex
    obtain ⟨e, he⟩ := hex
    have hne : wσ_J.haltMass (PMF.pure (q_C, x)) e ≠ 0 := fun h0 => he (by rw [h0, zero_mul])
    have hind : e.1.endState e.2 = p := by by_contra hc; exact he (by rw [if_neg hc, mul_zero])
    rw [← hind]; exact hRsupp e hne

/-- **Lifting a `weakTau` through a strong simulation** (Stage 1). If `R q_C x` and `pure q_C`
performs an internal weak transition to `ν_C` in `sys_C`, then `pure x` performs an internal weak
transition to some `Ν` in `sys_X` coupling `ν_C` along `R`. -/
theorem StrongProbabilisticSimulation.weakTau_lift
    (sim : StrongProbabilisticSimulation sys_C sys_X R)
    {q_C : State_C} {x : State_X} (hR : R q_C x)
    {ν_C : PMF State_C} (h : weakTau sys_C (PMF.pure q_C) ν_C) :
    ∃ Ν, weakTau sys_X (PMF.pure x) Ν ∧ PMFRel R ν_C Ν := by
  obtain ⟨Ξ, hwt, hfst, hsupp⟩ := sim.weakTau_joint hR h
  refine ⟨PMF.map Prod.snd Ξ, ?_, Ξ, hfst, rfl, hsupp⟩
  have hstep : ∀ (p : State_C × State_X) (μ : PMF (State_C × State_X)),
      (simProd sys_C sys_X R).step p Silent.τ μ →
        sys_X.step (Prod.snd p) Silent.τ (μ.map Prod.snd) := by
    intro p μ hs
    have hs' : sys_C.step p.1 Silent.τ (μ.map Prod.fst)
        ∧ sys_X.step p.2 Silent.τ (μ.map Prod.snd)
        ∧ (∀ q ∈ μ.support, R q.1 q.2) := hs
    exact hs'.2.1
  have hmap := weakTau_map (sysY := sys_X) Prod.snd hstep hwt
  rwa [PMF.pure_map] at hmap

end PLTS
