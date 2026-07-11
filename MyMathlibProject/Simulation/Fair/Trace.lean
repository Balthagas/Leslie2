/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Simulation.Fair.ConcreteMarginal

/-!
# Trace preservation of the coupled lift and its abstract marginal (step 3)

The trace-distribution half of fair soundness. Driving `simProd sys_C sys_A R` by a resolved
execution `pe_C` of `sys_C` via `simJointSchedR` (the resolved coupled scheduler), this file proves
the `R`-invariant of the coupled run (`simJointExecR_probOfR_R`), that the concrete marginalisation
collapses to `pe_C` (`cWeight_simJointExecR_eq_probOfR`), and assembles the trace-preservation chain
`simJointExecR_traceProbR`, `abstractMarginal_traceProbR`,
`abstractMarginal_simJointExecR_initState`,
culminating in `abstractMarginal_simJointExecR_traceProbR`
(`pe_A.traceProbR = pe_C.traceProbR`). No finiteness. The remaining fairness half is in
`Simulation/Fair/Soundness`.
-/

open Stream'

namespace PLTS

variable {State_C State_A Label : Type} [Silent Label]

namespace FairStrongProbabilisticSimulation

variable {sys_C : System State_C Label} {sys_A : System State_A Label}
  {F_C : Fairness sys_C} {F_A : Fairness sys_A} {R : State_C → State_A → Prop}

omit [Silent Label] in
/-- `probOfR` depends only on the history, not the termination proof. -/
private theorem probOfR_congr {sys : System (State_C × State_A) Label}
    (peJ : ResolvedProbabilisticExecution sys)
    (r r' : ResolvedExec (State_C × State_A) Label) (h : r = r')
    (hr : r.trans.Terminates) (hr' : r'.trans.Terminates) :
    peJ.probOfR r hr = peJ.probOfR r' hr' := by subst h; rfl

/-- Membership of `some (l, ω)` in `simJointSchedR.next r`'s support forces the guard at
`simLastStateR r` and identifies `ω` as the coupling `simCouple`. Resolved analogue of
`simJointSched_next_support` (`Simulation/Trace.lean`). -/
theorem simJointSchedR_next_support
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (r : ResolvedExec (State_C × State_A) Label) (l : Label) (ω : PMF (State_C × State_A))
    (h_supp : some (l, ω) ∈ ((simJointSchedR pe_C sim).next r).support) :
    ∃ μ_C, R (simLastStateR r).1 (simLastStateR r).2 ∧
      sys_C.step (simLastStateR r).1 l μ_C ∧
      ω = simCoupleF sim (simLastStateR r) l μ_C := by
  classical
  change some (l, ω) ∈ ((pe_C.scheduler.next (concreteProjR r)).bind (fun o =>
    match o with
    | none => PMF.pure none
    | some (l', μ_C) =>
      if h : R (simLastStateR r).1 (simLastStateR r).2 ∧
          sys_C.step (simLastStateR r).1 l' μ_C then
        PMF.pure (some (l', simCoupleF sim (simLastStateR r) l' μ_C))
      else PMF.pure none)).support at h_supp
  rw [PMF.mem_support_bind_iff] at h_supp
  obtain ⟨o, _, h_supp⟩ := h_supp
  cases o with
  | none =>
    rw [PMF.mem_support_pure_iff] at h_supp
    exact absurd h_supp.symm (by simp)
  | some lμ =>
    obtain ⟨l', μ_C⟩ := lμ
    simp only at h_supp
    by_cases hg : R (simLastStateR r).1 (simLastStateR r).2 ∧
        sys_C.step (simLastStateR r).1 l' μ_C
    · rw [dif_pos hg, PMF.mem_support_pure_iff] at h_supp
      rw [Option.some.injEq, Prod.mk.injEq] at h_supp
      obtain ⟨rfl, rfl⟩ := h_supp
      exact ⟨μ_C, hg.1, hg.2, rfl⟩
    · rw [dif_neg hg, PMF.mem_support_pure_iff] at h_supp
      exact absurd h_supp (by simp)

/-- **R-invariant** (over `Seq.ofList`-form histories) for the resolved coupled execution. Resolved
analogue of `simJointExec_probOf_R_ofList` (`Simulation/Trace.lean`). -/
private theorem simJointExecR_probOfR_R_ofList
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (L : List ((Label × PMF (State_C × State_A)) × (State_C × State_A))) (s₀ : State_C × State_A)
    (hFin : (Seq.ofList L :
        Seq ((Label × PMF (State_C × State_A)) × (State_C × State_A))).Terminates)
    (hne : (simJointExecR pe_C sim).probOfR ⟨s₀, Seq.ofList L⟩ hFin ≠ 0) :
    R ((⟨s₀, Seq.ofList L⟩ : ResolvedExec (State_C × State_A) Label).endState hFin).1
      ((⟨s₀, Seq.ofList L⟩ : ResolvedExec (State_C × State_A) Label).endState hFin).2 := by
  classical
  induction L using List.reverseRecOn generalizing s₀ with
  | nil =>
    rw [AlterSeq.endState_of_trans_nil _ (by rw [Stream'.Seq.ofList_nil]) hFin]
    rw [probOfR_congr (simJointExecR pe_C sim)
      ⟨s₀, Seq.ofList []⟩ ⟨s₀, Seq.nil⟩ (by rw [Stream'.Seq.ofList_nil]) hFin
      Stream'.Seq.terminates_nil,
      ResolvedProbabilisticExecution.probOfR_nil] at hne
    change (PMF.pure (simProd sys_C sys_A R).init) s₀ ≠ 0 at hne
    rw [PMF.pure_apply] at hne
    have : s₀ = (simProd sys_C sys_A R).init := by
      by_contra hc; rw [if_neg hc] at hne; exact hne rfl
    rw [this]; exact sim.init
  | append_singleton rest last ih =>
    -- ofList (rest ++ [last]) = (ofList rest).append (cons last nil).
    have hsplit : (Seq.ofList (rest ++ [last]) :
          Seq ((Label × PMF (State_C × State_A)) × (State_C × State_A)))
        = (Seq.ofList rest).append (Seq.cons last Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have hrest_fin : (Seq.ofList rest :
        Seq ((Label × PMF (State_C × State_A)) × (State_C × State_A))).Terminates :=
      Stream'.Seq.terminates_ofList _
    have hFinS : ((Seq.ofList rest).append (Seq.cons last Seq.nil)).Terminates := by
      rw [← hsplit]; exact hFin
    -- factor probOfR at the append.
    rw [probOfR_congr (simJointExecR pe_C sim)
      ⟨s₀, Seq.ofList (rest ++ [last])⟩ ⟨s₀, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩
      (by rw [hsplit]) hFin hFinS,
      (simJointExecR pe_C sim).probOfR_append_singleton s₀
        (Seq.ofList rest) hrest_fin last hFinS] at hne
    have hker : (simJointExecR pe_C sim).rkernel ⟨s₀, Seq.ofList rest⟩ last ≠ 0 :=
      fun h0 => hne (by rw [h0, mul_zero])
    -- rkernel ≠ 0 ⟹ next (some (last.1.1, last.1.2)) ≠ 0 and last.1.2 last.2 ≠ 0.
    rw [ResolvedProbabilisticExecution.rkernel] at hker
    have hnext_ne : (simJointExecR pe_C sim).scheduler.next ⟨s₀, Seq.ofList rest⟩
        (some (last.1.1, last.1.2)) ≠ 0 := fun h0 => hker (by rw [h0, zero_mul])
    have hωlast : last.1.2 last.2 ≠ 0 := fun h0 => hker (by rw [h0, mul_zero])
    -- from the support, identify last.1.2 = ω as a coupling and use its support ⊆ R.
    obtain ⟨μ_C, hRpre, _hstep, hωeq⟩ := simJointSchedR_next_support pe_C sim
      ⟨s₀, Seq.ofList rest⟩ last.1.1 last.1.2 ((PMF.mem_support_iff _ _).mpr hnext_ne)
    -- endState of the append is last.2.
    have hend : (⟨s₀, Seq.ofList (rest ++ [last])⟩ :
        ResolvedExec (State_C × State_A) Label).endState hFin = last.2 := by
      rw [AlterSeq.endState_congr_pub
        (show (⟨s₀, Seq.ofList (rest ++ [last])⟩ : ResolvedExec (State_C × State_A) Label)
          = ⟨s₀, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩ from by rw [hsplit]) hFin hFinS]
      obtain ⟨ll, qq⟩ := last
      exact AlterSeq.endState_append_singleton ⟨s₀, Seq.ofList rest⟩ hrest_fin ll qq
    rw [hend]
    -- last.2 ∈ (last.1.2).support ⊆ R.
    have hqsupp : last.2 ∈ (last.1.2).support := (PMF.mem_support_iff _ _).mpr hωlast
    rw [hωeq] at hqsupp
    exact (simCoupleF_step sim (simLastStateR ⟨s₀, Seq.ofList rest⟩) last.1.1 μ_C
      ⟨hRpre, _hstep⟩).2.2 last.2 hqsupp

/-- **R-invariant.** Every product resolved history with positive `simJointExecR`-probability ends
in an `R`-related pair. Resolved analogue of `simJointExec_probOf_R` (`Simulation/Trace.lean`). -/
theorem simJointExecR_probOfR_R
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (r : ResolvedExec (State_C × State_A) Label) (hT : r.trans.Terminates)
    (hne : (simJointExecR pe_C sim).probOfR r hT ≠ 0) :
    R (r.endState hT).1 (r.endState hT).2 := by
  classical
  have hofl : (Seq.ofList (r.trans.toList hT) :
      Seq ((Label × PMF (State_C × State_A)) × (State_C × State_A))) = r.trans :=
    Stream'.Seq.ofList_toList r.trans hT
  have hFin' : (Seq.ofList (r.trans.toList hT) :
      Seq ((Label × PMF (State_C × State_A)) × (State_C × State_A))).Terminates := by
    rw [hofl]; exact hT
  have heq :
    (⟨r.init, Seq.ofList (r.trans.toList hT)⟩ : ResolvedExec (State_C × State_A) Label) = r := by
    cases r; simp only [hofl]
  rw [AlterSeq.endState_congr_pub heq.symm hT hFin']
  refine simJointExecR_probOfR_R_ofList pe_C sim (r.trans.toList hT) r.init hFin' ?_
  rw [probOfR_congr (simJointExecR pe_C sim) _ r heq hFin' hT]
  exact hne

omit [Silent Label] in
/-- `probOfR` depends only on the history (concrete side), not the termination proof. -/
private theorem probOfR_congr' (pe : ResolvedProbabilisticExecution sys_C)
    (r r' : ResolvedExec State_C Label) (h : r = r')
    (hr : r.trans.Terminates) (hr' : r'.trans.Terminates) :
    pe.probOfR r hr = pe.probOfR r' hr' := by subst h; rfl

/-- **Pushforward of the coupled emission is the `pe_C`-emission.** When the guard holds at
`simLastStateR r`, the `Prod.fst`-pushforward of `simJointSchedR`'s emission, read on `some (l, ν)`,
is exactly `pe_C`'s emission `pe_C.scheduler.next (concreteProjR r) (some (l, ν))`. The coupling is
`simCouple …` whose `Prod.fst`-marginal is `ν`, so the pushforward maps the single `pe_C`-emission
`some (l, ν)` back to `some (l, ν)`; every other `pe_C`-emission `some (l', μ_C)` maps to
`some (l', μ_C)` (guard holds) or `none` (guard fails), contributing `0` to the `some (l, ν)`
slot. -/
theorem simJointSchedR_mapEmit_fst
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (r : ResolvedExec (State_C × State_A) Label) (l : Label) (ν : PMF State_C)
    (hg : R (simLastStateR r).1 (simLastStateR r).2 ∧ sys_C.step (simLastStateR r).1 l ν) :
    (((simJointExecR pe_C sim).scheduler.next r).map (mapEmit Prod.fst)) (some (l, ν))
      = pe_C.scheduler.next (concreteProjR r) (some (l, ν)) := by
  classical
  -- `map (mapEmit fst) (bind (next pe_C) k) = bind (next pe_C) (map (mapEmit fst) ∘ k)`.
  change ((((pe_C.scheduler.next (concreteProjR r)).bind (fun o =>
      match o with
      | none => PMF.pure none
      | some (l', μ_C) =>
        if h : R (simLastStateR r).1 (simLastStateR r).2 ∧
            sys_C.step (simLastStateR r).1 l' μ_C then
          PMF.pure (some (l', simCoupleF sim (simLastStateR r) l' μ_C))
        else PMF.pure none)).map (mapEmit Prod.fst))) (some (l, ν)) = _
  rw [PMF.map_bind]
  rw [PMF.bind_apply]
  -- Only `o = some (l, ν)` contributes: for it the pushforward of the emission is
  -- `pure (some(l,ν))`.
  rw [tsum_eq_single (some (l, ν)) ?_]
  · -- the surviving term.
    have hval : ((PMF.pure (some (l, simCoupleF sim (simLastStateR r) l ν))).map
          (mapEmit Prod.fst)) (some (l, ν)) = 1 := by
      rw [PMF.pure_map, mapEmit, Option.map_some,
        simCoupleF_map_fst sim (simLastStateR r) l ν hg]
      rw [PMF.pure_apply, if_pos rfl]
    -- reduce the `match`/`dif` on `o = some (l, ν)` using the guard.
    change pe_C.scheduler.next (concreteProjR r) (some (l, ν))
        * ((if h : R (simLastStateR r).1 (simLastStateR r).2 ∧
              sys_C.step (simLastStateR r).1 l ν then
            PMF.pure (some (l, simCoupleF sim (simLastStateR r) l ν))
          else PMF.pure none).map (mapEmit Prod.fst)) (some (l, ν))
      = pe_C.scheduler.next (concreteProjR r) (some (l, ν))
    rw [dif_pos hg, hval, mul_one]
  · -- other terms vanish.
    intro o ho
    cases o with
    | none =>
      change _ * ((PMF.pure none).map (mapEmit Prod.fst)) (some (l, ν)) = 0
      rw [PMF.pure_map, mapEmit]; simp
    | some lμ =>
      obtain ⟨l', μ_C⟩ := lμ
      by_cases hgm : R (simLastStateR r).1 (simLastStateR r).2 ∧
          sys_C.step (simLastStateR r).1 l' μ_C
      · change _ * ((if h : R (simLastStateR r).1 (simLastStateR r).2 ∧
              sys_C.step (simLastStateR r).1 l' μ_C then
            PMF.pure (some (l', simCoupleF sim (simLastStateR r) l' μ_C))
          else PMF.pure none).map (mapEmit Prod.fst)) (some (l, ν)) = 0
        rw [dif_pos hgm, PMF.pure_map, mapEmit, Option.map_some,
          simCoupleF_map_fst sim (simLastStateR r) l' μ_C hgm]
        rw [PMF.pure_apply, if_neg (fun h => ho h.symm), mul_zero]
      · change _ * ((if h : R (simLastStateR r).1 (simLastStateR r).2 ∧
              sys_C.step (simLastStateR r).1 l' μ_C then
            PMF.pure (some (l', simCoupleF sim (simLastStateR r) l' μ_C))
          else PMF.pure none).map (mapEmit Prod.fst)) (some (l, ν)) = 0
        rw [dif_neg hgm, PMF.pure_map, mapEmit]; simp

/-- **The concrete marginalisation collapses to `pe_C`.** The belief weight `cWeight` of the coupled
lift over a concrete resolved history `r_C` equals `pe_C.probOfR r_C`. Cons-end induction: at each
appended step the coupling `ω` in the fibre is forced to be `simCouple …` (whose `Prod.fst`-marginal
is `ν`, so `∑_{s_A'} ω (s_C', s_A') = ν s_C'`, packaged by `mapEmit_fst_mul`), and the
pushed-forward emission weight is `pe_C.scheduler.next (concreteProjR r') (some (l, ν))` (constant
over the fibre,
`simJointSchedR_mapEmit_fst`). The guard is discharged by `pe_C`-validity (for `sys_C.step`) and by
`simJointExecR_probOfR_R` (for the `R`-relation at the fibre history's end). -/
theorem cWeight_simJointExecR_eq_probOfR
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (h_init : pe_C.initState = PMF.pure sys_C.init)
    (r_C : ResolvedExec State_C Label) (hT : r_C.trans.Terminates) :
    cWeight (simJointExecR pe_C sim) r_C hT = pe_C.probOfR r_C hT := by
  classical
  suffices H : ∀ n (r_C : ResolvedExec State_C Label) (hT : r_C.trans.Terminates),
      (r_C.trans.toList hT).length = n →
      cWeight (simJointExecR pe_C sim) r_C hT = pe_C.probOfR r_C hT from H _ r_C hT rfl
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
    rw [cWeight_nil (simJointExecR pe_C sim) i, pe_C.probOfR_nil i]
    -- `(pure (simProd..).init).map Prod.fst` applied at `i` is `pure sys_C.init` applied at `i`.
    change ((PMF.pure (simProd sys_C sys_A R).init).map Prod.fst) i = pe_C.initState i
    rw [PMF.pure_map, h_init]
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
    -- LHS: cons-end sum for `cWeight` of the extended history.
    rw [cWeight_congr (simJointExecR pe_C sim) r_C
          ⟨r_C.init, prev.append (Seq.cons ((l, ν), s_C') Seq.nil)⟩ hr_eq hT happ,
        cWeight_append_singleton (simJointExecR pe_C sim) ⟨r_C.init, prev⟩ hprev l ν s_C' happ]
    -- RHS: cons-end factorisation of `pe_C.probOfR` + IH.
    rw [probOfR_congr' pe_C r_C ⟨r_C.init, prev.append (Seq.cons ((l, ν), s_C') Seq.nil)⟩ hr_eq
          hT happ,
        pe_C.probOfR_append_singleton r_C.init prev hprev ((l, ν), s_C') happ,
        ← ih ⟨r_C.init, prev⟩ hprev hlen_prev]
    unfold ResolvedProbabilisticExecution.rkernel
    -- Expose the belief-weight `cWeight prev` on the RHS as its fibre sum, then pull the common
    -- factor `(pe_C.next prev (some (l, ν)) · ν s_C')` inside; both sides become `∑' r'` over the
    -- `concreteProjR`-fibre of `⟨r_C.init, prev⟩`.
    unfold cWeight
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr (fun r' => ?_)
    -- collapse the inner double sum via `mapEmit_fst_mul`.
    rw [show (∑' p : {ω : PMF (State_C × State_A) // ω.map Prod.fst = ν} × State_A,
            (simJointExecR pe_C sim).probOfR r'.1 (terminates_of_concreteProjR_eq hprev r'.2)
              * ((simJointExecR pe_C sim).scheduler.next r'.1 (some (l, p.1.1))
                  * p.1.1 (s_C', p.2)))
          = (simJointExecR pe_C sim).probOfR r'.1 (terminates_of_concreteProjR_eq hprev r'.2)
              * (((simJointExecR pe_C sim).scheduler.next r'.1).map (mapEmit Prod.fst))
                  (some (l, ν))
              * ν s_C' from by
        rw [ENNReal.tsum_mul_left, mul_assoc,
          mapEmit_fst_mul (simJointExecR pe_C sim) r'.1 l ν s_C']]
    -- discharge the pushforward emission via `simJointSchedR_mapEmit_fst`, needing the guard.
    by_cases hp0 : (simJointExecR pe_C sim).probOfR r'.1
        (terminates_of_concreteProjR_eq hprev r'.2) = 0
    · rw [hp0, zero_mul, zero_mul, zero_mul]
    · have hfibT : r'.1.trans.Terminates := terminates_of_concreteProjR_eq hprev r'.2
      -- guard: `R` at the fibre history's end (from `simJointExecR_probOfR_R`), and `sys_C.step ν`
      -- (from `pe_C`-validity: the pushforward emission is nonzero, else the LHS is `0`).
      have hRend : R (simLastStateR r'.1).1 (simLastStateR r'.1).2 := by
        have hR := simJointExecR_probOfR_R pe_C sim r'.1 hfibT hp0
        rw [simLastStateR, dif_pos hfibT]; exact hR
      -- `pe_C.scheduler.next` at the fibre history `concreteProjR r'.1` and at `⟨r_C.init, prev⟩`
      -- (the RHS's argument) agree, since `concreteProjR r'.1 = ⟨r_C.init, prev⟩` (`r'.2`).
      have hnext_eq : pe_C.scheduler.next (concreteProjR r'.1) (some (l, ν))
          = pe_C.scheduler.next ⟨r_C.init, prev⟩ (some (l, ν)) :=
        congrArg (fun e => pe_C.scheduler.next e (some (l, ν))) r'.2
      -- The pushforward emission equals the `pe_C`-emission
      -- `pe_C.next ⟨r_C.init, prev⟩ (some (l, ν))`.
      -- Both sides then match syntactically
      -- (RHS is `pe_C.next ⟨r_C.init, prev⟩ (some (l, ν)) · ν s_C'`).
      have hemit_eq : (((simJointExecR pe_C sim).scheduler.next r'.1).map (mapEmit Prod.fst))
          (some (l, ν)) = pe_C.scheduler.next ⟨r_C.init, prev⟩ (some (l, ν)) := by
        by_cases hstep : sys_C.step (simLastStateR r'.1).1 l ν
        · rw [simJointSchedR_mapEmit_fst pe_C sim r'.1 l ν ⟨hRend, hstep⟩, hnext_eq]
        · -- guard fails ⇒ both emissions vanish. Pushforward = 0 (its support forces `sys_C.step`);
          -- `pe_C`-emission = 0 (validity: a nonzero emission is a `sys_C.step`).
          have hpush0 : (((simJointExecR pe_C sim).scheduler.next r'.1).map (mapEmit Prod.fst))
              (some (l, ν)) = 0 := by
            by_contra hemit0
            -- a nonzero pushforward gives a coupling `ω` over `ν` in the emission's support.
            obtain ⟨ω, hωne, hνeq⟩ :
                ∃ ω : PMF (State_C × State_A),
                  (simJointExecR pe_C sim).scheduler.next r'.1 (some (l, ω)) ≠ 0
                    ∧ ν = ω.map Prod.fst := by
              rw [mapEmit, PMF.map_apply] at hemit0
              have hex2 := mt ENNReal.tsum_eq_zero.mpr hemit0
              push Not at hex2
              obtain ⟨o, ho⟩ := hex2
              by_cases hc : some (l, ν) = Option.map
                  (fun lμ : Label × PMF (State_C × State_A) => (lμ.1, lμ.2.map Prod.fst)) o
              · cases o with
                | none => simp at hc
                | some lμ =>
                  obtain ⟨l', ω⟩ := lμ
                  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
                  obtain ⟨rfl, rfl⟩ := hc
                  exact ⟨ω, fun h0 => by rw [h0] at ho; simp at ho, rfl⟩
              · rw [if_neg hc] at ho; exact absurd rfl ho
            obtain ⟨μ_C, _, hstep', hωeq⟩ := simJointSchedR_next_support pe_C sim r'.1 l ω
              ((PMF.mem_support_iff _ _).mpr hωne)
            rw [hνeq, hωeq, simCoupleF_map_fst sim (simLastStateR r'.1) l μ_C
              ⟨hRend, hstep'⟩] at hstep
            exact hstep hstep'
          have hpe0 : pe_C.scheduler.next ⟨r_C.init, prev⟩ (some (l, ν)) = 0 := by
            rw [← hnext_eq]
            by_contra hnz
            have hstateP : (concreteProjR r'.1).stateAt (Nat.find hfibT)
                = some (simLastStateR r'.1).1 := by
              rw [concreteProjR_stateAt, simLastStateR, dif_pos hfibT,
                AlterSeq.stateAt_find_eq_endState r'.1 hfibT]; rfl
            have htermC : (concreteProjR r'.1).trans.TerminatedAt (Nat.find hfibT) :=
              (concreteProjR_terminatedAt_iff r'.1 (Nat.find hfibT)).mpr (Nat.find_spec hfibT)
            exact hstep (pe_C.scheduler.valid (concreteProjR r'.1) (Nat.find hfibT)
              (simLastStateR r'.1).1 htermC hstateP l ν ((PMF.mem_support_iff _ _).mpr hnz))
          rw [hpush0, hpe0]
      rw [hemit_eq, mul_assoc]

/-- **The coupled lift preserves `traceProbR`.** Assembled from the general marginal-preservation
`concreteMarginal_traceProbR`, the value telescoping `concreteMarginal_probOfR`, and the concrete
marginalisation collapse `cWeight_simJointExecR_eq_probOfR` (which identifies the concrete marginal
of the coupled lift with `pe_C`). -/
theorem simJointExecR_traceProbR
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (h_init : pe_C.initState = PMF.pure sys_C.init) (τ : Seq Label) :
    (simJointExecR pe_C sim).traceProbR τ = pe_C.traceProbR τ := by
  have hpt : ∀ (r_C : ResolvedExec State_C Label) (hT : r_C.trans.Terminates),
      (concreteMarginal (simJointExecR pe_C sim)).probOfR r_C hT = pe_C.probOfR r_C hT :=
    fun r_C hT => by
      rw [concreteMarginal_probOfR (simJointExecR pe_C sim) r_C hT,
        cWeight_simJointExecR_eq_probOfR pe_C sim h_init r_C hT]
  rw [← concreteMarginal_traceProbR (simJointExecR pe_C sim) rfl τ]
  unfold ResolvedProbabilisticExecution.traceProbR
  exact tsum_congr (fun r => hpt r.1 r.2.1)

/-- **The abstract marginal preserves `traceProbR`.** Assembled from `avgWeight_abstractMarginal`
and the existing plain results `mapBeliefExec_traceProb`, `traceProb_average`. No finiteness. -/
theorem abstractMarginal_traceProbR
    (peJ : ResolvedProbabilisticExecution (simProd sys_C sys_A R))
    (h_init : peJ.initState = PMF.pure (simProd sys_C sys_A R).init) (τ : Seq Label) :
    (abstractMarginal peJ).traceProbR τ = peJ.traceProbR τ := by
  rw [← (abstractMarginal peJ).traceProbR_eq_sum_avgWeight τ,
    show (∑' e : {e : AlterSeq State_A Label //
          e.trans.Terminates ∧ sys_A.trace e = τ ∧ sys_A.IsTight e},
        (abstractMarginal peJ).avgWeight e.1 e.2.1)
      = ∑' e : {e : AlterSeq State_A Label //
          e.trans.Terminates ∧ sys_A.trace e = τ ∧ sys_A.IsTight e},
        (mapBeliefExec Prod.snd simProd_hstep_snd peJ.average).probOf e.1 e.2.1 from
      tsum_congr (fun e => avgWeight_abstractMarginal peJ h_init e.1 e.2.1)]
  change sys_A.traceProb (mapBeliefExec Prod.snd simProd_hstep_snd peJ.average) τ
    = peJ.traceProbR τ
  rw [mapBeliefExec_traceProb Prod.snd simProd_hstep_snd peJ.average rfl h_init τ]
  exact peJ.traceProb_average τ

/-- Initial distribution of the abstract witness is Dirac on `sys_A.init`. -/
theorem abstractMarginal_simJointExecR_initState
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R) :
    (abstractMarginal (simJointExecR pe_C sim)).initState = PMF.pure sys_A.init := by
  change (PMF.pure (simProd sys_C sys_A R).init).map Prod.snd = PMF.pure sys_A.init
  rw [PMF.pure_map]; rfl

/-- **Trace preservation of the full construction** (`pe_A.traceProbR = pe_C.traceProbR`), the goal
of Phase 3. Composes `abstractMarginal_traceProbR` with `simJointExecR_traceProbR`. -/
theorem abstractMarginal_simJointExecR_traceProbR
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (h_init : pe_C.initState = PMF.pure sys_C.init) (τ : Seq Label) :
    (abstractMarginal (simJointExecR pe_C sim)).traceProbR τ = pe_C.traceProbR τ := by
  rw [abstractMarginal_traceProbR (simJointExecR pe_C sim) rfl τ]
  exact simJointExecR_traceProbR pe_C sim h_init τ

end FairStrongProbabilisticSimulation

end PLTS
