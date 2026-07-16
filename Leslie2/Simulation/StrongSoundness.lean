/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Other.Ennreal
import Leslie2.Simulation.SimDefs
import Leslie2.Simulation.TraceMap

/-!
# Strong simulation is sound for trace distributions

A `StrongProbabilisticSimulation` of `sys_C` by `sys_A` makes every trace
distribution achievable by the concrete system `sys_C` also achievable by the
abstract system `sys_A`:

  `achievableTraceDists sys_C ⊆ achievableTraceDists sys_A`.

This is the soundness direction of simulation. (Trace-distribution *equality*
would additionally require a simulation in the reverse direction.) The two
systems agree on which labels are internal automatically, since the
internal/external classification is canonical (the silent label `τ`).

## Proof architecture

A *strong* simulation is **lockstep**: each concrete step is matched by an
abstract step with the *same label* (no stuttering). The proof factors through
the **coupled product system** `simProd sys_C sys_A R` over `State_C × State_A`,
whose steps carry a `PMFRel R`-style coupling, in two inclusions:

* `simProd_achievableTraceDists_superset` (**lift**): every trace distribution of
  `sys_C` is realised by the joint system — drive the joint execution by `pe_C`
  on the concrete projection and, at each emitted `(l, μ_C)`, draw the joint
  successor from the coupling `ω` given by `sim.step` (so `ω.map fst = μ_C`,
  `ω.map snd` a valid `sys_A` step, `support ω ⊆ R`). The concrete projection of
  the joint execution is exactly `pe_C`, and labels are shared, so the joint
  trace distribution equals that of `pe_C`. This direction is a *forward*
  construction (no marginalisation).

* `achievableTraceDists_map` (**project**, the crux): a *functional*
  label-preserving simulation `f : X → Y` (`f init = init`,
  `sys_X.step s l μ → sys_Y.step (f s) l (μ.map f)`, internal-compatible)
  satisfies `achievableTraceDists sys_X ⊆ achievableTraceDists sys_Y`. Applied to
  `f = Prod.snd` this projects the joint system onto `sys_A`. Realising the
  pushed-forward execution by a single `sys_Y`-scheduler is a
  marginalisation/disintegration (posterior over `f`-fibres of histories), in the
  same family as `dist_traceProb` and the posterior-mixing in `Weak/WeakChar.lean`.

The main theorem is then `lift.trans (map Prod.snd …)`.
-/

open Stream'

namespace PLTS

-- The canonical-`τ` instance `[Silent Label]` is threaded as a section variable
-- but is unused by some pure helper lemmas; silence the over-inclusion linter.
set_option linter.unusedSectionVars false

variable {State_C State_A Label : Type} [Silent Label]

/-- The **coupled product** of two systems related by `R`: a labelled system on
`State_C × State_A` whose steps carry a coupling `ω : PMF (State_C × State_A)`
that projects to a valid step on each side and is supported in `R`. The
internal/external classification is canonical (the silent label `τ` from the
`Silent Label` instance), shared by both factors. -/
def simProd (sys_C : System State_C Label) (sys_A : System State_A Label)
    (R : State_C → State_A → Prop) : System (State_C × State_A) Label where
  init := (sys_C.init, sys_A.init)
  step p l ω :=
    sys_C.step p.1 l (ω.map Prod.fst) ∧
    sys_A.step p.2 l (ω.map Prod.snd) ∧
    (∀ q ∈ ω.support, R q.1 q.2)


/-! ### Infrastructure for the coupling lift

The lift drives the joint execution by `pe_C` on the concrete projection and, at
each emitted `(l, μ_C)`, draws the joint successor from the coupling `ω` supplied
by `sim.step`. We assemble: a total current-state extractor `simLastState`; a
classical coupling extractor `simCouple` (with its marginal/step facts); the
joint scheduler `simJointSched`; and the joint execution `simJointExec`. -/

variable {sys_C : System State_C Label} {sys_A : System State_A Label}
  {R : State_C → State_A → Prop}

/-- The current joint state of a finite history (its end-state), defaulting to
the initial state on non-terminating histories (never reached in practice). -/
noncomputable def simLastState (E : AlterSeq (State_C × State_A) Label) :
    State_C × State_A :=
  open Classical in
  if h : E.trans.Terminates then E.endState h else E.init

/-- The classical coupling extractor. When the guard `R p.1 p.2 ∧ sys_C.step p.1 l μ_C`
holds, `sim.step` yields an abstract successor and a `PMFRel`-coupling `ω`; we
return that `ω`. Otherwise the value is irrelevant (`PMF.pure p`). -/
noncomputable def simCouple (sim : StrongProbabilisticSimulation sys_C sys_A R)
    (p : State_C × State_A) (l : Label) (μ_C : PMF State_C) : PMF (State_C × State_A) :=
  open Classical in
  if h : R p.1 p.2 ∧ sys_C.step p.1 l μ_C then
    ((sim.step p.1 p.2 h.1 l μ_C h.2).choose_spec.2).choose
  else PMF.pure p

/-- First marginal of the coupling is `μ_C`. -/
theorem simCouple_map_fst (sim : StrongProbabilisticSimulation sys_C sys_A R)
    (p : State_C × State_A) (l : Label) (μ_C : PMF State_C)
    (h : R p.1 p.2 ∧ sys_C.step p.1 l μ_C) :
    (simCouple sim p l μ_C).map Prod.fst = μ_C := by
  rw [simCouple, dif_pos h]
  exact ((sim.step p.1 p.2 h.1 l μ_C h.2).choose_spec.2).choose_spec.1

/-- The coupling realises a valid `simProd`-step from `p`. -/
theorem simCouple_step (sim : StrongProbabilisticSimulation sys_C sys_A R)
    (p : State_C × State_A) (l : Label) (μ_C : PMF State_C)
    (h : R p.1 p.2 ∧ sys_C.step p.1 l μ_C) :
    (simProd sys_C sys_A R).step p l (simCouple sim p l μ_C) := by
  have hspec := (sim.step p.1 p.2 h.1 l μ_C h.2).choose_spec
  have hrel := hspec.2.choose_spec
  refine ⟨?_, ?_, ?_⟩
  · rw [simCouple_map_fst sim p l μ_C h]; exact h.2
  · rw [simCouple, dif_pos h, hrel.2.1]; exact hspec.1
  · intro q hq; rw [simCouple, dif_pos h] at hq; exact hrel.2.2 q hq

/-- The joint scheduler. On history `E`, run `pe_C`'s scheduler on the concrete
projection `E.map Prod.fst`; for each emitted `(l, μ_C)`, if the guard at the
current joint state `simLastState E` holds, emit `(l, simCouple …)`, else halt.
The guard makes `valid` provable universally: any emitted `(l, ω)` forces the
guard, so `ω` is a genuine coupling realising a `simProd`-step. -/
noncomputable def simJointSched
    (pe_C : ProbabilisticExecution sys_C)
    (sim : StrongProbabilisticSimulation sys_C sys_A R) :
    Scheduler (simProd sys_C sys_A R) where
  next E :=
    open Classical in
    (pe_C.scheduler.next (E.map Prod.fst)).bind (fun o =>
      match o with
      | none => PMF.pure none
      | some (l, μ_C) =>
        if h : R (simLastState E).1 (simLastState E).2 ∧
            sys_C.step (simLastState E).1 l μ_C then
          PMF.pure (some (l, simCouple sim (simLastState E) l μ_C))
        else PMF.pure none)
  valid := by
    classical
    intro E n s e_term_n e_stateAt_eq l ω h_supp
    -- Identify `s = E.endState`, i.e. `s = simLastState E` (mirrors SchedulerBind).
    have hT : E.trans.Terminates := ⟨n, e_term_n⟩
    have h_find_le : Nat.find hT ≤ n := Nat.find_le e_term_n
    have h_n_le : n ≤ Nat.find hT := by
      by_contra h_lt
      push Not at h_lt
      rcases n with _ | m
      · exact absurd h_lt (Nat.not_lt_zero _)
      · have hk_ge : Nat.find hT ≤ m := Nat.lt_succ_iff.mp h_lt
        have h_term_k : E.trans.TerminatedAt m :=
          Stream'.Seq.terminated_stable E.trans hk_ge (Nat.find_spec hT)
        have h_state_none : E.stateAt (m + 1) = none := by
          change (E.trans.get? m).map Prod.snd = none
          rw [show E.trans.get? m = none from h_term_k]; rfl
        rw [h_state_none] at e_stateAt_eq
        exact Option.some_ne_none s e_stateAt_eq.symm
    have h_n_eq : n = Nat.find hT := le_antisymm h_n_le h_find_le
    have h_s_eq : s = E.endState hT := by
      have h := AlterSeq.stateAt_find_eq_endState E hT
      rw [← h_n_eq] at h; rw [h] at e_stateAt_eq
      exact (Option.some.inj e_stateAt_eq).symm
    have h_last : simLastState E = s := by rw [h_s_eq, simLastState, dif_pos hT]
    -- The emitted `(l, ω)` forces the guard true, so `simCouple` is a real coupling.
    change some (l, ω) ∈ ((pe_C.scheduler.next (E.map Prod.fst)).bind (fun o =>
      match o with
      | none => PMF.pure none
      | some (l', μ_C) =>
        if h : R (simLastState E).1 (simLastState E).2 ∧
            sys_C.step (simLastState E).1 l' μ_C then
          PMF.pure (some (l', simCouple sim (simLastState E) l' μ_C))
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
      by_cases hg : R (simLastState E).1 (simLastState E).2 ∧
          sys_C.step (simLastState E).1 l' μ_C
      · rw [dif_pos hg, PMF.mem_support_pure_iff] at h_supp
        rw [Option.some.injEq, Prod.mk.injEq] at h_supp
        obtain ⟨rfl, rfl⟩ := h_supp
        rw [h_last] at hg ⊢
        exact simCouple_step sim s l μ_C hg
      · rw [dif_neg hg, PMF.mem_support_pure_iff] at h_supp
        exact absurd h_supp (by simp)

/-- The joint probabilistic execution: Dirac on the joint initial state, driven
by the joint scheduler. -/
noncomputable def simJointExec
    (pe_C : ProbabilisticExecution sys_C)
    (sim : StrongProbabilisticSimulation sys_C sys_A R) :
    ProbabilisticExecution (simProd sys_C sys_A R) where
  initState := PMF.pure (simProd sys_C sys_A R).init
  scheduler := simJointSched pe_C sim

/-- Membership of `some (l, ω)` in `simJointSched.next E`'s support forces the
guard at `simLastState E` and identifies `ω` as the coupling. -/
theorem simJointSched_next_support
    (pe_C : ProbabilisticExecution sys_C)
    (sim : StrongProbabilisticSimulation sys_C sys_A R)
    (E : AlterSeq (State_C × State_A) Label) (l : Label) (ω : PMF (State_C × State_A))
    (h_supp : some (l, ω) ∈ ((simJointSched pe_C sim).next E).support) :
    ∃ μ_C, R (simLastState E).1 (simLastState E).2 ∧
      sys_C.step (simLastState E).1 l μ_C ∧
      ω = simCouple sim (simLastState E) l μ_C := by
  classical
  change some (l, ω) ∈ ((pe_C.scheduler.next (E.map Prod.fst)).bind (fun o =>
    match o with
    | none => PMF.pure none
    | some (l', μ_C) =>
      if h : R (simLastState E).1 (simLastState E).2 ∧
          sys_C.step (simLastState E).1 l' μ_C then
        PMF.pure (some (l', simCouple sim (simLastState E) l' μ_C))
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
    by_cases hg : R (simLastState E).1 (simLastState E).2 ∧
        sys_C.step (simLastState E).1 l' μ_C
    · rw [dif_pos hg, PMF.mem_support_pure_iff] at h_supp
      rw [Option.some.injEq, Prod.mk.injEq] at h_supp
      obtain ⟨rfl, rfl⟩ := h_supp
      exact ⟨μ_C, hg.1, hg.2, rfl⟩
    · rw [dif_neg hg, PMF.mem_support_pure_iff] at h_supp
      exact absurd h_supp (by simp)

/-- **R-invariant** (over `Seq.ofList`-form histories). -/
private theorem simJointExec_probOf_R_ofList
    (pe_C : ProbabilisticExecution sys_C)
    (sim : StrongProbabilisticSimulation sys_C sys_A R)
    (L : List (Label × (State_C × State_A))) (s₀ : State_C × State_A)
    (hFin : (Seq.ofList L : Seq (Label × (State_C × State_A))).Terminates)
    (hne : (simJointExec pe_C sim).probOf ⟨s₀, Seq.ofList L⟩ hFin ≠ 0) :
    R ((⟨s₀, Seq.ofList L⟩ : AlterSeq (State_C × State_A) Label).endState hFin).1
      ((⟨s₀, Seq.ofList L⟩ : AlterSeq (State_C × State_A) Label).endState hFin).2 := by
  classical
  induction L using List.reverseRecOn generalizing s₀ with
  | nil =>
    rw [AlterSeq.endState_of_trans_nil _ (by rw [Stream'.Seq.ofList_nil]) hFin]
    rw [ProbabilisticExecution.probOf_congr (simJointExec pe_C sim)
      ⟨s₀, Seq.ofList []⟩ ⟨s₀, Seq.nil⟩ (by rw [Stream'.Seq.ofList_nil]) hFin
      Stream'.Seq.terminates_nil, ProbabilisticExecution.probOf_nil] at hne
    change (PMF.pure (simProd sys_C sys_A R).init) s₀ ≠ 0 at hne
    rw [PMF.pure_apply] at hne
    have : s₀ = (simProd sys_C sys_A R).init := by
      by_contra hc; rw [if_neg hc] at hne; exact hne rfl
    rw [this]; exact sim.init
  | append_singleton rest last ih =>
    -- ofList (rest ++ [last]) = (ofList rest).append (cons last nil).
    have hsplit : (Seq.ofList (rest ++ [last]) : Seq (Label × (State_C × State_A)))
        = (Seq.ofList rest).append (Seq.cons last Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have hrest_fin : (Seq.ofList rest : Seq (Label × (State_C × State_A))).Terminates :=
      Stream'.Seq.terminates_ofList _
    have hFinS : ((Seq.ofList rest).append (Seq.cons last Seq.nil)).Terminates := by
      rw [← hsplit]; exact hFin
    -- factor probOf at the append.
    rw [ProbabilisticExecution.probOf_congr (simJointExec pe_C sim)
      ⟨s₀, Seq.ofList (rest ++ [last])⟩ ⟨s₀, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩
      (by rw [hsplit]) hFin hFinS,
      ProbabilisticExecution.probOf_append_singleton (simJointExec pe_C sim) s₀
        (Seq.ofList rest) hrest_fin last hFinS] at hne
    have hker : (simJointExec pe_C sim).kernel ⟨s₀, Seq.ofList rest⟩ last ≠ 0 :=
      fun h0 => hne (by rw [h0, mul_zero])
    -- kernel ≠ 0 ⟹ ∃ ω with σ.next (some(last.1,ω)) ≠ 0 and ω last.2 ≠ 0.
    rw [ProbabilisticExecution.kernel] at hker
    have hex := mt ENNReal.tsum_eq_zero.mpr hker
    push Not at hex
    obtain ⟨ω, hω⟩ := hex
    have hnext_ne : (simJointExec pe_C sim).scheduler.next ⟨s₀, Seq.ofList rest⟩
        (some (last.1, ω)) ≠ 0 := fun h0 => hω (by rw [h0, zero_mul])
    have hωlast : ω last.2 ≠ 0 := fun h0 => hω (by rw [h0, mul_zero])
    -- from the support, identify ω as a coupling and use its support ⊆ R.
    obtain ⟨μ_C, hRpre, _hstep, hωeq⟩ := simJointSched_next_support pe_C sim
      ⟨s₀, Seq.ofList rest⟩ last.1 ω ((PMF.mem_support_iff _ _).mpr hnext_ne)
    -- endState of the append is last.2.
    have hend : (⟨s₀, Seq.ofList (rest ++ [last])⟩ : AlterSeq (State_C × State_A) Label).endState
        hFin = last.2 := by
      rw [AlterSeq.endState_congr_pub
        (show (⟨s₀, Seq.ofList (rest ++ [last])⟩ : AlterSeq (State_C × State_A) Label)
          = ⟨s₀, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩ from by rw [hsplit]) hFin hFinS]
      obtain ⟨ll, qq⟩ := last
      exact AlterSeq.endState_append_singleton ⟨s₀, Seq.ofList rest⟩ hrest_fin ll qq
    rw [hend]
    -- last.2 ∈ ω.support ⊆ R.
    have hqsupp : last.2 ∈ ω.support := (PMF.mem_support_iff _ _).mpr hωlast
    rw [hωeq] at hqsupp
    exact (simCouple_step sim (simLastState ⟨s₀, Seq.ofList rest⟩) last.1 μ_C
      ⟨hRpre, _hstep⟩).2.2 last.2 hqsupp

/-- **R-invariant.** Every joint history with positive `simJointExec`-probability
ends in an `R`-related pair. -/
theorem simJointExec_probOf_R
    (pe_C : ProbabilisticExecution sys_C)
    (sim : StrongProbabilisticSimulation sys_C sys_A R)
    (E : AlterSeq (State_C × State_A) Label) (hT : E.trans.Terminates)
    (hne : (simJointExec pe_C sim).probOf E hT ≠ 0) :
    R (E.endState hT).1 (E.endState hT).2 := by
  classical
  have hofl : (Seq.ofList (E.trans.toList hT) : Seq (Label × (State_C × State_A))) = E.trans :=
    Stream'.Seq.ofList_toList E.trans hT
  have hFin' : (Seq.ofList (E.trans.toList hT) :
      Seq (Label × (State_C × State_A))).Terminates := by rw [hofl]; exact hT
  have heq :
    (⟨E.init, Seq.ofList (E.trans.toList hT)⟩ : AlterSeq (State_C × State_A) Label) = E := by
    cases E; simp only [hofl]
  rw [AlterSeq.endState_congr_pub heq.symm hT hFin']
  refine simJointExec_probOf_R_ofList pe_C sim (E.trans.toList hT) E.init hFin' ?_
  rw [ProbabilisticExecution.probOf_congr (simJointExec pe_C sim) _ E heq hFin' hT]
  exact hne

/-- Summing a joint PMF over the second component recovers the first marginal. -/
private theorem simSumA_eq_mapFst (ω : PMF (State_C × State_A)) (s_C' : State_C) :
    (∑' s_A' : State_A, ω (s_C', s_A')) = (ω.map Prod.fst) s_C' := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod (f := fun a b => if s_C' = a then ω (a, b) else 0)]
  rw [tsum_eq_single s_C' (fun b hb => by
    refine ENNReal.tsum_eq_zero.mpr (fun b_1 => ?_); rw [if_neg (Ne.symm hb)])]
  exact tsum_congr (fun b => by rw [if_pos rfl])

/-- `AlterSeq.map` commutes with `endState`: projecting an execution and taking
its end-state equals projecting the end-state. -/
private theorem AlterSeq.map_endState (f : State_C → State_A) (e : AlterSeq State_C Label)
    (h : e.trans.Terminates) :
    (e.map f).endState ((AlterSeq.map_trans_terminates_iff f e).mpr h) = f (e.endState h) := by
  rw [AlterSeq.endState_eq_getLast?, AlterSeq.endState_eq_getLast?]
  have h_toList : (e.map f).trans.toList ((AlterSeq.map_trans_terminates_iff f e).mpr h)
      = (e.trans.toList h).map (fun lq => (lq.1, f lq.2)) := by
    change (e.trans.map (fun lq => (lq.1, f lq.2))).toList _ = _
    apply Stream'.Seq.ofList_injective
    rw [Stream'.Seq.ofList_toList _ _, ← Stream'.Seq.map_ofList_pub, Stream'.Seq.ofList_toList _ h]
  rw [h_toList, List.getLast?_map]
  cases (e.trans.toList h).getLast? with
  | none => rfl
  | some lq => rfl

open Classical in
/-- The algebraic collapse at the heart of the kernel marginal: summing the
coupling-emission weights over `(l', μ_C)` and joint successors `ω`, weighted by
the first marginal, recovers the concrete kernel (the R-guard always holds on the
support of `pe_C.next` by validity, and `simCouple`'s first marginal is `μ_C`). -/
private theorem simKernelCollapse (pe_C : ProbabilisticExecution sys_C)
    (sim : StrongProbabilisticSimulation sys_C sys_A R)
    (E : AlterSeq (State_C × State_A) Label) (l : Label) (s_C' : State_C)
    (hR : R (simLastState E).1 (simLastState E).2)
    (hvalid : ∀ μ_C : PMF State_C,
      pe_C.scheduler.next (E.map Prod.fst) (some (l, μ_C)) ≠ 0 →
      sys_C.step (simLastState E).1 l μ_C)
    (hcpl : ∀ μ_C : PMF State_C, R (simLastState E).1 (simLastState E).2 ∧
        sys_C.step (simLastState E).1 l μ_C →
        (simCouple sim (simLastState E) l μ_C).map Prod.fst = μ_C) :
    (∑' (y : Label × PMF State_C) (ω : PMF (State_C × State_A)),
          (pe_C.scheduler.next (E.map Prod.fst)) (some y) *
            ((if _ : R (simLastState E).1 (simLastState E).2 ∧
                sys_C.step (simLastState E).1 y.1 y.2 then
              PMF.pure (some (y.1, simCouple sim (simLastState E) y.1 y.2))
            else PMF.pure none) : PMF (Option (Label × PMF (State_C × State_A)))) (some (l, ω))
            * (ω.map Prod.fst) s_C')
      = pe_C.kernel (E.map Prod.fst) (l, s_C') := by
  classical
  set F : Label × PMF State_C → ENNReal := fun y =>
    ∑' (ω : PMF (State_C × State_A)),
          (pe_C.scheduler.next (E.map Prod.fst)) (some y) *
            ((if h : R (simLastState E).1 (simLastState E).2 ∧
                sys_C.step (simLastState E).1 y.1 y.2 then
              PMF.pure (some (y.1, simCouple sim (simLastState E) y.1 y.2))
            else PMF.pure none) : PMF (Option (Label × PMF (State_C × State_A)))) (some (l, ω))
            * (ω.map Prod.fst) s_C' with hF
  change (∑' y, F y) = _
  rw [← Function.Injective.tsum_eq (g := fun μ_C : PMF State_C => (l, μ_C))
    (fun a b hab => (Prod.mk.injEq ..).mp hab |>.2) (f := F) ?_]
  · change _ = ∑' μ_C, pe_C.scheduler.next (E.map Prod.fst) (some (l, μ_C)) * μ_C s_C'
    refine tsum_congr (fun μ_C => ?_)
    have hFval : F (l, μ_C) = ∑' (ω : PMF (State_C × State_A)),
          (pe_C.scheduler.next (E.map Prod.fst)) (some (l, μ_C)) *
            ((if h : R (simLastState E).1 (simLastState E).2 ∧
                sys_C.step (simLastState E).1 l μ_C then
              PMF.pure (some (l, simCouple sim (simLastState E) l μ_C))
            else PMF.pure none) : PMF (Option (Label × PMF (State_C × State_A)))) (some (l, ω))
            * (ω.map Prod.fst) s_C' := by rw [hF]
    rw [hFval]
    by_cases hg : R (simLastState E).1 (simLastState E).2 ∧
        sys_C.step (simLastState E).1 l μ_C
    · rw [show (fun (ω : PMF (State_C × State_A)) =>
            (pe_C.scheduler.next (E.map Prod.fst)) (some (l, μ_C)) *
              ((if h : R (simLastState E).1 (simLastState E).2 ∧
                  sys_C.step (simLastState E).1 l μ_C then
                PMF.pure (some (l, simCouple sim (simLastState E) l μ_C))
              else PMF.pure none) : PMF (Option (Label × PMF (State_C × State_A)))) (some (l, ω))
              * (ω.map Prod.fst) s_C')
          = (fun ω => (pe_C.scheduler.next (E.map Prod.fst)) (some (l, μ_C)) *
              (((if h : R (simLastState E).1 (simLastState E).2 ∧
                  sys_C.step (simLastState E).1 l μ_C then
                PMF.pure (some (l, simCouple sim (simLastState E) l μ_C))
              else PMF.pure none) : PMF (Option (Label × PMF (State_C × State_A)))) (some (l, ω))
              * (ω.map Prod.fst) s_C')) from funext (fun ω => by ring)]
      rw [ENNReal.tsum_mul_left]
      congr 1
      rw [show (∑' ω : PMF (State_C × State_A),
            ((if h : R (simLastState E).1 (simLastState E).2 ∧
                sys_C.step (simLastState E).1 l μ_C then
              PMF.pure (some (l, simCouple sim (simLastState E) l μ_C))
            else PMF.pure none) : PMF (Option (Label × PMF (State_C × State_A)))) (some (l, ω))
            * (ω.map Prod.fst) s_C')
          = ((simCouple sim (simLastState E) l μ_C).map Prod.fst) s_C' from by
        refine (tsum_eq_single (simCouple sim (simLastState E) l μ_C) ?_).trans ?_
        · intro ω hω
          rw [dif_pos hg, PMF.pure_apply_of_ne (some (l, simCouple sim (simLastState E) l μ_C))
            (some (l, ω)) (fun hc => hω ((Prod.mk.injEq ..).mp ((Option.some.injEq ..).mp hc)).2),
            zero_mul]
        · rw [dif_pos hg, PMF.pure_apply_self, one_mul]]
      rw [hcpl μ_C hg]
    · have hzero : pe_C.scheduler.next (E.map Prod.fst) (some (l, μ_C)) = 0 := by
        by_contra hne; exact hg ⟨hR, hvalid μ_C hne⟩
      rw [hzero, zero_mul]
      refine (ENNReal.tsum_eq_zero.mpr (fun ω => ?_))
      rw [zero_mul, zero_mul]
  · intro y hy
    rw [Function.mem_support] at hy
    refine ⟨y.2, ?_⟩
    by_contra hc
    apply hy
    have hFy : F y = ∑' (ω : PMF (State_C × State_A)),
          (pe_C.scheduler.next (E.map Prod.fst)) (some y) *
            ((if h : R (simLastState E).1 (simLastState E).2 ∧
                sys_C.step (simLastState E).1 y.1 y.2 then
              PMF.pure (some (y.1, simCouple sim (simLastState E) y.1 y.2))
            else PMF.pure none) : PMF (Option (Label × PMF (State_C × State_A)))) (some (l, ω))
            * (ω.map Prod.fst) s_C' := by rw [hF]
    rw [hFy]
    refine ENNReal.tsum_eq_zero.mpr (fun ω => ?_)
    by_cases hg : R (simLastState E).1 (simLastState E).2 ∧
        sys_C.step (simLastState E).1 y.1 y.2
    · rw [dif_pos hg, PMF.pure_apply_of_ne (some (y.1, simCouple sim (simLastState E) y.1 y.2))
        (some (l, ω)) (fun hc' => hc (by
          rw [((Prod.mk.injEq ..).mp ((Option.some.injEq ..).mp hc')).1])),
        mul_zero, zero_mul]
    · rw [dif_neg hg, PMF.pure_apply_of_ne none (some (l, ω)) (by simp), mul_zero, zero_mul]

/-- **Kernel marginal.** Summing the joint one-step kernel over the abstract
successor recovers the concrete one-step kernel of the projected history (needs
the `R`-invariant `hR` at the current joint state). -/
private theorem simKernelMarginal (pe_C : ProbabilisticExecution sys_C)
    (sim : StrongProbabilisticSimulation sys_C sys_A R)
    (E : AlterSeq (State_C × State_A) Label) (hT : E.trans.Terminates)
    (hR : R (simLastState E).1 (simLastState E).2)
    (l : Label) (s_C' : State_C) :
    (∑' s_A' : State_A, (simJointExec pe_C sim).kernel E (l, (s_C', s_A')))
      = pe_C.kernel (E.map Prod.fst) (l, s_C') := by
  classical
  have hC_term : (E.map Prod.fst).trans.Terminates := (AlterSeq.map_trans_terminates_iff _ _).mpr hT
  have hlast1 : (simLastState E).1 = (E.map Prod.fst).endState hC_term := by
    rw [simLastState, dif_pos hT, AlterSeq.map_endState Prod.fst E hT]
  have hvalid : ∀ μ_C : PMF State_C,
      pe_C.scheduler.next (E.map Prod.fst) (some (l, μ_C)) ≠ 0 →
      sys_C.step (simLastState E).1 l μ_C := by
    intro μ_C hne
    rw [hlast1]
    exact pe_C.scheduler.valid (E.map Prod.fst) (Nat.find hC_term)
      ((E.map Prod.fst).endState hC_term) (Nat.find_spec hC_term)
      (AlterSeq.stateAt_find_eq_endState _ hC_term) l μ_C ((PMF.mem_support_iff _ _).mpr hne)
  -- step 1: marginalise the abstract successor into the first marginal of ω.
  rw [show (∑' s_A' : State_A, (simJointExec pe_C sim).kernel E (l, (s_C', s_A')))
      = ∑' ω : PMF (State_C × State_A),
          (simJointExec pe_C sim).scheduler.next E (some (l, ω)) * (ω.map Prod.fst) s_C' from by
    change (∑' s_A', ∑' ω, _) = _
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun ω => ?_)
    rw [← simSumA_eq_mapFst ω s_C', ← ENNReal.tsum_mul_left]]
  -- step 2: expand the joint scheduler's emission weight (bind + match reduction).
  rw [show (∑' ω : PMF (State_C × State_A),
          (simJointExec pe_C sim).scheduler.next E (some (l, ω)) * (ω.map Prod.fst) s_C')
      = ∑' (y : Label × PMF State_C) (ω : PMF (State_C × State_A)),
          (pe_C.scheduler.next (E.map Prod.fst)) (some y) *
            ((if h : R (simLastState E).1 (simLastState E).2 ∧
                sys_C.step (simLastState E).1 y.1 y.2 then
              PMF.pure (some (y.1, simCouple sim (simLastState E) y.1 y.2))
            else PMF.pure none) : PMF (Option (Label × PMF (State_C × State_A)))) (some (l, ω))
            * (ω.map Prod.fst) s_C' from by
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun ω => ?_)
    rw [ENNReal.tsum_mul_right]
    congr 1
    change ((pe_C.scheduler.next (E.map Prod.fst)).bind _) (some (l, ω)) = _
    rw [PMF.bind_apply, ENNReal.tsum_option']
    rw [show (pe_C.scheduler.next (E.map Prod.fst)) none *
        (PMF.pure none : PMF (Option (Label × PMF (State_C × State_A)))) (some (l, ω)) = 0 from by
      rw [PMF.pure_apply_of_ne none (some (l, ω)) (by simp), mul_zero], zero_add]]
  exact simKernelCollapse pe_C sim E l s_C' hR hvalid
    (fun μ_C hg => simCouple_map_fst sim (simLastState E) l μ_C hg)

open Classical in
/-- **Append reindex for the marginal.** A joint execution projecting to
`⟨i_C, (ofList rest).append [(l,s_C')]⟩` is exactly the append, by a free abstract
component `s_A'`, of a joint prefix projecting to `⟨i_C, ofList rest⟩`. -/
private theorem simExecMarginal_reindex (pe_C : ProbabilisticExecution sys_C)
    (sim : StrongProbabilisticSimulation sys_C sys_A R)
    (i_C : State_C) (rest : List (Label × State_C)) (l : Label) (s_C' : State_C) :
    (∑' E : AlterSeq (State_C × State_A) Label,
        dite (E.trans.Terminates ∧ E.map Prod.fst
            = ⟨i_C, (Seq.ofList rest).append (Seq.cons (l, s_C') Seq.nil)⟩)
          (fun h => (simJointExec pe_C sim).probOf E h.1) (fun _ => 0))
      = ∑' (p : AlterSeq (State_C × State_A) Label × State_A),
          dite (p.1.trans.Terminates ∧ p.1.map Prod.fst = ⟨i_C, Seq.ofList rest⟩)
            (fun h => (simJointExec pe_C sim).probOf
              ⟨p.1.init, p.1.trans.append (Seq.cons (l, (s_C', p.2)) Seq.nil)⟩
              ⟨_, Stream'.Seq.terminatedAt_append_find h.1
                  (show (Seq.cons (l, (s_C', p.2)) Seq.nil).TerminatedAt 1 from rfl)⟩)
            (fun _ => 0) := by
  classical
  refine (tsum_eq_tsum_of_ne_zero_bij
    (i := fun x =>
      (⟨x.1.1.init, x.1.1.trans.append (Seq.cons (l, (s_C', x.1.2)) Seq.nil)⟩
        : AlterSeq (State_C × State_A) Label))
    ?hinj ?hf ?hfg)
  case hinj =>
    rintro ⟨⟨E1, a1⟩, hE1⟩ ⟨⟨E2, a2⟩, hE2⟩ hab
    rw [Function.mem_support] at hE1 hE2
    have hT1 : E1.trans.Terminates := by
      by_contra hc; exact hE1 (dif_neg (fun h => hc h.1))
    have hT2 : E2.trans.Terminates := by
      by_contra hc; exact hE2 (dif_neg (fun h => hc h.1))
    simp only at hab
    have hinit : E1.init = E2.init := congr_arg (·.init) hab
    have htrans : E1.trans.append (Seq.cons (l, (s_C', a1)) Seq.nil)
        = E2.trans.append (Seq.cons (l, (s_C', a2)) Seq.nil) := congr_arg (·.trans) hab
    have hE12 : E1.trans = E2.trans :=
      Stream'.Seq.append_singleton_inj_left _ _ hT1 hT2 _ _ htrans
    have ha12 : a1 = a2 := by
      have he1 := AlterSeq.endState_append_singleton E1 hT1 l (s_C', a1)
      have he2 := AlterSeq.endState_append_singleton E2 hT2 l (s_C', a2)
      have heq := AlterSeq.endState_congr_pub hab
        ⟨_, Stream'.Seq.terminatedAt_append_find hT1
          (show (Seq.cons (l, (s_C', a1)) Seq.nil).TerminatedAt 1 from rfl)⟩
        ⟨_, Stream'.Seq.terminatedAt_append_find hT2
          (show (Seq.cons (l, (s_C', a2)) Seq.nil).TerminatedAt 1 from rfl)⟩
      rw [he1, he2] at heq
      exact (Prod.mk.injEq .. ▸ heq).2
    have hEE : E1 = E2 := by
      cases E1; cases E2; simp only at hinit hE12; subst hinit; subst hE12; rfl
    subst hEE; subst ha12; rfl
  case hf =>
    intro E hE
    rw [Function.mem_support] at hE
    have hc : E.trans.Terminates ∧ E.map Prod.fst
        = ⟨i_C, (Seq.ofList rest).append (Seq.cons (l, s_C') Seq.nil)⟩ := by
      by_contra hcon; exact hE (dif_neg hcon)
    obtain ⟨hT, hmap⟩ := hc
    have htrans_proj : E.trans.map (fun lq => (lq.1, lq.2.1))
        = (Seq.ofList rest).append (Seq.cons (l, s_C') Seq.nil) := congr_arg (·.trans) hmap
    have hne : E.trans.toList hT ≠ [] := by
      intro hnil
      have hlen : E.trans.length' = 0 := by
        rw [Stream'.Seq.length'_of_terminates hT]
        have := Stream'.Seq.length_toList E.trans hT
        rw [hnil, List.length_nil] at this; simp [← this]
      have hmaplen : (E.trans.map
          (fun lq : Label × (State_C × State_A) => (lq.1, lq.2.1))).length' = 0 := by
        rw [Stream'.Seq.length'_map]; exact hlen
      rw [htrans_proj, Stream'.Seq.append_singleton_length'] at hmaplen
      exact absurd (by exact_mod_cast hmaplen : rest.length + 1 = 0) (Nat.succ_ne_zero _)
    obtain ⟨previous, last, h_prev, h_split, _, _⟩ :=
      Stream'.Seq.exists_split_last E.trans hT hne
    rw [h_split, Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil]
      at htrans_proj
    have hpm : (previous.map (fun lq : Label × (State_C × State_A) => (lq.1, lq.2.1))).Terminates :=
      Stream'.Seq.terminates_map_iff.mpr h_prev
    have hprevmap : previous.map (fun lq : Label × (State_C × State_A) => (lq.1, lq.2.1))
        = Seq.ofList rest :=
      Stream'.Seq.append_singleton_inj_left _ _ hpm (Stream'.Seq.terminates_ofList rest) _ _
        htrans_proj
    -- boundary element: (last.1, last.2.1) = (l, s_C')
    have hpm_min : ∀ k < rest.length,
        ¬ (previous.map (fun lq : Label × (State_C × State_A) =>
        (lq.1, lq.2.1))).TerminatedAt k := by
      intro k hk hterm
      rw [hprevmap, show (Seq.ofList rest).TerminatedAt k ↔ (Seq.ofList rest).get? k = none
        from Iff.rfl, Stream'.Seq.ofList_get?] at hterm
      exact absurd hterm (by rw [List.getElem?_eq_getElem hk]; exact Option.some_ne_none _)
    have hpm_done :
      (previous.map (fun lq : Label × (State_C × State_A) =>
      (lq.1, lq.2.1))).TerminatedAt rest.length := by
      rw [hprevmap]; exact Stream'.Seq.terminatedAt_ofList rest
    have h_rmin : ∀ k < rest.length,
      ¬ (Seq.ofList rest : Seq (Label × State_C)).TerminatedAt k := by
      intro k hk hterm
      rw [show (Seq.ofList rest).TerminatedAt k ↔ (Seq.ofList rest).get? k = none from Iff.rfl,
        Stream'.Seq.ofList_get?] at hterm
      exact absurd hterm (by rw [List.getElem?_eq_getElem hk]; exact Option.some_ne_none _)
    have hbound : (last.1, last.2.1) = (l, s_C') := by
      have h_lhs := Stream'.Seq.get?_append_after_length
        (s' := Seq.cons (last.1, last.2.1) Seq.nil) hpm_min hpm_done 0
      rw [Nat.add_zero] at h_lhs
      have h_rhs := Stream'.Seq.get?_append_after_length
        (s' := Seq.cons (l, s_C') Seq.nil) h_rmin (Stream'.Seq.terminatedAt_ofList rest) 0
      rw [Nat.add_zero] at h_rhs
      rw [htrans_proj] at h_lhs
      rw [h_rhs, Stream'.Seq.get?_cons_zero] at h_lhs
      rw [Stream'.Seq.get?_cons_zero] at h_lhs
      exact (Option.some.inj h_lhs).symm
    obtain ⟨hl', hsc'⟩ := Prod.mk.injEq .. ▸ hbound
    have hlasteq : last = (l, (s_C', last.2.2)) := by
      obtain ⟨ll, sc, sa⟩ := last; simp only at hl' hsc' ⊢; rw [hl', hsc']
    -- probOf_J E ≠ 0 (the dite was positive)
    have hprobE : (simJointExec pe_C sim).probOf E hT ≠ 0 := by
      intro h0; exact hE (by rw [dif_pos ⟨hT, hmap⟩, h0])
    -- the prefix execution ⟨E.init, previous⟩ projects to ⟨i_C, ofList rest⟩
    have hprevproj : (⟨E.init, previous⟩ : AlterSeq (State_C × State_A) Label).map Prod.fst
        = ⟨i_C, Seq.ofList rest⟩ := by
      have hinitC : E.init.1 = i_C := congr_arg (·.init) hmap
      change (⟨E.init.1, previous.map (fun lq => (lq.1, lq.2.1))⟩ : AlterSeq State_C Label)
        = ⟨i_C, Seq.ofList rest⟩
      rw [hprevmap, hinitC]
    -- the support membership: g (⟨E.init,previous⟩, last.2.2) ≠ 0
    have hsupp_ne : dite ((⟨E.init, previous⟩ : AlterSeq (State_C × State_A) Label).trans.Terminates
          ∧ (⟨E.init, previous⟩ : AlterSeq (State_C × State_A) Label).map Prod.fst
            = ⟨i_C, Seq.ofList rest⟩)
        (fun h => (simJointExec pe_C sim).probOf
          ⟨(⟨E.init, previous⟩ : AlterSeq (State_C × State_A) Label).init,
            (⟨E.init, previous⟩ : AlterSeq (State_C × State_A) Label).trans.append
              (Seq.cons (l, (s_C', last.2.2)) Seq.nil)⟩
          ⟨_, Stream'.Seq.terminatedAt_append_find h.1
              (show (Seq.cons (l, (s_C', last.2.2)) Seq.nil).TerminatedAt 1 from rfl)⟩)
        (fun _ => 0) ≠ 0 := by
      rw [dif_pos ⟨h_prev, hprevproj⟩]
      -- this probOf equals probOf_J E
      have hEeq : (⟨(⟨E.init, previous⟩ : AlterSeq (State_C × State_A) Label).init,
            previous.append (Seq.cons (l, (s_C', last.2.2)) Seq.nil)⟩
            : AlterSeq (State_C × State_A) Label) = E := by
        cases E; simp only at h_split ⊢; rw [h_split, hlasteq]
      rw [ProbabilisticExecution.probOf_congr (simJointExec pe_C sim) _ E hEeq _ hT]
      exact hprobE
    refine ⟨⟨(⟨E.init, previous⟩, last.2.2), hsupp_ne⟩, ?_⟩
    change (⟨(⟨E.init, previous⟩ : AlterSeq (State_C × State_A) Label).init,
        previous.append (Seq.cons (l, (s_C', last.2.2)) Seq.nil)⟩
        : AlterSeq (State_C × State_A) Label) = E
    cases E; simp only at h_split ⊢; rw [h_split, hlasteq]
  case hfg =>
    rintro ⟨⟨E1, a1⟩, hmem⟩
    rw [Function.mem_support] at hmem
    have hg : E1.trans.Terminates ∧ E1.map Prod.fst = ⟨i_C, Seq.ofList rest⟩ := by
      by_contra hc; exact hmem (dif_neg hc)
    change dite _ _ _ = dite _ _ _
    have hcondF : (⟨E1.init, E1.trans.append (Seq.cons (l, (s_C', a1)) Seq.nil)⟩
                : AlterSeq (State_C × State_A) Label).trans.Terminates ∧
              (⟨E1.init, E1.trans.append (Seq.cons (l, (s_C', a1)) Seq.nil)⟩
                : AlterSeq (State_C × State_A) Label).map Prod.fst
              = ⟨i_C, (Seq.ofList rest).append (Seq.cons (l, s_C') Seq.nil)⟩ :=
      ⟨⟨_, Stream'.Seq.terminatedAt_append_find hg.1
          (show (Seq.cons (l, (s_C', a1)) Seq.nil).TerminatedAt 1 from rfl)⟩,
        by rw [AlterSeq.map_append_singleton Prod.fst E1 l (s_C', a1), hg.2]⟩
    rw [dif_pos hcondF, dif_pos hg]

open Classical in
/-- **Execution marginal.** Summing the joint execution probability over all
joint histories projecting (via `Prod.fst`) to a fixed concrete history `e_C`
recovers `pe_C.probOf e_C`. Proved by `reverseRecOn` on `e_C`'s transition list:
the append step reindexes the joint fibre as a prefix fibre paired with a free
abstract successor, then collapses that successor via `simKernelMarginal`. -/
theorem simExecMarginal (pe_C : ProbabilisticExecution sys_C)
    (sim : StrongProbabilisticSimulation sys_C sys_A R)
    (h_init : pe_C.initState = PMF.pure sys_C.init)
    (L_C : List (Label × State_C)) (i_C : State_C) :
    (∑' E : AlterSeq (State_C × State_A) Label,
        dite (E.trans.Terminates ∧ E.map Prod.fst = ⟨i_C, Seq.ofList L_C⟩)
          (fun h => (simJointExec pe_C sim).probOf E h.1) (fun _ => 0))
      = pe_C.probOf ⟨i_C, Seq.ofList L_C⟩ (Stream'.Seq.terminates_ofList L_C) := by
  induction L_C using List.reverseRecOn generalizing i_C with
  | nil =>
    classical
    rw [ProbabilisticExecution.probOf_congr pe_C ⟨i_C, Seq.ofList []⟩ ⟨i_C, Seq.nil⟩
      (by rw [Stream'.Seq.ofList_nil]) (Stream'.Seq.terminates_ofList [])
      Stream'.Seq.terminates_nil]
    have hnil : (Seq.ofList ([] : List (Label × State_C))) = Seq.nil := Stream'.Seq.ofList_nil
    set G : AlterSeq (State_C × State_A) Label → ENNReal := fun E =>
      dite (E.trans.Terminates ∧ E.map Prod.fst = ⟨i_C, Seq.nil⟩)
        (fun h => (simJointExec pe_C sim).probOf E h.1) (fun _ => 0) with hG
    rw [show (∑' E : AlterSeq (State_C × State_A) Label,
        dite (E.trans.Terminates ∧ E.map Prod.fst
            = ⟨i_C, Seq.ofList ([] : List (Label × State_C))⟩)
          (fun h => (simJointExec pe_C sim).probOf E h.1) (fun _ => 0)) = ∑' E, G E from by
      rw [hG]; exact tsum_congr (fun E => by rw [hnil])]
    have hsupp : Function.support G ⊆ Set.range (fun s_A : State_A =>
        (⟨(i_C, s_A), Seq.nil⟩ : AlterSeq (State_C × State_A) Label)) := by
      intro E hE
      rw [Function.mem_support] at hE
      by_cases hc : E.trans.Terminates ∧ E.map Prod.fst = ⟨i_C, Seq.nil⟩
      · obtain ⟨hT, hmap⟩ := hc
        have hinit : E.init.1 = i_C := congr_arg (·.init) hmap
        have htrans : E.trans.map (fun lq => (lq.1, lq.2.1)) = Seq.nil := congr_arg (·.trans) hmap
        have hEtrans : E.trans = Seq.nil := by
          have := congr_arg Stream'.Seq.length' htrans
          rw [Stream'.Seq.length'_map, Stream'.Seq.length'_nil] at this
          exact (Stream'.Seq.length'_eq_zero_iff_nil E.trans).mp this
        refine ⟨E.init.2, ?_⟩
        obtain ⟨ei, et⟩ := E
        simp only at hinit hEtrans
        subst hEtrans
        change (⟨(i_C, ei.2), Seq.nil⟩ : AlterSeq (State_C × State_A) Label) = ⟨ei, Seq.nil⟩
        rw [← hinit]
      · rw [hG] at hE; exact absurd (dif_neg hc) hE
    rw [← Function.Injective.tsum_eq (g := fun s_A : State_A =>
        (⟨(i_C, s_A), Seq.nil⟩ : AlterSeq (State_C × State_A) Label))
      (fun a b hab => by
        have := congr_arg (·.init) hab; simp only [Prod.mk.injEq] at this; exact this.2)
      (f := G) hsupp]
    have hGval : ∀ s_A : State_A, G (⟨(i_C, s_A), Seq.nil⟩ : AlterSeq (State_C × State_A) Label)
        = (simJointExec pe_C sim).probOf ⟨(i_C, s_A), Seq.nil⟩ Stream'.Seq.terminates_nil := by
      intro s_A
      simp only [hG]
      rw [dif_pos ⟨Stream'.Seq.terminates_nil, by
        change (⟨i_C, Stream'.Seq.map _ Seq.nil⟩ : AlterSeq State_C Label) = ⟨i_C, Seq.nil⟩
        rw [Stream'.Seq.map_nil]⟩]
    rw [tsum_congr hGval, ProbabilisticExecution.probOf_nil]
    have hJval : ∀ s_A : State_A, (simJointExec pe_C sim).probOf
        ⟨(i_C, s_A), Seq.nil⟩ Stream'.Seq.terminates_nil
        = (if (i_C, s_A) = ((sys_C.init, sys_A.init) : State_C × State_A)
            then (1 : ENNReal) else 0) := by
      intro s_A
      rw [ProbabilisticExecution.probOf_nil]
      change (PMF.pure (simProd sys_C sys_A R).init) (i_C, s_A) = _
      rw [PMF.pure_apply]
      congr 1
    rw [tsum_congr hJval]
    rw [show (∑' s_A : State_A, (if (i_C, s_A)
          = ((sys_C.init, sys_A.init) : State_C × State_A)
          then (1 : ENNReal) else 0))
        = (if i_C = sys_C.init then (1 : ENNReal) else 0) from by
      by_cases hia : i_C = sys_C.init
      · subst hia
        rw [tsum_eq_single sys_A.init
          (fun s_A hs => by rw [if_neg (by simp only [Prod.mk.injEq]; tauto)]),
          if_pos rfl, if_pos rfl]
      · rw [if_neg hia]
        refine ENNReal.tsum_eq_zero.mpr (fun s_A => ?_)
        rw [if_neg (by simp only [Prod.mk.injEq]; tauto)]]
    change _ = pe_C.initState i_C
    rw [h_init, PMF.pure_apply]
  | append_singleton rest last ih =>
    classical
    obtain ⟨l, s_C'⟩ := last
    have hsplit : (Seq.ofList (rest ++ [(l, s_C')]) : Seq (Label × State_C))
        = (Seq.ofList rest).append (Seq.cons (l, s_C') Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    rw [show (∑' E : AlterSeq (State_C × State_A) Label,
        dite (E.trans.Terminates ∧ E.map Prod.fst = ⟨i_C, Seq.ofList (rest ++ [(l, s_C')])⟩)
          (fun h => (simJointExec pe_C sim).probOf E h.1) (fun _ => 0))
      = ∑' E : AlterSeq (State_C × State_A) Label,
        dite (E.trans.Terminates ∧ E.map Prod.fst
            = ⟨i_C, (Seq.ofList rest).append (Seq.cons (l, s_C') Seq.nil)⟩)
          (fun h => (simJointExec pe_C sim).probOf E h.1) (fun _ => 0) from by rw [hsplit]]
    rw [simExecMarginal_reindex pe_C sim i_C rest l s_C']
    -- split the pair sum and factor probOf at the appended step.
    rw [ENNReal.tsum_prod']
    -- per-(E',s_A') term: name the joint condition and the append-termination proof.
    have hper : ∀ E' : AlterSeq (State_C × State_A) Label,
        (∑' s_A' : State_A,
          dite (E'.trans.Terminates ∧ E'.map Prod.fst = ⟨i_C, Seq.ofList rest⟩)
            (fun h => (simJointExec pe_C sim).probOf
              ⟨E'.init, E'.trans.append (Seq.cons (l, (s_C', s_A')) Seq.nil)⟩
              ⟨_, Stream'.Seq.terminatedAt_append_find h.1
                  (show (Seq.cons (l, (s_C', s_A')) Seq.nil).TerminatedAt 1 from rfl)⟩)
            (fun _ => 0))
        = dite (E'.trans.Terminates ∧ E'.map Prod.fst = ⟨i_C, Seq.ofList rest⟩)
            (fun h => (simJointExec pe_C sim).probOf E' h.1
              * pe_C.kernel ⟨i_C, Seq.ofList rest⟩ (l, s_C')) (fun _ => 0) := by
      intro E'
      by_cases hc : E'.trans.Terminates ∧ E'.map Prod.fst = ⟨i_C, Seq.ofList rest⟩
      · rw [tsum_congr (fun s_A' => dif_pos hc), dif_pos hc]
        rw [tsum_congr (fun s_A' => ProbabilisticExecution.probOf_append_singleton
            (simJointExec pe_C sim) E'.init E'.trans hc.1 (l, (s_C', s_A')) _),
          ENNReal.tsum_mul_left]
        by_cases hp : (simJointExec pe_C sim).probOf E' hc.1 = 0
        · rw [hp, zero_mul, zero_mul]
        · -- R-invariant at E' gives the kernel marginal; rewrite the projected init.
          have hR := simJointExec_probOf_R pe_C sim E' hc.1 hp
          have hlast : R (simLastState E').1 (simLastState E').2 := by
            rw [simLastState, dif_pos hc.1]; exact hR
          have hk : pe_C.kernel ⟨i_C, Seq.ofList rest⟩ (l, s_C')
              = pe_C.kernel (E'.map Prod.fst) (l, s_C') := by rw [hc.2]
          rw [simKernelMarginal pe_C sim E' hc.1 hlast l s_C', hk]
      · rw [tsum_congr (fun s_A' => dif_neg hc), tsum_zero, dif_neg hc]
    rw [tsum_congr hper]
    -- factor out the (constant) concrete kernel, apply IH, repackage the RHS.
    rw [show (∑' (E' : AlterSeq (State_C × State_A) Label),
            dite (E'.trans.Terminates ∧ E'.map Prod.fst = ⟨i_C, Seq.ofList rest⟩)
              (fun h => (simJointExec pe_C sim).probOf E' h.1
                * pe_C.kernel ⟨i_C, Seq.ofList rest⟩ (l, s_C')) (fun _ => 0))
        = (∑' (E' : AlterSeq (State_C × State_A) Label),
            dite (E'.trans.Terminates ∧ E'.map Prod.fst = ⟨i_C, Seq.ofList rest⟩)
              (fun h => (simJointExec pe_C sim).probOf E' h.1) (fun _ => 0))
          * pe_C.kernel ⟨i_C, Seq.ofList rest⟩ (l, s_C') from by
      rw [show (∑' (E' : AlterSeq (State_C × State_A) Label),
            dite (E'.trans.Terminates ∧ E'.map Prod.fst = ⟨i_C, Seq.ofList rest⟩)
              (fun h => (simJointExec pe_C sim).probOf E' h.1
                * pe_C.kernel ⟨i_C, Seq.ofList rest⟩ (l, s_C')) (fun _ => 0))
          = ∑' (E' : AlterSeq (State_C × State_A) Label),
            (dite (E'.trans.Terminates ∧ E'.map Prod.fst = ⟨i_C, Seq.ofList rest⟩)
              (fun h => (simJointExec pe_C sim).probOf E' h.1) (fun _ => 0))
              * pe_C.kernel ⟨i_C, Seq.ofList rest⟩ (l, s_C') from by
        refine tsum_congr (fun E' => ?_)
        by_cases hc : E'.trans.Terminates ∧ E'.map Prod.fst = ⟨i_C, Seq.ofList rest⟩
        · rw [dif_pos hc, dif_pos hc]
        · rw [dif_neg hc, dif_neg hc, zero_mul]]
      rw [ENNReal.tsum_mul_right]]
    rw [ih i_C]
    rw [ProbabilisticExecution.probOf_congr pe_C ⟨i_C, Seq.ofList (rest ++ [(l, s_C')])⟩
      ⟨i_C, (Seq.ofList rest).append (Seq.cons (l, s_C') Seq.nil)⟩ (by rw [hsplit])
      (Stream'.Seq.terminates_ofList _) (by rw [← hsplit]; exact Stream'.Seq.terminates_ofList _),
      ProbabilisticExecution.probOf_append_singleton pe_C i_C (Seq.ofList rest)
      (Stream'.Seq.terminates_ofList rest) (l, s_C')]

open Classical in
/-- **Per-projection-fibre marginal.** Within the joint histories that map (via
`Prod.fst`) to a fixed concrete history `e_C`, the label-list-restricted joint
sum equals the corresponding `Prod.fst`-fibre constraint of the joint sum. -/
private theorem simPerEC (pe_C : ProbabilisticExecution sys_C)
    (sim : StrongProbabilisticSimulation sys_C sys_A R)
    (labs : List Label) (e_C : AlterSeq State_C Label) :
    (∑' (b : ↑((fun E : AlterSeq (State_C × State_A) Label => E.map Prod.fst) ⁻¹' {e_C})),
        dite ((b : AlterSeq (State_C × State_A) Label).trans.Terminates
            ∧ (b : AlterSeq (State_C × State_A) Label).trans.map Prod.fst = Seq.ofList labs)
          (fun h => (simJointExec pe_C sim).probOf (b : AlterSeq (State_C × State_A) Label) h.1)
          (fun _ => 0))
    = ∑' E : AlterSeq (State_C × State_A) Label,
        dite (E.trans.Terminates ∧ E.map Prod.fst = e_C
            ∧ E.trans.map Prod.fst = Seq.ofList labs)
          (fun h => (simJointExec pe_C sim).probOf E h.1) (fun _ => 0) := by
  classical
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun x : {E : AlterSeq (State_C × State_A) Label //
        (dite (E.trans.Terminates ∧ E.map Prod.fst = e_C ∧ E.trans.map Prod.fst = Seq.ofList labs)
          (fun h => (simJointExec pe_C sim).probOf E h.1) (fun _ => 0)) ≠ 0} =>
      (⟨(x : AlterSeq (State_C × State_A) Label), by
        have hx := x.2; simp only [ne_eq] at hx
        have hc : (x : AlterSeq (State_C × State_A) Label).trans.Terminates
            ∧ (x : AlterSeq (State_C × State_A) Label).map Prod.fst = e_C
            ∧ (x : AlterSeq (State_C × State_A) Label).trans.map Prod.fst = Seq.ofList labs := by
          by_contra hcon; exact hx (dif_neg hcon)
        change (x : AlterSeq (State_C × State_A) Label) ∈ ((fun E => E.map Prod.fst) ⁻¹' {e_C})
        exact hc.2.1⟩ :
        ↑((fun E : AlterSeq (State_C × State_A) Label => E.map Prod.fst) ⁻¹' {e_C})))
    ?_ ?_ ?_
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext hab
  · intro b hb
    simp only [Function.mem_support, ne_eq] at hb
    have hbfib : (b : AlterSeq (State_C × State_A) Label).map Prod.fst = e_C := b.2
    have hc2 : (b : AlterSeq (State_C × State_A) Label).trans.Terminates
        ∧ (b : AlterSeq (State_C × State_A) Label).trans.map Prod.fst = Seq.ofList labs := by
      by_contra hcon; exact hb (dif_neg hcon)
    refine ⟨⟨(b : AlterSeq (State_C × State_A) Label), ?_⟩, ?_⟩
    · change dite _ _ _ ≠ 0
      rw [dif_pos ⟨hc2.1, hbfib, hc2.2⟩]
      rw [dif_pos hc2] at hb; exact hb
    · exact Subtype.ext rfl
  · rintro ⟨x, hx⟩
    have hcfull : x.trans.Terminates ∧ x.map Prod.fst = e_C
        ∧ x.trans.map Prod.fst = Seq.ofList labs := by
      by_contra hcon; exact hx (dif_neg hcon)
    have hfibre : x.trans.Terminates ∧ x.trans.map Prod.fst = Seq.ofList labs :=
      ⟨hcfull.1, hcfull.2.2⟩
    simp only [dif_pos hcfull, dif_pos hfibre]

open Classical in
/-- **Per-label-list marginal.** The joint and concrete `probOf`-masses over
histories with a fixed label list `labs` agree (regroup the joint sum by the
`Prod.fst` state-projection; each fibre collapses by `simExecMarginal`). -/
private theorem simPerLabs (pe_C : ProbabilisticExecution sys_C)
    (sim : StrongProbabilisticSimulation sys_C sys_A R)
    (h_init : pe_C.initState = PMF.pure sys_C.init) (labs : List Label) :
    (∑' E : AlterSeq (State_C × State_A) Label,
        dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
          (fun h => (simJointExec pe_C sim).probOf E h.1) (fun _ => 0))
    = ∑' e_C : AlterSeq State_C Label,
        dite (e_C.trans.Terminates ∧ e_C.trans.map Prod.fst = Seq.ofList labs)
          (fun h => pe_C.probOf e_C h.1) (fun _ => 0) := by
  classical
  rw [← ENNReal.tsum_fiberwise
    (f := fun E : AlterSeq (State_C × State_A) Label =>
      dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
        (fun h => (simJointExec pe_C sim).probOf E h.1) (fun _ => 0))
    (g := fun E : AlterSeq (State_C × State_A) Label => E.map Prod.fst)]
  refine tsum_congr (fun e_C => ?_)
  rw [simPerEC pe_C sim labs e_C]
  by_cases hcond : e_C.trans.Terminates ∧ e_C.trans.map Prod.fst = Seq.ofList labs
  · rw [dif_pos hcond]
    rw [show (∑' E : AlterSeq (State_C × State_A) Label,
          dite (E.trans.Terminates ∧ E.map Prod.fst = e_C
              ∧ E.trans.map Prod.fst = Seq.ofList labs)
            (fun h => (simJointExec pe_C sim).probOf E h.1) (fun _ => 0))
        = ∑' E : AlterSeq (State_C × State_A) Label,
          dite (E.trans.Terminates ∧ E.map Prod.fst = e_C)
            (fun h => (simJointExec pe_C sim).probOf E h.1) (fun _ => 0) from by
      refine tsum_congr (fun E => ?_)
      by_cases hc2 : E.trans.Terminates ∧ E.map Prod.fst = e_C
      · rw [dif_pos hc2, dif_pos ⟨hc2.1, hc2.2, by
          have htr : E.trans.map (fun lq : Label × (State_C × State_A) => (lq.1, lq.2.1))
            = e_C.trans := congr_arg AlterSeq.trans hc2.2
          rw [show E.trans.map (Prod.fst : Label × (State_C × State_A) → Label)
            = e_C.trans.map Prod.fst from by rw [← htr, ← Seq.map_comp]; rfl]
          exact hcond.2⟩]
      · rw [dif_neg hc2, dif_neg (fun h => hc2 ⟨h.1, h.2.1⟩)]]
    -- transport `simExecMarginal` along `e_C = ⟨e_C.init, ofList (toList e_C)⟩`.
    have heq :
      (⟨e_C.init, Seq.ofList (e_C.trans.toList hcond.1)⟩ : AlterSeq State_C Label) = e_C := by
      cases e_C; simp only [Stream'.Seq.ofList_toList]
    have hmarg := simExecMarginal pe_C sim h_init (e_C.trans.toList hcond.1) e_C.init
    rw [ProbabilisticExecution.probOf_congr pe_C ⟨e_C.init, Seq.ofList (e_C.trans.toList hcond.1)⟩
      e_C heq (Stream'.Seq.terminates_ofList _) hcond.1] at hmarg
    rw [← hmarg]
    refine tsum_congr (fun E => ?_)
    by_cases hc2 : E.trans.Terminates ∧ E.map Prod.fst = e_C
    · rw [dif_pos hc2, dif_pos ⟨hc2.1, by rw [hc2.2]; exact heq.symm⟩]
    · rw [dif_neg hc2, dif_neg (fun h => hc2 ⟨h.1, by rw [h.2]; exact heq⟩)]
  · rw [dif_neg hcond]
    refine ENNReal.tsum_eq_zero.mpr (fun E => ?_)
    by_cases hc2 : E.trans.Terminates ∧ E.map Prod.fst = e_C
        ∧ E.trans.map Prod.fst = Seq.ofList labs
    · exfalso; apply hcond
      have htr : E.trans.map (fun lq : Label × (State_C × State_A) => (lq.1, lq.2.1))
        = e_C.trans := congr_arg AlterSeq.trans hc2.2.1
      have hterm : e_C.trans.Terminates := by
        rw [← htr]; exact Stream'.Seq.terminates_map_iff.mpr hc2.1
      refine ⟨hterm, ?_⟩
      rw [← hc2.2.2]
      rw [show E.trans.map (Prod.fst : Label × (State_C × State_A) → Label)
        = e_C.trans.map Prod.fst from by rw [← htr, ← Seq.map_comp]; rfl]
    · rw [dif_neg hc2]

open Classical in
/-- **Trace-probability transfer.** The joint execution `simJointExec pe_C sim`
realises the same trace distribution as `pe_C` (both systems share the internal
predicate, so `traceProb_eq_labProb_sum` reduces this to `simPerLabs`).

Public so that per-execution developments can reuse the trace equality for the
specific joint execution, rather than only the set-level
`simProd_achievableTraceDists_superset`. -/
theorem simProd_traceProb_eq (pe_C : ProbabilisticExecution sys_C)
    (sim : StrongProbabilisticSimulation sys_C sys_A R)
    (h_init : pe_C.initState = PMF.pure sys_C.init) (τ : Seq Label) :
    (simProd sys_C sys_A R).traceProb (simJointExec pe_C sim) τ = sys_C.traceProb pe_C τ := by
  classical
  rw [System.traceProb_eq_labProb_sum (simProd sys_C sys_A R) (simJointExec pe_C sim) τ,
    System.traceProb_eq_labProb_sum sys_C pe_C τ]
  refine tsum_congr (fun labs => ?_)
  by_cases htt : sys_C.traceTightLabs τ labs
  · rw [if_pos htt, if_pos (show (simProd sys_C sys_A R).traceTightLabs τ labs from htt)]
    exact simPerLabs pe_C sim h_init labs
  · rw [if_neg htt, if_neg (show ¬ (simProd sys_C sys_A R).traceTightLabs τ labs from htt)]

/-- **Coupling lift.** Every trace distribution achievable by `sys_C` is
achievable by the coupled product `simProd sys_C sys_A R`, using the simulation
to supply, step by step, a coupling of the concrete successor with an abstract
successor. -/
theorem simProd_achievableTraceDists_superset
    {sys_C : System State_C Label} {sys_A : System State_A Label}
    {R : State_C → State_A → Prop}
    (sim : StrongProbabilisticSimulation sys_C sys_A R) :
    achievableTraceDists sys_C ⊆ achievableTraceDists (simProd sys_C sys_A R) := by
  rintro D ⟨pe_C, h_init_C, h_trace_C⟩
  refine ⟨simJointExec pe_C sim, rfl, fun τ => ?_⟩
  rw [simProd_traceProb_eq pe_C sim h_init_C τ]
  exact h_trace_C τ

/-- **Strong simulation preserves achievable trace distributions** (soundness). -/
theorem StrongProbabilisticSimulation.achievableTraceDists_subset
    {sys_C : System State_C Label} {sys_A : System State_A Label}
    {R : State_C → State_A → Prop}
    (sim : StrongProbabilisticSimulation sys_C sys_A R) :
    achievableTraceDists sys_C ⊆ achievableTraceDists sys_A :=
  (simProd_achievableTraceDists_superset sim).trans
    (achievableTraceDists_map Prod.snd rfl (fun _ _ _ h => h.2.1))

end PLTS
