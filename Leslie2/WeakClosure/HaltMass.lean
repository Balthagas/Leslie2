/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.WeakClosure.TraceProb
import Leslie2.Weak.WeakChar

/-!
# The weak-closure `weakTau` collapse (G1)

The simulation-free crux behind forward-simulation transitivity
(`Simulation/Transitivity.weakTau_lift_pure`): a run-to-halt **internal** weak transition of the
weak closure `sys^w` collapses to one of the base system `sys`,

  `weakClosure_weakTau_collapse : weakTau sys^w μ ν → weakTau sys μ ν`.

This is the end-state / `haltMass`-level analogue of `weakClosure_traceProb_superset`
(`WeakClosure/TraceProb.lean`), read from an arbitrary Dirac source `PMF.pure s` rather than from
`PMF.pure sys.init`, and against the halting **end-state** distribution rather than the (tightened)
external trace. Because `traceProb` is taken over *tight* executions — which collapse every internal
run to the transition-free execution (`trans_nil_of_trace_nil_tight`) — the trace pipeline throws
away exactly the internal end-state we need, so a parallel end-state derivation is required.

## Structure of the collapse

Everything bottoms out at one **`g`-integrated halt-mass conservation** for the unfolding scheduler
`expandSched` (`WeakClosure/Scheduler.lean`), the exact structural twin of `lower_haltMass_g_eq`
(`Simulation/DistCollapse.lean`) used for the `𝒟`-collapse:

  `expandSched_haltMass_g_eq` :
    `∑' e, haltMass (expandSched ws) (pure init) e * g (endState e)`
      `= ∑' E, haltMass ws (pure init) E * g (endState E)`.

`sys^w` shares `sys`'s state space, so `endState` is a genuine `State` on both sides (no
pushforward integral, unlike the `𝒟` case). From it the collapse follows by two slices, mirroring
`weakTau_dist_collapse`:

* **`g = 1`** — a.s.-halting: the RHS is `ws`'s total halt mass `= 1` (`witness_halts`);
* **`g = [· = x]`** — end-state pushforward: the RHS is `ν x` (`witness_pushforward`).

The arbitrary source `PMF.pure s` is handled by the `{sys with init := s}` record-update relabeling
(`weakTau_step_congr`, exactly as in `StrongProbabilisticSimulation.weakTau_joint`), since `sys^w`'s
`step` is init-agnostic; the distribution source is handled by pointwise decomposition
(`weakTau_exists_pointwise`) and re-mixing (`weakTau_of_pointwise`).

## Proof structure of `expandSched_haltMass_g_eq`

Two independent halves, both `sorry`-free:

* **Convergence** (the sandwich, using `hAS`): the flow linchpin
  `reachProb_haltCfg_add_dep_le_reachArr` → injection `haltCfgSum_le_haltMass` (i); Kraft bound
  `expandSched_haltMass_tsum_le_one` (ii); `∑ = 1` from `hAS` (iii) ⟹ pointwise
  `haltMass_C = genuine-halt-config-mass`.
* **STEP2** (pure config-bookkeeping, no `hAS`): the genuine halt-config mass equals the abstract
  halt draw (`haltCfgSum_we_eq` : `∑_{halt c, we=E} reachProb c = probOf_A(E) · ws.next E ⊥`), built
  from a per-reset-point marginalization (`reset_draw_marg`/`reachProb_haltEntry_eq`) via the
  entry-draw reindex machinery, then fibered into `hiv` (the two `Equiv.tsum_eq` reindexes by
  `concat`/`we`, joined by the `reachProb_endpoint` swap).
-/

open Stream'

namespace PLTS

variable {State Label : Type} [Silent Label] {sys : System State Label}

/-! ### Relabeling: `weakTau` depends only on the step relation

Local (non-`private`) copy of the `weakTau_step_congr` helper from `Simulation/WeakTauLift.lean`,
used to move an arbitrary Dirac source into the system via `{sys with init := s}`. -/

/-- `weakTau` transports across systems with equal `step` relations (rebuilding the witness
scheduler over the target system). -/
theorem weakTau_step_congr {sys sys' : System State Label}
    (hstep : sys.step = sys'.step) {μ_init μ : PMF State} (h : weakTau sys μ_init μ) :
    weakTau sys' μ_init μ := by
  obtain ⟨σ, hhalt, hpush⟩ := h
  let σ' : Scheduler sys' :=
    { next := σ.next
      valid := by intro e n s ht hs l ν hsupp; rw [← hstep]; exact σ.valid e n s ht hs l ν hsupp }
  let τ' : WeakScheduler sys' := { toScheduler := σ', internal_only := σ.internal_only }
  have hhm : ∀ e, τ'.haltMass μ_init e = σ.haltMass μ_init e := fun _ => rfl
  exact ⟨τ', by simp only [hhm]; exact hhalt, fun s => by simp only [hhm]; exact hpush s⟩

/-- `weakStep` transports across systems with equal `step` relations (`hyperStep` references
`step` only, inlined below). -/
theorem weakStep_step_congr {sys sys' : System State Label} (hstep : sys.step = sys'.step)
    {μ ν : PMF State} {l : Label} (h : weakStep sys μ l ν) : weakStep sys' μ l ν := by
  obtain ⟨m, m', h1, h2, h3⟩ := h
  refine ⟨m, m', weakTau_step_congr hstep h1, ?_, weakTau_step_congr hstep h3⟩
  obtain ⟨p, hp, hν⟩ := h2
  exact ⟨p, fun s hs μ' hμ' => by rw [← hstep]; exact hp s hs μ' hμ', hν⟩

/-- The weak-closure `step` relation transports across systems with equal `step` relations: it is a
disjunction of `weakTau`/`weakStep` of the base, both of which transport. -/
theorem weakClosure_step_congr {sys sys' : System State Label} (hstep : sys.step = sys'.step) :
    (sys^w).step = (sys'^w).step := by
  funext s l μ
  apply propext
  constructor
  · rintro (⟨hτ, hw⟩ | ⟨hτ, hw⟩)
    · exact Or.inl ⟨hτ, weakTau_step_congr hstep hw⟩
    · exact Or.inr ⟨hτ, weakStep_step_congr hstep hw⟩
  · rintro (⟨hτ, hw⟩ | ⟨hτ, hw⟩)
    · exact Or.inl ⟨hτ, weakTau_step_congr hstep.symm hw⟩
    · exact Or.inr ⟨hτ, weakStep_step_congr hstep.symm hw⟩

/-! ### The halt-mass handle (probe of obligation #1)

`expandSched`'s halt draw is the *remainder* mass `expandMass ws e none = 1 − ∑ₚ reachDep/reachArr`,
so its halt mass is the **arrival flow-defect** `reachArr e − ∑ₚ reachDep e`
(via `probOf_eq_reachArr` and `reachDep_sum_le`).
This is the handle the crux proof reads halting mass through. -/

/-- **Probe (obligation #1) — the halt-mass handle.** The halt mass of the unfolding scheduler at a
terminating concrete execution `e` factors as arrival mass times the halt draw, via
`probOf_eq_reachArr`. Since `expandMass ws e none = 1 − ∑ₚ reachDep ws e p / reachArr ws e`
(definitionally), this is the arrival **flow-defect** `reachArr ws e − ∑ₚ reachDep ws e p`
whenever `reachArr ws e ≠ ⊤` (which holds, as `reachArr ≤ 1`) — the form the crux proof reads
halting mass through. -/
theorem expandSched_haltMass_eq_flow (ws : Scheduler sys^w)
    (e : AlterSeq State Label) (h : e.trans.Terminates) :
    Scheduler.haltMass (expandSched ws) (PMF.pure sys.init) ⟨e, h⟩
      = reachArr ws e * expandMass ws e none := by
  unfold Scheduler.haltMass
  rw [probOf_eq_reachArr ws e h]
  rfl

/-- **Sandwich ingredient (ii): `expandSched`'s halt mass is a sub-probability.** The total halting
mass of the unfolded scheduler is at most `1` — a Kraft/antichain bound (`probOf_halt_le_one`),
independent of almost-sure halting. One of the two bounds powering the sandwich proof of the crux
`hLHS` below (the other being `∑ entry-halt = 1`, from `hAS`). -/
theorem expandSched_haltMass_tsum_le_one (ws : Scheduler sys^w) :
    (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        Scheduler.haltMass (expandSched ws) (PMF.pure sys.init) e) ≤ 1 := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  rw [show (∑ e ∈ F, Scheduler.haltMass (expandSched ws) (PMF.pure sys.init) e)
      = ∑ e ∈ F, (⟨PMF.pure sys.init, expandSched ws⟩ : ProbabilisticExecution sys).probOf e.1 e.2
          * (⟨PMF.pure sys.init, expandSched ws⟩ :
              ProbabilisticExecution sys).scheduler.next e.1 none
        from Finset.sum_congr rfl fun e _ => rfl]
  exact ProbabilisticExecution.probOf_halt_le_one _ F

/-- **Sandwich ingredient (i): genuine halts inject into `expandSched` halts.** The mass of halted
configurations at a concrete trajectory `e` is at most `expandSched`'s halt mass there. This turns
the flow linchpin `reachProb_haltCfg_add_dep_le_reachArr` into the pointwise `≤` half of the
sandwich, via the flow-defect form `haltMass_C = reachArr · expandMass ⊥ = reachArr − ∑ reachDep`
(`expandSched_haltMass_eq_flow`; the `reachArr = ⊤` case gives `expandMass ⊥ = 1`, so `haltMass_C =
⊤`). -/
theorem haltCfgSum_le_haltMass (ws : Scheduler sys^w)
    (e : AlterSeq State Label) (h : e.trans.Terminates) :
    (∑' c : {c : Config sys //
        c.concat = e ∧ c.e'.trans = Seq.nil ∧ c.t = none ∧ c.wt = none}, reachProb ws c.1)
      ≤ Scheduler.haltMass (expandSched ws) (PMF.pure sys.init) ⟨e, h⟩ := by
  rw [expandSched_haltMass_eq_flow ws e h]
  set H := ∑' c : {c : Config sys //
      c.concat = e ∧ c.e'.trans = Seq.nil ∧ c.t = none ∧ c.wt = none}, reachProb ws c.1 with hH
  set S := ∑' p : Label × PMF State, reachDep ws e p.1 p.2 with hS
  have hlin : H + S ≤ reachArr ws e := reachProb_haltCfg_add_dep_le_reachArr ws e
  have hSle : S ≤ reachArr ws e := le_trans le_add_self hlin
  -- `∑ₚ reachDep/reachArr = S/reachArr` (division pulled out of the sum).
  have hSS : (∑' p : Label × PMF State, reachDep ws e p.1 p.2 / reachArr ws e)
      = S / reachArr ws e := by
    rw [hS]; simp_rw [div_eq_mul_inv]; rw [ENNReal.tsum_mul_right]
  by_cases hArr : reachArr ws e = ⊤
  · -- `reachArr = ⊤` forces `expandMass ⊥ = 1`, so the RHS is `⊤`.
    have hnone : expandMass ws e none = 1 := by
      rw [expandMass, hArr]; simp only [ENNReal.div_top, tsum_zero, tsub_zero]
    rw [hArr, hnone, mul_one]; exact le_top
  · -- `reachArr < ⊤`: `reachArr · expandMass ⊥ = reachArr − S`, and `H ≤ reachArr − S`.
    have hSne : S ≠ ⊤ := ne_top_of_le_ne_top hArr hSle
    have hflow : reachArr ws e * expandMass ws e none = reachArr ws e - S := by
      by_cases hA0 : reachArr ws e = 0
      · rw [hA0, zero_mul]; simp
      · have hcancel : reachArr ws e * (S / reachArr ws e) = S := by
          rw [div_eq_mul_inv, mul_comm S (reachArr ws e)⁻¹, ← mul_assoc,
            ENNReal.mul_inv_cancel hA0 hArr, one_mul]
        rw [expandMass, hSS, ENNReal.mul_sub (fun _ _ => hArr), mul_one, hcancel]
    rw [hflow]
    calc H = H + S - S := (ENNReal.add_sub_cancel_right hSne).symm
      _ ≤ reachArr ws e - S := tsub_le_tsub_right hlin S

/-! ### The analytic crux: `g`-integrated halt-mass conservation -/

/-- **THE CRUX (convergence), abstract side discharged.** Under almost-sure halting of `ws` (`hAS`),
integrating any test `g` over the halting end-state of the unfolded `sys`-scheduler `expandSched ws`
(from `pure sys.init`) equals integrating `g` over the halting end-state of the `sys^w`-scheduler
`ws`. The `g = 1` slice is a.s.-halting conservation; the `g = [· = x]` slice is the end-state
pushforward. Structural twin of `ProbabilisticExecution.lower_haltMass_g_eq`
(`Simulation/DistCollapse.lean`).

**`hAS` is essential.** Without it the identity is false: a `ws` drawing the reflexive empty step
`weakTau (pure s) (pure s)` (from `weakTau_refl`) forever never halts (RHS `= 0`), yet `expandSched`
counts the stuck mass as halt (LHS `= 1`). Halt/end-state is divergence-sensitive, unlike
`traceProb` (whose `expandSched`-fidelity needs no such hypothesis).

The **abstract side (`RHS`)** is reduced termwise (via `probOf_eq_reachProb_we`) to the common
`Base` sum: entry-config (`e' = nil`) `reachProb` mass, weighted by the outer halt draw
`ws.next E none` and the committed end-state `E.endState`. The **concrete side** `LHS = Base` is
proved by the sandwich (using `hAS`) — pointwise `haltMass_C e = genuine-halt-config-mass` — and
STEP2 (`haltCfgSum_we_eq`, `sorry`-free), which identifies the genuine halt mass with the abstract
halt draw (`E.endState = c.e.endState` on-support via `reachProb_endpoint`). -/
theorem expandSched_haltMass_g_eq (ws : Scheduler sys^w)
    (hAS : (∑' E : {E : AlterSeq State Label // E.trans.Terminates},
      Scheduler.haltMass ws (PMF.pure sys.init) E) = 1)
    (g : State → ENNReal) :
    (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        Scheduler.haltMass (expandSched ws) (PMF.pure sys.init) e * g (e.1.endState e.2))
      = ∑' E : {E : AlterSeq State Label // E.trans.Terminates},
          Scheduler.haltMass ws (PMF.pure sys.init) E * g (E.1.endState E.2) := by
  classical
  -- Abstract side: `RHS = Base`, termwise via `probOf_eq_reachProb_we`.
  have hRHS : (∑' E : {E : AlterSeq State Label // E.trans.Terminates},
        Scheduler.haltMass ws (PMF.pure sys.init) E * g (E.1.endState E.2))
      = ∑' E : {E : AlterSeq State Label // E.trans.Terminates},
          (∑' c : {c : Config sys // c.we = E.1 ∧ c.e'.trans = Seq.nil}, reachProb ws c.1)
            * ws.next E.1 none * g (E.1.endState E.2) := by
    refine tsum_congr (fun E => ?_)
    unfold Scheduler.haltMass
    rw [probOf_eq_reachProb_we ws E.1 E.2]
  -- Concrete side: `LHS = Base` (the crux; consumes `hAS` via the sandwich argument).
  have hLHS : (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        Scheduler.haltMass (expandSched ws) (PMF.pure sys.init) e * g (e.1.endState e.2))
      = ∑' E : {E : AlterSeq State Label // E.trans.Terminates},
          (∑' c : {c : Config sys // c.we = E.1 ∧ c.e'.trans = Seq.nil}, reachProb ws c.1)
            * ws.next E.1 none * g (E.1.endState E.2) := by
    -- **STEP2** — the halt-config ↔ abstract reindex (the sole remaining flow content):
    -- the `g'`-integrated genuine-halt-config mass equals the abstract halt draw.
    have hiv : ∀ g' : State → ENNReal,
        (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
            (∑' c : {c : Config sys // c.concat = e.1 ∧ c.e'.trans = Seq.nil
                ∧ c.t = none ∧ c.wt = none}, reachProb ws c.1) * g' (e.1.endState e.2))
          = ∑' E : {E : AlterSeq State Label // E.trans.Terminates},
              (∑' c : {c : Config sys // c.we = E.1 ∧ c.e'.trans = Seq.nil}, reachProb ws c.1)
                * ws.next E.1 none * g' (E.1.endState E.2) := by
      intro g'
      classical
      -- **RHS = CH_R**: apply `haltCfgSum_we_eq_term` per `E`, then fiber by `we`.
      have hR : (∑' E : {E : AlterSeq State Label // E.trans.Terminates},
            (∑' c : {c : Config sys // c.we = E.1 ∧ c.e'.trans = Seq.nil}, reachProb ws c.1)
              * ws.next E.1 none * g' (E.1.endState E.2))
          = ∑' c : {c : Config sys // (c.e'.trans = Seq.nil ∧ c.t = none ∧ c.wt = none)
              ∧ c.we.trans.Terminates}, reachProb ws c.1 * g' (lastOf c.1.we) := by
        rw [show (∑' E : {E : AlterSeq State Label // E.trans.Terminates},
              (∑' c : {c : Config sys // c.we = E.1 ∧ c.e'.trans = Seq.nil}, reachProb ws c.1)
                * ws.next E.1 none * g' (E.1.endState E.2))
            = ∑' E : {E : AlterSeq State Label // E.trans.Terminates},
                ∑' c : {c : Config sys // c.we = E.1 ∧ c.e'.trans = Seq.nil
                    ∧ c.t = none ∧ c.wt = none}, reachProb ws c.1 * g' (lastOf c.1.we) from ?_]
        · rw [← ENNReal.tsum_sigma (fun (E : {E : AlterSeq State Label // E.trans.Terminates})
              (c : {c : Config sys // c.we = E.1 ∧ c.e'.trans = Seq.nil
                  ∧ c.t = none ∧ c.wt = none}) => reachProb ws c.1 * g' (lastOf c.1.we))]
          exact Equiv.tsum_eq
            (({ toFun := fun p => ⟨p.2.1, ⟨p.2.2.2, by rw [p.2.2.1]; exact p.1.2⟩⟩
                invFun := fun c => ⟨⟨c.1.we, c.2.2⟩, ⟨c.1, rfl, c.2.1⟩⟩
                left_inv := by rintro ⟨⟨E, hE⟩, ⟨c, hcwe, hP⟩⟩; obtain rfl : c.we = E := hcwe; rfl
                right_inv := fun c => rfl } :
              (Σ E : {E : AlterSeq State Label // E.trans.Terminates},
                  {c : Config sys // c.we = E.1 ∧ c.e'.trans = Seq.nil ∧ c.t = none ∧ c.wt = none})
                ≃ {c : Config sys // (c.e'.trans = Seq.nil ∧ c.t = none ∧ c.wt = none)
                    ∧ c.we.trans.Terminates}))
            (fun c => reachProb ws c.1 * g' (lastOf c.1.we))
        · refine tsum_congr (fun E => ?_)
          rw [← lastOf_eq_endState E.1 E.2, ← haltCfgSum_we_eq_term ws E.1 E.2,
            ← ENNReal.tsum_mul_right]
          exact tsum_congr (fun c => by rw [c.2.1])
      -- **LHS = CH_L**: fiber by `concat`, using the endpoint to write `g'` at the abstract end.
      have hL : (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
            (∑' c : {c : Config sys // c.concat = e.1 ∧ c.e'.trans = Seq.nil
                ∧ c.t = none ∧ c.wt = none}, reachProb ws c.1) * g' (e.1.endState e.2))
          = ∑' c : {c : Config sys // (c.e'.trans = Seq.nil ∧ c.t = none ∧ c.wt = none)
              ∧ c.concat.trans.Terminates}, reachProb ws c.1 * g' (lastOf c.1.we) := by
        rw [show (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
              (∑' c : {c : Config sys // c.concat = e.1 ∧ c.e'.trans = Seq.nil
                  ∧ c.t = none ∧ c.wt = none}, reachProb ws c.1) * g' (e.1.endState e.2))
            = ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
                ∑' c : {c : Config sys // c.concat = e.1 ∧ c.e'.trans = Seq.nil
                    ∧ c.t = none ∧ c.wt = none}, reachProb ws c.1 * g' (lastOf c.1.we) from ?_]
        · rw [← ENNReal.tsum_sigma (fun (e : {e : AlterSeq State Label // e.trans.Terminates})
              (c : {c : Config sys // c.concat = e.1 ∧ c.e'.trans = Seq.nil
                  ∧ c.t = none ∧ c.wt = none}) => reachProb ws c.1 * g' (lastOf c.1.we))]
          exact Equiv.tsum_eq
            (({ toFun := fun p => ⟨p.2.1, ⟨p.2.2.2, by rw [p.2.2.1]; exact p.1.2⟩⟩
                invFun := fun c => ⟨⟨c.1.concat, c.2.2⟩, ⟨c.1, rfl, c.2.1⟩⟩
                left_inv := by rintro ⟨⟨e, he⟩, ⟨c, hcc, hP⟩⟩; obtain rfl : c.concat = e := hcc; rfl
                right_inv := fun c => rfl } :
              (Σ e : {e : AlterSeq State Label // e.trans.Terminates},
                  {c : Config sys // c.concat = e.1 ∧ c.e'.trans = Seq.nil ∧ c.t = none ∧ c.wt = none})
                ≃ {c : Config sys // (c.e'.trans = Seq.nil ∧ c.t = none ∧ c.wt = none)
                    ∧ c.concat.trans.Terminates}))
            (fun c => reachProb ws c.1 * g' (lastOf c.1.we))
        · refine tsum_congr (fun e => ?_)
          rw [← lastOf_eq_endState e.1 e.2, ← ENNReal.tsum_mul_right]
          refine tsum_congr (fun c => ?_)
          by_cases hr : reachProb ws c.1 = 0
          · rw [hr, zero_mul, zero_mul]
          · have hcc : c.1.concat = c.1.e := by
              have h0 := c.2.2.1
              simp only [Config.concat, h0, Stream'.Seq.append_nil]
            have hend := reachProb_endpoint ws c.1 hr
            have hle : lastOf e.1 = lastOf c.1.we := by
              have h1 : lastOf c.1.concat = lastOf e.1 := by rw [c.2.1]
              rw [← h1, hcc, hend]
            rw [hle]
      -- **CH_L = CH_R**: identity bijection on support (`concat`-term ⟺ `we`-term, same `g'`).
      have hLR : (∑' c : {c : Config sys // (c.e'.trans = Seq.nil ∧ c.t = none ∧ c.wt = none)
              ∧ c.concat.trans.Terminates}, reachProb ws c.1 * g' (lastOf c.1.we))
          = ∑' c : {c : Config sys // (c.e'.trans = Seq.nil ∧ c.t = none ∧ c.wt = none)
              ∧ c.we.trans.Terminates}, reachProb ws c.1 * g' (lastOf c.1.we) := by
        refine tsum_eq_tsum_of_ne_zero_bij
          (i := fun c : Function.support (fun c : {c : Config sys //
              (c.e'.trans = Seq.nil ∧ c.t = none ∧ c.wt = none) ∧ c.we.trans.Terminates} =>
              reachProb ws c.1 * g' (lastOf c.1.we)) =>
            (⟨c.1.1, ⟨c.1.2.1, by
              have hr : reachProb ws c.1.1 ≠ 0 := fun h0 => c.2 (by simp only [h0, zero_mul])
              have hcc : c.1.1.concat = c.1.1.e := by
                simp only [Config.concat, c.1.2.1.1, Stream'.Seq.append_nil]
              rw [hcc]; exact (reachProb_inv ws c.1.1 hr).1⟩⟩ :
              {c : Config sys //
                (c.e'.trans = Seq.nil ∧ c.t = none ∧ c.wt = none) ∧ c.concat.trans.Terminates}))
          ?_ ?_ ?_
        · rintro ⟨⟨a, ha⟩, hna⟩ ⟨⟨b, hb⟩, hnb⟩ hEq
          simp only [Subtype.mk.injEq] at hEq
          exact Subtype.ext (Subtype.ext hEq)
        · rintro ⟨c, hc⟩ hne
          have hr : reachProb ws c ≠ 0 := fun h0 => hne (by simp only [h0, zero_mul])
          exact ⟨⟨⟨c, ⟨hc.1, reachProb_we_fin ws c hr⟩⟩, hne⟩, Subtype.ext rfl⟩
        · rintro ⟨c, hc⟩; rfl
      rw [hL, hLR, hR]
    -- `∑_E (reset mass)·next = 1`, from `hAS` (via `probOf_eq_reachProb_we`).
    have hBase1 : (∑' E : {E : AlterSeq State Label // E.trans.Terminates},
        (∑' c : {c : Config sys // c.we = E.1 ∧ c.e'.trans = Seq.nil}, reachProb ws c.1)
          * ws.next E.1 none) = 1 := by
      rw [← hAS]
      refine tsum_congr (fun E => ?_)
      unfold Scheduler.haltMass
      rw [probOf_eq_reachProb_we ws E.1 E.2]
    -- (iii) `∑ₑ HC(e) = 1`, from `hiv` at `g' = 1`.
    have hiii : (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        ∑' c : {c : Config sys // c.concat = e.1 ∧ c.e'.trans = Seq.nil
            ∧ c.t = none ∧ c.wt = none}, reachProb ws c.1) = 1 := by
      have h1 := hiv (fun _ => 1)
      simp only [mul_one] at h1
      exact h1.trans hBase1
    -- Sandwich: (i) `HC ≤ HM`, (ii) `∑ HM ≤ 1`, (iii) `∑ HC = 1` ⟹ pointwise `HC = HM`.
    have hi : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
        (∑' c : {c : Config sys // c.concat = e.1 ∧ c.e'.trans = Seq.nil
            ∧ c.t = none ∧ c.wt = none}, reachProb ws c.1)
          ≤ Scheduler.haltMass (expandSched ws) (PMF.pure sys.init) e :=
      fun e => haltCfgSum_le_haltMass ws e.1 e.2
    have hii := expandSched_haltMass_tsum_le_one ws
    have hHM1 : (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        Scheduler.haltMass (expandSched ws) (PMF.pure sys.init) e) = 1 :=
      le_antisymm hii (hiii ▸ ENNReal.tsum_le_tsum hi)
    have hpt : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
        (∑' c : {c : Config sys // c.concat = e.1 ∧ c.e'.trans = Seq.nil
            ∧ c.t = none ∧ c.wt = none}, reachProb ws c.1)
          = Scheduler.haltMass (expandSched ws) (PMF.pure sys.init) e := by
      have hHCtop : (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          ∑' c : {c : Config sys // c.concat = e.1 ∧ c.e'.trans = Seq.nil
              ∧ c.t = none ∧ c.wt = none}, reachProb ws c.1) ≠ ⊤ := by
        rw [hiii]; exact ENNReal.one_ne_top
      intro e
      by_contra hne
      have hcontra := ENNReal.tsum_lt_tsum (i := e) hHCtop hi (lt_of_le_of_ne (hi e) hne)
      rw [hiii, hHM1] at hcontra
      exact lt_irrefl 1 hcontra
    -- Combine: `∑ HM·g = ∑ HC·g` (pointwise) `= Base` (`hiv`).
    calc (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
            Scheduler.haltMass (expandSched ws) (PMF.pure sys.init) e * g (e.1.endState e.2))
        = ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
            (∑' c : {c : Config sys // c.concat = e.1 ∧ c.e'.trans = Seq.nil
                ∧ c.t = none ∧ c.wt = none}, reachProb ws c.1) * g (e.1.endState e.2) :=
          tsum_congr (fun e => by rw [hpt e])
      _ = _ := hiv g
  rw [hLHS, hRHS]

/-! ### The collapse, assembled from the g-identity slices

The `WeakScheduler` wrapper's `internal_only` obligation is discharged by
`expandSched_internal_only` (`WeakClosure/TraceProb.lean`): `expandSched` of an internal-only
`sys^w`-scheduler emits only `τ`. -/

/-- **Init-source collapse.** A run-to-halt internal weak transition of `sys^w` from `pure sys.init`
collapses to one of `sys`. Assembled from `expandSched_haltMass_g_eq` by slicing at `g = 1`
(a.s.-halting) and `g = [· = x]` (end-state pushforward). -/
theorem weakTau_weakClosure_collapse_init {ν : PMF State}
    (h : weakTau sys^w (PMF.pure sys.init) ν) :
    weakTau sys (PMF.pure sys.init) ν := by
  classical
  set ws : WeakScheduler sys^w := h.witnessScheduler with hws
  refine ⟨⟨expandSched ws.toScheduler,
    expandSched_internal_only ws.toScheduler ws.internal_only⟩, ?_, ?_⟩
  · -- a.s.-halting: the `g = 1` slice.
    have key := expandSched_haltMass_g_eq ws.toScheduler h.witness_halts (fun _ => 1)
    simp only [mul_one] at key
    change (∑' e, Scheduler.haltMass (expandSched ws.toScheduler) (PMF.pure sys.init) e) = 1
    rw [key]
    exact h.witness_halts
  · -- end-state pushforward: the `g = [· = x]` slice.
    intro x
    have key := expandSched_haltMass_g_eq ws.toScheduler h.witness_halts
      (fun s => if s = x then (1 : ENNReal) else 0)
    change ν x = ∑' e, Scheduler.haltMass (expandSched ws.toScheduler) (PMF.pure sys.init) e
      * (if e.1.endState e.2 = x then (1 : ENNReal) else 0)
    rw [key]
    exact h.witness_pushforward x

/-- **Single-state collapse.** The `pure s` case, via the `{sys with init := s}` relabeling
(`sys^w`'s `step` is init-agnostic, so both step-congruences are `rfl`). -/
theorem weakClosure_weakTau_collapse_pure {s : State} {ν : PMF State}
    (h : weakTau sys^w (PMF.pure s) ν) :
    weakTau sys (PMF.pure s) ν := by
  have h' : weakTau (({sys with init := s} : System State Label)^w) (PMF.pure s) ν :=
    weakTau_step_congr (sys := sys^w)
      (sys' := ({sys with init := s} : System State Label)^w)
      (weakClosure_step_congr (sys := sys) (sys' := {sys with init := s}) rfl) h
  have hcol : weakTau ({sys with init := s} : System State Label) (PMF.pure s) ν :=
    weakTau_weakClosure_collapse_init (sys := {sys with init := s}) h'
  exact weakTau_step_congr (sys := ({sys with init := s} : System State Label))
    (sys' := sys) rfl hcol

/-- **The weak-closure `weakTau` collapse (G1).** A run-to-halt internal weak transition of the weak
closure `sys^w` collapses to one of the base `sys`. The distribution source is reduced to the
single-state case by pointwise decomposition + re-mixing. -/
theorem weakClosure_weakTau_collapse {μ ν : PMF State}
    (h : weakTau sys^w μ ν) :
    weakTau sys μ ν := by
  obtain ⟨ρ, hρ, hν⟩ := weakTau_exists_pointwise h
  rw [hν]
  exact weakTau_of_pointwise ρ (fun s hs => weakClosure_weakTau_collapse_pure (hρ s hs))

end PLTS
