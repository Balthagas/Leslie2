/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Hybrid
import Leslie2Protocols.ABA.ABAState

/-!
# Non-vacuity witnesses for the protocol-shaped specification

Machine-checked evidence that the composed system `hybrid P` can actually
execute a nontrivial prefix: the core simulation `ABA.coreSim` about it is not
vacuously true through an immediate deadlock.

We fix the small parameter set `P4` (`n = 4`, `f = 1`, `ε = 1/2`) and exhibit a
concrete **21-step run of `hybrid P4` that reaches a genuine `retABA`** — a
complete decision — starting from its initial state:

* `step_callABA₀/₁/₂` — three external input handshakes (`callABA`, *visible*:
  the addressed round loop takes its `input` row, the other three idle, and the
  round specifications, the ABA-side network and the coin oracle idle);
* `step_callG₀/₁/₂` — three graded-agreement calls (`callG 0`, *hidden* to `τ`:
  the caller's round loop hands over its estimate and the round-`0`
  specification takes its owned `call`);
* `step_bindUnset` — the round-`0` specification's `bindUnset` internal
  transition killing the bit `false` (a family `τ`, `n − f` quorum met at
  `n = 4, f = 1` by the three callers of `true`);
* `step_retG₀/₁/₂` — the three graded-agreement `A`-return handshakes
  (`retG 0`, *hidden*), the first locking the round grade to the `A`-side;
* `step_callW₀/₁/₂` — the three coin-call handshakes (`callW 0`, *hidden*);
* `step_flip` + `step_flip_mass` — the coin `flip`, the run's **single
  probabilistic step**: the successor lands on the `bit true` branch (the one
  agreeing with the bound value) with mass exactly `ε = 1/2 > 0`;
* `step_retW₀/₁/₂` — the three coin returns, each a rendezvous on `retWPub`
  (*hidden*): the round loop's fused round advance (deviation D10) joined with
  the network's publication of `⟨DECIDED, true⟩`, giving three distinct
  DECIDED-true senders;
* `step_deliver₀/₁/₂` — the adversary delivers all three receipts to process `0`
  (a rendezvous on `ddlv`, *hidden*), meeting the `n − f = 3` return quorum;
* `step_retABA` — process `0` fires `retABA 0 true`: the decision.

Plus `step_fail` — a `fail` broadcast synchronising all four factors.

Because every step but the flip is a Dirac and the flip's chosen branch has mass
`ε > 0`, the whole path is a positive-probability execution: a product of Diracs
times one `ε` factor. Every guard on these closed numeric states discharges by
`decide`/`rfl`; the Dirac successor distributions collapse through
`prodPMF_pure_pure` and `PMF.pure_map`, and the flip's branch mass through
`prodPMF_pure_left_apply` and `map_apply_inj`.

The ABA-side factors are named through the view of `ABA/ABAState.lean`: a state
of the run is a triple — the round specifications, one `ABAState` holding the
round loops beside the ABA-side network, and the coin oracle — assembled into
the four-factor state by `st`.
-/

namespace PLTS
namespace ABA

open Net Comp

/-- A concrete parameter set: four processes, corruption budget one, and a
never-failing `ε = 1/2` coin, so that each bit outcome carries positive mass
(`ε = 1/2`) and the witnessed `flip` can take the `bit true` branch.
`2 * ε + δ ≤ 1` holds with equality (`2 * (1/2) + 0 = 1`); the adversarial `⊤`
outcome and the failure outcome then both have mass `0`. -/
noncomputable abbrev P4 : Params := ⟨4, 1, by omega, 1 / 2, 0, by
  rw [add_zero, one_div, ENNReal.mul_inv_cancel] <;> simp⟩

namespace NonVacuity

/-! ### Assembling and moving the four factors -/

/-- A state of the protocol-shaped specification, assembled from the round
specifications, the ABA-side pair and the coin oracle. -/
def st (G : ℕ → GBCA.SpecState 4) (s : ABAState P4) (o : ℕ → WCC.SpecState 4) :
    HybridState P4 := (G, s.1, s.2, o)

/-- The round loops on a label one of them owns: the addressed loop takes its
row, the others stand still, and the group's successor is the pointwise
update. -/
theorem coreLoops_at {C : ∀ _ : Fin 4, CoreRec 4} (id : Fin 4) {L : NLab 4}
    {c' : CoreRec 4} (hown : CoreProcStepN P4 id (C id) L (PMF.pure c'))
    (hidle : ∀ j, j ≠ id → CoreProcStepN P4 j (C j) L (PMF.pure (C j))) (i : Fin 4) :
    CoreProcStepN P4 i (C i) L (PMF.pure (Function.update C id c' i)) := by
  by_cases h : i = id
  · subst h; rw [Function.update_self]; exact hown
  · rw [Function.update_of_ne h]; exact hidle i h

/-- The coin oracle's idle row on a shared label that is neither `τ`, nor one
of its own handshakes, nor `fail`. -/
theorem wccIdle (o : ℕ → WCC.SpecState 4) {l : Lab 4} (hl : l ≠ Lab.tau)
    (hr : Lab.wccRound l = none) (hf : ¬ Lab.isFail l) :
    (wccLift P4).step o (Sum.inl l) (PMF.pure o) :=
  (System.mapIdle_step_some (wccPull_inl l) (PMF.pure o)).mpr
    (wccFamilyN_idle P4 o hl hr hf)

/-! ### Named states of the run -/

/-- The round specifications: every round initial. -/
def G0 : ℕ → GBCA.SpecState 4 := fun _ => GBCA.SpecState.initial 4

/-- The coin oracle: every round initial. -/
def W0 : ℕ → WCC.SpecState 4 := fun _ => WCC.SpecState.initial 4

/-- The ABA-side state: every round loop idle, nothing multicast, nobody
corrupted. -/
noncomputable def S0 : ABAState P4 := ABAState.initial P4

/-- The ABA-side update of a `callABA id true` input: enter round `0`, ready to
call the graded agreement. -/
noncomputable def sInput (id : Fin 4) (s : ABAState P4) : ABAState P4 :=
  s.setProc id { s.procs id with
    input := some true, est := some true, round := 0, phase := .toCallG }

/-- The ABA-side update of a `callG r id` emit: advance to `awaitG`. -/
noncomputable def sCallG (id : Fin 4) (s : ABAState P4) : ABAState P4 :=
  s.setProc id { s.procs id with phase := .awaitG }

/-- The ABA-side update of a round-`0` graded-agreement `A true` return: adopt
the estimate, record the grade, head for the coin. -/
noncomputable def sRetG (id : Fin 4) (s : ABAState P4) : ABAState P4 :=
  s.setProc id { s.procs id with
    est := some true, lastGrade := some (.A true), phase := .toCallW }

/-- The ABA-side update of a `callW r id` emit: advance to `awaitW`. -/
noncomputable def sCallW (id : Fin 4) (s : ABAState P4) : ABAState P4 :=
  s.setProc id { s.procs id with phase := .awaitW }

/-- The round-`0` specification update of a `call id true`: record the input. -/
def gCall (id : Fin 4) (s : ℕ → GBCA.SpecState 4) : ℕ → GBCA.SpecState 4 :=
  Function.update s 0 { s 0 with call := Function.update (s 0).call id (some true) }

/-- The round-`0` specification update of an `A true` return by `id`: lock the
grade to the `A`-side and record the return. -/
def gRetA (id : Fin 4) (s : ℕ → GBCA.SpecState 4) : ℕ → GBCA.SpecState 4 :=
  Function.update s 0 { s 0 with grade := some true, ret := Function.update (s 0).ret id true }

/-- The round-`0` coin update of a `call id`: record `id` as a caller. -/
def wCall (id : Fin 4) (s : ℕ → WCC.SpecState 4) : ℕ → WCC.SpecState 4 :=
  Function.update s 0 { s 0 with called := Function.update (s 0).called id true }

/-- The round-`0` coin update of the `flip` landing on `bit true`. -/
def wFlip (s : ℕ → WCC.SpecState 4) : ℕ → WCC.SpecState 4 :=
  Function.update s 0 { s 0 with val := .bit true }

/-- The round-`0` coin update of a `ret id true`. -/
def wRet (id : Fin 4) (s : ℕ → WCC.SpecState 4) : ℕ → WCC.SpecState 4 :=
  Function.update s 0 { s 0 with ret := Function.update (s 0).ret id true }

/-- ABA-side states after the three inputs. -/
noncomputable def S1 : ABAState P4 := sInput 0 S0
noncomputable def S2 : ABAState P4 := sInput 1 S1
noncomputable def S3 : ABAState P4 := sInput 2 S2

/-- Round specifications after the three round-`0` calls. -/
def G1 : ℕ → GBCA.SpecState 4 := gCall 0 G0
def G2 : ℕ → GBCA.SpecState 4 := gCall 1 G1
def G3 : ℕ → GBCA.SpecState 4 := gCall 2 G2

/-- ABA-side states after the three round-`0` calls. -/
noncomputable def Sc1 : ABAState P4 := sCallG 0 S3
noncomputable def Sc2 : ABAState P4 := sCallG 1 Sc1
noncomputable def Sc3 : ABAState P4 := sCallG 2 Sc2

/-- Round specifications after `bindUnset` kills the round-`0` bit `false`,
sparing `true`. -/
def Gb : ℕ → GBCA.SpecState 4 := Function.update G3 0 { G3 0 with dead := {false} }

/-- Round specifications after the three round-`0` `A`-returns. -/
def Gr : ℕ → GBCA.SpecState 4 := gRetA 0 Gb
def Ga1 : ℕ → GBCA.SpecState 4 := gRetA 1 Gr
def Ga2 : ℕ → GBCA.SpecState 4 := gRetA 2 Ga1

/-- ABA-side states after the three round-`0` graded-agreement returns. -/
noncomputable def Sr : ABAState P4 := sRetG 0 Sc3
noncomputable def Sq1 : ABAState P4 := sRetG 1 Sr
noncomputable def Sq2 : ABAState P4 := sRetG 2 Sq1

/-- ABA-side states after all three processes call the coin. -/
noncomputable def Sw0 : ABAState P4 := sCallW 0 Sq2
noncomputable def Sw1 : ABAState P4 := sCallW 1 Sw0
noncomputable def Sw2 : ABAState P4 := sCallW 2 Sw1

/-- The coin oracle after all three processes call the coin. -/
def Wc0 : ℕ → WCC.SpecState 4 := wCall 0 W0
def Wc1 : ℕ → WCC.SpecState 4 := wCall 1 Wc0
def Wc2 : ℕ → WCC.SpecState 4 := wCall 2 Wc1

/-- The coin oracle after the coin flips to `bit true`. -/
def Wfl : ℕ → WCC.SpecState 4 := wFlip Wc2

/-- The coin oracle after all three processes receive the coin. -/
def Wr0 : ℕ → WCC.SpecState 4 := wRet 0 Wfl
def Wr1 : ℕ → WCC.SpecState 4 := wRet 1 Wr0
def Wr2 : ℕ → WCC.SpecState 4 := wRet 2 Wr1

/-- ABA-side states after the three coin returns; each is the fused round
advance (deviation D10), which multicasts `⟨DECIDED, true⟩` on the `A true`
grade the round carried. -/
noncomputable def Ss0 : ABAState P4 := Sw2.stepRound 0 true
noncomputable def Ss1 : ABAState P4 := Ss0.stepRound 1 true
noncomputable def Ss2 : ABAState P4 := Ss1.stepRound 2 true

/-- ABA-side states after the adversary delivers all three `⟨DECIDED, true⟩` to
process `0`. -/
noncomputable def Sd0 : ABAState P4 := Ss2.deliverDecided 0 0 true
noncomputable def Sd1 : ABAState P4 := Sd0.deliverDecided 0 1 true
noncomputable def Sd2 : ABAState P4 := Sd1.deliverDecided 0 2 true

/-- The ABA-side state after process `0` fires `retABA 0 true`. -/
noncomputable def Sfin : ABAState P4 := Sd2.setProc 0 { Sd2.procs 0 with returned := true }

/-- The four factors after a synchronised `fail 0` broadcast. -/
noncomputable def Gf : ℕ → GBCA.SpecState 4 := fun r => (G0 r).corrupt P4 (0 : Fin 4)
noncomputable def Wf : ℕ → WCC.SpecState 4 := fun r => (W0 r).corrupt P4 (0 : Fin 4)
noncomputable def Sf : ABAState P4 := ABAState.corrupt P4 (0 : Fin 4) S0

/-- The initial protocol-shaped state is `(G0, S0, W0)`. -/
theorem hybrid_init : (hybrid P4).init = st G0 S0 W0 := rfl

/-! ### Step 1–3: the external input handshakes (`callABA`, visible) -/

/-- First input: process `0` receives `callABA 0 true`. Visible label; process
`0`'s round loop takes `input`, the other three and the remaining factors
idle. -/
theorem step_callABA₀ :
    (hybrid P4).step (st G0 S0 W0) (Lab.callABA (0 : Fin 4) true)
      (PMF.pure (st G0 S1 W0)) := by
  refine hybrid_vis P4 (by simp) ?_
  have h := hybridPre_vis_step P4 (G := G0) (C := S0.1) (A := S0.2) (o := W0)
    (L := Sum.inl (Lab.callABA (0 : Fin 4) true)) (by simp)
    (specSide_idle P4 G0 (by simp) rfl not_false)
    (coreLoops_at 0 (CoreProcStepN.input (P := P4) (S0.1 0) true rfl)
      (fun j hj => CoreProcStepN.callABAIdle (P := P4) (S0.1 j) 0 true (Ne.symm hj)))
    (ANetStep.callABAIdle (P := P4) S0.2 0 true)
    (wccIdle W0 (by simp) rfl (by simp [Lab.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Second input: process `1`. -/
theorem step_callABA₁ :
    (hybrid P4).step (st G0 S1 W0) (Lab.callABA (1 : Fin 4) true)
      (PMF.pure (st G0 S2 W0)) := by
  refine hybrid_vis P4 (by simp) ?_
  have h := hybridPre_vis_step P4 (G := G0) (C := S1.1) (A := S1.2) (o := W0)
    (L := Sum.inl (Lab.callABA (1 : Fin 4) true)) (by simp)
    (specSide_idle P4 G0 (by simp) rfl not_false)
    (coreLoops_at 1 (CoreProcStepN.input (P := P4) (S1.1 1) true (by decide))
      (fun j hj => CoreProcStepN.callABAIdle (P := P4) (S1.1 j) 1 true (Ne.symm hj)))
    (ANetStep.callABAIdle (P := P4) S1.2 1 true)
    (wccIdle W0 (by simp) rfl (by simp [Lab.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Third input: process `2`. -/
theorem step_callABA₂ :
    (hybrid P4).step (st G0 S2 W0) (Lab.callABA (2 : Fin 4) true)
      (PMF.pure (st G0 S3 W0)) := by
  refine hybrid_vis P4 (by simp) ?_
  have h := hybridPre_vis_step P4 (G := G0) (C := S2.1) (A := S2.2) (o := W0)
    (L := Sum.inl (Lab.callABA (2 : Fin 4) true)) (by simp)
    (specSide_idle P4 G0 (by simp) rfl not_false)
    (coreLoops_at 2 (CoreProcStepN.input (P := P4) (S2.1 2) true (by decide))
      (fun j hj => CoreProcStepN.callABAIdle (P := P4) (S2.1 j) 2 true (Ne.symm hj)))
    (ANetStep.callABAIdle (P := P4) S2.2 2 true)
    (wccIdle W0 (by simp) rfl (by simp [Lab.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Steps 4–6: the graded-agreement calls (`callG 0`, hidden to `τ`) -/

/-- First graded-agreement call: process `0`'s round loop hands over its
estimate and the round-`0` specification takes its owned `call`. -/
theorem step_callG₀ :
    (hybrid P4).step (st G0 S3 W0) Lab.tau (PMF.pure (st G1 Sc1 W0)) := by
  refine hybrid_hidden P4 (l := Lab.callG 0 (0 : Fin 4) true) (by simp) ?_
  have h := hybridPre_vis_step P4 (G := G0) (C := S3.1) (A := S3.2) (o := W0)
    (L := Sum.inl (Lab.callG 0 (0 : Fin 4) true)) (by simp)
    (specSide_owned P4 rfl rfl (GBCA.Step.call (P := P4) (r := 0) (G0 0) 0 true rfl))
    (coreLoops_at 0 (CoreProcStepN.callG (P := P4) (S3.1 0) 0 true (by decide) (by decide)
        (by decide))
      (fun j hj => CoreProcStepN.callGIdle (P := P4) (S3.1 j) 0 0 true (Ne.symm hj)))
    (ANetStep.callGIdle (P := P4) S3.2 0 0 true)
    (wccIdle W0 (by simp) rfl (by simp [Lab.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Second graded-agreement call: process `1`. -/
theorem step_callG₁ :
    (hybrid P4).step (st G1 Sc1 W0) Lab.tau (PMF.pure (st G2 Sc2 W0)) := by
  refine hybrid_hidden P4 (l := Lab.callG 0 (1 : Fin 4) true) (by simp) ?_
  have h := hybridPre_vis_step P4 (G := G1) (C := Sc1.1) (A := Sc1.2) (o := W0)
    (L := Sum.inl (Lab.callG 0 (1 : Fin 4) true)) (by simp)
    (specSide_owned P4 rfl rfl (GBCA.Step.call (P := P4) (r := 0) (G1 0) 1 true (by decide)))
    (coreLoops_at 1 (CoreProcStepN.callG (P := P4) (Sc1.1 1) 0 true (by decide) (by decide)
        (by decide))
      (fun j hj => CoreProcStepN.callGIdle (P := P4) (Sc1.1 j) 0 1 true (Ne.symm hj)))
    (ANetStep.callGIdle (P := P4) Sc1.2 0 1 true)
    (wccIdle W0 (by simp) rfl (by simp [Lab.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Third graded-agreement call: process `2`. The round-`0` specification now
holds three inputs. -/
theorem step_callG₂ :
    (hybrid P4).step (st G2 Sc2 W0) Lab.tau (PMF.pure (st G3 Sc3 W0)) := by
  refine hybrid_hidden P4 (l := Lab.callG 0 (2 : Fin 4) true) (by simp) ?_
  have h := hybridPre_vis_step P4 (G := G2) (C := Sc2.1) (A := Sc2.2) (o := W0)
    (L := Sum.inl (Lab.callG 0 (2 : Fin 4) true)) (by simp)
    (specSide_owned P4 rfl rfl (GBCA.Step.call (P := P4) (r := 0) (G2 0) 2 true (by decide)))
    (coreLoops_at 2 (CoreProcStepN.callG (P := P4) (Sc2.1 2) 0 true (by decide) (by decide)
        (by decide))
      (fun j hj => CoreProcStepN.callGIdle (P := P4) (Sc2.1 j) 0 2 true (Ne.symm hj)))
    (ANetStep.callGIdle (P := P4) Sc2.2 0 2 true)
    (wccIdle W0 (by simp) rfl (by simp [Lab.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Step 7: the `bindUnset` internal transition of the round-`0`
specification (family `τ`, interleaved) -/

/-- With three of four processes having called, the round-`0` quorum `n − f = 3`
is met, so `bindUnset` kills the bit `false` (the three callers of `true` supply
the `f + 1` support for the surviving bit). This is a family `τ`, interleaved on
the specification side while the other three factors hold. -/
theorem step_bindUnset :
    (hybrid P4).step (st G3 Sc3 W0) Lab.tau (PMF.pure (st Gb Sc3 W0)) := by
  refine hybrid_vis P4 (by simp) ?_
  exact hybridPre_tau_spec P4 (specSide_tau P4
    (GBCA.Step.bindUnset (P := P4) (r := 0) (G3 0) false
      (by unfold GBCA.SpecState.quorum; decide) (by decide) (by decide)))

/-! ### Steps 8–10: the three graded-agreement `A`-returns (`retG 0`, hidden) -/

/-- Process `0` takes an `A`-return of the bound value `true`: the round-`0`
specification locks the grade and records the return, the round loop adopts the
estimate and heads for the coin. -/
theorem step_retG₀ :
    (hybrid P4).step (st Gb Sc3 W0) Lab.tau (PMF.pure (st Gr Sr W0)) := by
  refine hybrid_hidden P4 (l := Lab.retG 0 (0 : Fin 4) (.A true)) (by simp) ?_
  have h := hybridPre_vis_step P4 (G := Gb) (C := Sc3.1) (A := Sc3.2) (o := W0)
    (L := Sum.inl (Lab.retG 0 (0 : Fin 4) (.A true))) (by simp)
    (specSide_owned P4 rfl rfl (GBCA.Step.retA (P := P4) (r := 0) (Gb 0) 0 true
      (by decide) (by decide) (Or.inl rfl) rfl))
    (coreLoops_at 0 (CoreProcStepN.retG (P := P4) (Sc3.1 0) 0 (.A true) (by decide) (by decide))
      (fun j hj => CoreProcStepN.retGIdle (P := P4) (Sc3.1 j) 0 0 (.A true) (Ne.symm hj)))
    (ANetStep.retGIdle (P := P4) Sc3.2 0 0 (.A true))
    (wccIdle W0 (by simp) rfl (by simp [Lab.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `1`'s round-`0` `A`-return. -/
theorem step_retG₁ :
    (hybrid P4).step (st Gr Sr W0) Lab.tau (PMF.pure (st Ga1 Sq1 W0)) := by
  refine hybrid_hidden P4 (l := Lab.retG 0 (1 : Fin 4) (.A true)) (by simp) ?_
  have h := hybridPre_vis_step P4 (G := Gr) (C := Sr.1) (A := Sr.2) (o := W0)
    (L := Sum.inl (Lab.retG 0 (1 : Fin 4) (.A true))) (by simp)
    (specSide_owned P4 rfl rfl (GBCA.Step.retA (P := P4) (r := 0) (Gr 0) 1 true
      (by decide) (by decide) (Or.inr rfl) (by decide)))
    (coreLoops_at 1 (CoreProcStepN.retG (P := P4) (Sr.1 1) 0 (.A true) (by decide) (by decide))
      (fun j hj => CoreProcStepN.retGIdle (P := P4) (Sr.1 j) 0 1 (.A true) (Ne.symm hj)))
    (ANetStep.retGIdle (P := P4) Sr.2 0 1 (.A true))
    (wccIdle W0 (by simp) rfl (by simp [Lab.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `2`'s round-`0` `A`-return. -/
theorem step_retG₂ :
    (hybrid P4).step (st Ga1 Sq1 W0) Lab.tau (PMF.pure (st Ga2 Sq2 W0)) := by
  refine hybrid_hidden P4 (l := Lab.retG 0 (2 : Fin 4) (.A true)) (by simp) ?_
  have h := hybridPre_vis_step P4 (G := Ga1) (C := Sq1.1) (A := Sq1.2) (o := W0)
    (L := Sum.inl (Lab.retG 0 (2 : Fin 4) (.A true))) (by simp)
    (specSide_owned P4 rfl rfl (GBCA.Step.retA (P := P4) (r := 0) (Ga1 0) 2 true
      (by decide) (by decide) (Or.inr rfl) (by decide)))
    (coreLoops_at 2 (CoreProcStepN.retG (P := P4) (Sq1.1 2) 0 (.A true) (by decide) (by decide))
      (fun j hj => CoreProcStepN.retGIdle (P := P4) (Sq1.1 j) 0 2 (.A true) (Ne.symm hj)))
    (ANetStep.retGIdle (P := P4) Sq1.2 0 2 (.A true))
    (wccIdle W0 (by simp) rfl (by simp [Lab.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Steps 11–13: all three call the coin (hidden `callW` handshakes) -/

/-- Process `0` calls the round-`0` coin. -/
theorem step_callW₀ :
    (hybrid P4).step (st Ga2 Sq2 W0) Lab.tau (PMF.pure (st Ga2 Sw0 Wc0)) := by
  refine hybrid_hidden P4 (l := Lab.callW 0 (0 : Fin 4)) (by simp) ?_
  have h := hybridPre_vis_step P4 (G := Ga2) (C := Sq2.1) (A := Sq2.2) (o := W0)
    (L := Sum.inl (Lab.callW 0 (0 : Fin 4))) (by simp)
    (specSide_idle P4 Ga2 (by simp) rfl not_false)
    (coreLoops_at 0 (CoreProcStepN.callW (P := P4) (Sq2.1 0) 0 (by decide) (by decide))
      (fun j hj => CoreProcStepN.callWIdle (P := P4) (Sq2.1 j) 0 0 (Ne.symm hj)))
    (ANetStep.callWIdle (P := P4) Sq2.2 0 0)
    ((System.mapIdle_step_some (wccPull_inl (Lab.callW 0 (0 : Fin 4))) _).mpr
      (wccFamily_owned P4 W0 rfl (WCC.Step.call (P := P4) (r := 0) (W0 0) 0 (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `1` calls the round-`0` coin. -/
theorem step_callW₁ :
    (hybrid P4).step (st Ga2 Sw0 Wc0) Lab.tau (PMF.pure (st Ga2 Sw1 Wc1)) := by
  refine hybrid_hidden P4 (l := Lab.callW 0 (1 : Fin 4)) (by simp) ?_
  have h := hybridPre_vis_step P4 (G := Ga2) (C := Sw0.1) (A := Sw0.2) (o := Wc0)
    (L := Sum.inl (Lab.callW 0 (1 : Fin 4))) (by simp)
    (specSide_idle P4 Ga2 (by simp) rfl not_false)
    (coreLoops_at 1 (CoreProcStepN.callW (P := P4) (Sw0.1 1) 0 (by decide) (by decide))
      (fun j hj => CoreProcStepN.callWIdle (P := P4) (Sw0.1 j) 0 1 (Ne.symm hj)))
    (ANetStep.callWIdle (P := P4) Sw0.2 0 1)
    ((System.mapIdle_step_some (wccPull_inl (Lab.callW 0 (1 : Fin 4))) _).mpr
      (wccFamily_owned P4 Wc0 rfl (WCC.Step.call (P := P4) (r := 0) (Wc0 0) 1 (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `2` calls the round-`0` coin; three callers now meet the `> f`
resolution threshold. -/
theorem step_callW₂ :
    (hybrid P4).step (st Ga2 Sw1 Wc1) Lab.tau (PMF.pure (st Ga2 Sw2 Wc2)) := by
  refine hybrid_hidden P4 (l := Lab.callW 0 (2 : Fin 4)) (by simp) ?_
  have h := hybridPre_vis_step P4 (G := Ga2) (C := Sw1.1) (A := Sw1.2) (o := Wc1)
    (L := Sum.inl (Lab.callW 0 (2 : Fin 4))) (by simp)
    (specSide_idle P4 Ga2 (by simp) rfl not_false)
    (coreLoops_at 2 (CoreProcStepN.callW (P := P4) (Sw1.1 2) 0 (by decide) (by decide))
      (fun j hj => CoreProcStepN.callWIdle (P := P4) (Sw1.1 j) 0 2 (Ne.symm hj)))
    (ANetStep.callWIdle (P := P4) Sw1.2 0 2)
    ((System.mapIdle_step_some (wccPull_inl (Lab.callW 0 (2 : Fin 4))) _).mpr
      (wccFamily_owned P4 Wc1 rfl (WCC.Step.call (P := P4) (r := 0) (Wc1 0) 2 (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Step 14: the coin `flip` (the run's single probabilistic step) -/

/-- The coin distribution produced by the `flip`: the `wccPMF` outcome resolves
round `0`'s `val`. -/
noncomputable def flipWr : PMF (ℕ → WCC.SpecState 4) :=
  (P4.wccPMF.map (fun o => { Wc2 0 with val := o.toTVal })).map
    (Function.update Wc2 0)

/-- The successor distribution of the coin flip: the three other factors stay
put (Dirac), the coin oracle resolves. -/
noncomputable def flipμ : PMF (HybridState P4) :=
  prodPMF (PMF.pure Ga2) (prodPMF (PMF.pure Sw2.1) (prodPMF (PMF.pure Sw2.2) flipWr))

/-- The coin `flip` is a legal silent transition of the composed system: the
round-`0` coin resolves `val` by `wccPMF` (threshold met by the three callers),
the other three factors interleave. -/
theorem step_flip : (hybrid P4).step (st Ga2 Sw2 Wc2) Lab.tau flipμ := by
  refine hybrid_vis P4 (by simp) ?_
  exact hybridPre_tau_wcc P4 (wccFamily_tau P4 Wc2
    (WCC.Step.flip (P := P4) (r := 0) (Wc2 0)
      (by unfold WCC.SpecState.threshold; decide) (by decide)))

/-- The flip lands on the `bit true` branch — the outcome that agrees with the
bound value — with mass exactly `ε = 1/2 > 0`. This is the run's single
`ε` factor; every other step is Dirac, so the whole path has positive
probability. -/
theorem step_flip_mass : flipμ (st Ga2 Sw2 Wfl) = P4.ε := by
  have hup : Function.Injective (Function.update Wc2 0) := by
    intro a b h; have h0 := congrFun h 0; simpa using h0
  have hg : Function.Injective
      (fun o : CoinOutcome => ({ Wc2 0 with val := o.toTVal } : WCC.SpecState 4)) :=
    fun _ _ h => CoinOutcome.toTVal_injective (congrArg (·.val) h)
  change prodPMF (PMF.pure Ga2) (prodPMF (PMF.pure Sw2.1) (prodPMF (PMF.pure Sw2.2) flipWr))
      (Ga2, Sw2.1, Sw2.2, Wfl) = P4.ε
  rw [prodPMF_pure_left_apply, prodPMF_pure_left_apply, prodPMF_pure_left_apply]
  unfold flipWr
  rw [show (Wfl : ℕ → WCC.SpecState 4)
      = Function.update Wc2 0 { Wc2 0 with val := TVal.bit true } from rfl,
    map_apply_inj hup,
    show ({ Wc2 0 with val := TVal.bit true } : WCC.SpecState 4)
      = (fun o => { Wc2 0 with val := o.toTVal }) (CoinOutcome.bit true) from rfl,
    map_apply_inj hg, Params.wccPMF_apply_bit]

/-! ### Steps 15–17: the three coin returns, each a `retWPub` rendezvous of the
round loop's fused round advance (deviation D10) with the network's publication
of `⟨DECIDED, true⟩`. -/

/-- Process `0` receives the coin and multicasts `⟨DECIDED, true⟩`. -/
theorem step_retW₀ :
    (hybrid P4).step (st Ga2 Sw2 Wfl) Lab.tau (PMF.pure (st Ga2 Ss0 Wr0)) := by
  refine hybrid_rendezvous P4 (e := .retWPub 0 (0 : Fin 4) true true) ?_
  have h := hybridPre_vis_step P4 (G := Ga2) (C := Sw2.1) (A := Sw2.2) (o := Wfl)
    (L := Sum.inr (.retWPub 0 (0 : Fin 4) true true)) (by simp)
    (specSide_idle P4 Ga2 (by simp) rfl not_false)
    (coreLoops_at 0 (CoreProcStepN.retWPub (P := P4) (Sw2.1 0) 0 true true (by decide)
        (by decide) (by decide))
      (fun j hj => CoreProcStepN.retWPubIdle (P := P4) (Sw2.1 j) 0 0 true true (Ne.symm hj)))
    (ANetStep.retWPub (P := P4) Sw2.2 0 0 true true)
    ((System.mapIdle_step_some (wccPull_retWPub 0 (0 : Fin 4) true true) _).mpr
      (wccFamily_owned P4 Wfl rfl
        (WCC.Step.ret (P := P4) (r := 0) (Wfl 0) 0 true (Or.inr (by decide)) (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `1` receives the coin and multicasts `⟨DECIDED, true⟩`. -/
theorem step_retW₁ :
    (hybrid P4).step (st Ga2 Ss0 Wr0) Lab.tau (PMF.pure (st Ga2 Ss1 Wr1)) := by
  refine hybrid_rendezvous P4 (e := .retWPub 0 (1 : Fin 4) true true) ?_
  have h := hybridPre_vis_step P4 (G := Ga2) (C := Ss0.1) (A := Ss0.2) (o := Wr0)
    (L := Sum.inr (.retWPub 0 (1 : Fin 4) true true)) (by simp)
    (specSide_idle P4 Ga2 (by simp) rfl not_false)
    (coreLoops_at 1 (CoreProcStepN.retWPub (P := P4) (Ss0.1 1) 0 true true (by decide)
        (by decide) (by decide))
      (fun j hj => CoreProcStepN.retWPubIdle (P := P4) (Ss0.1 j) 0 1 true true (Ne.symm hj)))
    (ANetStep.retWPub (P := P4) Ss0.2 0 1 true true)
    ((System.mapIdle_step_some (wccPull_retWPub 0 (1 : Fin 4) true true) _).mpr
      (wccFamily_owned P4 Wr0 rfl
        (WCC.Step.ret (P := P4) (r := 0) (Wr0 0) 1 true (Or.inr (by decide)) (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `2` receives the coin and multicasts `⟨DECIDED, true⟩`; three
distinct senders now hold `⟨DECIDED, true⟩`. -/
theorem step_retW₂ :
    (hybrid P4).step (st Ga2 Ss1 Wr1) Lab.tau (PMF.pure (st Ga2 Ss2 Wr2)) := by
  refine hybrid_rendezvous P4 (e := .retWPub 0 (2 : Fin 4) true true) ?_
  have h := hybridPre_vis_step P4 (G := Ga2) (C := Ss1.1) (A := Ss1.2) (o := Wr1)
    (L := Sum.inr (.retWPub 0 (2 : Fin 4) true true)) (by simp)
    (specSide_idle P4 Ga2 (by simp) rfl not_false)
    (coreLoops_at 2 (CoreProcStepN.retWPub (P := P4) (Ss1.1 2) 0 true true (by decide)
        (by decide) (by decide))
      (fun j hj => CoreProcStepN.retWPubIdle (P := P4) (Ss1.1 j) 0 2 true true (Ne.symm hj)))
    (ANetStep.retWPub (P := P4) Ss1.2 0 2 true true)
    ((System.mapIdle_step_some (wccPull_retWPub 0 (2 : Fin 4) true true) _).mpr
      (wccFamily_owned P4 Wr1 rfl
        (WCC.Step.ret (P := P4) (r := 0) (Wr1 0) 2 true (Or.inr (by decide)) (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Steps 18–20: the adversary delivers the three `⟨DECIDED, true⟩` to
process `0` (a `ddlv` rendezvous of the receiving round loop with the
network). -/

/-- Deliver process `0`'s own `⟨DECIDED, true⟩`. -/
theorem step_deliver₀ :
    (hybrid P4).step (st Ga2 Ss2 Wr2) Lab.tau (PMF.pure (st Ga2 Sd0 Wr2)) := by
  refine hybrid_rendezvous P4 (e := .ddlv (0 : Fin 4) (0 : Fin 4) true) ?_
  have h := hybridPre_vis_step P4 (G := Ga2) (C := Ss2.1) (A := Ss2.2) (o := Wr2)
    (L := Sum.inr (.ddlv (0 : Fin 4) (0 : Fin 4) true)) (by simp)
    (specSide_idle P4 Ga2 (by simp) rfl not_false)
    (coreLoops_at 0 (CoreProcStepN.ddlvRecv (P := P4) (Ss2.1 0) 0 true (by decide))
      (fun j hj => CoreProcStepN.ddlvIdle (P := P4) (Ss2.1 j) 0 0 true (Ne.symm hj)))
    (ANetStep.ddlv (P := P4) Ss2.2 0 0 true (by decide))
    ((System.mapIdle_step_none (wccPull_ddlv (0 : Fin 4) (0 : Fin 4) true) _).mpr rfl)
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Deliver process `1`'s `⟨DECIDED, true⟩` to process `0`. -/
theorem step_deliver₁ :
    (hybrid P4).step (st Ga2 Sd0 Wr2) Lab.tau (PMF.pure (st Ga2 Sd1 Wr2)) := by
  refine hybrid_rendezvous P4 (e := .ddlv (0 : Fin 4) (1 : Fin 4) true) ?_
  have h := hybridPre_vis_step P4 (G := Ga2) (C := Sd0.1) (A := Sd0.2) (o := Wr2)
    (L := Sum.inr (.ddlv (0 : Fin 4) (1 : Fin 4) true)) (by simp)
    (specSide_idle P4 Ga2 (by simp) rfl not_false)
    (coreLoops_at 0 (CoreProcStepN.ddlvRecv (P := P4) (Sd0.1 0) 1 true (by decide))
      (fun j hj => CoreProcStepN.ddlvIdle (P := P4) (Sd0.1 j) 0 1 true (Ne.symm hj)))
    (ANetStep.ddlv (P := P4) Sd0.2 0 1 true (by decide))
    ((System.mapIdle_step_none (wccPull_ddlv (0 : Fin 4) (1 : Fin 4) true) _).mpr rfl)
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Deliver process `2`'s `⟨DECIDED, true⟩` to process `0`; process `0` now has
the `n − f = 3` distinct senders it needs. -/
theorem step_deliver₂ :
    (hybrid P4).step (st Ga2 Sd1 Wr2) Lab.tau (PMF.pure (st Ga2 Sd2 Wr2)) := by
  refine hybrid_rendezvous P4 (e := .ddlv (0 : Fin 4) (2 : Fin 4) true) ?_
  have h := hybridPre_vis_step P4 (G := Ga2) (C := Sd1.1) (A := Sd1.2) (o := Wr2)
    (L := Sum.inr (.ddlv (0 : Fin 4) (2 : Fin 4) true)) (by simp)
    (specSide_idle P4 Ga2 (by simp) rfl not_false)
    (coreLoops_at 0 (CoreProcStepN.ddlvRecv (P := P4) (Sd1.1 0) 2 true (by decide))
      (fun j hj => CoreProcStepN.ddlvIdle (P := P4) (Sd1.1 j) 0 2 true (Ne.symm hj)))
    (ANetStep.ddlv (P := P4) Sd1.2 0 2 true (by decide))
    ((System.mapIdle_step_none (wccPull_ddlv (0 : Fin 4) (2 : Fin 4) true) _).mpr rfl)
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Step 21: the decision (`retABA 0 true`, visible) -/

/-- Process `0` returns `true`: it has multicast `⟨DECIDED, true⟩` — the
network's conjunct — and holds `n − f = 3` distinct DECIDED-true receipts — the
round loop's. The whole 21-step run, every step a Dirac except the single
`ε`-mass coin flip, carries positive probability and ends in a genuine
`retABA`. -/
theorem step_retABA :
    (hybrid P4).step (st Ga2 Sd2 Wr2) (Lab.retABA (0 : Fin 4) true)
      (PMF.pure (st Ga2 Sfin Wr2)) := by
  refine hybrid_vis P4 (by simp) ?_
  have h := hybridPre_vis_step P4 (G := Ga2) (C := Sd2.1) (A := Sd2.2) (o := Wr2)
    (L := Sum.inl (Lab.retABA (0 : Fin 4) true)) (by simp)
    (specSide_idle P4 Ga2 (by simp) rfl not_false)
    (coreLoops_at 0 (CoreProcStepN.ret (P := P4) (Sd2.1 0) true (by decide) (by decide))
      (fun j hj => CoreProcStepN.retABAIdle (P := P4) (Sd2.1 j) 0 true (Ne.symm hj)))
    (ANetStep.retABA (P := P4) Sd2.2 0 true (by decide))
    (wccIdle Wr2 (by simp) rfl (by simp [Lab.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### A `fail` broadcast: all four factors corrupt in sync -/

/-- Corruption of process `0`: the visible `fail 0` synchronises every factor —
the round specifications and the coin oracle by global broadcast, the ABA-side
network by its own `fail` row, which carries the budget guard, and the round
loops by standing still (deviation D1). -/
theorem step_fail :
    (hybrid P4).step (st G0 S0 W0) (Lab.fail (0 : Fin 4))
      (PMF.pure (st Gf Sf Wf)) := by
  refine hybrid_vis P4 (by simp) ?_
  have h := hybridPre_vis_step P4 (G := G0) (C := S0.1) (A := S0.2) (o := W0)
    (L := Sum.inl (Lab.fail (0 : Fin 4))) (by simp)
    (specSide_fail P4 G0 0)
    (fun i => CoreProcStepN.failIdle (P := P4) (S0.1 i) 0)
    (ANetStep.fail (P := P4) S0.2 0)
    ((System.mapIdle_step_some (wccPull_inl (Lab.fail (0 : Fin 4))) _).mpr
      (wccFamily_fail P4 W0 0))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

end NonVacuity

end ABA
end PLTS
