/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Hybrid
import Leslie2Protocols.Framework.SyncProduct

/-!
# Non-vacuity witnesses for the analysis-side composition

Machine-checked evidence that the composed system `hybridSpec P` can actually
execute a nontrivial prefix: the core simulation `ABA.coreSim` about it is not
vacuously true through an immediate deadlock.

We fix the small parameter set `P4` (`n = 4`, `f = 1`, `ε = 1/2`) and exhibit a
concrete **21-step run of `hybridSpec P4` that reaches a genuine `retABA`** — a
complete decision — starting from its initial state:

* `step_callABA₀/₁/₂` — three external input handshakes (`callABA`, *visible*:
  Core takes its `input` constructor, both instance families idle);
* `step_callG₀/₁/₂` — three GBCA calls (`callG 0`, *hidden* to `τ`: Core emits,
  the GBCA round-`0` instance takes its owned `call`, WCC idles);
* `step_bindUnset` — the GBCA `bindUnset` internal transition killing the bit
  `false` (a family `τ`, `n − f` quorum met at `n = 4, f = 1` by the three
  callers of `true`, interleaved in `parallel`);
* `step_retG₀/₁/₂` — the three GBCA `A`-return handshakes (`retG 0`, *hidden*),
  the first locking the round grade to the `A`-side;
* `step_callW₀/₁/₂` — the three coin-call handshakes (`callW 0`, *hidden*);
* `step_flip` + `step_flip_mass` — the coin `flip`, the run's **single
  probabilistic step**: the successor lands on the `bit true` branch (the one
  agreeing with the bound value) with mass exactly `ε = 1/2 > 0`;
* `step_retW₀/₁/₂` — the three coin-return handshakes (`retW 0`, *hidden*); each
  fires the fused round advance (deviation D10) that multicasts
  `⟨DECIDED, true⟩`, giving three distinct DECIDED-true senders;
* `step_deliver₀/₁/₂` — the adversary delivers all three receipts to process `0`
  (Core internal `τ`), meeting the `n − f = 3` return quorum;
* `step_retABA` — process `0` fires `retABA 0 true`: the decision.

Plus `step_fail` — a `fail` broadcast synchronising all three components.

Because every step but the flip is a Dirac and the flip's chosen branch has mass
`ε > 0`, the whole path is a positive-probability execution: a product of Diracs
times one `ε` factor. Every guard on these closed numeric states discharges by
`decide`/`rfl`/`simp`; the Dirac successor distributions collapse through
`prodPMF_pure_pure` and `PMF.pure_map`, and the flip's branch mass through
`prodPMF_pure_left_apply` and `map_apply_inj`.
-/

namespace PLTS
namespace ABA

/-- A concrete parameter set: four processes, corruption budget one, and a
never-failing `ε = 1/2` coin, so that each bit outcome carries positive mass
(`ε = 1/2`) and the witnessed `flip` can take the `bit true` branch.
`2 * ε + δ ≤ 1` holds with equality (`2 * (1/2) + 0 = 1`); the adversarial `⊤`
outcome and the failure outcome then both have mass `0`. -/
noncomputable def P4 : Params := ⟨4, 1, by omega, 1 / 2, 0, by
  rw [add_zero, one_div, ENNReal.mul_inv_cancel] <;> simp⟩

/-! ### Named states of the run -/

/-- The GBCA family state: all instances initial. -/
def G0 : ℕ → GBCA.SpecState 4 := fun _ => GBCA.SpecState.initial 4

/-- The WCC family state: all instances initial. -/
def W0 : ℕ → WCC.SpecState 4 := fun _ => WCC.SpecState.initial 4

/-- The Core state: initial. -/
def C0 : CoreState 4 := CoreState.initial 4

/-- Core update performed by a `callABA id true` input: enter round `0`, ready
to call GBCA. -/
def cInput (id : Fin 4) (s : CoreState 4) : CoreState 4 :=
  s.setProc id { s.procs id with
    input := some true, est := some true, round := 0, phase := .toCallG }

/-- Core update performed by a `callG r id` emit: advance to `awaitG`. -/
def cCallG (id : Fin 4) (s : CoreState 4) : CoreState 4 :=
  s.setProc id { s.procs id with phase := .awaitG }

/-- GBCA-family update performed by a round-`0` `call id true`: record the input
in the round-`0` instance. -/
def gCall (id : Fin 4) (s : ℕ → GBCA.SpecState 4) : ℕ → GBCA.SpecState 4 :=
  Function.update s 0 { s 0 with call := Function.update (s 0).call id (some true) }

/-- Core states after the three inputs. -/
def C1 : CoreState 4 := cInput 0 C0
def C2 : CoreState 4 := cInput 1 C1
def C3 : CoreState 4 := cInput 2 C2

/-- GBCA-family states after the three round-`0` calls. -/
def G1 : ℕ → GBCA.SpecState 4 := gCall 0 G0
def G2 : ℕ → GBCA.SpecState 4 := gCall 1 G1
def G3 : ℕ → GBCA.SpecState 4 := gCall 2 G2

/-- Core states after the three round-`0` calls. -/
def Cc1 : CoreState 4 := cCallG 0 C3
def Cc2 : CoreState 4 := cCallG 1 Cc1
def Cc3 : CoreState 4 := cCallG 2 Cc2

/-- GBCA-family state after `bindUnset` kills the round-`0` bit `false`,
sparing `true`. -/
def Gb : ℕ → GBCA.SpecState 4 := Function.update G3 0 { G3 0 with dead := {false} }

/-- GBCA-family state after process `0`'s round-`0` `A`-return. -/
def Gr : ℕ → GBCA.SpecState 4 :=
  Function.update Gb 0
    { Gb 0 with grade := some true, ret := Function.update (Gb 0).ret 0 true }

/-- Core state after process `0`'s round-`0` GBCA return. -/
def Cr : CoreState 4 :=
  Cc3.setProc 0
    { Cc3.procs 0 with est := some true, lastGrade := some (.A true), phase := .toCallW }

/-! #### Continuation states: rounds `1,2` return, all call the coin, it
flips to `bit true`, all return, DECIDED gossip carries `0` to a decision. -/

/-- A further round-`0` GBCA `A`-return by process `id` (grade already locked
`some true` by process `0`'s return). -/
def gRetA (id : Fin 4) (s : ℕ → GBCA.SpecState 4) : ℕ → GBCA.SpecState 4 :=
  Function.update s 0 { s 0 with grade := some true, ret := Function.update (s 0).ret id true }

/-- Core update by process `id`'s round-`0` GBCA return (adopt estimate `true`,
head for the coin). -/
def cRetG (id : Fin 4) (s : CoreState 4) : CoreState 4 :=
  s.setProc id { s.procs id with est := some true, lastGrade := some (.A true), phase := .toCallW }

/-- Core update by a `callW r id` emit: advance to `awaitW`. -/
def cCallW (id : Fin 4) (s : CoreState 4) : CoreState 4 :=
  s.setProc id { s.procs id with phase := .awaitW }

/-- WCC-family update by a round-`0` `call id`: record `id` as a caller. -/
def wCall (id : Fin 4) (s : ℕ → WCC.SpecState 4) : ℕ → WCC.SpecState 4 :=
  Function.update s 0 { s 0 with called := Function.update (s 0).called id true }

/-- WCC-family update by the round-`0` coin `flip` landing on `bit true`. -/
def wFlip (s : ℕ → WCC.SpecState 4) : ℕ → WCC.SpecState 4 :=
  Function.update s 0 { s 0 with val := .bit true }

/-- WCC-family update by a round-`0` `ret id true`. -/
def wRet (id : Fin 4) (s : ℕ → WCC.SpecState 4) : ℕ → WCC.SpecState 4 :=
  Function.update s 0 { s 0 with ret := Function.update (s 0).ret id true }

/-- GBCA family after processes `1,2` also `A`-return round `0`. -/
def Ga1 : ℕ → GBCA.SpecState 4 := gRetA 1 Gr
def Ga2 : ℕ → GBCA.SpecState 4 := gRetA 2 Ga1

/-- Core after processes `1,2` return round `0`'s GBCA. -/
def Cq1 : CoreState 4 := cRetG 1 Cr
def Cq2 : CoreState 4 := cRetG 2 Cq1

/-- Core after all three processes call the coin. -/
def Cw0 : CoreState 4 := cCallW 0 Cq2
def Cw1 : CoreState 4 := cCallW 1 Cw0
def Cw2 : CoreState 4 := cCallW 2 Cw1

/-- WCC family after all three processes call the coin. -/
def Wc0 : ℕ → WCC.SpecState 4 := wCall 0 W0
def Wc1 : ℕ → WCC.SpecState 4 := wCall 1 Wc0
def Wc2 : ℕ → WCC.SpecState 4 := wCall 2 Wc1

/-- WCC family after the coin flips to `bit true`. -/
def Wfl : ℕ → WCC.SpecState 4 := wFlip Wc2

/-- WCC family after all three processes receive the coin. -/
def Wr0 : ℕ → WCC.SpecState 4 := wRet 0 Wfl
def Wr1 : ℕ → WCC.SpecState 4 := wRet 1 Wr0
def Wr2 : ℕ → WCC.SpecState 4 := wRet 2 Wr1

/-- Core after all three return the coin (each multicasts `⟨DECIDED, true⟩` via
the fused `stepRound`, having held an `A true` grade). -/
def Cs0 : CoreState 4 := Cw2.stepRound 0 true
def Cs1 : CoreState 4 := Cs0.stepRound 1 true
def Cs2 : CoreState 4 := Cs1.stepRound 2 true

/-- Core after the adversary delivers all three `⟨DECIDED, true⟩` to process 0. -/
def Cd0 : CoreState 4 := Cs2.deliverDecided 0 0 true
def Cd1 : CoreState 4 := Cd0.deliverDecided 0 1 true
def Cd2 : CoreState 4 := Cd1.deliverDecided 0 2 true

/-- Core after process `0` fires `retABA 0 true`. -/
def Cfin : CoreState 4 := Cd2.setProc 0 { Cd2.procs 0 with returned := true }

/-- The three components after a synchronised `fail 0` broadcast. -/
noncomputable def Gf : ℕ → GBCA.SpecState 4 := fun r => (G0 r).corrupt P4 (0 : Fin 4)
noncomputable def Wf : ℕ → WCC.SpecState 4 := fun r => (W0 r).corrupt P4 (0 : Fin 4)
noncomputable def Cf : CoreState 4 := C0.corrupt P4 (0 : Fin 4)

/-- The initial hybrid state is `(G0, (C0, W0))`. -/
theorem hybridSpec_init : (hybridSpec P4).init = (G0, (C0, W0)) := rfl

/-! ### Step 1–3: the external input handshakes (`callABA`, visible) -/

/-- First input: process `0` receives `callABA 0 true`. Visible label; Core
takes `input`, both families idle. -/
theorem step_callABA₀ :
    (hybridSpec P4).step (G0, (C0, W0)) (Lab.callABA (0 : Fin 4) true)
      (PMF.pure (G0, (C1, W0))) := by
  refine Or.inr ⟨by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure G0, PMF.pure (C1, W0), ?_, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
  · refine Or.inl ⟨by decide, PMF.pure C1, PMF.pure W0, ?_, ?_, ?_⟩
    · exact CoreStep.input (P := P4) C0 (0 : Fin 4) true rfl
    · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

/-- Second input: process `1`. -/
theorem step_callABA₁ :
    (hybridSpec P4).step (G0, (C1, W0)) (Lab.callABA (1 : Fin 4) true)
      (PMF.pure (G0, (C2, W0))) := by
  refine Or.inr ⟨by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure G0, PMF.pure (C2, W0), ?_, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
  · refine Or.inl ⟨by decide, PMF.pure C2, PMF.pure W0, ?_, ?_, ?_⟩
    · exact CoreStep.input (P := P4) C1 (1 : Fin 4) true rfl
    · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

/-- Third input: process `2`. -/
theorem step_callABA₂ :
    (hybridSpec P4).step (G0, (C2, W0)) (Lab.callABA (2 : Fin 4) true)
      (PMF.pure (G0, (C3, W0))) := by
  refine Or.inr ⟨by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure G0, PMF.pure (C3, W0), ?_, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
  · refine Or.inl ⟨by decide, PMF.pure C3, PMF.pure W0, ?_, ?_, ?_⟩
    · exact CoreStep.input (P := P4) C2 (2 : Fin 4) true rfl
    · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

/-! ### Step 4: first hidden GBCA call (`callG 0`, hidden to `τ`) -/

/-- First GBCA call: Core emits `callG 0 0 true`, the GBCA round-`0` instance
takes its owned `call`, WCC idles; the whole handshake is hidden to `τ`. -/
theorem step_callG₀ :
    (hybridSpec P4).step (G0, (C3, W0)) Lab.tau
      (PMF.pure (G1, (Cc1, W0))) := by
  refine Or.inl ⟨rfl, Lab.callG 0 (0 : Fin 4) true, by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure G1, PMF.pure (Cc1, W0), ?_, ?_, ?_⟩
  · exact Or.inr (Or.inl ⟨0, rfl, _,
      GBCA.Step.call (P := P4) (r := 0) (G0 0) (0 : Fin 4) true rfl, by rw [PMF.pure_map]; rfl⟩)
  · refine Or.inl ⟨by decide, PMF.pure Cc1, PMF.pure W0, ?_, ?_, ?_⟩
    · exact CoreStep.callG (P := P4) C3 0 (0 : Fin 4) true rfl rfl rfl
    · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

/-- Second GBCA call: process `1`. -/
theorem step_callG₁ :
    (hybridSpec P4).step (G1, (Cc1, W0)) Lab.tau
      (PMF.pure (G2, (Cc2, W0))) := by
  refine Or.inl ⟨rfl, Lab.callG 0 (1 : Fin 4) true, by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure G2, PMF.pure (Cc2, W0), ?_, ?_, ?_⟩
  · exact Or.inr (Or.inl ⟨0, rfl, _,
      GBCA.Step.call (P := P4) (r := 0) (G1 0) (1 : Fin 4) true rfl, by rw [PMF.pure_map]; rfl⟩)
  · refine Or.inl ⟨by decide, PMF.pure Cc2, PMF.pure W0, ?_, ?_, ?_⟩
    · exact CoreStep.callG (P := P4) Cc1 0 (1 : Fin 4) true rfl rfl rfl
    · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

/-- Third GBCA call: process `2`. Now the round-`0` instance holds three inputs. -/
theorem step_callG₂ :
    (hybridSpec P4).step (G2, (Cc2, W0)) Lab.tau
      (PMF.pure (G3, (Cc3, W0))) := by
  refine Or.inl ⟨rfl, Lab.callG 0 (2 : Fin 4) true, by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure G3, PMF.pure (Cc3, W0), ?_, ?_, ?_⟩
  · exact Or.inr (Or.inl ⟨0, rfl, _,
      GBCA.Step.call (P := P4) (r := 0) (G2 0) (2 : Fin 4) true rfl, by rw [PMF.pure_map]; rfl⟩)
  · refine Or.inl ⟨by decide, PMF.pure Cc3, PMF.pure W0, ?_, ?_, ?_⟩
    · exact CoreStep.callG (P := P4) Cc2 0 (2 : Fin 4) true rfl rfl rfl
    · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

/-! ### Step 7: the GBCA `bindUnset` internal transition (family `τ`, interleaved) -/

/-- With three of four processes having called, the round-`0` GBCA quorum
`n − f = 3` is met, so `bindUnset` kills the bit `false` (the three callers of
`true` supply the `f + 1` support for the surviving bit). This is a family `τ`,
interleaved on the GBCA side while the context holds. -/
theorem step_bindUnset :
    (hybridSpec P4).step (G3, (Cc3, W0)) Lab.tau
      (PMF.pure (Gb, (Cc3, W0))) := by
  refine Or.inr ⟨by simp, ?_⟩
  refine Or.inr (Or.inl ⟨rfl, PMF.pure Gb, ?_, ?_⟩)
  · refine Or.inl ⟨rfl, 0, _, ?_, by rw [PMF.pure_map]; rfl⟩
    exact GBCA.Step.bindUnset (P := P4) (r := 0) (G3 0) false
      (by unfold GBCA.SpecState.quorum; decide) (by decide) (by decide)
  · rw [prodPMF_pure_pure]

/-! ### Step 8: process `0`'s hidden GBCA `A`-return (`retG 0`, hidden to `τ`) -/

/-- Process `0` takes an `A`-return of the bound value `true`: the GBCA instance
locks the grade and records the return, Core adopts the estimate and heads for
the coin. Hidden to `τ`. -/
theorem step_retG₀ :
    (hybridSpec P4).step (Gb, (Cc3, W0)) Lab.tau
      (PMF.pure (Gr, (Cr, W0))) := by
  refine Or.inl ⟨rfl, Lab.retG 0 (0 : Fin 4) (.A true), by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure Gr, PMF.pure (Cr, W0), ?_, ?_, ?_⟩
  · refine Or.inr (Or.inl ⟨0, rfl, _, ?_, by rw [PMF.pure_map]; rfl⟩)
    exact GBCA.Step.retA (P := P4) (r := 0) (Gb 0) (0 : Fin 4) true (by decide) (by decide)
      (Or.inl rfl) rfl
  · refine Or.inl ⟨by decide, PMF.pure Cr, PMF.pure W0, ?_, ?_, ?_⟩
    · exact CoreStep.retG (P := P4) Cc3 0 (0 : Fin 4) (.A true) rfl rfl
    · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

/-! ### A `fail` broadcast: all three components corrupt in sync -/

/-- Corruption of process `0`: the visible `fail 0` synchronises every
component, each applying its `corrupt` transform (the GBCA/WCC families by
global broadcast, Core by its `fail` constructor). -/
theorem step_fail :
    (hybridSpec P4).step (G0, (C0, W0)) (Lab.fail (0 : Fin 4))
      (PMF.pure (Gf, (Cf, Wf))) := by
  refine Or.inr ⟨by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure Gf, PMF.pure (Cf, Wf), ?_, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inl ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
  · refine Or.inl ⟨by decide, PMF.pure Cf, PMF.pure Wf, ?_, ?_, ?_⟩
    · exact CoreStep.fail (P := P4) C0 (0 : Fin 4)
    · exact Or.inr (Or.inr (Or.inl ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

/-! ### Steps 9–10: processes `1,2` also `A`-return round `0` (hidden `retG`) -/

/-- Process `1`'s round-`0` GBCA `A`-return. -/
theorem step_retG₁ :
    (hybridSpec P4).step (Gr, (Cr, W0)) Lab.tau
      (PMF.pure (Ga1, (Cq1, W0))) := by
  refine Or.inl ⟨rfl, Lab.retG 0 (1 : Fin 4) (.A true), by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure Ga1, PMF.pure (Cq1, W0), ?_, ?_, ?_⟩
  · refine Or.inr (Or.inl ⟨0, rfl, _, ?_, by rw [PMF.pure_map]; rfl⟩)
    exact GBCA.Step.retA (P := P4) (r := 0) (Gr 0) (1 : Fin 4) true (by decide) (by decide)
      (Or.inr rfl) (by decide)
  · refine Or.inl ⟨by decide, PMF.pure Cq1, PMF.pure W0, ?_, ?_, ?_⟩
    · exact CoreStep.retG (P := P4) Cr 0 (1 : Fin 4) (.A true) (by decide) (by decide)
    · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

/-- Process `2`'s round-`0` GBCA `A`-return. -/
theorem step_retG₂ :
    (hybridSpec P4).step (Ga1, (Cq1, W0)) Lab.tau
      (PMF.pure (Ga2, (Cq2, W0))) := by
  refine Or.inl ⟨rfl, Lab.retG 0 (2 : Fin 4) (.A true), by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure Ga2, PMF.pure (Cq2, W0), ?_, ?_, ?_⟩
  · refine Or.inr (Or.inl ⟨0, rfl, _, ?_, by rw [PMF.pure_map]; rfl⟩)
    exact GBCA.Step.retA (P := P4) (r := 0) (Ga1 0) (2 : Fin 4) true (by decide) (by decide)
      (Or.inr rfl) (by decide)
  · refine Or.inl ⟨by decide, PMF.pure Cq2, PMF.pure W0, ?_, ?_, ?_⟩
    · exact CoreStep.retG (P := P4) Cq1 0 (2 : Fin 4) (.A true) (by decide) (by decide)
    · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

/-! ### Steps 11–13: all three call the coin (hidden `callW` handshakes) -/

/-- Process `0` calls the round-`0` coin (`callW`, hidden). -/
theorem step_callW₀ :
    (hybridSpec P4).step (Ga2, (Cq2, W0)) Lab.tau
      (PMF.pure (Ga2, (Cw0, Wc0))) := by
  refine Or.inl ⟨rfl, Lab.callW 0 (0 : Fin 4), by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure Ga2, PMF.pure (Cw0, Wc0), ?_, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
  · refine Or.inl ⟨by decide, PMF.pure Cw0, PMF.pure Wc0, ?_, ?_, ?_⟩
    · exact CoreStep.callW (P := P4) Cq2 0 (0 : Fin 4) (by decide) (by decide)
    · exact Or.inr (Or.inl ⟨0, rfl, _,
        WCC.Step.call (P := P4) (r := 0) (W0 0) (0 : Fin 4) (by decide),
        by rw [PMF.pure_map]; rfl⟩)
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

/-- Process `1` calls the round-`0` coin. -/
theorem step_callW₁ :
    (hybridSpec P4).step (Ga2, (Cw0, Wc0)) Lab.tau
      (PMF.pure (Ga2, (Cw1, Wc1))) := by
  refine Or.inl ⟨rfl, Lab.callW 0 (1 : Fin 4), by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure Ga2, PMF.pure (Cw1, Wc1), ?_, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
  · refine Or.inl ⟨by decide, PMF.pure Cw1, PMF.pure Wc1, ?_, ?_, ?_⟩
    · exact CoreStep.callW (P := P4) Cw0 0 (1 : Fin 4) (by decide) (by decide)
    · exact Or.inr (Or.inl ⟨0, rfl, _,
        WCC.Step.call (P := P4) (r := 0) (Wc0 0) (1 : Fin 4) (by decide),
        by rw [PMF.pure_map]; rfl⟩)
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

/-- Process `2` calls the round-`0` coin; now three callers meet the `> f`
resolution threshold. -/
theorem step_callW₂ :
    (hybridSpec P4).step (Ga2, (Cw1, Wc1)) Lab.tau
      (PMF.pure (Ga2, (Cw2, Wc2))) := by
  refine Or.inl ⟨rfl, Lab.callW 0 (2 : Fin 4), by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure Ga2, PMF.pure (Cw2, Wc2), ?_, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
  · refine Or.inl ⟨by decide, PMF.pure Cw2, PMF.pure Wc2, ?_, ?_, ?_⟩
    · exact CoreStep.callW (P := P4) Cw1 0 (2 : Fin 4) (by decide) (by decide)
    · exact Or.inr (Or.inl ⟨0, rfl, _,
        WCC.Step.call (P := P4) (r := 0) (Wc1 0) (2 : Fin 4) (by decide),
        by rw [PMF.pure_map]; rfl⟩)
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

/-! ### Step 14: the coin `flip` (the run's single probabilistic step) -/

/-- The WCC round-`0` family distribution produced by the coin `flip`: the
`wccPMF` outcome resolves instance `0`'s `val`. -/
noncomputable def flipWr : PMF (ℕ → WCC.SpecState 4) :=
  (P4.wccPMF.map (fun o => { Wc2 0 with val := o.toTVal })).map
    (Function.update Wc2 0)

/-- The full hybrid successor distribution of the coin flip: the two idle
components stay put (Dirac), the WCC family resolves the coin. -/
noncomputable def flipμ :
    PMF ((ℕ → GBCA.SpecState 4) × (CoreState 4 × (ℕ → WCC.SpecState 4))) :=
  prodPMF (PMF.pure Ga2) (prodPMF (PMF.pure Cw2) flipWr)

/-- The coin `flip` is a legal hidden (`τ`) transition of the composed system:
GBCA and Core idle, the WCC round-`0` instance resolves `val` by `wccPMF`
(threshold met by the three callers). -/
theorem step_flip :
    (hybridSpec P4).step (Ga2, (Cw2, Wc2)) Lab.tau flipμ := by
  refine Or.inr ⟨by simp, ?_⟩
  refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure Cw2) flipWr, ?_, rfl⟩)
  refine Or.inr (Or.inr ⟨rfl, flipWr, ?_, rfl⟩)
  refine Or.inl ⟨rfl, 0,
    P4.wccPMF.map (fun o => { Wc2 0 with val := o.toTVal }), ?_, rfl⟩
  exact WCC.Step.flip (P := P4) (r := 0) (Wc2 0)
    (by unfold WCC.SpecState.threshold; decide) (by decide)

/-- The flip lands on the `bit true` branch — the outcome that agrees with the
bound value — with mass exactly `ε = 1/2 > 0`. This is the run's single
`ε` factor; every other step is Dirac, so the whole path has positive
probability. -/
theorem step_flip_mass : flipμ (Ga2, (Cw2, Wfl)) = P4.ε := by
  have hup : Function.Injective (Function.update Wc2 0) := by
    intro a b h; have h0 := congrFun h 0; simpa using h0
  have hg : Function.Injective
      (fun o : CoinOutcome => ({ Wc2 0 with val := o.toTVal } : WCC.SpecState 4)) :=
    fun _ _ h => CoinOutcome.toTVal_injective (congrArg (·.val) h)
  unfold flipμ flipWr
  rw [prodPMF_pure_left_apply, prodPMF_pure_left_apply,
    show (Wfl : ℕ → WCC.SpecState 4)
      = Function.update Wc2 0 { Wc2 0 with val := TVal.bit true } from rfl,
    map_apply_inj hup,
    show ({ Wc2 0 with val := TVal.bit true } : WCC.SpecState 4)
      = (fun o => { Wc2 0 with val := o.toTVal }) (CoinOutcome.bit true) from rfl,
    map_apply_inj hg, Params.wccPMF_apply_bit]

/-! ### Steps 15–17: all three receive the coin (`retW`); each multicasts
`⟨DECIDED, true⟩` via the fused round advance (deviation D10). -/

/-- Process `0` receives the coin and multicasts `⟨DECIDED, true⟩`. -/
theorem step_retW₀ :
    (hybridSpec P4).step (Ga2, (Cw2, Wfl)) Lab.tau
      (PMF.pure (Ga2, (Cs0, Wr0))) := by
  refine Or.inl ⟨rfl, Lab.retW 0 (0 : Fin 4) true, by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure Ga2, PMF.pure (Cs0, Wr0), ?_, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
  · refine Or.inl ⟨by decide, PMF.pure Cs0, PMF.pure Wr0, ?_, ?_, ?_⟩
    · exact CoreStep.retW (P := P4) Cw2 0 (0 : Fin 4) true (by decide) (by decide)
    · exact Or.inr (Or.inl ⟨0, rfl, _,
        WCC.Step.ret (P := P4) (r := 0) (Wfl 0) (0 : Fin 4) true (Or.inr (by decide)) (by decide),
        by rw [PMF.pure_map]; rfl⟩)
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

/-- Process `1` receives the coin and multicasts `⟨DECIDED, true⟩`. -/
theorem step_retW₁ :
    (hybridSpec P4).step (Ga2, (Cs0, Wr0)) Lab.tau
      (PMF.pure (Ga2, (Cs1, Wr1))) := by
  refine Or.inl ⟨rfl, Lab.retW 0 (1 : Fin 4) true, by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure Ga2, PMF.pure (Cs1, Wr1), ?_, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
  · refine Or.inl ⟨by decide, PMF.pure Cs1, PMF.pure Wr1, ?_, ?_, ?_⟩
    · exact CoreStep.retW (P := P4) Cs0 0 (1 : Fin 4) true (by decide) (by decide)
    · exact Or.inr (Or.inl ⟨0, rfl, _,
        WCC.Step.ret (P := P4) (r := 0) (Wr0 0) (1 : Fin 4) true (Or.inr (by decide)) (by decide),
        by rw [PMF.pure_map]; rfl⟩)
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

/-- Process `2` receives the coin and multicasts `⟨DECIDED, true⟩`; now three
distinct senders hold `⟨DECIDED, true⟩`. -/
theorem step_retW₂ :
    (hybridSpec P4).step (Ga2, (Cs1, Wr1)) Lab.tau
      (PMF.pure (Ga2, (Cs2, Wr2))) := by
  refine Or.inl ⟨rfl, Lab.retW 0 (2 : Fin 4) true, by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure Ga2, PMF.pure (Cs2, Wr2), ?_, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
  · refine Or.inl ⟨by decide, PMF.pure Cs2, PMF.pure Wr2, ?_, ?_, ?_⟩
    · exact CoreStep.retW (P := P4) Cs1 0 (2 : Fin 4) true (by decide) (by decide)
    · exact Or.inr (Or.inl ⟨0, rfl, _,
        WCC.Step.ret (P := P4) (r := 0) (Wr1 0) (2 : Fin 4) true (Or.inr (by decide)) (by decide),
        by rw [PMF.pure_map]; rfl⟩)
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

/-! ### Steps 18–20: the adversary delivers the three `⟨DECIDED, true⟩` to
process `0` (Core internal `τ`). -/

/-- Deliver process `0`'s own `⟨DECIDED, true⟩`. -/
theorem step_deliver₀ :
    (hybridSpec P4).step (Ga2, (Cs2, Wr2)) Lab.tau
      (PMF.pure (Ga2, (Cd0, Wr2))) := by
  refine Or.inr ⟨by simp, ?_⟩
  refine Or.inr (Or.inr ⟨rfl, PMF.pure (Cd0, Wr2), ?_, by rw [prodPMF_pure_pure]⟩)
  refine Or.inr (Or.inl ⟨rfl, PMF.pure Cd0, ?_, by rw [prodPMF_pure_pure]⟩)
  exact CoreStep.deliver (P := P4) Cs2 (0 : Fin 4) (0 : Fin 4) true (by decide) (by decide)

/-- Deliver process `1`'s `⟨DECIDED, true⟩` to process `0`. -/
theorem step_deliver₁ :
    (hybridSpec P4).step (Ga2, (Cd0, Wr2)) Lab.tau
      (PMF.pure (Ga2, (Cd1, Wr2))) := by
  refine Or.inr ⟨by simp, ?_⟩
  refine Or.inr (Or.inr ⟨rfl, PMF.pure (Cd1, Wr2), ?_, by rw [prodPMF_pure_pure]⟩)
  refine Or.inr (Or.inl ⟨rfl, PMF.pure Cd1, ?_, by rw [prodPMF_pure_pure]⟩)
  exact CoreStep.deliver (P := P4) Cd0 (0 : Fin 4) (1 : Fin 4) true (by decide) (by decide)

/-- Deliver process `2`'s `⟨DECIDED, true⟩` to process `0`; now `0` has the
`n − f = 3` distinct senders it needs. -/
theorem step_deliver₂ :
    (hybridSpec P4).step (Ga2, (Cd1, Wr2)) Lab.tau
      (PMF.pure (Ga2, (Cd2, Wr2))) := by
  refine Or.inr ⟨by simp, ?_⟩
  refine Or.inr (Or.inr ⟨rfl, PMF.pure (Cd2, Wr2), ?_, by rw [prodPMF_pure_pure]⟩)
  refine Or.inr (Or.inl ⟨rfl, PMF.pure Cd2, ?_, by rw [prodPMF_pure_pure]⟩)
  exact CoreStep.deliver (P := P4) Cd1 (0 : Fin 4) (2 : Fin 4) true (by decide) (by decide)

/-! ### Step 21: the decision (`retABA 0 true`, visible) -/

/-- Process `0` returns `true`: it has multicast `⟨DECIDED, true⟩` and holds
`n − f = 3` distinct DECIDED-true receipts, so the return quorum is met. The
whole 21-step run — every step a Dirac except the single `ε`-mass coin flip —
carries positive probability and ends in a genuine `retABA`. -/
theorem step_retABA :
    (hybridSpec P4).step (Ga2, (Cd2, Wr2)) (Lab.retABA (0 : Fin 4) true)
      (PMF.pure (Ga2, (Cfin, Wr2))) := by
  refine Or.inr ⟨by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure Ga2, PMF.pure (Cfin, Wr2), ?_, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
  · refine Or.inl ⟨by decide, PMF.pure Cfin, PMF.pure Wr2, ?_, ?_, ?_⟩
    · exact CoreStep.ret (P := P4) Cd2 (0 : Fin 4) true (by decide) (by decide) (by decide)
    · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

end ABA
end PLTS
