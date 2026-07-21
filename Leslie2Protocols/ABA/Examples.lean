/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2Protocols.ABA.Hybrid

/-!
# Non-vacuity witnesses for the ABA hybrids (M7)

Machine-checked evidence that the composed system `hybridSpec P` can actually
execute a nontrivial prefix: the refinement theorem `ABA.substitution` about it
is not vacuously true through an immediate deadlock.

We fix the small parameter set `P4` (`n = 4`, `f = 1`, `ε = 0`) and exhibit a
concrete run of eight steps of `hybridSpec P4` starting from its initial state:

* `step_callABA₀/₁/₂` — three external input handshakes (`callABA`, *visible*:
  Core takes its `input` constructor, both instance families idle);
* `step_callG₀/₁/₂` — three GBCA calls (`callG 0`, *hidden* to `τ`: Core emits,
  the GBCA round-`0` instance takes its owned `call`, WCC idles);
* `step_bindSet` — the GBCA `bindSet` internal transition (a family `τ`, `n − f`
  quorum met at `n = 4, f = 1` by the three callers, interleaved in `parallel`);
* `step_retG₀` — one GBCA `A`-return handshake (`retG 0`, *hidden* to `τ`).

Plus `step_fail` — a `fail` broadcast synchronising all three components.

Every guard on these closed numeric states discharges by `decide`/`rfl`/`simp`;
the successor distributions collapse through `prodPMF_pure_pure` and
`PMF.pure_map`.
-/

namespace PLTS
namespace ABA

/-- A concrete parameter set: four processes, corruption budget one, zero-goodness
coin (`2 * 0 ≤ 1` holds, and the coin never flips along the witnessed run). -/
def P4 : Params := ⟨4, 1, by omega, 0, by simp⟩

/-- Collapse a product of two Dirac distributions to a single Dirac. -/
theorem prodPMF_pure_pure {α β : Type*} (a : α) (b : β) :
    prodPMF (PMF.pure a) (PMF.pure b) = PMF.pure (a, b) := by
  rw [prodPMF_pure_left, PMF.pure_map]

/-! ### Named states of the run -/

/-- The GBCA family state: all instances initial. -/
def G0 : ℕ → GBCA.SpecState 4 := fun _ => GBCA.SpecState.initial 4

/-- The GBCA *implementation* family state: all instances initial (for the
`hybridImpl` witness). -/
def GI0 : ℕ → GBCA.ImplState 4 := fun _ => GBCA.ImplState.initial 4

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

/-- GBCA-family state after `bindSet` fixes the round-`0` bound value to `true`. -/
def Gb : ℕ → GBCA.SpecState 4 := Function.update G3 0 { G3 0 with bind := some true }

/-- GBCA-family state after process `0`'s round-`0` `A`-return. -/
def Gr : ℕ → GBCA.SpecState 4 :=
  Function.update Gb 0
    { Gb 0 with grade := some true, ret := Function.update (Gb 0).ret 0 true }

/-- Core state after process `0`'s round-`0` GBCA return. -/
def Cr : CoreState 4 :=
  Cc3.setProc 0
    { Cc3.procs 0 with est := some true, lastGrade := some (.A true), phase := .toCallW }

/-- The three components after a synchronised `fail 0` broadcast. -/
def Gf : ℕ → GBCA.SpecState 4 := fun r => (G0 r).corrupt P4 (0 : Fin 4)
def Wf : ℕ → WCC.SpecState 4 := fun r => (W0 r).corrupt P4 (0 : Fin 4)
def Cf : CoreState 4 := C0.corrupt P4 (0 : Fin 4)

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

/-! ### Step 7: the GBCA `bindSet` internal transition (family `τ`, interleaved) -/

/-- With three of four processes having called, the round-`0` GBCA quorum
`n − f = 3` is met, so `bindSet` fixes the bound value. This is a family `τ`,
interleaved on the GBCA side while the context holds. -/
theorem step_bindSet :
    (hybridSpec P4).step (G3, (Cc3, W0)) Lab.tau
      (PMF.pure (Gb, (Cc3, W0))) := by
  refine Or.inr ⟨by simp, ?_⟩
  refine Or.inr (Or.inl ⟨rfl, PMF.pure Gb, ?_, ?_⟩)
  · refine Or.inl ⟨rfl, 0, _, ?_, by rw [PMF.pure_map]; rfl⟩
    exact GBCA.Step.bindSet (P := P4) (r := 0) (G3 0) true
      (by unfold GBCA.SpecState.quorum; decide) ⟨(0 : Fin 4), by decide, by decide⟩ rfl
  · rw [prodPMF_pure_pure]

/-! ### Step 8: process `0`'s hidden GBCA `A`-return (`retG 0`, hidden to `τ`) -/

/-- Process `0` takes an `A`-return of the bound value `true`: the GBCA instance
locks the grade and records the return, Core adopts the estimate and heads for
the coin. Hidden to `τ`. -/
theorem step_retG₀ :
    (hybridSpec P4).step (Gb, (Cc3, W0)) Lab.tau
      (PMF.pure (Gr, (Cr, W0))) := by
  refine Or.inl ⟨rfl, Lab.retG 0 (0 : Fin 4) (.A true) true, by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure Gr, PMF.pure (Cr, W0), ?_, ?_, ?_⟩
  · refine Or.inr (Or.inl ⟨0, rfl, _, ?_, by rw [PMF.pure_map]; rfl⟩)
    exact GBCA.Step.retA (P := P4) (r := 0) (Gb 0) (0 : Fin 4) true rfl (Or.inl rfl) rfl
  · refine Or.inl ⟨by decide, PMF.pure Cr, PMF.pure W0, ?_, ?_, ?_⟩
    · exact CoreStep.retG (P := P4) Cc3 0 (0 : Fin 4) (.A true) true rfl rfl
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

/-! ### The implementation-side hybrid also starts -/

/-- The initial hybrid-impl state is `(GI0, (C0, W0))`. -/
theorem hybridImpl_init : (hybridImpl P4).init = (GI0, (C0, W0)) := rfl

/-- `hybridImpl P4` executes the same first external input handshake: the GBCA
implementation family idles on `callABA` exactly as its specification does, so
non-vacuity holds on the implementation side too. -/
theorem hybridImpl_step_callABA₀ :
    (hybridImpl P4).step (GI0, (C0, W0)) (Lab.callABA (0 : Fin 4) true)
      (PMF.pure (GI0, (C1, W0))) := by
  refine Or.inr ⟨by simp, ?_⟩
  refine Or.inl ⟨by decide, PMF.pure GI0, PMF.pure (C1, W0), ?_, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
  · refine Or.inl ⟨by decide, PMF.pure C1, PMF.pure W0, ?_, ?_, ?_⟩
    · exact CoreStep.input (P := P4) C0 (0 : Fin 4) true rfl
    · exact Or.inr (Or.inr (Or.inr ⟨by decide, rfl, by simp [Lab.isFail], rfl⟩))
    · rw [prodPMF_pure_pure]
  · rw [prodPMF_pure_pure]

end ABA
end PLTS
