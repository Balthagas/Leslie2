/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.CoreSimInv

/-!
# The core simulation's stutter rows: `Abs` preservation, and the assembly

Stage C of the proof that `coreR` is a simulation relation
(`DESIGN-CoreSim.md`), and the assembly of Stages A–C.

* **Stage C** — `Abs` preservation for the stutter rows. The abstract twin is
  ultra-lazy (D16): it is untouched by every hidden row and moves only at the
  visible ones (`callABA`/`retABA`/`fail`, handled in `CoreSim.lean`). All six
  lemmas are instances of one frame argument, `Abs.frame`.
* **Assembly** — `Inv.step`: `Inv` is preserved by every `hybridSpec` step,
  dispatching on the label class through Stage A's inversion lemmas and calling
  the matching Stage B helper (`CoreSimInv.lean`) in each case.
-/

namespace PLTS
namespace ABA

variable {P : Params}

/-! ### Stage C: `Abs` preservation for the stutter rows

Every one of `hybrid_step_tau`'s seven disjuncts is answered by a stutter — the
ultra-lazy twin (D16) is untouched by every hidden row and only moves at the
visible rows (`callABA`/`retABA`/`fail`), handled in `CoreSim.lean`. All six
lemmas below are instances of a single frame argument: `Abs` inspects only `F`,
the per-process `input`/`returned` projections, and the `g`-side `A`-lock
certificate — and each row preserves all three. -/

/-- `Abs` transfers along any frame that preserves `F`, the per-process
`input`/`returned` projections, and the `A`-certificate/holder-pin package. -/
theorem Abs.frame {P : Params} {g g' : ℕ → GBCA.SpecState P.n} {c c' : CoreState P.n}
    {w w' : ℕ → WCC.SpecState P.n} {a : SpecState P.n} (hA : Abs P g c w a)
    (hF : c'.F = c.F)
    (hin : ∀ id, (c'.procs id).input = (c.procs id).input)
    (hret : ∀ id, (c'.procs id).returned = (c.procs id).returned)
    (hAF : AbsFrame P g g' c c') :
    Abs P g' c' w' a := by
  refine ⟨hA.F_eq.trans hF.symm, fun id => (hA.ret_eq id).trans (hret id).symm,
    hA.coin_bot, ?_⟩
  rcases hA.phase with ⟨hb, hv, hcall, hghost⟩ | ⟨v, hb, hv, hcall, ⟨r, hcv⟩, hpin⟩
  · exact Or.inl ⟨hb, hv, fun id => (hcall id).trans (hin id).symm,
      fun id b h => hghost id b (by rw [← hin id]; exact h)⟩
  · exact Or.inr ⟨v, hb, hv, hcall, hAF.1 r v hcv, hAF.2 v ⟨r, hcv⟩ hpin⟩

/-- `Abs` never reads `w`: the twin never fires rule 5. -/
theorem Abs.w_swap {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w w' : ℕ → WCC.SpecState P.n} {a : SpecState P.n} (hA : Abs P g c w a) :
    Abs P g c w' a :=
  hA.frame rfl (fun _ => rfl) (fun _ => rfl) (AbsFrame.refl P g c)

/-- `bindUnset`: stutters; the row's `AbsFrame` package carries the certificates. -/
theorem Abs.step_gbcaTau {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n} (hA : Abs P g c w a)
    (hI : Inv P g c w) (r : ℕ)
    {μr : PMF (GBCA.SpecState P.n)} (hstep : GBCA.Step P r (g r) .tau μr)
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support) :
    Abs P (Function.update g r gr') c w a :=
  hA.frame rfl (fun _ => rfl) (fun _ => rfl) (Inv.step_gbcaTau hI r hstep hgr').2

/-- Core `τ` (DECIDED delivery/echo/byz injection): stutters; `F`/`procs` untouched. -/
theorem Abs.step_coreTau {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n} (hA : Abs P g c w a)
    (hI : Inv P g c w)
    {μc : PMF (CoreState P.n)} (hstep : CoreStep P c .tau μc)
    {c' : CoreState P.n} (hc' : c' ∈ μc.support) :
    Abs P g c' w a := by
  have hAF := (Inv.step_coreTau hI hstep hc').2
  have hCFrame : c'.F = c.F ∧ c'.procs = c.procs := by
    rw [coreStep_tau_iff] at hstep
    rcases hstep with ⟨i, j, b, hs, hr, rfl⟩ | ⟨id, b, hcnt, hs, rfl⟩ | ⟨id, b, hF, rfl⟩ <;>
      rw [PMF.mem_support_pure_iff] at hc' <;> subst hc'
    · exact ⟨CoreState.deliverDecided_F _ _ _ _, CoreState.deliverDecided_procs _ _ _ _⟩
    · exact ⟨CoreState.sendDecided_F _ _ _, CoreState.sendDecided_procs _ _ _⟩
    · exact ⟨CoreState.sendDecided_F _ _ _, CoreState.sendDecided_procs _ _ _⟩
  exact hA.frame hCFrame.1 (fun id => by rw [hCFrame.2]) (fun id => by rw [hCFrame.2]) hAF

/-- `callG`: stutters; `Abs` reads none of the touched fields, certificates ride the
row's `AbsFrame`. -/
theorem Abs.step_callG {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n}
    (hA : Abs P g c w a) (hI : Inv P g c w) (r : ℕ) (id : Fin P.n) (b : Bool)
    {μr : PMF (GBCA.SpecState P.n)} (hstepG : GBCA.Step P r (g r) (.callG r id b) μr)
    {μc : PMF (CoreState P.n)} (hstepC : CoreStep P c (.callG r id b) μc)
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support)
    {c' : CoreState P.n} (hc' : c' ∈ μc.support) :
    Abs P (Function.update g r gr') c' w a := by
  have hAF := (Inv.step_callG hI r id b hstepG hstepC hgr' hc').2
  have hCFrame : c'.F = c.F ∧ ∀ id', (c'.procs id').input = (c.procs id').input ∧
      (c'.procs id').returned = (c.procs id').returned := by
    rw [coreStep_callG_iff] at hstepC
    rcases hstepC with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩ <;>
      rw [PMF.mem_support_pure_iff] at hc' <;> subst hc'
    · refine ⟨CoreState.setProc_F _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [CoreState.setProc_procs_self]; exact ⟨rfl, rfl⟩
      · rw [CoreState.setProc_procs_ne _ _ _ h]; exact ⟨rfl, rfl⟩
    · exact ⟨rfl, fun id' => ⟨rfl, rfl⟩⟩
  exact hA.frame hCFrame.1 (fun id' => (hCFrame.2 id').1) (fun id' => (hCFrame.2 id').2) hAF

/-- `retG`: stutters; certificates and the holder pin ride the row's `AbsFrame`. -/
theorem Abs.step_retG {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n}
    (hA : Abs P g c w a) (hI : Inv P g c w) (r : ℕ) (id : Fin P.n) (out : GbcaOut)
    {μr : PMF (GBCA.SpecState P.n)} (hstepG : GBCA.Step P r (g r) (.retG r id out) μr)
    {μc : PMF (CoreState P.n)} (hstepC : CoreStep P c (.retG r id out) μc)
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support)
    {c' : CoreState P.n} (hc' : c' ∈ μc.support) :
    Abs P (Function.update g r gr') c' w a := by
  have hAF := (Inv.step_retG hI r id out hstepG hstepC hgr' hc').2
  have hCFrame : c'.F = c.F ∧ ∀ id', (c'.procs id').input = (c.procs id').input ∧
      (c'.procs id').returned = (c.procs id').returned := by
    rw [coreStep_retG_iff] at hstepC
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩ <;>
      rw [PMF.mem_support_pure_iff] at hc' <;> subst hc'
    · refine ⟨CoreState.setProc_F _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [CoreState.setProc_procs_self]; exact ⟨rfl, rfl⟩
      · rw [CoreState.setProc_procs_ne _ _ _ h]; exact ⟨rfl, rfl⟩
    · exact ⟨rfl, fun id' => ⟨rfl, rfl⟩⟩
  exact hA.frame hCFrame.1 (fun id' => (hCFrame.2 id').1) (fun id' => (hCFrame.2 id').2) hAF

/-- `callW`: stutters. -/
theorem Abs.step_callW {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n}
    (hA : Abs P g c w a) (hI : Inv P g c w) (r : ℕ) (id : Fin P.n)
    {μw' : PMF (WCC.SpecState P.n)} (hstepW : WCC.Step P r (w r) (.callW r id) μw')
    {μc : PMF (CoreState P.n)} (hstepC : CoreStep P c (.callW r id) μc)
    {wr' : WCC.SpecState P.n} (hwr' : wr' ∈ μw'.support)
    {c' : CoreState P.n} (hc' : c' ∈ μc.support) :
    Abs P g c' (Function.update w r wr') a := by
  have hAF := (Inv.step_callW hI r id hstepW hstepC hwr' hc').2
  have hCFrame : c'.F = c.F ∧ ∀ id', (c'.procs id').input = (c.procs id').input ∧
      (c'.procs id').returned = (c.procs id').returned := by
    rw [coreStep_callW_iff] at hstepC
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩ <;>
      rw [PMF.mem_support_pure_iff] at hc' <;> subst hc'
    · refine ⟨CoreState.setProc_F _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [CoreState.setProc_procs_self]; exact ⟨rfl, rfl⟩
      · rw [CoreState.setProc_procs_ne _ _ _ h]; exact ⟨rfl, rfl⟩
    · exact ⟨rfl, fun id' => ⟨rfl, rfl⟩⟩
  exact hA.frame hCFrame.1 (fun id' => (hCFrame.2 id').1) (fun id' => (hCFrame.2 id').2) hAF

/-- `retW`: stutters. -/
theorem Abs.step_retW {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n}
    (hA : Abs P g c w a) (hI : Inv P g c w) (r : ℕ) (id : Fin P.n) (b : Bool)
    {μw' : PMF (WCC.SpecState P.n)} (hstepW : WCC.Step P r (w r) (.retW r id b) μw')
    {μc : PMF (CoreState P.n)} (hstepC : CoreStep P c (.retW r id b) μc)
    {wr' : WCC.SpecState P.n} (hwr' : wr' ∈ μw'.support)
    {c' : CoreState P.n} (hc' : c' ∈ μc.support) :
    Abs P g c' (Function.update w r wr') a := by
  have hAF := (Inv.step_retW hI r id b hstepW hstepC hwr' hc').2
  have hCFrame : c'.F = c.F ∧ ∀ id', (c'.procs id').input = (c.procs id').input ∧
      (c'.procs id').returned = (c.procs id').returned := by
    rw [coreStep_retW_iff] at hstepC
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩ <;>
      rw [PMF.mem_support_pure_iff] at hc' <;> subst hc'
    · refine ⟨CoreState.stepRound_F _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [CoreState.stepRound_procs_self _ _ _]; exact ⟨rfl, rfl⟩
      · rw [CoreState.stepRound_procs_ne _ _ _ h]; exact ⟨rfl, rfl⟩
    · exact ⟨rfl, fun id' => ⟨rfl, rfl⟩⟩
  exact hA.frame hCFrame.1 (fun id' => (hCFrame.2 id').1) (fun id' => (hCFrame.2 id').2) hAF

/-! ### Assembly: `Inv` is preserved by every `hybridSpec` step -/

/-- **`Inv` is preserved.** Dispatches on the label class via `hybrid_step_callABA`/
`hybrid_step_retABA`/`hybrid_step_fail` (Stage A1) and `hybrid_step_tau` (Stage A2), calling
the matching `Inv.step_*` helper (Stage B) in each case. -/
theorem Inv.step {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) {l : Lab P.n} {μ : PMF (HState P)}
    (hstep : (hybridSpec P).step (g, (c, w)) l μ)
    {g' : ℕ → GBCA.SpecState P.n} {c' : CoreState P.n} {w' : ℕ → WCC.SpecState P.n}
    (hmem : (g', (c', w')) ∈ μ.support) :
    Inv P g' c' w' := by
  cases l with
  | tau =>
    rcases hybrid_step_tau P g c w μ hstep with
      ⟨r, μr, hstepG, rfl⟩ | ⟨μc, hstepC, rfl⟩ | ⟨r, μw', hstepW, rfl⟩ |
      ⟨r, id, b, μr, μc, hstepG, hstepC, rfl⟩ |
      ⟨r, id, out, μr, μc, hstepG, hstepC, rfl⟩ |
      ⟨r, id, μw', μc, hstepW, hstepC, rfl⟩ |
      ⟨r, id, b, μw', μc, hstepW, hstepC, rfl⟩
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_map_iff] at h1; rw [PMF.mem_support_pure_iff] at h2
      obtain ⟨gr', hgr', heq⟩ := h1
      have hc : c' = c := congrArg Prod.fst h2
      have hw : w' = w := congrArg Prod.snd h2
      rw [← heq, hc, hw]
      exact (Inv.step_gbcaTau hI r hstepG hgr').1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_pure_iff] at h1
      obtain ⟨h2, h3⟩ := h2
      rw [PMF.mem_support_pure_iff] at h3
      rw [h1, h3]
      exact (Inv.step_coreTau hI hstepC h2).1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_pure_iff] at h1
      obtain ⟨h2, h3⟩ := h2
      rw [PMF.mem_support_pure_iff] at h2
      rw [PMF.mem_support_map_iff] at h3
      obtain ⟨wr', hwr', heq⟩ := h3
      rw [h1, h2, ← heq]
      exact (Inv.step_wccTau hI r hstepW hwr').1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_map_iff] at h1
      obtain ⟨h2, h3⟩ := h2
      rw [PMF.mem_support_pure_iff] at h3
      obtain ⟨gr', hgr', heq⟩ := h1
      rw [← heq, h3]
      exact (Inv.step_callG hI r id b hstepG hstepC hgr' h2).1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_map_iff] at h1
      obtain ⟨h2, h3⟩ := h2
      rw [PMF.mem_support_pure_iff] at h3
      obtain ⟨gr', hgr', heq⟩ := h1
      rw [← heq, h3]
      exact (Inv.step_retG hI r id out hstepG hstepC hgr' h2).1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_pure_iff] at h1
      obtain ⟨h2, h3⟩ := h2
      rw [PMF.mem_support_map_iff] at h3
      obtain ⟨wr', hwr', heq⟩ := h3
      rw [h1, ← heq]
      exact (Inv.step_callW hI r id hstepW hstepC hwr' h2).1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_pure_iff] at h1
      obtain ⟨h2, h3⟩ := h2
      rw [PMF.mem_support_map_iff] at h3
      obtain ⟨wr', hwr', heq⟩ := h3
      rw [h1, ← heq]
      exact (Inv.step_retW hI r id b hstepW hstepC hwr' h2).1
  | callABA id b =>
    rw [hybrid_step_callABA] at hstep
    obtain ⟨μc, hstepC, rfl⟩ := hstep
    simp only [mem_support_prodPMF] at hmem
    obtain ⟨h1, h2⟩ := hmem
    rw [PMF.mem_support_pure_iff] at h1
    obtain ⟨h2, h3⟩ := h2
    rw [PMF.mem_support_pure_iff] at h3
    rw [h1, h3]
    exact (Inv.step_callABA hI id b hstepC h2).1
  | retABA id b =>
    rw [hybrid_step_retABA] at hstep
    obtain ⟨μc, hstepC, rfl⟩ := hstep
    simp only [mem_support_prodPMF] at hmem
    obtain ⟨h1, h2⟩ := hmem
    rw [PMF.mem_support_pure_iff] at h1
    obtain ⟨h2, h3⟩ := h2
    rw [PMF.mem_support_pure_iff] at h3
    rw [h1, h3]
    exact (Inv.step_retABA hI id b hstepC h2).1
  | fail id =>
    rw [hybrid_step_fail] at hstep
    subst hstep
    simp only [mem_support_prodPMF] at hmem
    obtain ⟨h1, h2⟩ := hmem
    rw [PMF.mem_support_pure_iff] at h1
    obtain ⟨h2, h3⟩ := h2
    rw [PMF.mem_support_pure_iff] at h2; rw [PMF.mem_support_pure_iff] at h3
    rw [h1, h2, h3]
    exact (Inv.step_fail hI id).1
  | callG r id b =>
    exfalso; unfold hybridSpec at hstep; rw [System.abstract_step] at hstep
    rcases hstep with ⟨hτ, -⟩ | ⟨hnotmem, -⟩
    · exact absurd hτ (by simp)
    · exact hnotmem (Lab.callG_mem_hiddenAPI r id b)
  | retG r id out =>
    exfalso; unfold hybridSpec at hstep; rw [System.abstract_step] at hstep
    rcases hstep with ⟨hτ, -⟩ | ⟨hnotmem, -⟩
    · exact absurd hτ (by simp)
    · exact hnotmem (Lab.retG_mem_hiddenAPI r id out)
  | callW r id =>
    exfalso; unfold hybridSpec at hstep; rw [System.abstract_step] at hstep
    rcases hstep with ⟨hτ, -⟩ | ⟨hnotmem, -⟩
    · exact absurd hτ (by simp)
    · exact hnotmem (Lab.callW_mem_hiddenAPI r id)
  | retW r id b =>
    exfalso; unfold hybridSpec at hstep; rw [System.abstract_step] at hstep
    rcases hstep with ⟨hτ, -⟩ | ⟨hnotmem, -⟩
    · exact absurd hτ (by simp)
    · exact hnotmem (Lab.retW_mem_hiddenAPI r id b)

end ABA
end PLTS
