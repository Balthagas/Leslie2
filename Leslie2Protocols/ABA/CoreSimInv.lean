/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.CoreSimRel
import Leslie2Protocols.ABA.Hybrid

/-!
# The core-simulation invariant: step inversion and preservation

Stages A and B of the proof that `coreR` is a simulation relation
(`DESIGN-CoreSim.md`), on top of the relation and invariant of
`CoreSimRel.lean`.

* **Stage A** — step inversion for `hybrid`: one lemma per visible label
  class (`callABA`, `retABA`, `fail`) and one for `τ`, each reading a composite
  transition back into the component rows that produced it. `hybrid_step_tau`
  is the seven-way disjunction the τ-side of the simulation dispatches on; its
  τ has more sources than the visible labels do, the whole rendezvous alphabet
  being hidden, and each of those sources collapses into one of the seven.
* **Stage B** — preservation of `Inv`: one `Inv.step_*` lemma per row of Stage
  A's inversion, each carrying all thirty-nine invariant fields across that
  row.

The assembly of the two into `Inv.step` is in `CoreSimAbs.lean`, beside the
`Abs`-side stutter lemmas it is stated with.
-/

namespace PLTS
namespace ABA

open Net Comp

variable {P : Params}

/-! ### Stage A: step inversion for `hybrid`

Each lemma reads a transition of the protocol-shaped specification back into
the rows of its four components, delivering the ABA-side content in the view's own
coordinates: the pair `(C, A)` of the round loops beside the ABA-side network,
read through `ABAState`'s accessors. -/

/-- `hybrid` inversion, `callABA`: the round specifications and the coin
oracle idle on a label outside their own API and the ABA-side network has no
row of its own, so the whole transition is the addressed round loop's — either
the genuine input, guarded by `input = ⊥`, or the input-enabledness loop. -/
theorem hybrid_step_callABA (P : Params) (G : ℕ → GBCA.SpecState P.n)
    (C : ∀ _ : Fin P.n, CoreRec P.n) (A : ANetState P.n)
    (o : ℕ → WCC.SpecState P.n) (id : Fin P.n) (b : Bool) (μ : PMF (HybridState P)) :
    (hybrid P).step (G, C, A, o) (.callABA id b) μ ↔
      ∃ μc : PMF (ABAState P),
        (((ABAState.procs (C, A) id).input = none ∧
            μc = PMF.pure (ABAState.setProc (C, A) id
              { ABAState.procs (C, A) id with
                input := some b, est := some b, round := 0, phase := .toCallG })) ∨
          μc = PMF.pure (C, A)) ∧
        μ = prodPMF (PMF.pure G) (μc.map fun c => (c.1, c.2, o)) := by
  have hWlift : (wccLift P).step o (Sum.inl (Lab.callABA id b)) (PMF.pure o) :=
    (System.mapIdle_step_some (wccPull_inl (Lab.callABA id b)) (PMF.pure o)).mpr
      (wccFamilyN_idle P o (by simp) rfl (by simp [Lab.isFail]))
  constructor
  · intro hstep
    rw [hybrid_step_iff] at hstep
    rcases hstep with ⟨habs, -⟩ | ⟨-, hg⟩
    · exact absurd habs (by simp)
    · rw [hybridGroup_step_iff] at hg
      rcases hg with ⟨habs, -⟩ | hpre
      · exact absurd habs (by simp)
      · obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
          hybridPre_vis_inv P (by simp) hpre
        obtain rfl : G = G' :=
          (pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)).symm
        obtain rfl : A = A' := (pureN_inj (aStep_callABA hA)).symm
        obtain rfl : ω = PMF.pure o := wccFamily_idle_inv P (by simp) rfl (by simp [Lab.isFail])
          ((System.mapIdle_step_some (wccPull_inl (Lab.callABA id b)) _).mp hW)
        rcases stepC_callABA_own (hall id) with ⟨hin, hx0⟩ | hx0
        · obtain rfl : C' = Function.update C id ((C id).setProc { (C id).proc with
              input := some b, est := some b, round := 0, phase := .toCallG }) :=
            coresN_update hx0 (fun i hi => stepC_callABA_foreign (Ne.symm hi) (hall i))
          exact ⟨PMF.pure (ABAState.setProc (C, A) id
              { ABAState.procs (C, A) id with
                input := some b, est := some b, round := 0, phase := .toCallG }),
            Or.inl ⟨hin, rfl⟩, by simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩
        · obtain rfl : C = C' := (coresN_id fun i => by
            by_cases hi : i = id
            · subst hi; exact hx0
            · exact stepC_callABA_foreign (Ne.symm hi) (hall i)).symm
          exact ⟨PMF.pure (C, A), Or.inr rfl, by
            simp only [PMF.pure_map, prodPMF_pure_pure]⟩
  · rintro ⟨μc, hdisj, rfl⟩
    rw [hybrid_step_iff]
    refine Or.inr ⟨by simp, ?_⟩
    rw [hybridGroup_step_iff]
    refine Or.inr ?_
    rcases hdisj with ⟨hin, rfl⟩ | rfl
    · have h := hybridPre_vis_step P (L := Sum.inl (Lab.callABA id b)) (by simp)
        (specSide_idle P G (by simp) rfl not_false)
        (coresN_family id ((C id).setProc { (C id).proc with
            input := some b, est := some b, round := 0, phase := .toCallG })
          (CoreProcStepN.input (C id) b hin)
          (fun i hi => CoreProcStepN.callABAIdle (C i) id b (Ne.symm hi)))
        (ANetStep.callABAIdle A id b) hWlift
      simp only [PMF.pure_map, prodPMF_pure_pure] at h ⊢
      exact h
    · have h := hybridPre_vis_step P (L := Sum.inl (Lab.callABA id b)) (by simp)
        (specSide_idle P G (by simp) rfl not_false)
        (fun i => by
          by_cases hi : i = id
          · subst hi; exact CoreProcStepN.inputLoop (C i) b
          · exact CoreProcStepN.callABAIdle (C i) id b (Ne.symm hi))
        (ANetStep.callABAIdle A id b) hWlift
      simp only [PMF.pure_map, prodPMF_pure_pure] at h ⊢
      exact h

/-- `hybrid` inversion, `retABA`: the return's two guards are split across
two components — the `n − f` quorum is the round loop's, having multicast
`⟨DECIDED, b⟩` oneself is the network's — and rejoin on `ABAState`. -/
theorem hybrid_step_retABA (P : Params) (G : ℕ → GBCA.SpecState P.n)
    (C : ∀ _ : Fin P.n, CoreRec P.n) (A : ANetState P.n)
    (o : ℕ → WCC.SpecState P.n) (id : Fin P.n) (b : Bool) (μ : PMF (HybridState P)) :
    (hybrid P).step (G, C, A, o) (.retABA id b) μ ↔
      ∃ μc : PMF (ABAState P),
        (P.n - P.f ≤ ABAState.decidedCount (C, A) id b ∧
          b ∈ ABAState.decidedSent (C, A) id ∧
          (ABAState.procs (C, A) id).returned = false ∧
          μc = PMF.pure (ABAState.setProc (C, A) id
            { ABAState.procs (C, A) id with returned := true })) ∧
        μ = prodPMF (PMF.pure G) (μc.map fun c => (c.1, c.2, o)) := by
  have hWlift : (wccLift P).step o (Sum.inl (Lab.retABA id b)) (PMF.pure o) :=
    (System.mapIdle_step_some (wccPull_inl (Lab.retABA id b)) (PMF.pure o)).mpr
      (wccFamilyN_idle P o (by simp) rfl (by simp [Lab.isFail]))
  constructor
  · intro hstep
    rw [hybrid_step_iff] at hstep
    rcases hstep with ⟨habs, -⟩ | ⟨-, hg⟩
    · exact absurd habs (by simp)
    · rw [hybridGroup_step_iff] at hg
      rcases hg with ⟨habs, -⟩ | hpre
      · exact absurd habs (by simp)
      · obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
          hybridPre_vis_inv P (by simp) hpre
        obtain rfl : G = G' :=
          (pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)).symm
        obtain ⟨hpool, hA'⟩ := aStep_retABA hA
        obtain rfl : A = A' := (pureN_inj hA').symm
        obtain rfl : ω = PMF.pure o := wccFamily_idle_inv P (by simp) rfl (by simp [Lab.isFail])
          ((System.mapIdle_step_some (wccPull_inl (Lab.retABA id b)) _).mp hW)
        obtain ⟨hcnt, hret, hx0⟩ := stepC_retABA_own (hall id)
        obtain rfl : C' = Function.update C id
            ((C id).setProc { (C id).proc with returned := true }) :=
          coresN_update hx0 (fun i hi => stepC_retABA_foreign (Ne.symm hi) (hall i))
        exact ⟨PMF.pure (ABAState.setProc (C, A) id
            { ABAState.procs (C, A) id with returned := true }),
          ⟨hcnt, hpool, hret, rfl⟩, by simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩
  · rintro ⟨μc, ⟨hcnt, hpool, hret, rfl⟩, rfl⟩
    rw [hybrid_step_iff]
    refine Or.inr ⟨by simp, ?_⟩
    rw [hybridGroup_step_iff]
    refine Or.inr ?_
    have h := hybridPre_vis_step P (L := Sum.inl (Lab.retABA id b)) (by simp)
      (specSide_idle P G (by simp) rfl not_false)
      (coresN_family id ((C id).setProc { (C id).proc with returned := true })
        (CoreProcStepN.ret (C id) b hcnt hret)
        (fun i hi => CoreProcStepN.retABAIdle (C i) id b (Ne.symm hi)))
      (ANetStep.retABA A id b hpool) hWlift
    simp only [PMF.pure_map, prodPMF_pure_pure] at h ⊢
    exact h

/-- `hybrid` inversion, `fail`: a genuine synchronisation of all four
components. Corruption is the round loops' one blind spot (D1): the round
specifications and the coin oracle each corrupt their own copy of `F`, the
ABA-side network corrupts the view's, and the round loops stand still. -/
theorem hybrid_step_fail (P : Params) (G : ℕ → GBCA.SpecState P.n)
    (C : ∀ _ : Fin P.n, CoreRec P.n) (A : ANetState P.n)
    (o : ℕ → WCC.SpecState P.n) (id : Fin P.n) (μ : PMF (HybridState P)) :
    (hybrid P).step (G, C, A, o) (.fail id) μ ↔
      μ = prodPMF (PMF.pure fun r => (G r).corrupt P id)
        ((PMF.pure (ABAState.corrupt P id (C, A))).map
          fun c => (c.1, c.2, fun r => (o r).corrupt P id)) := by
  constructor
  · intro hstep
    rw [hybrid_step_iff] at hstep
    rcases hstep with ⟨habs, -⟩ | ⟨-, hg⟩
    · exact absurd habs (by simp)
    · rw [hybridGroup_step_iff] at hg
      rcases hg with ⟨habs, -⟩ | hpre
      · exact absurd habs (by simp)
      · obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
          hybridPre_vis_inv P (by simp) hpre
        obtain rfl : G' = fun r => (G r).corrupt P id :=
          pureN_inj (specSide_fail_inv P id hG)
        obtain rfl : C = C' := (coresN_id fun i => stepC_fail (hall i)).symm
        obtain rfl : A' = ANetState.corrupt P id A := pureN_inj (aStep_fail hA)
        obtain rfl : ω = PMF.pure (fun r => (o r).corrupt P id) := wccFamily_fail_inv P id
          ((System.mapIdle_step_some (wccPull_inl (Lab.fail id)) _).mp hW)
        simp only [PMF.pure_map, prodPMF_pure_pure]
        rfl
  · rintro rfl
    rw [hybrid_step_iff]
    refine Or.inr ⟨by simp, ?_⟩
    rw [hybridGroup_step_iff]
    refine Or.inr ?_
    have h := hybridPre_vis_step P (L := Sum.inl (Lab.fail id)) (by simp)
      (specSide_fail P G id)
      (fun i => CoreProcStepN.failIdle (C i) id)
      (ANetStep.fail A id)
      ((System.mapIdle_step_some (wccPull_inl (Lab.fail id)) _).mpr (wccFamily_fail P o id))
    simp only [PMF.pure_map, prodPMF_pure_pure] at h ⊢
    exact h

/-- `hybrid` inversion, `τ` (`mp`-only: preservation only needs the forward
direction). Seven sources, and the whole rendezvous alphabet folds into them:
the specification family's binding kill, the view's own DECIDED traffic
(delivery, echo, Byzantine injection), the coin resolution, and the four
handshakes — `callG`/`retG` against a round specification, `callW`/`retW`
against the coin oracle — each reached either by the shared label under the
sub-protocol hiding or by the rendezvous that stands for it (`gcallLoop`, the
Byzantine drives, and the fused coin return `retWPub`). -/
theorem hybrid_step_tau (P : Params) (G : ℕ → GBCA.SpecState P.n)
    (C : ∀ _ : Fin P.n, CoreRec P.n) (A : ANetState P.n)
    (o : ℕ → WCC.SpecState P.n) (μ : PMF (HybridState P))
    (hstep : (hybrid P).step (G, C, A, o) .tau μ) :
    (∃ r μr, GBCA.Step P r (G r) .tau μr ∧
        μ = prodPMF (μr.map (Function.update G r)) (PMF.pure (C, A, o))) ∨
      (∃ μc : PMF (ABAState P),
        ((∃ i j b, b ∈ ABAState.decidedSent (C, A) j ∧
              b ∉ ABAState.decidedRecv (C, A) i j ∧
              μc = PMF.pure (ABAState.deliverDecided (C, A) i j b)) ∨
          (∃ k b, P.f + 1 ≤ ABAState.decidedCount (C, A) k b ∧
              b ∉ ABAState.decidedSent (C, A) k ∧
              μc = PMF.pure (ABAState.sendDecided (C, A) k b)) ∨
          (∃ k b, k ∈ ABAState.F (C, A) ∧
              μc = PMF.pure (ABAState.sendDecided (C, A) k b))) ∧
        μ = prodPMF (PMF.pure G) (μc.map fun c => (c.1, c.2, o))) ∨
      (∃ r μw', WCC.Step P r (o r) .tau μw' ∧
        μ = prodPMF (PMF.pure G) (prodPMF (PMF.pure C)
              (prodPMF (PMF.pure A) (μw'.map (Function.update o r))))) ∨
      (∃ (r : ℕ) (id : Fin P.n) (b : Bool) (μr : PMF (GBCA.SpecState P.n))
          (μc : PMF (ABAState P)), GBCA.Step P r (G r) (.callG r id b) μr ∧
        (((ABAState.procs (C, A) id).phase = .toCallG ∧
            (ABAState.procs (C, A) id).round = r ∧
            (ABAState.procs (C, A) id).est = some b ∧
            μc = PMF.pure (ABAState.setProc (C, A) id
              { ABAState.procs (C, A) id with phase := .awaitG })) ∨
          (id ∈ ABAState.F (C, A) ∧ μc = PMF.pure (C, A))) ∧
        μ = prodPMF (μr.map (Function.update G r)) (μc.map fun c => (c.1, c.2, o))) ∨
      (∃ (r : ℕ) (id : Fin P.n) (out : GbcaOut) (μr : PMF (GBCA.SpecState P.n))
          (μc : PMF (ABAState P)), GBCA.Step P r (G r) (.retG r id out) μr ∧
        (((ABAState.procs (C, A) id).phase = .awaitG ∧
            (ABAState.procs (C, A) id).round = r ∧
            μc = PMF.pure (ABAState.setProc (C, A) id
              { ABAState.procs (C, A) id with
                est := out.est, lastGrade := some out, phase := .toCallW })) ∨
          (id ∈ ABAState.F (C, A) ∧ μc = PMF.pure (C, A))) ∧
        μ = prodPMF (μr.map (Function.update G r)) (μc.map fun c => (c.1, c.2, o))) ∨
      (∃ (r : ℕ) (id : Fin P.n) (μw' : PMF (WCC.SpecState P.n))
          (μc : PMF (ABAState P)), WCC.Step P r (o r) (.callW r id) μw' ∧
        (((ABAState.procs (C, A) id).phase = .toCallW ∧
            (ABAState.procs (C, A) id).round = r ∧
            μc = PMF.pure (ABAState.setProc (C, A) id
              { ABAState.procs (C, A) id with phase := .awaitW })) ∨
          (id ∈ ABAState.F (C, A) ∧ μc = PMF.pure (C, A))) ∧
        μ = prodPMF (PMF.pure G) (μc.bind fun c => prodPMF (PMF.pure c.1)
              (prodPMF (PMF.pure c.2) (μw'.map (Function.update o r))))) ∨
      (∃ (r : ℕ) (id : Fin P.n) (b : Bool) (μw' : PMF (WCC.SpecState P.n))
          (μc : PMF (ABAState P)), WCC.Step P r (o r) (.retW r id b) μw' ∧
        (((ABAState.procs (C, A) id).phase = .awaitW ∧
            (ABAState.procs (C, A) id).round = r ∧
            μc = PMF.pure (ABAState.stepRound (C, A) id b)) ∨
          (id ∈ ABAState.F (C, A) ∧ μc = PMF.pure (C, A))) ∧
        μ = prodPMF (PMF.pure G) (μc.bind fun c => prodPMF (PMF.pure c.1)
              (prodPMF (PMF.pure c.2) (μw'.map (Function.update o r))))) := by
  rw [hybrid_step_iff] at hstep
  rcases hstep with ⟨-, l', hl', hg⟩ | ⟨-, hg⟩
  · rw [hybridGroup_step_iff] at hg
    rcases hg with ⟨rfl, e, hpre⟩ | hpre
    · exact absurd hl' (by simp)
    · -- a sub-protocol API label, sent to `τ` by the outer hiding
      cases l' with
      | tau => exact absurd hl' (by simp)
      | callABA id b => exact absurd hl' (by simp)
      | retABA id b => exact absurd hl' (by simp)
      | fail k => exact absurd hl' (by simp)
      | callG r id b =>
        obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
          hybridPre_vis_inv P (by simp) hpre
        obtain ⟨X, hstepG, rfl⟩ := specSide_owned_step P rfl (by simp) rfl hG
        obtain rfl : A = A' := (pureN_inj (aStep_callG hA)).symm
        obtain rfl : ω = PMF.pure o := wccFamily_idle_inv P (by simp) rfl (by simp [Lab.isFail])
          ((System.mapIdle_step_some (wccPull_inl (Lab.callG r id b)) _).mp hW)
        obtain ⟨hph, hr, hest, hx0⟩ := stepC_callG_own (hall id)
        obtain rfl : C' = Function.update C id
            ((C id).setProc { (C id).proc with phase := .awaitG }) :=
          coresN_update hx0 (fun i hi => stepC_callG_foreign (Ne.symm hi) (hall i))
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, id, b, PMF.pure X,
          PMF.pure (ABAState.setProc (C, A) id
            { ABAState.procs (C, A) id with phase := .awaitG }),
          hstepG, Or.inl ⟨hph, hr, hest, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩)))
      | retG r id out =>
        obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
          hybridPre_vis_inv P (by simp) hpre
        obtain ⟨X, hstepG, rfl⟩ := specSide_owned_step P rfl (by simp) rfl hG
        obtain rfl : A = A' := (pureN_inj (aStep_retG hA)).symm
        obtain rfl : ω = PMF.pure o := wccFamily_idle_inv P (by simp) rfl (by simp [Lab.isFail])
          ((System.mapIdle_step_some (wccPull_inl (Lab.retG r id out)) _).mp hW)
        obtain ⟨hph, hr, hx0⟩ := stepC_retG_own (hall id)
        obtain rfl : C' = Function.update C id ((C id).setProc
            { (C id).proc with est := out.est, lastGrade := some out, phase := .toCallW }) :=
          coresN_update hx0 (fun i hi => stepC_retG_foreign (Ne.symm hi) (hall i))
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, id, out, PMF.pure X,
          PMF.pure (ABAState.setProc (C, A) id
            { ABAState.procs (C, A) id with
              est := out.est, lastGrade := some out, phase := .toCallW }),
          hstepG, Or.inl ⟨hph, hr, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩))))
      | callW r id =>
        obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
          hybridPre_vis_inv P (by simp) hpre
        obtain rfl : G = G' :=
          (pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)).symm
        obtain rfl : A = A' := (pureN_inj (aStep_callW hA)).symm
        obtain ⟨μw', hstepW, rfl⟩ := wccFamily_owned_inv P (by simp) rfl
          ((System.mapIdle_step_some (wccPull_inl (Lab.callW r id)) _).mp hW)
        obtain ⟨hph, hr, hx0⟩ := stepC_callW_own (hall id)
        obtain rfl : C' = Function.update C id
            ((C id).setProc { (C id).proc with phase := .awaitW }) :=
          coresN_update hx0 (fun i hi => stepC_callW_foreign (Ne.symm hi) (hall i))
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, id, μw',
          PMF.pure (ABAState.setProc (C, A) id
            { ABAState.procs (C, A) id with phase := .awaitW }),
          hstepW, Or.inl ⟨hph, hr, rfl⟩, by rw [PMF.pure_bind]; rfl⟩)))))
      | retW r id c =>
        obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
          hybridPre_vis_inv P (by simp) hpre
        obtain rfl : G = G' :=
          (pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)).symm
        obtain rfl : A = A' := (pureN_inj (aStep_retW hA)).symm
        obtain ⟨μw', hstepW, rfl⟩ := wccFamily_owned_inv P (by simp) rfl
          ((System.mapIdle_step_some (wccPull_inl (Lab.retW r id c)) _).mp hW)
        obtain ⟨hph, hr, hgr, hx0⟩ := stepC_retW_own (hall id)
        obtain rfl : C' = Function.update C id ((C id).stepRound c) :=
          coresN_update hx0 (fun i hi => stepC_retW_foreign (Ne.symm hi) (hall i))
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, id, c, μw',
          PMF.pure (ABAState.stepRound (C, A) id c), hstepW,
          Or.inl ⟨hph, hr, rfl⟩, ?_⟩)))))
        rw [PMF.pure_bind, ABAState.stepRound_plain C A id c hgr]
  · rw [hybridGroup_step_iff] at hg
    rcases hg with ⟨-, e, hpre⟩ | hpre
    · -- a rendezvous of the hidden alphabet
      obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
        hybridPre_vis_inv P (by simp) hpre
      cases e with
      | gsnd r j m => exact (aStep_gsnd_dead hA).elim
      | gdlv r i j m => exact (aStep_gdlv_dead hA).elim
      | dsnd j b =>
        obtain rfl : G = G' :=
          (pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)).symm
        obtain ⟨hcnt, hx0⟩ := stepC_dsnd_self (hall j)
        obtain rfl : C = C' := (coresN_id fun i => by
          by_cases hi : i = j
          · subst hi; exact hx0
          · exact stepC_dsnd_foreign (Ne.symm hi) (hall i)).symm
        obtain ⟨hpool, hA'⟩ := aStep_dsnd hA
        obtain rfl : A' = A.dput j b := pureN_inj hA'
        obtain rfl : ω = PMF.pure o :=
          (System.mapIdle_step_none (wccPull_dsnd j b) ω).mp hW
        exact Or.inr (Or.inl ⟨PMF.pure (ABAState.sendDecided (C, A) j b),
          Or.inr (Or.inl ⟨j, b, hcnt, hpool, rfl⟩), by
            simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩)
      | ddlv i j b =>
        obtain rfl : G = G' :=
          (pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)).symm
        obtain ⟨hnr, hx0⟩ := stepC_ddlv_self (hall i)
        obtain rfl : C' = Function.update C i ((C i).recvDec j b) :=
          coresN_update hx0 (fun k hk => stepC_ddlv_foreign (Ne.symm hk) (hall k))
        obtain ⟨hmem, hA'⟩ := aStep_ddlv hA
        obtain rfl : A = A' := (pureN_inj hA').symm
        obtain rfl : ω = PMF.pure o :=
          (System.mapIdle_step_none (wccPull_ddlv i j b) ω).mp hW
        exact Or.inr (Or.inl ⟨PMF.pure (ABAState.deliverDecided (C, A) i j b),
          Or.inl ⟨i, j, b, hmem, hnr, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩)
      | retWPub r id c b =>
        obtain rfl : G = G' :=
          (pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)).symm
        obtain ⟨μw', hstepW, rfl⟩ := wccFamily_owned_inv P (by simp) rfl
          ((System.mapIdle_step_some (wccPull_retWPub r id c b) ω).mp hW)
        obtain ⟨hph, hr, hgA, hx0⟩ := stepC_retWPub_self (hall id)
        obtain rfl : C' = Function.update C id ((C id).stepRound c) :=
          coresN_update hx0 (fun k hk => stepC_retWPub_foreign (Ne.symm hk) (hall k))
        obtain rfl : A' = A.dput id b := pureN_inj (aStep_retWPub hA)
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, id, c, μw',
          PMF.pure (ABAState.stepRound (C, A) id c), hstepW,
          Or.inl ⟨hph, hr, rfl⟩, ?_⟩)))))
        rw [PMF.pure_bind, ABAState.stepRound_pub C A id c b hgA]
      | gcallLoop r id b =>
        obtain ⟨X, hstepG, rfl⟩ := specSide_owned_step P rfl (by simp) rfl hG
        obtain ⟨hph, hr, hest, hx0⟩ := stepC_gcallLoop_self (hall id)
        obtain rfl : C' = Function.update C id
            ((C id).setProc { (C id).proc with phase := .awaitG }) :=
          coresN_update hx0 (fun k hk => stepC_gcallLoop_foreign (Ne.symm hk) (hall k))
        obtain rfl : A = A' := (pureN_inj (aStep_gcallLoop hA)).symm
        obtain rfl : ω = PMF.pure o :=
          (System.mapIdle_step_none (wccPull_gcallLoop r id b) ω).mp hW
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, id, b, PMF.pure X,
          PMF.pure (ABAState.setProc (C, A) id
            { ABAState.procs (C, A) id with phase := .awaitG }),
          hstepG, Or.inl ⟨hph, hr, hest, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩)))
      | byzCallG r k b =>
        obtain ⟨X, hstepG, rfl⟩ := specSide_owned_step P rfl (by simp) rfl hG
        obtain rfl : C = C' := (coresN_id fun i => stepC_byzCallG (hall i)).symm
        obtain ⟨hF, hA'⟩ := aStep_byzCallG hA
        obtain rfl : A = A' := (pureN_inj hA').symm
        obtain rfl : ω = PMF.pure o :=
          (System.mapIdle_step_none (wccPull_byzCallG r k b) ω).mp hW
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, k, b, PMF.pure X, PMF.pure (C, A),
          hstepG, Or.inr ⟨hF, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]⟩)))
      | byzCallGLoop r k b =>
        obtain ⟨X, hstepG, rfl⟩ := specSide_owned_step P rfl (by simp) rfl hG
        obtain rfl : C = C' := (coresN_id fun i => stepC_byzCallGLoop (hall i)).symm
        obtain ⟨hF, hA'⟩ := aStep_byzCallGLoop hA
        obtain rfl : A = A' := (pureN_inj hA').symm
        obtain rfl : ω = PMF.pure o :=
          (System.mapIdle_step_none (wccPull_byzCallGLoop r k b) ω).mp hW
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, k, b, PMF.pure X, PMF.pure (C, A),
          hstepG, Or.inr ⟨hF, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]⟩)))
      | byzRetG r k out =>
        obtain ⟨X, hstepG, rfl⟩ := specSide_owned_step P rfl (by simp) rfl hG
        obtain rfl : C = C' := (coresN_id fun i => stepC_byzRetG (hall i)).symm
        obtain ⟨hF, hA'⟩ := aStep_byzRetG hA
        obtain rfl : A = A' := (pureN_inj hA').symm
        obtain rfl : ω = PMF.pure o :=
          (System.mapIdle_step_none (wccPull_byzRetG r k out) ω).mp hW
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, k, out, PMF.pure X,
          PMF.pure (C, A), hstepG, Or.inr ⟨hF, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]⟩))))
      | byzCallW r k =>
        obtain rfl : G = G' :=
          (pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)).symm
        obtain rfl : C = C' := (coresN_id fun i => stepC_byzCallW (hall i)).symm
        obtain ⟨hF, hA'⟩ := aStep_byzCallW hA
        obtain rfl : A = A' := (pureN_inj hA').symm
        obtain ⟨μw', hstepW, rfl⟩ := wccFamily_owned_inv P (by simp) rfl
          ((System.mapIdle_step_some (wccPull_byzCallW r k) ω).mp hW)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, k, μw',
          PMF.pure (C, A), hstepW, Or.inr ⟨hF, rfl⟩, by rw [PMF.pure_bind]⟩)))))
      | byzRetW r k b =>
        obtain rfl : G = G' :=
          (pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)).symm
        obtain rfl : C = C' := (coresN_id fun i => stepC_byzRetW (hall i)).symm
        obtain ⟨hF, hA'⟩ := aStep_byzRetW hA
        obtain rfl : A = A' := (pureN_inj hA').symm
        obtain ⟨μw', hstepW, rfl⟩ := wccFamily_owned_inv P (by simp) rfl
          ((System.mapIdle_step_some (wccPull_byzRetW r k b) ω).mp hW)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, k, b, μw',
          PMF.pure (C, A), hstepW, Or.inr ⟨hF, rfl⟩, by rw [PMF.pure_bind]⟩)))))
    · -- genuine `τ`: the binding kill, the network's Byzantine injection, or the coin
      rcases hybridPre_tau_inv P hpre with ⟨G', hspec, rfl⟩ | ⟨A', hnet, rfl⟩ |
        ⟨ω, hW, rfl⟩
      · obtain ⟨r, X, hstepG, hGeq⟩ := specSide_tau_inv P hspec
        obtain rfl : G' = Function.update G r X := pureN_inj hGeq
        rw [GSub.liftedSpecG, System.mapIdle_step_some (GSub.gPull_inl (Lab.tau : Lab P.n))]
          at hstepG
        exact Or.inl ⟨r, PMF.pure X, hstepG, by rw [PMF.pure_map, prodPMF_pure_pure]⟩
      · obtain ⟨k, b, hF, hA'⟩ := aStep_tau hnet
        obtain rfl : A' = A.dput k b := pureN_inj hA'
        exact Or.inr (Or.inl ⟨PMF.pure (ABAState.sendDecided (C, A) k b),
          Or.inr (Or.inr ⟨k, b, hF, rfl⟩), by rw [PMF.pure_map, prodPMF_pure_pure]; rfl⟩)
      · rw [WCC.specFamily, System.family_step_iff] at hW
        simp only [Lab.wccRound, Lab.isFail] at hW
        rcases hW with ⟨-, r, μw', hw1, rfl⟩ | ⟨r, hr, -⟩ | ⟨hτ, -, -, -⟩ | ⟨hτ, -, -, -⟩
        · exact Or.inr (Or.inr (Or.inl ⟨r, μw', hw1, rfl⟩))
        · exact absurd hr (by simp)
        · exact absurd rfl hτ
        · exact absurd rfl hτ

/-! ### Stage B: preservation of `Inv` -/

/-- WCC corruption changes only `F`. -/
theorem WCC.corrupt_val {P : Params} (id : Fin P.n) (s : WCC.SpecState P.n) :
    (s.corrupt P id).val = s.val := by unfold WCC.SpecState.corrupt; split <;> rfl

theorem WCC.corrupt_called {P : Params} (id : Fin P.n) (s : WCC.SpecState P.n) :
    (s.corrupt P id).called = s.called := by unfold WCC.SpecState.corrupt; split <;> rfl

/-- The GBCA corruption of a state agreeing with the core on `F` agrees with the core's
corruption on `F` (keeps `F_g` in lockstep across a `fail` broadcast). -/
theorem GBCA.corrupt_F_eq {P : Params} (id : Fin P.n) (s : GBCA.SpecState P.n)
    (c : ABAState P) (h : s.F = c.F) :
    (s.corrupt P id).F = (c.corrupt P id).F := by
  unfold GBCA.SpecState.corrupt
  rw [ABAState.corrupt_F, h]; split_ifs <;> simp [h]

/-- The WCC corruption of a state agreeing with the core on `F` agrees with the core's
corruption on `F` (keeps `F_w` in lockstep across a `fail` broadcast). -/
theorem WCC.corrupt_F_eq {P : Params} (id : Fin P.n) (s : WCC.SpecState P.n)
    (c : ABAState P) (h : s.F = c.F) :
    (s.corrupt P id).F = (c.corrupt P id).F := by
  unfold WCC.SpecState.corrupt
  rw [ABAState.corrupt_F, h]; split_ifs <;> simp [h]

/-- `retABA` only sets `returned`, a field `Inv` never inspects: `Inv` transfers verbatim
modulo the pointwise-unchanged projections of `procs`. -/
theorem Inv.step_retABA {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (id : Fin P.n) (b : Bool)
    {μc : PMF (ABAState P)}
    (hstep : P.n - P.f ≤ c.decidedCount id b ∧ b ∈ c.decidedSent id ∧
      (c.procs id).returned = false ∧
      μc = PMF.pure (c.setProc id { c.procs id with returned := true }))
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Inv P g c' w ∧ AbsFrame P g g c c' := by
  obtain ⟨-, -, -, rfl⟩ := hstep
  rw [PMF.mem_support_pure_iff] at hc'
  subst hc'
  set c' := c.setProc id { c.procs id with returned := true } with hc'def
  have hF : c'.F = c.F := ABAState.setProc_F _ _ _
  have hDS : c'.decidedSent = c.decidedSent := ABAState.setProc_decidedSent _ _ _
  have hDR : c'.decidedRecv = c.decidedRecv := ABAState.setProc_decidedRecv _ _ _
  have hDC : ∀ i b', c'.decidedCount i b' = c.decidedCount i b' :=
    fun i b' => ABAState.setProc_decidedCount _ _ _ _ _
  have hInput : ∀ id', (c'.procs id').input = (c.procs id').input := by
    intro id'; by_cases h : id' = id
    · subst h; rw [hc'def, ABAState.setProc_procs_self]
    · rw [hc'def, ABAState.setProc_procs_ne _ _ _ h]
  have hEst : ∀ id', (c'.procs id').est = (c.procs id').est := by
    intro id'; by_cases h : id' = id
    · subst h; rw [hc'def, ABAState.setProc_procs_self]
    · rw [hc'def, ABAState.setProc_procs_ne _ _ _ h]
  have hRound : ∀ id', (c'.procs id').round = (c.procs id').round := by
    intro id'; by_cases h : id' = id
    · subst h; rw [hc'def, ABAState.setProc_procs_self]
    · rw [hc'def, ABAState.setProc_procs_ne _ _ _ h]
  have hPhase : ∀ id', (c'.procs id').phase = (c.procs id').phase := by
    intro id'; by_cases h : id' = id
    · subst h; rw [hc'def, ABAState.setProc_procs_self]
    · rw [hc'def, ABAState.setProc_procs_ne _ _ _ h]
  have hLastGrade : ∀ id', (c'.procs id').lastGrade = (c.procs id').lastGrade := by
    intro id'; by_cases h : id' = id
    · subst h; rw [hc'def, ABAState.setProc_procs_self]
    · rw [hc'def, ABAState.setProc_procs_ne _ _ _ h]
  have hCarr : ∀ r' id' v, Carrier P g c' r' id' v → Carrier P g c r' id' v := by
    intro r' id' v hc
    unfold Carrier at hc ⊢
    rwa [hEst, hRound, hPhase] at hc
  have hCert : ∀ r' b', ACert P g c r' b' → ACert P g c' r' b' := fun r' b' =>
    ACert.of_frame rfl (fun _ => rfl) (fun _ _ => rfl)
      (by rw [hF] : c.F ⊆ c'.F) hRound hEst (fun id0 v => hCarr r' id0 v)
  have hHold : ∀ id' b', AHolder P c' id' b' → AHolder P c id' b' := by
    intro id' b' h
    unfold AHolder at h ⊢
    rwa [hLastGrade, hDS] at h
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
    fun v _ hpin j b' hj hh => hpin j b' (hF ▸ hj) (hHold j b' hh)⟩
  refine ⟨fun r => (hI.F_g r).trans hF.symm, fun r => ?_, ?_, ?_, ?_, ?_,
    hI.down_closed, hI.quiescent, hI.w_bound, ?_, ?_, ?_, ?_, ?_,
    hI.gradeA_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.c_chain, ?_,
    hI.w_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
    fun r v hb => (hI.bind_supp r v hb).mono
      (fun id' b' h => by rw [hInput]; exact h) (fun x hx => by rw [hF]; exact hx),
    hI.clock_supp, hI.dead_supp,
    fun r' i j v v' hm hm' h h' => hI.carrier_agree r' i j v v' (hF ▸ hm) (hF ▸ hm')
      (hCarr _ _ _ h) (hCarr _ _ _ h'),
    fun i j b₀ b₀' hm hm' h h' => hI.alock_agree i j b₀ b₀' (hF ▸ hm) (hF ▸ hm')
      (hHold _ _ h) (hHold _ _ h')⟩
  · rw [hF]; exact hI.F_w r
  · rw [hF]; exact hI.F_card
  · intro id' b' hmem hcall; rw [hInput]; exact hI.input_g0 id' b' (hF ▸ hmem) hcall
  · intro r id' hmem hcall; rw [hInput]; exact hI.input_called r id' (hF ▸ hmem) hcall
  · intro id' hmem hne; rw [hPhase] at hne; rw [hInput]; exact hI.phase_input id' (hF ▸ hmem) hne
  · intro i j b' h; rw [hDR] at h; rw [hDS]; exact hI.recv_sound i j b' h
  · intro id' b' hmem h; rw [hDS] at h
    exact (hI.decided_src id' b' (hF ▸ hmem) h).imp (fun r => hCert r b')
  · intro r b' hg hb
    exact ACommit.of_frame (fun _ => rfl) (fun _ _ => rfl)
      (by rw [hF]) hRound hEst (fun id0 v => hCarr r id0 v) (hI.a_commit r b' hg hb)
  · intro id' hmem r hr; exact hI.round_bound id' (hF ▸ hmem) r (hRound id' ▸ hr)
  · intro r v hlast hb hcoin id' hmem hr
    rw [hEst]; exact hI.agree_locked r v hlast hb hcoin id' (hF ▸ hmem) (hRound id' ▸ hr)
  · intro r id' hmem hcall; rw [hRound]; exact hI.call_round r id' (hF ▸ hmem) hcall
  · intro r id' hmem hcalled; exact hI.w_called r id' (hF ▸ hmem) hcalled
  · intro r id' hmem hr; rw [hRound] at hr; exact hI.round_flip r id' (hF ▸ hmem) hr
  · intro id' hmem hround hphase
    rw [hRound] at hround; rw [hPhase] at hphase
    rw [hEst, hInput]; exact hI.est0 id' (hF ▸ hmem) hround hphase
  · intro id' b' hlg; rw [hLastGrade] at hlg
    exact (hI.grade_A_src id' b' hlg).imp (fun r => hCert r b')
  · intro r id' hmem hround hphase
    rw [hRound] at hround; rw [hPhase] at hphase
    rw [hEst]; exact hI.est_ret r id' (hF ▸ hmem) hround hphase
  · intro r id' v hmem hcall; exact hI.call_prov r id' v (hF ▸ hmem) hcall
  · intro r id' hmem hround hphase v hest
    rw [hRound] at hround; rw [hPhase] at hphase; rw [hEst] at hest
    exact hI.est_prev r id' (hF ▸ hmem) hround hphase v hest
  · intro id' hmem hround hphase
    rw [hRound] at hround; rw [hPhase] at hphase; rw [hEst]
    exact hI.est_prev_ne id' (hF ▸ hmem) hround hphase
  · intro id' b' h
    rcases hI.input_g0_perm id' b' h with hin | hf
    · left; rw [hInput]; exact hin
    · right; rw [hF]; exact hf
  · intro r id' hmem hcalled; rw [hRound]; exact hI.w_call_round r id' (hF ▸ hmem) hcalled
  · intro r h
    rcases hI.flip_alock r h with hg | hd
    · left; exact hg
    · right; exact DissentResidue.transport rfl rfl (fun hh => hh) (fun id' => hInput id') hd
  · intro id' hmem hin r'; rw [hInput] at hin; exact hI.idle_no_wcall id' (hF ▸ hmem) hin r'
  · intro r id' hmem h
    rw [hRound] at h; rw [hPhase] at h
    rcases hI.retg_residue r id' (hF ▸ hmem) h with hg | hd
    · left; exact hg
    · right; exact DissentResidue.transport rfl rfl (fun hh => hh) (fun id'' => hInput id'') hd
  · intro r id' hmem hcalled
    rcases hI.wcalled_residue r id' (hF ▸ hmem) hcalled with hg | hd
    · left; exact hg
    · right; exact DissentResidue.transport rfl rfl (fun hh => hh) (fun id'' => hInput id'') hd

/-- `callABA`: either a genuine external input (guarded by `input = none`, so `input_called`
rules out the "already called GBCA" corner) or the idle self-loop. -/
theorem Inv.step_callABA {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (id : Fin P.n) (b : Bool)
    {μc : PMF (ABAState P)}
    (hstep :
      ((c.procs id).input = none ∧
          μc = PMF.pure (c.setProc id { c.procs id with
            input := some b, est := some b, round := 0, phase := .toCallG })) ∨
        μc = PMF.pure c)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Inv P g c' w ∧ AbsFrame P g g c c' := by
  rcases hstep with ⟨hin, rfl⟩ | rfl
  · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    set c' := c.setProc id { c.procs id with
      input := some b, est := some b, round := 0, phase := .toCallG } with hc'def
    have hF : c'.F = c.F := ABAState.setProc_F _ _ _
    have hDS : c'.decidedSent = c.decidedSent := ABAState.setProc_decidedSent _ _ _
    have hDR : c'.decidedRecv = c.decidedRecv := ABAState.setProc_decidedRecv _ _ _
    have hSelf : c'.procs id = { c.procs id with
        input := some b, est := some b, round := 0, phase := .toCallG } := by
      rw [hc'def]; exact ABAState.setProc_procs_self _ _ _
    have hNe : ∀ id', id' ≠ id → c'.procs id' = c.procs id' := by
      intro id' h; rw [hc'def]; exact ABAState.setProc_procs_ne _ _ _ h
    have hDissTrans : ∀ r, DissentResidue P g c r → DissentResidue P g c' r := by
      intro r hd
      obtain ⟨v, hbv, hif⟩ := hd
      refine ⟨v, hbv, ?_⟩
      by_cases h0 : r = 0
      · rw [if_pos h0] at hif ⊢
        obtain ⟨id', hid'⟩ := hif
        by_cases hidmatch : id' = id
        · exfalso; rw [hidmatch, hin] at hid'; exact absurd hid' (by simp)
        · exact ⟨id', by rw [hNe id' hidmatch]; exact hid'⟩
      · rw [if_neg h0] at hif ⊢; exact hif
    have hInMono : ∀ id' b', (c.procs id').input = some b' → (c'.procs id').input = some b' := by
      intro id' b' h
      by_cases hid : id' = id
      · exact absurd (hid ▸ h) (by rw [hin]; simp)
      · rw [hNe id' hid]; exact h
    have hCarrTrans : ∀ r' id₀ v, Carrier P g c' r' id₀ v → Carrier P g c r' id₀ v := by
      intro r' id₀ v hc
      rcases hc with h | ⟨he, hk⟩
      · exact Or.inl h
      · by_cases hid : id₀ = id
        · subst hid; exfalso; simp [hSelf] at hk
        · rw [hNe id₀ hid] at he hk
          exact Or.inr ⟨he, hk⟩
    have hCertTrans : ∀ r' b', ACert P g c r' b' → ACert P g c' r' b' := by
      rintro r' b' ⟨hg1, hd1, h1, h2, h3, h4⟩
      refine ⟨hg1, hd1, h1,
        fun r'' id'' b'' hrr hmem hcall => h2 r'' id'' b'' hrr (hF ▸ hmem) hcall,
        fun id'' hmem hr => ?_,
        fun id'' v hmem hcar => h4 id'' v (hF ▸ hmem) (hCarrTrans r' id'' v hcar)⟩
      by_cases h : id'' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id'' h] at hr ⊢; exact h3 id'' (hF ▸ hmem) hr
    have hLG : ∀ id₀, (c'.procs id₀).lastGrade = (c.procs id₀).lastGrade := by
      intro id₀; by_cases h : id₀ = id
      · subst h; simp [hSelf]
      · rw [hNe id₀ h]
    have hHold : ∀ id₀ b₀, AHolder P c' id₀ b₀ → AHolder P c id₀ b₀ := by
      intro id₀ b₀ h
      unfold AHolder at h ⊢
      rwa [hLG, hDS] at h
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hF ▸ hj) (hHold j b' hh)⟩
    refine ⟨fun r => (hI.F_g r).trans hF.symm, fun r => hF ▸ hI.F_w r, hF ▸ hI.F_card,
      ?_, ?_, ?_, hI.down_closed, hI.quiescent, hI.w_bound, ?_, ?_, ?_, ?_, ?_,
      hI.gradeA_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.c_chain, ?_,
      hI.w_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_supp r v hb).mono hInMono (fun x hx => by rw [hF]; exact hx),
      hI.clock_supp, hI.dead_supp,
      fun r' i j v v' hm hm' h h' => hI.carrier_agree r' i j v v' (hF ▸ hm) (hF ▸ hm')
        (hCarrTrans _ _ _ h) (hCarrTrans _ _ _ h'),
      fun i j b₀ b₀' hm hm' h h' => hI.alock_agree i j b₀ b₀' (hF ▸ hm) (hF ▸ hm')
        (hHold _ _ h) (hHold _ _ h')⟩
    · intro id' b' hmem hcall
      by_cases h : id' = id
      · rw [h] at hcall hmem
        have hne : (g 0).call id ≠ none := by rw [hcall]; simp
        exact absurd hin (hI.input_called 0 id (hF ▸ hmem) hne)
      · rw [hNe id' h]; exact hI.input_g0 id' b' (hF ▸ hmem) hcall
    · intro r id' hmem hcall
      by_cases h : id' = id
      · rw [h]; simp [hSelf]
      · rw [hNe id' h]; exact hI.input_called r id' (hF ▸ hmem) hcall
    · intro id' hmem hne
      by_cases h : id' = id
      · rw [h]; simp [hSelf]
      · rw [hNe id' h] at hne ⊢; exact hI.phase_input id' (hF ▸ hmem) hne
    · intro i j b' h; rw [hDR] at h; rw [hDS]; exact hI.recv_sound i j b' h
    · intro id' b' hmem h; rw [hDS] at h
      exact (hI.decided_src id' b' (hF ▸ hmem) h).imp (fun r => hCertTrans r b')
    · intro r b' hg hb
      obtain ⟨h1, h2, h3, h4⟩ := hI.a_commit r b' hg hb
      refine ⟨h1, h2, fun id' hmem hr => ?_,
        fun id0 v hmem hcar => h4 id0 v (hF ▸ hmem) (hCarrTrans r id0 v hcar)⟩
      by_cases h : id' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id' h] at hr ⊢; exact h3 id' (hF ▸ hmem) hr
    · intro id' hmem r hr
      by_cases h : id' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id' h] at hr; exact hI.round_bound id' (hF ▸ hmem) r hr
    · intro r v hlast hb hcoin id' hmem hr
      by_cases h : id' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id' h] at hr ⊢; exact hI.agree_locked r v hlast hb hcoin id' (hF ▸ hmem) hr
    · intro r id' hmem hcall
      by_cases h : id' = id
      · rw [h] at hcall hmem; exact absurd hin (hI.input_called r id (hF ▸ hmem) hcall)
      · rw [hNe id' h]; exact hI.call_round r id' (hF ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.w_called r id' (hF ▸ hmem) hcalled
    · intro r id' hmem hr
      by_cases h : id' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id' h] at hr; exact hI.round_flip r id' (hF ▸ hmem) hr
    · intro id' hmem hround hphase
      by_cases h : id' = id
      · subst h; simp [hSelf]
      · rw [hNe id' h] at hround hphase ⊢; exact hI.est0 id' (hF ▸ hmem) hround hphase
    · intro id' b' hlg
      by_cases h : id' = id
      · rw [h] at hlg; rw [hSelf] at hlg
        exact (hI.grade_A_src id b' hlg).imp (fun r => hCertTrans r b')
      · rw [hNe id' h] at hlg
        exact (hI.grade_A_src id' b' hlg).imp (fun r => hCertTrans r b')
    · intro r id' hmem hround hphase
      by_cases h : id' = id
      · subst h; simp [hSelf] at hphase
      · rw [hNe id' h] at hround hphase ⊢; exact hI.est_ret r id' (hF ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_prov r id' v (hF ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      by_cases h : id' = id
      · subst h; simp [hSelf] at hround
      · rw [hNe id' h] at hround hphase hest
        exact hI.est_prev r id' (hF ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      by_cases h : id' = id
      · subst h; simp [hSelf] at hround
      · rw [hNe id' h] at hround hphase ⊢
        exact hI.est_prev_ne id' (hF ▸ hmem) hround hphase
    · intro id' b' h
      rcases hI.input_g0_perm id' b' h with hpre | hf
      · by_cases hid : id' = id
        · rw [hid, hin] at hpre; exact absurd hpre (by simp)
        · left; rw [hNe id' hid]; exact hpre
      · right; rw [hF]; exact hf
    · -- `w_call_round`'s `id' = id` corner: `id` was just idle (`hin`), so `idle_no_wcall`
      -- rules out `id` having ever called any `WCC` instance.
      intro r id' hmem hcalled
      by_cases hid : id' = id
      · rw [hid] at hmem hcalled
        have := hI.idle_no_wcall id (hF ▸ hmem) hin r
        rw [this] at hcalled
        exact absurd hcalled (by simp)
      · rw [hNe id' hid]; exact hI.w_call_round r id' (hF ▸ hmem) hcalled
    · -- `flip_alock`: `g` is untouched entirely; the only wrinkle is the `r = 0` dissent
      -- witness possibly naming `id` itself, ruled out by `hin : input = none` (the fresh
      -- honest input can't have been the opposing dissenter).
      intro r h
      rcases hI.flip_alock r h with hg | hd
      · left; exact hg
      · right
        obtain ⟨v, hbv, hif⟩ := hd
        refine ⟨v, hbv, ?_⟩
        by_cases h0 : r = 0
        · rw [if_pos h0] at hif ⊢
          obtain ⟨id', hid'⟩ := hif
          by_cases hidmatch : id' = id
          · exfalso; rw [hidmatch, hin] at hid'; exact absurd hid' (by simp)
          · exact ⟨id', by rw [hNe id' hidmatch]; exact hid'⟩
        · rw [if_neg h0] at hif ⊢; exact hif
    · intro id' hmem hin' r'
      by_cases h : id' = id
      · subst h; simp [hSelf] at hin'
      · rw [hNe id' h] at hin'; exact hI.idle_no_wcall id' (hF ▸ hmem) hin' r'
    · intro r id' hmem hp
      by_cases h : id' = id
      · subst h; simp [hSelf] at hp
      · rw [hNe id' h] at hp
        rcases hI.retg_residue r id' (hF ▸ hmem) hp with hg | hd
        · left; exact hg
        · right; exact hDissTrans r hd
    · intro r id' hmem hcalled
      rcases hI.wcalled_residue r id' (hF ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact hDissTrans r hd
  · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    exact ⟨hI, AbsFrame.refl P g _⟩

/-- `fail`: a genuine synchronised corruption of all three components; `F` only grows, and
every other projection is untouched, so honesty hypotheses transfer via `F`-monotonicity. -/
theorem Inv.step_fail {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (id : Fin P.n) :
    Inv P (fun r => (g r).corrupt P id) (c.corrupt P id) (fun r => (w r).corrupt P id) ∧
      AbsFrame P g (fun r => (g r).corrupt P id) c (c.corrupt P id) := by
  set g' := fun r => (g r).corrupt P id with hg'def
  set c' := c.corrupt P id with hc'def
  set w' := fun r => (w r).corrupt P id with hw'def
  have hcall : ∀ r, (g' r).call = (g r).call := fun r => GBCA.corrupt_call P (g r) id
  have hbind : ∀ r, (g' r).dead = (g r).dead := fun r => GBCA.corrupt_dead P (g r) id
  have hgrade : ∀ r, (g' r).grade = (g r).grade := fun r => GBCA.corrupt_grade P (g r) id
  have hval : ∀ r, (w' r).val = (w r).val := fun r => WCC.corrupt_val id (w r)
  have hcalled : ∀ r, (w' r).called = (w r).called := fun r => WCC.corrupt_called id (w r)
  have hprocs : c'.procs = c.procs := ABAState.corrupt_procs c id
  have hDS : c'.decidedSent = c.decidedSent := ABAState.corrupt_decidedSent c id
  have hDR : c'.decidedRecv = c.decidedRecv := ABAState.corrupt_decidedRecv c id
  have hFg : ∀ r, (g' r).F = c'.F := fun r => GBCA.corrupt_F_eq id (g r) c (hI.F_g r)
  have hFw : ∀ r, (w' r).F = c'.F := fun r => WCC.corrupt_F_eq id (w r) c (hI.F_w r)
  have hFsub : c.F ⊆ c'.F := by
    rw [hc'def, ABAState.corrupt_F]; split_ifs with hcond
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _
  have hFcard : c'.F.card ≤ P.f := by
    rw [hc'def, ABAState.corrupt_F]; split_ifs with hcond
    · obtain ⟨-, hlt⟩ := hcond
      show (insert id c.F).card ≤ P.f
      have hcard := Finset.card_insert_le id c.F
      omega
    · exact hI.F_card
  have hLastBound : ∀ r, IsLastBound g' r ↔ IsLastBound g r := by
    intro r; unfold IsLastBound; rw [hbind r, hbind (r + 1)]
  have hCarrTrans : ∀ r' id₀ v, Carrier P g' c' r' id₀ v → Carrier P g c r' id₀ v := by
    intro r' id₀ v hc
    unfold Carrier at hc ⊢
    rwa [hprocs, hcall (r' + 1)] at hc
  have hCertTrans : ∀ r' b', ACert P g c r' b' → ACert P g' c' r' b' := fun r' b' =>
    ACert.of_frame (hgrade r') hbind (fun r'' id' => congrFun (hcall r'') id') hFsub
      (fun id' => by rw [hprocs]) (fun id' => by rw [hprocs])
      (fun id0 v => hCarrTrans r' id0 v)
  have hHold : ∀ id₀ b₀, AHolder P c' id₀ b₀ → AHolder P c id₀ b₀ := by
    intro id₀ b₀ h
    unfold AHolder at h ⊢
    rwa [hprocs, hDS] at h
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
    fun v _ hpin j b' hj hh => hpin j b' (fun h0 => hj (hFsub h0)) (hHold j b' hh)⟩
  refine ⟨fun r => hFg r, fun r => hFw r, hFcard, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r v hb => (hI.bind_supp r v (by rw [← hbind r]; exact hb)).mono
      (fun id' b' h => by rw [hprocs]; exact h) hFsub,
    fun r b hgf => GBCA.callSupp_mono (fun id' h => by rw [hcall r]; exact h)
      (by rw [hFg r, hI.F_g r]; exact hFsub)
      (hI.clock_supp r b (by rw [← hgrade r]; exact hgf)),
    fun r b h => GBCA.callSupp_mono (fun id' h' => by rw [hcall r]; exact h')
      (by rw [hFg r, hI.F_g r]; exact hFsub)
      (hI.dead_supp r b (by rw [← hbind r]; exact h)),
    fun r' i j v v' hm hm' h h' => hI.carrier_agree r' i j v v'
      (fun hh => hm (hFsub hh)) (fun hh => hm' (hFsub hh))
      (hCarrTrans _ _ _ h) (hCarrTrans _ _ _ h') |>.imp (fun hh => hh) (fun hh => by
        rw [hgrade r']; exact hh),
    fun i j b₀ b₀' hm hm' h h' => hI.alock_agree i j b₀ b₀'
      (fun hh => hm (hFsub hh)) (fun hh => hm' (hFsub hh))
      (hHold _ _ h) (hHold _ _ h')⟩
  · intro id' b' hmem hcall0
    rw [hprocs]; rw [hcall 0] at hcall0
    exact hI.input_g0 id' b' (fun h => hmem (hFsub h)) hcall0
  · intro r id' hmem hcall0
    rw [hprocs]; rw [hcall r] at hcall0
    exact hI.input_called r id' (fun h => hmem (hFsub h)) hcall0
  · intro id' hmem hne
    rw [hprocs] at hne ⊢; exact hI.phase_input id' (fun h => hmem (hFsub h)) hne
  · intro r h
    rw [Closed.congr (hbind r) (hgrade r)]
    exact hI.down_closed r ((Closed.congr (hbind (r + 1)) (hgrade (r + 1))).mp h)
  · obtain ⟨R, hR⟩ := hI.quiescent
    exact ⟨R, fun r hr h => hR r hr ((Closed.congr (hbind r) (hgrade r)).mp h)⟩
  · intro r h
    rw [hval r] at h; rw [Closed.congr (hbind r) (hgrade r)]
    exact hI.w_bound r h
  · intro i j b' h
    rw [hDR] at h; rw [hDS]
    exact hI.recv_sound i j b' h
  · intro id' b' hmem h
    rw [hDS] at h
    exact (hI.decided_src id' b' (fun h' => hmem (hFsub h')) h).imp (fun r => hCertTrans r b')
  · intro r b' hgr hbr
    rw [hgrade r] at hgr; rw [hbind r] at hbr
    obtain ⟨h1, h2, h3, h4⟩ := hI.a_commit r b' hgr hbr
    refine ⟨fun r' b'' hrr' hb' => ?_, fun r' id' b'' hrr' hmem hcall0 => ?_,
      fun id' hmem hround => ?_,
      fun id0 v hmem hcar => h4 id0 v (fun h => hmem (hFsub h)) (hCarrTrans r id0 v hcar)⟩
    · rw [hbind r'] at hb'; exact h1 r' b'' hrr' hb'
    · rw [hcall r'] at hcall0; exact h2 r' id' b'' hrr' (fun h => hmem (hFsub h)) hcall0
    · rw [hprocs] at hround ⊢; exact h3 id' (fun h => hmem (hFsub h)) hround
  · intro id' hmem r hround
    rw [hprocs] at hround; rw [Closed.congr (hbind r) (hgrade r)]
    exact hI.round_bound id' (fun h => hmem (hFsub h)) r hround
  · intro r v hlast hbr hcoin id' hmem hround
    rw [hLastBound r] at hlast; rw [hbind r] at hbr; rw [hval r] at hcoin
    rw [hprocs] at hround ⊢
    exact hI.agree_locked r v hlast hbr hcoin id' (fun h => hmem (hFsub h)) hround
  · intro r h; rw [hgrade r] at h; rw [hbind r]; exact hI.gradeA_needs_bind r h
  · intro r id' hmem hcall0
    rw [hprocs]; rw [hcall r] at hcall0
    exact hI.call_round r id' (fun h => hmem (hFsub h)) hcall0
  · intro r id' hmem hcalled0
    rw [hcalled r] at hcalled0; rw [Closed.congr (hbind r) (hgrade r)]
    exact hI.w_called r id' (fun h => hmem (hFsub h)) hcalled0
  · intro r id' hmem hround
    rw [hprocs] at hround; rw [hval r]
    exact hI.round_flip r id' (fun h => hmem (hFsub h)) hround
  · intro id' hmem hround hphase
    rw [hprocs] at hround hphase ⊢
    exact hI.est0 id' (fun h => hmem (hFsub h)) hround hphase
  · intro id' b' hlg
    rw [hprocs] at hlg
    exact (hI.grade_A_src id' b' hlg).imp (fun r => hCertTrans r b')
  · intro r id' hmem hround hphase
    rw [hprocs] at hround hphase
    obtain ⟨hnone, hsome⟩ := hI.est_ret r id' (fun h => hmem (hFsub h)) hround hphase
    rw [hprocs]
    refine ⟨fun he => ?_, fun b' hb' => ?_⟩
    · obtain ⟨hg0, hno⟩ := hnone he
      refine ⟨by rw [hgrade]; exact hg0, fun r₀ hr0 hgr0 => ?_⟩
      rw [hgrade] at hgr0
      exact hno r₀ hr0 hgr0
    · rw [hbind]; exact hsome b' hb'
  · intro r v h
    rw [hbind (r + 1)] at h; rw [hbind r, hgrade r, hval r]
    exact hI.bind_succ r v h
  · intro r id' v hmem hcall0
    rw [hcall (r + 1)] at hcall0; rw [hbind r, hgrade r, hval r]
    exact hI.call_prov r id' v (fun h => hmem (hFsub h)) hcall0
  · intro r id' hmem hround hphase v hest
    rw [hprocs] at hround hphase hest; rw [hbind r, hgrade r, hval r]
    exact hI.est_prev r id' (fun h => hmem (hFsub h)) hround hphase v hest
  · intro r h; rw [hgrade (r + 1)] at h; rw [hgrade r]; exact hI.c_chain r h
  · intro id' hmem hround hphase
    rw [hprocs] at hround hphase ⊢
    exact hI.est_prev_ne id' (fun h => hmem (hFsub h)) hround hphase
  · intro r h; rw [hval] at h ⊢; exact hI.w_order r h
  · intro id' b' h
    rw [hcall 0] at h; rw [hprocs]
    rcases hI.input_g0_perm id' b' h with hin | hf
    · left; exact hin
    · right; exact hFsub hf
  · intro r id' hmem hcalled0
    rw [hcalled r] at hcalled0; rw [hprocs]
    exact hI.w_call_round r id' (fun h => hmem (hFsub h)) hcalled0
  · intro r h
    rw [hval] at h
    rcases hI.flip_alock r h with hg | hd
    · left; rw [hgrade]; exact hg
    · right
      exact DissentResidue.transport (hbind r) (hbind (r - 1)) (fun hh => (hgrade (r - 1)) ▸ hh)
        (fun id' => by rw [hprocs]) hd
  · intro id' hmem hin r
    rw [hprocs] at hin; rw [hcalled r]
    exact hI.idle_no_wcall id' (fun h => hmem (hFsub h)) hin r
  · intro r id' hmem hp
    rw [hprocs] at hp
    rcases hI.retg_residue r id' (fun h => hmem (hFsub h)) hp with hg | hd
    · left; rw [hgrade]; exact hg
    · right
      exact DissentResidue.transport (hbind r) (hbind (r - 1)) (fun hh => (hgrade (r - 1)) ▸ hh)
        (fun id' => by rw [hprocs]) hd
  · intro r id' hmem hcalled0
    rw [hcalled r] at hcalled0
    rcases hI.wcalled_residue r id' (fun h => hmem (hFsub h)) hcalled0 with hg | hd
    · left; rw [hgrade]; exact hg
    · right
      exact DissentResidue.transport (hbind r) (hbind (r - 1)) (fun hh => (hgrade (r - 1)) ▸ hh)
        (fun id' => by rw [hprocs]) hd
  · intro r h
    rw [hbind r] at h
    exact GBCA.SpecState.quorum_mono (by rw [hFg r, hI.F_g r]; exact hFsub)
      (fun id' hne => by rw [hcall r]; exact hne) (hI.bound_quorum r h)

/-- `bindUnset` (the GBCA family's only genuine `τ`-step): kills one bit of round `r`'s
exclusion set. `down_closed`'s round-`r` corner needs "a call at round `r` implies current
round `≥ r`", a fact `Inv` doesn't carry explicitly — handed off. The value-transport
corners lean on the kill's own D15 guard: the spared bit `!b` keeps `f + 1` F-blind call
support at round `r`, whose harvested honest caller pins `!b` against every standing
commitment. -/
theorem Inv.step_gbcaTau {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ)
    {μr : PMF (GBCA.SpecState P.n)} (hstep : GBCA.Step P r (g r) .tau μr)
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support) :
    Inv P (Function.update g r gr') c w ∧
      AbsFrame P g (Function.update g r gr') c c := by
  cases hstep
  case bindUnset b _hq _hw hd0 =>
    rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'
    have hb : b ∉ (g r).dead := by rw [hd0]; simp
    set g' := Function.update g r { g r with dead := insert b (g r).dead } with hg'def
    have hFeq : ∀ r', (g' r').F = (g r').F := by
      intro r'; by_cases h : r' = r
      · subst h; rw [hg'def, Function.update_self]
      · rw [hg'def, Function.update_of_ne h]
    have hCalleq : ∀ r', (g' r').call = (g r').call := by
      intro r'; by_cases h : r' = r
      · subst h; rw [hg'def, Function.update_self]
      · rw [hg'def, Function.update_of_ne h]
    have hGradeeq : ∀ r', (g' r').grade = (g r').grade := by
      intro r'; by_cases h : r' = r
      · subst h; rw [hg'def, Function.update_self]
      · rw [hg'def, Function.update_of_ne h]
    have hDeadSelf : (g' r).dead = insert b (g r).dead := by
      rw [hg'def, Function.update_self]
    have hDeadNe : ∀ r', r' ≠ r → (g' r').dead = (g r').dead := by
      intro r' h; rw [hg'def, Function.update_of_ne h]
    have hDeadMono : ∀ r' x, x ∈ (g r').dead → x ∈ (g' r').dead := by
      intro r' x hx
      by_cases h : r' = r
      · subst h; rw [hDeadSelf]; exact Finset.mem_insert_of_mem hx
      · rw [hDeadNe r' h]; exact hx
    obtain ⟨id0, hid0F, hcall0⟩ :=
      GBCA.exists_honest_caller _hw (by rw [hI.F_g r]; exact hI.F_card)
    have hFid0 : id0 ∉ c.F := by rw [← hI.F_g r]; exact hid0F
    have hClosedNe : ∀ r', r' ≠ r → (Closed g' r' ↔ Closed g r') :=
      fun r' h => Closed.congr (hDeadNe r' h) (hGradeeq r')
    have hClosedSelf : Closed g' r := Or.inl (by rw [hDeadSelf]; simp)
    have hDissTrans : ∀ r₀, DissentResidue P g c r₀ → DissentResidue P g' c r₀ := by
      intro r₀ hd
      obtain ⟨v, hbv, hif⟩ := hd
      refine ⟨v, hDeadMono r₀ _ hbv, ?_⟩
      by_cases h0 : r₀ = 0
      · rw [if_pos h0] at hif ⊢; exact hif
      · rw [if_neg h0] at hif ⊢
        rcases hif with hh | hh
        · exact Or.inl (hDeadMono (r₀ - 1) _ hh)
        · exact Or.inr ((hGradeeq (r₀ - 1)).trans hh)
    have hCarrTrans : ∀ r₀ id₀ v, Carrier P g' c r₀ id₀ v → Carrier P g c r₀ id₀ v := by
      intro r₀ id₀ v hc
      unfold Carrier at hc ⊢
      rwa [hCalleq (r₀ + 1)] at hc
    have hCommitTrans : ∀ r'' b'', (!b'') ∈ (g r'').dead → ACommit P g c r'' b'' →
        ACommit P g' c r'' b'' := by
      rintro r'' b'' hres ⟨h1, h2, h3, h4⟩
      refine ⟨fun r₀ b₀ hrr hb' => ?_,
        fun r₀ id₀ b₀ hrr hmem hcall =>
          h2 r₀ id₀ b₀ hrr hmem (by rw [← hCalleq r₀]; exact hcall), h3,
        fun id₀ v hmem hcar => h4 id₀ v hmem (hCarrTrans r'' id₀ v hcar)⟩
      by_cases h3' : r₀ = r
      · subst h3'
        rw [hDeadSelf] at hb'
        have hb₀nd : b₀ ∉ (g r₀).dead := fun hh => hb'.2 (Finset.mem_insert_of_mem hh)
        rcases Finset.mem_insert.mp hb'.1 with hnew | hold
        · rcases eq_or_lt_of_le hrr with heq | hlt
          · have hne : b₀ ≠ !b'' := fun hh => hb₀nd (hh ▸ (heq ▸ hres))
            revert hne; cases b₀ <;> cases b'' <;> simp
          · have hb₀ : b₀ = !b := by revert hnew; cases b₀ <;> cases b <;> simp
            rw [hb₀]; exact h2 r₀ id0 (!b) hlt hFid0 hcall0
        · exact h1 r₀ b₀ hrr ⟨hold, hb₀nd⟩
      · rw [hDeadNe r₀ h3'] at hb'; exact h1 r₀ b₀ hrr hb'
    have hCertTrans : ∀ r'' b'', ACert P g c r'' b'' → ACert P g' c r'' b'' := by
      rintro r'' b'' ⟨hg1, hd1, hcm⟩
      exact ⟨(hGradeeq r'').trans hg1, hDeadMono r'' _ hd1, hCommitTrans r'' b'' hd1 hcm⟩
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
      fun v _ hpin => hpin⟩
    refine ⟨fun r' => (hFeq r').trans (hI.F_g r'), hI.F_w, hI.F_card, ?_, ?_, hI.phase_input,
      ?_, ?_, ?_,
      hI.recv_sound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.round_flip, hI.est0, ?_, ?_,
      ?_, ?_, ?_, ?_, hI.est_prev_ne, hI.w_order, ?_, hI.w_call_round, ?_,
      hI.idle_no_wcall, ?_, ?_, ?_, ?_, ?_, ?_,
      fun r₀ i j v v' hm hm' h h' => (hI.carrier_agree r₀ i j v v' hm hm'
        (hCarrTrans _ _ _ h) (hCarrTrans _ _ _ h')).imp (fun x => x)
        (fun hh => (hGradeeq r₀).trans hh),
      hI.alock_agree⟩
    · intro id b' hmem hcall; rw [hCalleq] at hcall; exact hI.input_g0 id b' hmem hcall
    · intro r' id hmem hcall; rw [hCalleq] at hcall; exact hI.input_called r' id hmem hcall
    · intro r' h
      by_cases h2 : r' = r
      · subst h2; exact hClosedSelf
      · by_cases h1 : r' + 1 = r
        · -- the fresh kill at `r' + 1` had an honest caller of the spared bit, whose
          -- round progress closes `r'`
          obtain ⟨id0, hid0F, hcall0⟩ :=
            GBCA.exists_honest_caller _hw (by rw [hI.F_g r]; exact hI.F_card)
          have hFid0 : id0 ∉ c.F := by rw [← hI.F_g r]; exact hid0F
          have hcr : r ≤ (c.procs id0).round :=
            hI.call_round r id0 hFid0 (by rw [hcall0]; simp)
          rw [hClosedNe r' h2]
          exact hI.round_bound id0 hFid0 r' (by omega)
        · rw [hClosedNe r' h2]
          exact hI.down_closed r' ((hClosedNe (r' + 1) h1).mp h)
    · obtain ⟨R, hR⟩ := hI.quiescent
      exact ⟨max R (r + 1), fun r' hr' h =>
        hR r' (by omega) ((hClosedNe r' (by omega)).mp h)⟩
    · intro r' h
      by_cases h2 : r' = r
      · subst h2; exact hClosedSelf
      · rw [hClosedNe r' h2]; exact hI.w_bound r' h
    · intro id b' hmem h
      exact (hI.decided_src id b' hmem h).imp (fun r'' => hCertTrans r'' b')
    · intro r' b' hgr hbr
      rw [hGradeeq] at hgr
      have hpair : (!b') ∈ (g r').dead ∧ b' ∉ (g r').dead := by
        by_cases h2 : r' = r
        · subst h2
          rw [hDeadSelf] at hbr
          refine ⟨?_, fun hh => hbr.2 (Finset.mem_insert_of_mem hh)⟩
          rcases Finset.mem_insert.mp hbr.1 with hnew | hold
          · -- the fresh kill is `!b'`: the A-locked round already had a dead bit,
            -- which can be neither `b` (`hb`) nor `b'` (still alive), so it is `!b'`
            obtain ⟨wd, hwd⟩ :=
              Finset.nonempty_iff_ne_empty.mpr (hI.gradeA_needs_bind r' hgr)
            have hwb : wd ≠ b := fun hh => hb (hh ▸ hwd)
            have hwb' : wd ≠ b' := fun hh => hbr.2 (Finset.mem_insert_of_mem (hh ▸ hwd))
            have hwd' : wd = !b' := by
              revert hwb hwb' hnew; cases wd <;> cases b' <;> cases b <;> simp
            exact hwd' ▸ hwd
          · exact hold
        · rw [hDeadNe r' h2] at hbr; exact hbr
      exact hCommitTrans r' b' hpair.1 (hI.a_commit r' b' hgr hpair)
    · intro id hmem r' hround
      by_cases h2 : r' = r
      · subst h2; exact hClosedSelf
      · rw [hClosedNe r' h2]; exact hI.round_bound id hmem r' hround
    · intro r' v hlast hbr hcoin id hmem hround
      by_cases h1 : r' + 1 = r
      · exfalso
        have hemp : (g' (r' + 1)).dead = ∅ := hlast.2
        rw [h1, hDeadSelf] at hemp; exact absurd hemp (by simp)
      · by_cases h2 : r' = r
        · have hDeadSelf' : (g' r').dead = insert b (g r').dead := by
            rw [h2]; exact hDeadSelf
          have hbAt : b ∉ (g r').dead := by rw [h2]; exact hb
          have hemp1 : (g (r' + 1)).dead = ∅ := by
            rw [← hDeadNe (r' + 1) h1]; exact hlast.2
          by_cases hdead0 : (g r').dead = ∅
          · -- round `r'` was fresh before this kill, hence already `C`-blocked upward;
            -- `est_prev` pins `id`'s estimate to the agreeing coin's bit.
            have hnoC : (g (r' + 1)).grade ≠ some false :=
              fun hh => hI.no_cgrade_succ r' v hcoin (by rw [hdead0]; simp) hh
            have hround1 : (c.procs id).round = r' + 1 := by
              by_contra hne
              rcases hI.round_bound id hmem (r' + 1) (by omega) with hh | hh
              · exact hh hemp1
              · exact hnoC hh
            by_cases hgroup : (c.procs id).phase = .toCallW ∨ (c.procs id).phase = .awaitW
            · exfalso
              obtain ⟨hnone, hsome⟩ := hI.est_ret (r' + 1) id hmem hround1 hgroup
              rcases Option.eq_none_or_eq_some ((c.procs id).est) with he | ⟨u, he⟩
              · exact hnoC (hnone he).1
              · have hu := hsome u he
                rw [hemp1] at hu; exact absurd hu (by simp)
            · have hphase3 : (c.procs id).phase = .idle ∨ (c.procs id).phase = .toCallG ∨
                  (c.procs id).phase = .awaitG := by
                rcases hph2 : (c.procs id).phase with _ | _ | _ | _ | _
                · exact Or.inl rfl
                · exact Or.inr (Or.inl rfl)
                · exact Or.inr (Or.inr rfl)
                · exact absurd (Or.inl hph2) hgroup
                · exact absurd (Or.inr hph2) hgroup
              obtain ⟨u, he⟩ :=
                Option.ne_none_iff_exists'.mp (hI.est_prev_ne id hmem (by omega) hphase3)
              rw [he]
              rcases hI.est_prev r' id hmem hround1 hphase3 u he with hbu | ⟨-, hw0⟩
              · rw [hdead0] at hbu; simp at hbu
              · rcases hw0 with hh | hh
                · rw [hcoin] at hh; simp only [TVal.bit.injEq] at hh; rw [hh]
                · rw [hcoin] at hh; simp at hh
          · -- round `r'` already had a dead bit, which the live pair pins to `!v`:
            -- the pre-kill pair holds and the old `agree_locked` applies
            have hpairold : (!v) ∈ (g r').dead ∧ v ∉ (g r').dead := by
              rw [hDeadSelf'] at hbr
              refine ⟨?_, fun hh => hbr.2 (Finset.mem_insert_of_mem hh)⟩
              rcases Finset.mem_insert.mp hbr.1 with hnew | hold
              · obtain ⟨wd, hwd⟩ := Finset.nonempty_iff_ne_empty.mpr hdead0
                have hwb : wd ≠ b := fun hh => hbAt (hh ▸ hwd)
                have hwv : wd ≠ v := fun hh => hbr.2 (Finset.mem_insert_of_mem (hh ▸ hwd))
                have hwd' : wd = !v := by
                  revert hwb hwv hnew; cases wd <;> cases v <;> cases b <;> simp
                exact hwd' ▸ hwd
              · exact hold
            have hlast' : IsLastBound g r' :=
              ⟨Finset.nonempty_iff_ne_empty.mp ⟨_, hpairold.1⟩, hemp1⟩
            exact hI.agree_locked r' v hlast' hpairold hcoin id hmem hround
        · have hlast' : IsLastBound g r' := ⟨by rw [← hDeadNe r' h2]; exact hlast.1,
            by rw [← hDeadNe (r' + 1) h1]; exact hlast.2⟩
          rw [hDeadNe r' h2] at hbr
          exact hI.agree_locked r' v hlast' hbr hcoin id hmem hround
    · intro r' h
      by_cases h2 : r' = r
      · subst h2; rw [hDeadSelf]; simp
      · rw [hGradeeq] at h
        rw [hDeadNe r' h2]; exact hI.gradeA_needs_bind r' h
    · intro r' id hmem hcall; rw [hCalleq] at hcall; exact hI.call_round r' id hmem hcall
    · intro r' id hmem hcalled
      by_cases h2 : r' = r
      · subst h2; exact hClosedSelf
      · rw [hClosedNe r' h2]; exact hI.w_called r' id hmem hcalled
    · intro id b hlg
      exact (hI.grade_A_src id b hlg).imp (fun r'' => hCertTrans r'' b)
    · intro r' id hmem hround hphase
      obtain ⟨hnone, hsome⟩ := hI.est_ret r' id hmem hround hphase
      refine ⟨fun he => ?_, fun b' hb' => ?_⟩
      · obtain ⟨hg0, hno⟩ := hnone he
        refine ⟨(hGradeeq r').trans hg0, fun r₀ hr0 hgr0 => ?_⟩
        rw [hGradeeq] at hgr0
        exact hno r₀ hr0 hgr0
      · exact hDeadMono r' _ (hsome b' hb')
    · intro r' v h
      by_cases h1 : r' + 1 = r
      · rw [h1, hDeadSelf] at h
        rcases Finset.mem_insert.mp h with hnew | hold
        · -- the fresh kill: the spared bit `!b = v` was carried by the harvested
          -- honest caller, whose `call_prov` provenance is the conclusion verbatim
          have hveq : v = !b := by revert hnew; cases v <;> cases b <;> simp
          have hcp := hI.call_prov r' id0 (!b) hFid0 (by rw [h1]; exact hcall0)
          rw [← hveq] at hcp
          rcases hcp with hd | ⟨hg0, hw0⟩
          · exact Or.inl (hDeadMono r' _ hd)
          · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
        · rcases hI.bind_succ r' v (by rw [h1]; exact hold) with hd | ⟨hg0, hw0⟩
          · exact Or.inl (hDeadMono r' _ hd)
          · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
      · rw [hDeadNe (r' + 1) h1] at h
        rcases hI.bind_succ r' v h with hd | ⟨hg0, hw0⟩
        · exact Or.inl (hDeadMono r' _ hd)
        · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
    · intro r' id v hmem hcall
      rw [hCalleq] at hcall
      rcases hI.call_prov r' id v hmem hcall with hd | ⟨hg0, hw0⟩
      · exact Or.inl (hDeadMono r' _ hd)
      · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
    · intro r' id hmem hround hphase v hest
      rcases hI.est_prev r' id hmem hround hphase v hest with hd | ⟨hg0, hw0⟩
      · exact Or.inl (hDeadMono r' _ hd)
      · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
    · intro r' h
      rw [hGradeeq] at h ⊢
      exact hI.c_chain r' h
    · intro id b' h; rw [hCalleq] at h; exact hI.input_g0_perm id b' h
    · -- `flip_alock`: `grade` and every residue component are monotone-transported
      intro r' h
      rcases hI.flip_alock r' h with hg | hd
      · left; rw [hGradeeq]; exact hg
      · right; exact hDissTrans r' hd
    · intro r' id hmem hp
      rcases hI.retg_residue r' id hmem hp with hg | hd
      · left; rw [hGradeeq]; exact hg
      · right; exact hDissTrans r' hd
    · intro r' id hmem hcalled
      rcases hI.wcalled_residue r' id hmem hcalled with hg | hd
      · left; rw [hGradeeq]; exact hg
      · right; exact hDissTrans r' hd
    · intro r' h
      by_cases h2 : r' = r
      · rw [h2]
        exact GBCA.SpecState.quorum_of_eq (hFeq r) (hCalleq r) _hq
      · rw [hDeadNe r' h2] at h
        exact GBCA.SpecState.quorum_of_eq (hFeq r') (hCalleq r') (hI.bound_quorum r' h)
    · -- I26 establishment: the fresh kill's D15 count is the spared bit's pool source
      intro r' v hb'
      by_cases h2 : r' = r
      · rw [h2, hDeadSelf] at hb'
        rcases Finset.mem_insert.mp hb' with hnew | hold
        · have hveq : v = !b := by revert hnew; cases v <;> cases b <;> simp
          rw [hveq]
          exact hI.supp_of_call_count r (!b) _hw
        · exact hI.bind_supp r v hold
      · rw [hDeadNe r' h2] at hb'; exact hI.bind_supp r' v hb'
    · intro r' b' hgf
      rw [hGradeeq] at hgf
      exact GBCA.callSupp_mono (fun id' h => by rw [hCalleq r']; exact h) (hFeq r').ge
        (hI.clock_supp r' b' hgf)
    · -- I28 establishment: the fresh kill records its own guard; old kills keep theirs
      intro r' b' hb'
      have hcnt : ∀ r₀ b₀, P.f + 1 ≤ (Finset.univ.filter
          (fun id' => (g r₀).call id' = some (!b₀) ∨ id' ∈ (g r₀).F)).card →
          P.f + 1 ≤ (Finset.univ.filter
          (fun id' => (g' r₀).call id' = some (!b₀) ∨ id' ∈ (g' r₀).F)).card :=
        fun r₀ b₀ hh => GBCA.callSupp_mono (fun id' h => by rw [hCalleq r₀]; exact h)
          (hFeq r₀).ge hh
      by_cases h2 : r' = r
      · rw [h2] at hb' ⊢
        rw [hDeadSelf] at hb'
        rcases Finset.mem_insert.mp hb' with hnew | hold
        · rw [hnew]; exact hcnt r b _hw
        · exact hcnt r b' (hI.dead_supp r b' hold)
      · rw [hDeadNe r' h2] at hb'
        exact hcnt r' b' (hI.dead_supp r' b' hb')

/-- `flip` (the WCC family's only genuine `τ`-step): resolves round `r`'s coin. Only `F_w`,
`w_bound` and `agree_locked` mention `w`; the coin-agreement corner of `agree_locked` (and the
call-implies-bind fact `w_bound` needs at round `r`) are handed off. -/
theorem Inv.step_wccTau {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ)
    {μw' : PMF (WCC.SpecState P.n)} (hstep : WCC.Step P r (w r) .tau μw')
    {wr' : WCC.SpecState P.n} (hwr' : wr' ∈ μw'.support) :
    Inv P g c (Function.update w r wr') ∧ AbsFrame P g g c c := by
  cases hstep
  case flip hq hv =>
    rw [PMF.mem_support_map_iff] at hwr'
    obtain ⟨o, -, hwr'⟩ := hwr'
    set w' := Function.update w r { w r with val := o.toTVal } with hw'def
    rw [← hwr']
    have hFeq : ∀ r', (w' r').F = (w r').F := by
      intro r'; by_cases h : r' = r
      · subst h; rw [hw'def, Function.update_self]
      · rw [hw'def, Function.update_of_ne h]
    have hValNe : ∀ r', r' ≠ r → (w' r').val = (w r').val := by
      intro r' h; rw [hw'def, Function.update_of_ne h]
    have hValSelf : (w' r).val = o.toTVal := by
      rw [hw'def, Function.update_self]
    have hCalledEq : ∀ r', (w' r').called = (w r').called := by
      intro r'; by_cases h : r' = r
      · subst h; rw [hw'def, Function.update_self]
      · rw [hw'def, Function.update_of_ne h]
    refine And.intro ?_ (AbsFrame.refl P g c)
    refine ⟨hI.F_g, fun r' => (hFeq r').trans (hI.F_w r'), hI.F_card, hI.input_g0,
      hI.input_called, hI.phase_input, hI.down_closed, hI.quiescent, ?_, hI.recv_sound,
      hI.decided_src, hI.a_commit, hI.round_bound, ?_, hI.gradeA_needs_bind, hI.call_round, ?_, ?_,
      hI.est0, hI.grade_A_src, hI.est_ret, ?_, ?_, ?_, hI.c_chain, hI.est_prev_ne,
      ?_, hI.input_g0_perm, ?_, ?_, ?_, hI.retg_residue, ?_, hI.bound_quorum,
      hI.bind_supp, hI.clock_supp, hI.dead_supp, hI.carrier_agree, hI.alock_agree⟩
    · intro r' h
      by_cases h2 : r' = r
      · have hq' : (w r').threshold P := by rw [h2]; exact hq
        have hFcardw : (w r').F.card ≤ P.f := by rw [hI.F_w r']; exact hI.F_card
        have hAne : (Finset.univ.filter
            (fun id => id ∉ (w r').F ∧ (w r').called id)).Nonempty := by
          by_contra hemp
          rw [Finset.not_nonempty_iff_eq_empty] at hemp
          unfold WCC.SpecState.threshold at hq'
          rw [hemp, Finset.empty_union] at hq'
          omega
        obtain ⟨id0, hid0⟩ := hAne
        rw [Finset.mem_filter] at hid0
        obtain ⟨-, hid0F, hid0called⟩ := hid0
        have hid0cF : id0 ∉ c.F := by rw [← hI.F_w r']; exact hid0F
        exact hI.w_called r' id0 hid0cF hid0called
      · rw [hValNe r' h2] at h; exact hI.w_bound r' h
    · intro r' v hlast hbr hcoin id hmem hround
      by_cases h2 : r' = r
      · have hround' : r < (c.procs id).round := by rw [← h2]; exact hround
        exact absurd hv (hI.round_flip r id hmem hround')
      · rw [hValNe r' h2] at hcoin
        exact hI.agree_locked r' v hlast hbr hcoin id hmem hround
    · intro r' id hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.w_called r' id hmem hcalled
    · intro r' id hmem hround
      by_cases h2 : r' = r
      · subst h2; rw [hValSelf]; cases o <;> simp [CoinOutcome.toTVal]
      · rw [hValNe r' h2]; exact hI.round_flip r' id hmem hround
    · intro r' v h
      have hb := hI.bind_succ r' v h
      by_cases h2 : r' = r
      · rw [h2] at hb ⊢
        rcases hb with hbv | ⟨hg0, hw0⟩
        · exact Or.inl hbv
        · rcases hw0 with hh | hh <;> rw [hv] at hh <;> simp at hh
      · rw [hValNe r' h2]; exact hb
    · intro r' id v hmem hcall
      have hcp := hI.call_prov r' id v hmem hcall
      by_cases h2 : r' = r
      · rw [h2] at hcp ⊢
        rcases hcp with hbv | ⟨hg0, hw0⟩
        · exact Or.inl hbv
        · rcases hw0 with hh | hh <;> rw [hv] at hh <;> simp at hh
      · rw [hValNe r' h2]; exact hcp
    · intro r' id hmem hround hphase v hest
      have hep := hI.est_prev r' id hmem hround hphase v hest
      by_cases h2 : r' = r
      · rw [h2] at hep ⊢
        rcases hep with hbv | ⟨hg0, hw0⟩
        · exact Or.inl hbv
        · rcases hw0 with hh | hh <;> rw [hv] at hh <;> simp at hh
      · rw [hValNe r' h2]; exact hep
    · -- `w_order`: pass-through, except the newly-flipped round's predecessor, established via
      -- the same honest-caller `Finset` argument as `w_bound` above, chained through
      -- `w_call_round`/`round_flip`.
      intro r' h
      by_cases h2 : r' = r
      · subst h2; rw [hValSelf]; cases o <;> simp [CoinOutcome.toTVal]
      · by_cases h1 : r' + 1 = r
        · have hq' : (w r).threshold P := hq
          have hFcardw : (w r).F.card ≤ P.f := by rw [hI.F_w r]; exact hI.F_card
          have hAne : (Finset.univ.filter
              (fun id => id ∉ (w r).F ∧ (w r).called id)).Nonempty := by
            by_contra hemp
            rw [Finset.not_nonempty_iff_eq_empty] at hemp
            unfold WCC.SpecState.threshold at hq'
            rw [hemp, Finset.empty_union] at hq'
            omega
          obtain ⟨id0, hid0⟩ := hAne
          rw [Finset.mem_filter] at hid0
          obtain ⟨-, hid0F, hid0called⟩ := hid0
          have hid0cF : id0 ∉ c.F := by rw [← hI.F_w r]; exact hid0F
          have hcr := hI.w_call_round r id0 hid0cF hid0called
          rw [hValNe r' h2]
          exact hI.round_flip r' id0 hid0cF (by omega)
        · rw [hValNe (r' + 1) h1] at h; rw [hValNe r' h2]; exact hI.w_order r' h
    · intro r' id hmem hcalled; rw [hCalledEq] at hcalled; exact hI.w_call_round r' id hmem hcalled
    · -- `flip_alock`'s establishment: the threshold on the newly-flipped round `r` yields an
      -- honest caller (`Finset` pigeonhole, as in `w_bound`/`w_order` above), which feeds
      -- `wcalled_residue` directly.
      intro r' h
      by_cases h2 : r' = r
      · have hq' : (w r').threshold P := by rw [h2]; exact hq
        have hFcardw : (w r').F.card ≤ P.f := by rw [hI.F_w r']; exact hI.F_card
        have hAne : (Finset.univ.filter
            (fun id => id ∉ (w r').F ∧ (w r').called id)).Nonempty := by
          by_contra hemp
          rw [Finset.not_nonempty_iff_eq_empty] at hemp
          unfold WCC.SpecState.threshold at hq'
          rw [hemp, Finset.empty_union] at hq'
          omega
        obtain ⟨id0, hid0⟩ := hAne
        rw [Finset.mem_filter] at hid0
        obtain ⟨-, hid0F, hid0called⟩ := hid0
        have hid0cF : id0 ∉ c.F := by rw [← hI.F_w r']; exact hid0F
        exact hI.wcalled_residue r' id0 hid0cF hid0called
      · rw [hValNe r' h2] at h; exact hI.flip_alock r' h
    · intro id hmem hin r'; rw [hCalledEq]; exact hI.idle_no_wcall id hmem hin r'
    · intro r' id hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.wcalled_residue r' id hmem hcalled

/-- Core `τ`: DECIDED delivery, echo, or byzantine injection. All three leave `procs`/`F`
untouched, so only `recv_sound`/`decided_src` need real work; the `echo` case's honest
sender comes from an `f + 1`-vs-`≤ f` pigeonhole on the delivered senders. -/
theorem Inv.step_coreTau {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w)
    {μc : PMF (ABAState P)}
    (hstep :
      (∃ i j b, b ∈ c.decidedSent j ∧ b ∉ c.decidedRecv i j ∧
          μc = PMF.pure (c.deliverDecided i j b)) ∨
        (∃ id b, P.f + 1 ≤ c.decidedCount id b ∧ b ∉ c.decidedSent id ∧
          μc = PMF.pure (c.sendDecided id b)) ∨
        (∃ id b, id ∈ c.F ∧ μc = PMF.pure (c.sendDecided id b)))
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Inv P g c' w ∧ AbsFrame P g g c c' := by
  rcases hstep with ⟨i, j, b, hs, hr, rfl⟩ | ⟨id, b, hcnt, hs, rfl⟩ | ⟨id, b, hF, rfl⟩
  · -- deliver
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    have hProcs : (c.deliverDecided i j b).procs = c.procs := ABAState.deliverDecided_procs _ _ _ _
    have hFeq : (c.deliverDecided i j b).F = c.F := ABAState.deliverDecided_F _ _ _ _
    have hDS : (c.deliverDecided i j b).decidedSent = c.decidedSent :=
      ABAState.deliverDecided_decidedSent _ _ _ _
    have hCert : ∀ r' b', ACert P g c r' b' → ACert P g (c.deliverDecided i j b) r' b' :=
      fun r' b' => ACert.of_frame rfl (fun _ => rfl) (fun _ _ => rfl)
        (by rw [hFeq] : c.F ⊆ _) (fun id' => by rw [hProcs]) (fun id' => by rw [hProcs])
        (fun id0 v hcar => by unfold Carrier at hcar ⊢; rwa [hProcs] at hcar)
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hFeq ▸ hj)
        (by unfold AHolder at hh ⊢; rwa [hProcs, hDS] at hh)⟩
    refine ⟨fun r => by rw [hFeq]; exact hI.F_g r, fun r => by rw [hFeq]; exact hI.F_w r,
      hFeq ▸ hI.F_card, ?_, ?_, ?_, hI.down_closed, hI.quiescent, hI.w_bound, ?_, ?_, ?_, ?_, ?_,
      hI.gradeA_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.c_chain, ?_,
      hI.w_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_supp r v hb).mono
        (fun id' b' h => by rw [hProcs]; exact h) (fun x hx => by rw [hFeq]; exact hx),
      hI.clock_supp, hI.dead_supp,
      fun r' i0 j0 v v' hm hm' h h' => hI.carrier_agree r' i0 j0 v v' (hFeq ▸ hm) (hFeq ▸ hm')
        (by unfold Carrier at h ⊢; rwa [hProcs] at h)
        (by unfold Carrier at h' ⊢; rwa [hProcs] at h'),
      fun i0 j0 b0 b0' hm hm' h h' => hI.alock_agree i0 j0 b0 b0' (hFeq ▸ hm) (hFeq ▸ hm')
        (by unfold AHolder at h ⊢; rwa [hProcs, hDS] at h)
        (by unfold AHolder at h' ⊢; rwa [hProcs, hDS] at h')⟩
    · intro id' b' hmem hcall
      rw [hProcs]; exact hI.input_g0 id' b' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcall
      rw [hProcs]; exact hI.input_called r id' (hFeq ▸ hmem) hcall
    · intro id' hmem hne
      rw [hProcs] at hne ⊢; exact hI.phase_input id' (hFeq ▸ hmem) hne
    · intro i' j' b' h
      rw [hDS]
      by_cases hij : i' = i ∧ j' = j
      · obtain ⟨rfl, rfl⟩ := hij
        rw [ABAState.deliverDecided_decidedRecv_self, Finset.mem_insert] at h
        rcases h with rfl | h
        · exact hs
        · exact hI.recv_sound i' j' b' h
      · rw [ABAState.deliverDecided_decidedRecv_of_ne _ _ _ _ (by tauto)] at h
        exact hI.recv_sound i' j' b' h
    · intro id' b' hmem h
      rw [hDS] at h
      exact (hI.decided_src id' b' (hFeq ▸ hmem) h).imp (fun r => hCert r b')
    · intro r b' hgr hbr
      obtain ⟨h1, h2, h3, h4⟩ := hI.a_commit r b' hgr hbr
      refine ⟨h1, h2, fun id' hmem hround => ?_,
        fun id0 v hmem hcar => h4 id0 v (hFeq ▸ hmem)
          (by unfold Carrier at hcar ⊢; rwa [hProcs] at hcar)⟩
      rw [hProcs] at hround ⊢; exact h3 id' (hFeq ▸ hmem) hround
    · intro id' hmem r hround
      rw [hProcs] at hround; exact hI.round_bound id' (hFeq ▸ hmem) r hround
    · intro r v hlast hbr hcoin id' hmem hround
      rw [hProcs] at hround ⊢; exact hI.agree_locked r v hlast hbr hcoin id' (hFeq ▸ hmem) hround
    · intro r id' hmem hcall; rw [hProcs]; exact hI.call_round r id' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.w_called r id' (hFeq ▸ hmem) hcalled
    · intro r id' hmem hround
      rw [hProcs] at hround; exact hI.round_flip r id' (hFeq ▸ hmem) hround
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢; exact hI.est0 id' (hFeq ▸ hmem) hround hphase
    · intro id' b' hlg
      rw [hProcs] at hlg
      exact (hI.grade_A_src id' b' hlg).imp (fun r => hCert r b')
    · intro r id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢; exact hI.est_ret r id' (hFeq ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_prov r id' v (hFeq ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      rw [hProcs] at hround hphase hest
      exact hI.est_prev r id' (hFeq ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢
      exact hI.est_prev_ne id' (hFeq ▸ hmem) hround hphase
    · intro id' b' h; rw [hProcs]; exact hI.input_g0_perm id' b' h
    · intro r id' hmem hcalled; rw [hProcs]; exact hI.w_call_round r id' (hFeq ▸ hmem) hcalled
    · intro r h
      rcases hI.flip_alock r h with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro id' hmem hin r; rw [hProcs] at hin; exact hI.idle_no_wcall id' (hFeq ▸ hmem) hin r
    · intro r id' hmem hp
      rw [hProcs] at hp
      rcases hI.retg_residue r id' (hFeq ▸ hmem) hp with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro r id' hmem hcalled
      rcases hI.wcalled_residue r id' (hFeq ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
  · -- echo: an honest sender among the `f + 1` counted deliveries
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    have hProcs : (c.sendDecided id b).procs = c.procs := ABAState.sendDecided_procs _ _ _
    have hFeq : (c.sendDecided id b).F = c.F := ABAState.sendDecided_F _ _ _
    have hDR : (c.sendDecided id b).decidedRecv = c.decidedRecv :=
      ABAState.sendDecided_decidedRecv _ _ _
    have hcnt' : P.f + 1 ≤ (Finset.univ.filter (fun j => b ∈ c.decidedRecv id j)).card :=
      hcnt
    have hcard : c.F.card < (Finset.univ.filter (fun j => b ∈ c.decidedRecv id j)).card := by
      have := hI.F_card
      omega
    obtain ⟨j, hjmem, hjF⟩ :=
      (Finset.not_subset (s := Finset.univ.filter (fun j => b ∈ c.decidedRecv id j))
        (t := c.F)).mp (fun hsub => absurd (Finset.card_le_card hsub) (by omega))
    rw [Finset.mem_filter] at hjmem
    have hjsent : b ∈ c.decidedSent j := hI.recv_sound id j b hjmem.2
    obtain ⟨r0, hcert0⟩ := hI.decided_src j b hjF hjsent
    have hCert : ∀ r' b', ACert P g c r' b' → ACert P g (c.sendDecided id b) r' b' :=
      fun r' b' => ACert.of_frame rfl (fun _ => rfl) (fun _ _ => rfl)
        (by rw [hFeq] : c.F ⊆ _) (fun id' => by rw [hProcs]) (fun id' => by rw [hProcs])
        (fun id0 v hcar => by unfold Carrier at hcar ⊢; rwa [hProcs] at hcar)
    have hHold : ∀ i0 b0, i0 ∉ c.F → AHolder P (c.sendDecided id b) i0 b0 →
        ∃ j0, j0 ∉ c.F ∧ AHolder P c j0 b0 := by
      intro i0 b0 hm h
      rcases h with h | h
      · rw [hProcs] at h; exact ⟨i0, hm, Or.inl h⟩
      · rcases (ABAState.mem_sendDecided_decidedSent_iff _ _ _ _ _).mp h with ⟨-, rfl⟩ | h
        · exact ⟨j, hjF, Or.inr hjsent⟩
        · exact ⟨i0, hm, Or.inr h⟩
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => by
        obtain ⟨j0, hj0, hh0⟩ := hHold j b' (hFeq ▸ hj) hh
        exact hpin j0 b' hj0 hh0⟩
    refine ⟨fun r => by rw [hFeq]; exact hI.F_g r, fun r => by rw [hFeq]; exact hI.F_w r,
      hFeq ▸ hI.F_card, ?_, ?_, ?_, hI.down_closed, hI.quiescent, hI.w_bound, ?_, ?_, ?_, ?_, ?_,
      hI.gradeA_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.c_chain, ?_,
      hI.w_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_supp r v hb).mono
        (fun id' b' h => by rw [hProcs]; exact h) (fun x hx => by rw [hFeq]; exact hx),
      hI.clock_supp, hI.dead_supp,
      fun r' i0 j0 v v' hm hm' h h' => hI.carrier_agree r' i0 j0 v v' (hFeq ▸ hm) (hFeq ▸ hm')
        (by unfold Carrier at h ⊢; rwa [hProcs] at h)
        (by unfold Carrier at h' ⊢; rwa [hProcs] at h'),
      fun i0 j0 b0 b0' hm hm' h h' => by
        obtain ⟨ja, hjaF, hja⟩ := hHold i0 b0 (hFeq ▸ hm) h
        obtain ⟨jb, hjbF, hjb⟩ := hHold j0 b0' (hFeq ▸ hm') h'
        exact hI.alock_agree ja jb b0 b0' hjaF hjbF hja hjb⟩
    · intro id' b' hmem hcall
      rw [hProcs]; exact hI.input_g0 id' b' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcall
      rw [hProcs]; exact hI.input_called r id' (hFeq ▸ hmem) hcall
    · intro id' hmem hne
      rw [hProcs] at hne ⊢; exact hI.phase_input id' (hFeq ▸ hmem) hne
    · intro i' j' b' h
      rw [hDR] at h
      exact ABAState.sendDecided_decidedSent_mono _ _ _ (hI.recv_sound i' j' b' h)
    · intro id' b' hmem h
      rw [ABAState.sendDecided_decidedSent] at h
      by_cases hid : id' = id
      · subst hid
        rw [Function.update_self, Finset.mem_insert] at h
        rcases h with rfl | h
        · exact ⟨r0, hCert r0 b' hcert0⟩
        · exact (hI.decided_src id' b' (hFeq ▸ hmem) h).imp (fun r => hCert r b')
      · rw [Function.update_of_ne hid] at h
        exact (hI.decided_src id' b' (hFeq ▸ hmem) h).imp (fun r => hCert r b')
    · intro r b' hgr hbr
      obtain ⟨h1, h2, h3, h4⟩ := hI.a_commit r b' hgr hbr
      refine ⟨h1, h2, fun id' hmem hround => ?_,
        fun id0 v hmem hcar => h4 id0 v (hFeq ▸ hmem)
          (by unfold Carrier at hcar ⊢; rwa [hProcs] at hcar)⟩
      rw [hProcs] at hround ⊢; exact h3 id' (hFeq ▸ hmem) hround
    · intro id' hmem r hround
      rw [hProcs] at hround; exact hI.round_bound id' (hFeq ▸ hmem) r hround
    · intro r v hlast hbr hcoin id' hmem hround
      rw [hProcs] at hround ⊢; exact hI.agree_locked r v hlast hbr hcoin id' (hFeq ▸ hmem) hround
    · intro r id' hmem hcall; rw [hProcs]; exact hI.call_round r id' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.w_called r id' (hFeq ▸ hmem) hcalled
    · intro r id' hmem hround
      rw [hProcs] at hround; exact hI.round_flip r id' (hFeq ▸ hmem) hround
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢; exact hI.est0 id' (hFeq ▸ hmem) hround hphase
    · intro id' b' hlg
      rw [hProcs] at hlg; exact hI.grade_A_src id' b' hlg
    · intro r id' hmem hround hphase
      rw [hProcs] at hround hphase; exact hI.est_ret r id' (hFeq ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_prov r id' v (hFeq ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      rw [hProcs] at hround hphase hest
      exact hI.est_prev r id' (hFeq ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢
      exact hI.est_prev_ne id' (hFeq ▸ hmem) hround hphase
    · intro id' b' h; rw [hProcs]; exact hI.input_g0_perm id' b' h
    · intro r id' hmem hcalled; rw [hProcs]; exact hI.w_call_round r id' (hFeq ▸ hmem) hcalled
    · intro r h
      rcases hI.flip_alock r h with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro id' hmem hin r; rw [hProcs] at hin; exact hI.idle_no_wcall id' (hFeq ▸ hmem) hin r
    · intro r id' hmem hp
      rw [hProcs] at hp
      rcases hI.retg_residue r id' (hFeq ▸ hmem) hp with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro r id' hmem hcalled
      rcases hI.wcalled_residue r id' (hFeq ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
  · -- byzantine DECIDED injection: `id ∈ F`, so honest `decided_src` at `id` is vacuous
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    have hProcs : (c.sendDecided id b).procs = c.procs := ABAState.sendDecided_procs _ _ _
    have hFeq : (c.sendDecided id b).F = c.F := ABAState.sendDecided_F _ _ _
    have hDR : (c.sendDecided id b).decidedRecv = c.decidedRecv :=
      ABAState.sendDecided_decidedRecv _ _ _
    have hCert : ∀ r' b', ACert P g c r' b' → ACert P g (c.sendDecided id b) r' b' :=
      fun r' b' => ACert.of_frame rfl (fun _ => rfl) (fun _ _ => rfl)
        (by rw [hFeq] : c.F ⊆ _) (fun id' => by rw [hProcs]) (fun id' => by rw [hProcs])
        (fun id0 v hcar => by unfold Carrier at hcar ⊢; rwa [hProcs] at hcar)
    have hHold : ∀ i0 b0, i0 ∉ c.F → AHolder P (c.sendDecided id b) i0 b0 →
        AHolder P c i0 b0 := by
      intro i0 b0 hm h
      rcases h with h | h
      · rw [hProcs] at h; exact Or.inl h
      · rcases (ABAState.mem_sendDecided_decidedSent_iff _ _ _ _ _).mp h with ⟨rfl, rfl⟩ | h
        · exact absurd hF hm
        · exact Or.inr h
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hFeq ▸ hj) (hHold j b' (hFeq ▸ hj) hh)⟩
    refine ⟨fun r => by rw [hFeq]; exact hI.F_g r, fun r => by rw [hFeq]; exact hI.F_w r,
      hFeq ▸ hI.F_card, ?_, ?_, ?_, hI.down_closed, hI.quiescent, hI.w_bound, ?_, ?_, ?_, ?_, ?_,
      hI.gradeA_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.c_chain, ?_,
      hI.w_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_supp r v hb).mono
        (fun id' b' h => by rw [hProcs]; exact h) (fun x hx => by rw [hFeq]; exact hx),
      hI.clock_supp, hI.dead_supp,
      fun r' i0 j0 v v' hm hm' h h' => hI.carrier_agree r' i0 j0 v v' (hFeq ▸ hm) (hFeq ▸ hm')
        (by unfold Carrier at h ⊢; rwa [hProcs] at h)
        (by unfold Carrier at h' ⊢; rwa [hProcs] at h'),
      fun i0 j0 b0 b0' hm hm' h h' => hI.alock_agree i0 j0 b0 b0' (hFeq ▸ hm) (hFeq ▸ hm')
        (hHold i0 b0 (hFeq ▸ hm) h) (hHold j0 b0' (hFeq ▸ hm') h')⟩
    · intro id' b' hmem hcall
      rw [hProcs]; exact hI.input_g0 id' b' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcall
      rw [hProcs]; exact hI.input_called r id' (hFeq ▸ hmem) hcall
    · intro id' hmem hne
      rw [hProcs] at hne ⊢; exact hI.phase_input id' (hFeq ▸ hmem) hne
    · intro i' j' b' h
      rw [hDR] at h
      exact ABAState.sendDecided_decidedSent_mono _ _ _ (hI.recv_sound i' j' b' h)
    · intro id' b' hmem h
      rw [ABAState.sendDecided_decidedSent] at h
      by_cases hid : id' = id
      · subst hid; exact absurd (hFeq ▸ hmem) (not_not.mpr hF)
      · rw [Function.update_of_ne hid] at h
        exact (hI.decided_src id' b' (hFeq ▸ hmem) h).imp (fun r => hCert r b')
    · intro r b' hgr hbr
      obtain ⟨h1, h2, h3, h4⟩ := hI.a_commit r b' hgr hbr
      refine ⟨h1, h2, fun id' hmem hround => ?_,
        fun id0 v hmem hcar => h4 id0 v (hFeq ▸ hmem)
          (by unfold Carrier at hcar ⊢; rwa [hProcs] at hcar)⟩
      rw [hProcs] at hround ⊢; exact h3 id' (hFeq ▸ hmem) hround
    · intro id' hmem r hround
      rw [hProcs] at hround; exact hI.round_bound id' (hFeq ▸ hmem) r hround
    · intro r v hlast hbr hcoin id' hmem hround
      rw [hProcs] at hround ⊢; exact hI.agree_locked r v hlast hbr hcoin id' (hFeq ▸ hmem) hround
    · intro r id' hmem hcall; rw [hProcs]; exact hI.call_round r id' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.w_called r id' (hFeq ▸ hmem) hcalled
    · intro r id' hmem hround
      rw [hProcs] at hround; exact hI.round_flip r id' (hFeq ▸ hmem) hround
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢; exact hI.est0 id' (hFeq ▸ hmem) hround hphase
    · intro id' b' hlg
      rw [hProcs] at hlg
      exact (hI.grade_A_src id' b' hlg).imp (fun r => hCert r b')
    · intro r id' hmem hround hphase
      rw [hProcs] at hround hphase; exact hI.est_ret r id' (hFeq ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_prov r id' v (hFeq ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      rw [hProcs] at hround hphase hest
      exact hI.est_prev r id' (hFeq ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢
      exact hI.est_prev_ne id' (hFeq ▸ hmem) hround hphase
    · intro id' b' h; rw [hProcs]; exact hI.input_g0_perm id' b' h
    · intro r id' hmem hcalled; rw [hProcs]; exact hI.w_call_round r id' (hFeq ▸ hmem) hcalled
    · intro r h
      rcases hI.flip_alock r h with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro id' hmem hin r; rw [hProcs] at hin; exact hI.idle_no_wcall id' (hFeq ▸ hmem) hin r
    · intro r id' hmem hp
      rw [hProcs] at hp
      rcases hI.retg_residue r id' (hFeq ▸ hmem) hp with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro r id' hmem hcalled
      rcases hI.wcalled_residue r id' (hFeq ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd

/-- `callW`: the WCC instance only ever touches `.called` (never `.val`/`.F`), and the core
only ever touches `.phase` at `id` (never `.input`/`.est`/`.round`); `Inv` doesn't inspect
either, so this is pure bookkeeping. -/
theorem Inv.step_callW {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ) (id : Fin P.n)
    {μw' : PMF (WCC.SpecState P.n)} (hstepW : WCC.Step P r (w r) (.callW r id) μw')
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.procs id).phase = .toCallW ∧ (c.procs id).round = r ∧
          μc = PMF.pure (c.setProc id { c.procs id with phase := .awaitW })) ∨
        (id ∈ c.F ∧ μc = PMF.pure c))
    {wr' : WCC.SpecState P.n} (hwr' : wr' ∈ μw'.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Inv P g c' (Function.update w r wr') ∧ AbsFrame P g g c c' := by
  have hWeq : (Function.update w r wr' r).F = (w r).F ∧
      (Function.update w r wr' r).val = (w r).val := by
    rw [Function.update_self]
    cases hstepW with
    | call h => rw [PMF.mem_support_pure_iff] at hwr'; subst hwr'; exact ⟨rfl, rfl⟩
    | callLoop => rw [PMF.mem_support_pure_iff] at hwr'; subst hwr'; exact ⟨rfl, rfl⟩
  have hWNe : ∀ r', r' ≠ r → Function.update w r wr' r' = w r' := fun r' h =>
    Function.update_of_ne h wr' w
  have hFweq : ∀ r', (Function.update w r wr' r').F = (w r').F := by
    intro r'; by_cases h : r' = r
    · subst h; exact hWeq.1
    · rw [hWNe r' h]
  have hValeq : ∀ r', (Function.update w r wr' r').val = (w r').val := by
    intro r'; by_cases h : r' = r
    · subst h; exact hWeq.2
    · rw [hWNe r' h]
  have hCframe : c'.F = c.F ∧ c'.decidedSent = c.decidedSent ∧ c'.decidedRecv = c.decidedRecv ∧
      ∀ id', (c'.procs id').input = (c.procs id').input ∧ (c'.procs id').est = (c.procs id').est ∧
        (c'.procs id').round = (c.procs id').round := by
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
      refine ⟨ABAState.setProc_F _ _ _, ABAState.setProc_decidedSent _ _ _,
        ABAState.setProc_decidedRecv _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [ABAState.setProc_procs_self]; exact ⟨rfl, rfl, rfl⟩
      · rw [ABAState.setProc_procs_ne _ _ _ h]; exact ⟨rfl, rfl, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
      exact ⟨rfl, rfl, rfl, fun id' => ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨hCF, hCDS, hCDR, hCprocs⟩ := hCframe
  have hCstep : ((c.procs id).phase = .toCallW ∧ (c.procs id).round = r ∧
      c' = c.setProc id { c.procs id with phase := .awaitW }) ∨ (id ∈ c.F ∧ c' = c) := by
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inl ⟨hph, hr, hc'⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inr ⟨hF, hc'⟩
  have hLastGrade : ∀ id', (c'.procs id').lastGrade = (c.procs id').lastGrade := by
    rcases hCstep with ⟨-, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · intro id'; rw [hc'eq]; by_cases h : id' = id
      · subst h; rw [ABAState.setProc_procs_self]
      · rw [ABAState.setProc_procs_ne _ _ _ h]
    · intro id'; rw [hc'eq]
  have hCarr : ∀ r₀ id₀ v, Carrier P g c' r₀ id₀ v → Carrier P g c r₀ id₀ v := by
    intro r₀ id₀ v hc0
    rcases hc0 with h | ⟨he, hk⟩
    · exact Or.inl h
    · refine Or.inr ⟨(hCprocs id₀).2.1 ▸ he, ?_⟩
      rcases hCstep with ⟨hph, hrid, hc'eq⟩ | ⟨-, hc'eq⟩
      · by_cases hid : id₀ = id
        · subst hid
          rw [hc'eq, ABAState.setProc_procs_self] at hk
          rcases hk with ⟨hr0, -⟩ | ⟨-, hp⟩
          · exact Or.inl ⟨hr0, Or.inl hph⟩
          · exfalso; rcases hp with hp | hp | hp <;> simp at hp
        · rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hk
          exact hk
      · rw [hc'eq] at hk; exact hk
  have hCert : ∀ r' b', ACert P g c r' b' → ACert P g c' r' b' :=
    fun r' b' => ACert.of_frame rfl (fun _ => rfl) (fun _ _ => rfl)
      (by rw [hCF] : c.F ⊆ _) (fun id' => (hCprocs id').2.2) (fun id' => (hCprocs id').2.1)
      (fun id0 v => hCarr r' id0 v)
  have hHold : ∀ i0 b0, AHolder P c' i0 b0 → AHolder P c i0 b0 := by
    intro i0 b0 h
    unfold AHolder at h ⊢
    rwa [hLastGrade, hCDS] at h
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
    fun v _ hpin j b' hj hh => hpin j b' (hCF ▸ hj) (hHold j b' hh)⟩
  refine ⟨fun r' => hCF ▸ hI.F_g r', fun r' => (hFweq r').trans (hCF ▸ hI.F_w r'), hCF ▸ hI.F_card,
    ?_, ?_, ?_, hI.down_closed, hI.quiescent, ?_, ?_, ?_, ?_, ?_, ?_,
    hI.gradeA_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.c_chain, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
    fun r' v hb => (hI.bind_supp r' v hb).mono
      (fun id' b' h => by rw [(hCprocs id').1]; exact h) (fun x hx => by rw [hCF]; exact hx),
    hI.clock_supp, hI.dead_supp,
    fun r₀ i0 j0 v v' hm hm' h h' => hI.carrier_agree r₀ i0 j0 v v' (hCF ▸ hm) (hCF ▸ hm')
      (hCarr _ _ _ h) (hCarr _ _ _ h'),
    fun i0 j0 b0 b0' hm hm' h h' => hI.alock_agree i0 j0 b0 b0' (hCF ▸ hm) (hCF ▸ hm')
      (hHold _ _ h) (hHold _ _ h')⟩
  · intro id' b' hmem hcall; rw [(hCprocs id').1]; exact hI.input_g0 id' b' (hCF ▸ hmem) hcall
  · intro r' id' hmem hcall
    rw [(hCprocs id').1]; exact hI.input_called r' id' (hCF ▸ hmem) hcall
  · intro id' hmem hne
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid, (hCprocs id).1]
        have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
        exact hI.phase_input id hmem' (by rw [hph]; simp)
      · rw [(hCprocs id').1]
        have hne' : (c.procs id').phase ≠ .idle := by
          rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hne; exact hne
        exact hI.phase_input id' (hCF ▸ hmem) hne'
    · rw [hc'eq] at hne; rw [(hCprocs id').1]; exact hI.phase_input id' (hCF ▸ hmem) hne
  · intro r' h; rw [hValeq] at h; exact hI.w_bound r' h
  · intro i j b h; rw [hCDR] at h; rw [hCDS]; exact hI.recv_sound i j b h
  · intro id' b' hmem h; rw [hCDS] at h
    exact (hI.decided_src id' b' (hCF ▸ hmem) h).imp (fun r' => hCert r' b')
  · intro r' b' hgr hbr
    obtain ⟨h1, h2, h3, h4⟩ := hI.a_commit r' b' hgr hbr
    refine ⟨h1, fun r'' id' b'' hr hmem hcall => h2 r'' id' b'' hr (hCF ▸ hmem) hcall,
      fun id' hmem hround => ?_,
      fun id0 v hmem hcar => h4 id0 v (hCF ▸ hmem) (hCarr r' id0 v hcar)⟩
    rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1]; exact h3 id' (hCF ▸ hmem) hround
  · intro id' hmem r' hround
    rw [(hCprocs id').2.2] at hround; exact hI.round_bound id' (hCF ▸ hmem) r' hround
  · intro r' v hlast hbr hcoin id' hmem hround
    rw [hValeq] at hcoin; rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1]
    exact hI.agree_locked r' v hlast hbr hcoin id' (hCF ▸ hmem) hround
  · intro r' id' hmem hcall
    rw [(hCprocs id').2.2]; exact hI.call_round r' id' (hCF ▸ hmem) hcall
  · intro r' id' hmem hcalled
    by_cases h2 : r' = r
    · rw [h2] at hcalled ⊢
      simp only [Function.update_self] at hcalled
      by_cases hid : id' = id
      · rw [hid] at hmem
        rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · obtain ⟨hnone, hsome⟩ := hI.est_ret r id (hCF ▸ hmem) hr (Or.inl hph)
          by_cases hE : (c.procs id).est = none
          · exact Or.inr (hnone hE).1
          · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hE
            exact Or.inl (fun hemp => by
              have hm := hsome b hb
              rw [hemp] at hm
              simp at hm)
        · exact absurd (hCF ▸ hmem) (not_not.mpr hF)
      · cases hstepW with
        | call h =>
          rw [PMF.mem_support_pure_iff] at hwr'
          subst hwr'
          simp only [Function.update_of_ne hid] at hcalled
          exact hI.w_called r id' (hCF ▸ hmem) hcalled
        | callLoop =>
          rw [PMF.mem_support_pure_iff] at hwr'
          subst hwr'
          exact hI.w_called r id' (hCF ▸ hmem) hcalled
    · rw [hWNe r' h2] at hcalled; exact hI.w_called r' id' (hCF ▸ hmem) hcalled
  · intro r' id' hmem hround
    rw [hValeq]; rw [(hCprocs id').2.2] at hround
    exact hI.round_flip r' id' (hCF ▸ hmem) hround
  · intro id' hmem hround hphase
    rw [(hCprocs id').2.2] at hround
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid] at hphase
        simp only [hc'eq, ABAState.setProc_procs_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · simp only [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hphase
        rw [(hCprocs id').2.1, (hCprocs id').1]; exact hI.est0 id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase
      rw [(hCprocs id').2.1, (hCprocs id').1]; exact hI.est0 id' (hCF ▸ hmem) hround hphase
  · intro id' b' hlg
    rw [hLastGrade] at hlg
    exact (hI.grade_A_src id' b' hlg).imp (fun r' => hCert r' b')
  · intro r' id' hmem hround hphase
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · have hround' : (c.procs id).round = r' := by
          rw [hid] at hround
          simpa [hc'eq, ABAState.setProc_procs_self] using hround
        have hreq : r' = r := hround'.symm.trans hr
        rw [hid, hreq, (hCprocs id).2.1]
        exact hI.est_ret r id (hCF ▸ (hid ▸ hmem)) hr (Or.inl hph)
      · simp only [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hround hphase
        rw [(hCprocs id').2.1]
        exact hI.est_ret r' id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hround hphase
      rw [(hCprocs id').2.1]
      exact hI.est_ret r' id' (hCF ▸ hmem) hround hphase
  · intro r' v h; rw [hValeq]; exact hI.bind_succ r' v h
  · intro r' id' v hmem hcall; rw [hValeq]; exact hI.call_prov r' id' v (hCF ▸ hmem) hcall
  · intro r' id' hmem hround hphase v hest
    rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1] at hest; rw [hValeq]
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid] at hphase
        simp only [hc'eq, ABAState.setProc_procs_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · simp only [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hphase
        exact hI.est_prev r' id' (hCF ▸ hmem) hround hphase v hest
    · rw [hc'eq] at hphase
      exact hI.est_prev r' id' (hCF ▸ hmem) hround hphase v hest
  · intro id' hmem hround hphase
    rw [(hCprocs id').2.2] at hround
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid] at hphase
        simp only [hc'eq, ABAState.setProc_procs_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · simp only [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hphase
        rw [(hCprocs id').2.1]
        exact hI.est_prev_ne id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase
      rw [(hCprocs id').2.1]
      exact hI.est_prev_ne id' (hCF ▸ hmem) hround hphase
  · intro r' h; rw [hValeq] at h ⊢; exact hI.w_order r' h
  · intro id' b' h
    rcases hI.input_g0_perm id' b' h with hin | hf
    · left; rw [(hCprocs id').1]; exact hin
    · right; rw [hCF]; exact hf
  · -- `w_call_round`'s establishment: an honest caller of `WCC_r` just finished `GBCA_r`
    -- (`r ≤ round` from `hr : (c.procs id).round = r`, unaffected by `callW`).
    intro r' id' hmem hcalled
    by_cases h2 : r' = r
    · rw [h2] at hcalled ⊢
      simp only [Function.update_self] at hcalled
      by_cases hid : id' = id
      · rw [hid, (hCprocs id).2.2]
        rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · omega
        · rw [hid] at hmem; exact absurd (hCF ▸ hmem) (not_not.mpr hF)
      · cases hstepW with
        | call h =>
          rw [PMF.mem_support_pure_iff] at hwr'
          subst hwr'
          simp only [Function.update_of_ne hid] at hcalled
          rw [(hCprocs id').2.2]; exact hI.w_call_round r id' (hCF ▸ hmem) hcalled
        | callLoop =>
          rw [PMF.mem_support_pure_iff] at hwr'
          subst hwr'
          rw [(hCprocs id').2.2]; exact hI.w_call_round r id' (hCF ▸ hmem) hcalled
    · rw [hWNe r' h2] at hcalled
      rw [(hCprocs id').2.2]; exact hI.w_call_round r' id' (hCF ▸ hmem) hcalled
  · intro r' h
    rw [hValeq] at h
    rcases hI.flip_alock r' h with hg | hd
    · left; exact hg
    · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
  · intro id' hmem hin r'
    by_cases h2 : r' = r
    · rw [h2, Function.update_self]
      rw [(hCprocs id').1] at hin
      by_cases hid : id' = id
      · exfalso
        rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · rw [hid] at hin
          have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
          exact absurd hin (hI.phase_input id hmem' (by rw [hph]; simp))
        · rw [hid] at hmem; exact hmem (hCF ▸ hF)
      · cases hstepW with
        | call h =>
          rw [PMF.mem_support_pure_iff] at hwr'
          subst hwr'
          simp only [Function.update_of_ne hid]
          exact hI.idle_no_wcall id' (hCF ▸ hmem) hin r
        | callLoop =>
          rw [PMF.mem_support_pure_iff] at hwr'
          subst hwr'
          exact hI.idle_no_wcall id' (hCF ▸ hmem) hin r
    · rw [hWNe r' h2]
      rw [(hCprocs id').1] at hin
      exact hI.idle_no_wcall id' (hCF ▸ hmem) hin r'
  · intro r' id' hmem hp
    rw [(hCprocs id').2.2] at hp
    have hphaseImp : ((c'.procs id').phase = .toCallW ∨ (c'.procs id').phase = .awaitW) →
        ((c.procs id').phase = .toCallW ∨ (c.procs id').phase = .awaitW) := by
      intro hph2
      rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
      · by_cases hid : id' = id
        · exact Or.inl (hid ▸ hph)
        · rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hph2; exact hph2
      · rw [hc'eq] at hph2; exact hph2
    have hp' : ((c.procs id').round = r' ∧
        ((c.procs id').phase = .toCallW ∨ (c.procs id').phase = .awaitW)) ∨
        r' < (c.procs id').round := by
      rcases hp with ⟨hround, hphase⟩ | hlt
      · exact Or.inl ⟨hround, hphaseImp hphase⟩
      · exact Or.inr hlt
    rcases hI.retg_residue r' id' (hCF ▸ hmem) hp' with hg | hd
    · left; exact hg
    · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
  · intro r' id' hmem hcalled
    by_cases h2 : r' = r
    · rw [h2] at hcalled ⊢
      simp only [Function.update_self] at hcalled
      by_cases hid : id' = id
      · rw [hid] at hmem
        rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · rcases hI.retg_residue r id (hCF ▸ hmem) (Or.inl ⟨hr, Or.inl hph⟩) with hg | hd
          · left; exact hg
          · right
            exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
        · exact absurd (hCF ▸ hmem) (not_not.mpr hF)
      · cases hstepW with
        | call h =>
          rw [PMF.mem_support_pure_iff] at hwr'
          subst hwr'
          simp only [Function.update_of_ne hid] at hcalled
          rcases hI.wcalled_residue r id' (hCF ▸ hmem) hcalled with hg | hd
          · left; exact hg
          · right
            exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
        | callLoop =>
          rw [PMF.mem_support_pure_iff] at hwr'
          subst hwr'
          rcases hI.wcalled_residue r id' (hCF ▸ hmem) hcalled with hg | hd
          · left; exact hg
          · right
            exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
    · rw [hWNe r' h2] at hcalled
      rcases hI.wcalled_residue r' id' (hCF ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd

/-- `callG`: the GBCA instance only ever touches `.call` (never `.F`/`.dead`/`.grade`), the
core only ever touches `.phase` at `id` (never `.input`/`.est`/`.round`). `input_g0`/
`input_called`'s honest-fresh-call corner needs "`est = input` before any round-`0` return"
(phase/input coherence, not an explicit `Inv` conjunct) — handed off; `a_commit`'s second
conjunct is derived cleanly from its own third conjunct plus the honest call guard
`est = b`. -/
theorem Inv.step_callG {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ) (id : Fin P.n) (b : Bool)
    {μr : PMF (GBCA.SpecState P.n)} (hstepG : GBCA.Step P r (g r) (.callG r id b) μr)
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.procs id).phase = .toCallG ∧ (c.procs id).round = r ∧
          (c.procs id).est = some b ∧
          μc = PMF.pure (c.setProc id { c.procs id with phase := .awaitG })) ∨
        (id ∈ c.F ∧ μc = PMF.pure c))
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Inv P (Function.update g r gr') c' w ∧
      AbsFrame P g (Function.update g r gr') c c' := by
  have hGframe : gr'.F = (g r).F ∧ gr'.dead = (g r).dead ∧ gr'.grade = (g r).grade := by
    cases hstepG with
    | call h => rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'; exact ⟨rfl, rfl, rfl⟩
    | callLoop => rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'; exact ⟨rfl, rfl, rfl⟩
  have hGeq : ∀ r', r' ≠ r → Function.update g r gr' r' = g r' := fun r' h =>
    Function.update_of_ne h gr' g
  have hFgeq : ∀ r', (Function.update g r gr' r').F = (g r').F := by
    intro r'; by_cases h : r' = r
    · subst h; rw [Function.update_self]; exact hGframe.1
    · rw [hGeq r' h]
  have hBindeq : ∀ r', (Function.update g r gr' r').dead = (g r').dead := by
    intro r'; by_cases h : r' = r
    · subst h; rw [Function.update_self]; exact hGframe.2.1
    · rw [hGeq r' h]
  have hGradeeq : ∀ r', (Function.update g r gr' r').grade = (g r').grade := by
    intro r'; by_cases h : r' = r
    · subst h; rw [Function.update_self]; exact hGframe.2.2
    · rw [hGeq r' h]
  have hCframe : c'.F = c.F ∧ c'.decidedSent = c.decidedSent ∧ c'.decidedRecv = c.decidedRecv ∧
      ∀ id', (c'.procs id').input = (c.procs id').input ∧ (c'.procs id').est = (c.procs id').est ∧
        (c'.procs id').round = (c.procs id').round := by
    rcases hstepC with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
      refine ⟨ABAState.setProc_F _ _ _, ABAState.setProc_decidedSent _ _ _,
        ABAState.setProc_decidedRecv _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [ABAState.setProc_procs_self]; exact ⟨rfl, rfl, rfl⟩
      · rw [ABAState.setProc_procs_ne _ _ _ h]; exact ⟨rfl, rfl, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
      exact ⟨rfl, rfl, rfl, fun id' => ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨hCF, hCDS, hCDR, hCprocs⟩ := hCframe
  -- The one fact needing case analysis: `gr'.call`, as an unconditional description
  -- (`Or.inl`: a fresh honest/byz `call` at `id`; `Or.inr`: `callLoop`, unaffected).
  have hGcall : (gr' = { g r with call := Function.update (g r).call id (some b) }) ∨
      gr' = g r := by
    cases hstepG with
    | call h => rw [PMF.mem_support_pure_iff] at hgr'; exact Or.inl hgr'
    | callLoop => rw [PMF.mem_support_pure_iff] at hgr'; exact Or.inr hgr'
  have hCcall : ((c.procs id).phase = .toCallG ∧ (c.procs id).round = r ∧
      (c.procs id).est = some b ∧
      c' = c.setProc id { c.procs id with phase := .awaitG }) ∨ (id ∈ c.F ∧ c' = c) := by
    rcases hstepC with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inl ⟨hph, hr, hest, hc'⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inr ⟨hF, hc'⟩
  -- Every honest fresh call, at any `id'` and any round `r'`, agrees with `est` at that id'.
  have hGcallval : ∀ id' b', gr'.call id' = some b' → id' ≠ id → (g r).call id' = some b' := by
    rcases hGcall with rfl | rfl
    · intro id' b' h hne; simpa [Function.update_of_ne hne] using h
    · intro id' b' h _; exact h
  -- `call` slots are write-once (`Step.call` fires only on an empty slot), so a fresh call
  -- only ever adds to a support count.
  have hCallMono : ∀ id' b', (g r).call id' = some b' → gr'.call id' = some b' := by
    cases hstepG with
    | call _ _ hfresh =>
      rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'
      intro id' b' h'
      show Function.update (g r).call id (some b) id' = some b'
      by_cases hid : id' = id
      · rw [hid] at h'; rw [hfresh] at h'; simp at h'
      · rw [Function.update_of_ne hid]; exact h'
    | callLoop =>
      rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'; exact fun _ _ h => h
  have hGcallSelf : gr'.call id = some b ∨ gr' = g r := by
    rcases hGcall with rfl | rfl
    · left; simp
    · right; rfl
  have hPhaseNe : ∀ id', id' ≠ id → (c'.procs id').phase = (c.procs id').phase := by
    rcases hCcall with ⟨-, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · intro id' hne; rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hne]
    · intro id' _; rw [hc'eq]
  have hLastGradeG : ∀ id', (c'.procs id').lastGrade = (c.procs id').lastGrade := by
    rcases hCcall with ⟨-, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · intro id'; rw [hc'eq]; by_cases h : id' = id
      · subst h; rw [ABAState.setProc_procs_self]
      · rw [ABAState.setProc_procs_ne _ _ _ h]
    · intro id'; rw [hc'eq]
  have hCarrTrans : ∀ r₀ id₀ v, id₀ ∉ c.F →
      Carrier P (Function.update g r gr') c' r₀ id₀ v → Carrier P g c r₀ id₀ v := by
    intro r₀ id₀ v hmem0 hc0
    rcases hc0 with h | ⟨he, hk⟩
    · by_cases h1 : r₀ + 1 = r
      · rw [h1, Function.update_self] at h
        by_cases hid : id₀ = id
        · subst hid
          rcases hGcallSelf with hself | hself
          · rw [hself, Option.some_inj] at h
            rcases hCcall with ⟨hph, hr, hest, -⟩ | ⟨hF, -⟩
            · exact Or.inr ⟨by rw [hest, h], Or.inr ⟨by rw [hr, h1], Or.inr (Or.inl hph)⟩⟩
            · exact absurd hF hmem0
          · rw [hself] at h
            exact Or.inl (by rw [h1]; exact h)
        · have := hGcallval id₀ v h hid
          exact Or.inl (by rw [h1]; exact this)
      · rw [hGeq (r₀ + 1) h1] at h; exact Or.inl h
    · refine Or.inr ⟨(hCprocs id₀).2.1 ▸ he, ?_⟩
      rcases hCcall with ⟨hph, hr, hest, hc'eq⟩ | ⟨-, hc'eq⟩
      · by_cases hid : id₀ = id
        · subst hid
          rw [hc'eq, ABAState.setProc_procs_self] at hk
          rcases hk with ⟨-, hp | hp⟩ | ⟨hr0, -⟩
          · exact absurd hp (by simp)
          · exact absurd hp (by simp)
          · exact Or.inr ⟨hr0, Or.inr (Or.inl hph)⟩
        · rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hk
          exact hk
      · rw [hc'eq] at hk; exact hk
  have hCommitTrans : ∀ r0 b0, ACommit P g c r0 b0 →
      ACommit P (Function.update g r gr') c' r0 b0 := by
    rintro r0 b0 ⟨h1, h2, h3, h4⟩
    refine ⟨fun r'' b'' hrr' hbind =>
        h1 r'' b'' hrr' (by rw [← hBindeq r'']; exact hbind),
      fun r'' id' b'' hrr' hmem hcall => ?_, fun id' hmem hround => ?_,
      fun id0 v hmem hcar => h4 id0 v (hCF ▸ hmem)
        (hCarrTrans r0 id0 v (hCF ▸ hmem) hcar)⟩
    · by_cases hrr : r'' = r
      · rw [hrr, Function.update_self] at hcall
        by_cases hid : id' = id
        · rw [hid] at hcall hmem
          rcases hGcallSelf with hself | hself
          · rw [hself] at hcall; rw [Option.some_inj] at hcall
            rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
            · have hh3 := h3 id (hCF ▸ hmem) (by rw [hr, ← hrr]; exact hrr')
              rw [hest] at hh3; rw [Option.some_inj] at hh3
              rw [← hcall, hh3]
            · exact absurd (hCF ▸ hmem) (not_not.mpr hF)
          · rw [hself] at hcall
            exact h2 r'' id b'' hrr' (hCF ▸ hmem) (by rw [hrr]; exact hcall)
        · have := hGcallval id' b'' hcall hid
          exact h2 r'' id' b'' hrr' (hCF ▸ hmem) (by rw [hrr]; exact this)
      · rw [hGeq r'' hrr] at hcall
        exact h2 r'' id' b'' hrr' (hCF ▸ hmem) hcall
    · rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1]; exact h3 id' (hCF ▸ hmem) hround
  have hCertTrans : ∀ r0 b0, ACert P g c r0 b0 →
      ACert P (Function.update g r gr') c' r0 b0 := by
    rintro r0 b0 ⟨hg1, hd1, hcm⟩
    exact ⟨by rw [hGradeeq]; exact hg1, by rw [hBindeq]; exact hd1, hCommitTrans r0 b0 hcm⟩
  have hHold : ∀ i0 b0, AHolder P c' i0 b0 → AHolder P c i0 b0 := by
    intro i0 b0 h
    unfold AHolder at h ⊢
    rwa [hLastGradeG, hCDS] at h
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
    fun v _ hpin j b' hj hh => hpin j b' (hCF ▸ hj) (hHold j b' hh)⟩
  refine ⟨fun r' => (hFgeq r').trans (hCF ▸ hI.F_g r'), fun r' => hCF ▸ hI.F_w r', hCF ▸ hI.F_card,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, fun r' h => by rw [hGradeeq] at h ⊢; exact hI.c_chain r' h, ?_,
    hI.w_order, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r' v hb => (hI.bind_supp r' v (by rw [← hBindeq r']; exact hb)).mono
      (fun id' b' h => by rw [(hCprocs id').1]; exact h) (fun x hx => by rw [hCF]; exact hx),
    fun r' b' hgf => GBCA.callSupp_mono
      (fun id' h => by
        by_cases hrr : r' = r
        · subst hrr; rw [Function.update_self]; exact hCallMono id' b' h
        · rw [hGeq r' hrr]; exact h)
      (hFgeq r').ge (hI.clock_supp r' b' ((hGradeeq r').symm.trans hgf)),
    fun r' b0 hbd => GBCA.callSupp_mono
      (fun id' h => by
        by_cases hrr : r' = r
        · subst hrr; rw [Function.update_self]; exact hCallMono id' (!b0) h
        · rw [hGeq r' hrr]; exact h)
      (hFgeq r').ge (hI.dead_supp r' b0 (by rw [← hBindeq r']; exact hbd)),
    fun r₀ i0 j0 v v' hm hm' h h' => (hI.carrier_agree r₀ i0 j0 v v' (hCF ▸ hm) (hCF ▸ hm')
      (hCarrTrans r₀ i0 v (hCF ▸ hm) h) (hCarrTrans r₀ j0 v' (hCF ▸ hm') h')).imp
      (fun x => x) (fun hh => (hGradeeq r₀).trans hh),
    fun i0 j0 b0 b0' hm hm' h h' => hI.alock_agree i0 j0 b0 b0' (hCF ▸ hm) (hCF ▸ hm')
      (hHold _ _ h) (hHold _ _ h')⟩
  · -- input_g0
    intro id' b' hmem hcall
    rw [(hCprocs id').1]
    by_cases hr0 : r = 0
    · rw [hr0, Function.update_self] at hcall
      by_cases hid : id' = id
      · rw [hid] at hcall
        rcases hGcallSelf with hself | hself
        · rw [hself] at hcall; rw [Option.some_inj] at hcall
          rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
          · rw [hid]
            have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
            have he0 := hI.est0 id hmem' (hr.trans hr0) (Or.inr (Or.inl hph))
            rw [← he0, hest, hcall]
          · rw [hid] at hmem; exact absurd (hCF ▸ hmem) (not_not.mpr hF)
        · rw [hself, hr0] at hcall
          rw [hid] at hmem ⊢
          exact hI.input_g0 id b' (hCF ▸ hmem) hcall
      · have := hGcallval id' b' hcall hid
        rw [hr0] at this
        exact hI.input_g0 id' b' (hCF ▸ hmem) this
    · rw [hGeq 0 (Ne.symm hr0)] at hcall
      exact hI.input_g0 id' b' (hCF ▸ hmem) hcall
  · -- input_called
    intro r' id' hmem hcall
    rw [(hCprocs id').1]
    by_cases hrr : r' = r
    · rw [hrr, Function.update_self] at hcall
      by_cases hid : id' = id
      · rw [hid] at hcall ⊢
        rcases hGcallSelf with hself | hself
        · rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
          · have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
            exact hI.phase_input id hmem' (by rw [hph]; simp)
          · rw [hid] at hmem; exact absurd (hCF ▸ hmem) (not_not.mpr hF)
        · rw [hself] at hcall; rw [hid] at hmem; exact hI.input_called r id (hCF ▸ hmem) hcall
      · rcases hGcall with hgeq | hgeq
        · rw [hgeq] at hcall; simp only [Function.update_of_ne hid] at hcall
          exact hI.input_called r id' (hCF ▸ hmem) hcall
        · rw [hgeq] at hcall; exact hI.input_called r id' (hCF ▸ hmem) hcall
    · rw [hGeq r' hrr] at hcall
      exact hI.input_called r' id' (hCF ▸ hmem) hcall
  · -- phase_input
    intro id' hmem hne
    rcases hCcall with ⟨hph, hr, hest, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid, (hCprocs id).1]
        have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
        exact hI.phase_input id hmem' (by rw [hph]; simp)
      · rw [(hCprocs id').1]
        rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hne
        exact hI.phase_input id' (hCF ▸ hmem) hne
    · rw [hc'eq] at hne
      rw [(hCprocs id').1]
      exact hI.phase_input id' (hCF ▸ hmem) hne
  · -- down_closed
    intro r' h
    rw [Closed.congr (hBindeq r') (hGradeeq r')]
    exact hI.down_closed r' ((Closed.congr (hBindeq (r' + 1)) (hGradeeq (r' + 1))).mp h)
  · -- quiescent
    obtain ⟨R, hR⟩ := hI.quiescent
    exact ⟨R, fun r' hr' h => hR r' hr' ((Closed.congr (hBindeq r') (hGradeeq r')).mp h)⟩
  · -- w_bound
    intro r' h; rw [Closed.congr (hBindeq r') (hGradeeq r')]; exact hI.w_bound r' h
  · intro i j b' h; rw [hCDR] at h; rw [hCDS]; exact hI.recv_sound i j b' h
  · intro id' b' hmem h
    rw [hCDS] at h
    exact (hI.decided_src id' b' (hCF ▸ hmem) h).imp (fun r0 => hCertTrans r0 b')
  · intro r0 b0 hgr hbr
    rw [hGradeeq] at hgr; rw [hBindeq] at hbr
    exact hCommitTrans r0 b0 (hI.a_commit r0 b0 hgr hbr)
  · intro id' hmem r' hround
    rw [(hCprocs id').2.2] at hround
    rw [Closed.congr (hBindeq r') (hGradeeq r')]
    exact hI.round_bound id' (hCF ▸ hmem) r' hround
  · intro r' v hlast hbr hcoin id' hmem hround
    have hlast' : IsLastBound g r' := ⟨fun h => hlast.1 (by rw [hBindeq]; exact h),
      by rw [← hBindeq (r' + 1)]; exact hlast.2⟩
    rw [hBindeq] at hbr
    rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1]
    exact hI.agree_locked r' v hlast' hbr hcoin id' (hCF ▸ hmem) hround
  · intro r' h; rw [hGradeeq] at h; rw [hBindeq]; exact hI.gradeA_needs_bind r' h
  · intro r' id' hmem hcall
    by_cases hrr : r' = r
    · rw [hrr, Function.update_self] at hcall
      by_cases hid : id' = id
      · rw [hid, (hCprocs id).2.2]
        rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
        · omega
        · rw [hid] at hmem; exact absurd (hCF ▸ hmem) (not_not.mpr hF)
      · rw [(hCprocs id').2.2]
        obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.mp hcall
        have hcv := hGcallval id' b' hb' hid
        rw [hrr]
        exact hI.call_round r id' (hCF ▸ hmem) (by rw [hcv]; simp)
    · rw [hGeq r' hrr] at hcall
      rw [(hCprocs id').2.2]; exact hI.call_round r' id' (hCF ▸ hmem) hcall
  · intro r' id' hmem hcalled
    rw [Closed.congr (hBindeq r') (hGradeeq r')]
    exact hI.w_called r' id' (hCF ▸ hmem) hcalled
  · intro r' id' hmem hround
    rw [(hCprocs id').2.2] at hround
    exact hI.round_flip r' id' (hCF ▸ hmem) hround
  · intro id' hmem hround hphase
    rcases hCcall with ⟨hph, hr, hest, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
        rw [hid, (hCprocs id).2.2] at hround
        rw [hid, (hCprocs id).1, (hCprocs id).2.1]
        exact hI.est0 id hmem' hround (Or.inr (Or.inl hph))
      · rw [(hCprocs id').2.2] at hround
        rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hphase
        rw [(hCprocs id').1, (hCprocs id').2.1]
        exact hI.est0 id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase
      rw [(hCprocs id').2.2] at hround
      rw [(hCprocs id').1, (hCprocs id').2.1]
      exact hI.est0 id' (hCF ▸ hmem) hround hphase
  · intro id' b' hlg
    rw [hLastGradeG] at hlg
    exact (hI.grade_A_src id' b' hlg).imp (fun r0 => hCertTrans r0 b')
  · intro r' id' hmem hround hphase
    rcases hCcall with ⟨hph, hr, hest, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid, hc'eq, ABAState.setProc_procs_self] at hphase
        rcases hphase with h | h <;> simp at h
      · rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hround hphase
        rw [(hCprocs id').2.1]
        obtain ⟨hnone, hsome⟩ := hI.est_ret r' id' (hCF ▸ hmem) hround hphase
        refine ⟨fun he => ?_, fun b hb => ?_⟩
        · obtain ⟨hg0, hno⟩ := hnone he
          refine ⟨by rw [hGradeeq]; exact hg0, fun r₀ hr0 hgr0 => ?_⟩
          rw [hGradeeq] at hgr0
          exact hno r₀ hr0 hgr0
        · rw [hBindeq]; exact hsome b hb
    · rw [hc'eq] at hround hphase
      rw [(hCprocs id').2.1]
      obtain ⟨hnone, hsome⟩ := hI.est_ret r' id' (hCF ▸ hmem) hround hphase
      refine ⟨fun he => ?_, fun b hb => ?_⟩
      · obtain ⟨hg0, hno⟩ := hnone he
        refine ⟨by rw [hGradeeq]; exact hg0, fun r₀ hr0 hgr0 => ?_⟩
        rw [hGradeeq] at hgr0
        exact hno r₀ hr0 hgr0
      · rw [hBindeq]; exact hsome b hb
  · intro r' v h
    rw [hBindeq] at h; rw [hBindeq r', hGradeeq r']
    exact hI.bind_succ r' v h
  · intro r' id' v hmem hcall
    by_cases h1 : r' + 1 = r
    · by_cases hid : id' = id
      · rw [hid] at hcall hmem
        rw [h1, Function.update_self] at hcall
        rcases hGcallSelf with hself | hself
        · rw [hself, Option.some_inj] at hcall
          rcases hCcall with ⟨hph, hr, hest, -⟩ | ⟨hF, -⟩
          · have hround : (c.procs id).round = r' + 1 := by rw [hr, h1]
            have hep := hI.est_prev r' id (hCF ▸ hmem) hround (Or.inr (Or.inl hph)) b hest
            rw [hBindeq r', hGradeeq r']
            rwa [hcall] at hep
          · exact absurd hF (hCF ▸ hmem)
        · rw [hself] at hcall
          rw [hBindeq r', hGradeeq r']
          exact hI.call_prov r' id v (hCF ▸ hmem) (by rw [h1]; exact hcall)
      · rw [h1, Function.update_self] at hcall
        have hcv := hGcallval id' v hcall hid
        rw [hBindeq r', hGradeeq r']
        exact hI.call_prov r' id' v (hCF ▸ hmem) (by rw [h1]; exact hcv)
    · rw [hGeq (r' + 1) h1] at hcall
      rw [hBindeq r', hGradeeq r']
      exact hI.call_prov r' id' v (hCF ▸ hmem) hcall
  · intro r' id' hmem hround hphase v hest
    rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1] at hest
    rw [hBindeq r', hGradeeq r']
    rcases hCcall with ⟨hph, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid] at hmem hround hest
        exact hI.est_prev r' id (hCF ▸ hmem) hround (Or.inr (Or.inl hph)) v hest
      · rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hphase
        exact hI.est_prev r' id' (hCF ▸ hmem) hround hphase v hest
    · rw [hc'eq] at hphase
      exact hI.est_prev r' id' (hCF ▸ hmem) hround hphase v hest
  · intro id' hmem hround hphase
    rw [(hCprocs id').2.2] at hround
    rw [(hCprocs id').2.1]
    rcases hCcall with ⟨hph, hr, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid] at hmem hround ⊢
        exact hI.est_prev_ne id (hCF ▸ hmem) hround (Or.inr (Or.inl hph))
      · rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hphase
        exact hI.est_prev_ne id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase
      exact hI.est_prev_ne id' (hCF ▸ hmem) hround hphase
  · -- `input_g0_perm`: mirrors `input_g0`'s establishment above, with an `id' ∈ F` escape
    -- hatch replacing the honesty hypothesis.
    intro id' b' h
    by_cases hmem : id' ∈ c.F
    · right; rw [hCF]; exact hmem
    · left
      rw [(hCprocs id').1]
      by_cases hr0 : r = 0
      · rw [hr0, Function.update_self] at h
        by_cases hid : id' = id
        · rw [hid] at h
          rcases hGcallSelf with hself | hself
          · rw [hself] at h; rw [Option.some_inj] at h
            rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
            · rw [hid]
              have hmem' : id ∉ c.F := by rw [hid] at hmem; exact hmem
              have he0 := hI.est0 id hmem' (hr.trans hr0) (Or.inr (Or.inl hph))
              rw [← he0, hest, h]
            · rw [hid] at hmem; exact absurd hF hmem
          · rw [hself, hr0] at h
            rw [hid] at hmem ⊢
            rcases hI.input_g0_perm id b' h with hin | hf
            · exact hin
            · exact absurd hf hmem
        · have hcv := hGcallval id' b' h hid
          rw [hr0] at hcv
          rcases hI.input_g0_perm id' b' hcv with hin | hf
          · exact hin
          · exact absurd hf hmem
      · rw [hGeq 0 (Ne.symm hr0)] at h
        rcases hI.input_g0_perm id' b' h with hin | hf
        · exact hin
        · exact absurd hf hmem
  · intro r' id' hmem hcalled
    rw [(hCprocs id').2.2]; exact hI.w_call_round r' id' (hCF ▸ hmem) hcalled
  · intro r' h
    rcases hI.flip_alock r' h with hg | hd
    · left; rw [hGradeeq]; exact hg
    · right
      exact DissentResidue.transport (hBindeq r') (hBindeq (r' - 1))
        (fun h => (hGradeeq (r' - 1)) ▸ h) (fun id' => (hCprocs id').1) hd
  · intro id' hmem hin r'
    rw [(hCprocs id').1] at hin; exact hI.idle_no_wcall id' (hCF ▸ hmem) hin r'
  · intro r' id' hmem hp
    rw [(hCprocs id').2.2] at hp
    have hp' : ((c.procs id').round = r' ∧
        ((c.procs id').phase = .toCallW ∨ (c.procs id').phase = .awaitW)) ∨
        r' < (c.procs id').round := by
      rcases hp with ⟨hround, hphase⟩ | hlt
      · refine Or.inl ⟨hround, ?_⟩
        by_cases hid : id' = id
        · rcases hCcall with ⟨-, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
          · exfalso
            rw [hid, hc'eq, ABAState.setProc_procs_self] at hphase
            rcases hphase with h | h <;> simp at h
          · rw [hid]
            rw [hid, hc'eq] at hphase
            exact hphase
        · rwa [hPhaseNe id' hid] at hphase
      · exact Or.inr hlt
    rw [hGradeeq]
    rcases hI.retg_residue r' id' (hCF ▸ hmem) hp' with hg | hd
    · left; exact hg
    · right; exact DissentResidue.transport (hBindeq r') (hBindeq (r' - 1))
        (fun h => (hGradeeq (r' - 1)) ▸ h) (fun id' => (hCprocs id').1) hd
  · intro r' id' hmem hcalled
    rcases hI.wcalled_residue r' id' (hCF ▸ hmem) hcalled with hg | hd
    · left; rw [hGradeeq]; exact hg
    · right
      exact DissentResidue.transport (hBindeq r') (hBindeq (r' - 1))
        (fun h => (hGradeeq (r' - 1)) ▸ h) (fun id' => (hCprocs id').1) hd
  · intro r' h
    rw [hBindeq] at h
    refine GBCA.SpecState.quorum_mono (hFgeq r').ge (fun id' hne => ?_) (hI.bound_quorum r' h)
    by_cases hrr : r' = r
    · rw [hrr] at hne ⊢
      rw [Function.update_self]
      rcases hGcall with hg | hg
      · rw [hg]
        show Function.update (g r).call id (some b) id' ≠ none
        by_cases hid : id' = id
        · rw [hid, Function.update_self]; simp
        · rw [Function.update_of_ne hid]; exact hne
      · rw [hg]; exact hne
    · rw [hGeq r' hrr]; exact hne

/-- Once a round `r` is not (yet) `C`-locked and its surviving bit `b` is still alive, every
round `r' ≥ r` either has an empty exclusion set or the same live pair, and is never
`C`-locked either: `bind_succ` forces every bit killed at a freshly-bound round `r' + 1` to
be a bit already dead at `r'` — hence `!b`, by the inductive pair — unless `r'` itself just
closed `C`-locked (ruled out by the IH), and `c_chain` propagates the absence of a `C`-lock
downward, so its contrapositive propagates it upward along the induction. -/
theorem Inv.commit_up {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) :
    ∀ r b, (g r).grade ≠ some false → (!b) ∈ (g r).dead → b ∉ (g r).dead →
      ∀ r', r ≤ r' →
        ((g r').dead = ∅ ∨ ((!b) ∈ (g r').dead ∧ b ∉ (g r').dead)) ∧
          (g r').grade ≠ some false := by
  intro r b hg hres hlive r' hrr'
  induction r', hrr' using Nat.le_induction with
  | base => exact ⟨Or.inr ⟨hres, hlive⟩, hg⟩
  | succ r' hrr' ih =>
    refine ⟨?_, fun h => ih.2 (hI.c_chain r' h)⟩
    rcases Finset.eq_empty_or_nonempty ((g (r' + 1)).dead) with hemp | ⟨w', hw'⟩
    · exact Or.inl hemp
    · right
      have hwmem : ∀ x, x ∈ (g (r' + 1)).dead → x = !b := by
        intro x hx
        have hxres : (!(!x)) ∈ (g (r' + 1)).dead := by simpa using hx
        rcases hI.bind_succ r' (!x) hxres with hd | ⟨hgf, -⟩
        · rcases ih.1 with hn | ⟨hpr, hpl⟩
          · rw [hn] at hd; simp at hd
          · have hx' : x ∈ (g r').dead := by simpa using hd
            have hxb : x ≠ b := fun hh => hpl (hh ▸ hx')
            revert hxb; cases x <;> cases b <;> simp
        · exact absurd hgf ih.2
      refine ⟨?_, fun hb0 => ?_⟩
      · have hwb := hwmem w' hw'
        rw [← hwb]; exact hw'
      · have hbb := hwmem b hb0
        exact absurd hbb (by cases b <;> simp)

/-- `C`-locks propagate downward to every earlier round, by iterating `c_chain`. -/
theorem Inv.c_chain_down {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) :
    ∀ r r', r ≤ r' → (g r').grade = some false → (g r).grade = some false := by
  intro r r' hrr'
  induction r', hrr' using Nat.le_induction with
  | base => exact id
  | succ r' hrr' ih => intro h; exact ih (hI.c_chain r' h)

/-- `retG`: the GBCA instance only ever touches `.grade`/`.ret` (never `.F`/`.dead`/`.call`;
`.ret` isn't inspected by `Inv`), the core only ever touches `.est`/`.lastGrade`/`.phase` at
`id` (never `.round`/`.input`). The genuinely hard obligations — `a_commit`'s *new*
round-`r` commitment and `agree_locked`'s est-transfer at `id` — are handed off; they need
GBCA's own Graded-Agreement safety property, not local bookkeeping. -/
theorem Inv.step_retG {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ) (id : Fin P.n) (out : GbcaOut)
    {μr : PMF (GBCA.SpecState P.n)} (hstepG : GBCA.Step P r (g r) (.retG r id out) μr)
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.procs id).phase = .awaitG ∧ (c.procs id).round = r ∧
          μc = PMF.pure (c.setProc id { c.procs id with
            est := out.est, lastGrade := some out, phase := .toCallW })) ∨
        (id ∈ c.F ∧ μc = PMF.pure c))
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Inv P (Function.update g r gr') c' w ∧
      AbsFrame P g (Function.update g r gr') c c' := by
  have hGframe : gr'.F = (g r).F ∧ gr'.dead = (g r).dead ∧ gr'.call = (g r).call := by
    cases hstepG with
    | retB _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact ⟨rfl, rfl, rfl⟩
    | retA _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact ⟨rfl, rfl, rfl⟩
    | retC _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact ⟨rfl, rfl, rfl⟩
  have hGgradeTrue : (g r).grade = some true → gr'.grade = some true := by
    cases hstepG with
    | retB _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact fun h => h
    | retA _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact fun _ => rfl
    | retC _ _ _ _ hg _ =>
      rw [PMF.mem_support_pure_iff] at hgr'
      intro hgt; rw [hgt] at hg; rcases hg with hg | hg <;> simp at hg
  have hGgradeFalse : (g r).grade = some false → gr'.grade = some false := by
    cases hstepG with
    | retB _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact fun h => h
    | retA _ _ _ _ hg _ => intro hgt; rw [hgt] at hg; rcases hg with hg | hg <;> simp at hg
    | retC _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact fun _ => rfl
  have hGeq : ∀ r', r' ≠ r → Function.update g r gr' r' = g r' := fun r' h =>
    Function.update_of_ne h gr' g
  have hFgeq : ∀ r', (Function.update g r gr' r').F = (g r').F := by
    intro r'; by_cases h : r' = r
    · rw [h, Function.update_self]; exact hGframe.1
    · rw [hGeq r' h]
  have hBindeq : ∀ r', (Function.update g r gr' r').dead = (g r').dead := by
    intro r'; by_cases h : r' = r
    · rw [h, Function.update_self]; exact hGframe.2.1
    · rw [hGeq r' h]
  have hCalleq : ∀ r', (Function.update g r gr' r').call = (g r').call := by
    intro r'; by_cases h : r' = r
    · rw [h, Function.update_self]; exact hGframe.2.2
    · rw [hGeq r' h]
  have hGself : Function.update g r gr' r = gr' := by rw [Function.update_self]
  have hClosedEq : ∀ r', r' ≠ r → (Closed (Function.update g r gr') r' ↔ Closed g r') :=
    fun r' h => Closed.congr (hBindeq r') (by rw [hGeq r' h])
  have hClosedTo : ∀ r', Closed g r' → Closed (Function.update g r gr') r' := by
    intro r' h
    refine Closed.of_frame (hBindeq r') (fun hh => ?_) h
    by_cases h2 : r' = r
    · rw [h2, hGself]; exact hGgradeFalse (by rw [← h2]; exact hh)
    · rw [hGeq r' h2]; exact hh
  have hCframe : c'.F = c.F ∧ c'.decidedSent = c.decidedSent ∧ c'.decidedRecv = c.decidedRecv ∧
      ∀ id', (c'.procs id').input = (c.procs id').input ∧
        (c'.procs id').round = (c.procs id').round := by
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
      refine ⟨ABAState.setProc_F _ _ _, ABAState.setProc_decidedSent _ _ _,
        ABAState.setProc_decidedRecv _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · rw [h, ABAState.setProc_procs_self]; exact ⟨rfl, rfl⟩
      · rw [ABAState.setProc_procs_ne _ _ _ h]; exact ⟨rfl, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact ⟨rfl, rfl, rfl, fun id' => ⟨rfl, rfl⟩⟩
  obtain ⟨hCF, hCDS, hCDR, hCprocs⟩ := hCframe
  have hCstepG : ((c.procs id).phase = .awaitG ∧ (c.procs id).round = r ∧
      c' = c.setProc id { c.procs id with
        est := out.est, lastGrade := some out, phase := .toCallW }) ∨
      (id ∈ c.F ∧ c' = c) := by
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inl ⟨hph, hr, hc'⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inr ⟨hF, hc'⟩
  -- The return either hands out round `r`'s surviving bit (`retA`/`retB`, with its live
  -- pair as fire-time guards) or hands out nothing and locks the round to the C-side
  -- (`retC`).
  have hRetInfo : (∃ v, out.est = some v ∧ v ∉ (g r).dead ∧ (!v) ∈ (g r).dead) ∨
      (out.est = none ∧ gr'.grade = some false) := by
    cases hstepG with
    | retB _ v hlive hdead _ _ => exact Or.inl ⟨v, rfl, hlive, hdead⟩
    | retA _ v hlive hdead _ _ => exact Or.inl ⟨v, rfl, hlive, hdead⟩
    | retC _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'
      exact Or.inr ⟨rfl, by rw [hgr']⟩
  -- A round that is `C`-locked after the return carries the `retC` guards at `g r`: either
  -- they were already there (`retB` leaves the grade alone; `retA` locks the A-side) or this
  -- very return supplied them.
  have hCsupp : gr'.grade = some false → ∀ b, P.f + 1 ≤ (Finset.univ.filter
      (fun id' => (g r).call id' = some b ∨ id' ∈ (g r).F)).card := by
    cases hstepG with
    | retB _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'
      intro hgf b; rw [hgr'] at hgf; exact hI.clock_supp r b hgf
    | retA _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'
      intro hgf; rw [hgr'] at hgf; simp at hgf
    | retC _ _ hwT hwF _ _ =>
      intro _ b; cases b
      · exact hwF
      · exact hwT
  have hGradeTrueOfA : ∀ b, out = .A b → gr'.grade = some true := by
    cases hstepG with
    | retB _ _ _ _ _ _ => intro b h; simp at h
    | retA _ _ _ _ _ _ => intro b h; rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']
    | retC _ _ _ _ _ _ => intro b h; simp at h
  have hGradeNoneTrans : (g r).grade ≠ none → gr'.grade ≠ none := by
    intro hgne hcontra
    obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.mp hgne
    cases b' with
    | true => rw [hGgradeTrue hb'] at hcontra; simp at hcontra
    | false => rw [hGgradeFalse hb'] at hcontra; simp at hcontra
  have hTransport : ∀ r', (g r').grade ≠ none ∨ DissentResidue P g c r' →
      (Function.update g r gr' r').grade ≠ none ∨
        DissentResidue P (Function.update g r gr') c' r' := by
    intro r' hres
    rcases hres with hg | hd
    · left
      by_cases h2 : r' = r
      · rw [h2, Function.update_self]; exact hGradeNoneTrans (h2 ▸ hg)
      · rwa [hGeq r' h2]
    · right
      by_cases hrr1 : r' - 1 = r
      · refine DissentResidue.transport (hBindeq r') (hBindeq (r' - 1)) (fun hgf => ?_)
          (fun id' => (hCprocs id').1) hd
        rw [hrr1, Function.update_self]; exact hGgradeFalse (hrr1 ▸ hgf)
      · exact DissentResidue.transport (hBindeq r') (hBindeq (r' - 1))
          (fun hgf => by rwa [hGeq (r' - 1) hrr1]) (fun id' => (hCprocs id').1) hd
  -- A `C`-locking return at round `r` pulls a `C`-lock below every `A`-locked round under
  -- `r` (its own both-bit supports via `c_chain_of_both_supports`, then `c_chain_down`) —
  -- contradiction.
  have hNoCAbove : ∀ r0, r0 < r → (g r0).grade = some true → gr'.grade = some false →
      False := by
    intro r0 hlt hg0 hgf
    have hr1 : r - 1 + 1 = r := by omega
    have hgf' := hI.c_chain_of_both_supports (r - 1)
      (by rw [hr1]; exact hCsupp hgf true) (by rw [hr1]; exact hCsupp hgf false)
    have hgf0 := hI.c_chain_down r0 (r - 1) (by omega) hgf'
    rw [hg0] at hgf0; simp at hgf0
  -- Carrier reduction: a carrier of the post-state is an old carrier or the freshly
  -- returned `id` itself, holding the return's own output.
  have hRedC : ∀ r₀ i1 v1, Carrier P (Function.update g r gr') c' r₀ i1 v1 →
      Carrier P g c r₀ i1 v1 ∨ (i1 = id ∧ r₀ = r ∧ out.est = some v1) := by
    intro r₀ i1 v1 hc1
    rcases hc1 with hcall | ⟨he, hk⟩
    · exact Or.inl (Or.inl (by rw [← hCalleq (r₀ + 1)]; exact hcall))
    · rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid1 : i1 = id
        · subst hid1
          rw [hc'eq, ABAState.setProc_procs_self] at he hk
          right
          refine ⟨rfl, ?_, he⟩
          rcases hk with ⟨hr0, -⟩ | ⟨-, hp⟩
          · rw [← hr0]; exact hr
          · exfalso; rcases hp with hp | hp | hp <;> simp at hp
        · rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid1] at he hk
          exact Or.inl (Or.inr ⟨he, hk⟩)
      · rw [hc'eq] at he hk
        exact Or.inl (Or.inr ⟨he, hk⟩)
  -- Provenance of a standing round-`r` carrier: the permanent residue or the `C`-lock.
  have hProvC : ∀ j1 v1, j1 ∉ c.F → Carrier P g c r j1 v1 →
      (!v1) ∈ (g r).dead ∨ (g r).grade = some false := by
    intro j1 v1 hj hcar
    rcases hcar with hcall | ⟨he, hk⟩
    · rcases hI.call_prov r j1 v1 hj hcall with hd | ⟨hgf, -⟩
      · exact Or.inl hd
      · exact Or.inr hgf
    · rcases hk with ⟨hr0, hph⟩ | ⟨hr0, hph⟩
      · obtain ⟨-, hsome⟩ := hI.est_ret r j1 hj hr0 hph
        exact Or.inl (hsome v1 he)
      · rcases hI.est_prev r j1 hj hr0 hph v1 he with hd | ⟨hgf, -⟩
        · exact Or.inl hd
        · exact Or.inr hgf
  have hCommitTrans : ∀ r0 b0, (g r0).grade = some true → ACommit P g c r0 b0 →
      ACommit P (Function.update g r gr') c' r0 b0 := by
    rintro r0 b0 hg0 ⟨h1, h2, h3, h4⟩
    refine ⟨fun r' b'' hrr' hb' => h1 r' b'' hrr' (by rw [← hBindeq r']; exact hb'),
      fun r' id' b'' hrr' hmem hcall =>
        h2 r' id' b'' hrr' (hCF ▸ hmem) (by rw [← hCalleq r']; exact hcall),
      fun id' hmem hround => ?_, fun id0 v hmem hcar => ?_⟩
    · rw [(hCprocs id').2] at hround
      rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid : id' = id
        · rw [hid, hc'eq, ABAState.setProc_procs_self]
          have hround' : r0 < r := by rw [hid, hr] at hround; exact hround
          rcases hRetInfo with ⟨v, hoev, hlive, hdead⟩ | ⟨-, hgf⟩
          · show out.est = some b0
            rw [hoev, h1 r v (le_of_lt hround') ⟨hdead, hlive⟩]
          · exact absurd hgf (fun hgf => hNoCAbove r0 hround' hg0 hgf)
        · rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid]
          exact h3 id' (hCF ▸ hmem) hround
      · rw [hc'eq]
        exact h3 id' (hCF ▸ hmem) hround
    · rcases hRedC r0 id0 v hcar with hold | ⟨-, hreq, hev⟩
      · exact h4 id0 v (hCF ▸ hmem) hold
      · subst hreq
        rcases hRetInfo with ⟨u, hoev, hulive, hudead⟩ | ⟨-, hgf⟩
        · have hu : u = v := Option.some_inj.mp (hoev.symm.trans hev)
          rw [← hu]
          exact h1 r0 u le_rfl ⟨hudead, hulive⟩
        · have hgt := hGgradeTrue hg0
          rw [hgf] at hgt
          simp at hgt
  have hCertTrans : ∀ r0 b0, ACert P g c r0 b0 →
      ACert P (Function.update g r gr') c' r0 b0 := by
    rintro r0 b0 ⟨hg0, hres0, hcm⟩
    refine ⟨?_, by rw [hBindeq]; exact hres0, hCommitTrans r0 b0 hg0 hcm⟩
    by_cases h2 : r0 = r
    · rw [h2, hGself]; exact hGgradeTrue (h2 ▸ hg0)
    · rw [hGeq r0 h2]; exact hg0
  -- The *fresh* round-`r` commitment: a live pair at the returning round that is not (yet)
  -- `C`-locked commits everything at and above it, through `commit_up`'s pair invariant.
  have hFreshCommit : ∀ b0, (g r).grade ≠ some false →
      (!b0) ∈ (g r).dead → b0 ∉ (g r).dead →
      ACommit P (Function.update g r gr') c' r b0 := by
    intro b0 hgne hres0 hlive0
    have hCU := hI.commit_up r b0 hgne hres0 hlive0
    have hconj3 : ∀ id', id' ∉ c.F → r < (c.procs id').round →
        (c.procs id').est = some b0 := by
      intro id' hmem2 hround2
      by_cases hgroup : (c.procs id').phase = .toCallW ∨ (c.procs id').phase = .awaitW
      · obtain ⟨hnone, hsome⟩ := hI.est_ret (c.procs id').round id' hmem2 rfl hgroup
        rcases Option.eq_none_or_eq_some ((c.procs id').est) with he | ⟨v, he⟩
        · exfalso
          obtain ⟨hgf, -⟩ := hnone he
          exact (hCU (c.procs id').round (by omega)).2 hgf
        · have hveq := hsome v he
          rw [he]
          rcases (hCU (c.procs id').round (by omega)).1 with hn | ⟨hres', hlive'⟩
          · rw [hn] at hveq; simp at hveq
          · have hvb : v = b0 := by
              by_contra hne
              have hv' : (!v) = b0 := by revert hne; cases v <;> cases b0 <;> simp
              exact hlive' (hv' ▸ hveq)
            rw [hvb]
      · have hphase3 : (c.procs id').phase = .idle ∨ (c.procs id').phase = .toCallG ∨
            (c.procs id').phase = .awaitG := by
          rcases hph2 : (c.procs id').phase with _ | _ | _ | _ | _
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact absurd (Or.inl hph2) hgroup
          · exact absurd (Or.inr hph2) hgroup
        have hround1 : (c.procs id').round ≠ 0 := by omega
        have hne := hI.est_prev_ne id' hmem2 hround1 hphase3
        obtain ⟨v, he⟩ := Option.ne_none_iff_exists'.mp hne
        have hr'eq2 : (c.procs id').round = (c.procs id').round - 1 + 1 := by omega
        have hep := hI.est_prev ((c.procs id').round - 1) id' hmem2 hr'eq2 hphase3 v he
        rw [he]
        rcases hep with hbv | ⟨hgf, -⟩
        · rcases (hCU ((c.procs id').round - 1) (by omega)).1 with hn | ⟨hres', hlive'⟩
          · rw [hn] at hbv; simp at hbv
          · have hvb : v = b0 := by
              by_contra hne
              have hv' : (!v) = b0 := by revert hne; cases v <;> cases b0 <;> simp
              exact hlive' (hv' ▸ hbv)
            rw [hvb]
        · exact absurd hgf (hCU ((c.procs id').round - 1) (by omega)).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r' b'' hrr' hb'
      rw [hBindeq r'] at hb'
      rcases (hCU r' hrr').1 with hn | ⟨hres', hlive'⟩
      · rw [hn] at hb'; exact absurd hb'.1 (by simp)
      · by_contra hne
        have hv' : (!b'') = b0 := by revert hne; cases b'' <;> cases b0 <;> simp
        exact hlive' (hv' ▸ hb'.1)
    · intro r' id' b'' hrr' hmem hcall
      have hr'eq : r' = (r' - 1) + 1 := by omega
      rw [hCalleq] at hcall
      rw [hr'eq] at hcall
      have hcp := hI.call_prov (r' - 1) id' b'' (hCF ▸ hmem) hcall
      have hcu2 := hCU (r' - 1) (by omega)
      rcases hcp with hbv | ⟨hgf, -⟩
      · rcases hcu2.1 with hn | ⟨hres', hlive'⟩
        · rw [hn] at hbv; simp at hbv
        · by_contra hne
          have hv' : (!b'') = b0 := by revert hne; cases b'' <;> cases b0 <;> simp
          exact hlive' (hv' ▸ hbv)
      · exact absurd hgf hcu2.2
    · intro id' hmem hround
      rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid : id' = id
        · exfalso
          have hround' : r < (c.procs id).round := by
            simpa [hid, hc'eq, ABAState.setProc_procs_self] using hround
          omega
        · rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hround ⊢
          exact hconj3 id' (hCF ▸ hmem) hround
      · rw [hc'eq] at hround ⊢
        exact hconj3 id' (hCF ▸ hmem) hround
    · intro id0 v hmem hcar
      rcases hRedC r id0 v hcar with hold | ⟨-, -, hev⟩
      · rcases hProvC id0 v (hCF ▸ hmem) hold with hres | hgf
        · by_contra hne
          have hv' : (!v) = b0 := by revert hne; cases v <;> cases b0 <;> simp
          exact hlive0 (hv' ▸ hres)
        · exact absurd hgf hgne
      · rcases hRetInfo with ⟨u, hoev, hulive, -⟩ | ⟨hoe, -⟩
        · have hu : u = v := Option.some_inj.mp (hoev.symm.trans hev)
          rw [← hu]
          by_contra hne
          have hv' : u = !b0 := by revert hne; cases u <;> cases b0 <;> simp
          exact hulive (hv' ▸ hres0)
        · rw [hoe] at hev; simp at hev
  have hRedH : ∀ i1 b1, AHolder P c' i1 b1 → AHolder P c i1 b1 ∨ (i1 = id ∧ out = .A b1) := by
    intro i1 b1 h1
    rcases h1 with h1 | h1
    · rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid1 : i1 = id
        · subst hid1
          rw [hc'eq, ABAState.setProc_procs_self] at h1
          exact Or.inr ⟨rfl, Option.some_inj.mp h1⟩
        · rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid1] at h1
          exact Or.inl (Or.inl h1)
      · rw [hc'eq] at h1
        exact Or.inl (Or.inl h1)
    · rw [hCDS] at h1
      exact Or.inl (Or.inr h1)
  -- A fresh `A`-return's value against any standing certificate: same round via the
  -- fire-time pair, below via the certificate's commitment, above via the fresh
  -- commitment and the harvested caller of the certificate's spared bit.
  have hpinCert : ∀ b1, out = .A b1 → ∀ r1 b1', ACert P g c r1 b1' → b1' = b1 := by
    intro b1 hout r1 b1' hcert
    rcases hRetInfo with ⟨u, hoev, hulive, hudead⟩ | ⟨hoe, -⟩
    · have hu : u = b1 := by
        rw [hout] at hoev
        simpa using hoev.symm
      have hulive' : b1 ∉ (g r).dead := hu ▸ hulive
      have hudead' : (!b1) ∈ (g r).dead := hu ▸ hudead
      obtain ⟨hg1, hres1, hcm1⟩ := hcert
      rcases lt_trichotomy r1 r with hlt | heq | hgt
      · exact (hcm1.1 r b1 (le_of_lt hlt) ⟨hudead', hulive'⟩).symm
      · subst heq
        by_contra hne
        have hv' : (!b1') = b1 := by revert hne; cases b1 <;> cases b1' <;> simp
        exact hulive' (hv' ▸ hres1)
      · have hgne : (g r).grade ≠ some false := fun hf => by
          have h1 := hGgradeFalse hf
          rw [hGradeTrueOfA b1 hout] at h1
          simp at h1
        have hFC := hFreshCommit b1 hgne hudead' hulive'
        obtain ⟨id0, hid0F, hcall0⟩ := GBCA.exists_honest_caller
          (hI.dead_supp r1 (!b1') hres1) (by rw [hI.F_g r1]; exact hI.F_card)
        have hcall0' : (g r1).call id0 = some b1' := by simpa using hcall0
        have hid0c' : id0 ∉ c'.F := by rw [hCF, ← hI.F_g r1]; exact hid0F
        exact hFC.2.1 r1 id0 b1' hgt hid0c' (by rw [hCalleq r1]; exact hcall0')
    · rw [hout] at hoe; simp at hoe
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
    fun v hcv hpin j b' hj hh => ?_⟩
  case refine_2 =>
    rcases hRedH j b' hh with hold | ⟨-, hout⟩
    · exact hpin j b' (hCF ▸ hj) hold
    · obtain ⟨r1, hcv1⟩ := hcv
      exact (hpinCert b' hout r1 v hcv1).symm
  refine ⟨fun r' => (hFgeq r').trans (hCF ▸ hI.F_g r'), fun r' => hCF ▸ hI.F_w r', hCF ▸ hI.F_card,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, hI.w_order, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id' b' hmem hcall
    rw [(hCprocs id').1]; rw [hCalleq] at hcall
    exact hI.input_g0 id' b' (hCF ▸ hmem) hcall
  · intro r' id' hmem hcall
    rw [(hCprocs id').1]; rw [hCalleq] at hcall; exact hI.input_called r' id' (hCF ▸ hmem) hcall
  · intro id' hmem hne
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid, (hCprocs id).1]
        have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
        exact hI.phase_input id hmem' (by rw [hph]; simp)
      · rw [(hCprocs id').1]
        have hne' : (c.procs id').phase ≠ .idle := by
          rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hne; exact hne
        exact hI.phase_input id' (hCF ▸ hmem) hne'
    · rw [hc'eq] at hne; rw [(hCprocs id').1]; exact hI.phase_input id' (hCF ▸ hmem) hne
  · -- `down_closed`: off the returning round nothing moved; at `r' + 1 = r` a `C`-return's
    -- both-bit support pushes the `C`-lock down one round (`c_chain_of_both_supports`).
    intro r' h
    by_cases h2 : r' = r
    · exact hClosedTo r' (hI.down_closed r' ((hClosedEq (r' + 1) (by omega)).mp h))
    · rw [hClosedEq r' h2]
      by_cases h1 : r' + 1 = r
      · rcases h with hb | hgf
        · refine hI.down_closed r' (Or.inl ?_)
          rw [← hBindeq (r' + 1)]; exact hb
        · have hgself : Function.update g r gr' (r' + 1) = gr' := by rw [h1]; exact hGself
          rw [hgself] at hgf
          exact Or.inr (hI.c_chain_of_both_supports r' (by rw [h1]; exact hCsupp hgf true)
            (by rw [h1]; exact hCsupp hgf false))
      · exact hI.down_closed r' ((hClosedEq (r' + 1) h1).mp h)
  · obtain ⟨R, hR⟩ := hI.quiescent
    exact ⟨max R (r + 1), fun r' hr' h =>
      hR r' (by omega) ((hClosedEq r' (by omega)).mp h)⟩
  · intro r' h; exact hClosedTo r' (hI.w_bound r' h)
  · intro i j b' h; rw [hCDR] at h; rw [hCDS]; exact hI.recv_sound i j b' h
  · intro id' b' hmem h
    rw [hCDS] at h
    exact (hI.decided_src id' b' (hCF ▸ hmem) h).imp (fun r0 => hCertTrans r0 b')
  · intro r0 b0 hgr hbr
    by_cases hr0r : r0 = r
    · rw [hr0r, Function.update_self] at hgr hbr
      have hgne : (g r).grade ≠ some false := fun hf => by
        rw [hGgradeFalse hf] at hgr; simp at hgr
      have hb0eq : (!b0) ∈ (g r).dead ∧ b0 ∉ (g r).dead := by
        rw [← hGframe.2.1]; exact hbr
      rw [hr0r]
      exact hFreshCommit b0 hgne hb0eq.1 hb0eq.2
    · rw [hGeq r0 hr0r] at hgr hbr
      obtain ⟨h1, h2, h3, h4⟩ := hI.a_commit r0 b0 hgr hbr
      refine ⟨fun r' b'' hrr' hb' => by rw [hBindeq] at hb'; exact h1 r' b'' hrr' hb',
        fun r' id' b'' hrr' hmem hcall => by
          rw [hCalleq] at hcall; exact h2 r' id' b'' hrr' (hCF ▸ hmem) hcall,
        fun id' hmem hround => ?_,
        fun id0 v hmem hcar => by
          rcases hRedC r0 id0 v hcar with hold | ⟨-, hreq, -⟩
          · exact h4 id0 v (hCF ▸ hmem) hold
          · exact absurd hreq hr0r⟩
      rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid : id' = id
        · rw [hid] at hround hmem
          have hround' : r0 < (c.procs id).round := by
            simpa [hc'eq, ABAState.setProc_procs_self] using hround
          rw [hid, hc'eq, ABAState.setProc_procs_self]
          by_cases hr0lt : r0 < r
          · rcases hRetInfo with ⟨v, hoev, hlive, hdead⟩ | ⟨-, hgf⟩
            · rw [hoev, h1 r v (le_of_lt hr0lt) ⟨hdead, hlive⟩]
            · exact (hNoCAbove r0 hr0lt hgr hgf).elim
          · exfalso; omega
        · rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hround ⊢
          exact h3 id' (hCF ▸ hmem) hround
      · rw [hc'eq] at hround ⊢
        exact h3 id' (hCF ▸ hmem) hround
  · intro id' hmem r' hround
    rw [(hCprocs id').2] at hround
    exact hClosedTo r' (hI.round_bound id' (hCF ▸ hmem) r' hround)
  · intro r' v hlast hbr hcoin id' hmem hround
    have hlast' : IsLastBound g r' := ⟨fun h => hlast.1 (by rw [hBindeq]; exact h),
      by rw [← hBindeq (r' + 1)]; exact hlast.2⟩
    rw [hBindeq] at hbr
    rw [(hCprocs id').2] at hround
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · -- `id` sits at round `r` with `r' < r` and an agreeing coin at `r'`: round `r' + 1`
        -- can neither have bound (`hlast'`) nor be `C`-locked (`no_cgrade_succ`).
        exfalso
        have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
        have hround' : r' < r := by rw [hid, hr] at hround; exact hround
        have hbnd : v ∉ (g r').dead := hbr.2
        by_cases heq : r' + 1 = r
        · rcases hRetInfo with ⟨u, -, -, hudead⟩ | ⟨-, hgf⟩
          · rw [← heq] at hudead
            rw [hlast'.2] at hudead
            simp at hudead
          · exact hI.no_cgrade_succ_of_supp r' v hcoin hbnd (by rw [heq]; exact hCsupp hgf (!v))
        · rcases hI.round_bound id hmem' (r' + 1) (by omega) with hh | hh
          · exact hh hlast'.2
          · exact hI.no_cgrade_succ r' v hcoin hbnd hh
      · rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid]
        exact hI.agree_locked r' v hlast' hbr hcoin id' (hCF ▸ hmem) hround
    · rw [hc'eq]
      exact hI.agree_locked r' v hlast' hbr hcoin id' (hCF ▸ hmem) hround
  · intro r' h
    by_cases h2 : r' = r
    · rw [h2, hBindeq]
      rcases hRetInfo with ⟨v, -, -, hdead⟩ | ⟨-, hgf⟩
      · exact fun hemp => by rw [hemp] at hdead; simp at hdead
      · exfalso; rw [h2, hGself, hgf] at h; simp at h
    · rw [hGeq r' h2] at h; rw [hBindeq]; exact hI.gradeA_needs_bind r' h
  · intro r' id' hmem hcall
    rw [hCalleq] at hcall
    rw [(hCprocs id').2]
    exact hI.call_round r' id' (hCF ▸ hmem) hcall
  · intro r' id' hmem hcalled
    exact hClosedTo r' (hI.w_called r' id' (hCF ▸ hmem) hcalled)
  · intro r' id' hmem hround
    rw [(hCprocs id').2] at hround
    exact hI.round_flip r' id' (hCF ▸ hmem) hround
  · intro id' hmem hround hphase
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid, hc'eq, ABAState.setProc_procs_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · rw [(hCprocs id').2] at hround
        rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hphase
        rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid]
        exact hI.est0 id' (hCF ▸ hmem) hround hphase
    · rw [(hCprocs id').2] at hround
      rw [hc'eq] at hphase
      rw [hc'eq]
      exact hI.est0 id' (hCF ▸ hmem) hround hphase
  · intro id' b' hlg
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · -- the fresh `A`-return certifies itself: its fire-time pair plus `hFreshCommit`
        rw [hid, hc'eq, ABAState.setProc_procs_self] at hlg
        rw [Option.some_inj] at hlg
        refine ⟨r, by rw [Function.update_self]; exact hGradeTrueOfA b' hlg, ?_, ?_⟩
        · rw [hBindeq]
          rcases hRetInfo with ⟨v, hoev, -, hdead⟩ | ⟨hoe, -⟩
          · have hb'eq : out.est = some b' := by simp [hlg]
            rw [hb'eq] at hoev
            rw [Option.some_inj.mp hoev]
            exact hdead
          · exfalso; rw [hlg] at hoe; simp at hoe
        · rcases hRetInfo with ⟨v, hoev, hlive, hdead⟩ | ⟨hoe, -⟩
          · have hb'eq : out.est = some b' := by simp [hlg]
            rw [hb'eq] at hoev
            have hveq := Option.some_inj.mp hoev
            have hgne : (g r).grade ≠ some false := fun hf => by
              have h1 := hGgradeFalse hf
              rw [hGradeTrueOfA b' hlg] at h1
              simp at h1
            exact hFreshCommit b' hgne (hveq ▸ hdead) (hveq ▸ hlive)
          · exfalso; rw [hlg] at hoe; simp at hoe
      · rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hlg
        exact (hI.grade_A_src id' b' hlg).imp (fun r0 => hCertTrans r0 b')
    · rw [hc'eq] at hlg
      exact (hI.grade_A_src id' b' hlg).imp (fun r0 => hCertTrans r0 b')
  · intro r' id' hmem hround hphase
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · have hround' : (c.procs id).round = r' := by
          rw [hid] at hround
          simpa [hc'eq, ABAState.setProc_procs_self] using hround
        have hreq : r' = r := hround'.symm.trans hr
        simp only [hid, hreq, hc'eq, ABAState.setProc_procs_self]
        refine ⟨fun he => ?_, fun b hb => ?_⟩
        · rcases hRetInfo with ⟨v, hoev, -⟩ | ⟨-, hgf⟩
          · exfalso; rw [hoev] at he; simp at he
          · refine ⟨by rw [Function.update_self]; exact hgf, fun r₀ hr0 hgr0 => ?_⟩
            by_cases hr0eq : r₀ = r
            · rw [hr0eq, Function.update_self] at hgr0
              exact absurd (hgr0.symm.trans hgf) (by simp)
            · rw [hGeq r₀ hr0eq] at hgr0
              exact hNoCAbove r₀ (by omega) hgr0 hgf
        · rw [hBindeq]
          rcases hRetInfo with ⟨v, hoev, -, hdead⟩ | ⟨hoe, -⟩
          · rw [hoev] at hb
            rw [← Option.some_inj.mp hb]
            exact hdead
          · exfalso; rw [hoe] at hb; exact absurd hb (by simp)
      · rw [(hCprocs id').2] at hround
        rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hphase
        obtain ⟨hnone, hsome⟩ := hI.est_ret r' id' (hCF ▸ hmem) hround hphase
        rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid]
        refine ⟨fun he => ?_, fun b hb => by rw [hBindeq]; exact hsome b hb⟩
        obtain ⟨hg0, hno⟩ := hnone he
        refine ⟨?_, fun r₀ hr0 hgr0 => ?_⟩
        · by_cases hrr : r' = r
          · rw [hrr, Function.update_self]; exact hGgradeFalse (by rw [← hrr]; exact hg0)
          · rw [hGeq r' hrr]; exact hg0
        · by_cases hr0eq : r₀ = r
          · rw [hr0eq, Function.update_self] at hgr0
            by_cases hrr : r' = r
            · exact absurd hgr0 (by rw [hGgradeFalse (by rw [← hrr]; exact hg0)]; simp)
            · have hgrfalse : (g r).grade = some false := hI.c_chain_down r r' (by omega) hg0
              rw [hGgradeFalse hgrfalse] at hgr0
              simp at hgr0
          · rw [hGeq r₀ hr0eq] at hgr0
            exact hno r₀ hr0 hgr0
    · rw [hc'eq] at hround hphase
      obtain ⟨hnone, hsome⟩ := hI.est_ret r' id' (hCF ▸ hmem) hround hphase
      rw [hc'eq]
      refine ⟨fun he => ?_, fun b hb => by rw [hBindeq]; exact hsome b hb⟩
      obtain ⟨hg0, hno⟩ := hnone he
      refine ⟨?_, fun r₀ hr0 hgr0 => ?_⟩
      · by_cases hrr : r' = r
        · rw [hrr, Function.update_self]; exact hGgradeFalse (by rw [← hrr]; exact hg0)
        · rw [hGeq r' hrr]; exact hg0
      · by_cases hr0eq : r₀ = r
        · rw [hr0eq, Function.update_self] at hgr0
          by_cases hrr : r' = r
          · exact absurd hgr0 (by rw [hGgradeFalse (by rw [← hrr]; exact hg0)]; simp)
          · have hgrfalse : (g r).grade = some false := hI.c_chain_down r r' (by omega) hg0
            rw [hGgradeFalse hgrfalse] at hgr0
            simp at hgr0
        · rw [hGeq r₀ hr0eq] at hgr0
          exact hno r₀ hr0 hgr0
  · intro r' v h
    rw [hBindeq (r' + 1)] at h
    rcases hI.bind_succ r' v h with hbv | ⟨hgf, hw0⟩
    · rw [hBindeq r']; exact Or.inl hbv
    · by_cases h2 : r' = r
      · rw [h2] at hgf hw0 ⊢; rw [Function.update_self]
        exact Or.inr ⟨hGgradeFalse hgf, hw0⟩
      · rw [hGeq r' h2]; exact Or.inr ⟨hgf, hw0⟩
  · intro r' id' v hmem hcall
    rw [hCalleq] at hcall
    rcases hI.call_prov r' id' v (hCF ▸ hmem) hcall with hbv | ⟨hgf, hw0⟩
    · rw [hBindeq r']; exact Or.inl hbv
    · by_cases h2 : r' = r
      · rw [h2] at hgf hw0 ⊢; rw [Function.update_self]
        exact Or.inr ⟨hGgradeFalse hgf, hw0⟩
      · rw [hGeq r' h2]; exact Or.inr ⟨hgf, hw0⟩
  · intro r' id' hmem hround hphase v hest
    rw [(hCprocs id').2] at hround
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid, hc'eq, ABAState.setProc_procs_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hphase hest
        rcases hI.est_prev r' id' (hCF ▸ hmem) hround hphase v hest with hbv | ⟨hgf, hw0⟩
        · rw [hBindeq r']; exact Or.inl hbv
        · by_cases h2 : r' = r
          · rw [h2] at hgf hw0 ⊢; rw [Function.update_self]
            exact Or.inr ⟨hGgradeFalse hgf, hw0⟩
          · rw [hGeq r' h2]; exact Or.inr ⟨hgf, hw0⟩
    · rw [hc'eq] at hphase hest
      rcases hI.est_prev r' id' (hCF ▸ hmem) hround hphase v hest with hbv | ⟨hgf, hw0⟩
      · rw [hBindeq r']; exact Or.inl hbv
      · by_cases h2 : r' = r
        · rw [h2] at hgf hw0 ⊢; rw [Function.update_self]
          exact Or.inr ⟨hGgradeFalse hgf, hw0⟩
        · rw [hGeq r' h2]; exact Or.inr ⟨hgf, hw0⟩
  · intro r' h
    by_cases h2 : r' = r
    · rw [h2] at h ⊢
      rw [hGeq (r + 1) (by omega)] at h
      rw [Function.update_self]
      exact hGgradeFalse (hI.c_chain r h)
    · by_cases h1 : r' + 1 = r
      · rw [h1, Function.update_self] at h
        rw [hGeq r' h2]
        exact hI.c_chain_of_both_supports r' (by rw [h1]; exact hCsupp h true)
          (by rw [h1]; exact hCsupp h false)
      · rw [hGeq (r' + 1) h1] at h
        rw [hGeq r' h2]
        exact hI.c_chain r' h
  · intro id' hmem hround hphase
    rw [(hCprocs id').2] at hround
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid, hc'eq, ABAState.setProc_procs_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hphase ⊢
        exact hI.est_prev_ne id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase ⊢
      exact hI.est_prev_ne id' (hCF ▸ hmem) hround hphase
  · intro id' b' h
    rw [hCalleq] at h
    rcases hI.input_g0_perm id' b' h with hin | hf
    · left; rw [(hCprocs id').1]; exact hin
    · right; rw [hCF]; exact hf
  · intro r' id' hmem hcalled
    rw [(hCprocs id').2]; exact hI.w_call_round r' id' (hCF ▸ hmem) hcalled
  · intro r' h
    rcases hI.flip_alock r' h with hg | hd
    · left
      by_cases hrr : r' = r
      · rw [hrr, Function.update_self]; exact hGradeNoneTrans (hrr ▸ hg)
      · rwa [hGeq r' hrr]
    · right
      by_cases hrr1 : r' - 1 = r
      · refine DissentResidue.transport (hBindeq r') (hBindeq (r' - 1)) (fun hgf => ?_)
          (fun id' => (hCprocs id').1) hd
        rw [hrr1, Function.update_self]; exact hGgradeFalse (hrr1 ▸ hgf)
      · exact DissentResidue.transport (hBindeq r') (hBindeq (r' - 1))
          (fun hgf => by rwa [hGeq (r' - 1) hrr1]) (fun id' => (hCprocs id').1) hd
  · intro id' hmem hin r'
    rw [(hCprocs id').1] at hin
    exact hI.idle_no_wcall id' (hCF ▸ hmem) hin r'
  · -- `retg_residue`'s establishment: the freshly-`retG`'d `id` at round `r` (`awaitG →
    -- toCallW`) gets a fresh grade/dissent fact from the genuine GBCA return guards
    -- (`retA`/`retC` grade the round outright; `retB`'s dissent converts to `DissentResidue`
    -- via `input_g0`/`call_prov`, mirroring `DissentResidue`'s own provenance argument);
    -- everywhere else is `hTransport`-routed pass-through of the pre-state fact.
    intro r' id' hmem hp
    rcases hp with ⟨hround, hphase⟩ | hlt
    · rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid : id' = id
        · have hround' : (c.procs id).round = r' := by
            rw [hid] at hround
            simpa [hc'eq, ABAState.setProc_procs_self] using hround
          have hreq : r' = r := hround'.symm.trans hr
          rw [hreq, Function.update_self]
          cases hstepG with
          | retA _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; left; rw [hgr']; simp
          | retC _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; left; rw [hgr']; simp
          | retB _ v hlive hdead hw _ =>
            rw [PMF.mem_support_pure_iff] at hgr'
            by_cases hgn : (g r).grade = none
            · right
              obtain ⟨id0, hid0F, hcall0⟩ :=
                GBCA.exists_honest_caller hw (by rw [hI.F_g r]; exact hI.F_card)
              have hcF0 : id0 ∉ c.F := by rw [← hI.F_g r]; exact hid0F
              refine ⟨v, by rw [hBindeq r]; exact hdead, ?_⟩
              by_cases hr0 : r = 0
              · rw [if_pos hr0]
                refine ⟨id0, ?_⟩
                rw [(hCprocs id0).1]
                exact hI.input_g0 id0 (!v) hcF0 (by rw [← hr0]; exact hcall0)
              · rw [if_neg hr0]
                have heqr : r - 1 + 1 = r := by omega
                have hcp := hI.call_prov (r - 1) id0 (!v) hcF0 (by rw [heqr]; exact hcall0)
                rcases hcp with hbv | ⟨hgf, -⟩
                · left; rw [hGeq (r - 1) (by omega)]; simpa using hbv
                · right; rw [hGeq (r - 1) (by omega)]; exact hgf
            · left; rw [hgr']; exact hgn
        · rw [(hCprocs id').2] at hround
          rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid] at hphase
          exact hTransport r' (hI.retg_residue r' id' (hCF ▸ hmem) (Or.inl ⟨hround, hphase⟩))
      · rw [(hCprocs id').2] at hround
        rw [hc'eq] at hphase
        exact hTransport r' (hI.retg_residue r' id' (hCF ▸ hmem) (Or.inl ⟨hround, hphase⟩))
    · rw [(hCprocs id').2] at hlt
      exact hTransport r' (hI.retg_residue r' id' (hCF ▸ hmem) (Or.inr hlt))
  · intro r' id' hmem hcalled
    exact hTransport r' (hI.wcalled_residue r' id' (hCF ▸ hmem) hcalled)
  · intro r' h
    rw [hBindeq] at h
    exact GBCA.SpecState.quorum_of_eq (hFgeq r') (hCalleq r') (hI.bound_quorum r' h)
  · -- I26: `retG` never touches `dead`, pools pass through the `c`-frame
    intro r' v hb
    rw [hBindeq r'] at hb
    exact (hI.bind_supp r' v hb).mono
      (fun id' b' h => by rw [(hCprocs id').1]; exact h) (fun x hx => by rw [hCF]; exact hx)
  · -- I27: `retG` never touches `call`/`F`; off the returning round the grade is untouched
    -- too, and on it `hCsupp` reads the guards straight off the return.
    intro r' b' hgf
    refine GBCA.callSupp_mono (s := g r') (fun id' h => by rw [hCalleq r']; exact h)
      (hFgeq r').ge ?_
    by_cases hrr : r' = r
    · rw [hrr, hGself] at hgf
      rw [hrr]
      exact hCsupp hgf b'
    · rw [hGeq r' hrr] at hgf
      exact hI.clock_supp r' b' hgf
  · -- I28: `retG` never touches `dead`/`call`/`F`
    intro r' b0 hbd
    rw [hBindeq r'] at hbd
    exact GBCA.callSupp_mono (fun id' h => by rw [hCalleq r']; exact h) (hFgeq r').ge
      (hI.dead_supp r' b0 hbd)
  · -- I29 establishment: a fresh value-bearing return's carrier meets every standing
    -- opposite carrier's permanent residue head-on — the return's own liveness guard
    -- refutes it; a `C`-return locks the round's grade instead.
    intro r₀ i0 j0 v v' hm hm' h h'
    have hred : ∀ i1 v1, Carrier P (Function.update g r gr') c' r₀ i1 v1 →
        Carrier P g c r₀ i1 v1 ∨ (i1 = id ∧ r₀ = r ∧ out.est = some v1) := by
      intro i1 v1 hc1
      rcases hc1 with hcall | ⟨he, hk⟩
      · exact Or.inl (Or.inl (by rw [← hCalleq (r₀ + 1)]; exact hcall))
      · rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · by_cases hid1 : i1 = id
          · subst hid1
            rw [hc'eq, ABAState.setProc_procs_self] at he hk
            right
            refine ⟨rfl, ?_, he⟩
            rcases hk with ⟨hr0, -⟩ | ⟨-, hp⟩
            · rw [← hr0]; exact hr
            · exfalso; rcases hp with hp | hp | hp <;> simp at hp
          · rw [hc'eq, ABAState.setProc_procs_ne _ _ _ hid1] at he hk
            exact Or.inl (Or.inr ⟨he, hk⟩)
        · rw [hc'eq] at he hk
          exact Or.inl (Or.inr ⟨he, hk⟩)
    have hprov : ∀ j1 v1, j1 ∉ c.F → Carrier P g c r j1 v1 →
        (!v1) ∈ (g r).dead ∨ (g r).grade = some false := by
      intro j1 v1 hj hcar
      rcases hcar with hcall | ⟨he, hk⟩
      · rcases hI.call_prov r j1 v1 hj hcall with hd | ⟨hgf, -⟩
        · exact Or.inl hd
        · exact Or.inr hgf
      · rcases hk with ⟨hr0, hph⟩ | ⟨hr0, hph⟩
        · obtain ⟨-, hsome⟩ := hI.est_ret r j1 hj hr0 hph
          exact Or.inl (hsome v1 he)
        · rcases hI.est_prev r j1 hj hr0 hph v1 he with hd | ⟨hgf, -⟩
          · exact Or.inl hd
          · exact Or.inr hgf
    have hnewpin : ∀ vnew j1 v1, j1 ∉ c.F → out.est = some vnew → Carrier P g c r j1 v1 →
        v1 = vnew ∨ (g r).grade = some false := by
      intro vnew j1 v1 hj hoev hcar
      rcases hprov j1 v1 hj hcar with hres | hgf
      · rcases hRetInfo with ⟨u, hoev', hulive, -⟩ | ⟨hoe, -⟩
        · have hu : u = vnew := Option.some_inj.mp (hoev'.symm.trans hoev)
          rw [hu] at hulive
          left
          by_contra hne
          have hv' : (!v1) = vnew := by revert hne; cases vnew <;> cases v1 <;> simp
          exact hulive (hv' ▸ hres)
        · rw [hoe] at hoev; simp at hoev
      · exact Or.inr hgf
    have hGradeTo : ∀ r₁, (g r₁).grade = some false →
        (Function.update g r gr' r₁).grade = some false := by
      intro r₁ hgf
      by_cases h2 : r₁ = r
      · rw [h2, hGself]; exact hGgradeFalse (h2 ▸ hgf)
      · rwa [hGeq r₁ h2]
    rcases hred i0 v h with hold0 | ⟨-, hreq0, hev0⟩
    · rcases hred j0 v' h' with hold1 | ⟨-, hreq1, hev1⟩
      · exact (hI.carrier_agree r₀ i0 j0 v v' (hCF ▸ hm) (hCF ▸ hm') hold0 hold1).imp
          (fun x => x) (hGradeTo r₀)
      · rcases hnewpin v' i0 v (hCF ▸ hm) hev1 (hreq1 ▸ hold0) with hvv | hgf
        · exact Or.inl hvv
        · exact Or.inr (by rw [hreq1]; exact hGradeTo r hgf)
    · rcases hred j0 v' h' with hold1 | ⟨-, -, hev1⟩
      · rcases hnewpin v j0 v' (hCF ▸ hm') hev0 (hreq0 ▸ hold1) with hvv | hgf
        · exact Or.inl hvv.symm
        · exact Or.inr (by rw [hreq0]; exact hGradeTo r hgf)
      · exact Or.inl (Option.some_inj.mp (hev0.symm.trans hev1))
  · -- I30 establishment: a fresh `A`-return is compared against every standing honest
    -- holder's certificate through `hpinCert`.
    intro i0 j0 b0 b0' hm hm' h h'
    have hpin : ∀ b1, out = .A b1 → ∀ j1 b1', j1 ∉ c.F → AHolder P c j1 b1' → b1' = b1 := by
      intro b1 hout j1 b1' hj hold
      have hcert : ∃ r1, ACert P g c r1 b1' := by
        rcases hold with h1 | h1
        · exact hI.grade_A_src j1 b1' h1
        · exact hI.decided_src j1 b1' hj h1
      obtain ⟨r1, hcv1⟩ := hcert
      exact hpinCert b1 hout r1 b1' hcv1
    rcases hRedH i0 b0 h with hold0 | ⟨-, hout0⟩
    · rcases hRedH j0 b0' h' with hold1 | ⟨-, hout1⟩
      · exact hI.alock_agree i0 j0 b0 b0' (hCF ▸ hm) (hCF ▸ hm') hold0 hold1
      · exact hpin b0' hout1 i0 b0 (hCF ▸ hm) hold0
    · rcases hRedH j0 b0' h' with hold1 | ⟨-, hout1⟩
      · exact (hpin b0 hout0 j0 b0' (hCF ▸ hm') hold1).symm
      · rw [hout0] at hout1
        simpa using hout1

/-- `retW`: `g` is untouched entirely; the WCC instance only touches `.ret` (not inspected by
`Inv`); the core's `stepRound` touches `est`/`lastGrade`/`round`/`phase` at `id` and
conditionally `decidedSent id` (on an `A`-grade). `round_bound`'s freshly-included round is
covered by `w_bound` (the coin having resolved closes the round); the DECIDED-on-`A`-grade
witness for `decided_src`, and the `a_commit`/`agree_locked` extension to `id`'s new round,
need the cross-round `lastGrade`-to-`(g r).grade/.dead` correlation (GBCA Graded Agreement)
that isn't a local `Inv` consequence — handed off. -/
theorem Inv.step_retW {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ) (id : Fin P.n) (b : Bool)
    {μw' : PMF (WCC.SpecState P.n)} (hstepW : WCC.Step P r (w r) (.retW r id b) μw')
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.procs id).phase = .awaitW ∧ (c.procs id).round = r ∧
          μc = PMF.pure (c.stepRound id b)) ∨
        (id ∈ c.F ∧ μc = PMF.pure c))
    {wr' : WCC.SpecState P.n} (hwr' : wr' ∈ μw'.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Inv P g c' (Function.update w r wr') ∧ AbsFrame P g g c c' := by
  have hWeq : (Function.update w r wr' r).F = (w r).F ∧
      (Function.update w r wr' r).val = (w r).val := by
    rw [Function.update_self]; cases hstepW with
    | ret _ _ _ _ => rw [PMF.mem_support_pure_iff] at hwr'; rw [hwr']; exact ⟨rfl, rfl⟩
  have hWNe : ∀ r', r' ≠ r → Function.update w r wr' r' = w r' := fun r' h =>
    Function.update_of_ne h wr' w
  have hFweq : ∀ r', (Function.update w r wr' r').F = (w r').F := by
    intro r'; by_cases h : r' = r
    · rw [h]; exact hWeq.1
    · rw [hWNe r' h]
  have hValeq : ∀ r', (Function.update w r wr' r').val = (w r').val := by
    intro r'; by_cases h : r' = r
    · rw [h]; exact hWeq.2
    · rw [hWNe r' h]
  have hWval : (w r).val ≠ .bot := by
    cases hstepW with
    | ret _ _ h1 _ => rcases h1 with h1 | h1 <;> rw [h1] <;> simp
  have hCoinEq : ∀ v', (w r).val = .bit v' → b = v' := by
    cases hstepW with
    | ret _ _ h1 _ =>
      intro v' hv'
      rcases h1 with h1 | h1
      · rw [h1] at hv'; simp at hv'
      · rw [h1] at hv'; simpa using hv'
  have hCalledEq : ∀ r', (Function.update w r wr' r').called = (w r').called := by
    intro r'; by_cases h : r' = r
    · rw [h, Function.update_self]
      cases hstepW with
      | ret _ _ _ _ => rw [PMF.mem_support_pure_iff] at hwr'; rw [hwr']
    · rw [hWNe r' h]
  rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
  · rw [PMF.mem_support_pure_iff] at hc'
    have hFeq : (c.stepRound id b).F = c.F := ABAState.stepRound_F _ _ _
    have hDReq : (c.stepRound id b).decidedRecv = c.decidedRecv :=
      ABAState.stepRound_decidedRecv _ _ _
    have hProcNe : ∀ id', id' ≠ id → (c.stepRound id b).procs id' = c.procs id' := by
      intro id' h; exact ABAState.stepRound_procs_ne _ _ _ h
    have hProcSelf : (c.stepRound id b).procs id = { c.procs id with
        est := some ((c.procs id).est.getD b), lastGrade := none,
        round := (c.procs id).round + 1, phase := .toCallG } := ABAState.stepRound_procs_self _ _ _
    have hInputEq : ((c.stepRound id b).procs id).input = (c.procs id).input := by
      rw [hProcSelf]
    have hRoundEq : ((c.stepRound id b).procs id).round = (c.procs id).round + 1 := by
      rw [hProcSelf]
    have hDSeq : (c.stepRound id b).decidedSent = c.decidedSent ∨
        ∃ b0, (c.procs id).lastGrade = some (.A b0) ∧
          (c.stepRound id b).decidedSent =
            Function.update c.decidedSent id (insert b0 (c.decidedSent id)) := by
      by_cases hA : ∃ b0, (c.procs id).lastGrade = some (.A b0)
      · obtain ⟨b0, hlg⟩ := hA
        exact Or.inr ⟨b0, hlg, ABAState.stepRound_decidedSent_of_A c id b b0 hlg⟩
      · exact Or.inl (ABAState.stepRound_decidedSent_of_not_A c id b (fun b1 heq => hA ⟨b1, heq⟩))
    have hDR2 : ∀ r', DissentResidue P g c r' → DissentResidue P g (c.stepRound id b) r' := by
      intro r' hd
      refine DissentResidue.transport rfl rfl (fun hh => hh) (fun id2 => ?_) hd
      by_cases hid2 : id2 = id
      · rw [hid2]; exact hInputEq
      · rw [hProcNe id2 hid2]
    -- Carrier reduction: a post-`stepRound` carrier is an old one or `id`, now holding the
    -- adopted estimate at the finished round `r`.
    have hRedW : ∀ r₀ i1 v1, Carrier P g (c.stepRound id b) r₀ i1 v1 →
        Carrier P g c r₀ i1 v1 ∨ (i1 = id ∧ r₀ = r ∧ (c.procs id).est.getD b = v1) := by
      intro r₀ i1 v1 hc1
      rcases hc1 with hcall | ⟨he, hk⟩
      · exact Or.inl (Or.inl hcall)
      · by_cases hid1 : i1 = id
        · rw [hid1, hProcSelf] at he hk
          rcases hk with ⟨-, hp | hp⟩ | ⟨hr0, -⟩
          · exact absurd hp (by simp)
          · exact absurd hp (by simp)
          · have hr0' : (c.procs id).round + 1 = r₀ + 1 := by simpa using hr0
            exact Or.inr ⟨hid1, by omega, Option.some_inj.mp he⟩
        · rw [hProcNe i1 hid1] at he hk
          exact Or.inl (Or.inr ⟨he, hk⟩)
    have hIdCarr : ∀ bv, (c.procs id).est = some bv → Carrier P g c r id bv :=
      fun bv hoe => Or.inr ⟨hoe, Or.inl ⟨hr, Or.inr hph⟩⟩
    have hCommitW : ∀ r0 b0, (g r0).grade = some true → ACommit P g c r0 b0 →
        ACommit P g (c.stepRound id b) r0 b0 := by
      rintro r0 b0 hg0 ⟨h1, h2, h3, h4⟩
      refine ⟨h1, fun r' id' b'' hrr' hmem hcall => h2 r' id' b'' hrr' (hFeq ▸ hmem) hcall,
        fun id' hmem hround => ?_, fun id0 v hmem hcar => ?_⟩
      · by_cases hid : id' = id
        · rw [hid, hRoundEq] at hround
          by_cases hle : r0 < (c.procs id).round
          · have hold := h3 id (hFeq ▸ (hid ▸ hmem)) hle
            rw [hid]; simp [hold]
          · have hr0r : r0 = r := (by omega : r0 = (c.procs id).round).trans hr
            rw [hid]; simp only [hProcSelf]
            rcases Option.eq_none_or_eq_some ((c.procs id).est) with hoe | ⟨bv, hoe⟩
            · exfalso
              obtain ⟨hg0', -⟩ :=
                (hI.est_ret r id (hFeq ▸ (hid ▸ hmem)) hr (Or.inr hph)).1 hoe
              rw [hr0r] at hg0
              exact absurd (hg0.symm.trans hg0') (by simp)
            · have hbv0 : bv = b0 :=
                h4 id bv (hFeq ▸ (hid ▸ hmem)) (hr0r ▸ hIdCarr bv hoe)
              simp [hoe, hbv0]
        · rw [hProcNe id' hid] at hround; rw [hProcNe id' hid]
          exact h3 id' (hFeq ▸ hmem) hround
      · rcases hRedW r0 id0 v hcar with hold | ⟨heq0, hreq, hev⟩
        · exact h4 id0 v (hFeq ▸ hmem) hold
        · rcases Option.eq_none_or_eq_some ((c.procs id).est) with hoe | ⟨bv, hoe⟩
          · obtain ⟨hg0', -⟩ :=
              (hI.est_ret r id (hFeq ▸ (heq0 ▸ hmem)) hr (Or.inr hph)).1 hoe
            rw [hreq] at hg0
            exact absurd (hg0.symm.trans hg0') (by simp)
          · have hv : v = bv := by rw [hoe] at hev; simpa using hev.symm
            rw [hv]
            exact h4 id bv (hFeq ▸ (heq0 ▸ hmem)) (hreq ▸ hIdCarr bv hoe)
    have hCertW : ∀ r0 b0, ACert P g c r0 b0 → ACert P g (c.stepRound id b) r0 b0 := by
      rintro r0 b0 ⟨hg0, hres0, hcm⟩
      exact ⟨hg0, hres0, hCommitW r0 b0 hg0 hcm⟩
    have hRedHW : ∀ i1 b1, AHolder P (c.stepRound id b) i1 b1 → AHolder P c i1 b1 := by
      intro i1 b1 h1
      rcases h1 with h1 | h1
      · by_cases hid1 : i1 = id
        · rw [hid1, hProcSelf] at h1; simp at h1
        · rw [hProcNe i1 hid1] at h1; exact Or.inl h1
      · rcases hDSeq with heq | ⟨b2, hlg, heq⟩
        · rw [heq] at h1; exact Or.inr h1
        · rw [heq] at h1
          by_cases hid1 : i1 = id
          · subst hid1
            rw [Function.update_self, Finset.mem_insert] at h1
            rcases h1 with rfl | h1
            · exact Or.inl hlg
            · exact Or.inr h1
          · rw [Function.update_of_ne hid1] at h1
            exact Or.inr h1
    rw [hc']
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertW r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hFeq ▸ hj) (hRedHW j b' hh)⟩
    refine ⟨fun r' => hFeq ▸ hI.F_g r', fun r' => (hFweq r').trans (hFeq ▸ hI.F_w r'),
      hFeq ▸ hI.F_card, ?_, ?_, ?_, hI.down_closed, hI.quiescent,
      fun r' h => hI.w_bound r' (by rw [← hValeq r']; exact h),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.c_chain, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r' v hb2 => (hI.bind_supp r' v hb2).mono
        (fun id2 b2 h => by
          by_cases hid2 : id2 = id
          · rw [hid2, hInputEq]; exact hid2 ▸ h
          · rw [hProcNe id2 hid2]; exact h)
        (fun x hx => by rw [hFeq]; exact hx),
      hI.clock_supp, hI.dead_supp,
      fun r₀ i0 j0 v v' hm hm' h h' => by
        rcases hRedW r₀ i0 v h with hold0 | ⟨heq0, hreq0, hev0⟩
        · rcases hRedW r₀ j0 v' h' with hold1 | ⟨heq1, hreq1, hev1⟩
          · exact hI.carrier_agree r₀ i0 j0 v v' (hFeq ▸ hm) (hFeq ▸ hm') hold0 hold1
          · rcases Option.eq_none_or_eq_some ((c.procs id).est) with hoe | ⟨bv, hoe⟩
            · obtain ⟨hg0, -⟩ :=
                (hI.est_ret r id (hFeq ▸ (heq1 ▸ hm')) hr (Or.inr hph)).1 hoe
              exact Or.inr (by rw [hreq1]; exact hg0)
            · have hv' : v' = bv := by rw [hoe] at hev1; simpa using hev1.symm
              rw [hv']
              exact hI.carrier_agree r₀ i0 id v bv (hFeq ▸ hm) (hFeq ▸ (heq1 ▸ hm')) hold0
                (hreq1 ▸ hIdCarr bv hoe)
        · rcases hRedW r₀ j0 v' h' with hold1 | ⟨heq1, hreq1, hev1⟩
          · rcases Option.eq_none_or_eq_some ((c.procs id).est) with hoe | ⟨bv, hoe⟩
            · obtain ⟨hg0, -⟩ :=
                (hI.est_ret r id (hFeq ▸ (heq0 ▸ hm)) hr (Or.inr hph)).1 hoe
              exact Or.inr (by rw [hreq0]; exact hg0)
            · have hv0 : v = bv := by rw [hoe] at hev0; simpa using hev0.symm
              rw [hv0]
              exact hI.carrier_agree r₀ id j0 bv v' (hFeq ▸ (heq0 ▸ hm)) (hFeq ▸ hm')
                (hreq0 ▸ hIdCarr bv hoe) hold1
          · exact Or.inl (hev0.symm.trans hev1),
      fun i0 j0 b0 b0' hm hm' h h' => hI.alock_agree i0 j0 b0 b0' (hFeq ▸ hm) (hFeq ▸ hm')
        (hRedHW i0 b0 h) (hRedHW j0 b0' h')⟩
    · intro id' b' hmem hcall
      by_cases h : id' = id
      · rw [h] at hmem hcall; rw [h, hInputEq]
        exact hI.input_g0 id b' (hFeq ▸ hmem) hcall
      · rw [hProcNe id' h]; exact hI.input_g0 id' b' (hFeq ▸ hmem) hcall
    · intro r' id' hmem hcall
      by_cases h : id' = id
      · rw [h] at hmem hcall; rw [h, hInputEq]
        exact hI.input_called r' id (hFeq ▸ hmem) hcall
      · rw [hProcNe id' h]; exact hI.input_called r' id' (hFeq ▸ hmem) hcall
    · intro id' hmem hne
      by_cases h : id' = id
      · rw [h, hInputEq]; rw [h] at hmem
        exact hI.phase_input id (hFeq ▸ hmem) (by rw [hph]; simp)
      · rw [hProcNe id' h] at hne ⊢
        exact hI.phase_input id' (hFeq ▸ hmem) hne
    · intro i j b' h
      rw [hDReq] at h
      rcases hDSeq with heq | ⟨b0, hlg, heq⟩
      · rw [heq]; exact hI.recv_sound i j b' h
      · rw [heq]
        by_cases hji : j = id
        -- the sent pool only grows (D12′): the old receipt stays covered
        · rw [hji] at h ⊢
          rw [Function.update_self]
          exact Finset.mem_insert_of_mem (hI.recv_sound i id b' h)
        · rw [Function.update_of_ne hji]; exact hI.recv_sound i j b' h
    · intro id' b' hmem h
      rcases hDSeq with heq | ⟨b0, hlg, heq⟩
      · rw [heq] at h
        exact (hI.decided_src id' b' (hFeq ▸ hmem) h).imp (fun r0 => hCertW r0 b')
      · rw [heq] at h
        by_cases hid : id' = id
        · rw [hid, Function.update_self, Finset.mem_insert] at h
          rcases h with rfl | h
          · exact (hI.grade_A_src id b' hlg).imp (fun r0 => hCertW r0 b')
          · exact (hI.decided_src id b' (hFeq ▸ hid ▸ hmem) h).imp (fun r0 => hCertW r0 b')
        · rw [Function.update_of_ne hid] at h
          exact (hI.decided_src id' b' (hFeq ▸ hmem) h).imp (fun r0 => hCertW r0 b')
    · intro r0 b0 hgr hbr
      exact hCommitW r0 b0 hgr (hI.a_commit r0 b0 hgr hbr)
    · intro id' hmem r' hround
      by_cases h : id' = id
      · rw [h] at hmem; rw [h, hRoundEq] at hround
        by_cases hr' : r' = (c.procs id).round
        · rw [hr', hr]; exact hI.w_bound r hWval
        · exact hI.round_bound id (hFeq ▸ hmem) r' (by omega)
      · rw [hProcNe id' h] at hround; exact hI.round_bound id' (hFeq ▸ hmem) r' hround
    · intro r' v hlast hbr hcoin id' hmem hround
      rw [hValeq] at hcoin
      by_cases hid : id' = id
      · rw [hid, hRoundEq] at hround
        by_cases hle : r' < (c.procs id).round
        · have hold := hI.agree_locked r' v hlast hbr hcoin id (hFeq ▸ (hid ▸ hmem)) hle
          rw [hid]; simp [hold]
        · have hr'eq : r' = (c.procs id).round := by omega
          have hr'r : r' = r := hr'eq.trans hr
          rw [hid]; simp only [hProcSelf]
          obtain ⟨hnone, hsome⟩ := hI.est_ret r id (hFeq ▸ (hid ▸ hmem)) hr (Or.inr hph)
          by_cases holdE : (c.procs id).est = none
          · obtain ⟨hg0, -⟩ := hnone holdE
            have hbeqv : b = v := hCoinEq v (by rw [← hr'r]; exact hcoin)
            simp [holdE, hbeqv]
          · obtain ⟨bv, hbv⟩ := Option.ne_none_iff_exists'.mp holdE
            have hbveq := hsome bv hbv
            rw [hr'r] at hbr
            have hbv0 : bv = v := by
              by_contra hne
              have hv' : (!bv) = v := by revert hne; cases bv <;> cases v <;> simp
              exact hbr.2 (hv' ▸ hbveq)
            simp [hbv, hbv0]
      · rw [hProcNe id' hid] at hround; rw [hProcNe id' hid]
        exact hI.agree_locked r' v hlast hbr hcoin id' (hFeq ▸ hmem) hround
    · exact hI.gradeA_needs_bind
    · intro r' id' hmem hcall
      by_cases h : id' = id
      · rw [h, hRoundEq]; rw [h] at hmem hcall
        exact le_trans (hI.call_round r' id (hFeq ▸ hmem) hcall) (by omega)
      · rw [hProcNe id' h]
        exact hI.call_round r' id' (hFeq ▸ hmem) hcall
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.w_called r' id' (hFeq ▸ hmem) hcalled
    · intro r' id' hmem hround
      by_cases h : id' = id
      · rw [h, hRoundEq] at hround
        rw [hValeq]
        by_cases hlt : r' < (c.procs id).round
        · exact hI.round_flip r' id (hFeq ▸ (h ▸ hmem)) hlt
        · have hreq : r' = (c.procs id).round := by omega
          rw [hreq, hr]; exact hWval
      · rw [hProcNe id' h] at hround
        rw [hValeq]; exact hI.round_flip r' id' (hFeq ▸ hmem) hround
    · intro id' hmem hround hphase
      by_cases h : id' = id
      · exfalso
        rw [h, hRoundEq] at hround
        omega
      · rw [hProcNe id' h] at hround hphase ⊢
        exact hI.est0 id' (hFeq ▸ hmem) hround hphase
    · intro id' b' hlg
      by_cases h : id' = id
      · exfalso; rw [h, hProcSelf] at hlg; simp at hlg
      · rw [hProcNe id' h] at hlg
        exact (hI.grade_A_src id' b' hlg).imp (fun r0 => hCertW r0 b')
    · intro r' id' hmem hround hphase
      by_cases h : id' = id
      · exfalso
        rw [h, hProcSelf] at hphase
        rcases hphase with hp | hp <;> simp at hp
      · rw [hProcNe id' h] at hround hphase
        rw [hProcNe id' h]
        exact hI.est_ret r' id' (hFeq ▸ hmem) hround hphase
    · intro r' v h; rw [hValeq r']; exact hI.bind_succ r' v h
    · intro r' id' v hmem hcall
      rw [hValeq r']; exact hI.call_prov r' id' v (hFeq ▸ hmem) hcall
    · intro r' id' hmem hround hphase v hest
      by_cases hid : id' = id
      · rw [hid, hRoundEq] at hround
        have hreq : r' = r := by omega
        rw [hreq, hValeq r]
        have hveq : (c.procs id).est.getD b = v := by
          have hcopy := hest
          rw [hid, hProcSelf] at hcopy
          exact Option.some_inj.mp hcopy
        have hep := hI.est_ret r id (hFeq ▸ (hid ▸ hmem)) hr (Or.inr hph)
        rcases Option.eq_none_or_eq_some ((c.procs id).est) with hoe | ⟨bv, hoe⟩
        · rw [hoe] at hveq; simp at hveq
          obtain ⟨hg0, -⟩ := hep.1 hoe
          have hWtb : (w r).val = .top ∨ (w r).val = .bit b := by
            cases hstepW with | ret _ _ h1 _ => exact h1
          rw [← hveq]; exact Or.inr ⟨hg0, hWtb.symm⟩
        · rw [hoe] at hveq; simp at hveq
          have hbveq := hep.2 bv hoe
          rw [← hveq]; exact Or.inl hbveq
      · rw [hProcNe id' hid] at hround hphase hest
        rw [hValeq r']
        exact hI.est_prev r' id' (hFeq ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      by_cases hid : id' = id
      · rw [hid, hProcSelf]; simp
      · rw [hProcNe id' hid] at hround hphase ⊢
        exact hI.est_prev_ne id' (hFeq ▸ hmem) hround hphase
    · intro r' h; rw [hValeq] at h ⊢; exact hI.w_order r' h
    · intro id' b' h
      by_cases hid : id' = id
      · rw [hid] at h ⊢
        rcases hI.input_g0_perm id b' h with hin | hf
        · left; rw [hInputEq]; exact hin
        · right; rw [hFeq]; exact hf
      · rw [hProcNe id' hid]
        rcases hI.input_g0_perm id' b' h with hin | hf
        · left; exact hin
        · right; rw [hFeq]; exact hf
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled
      by_cases h : id' = id
      · rw [h, hRoundEq]; rw [h] at hmem hcalled
        exact le_trans (hI.w_call_round r' id (hFeq ▸ hmem) hcalled) (by omega)
      · rw [hProcNe id' h]
        exact hI.w_call_round r' id' (hFeq ▸ hmem) hcalled
    · intro r' h
      rw [hValeq] at h
      rcases hI.flip_alock r' h with hg | hd
      · left; exact hg
      · right
        refine DissentResidue.transport rfl rfl (fun hh => hh) (fun id2 => ?_) hd
        by_cases hid2 : id2 = id
        · rw [hid2]; exact hInputEq
        · rw [hProcNe id2 hid2]
    · intro id' hmem hin r'
      rw [hCalledEq]
      by_cases h : id' = id
      · rw [h] at hmem hin
        rw [h]; rw [hInputEq] at hin
        exact hI.idle_no_wcall id (hFeq ▸ hmem) hin r'
      · rw [hProcNe id' h] at hin
        exact hI.idle_no_wcall id' (hFeq ▸ hmem) hin r'
    · intro r' id' hmem hp
      by_cases hid : id' = id
      · rw [hid] at hmem hp
        rcases hp with ⟨hround, hphase⟩ | hlt0
        · exfalso
          rw [hProcSelf] at hphase
          rcases hphase with h | h <;> simp at h
        · rw [hRoundEq] at hlt0
          by_cases hlt : r' < (c.procs id).round
          · rcases hI.retg_residue r' id (hFeq ▸ hmem) (Or.inr hlt) with hg | hd
            · left; exact hg
            · right; exact hDR2 r' hd
          · have hreq : r' = r := by omega
            rcases hI.retg_residue r id (hFeq ▸ hmem) (Or.inl ⟨hr, Or.inr hph⟩) with hg | hd
            · left; rw [hreq]; exact hg
            · right; rw [hreq]; exact hDR2 r hd
      · rw [hProcNe id' hid] at hp
        rcases hI.retg_residue r' id' (hFeq ▸ hmem) hp with hg | hd
        · left; exact hg
        · right; exact hDR2 r' hd
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled
      rcases hI.wcalled_residue r' id' (hFeq ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact hDR2 r' hd
  · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    refine And.intro ?_ (AbsFrame.refl P g _)
    refine ⟨hI.F_g, fun r' => (hFweq r').trans (hI.F_w r'), hI.F_card,
      hI.input_g0, hI.input_called, hI.phase_input, hI.down_closed, hI.quiescent,
      fun r' h => hI.w_bound r' (by rw [← hValeq r']; exact h),
      hI.recv_sound, hI.decided_src, hI.a_commit, hI.round_bound, ?_,
      hI.gradeA_needs_bind, hI.call_round, ?_, ?_, hI.est0, hI.grade_A_src, hI.est_ret,
      ?_, ?_, ?_, hI.c_chain, hI.est_prev_ne,
      ?_, hI.input_g0_perm, ?_, ?_, ?_, hI.retg_residue, ?_, hI.bound_quorum,
      hI.bind_supp, hI.clock_supp, hI.dead_supp, hI.carrier_agree, hI.alock_agree⟩
    · intro r' v hlast hbr hcoin id' hmem hround
      rw [hValeq] at hcoin
      exact hI.agree_locked r' v hlast hbr hcoin id' hmem hround
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.w_called r' id' hmem hcalled
    · intro r' id' hmem hround
      rw [hValeq]; exact hI.round_flip r' id' hmem hround
    · intro r' v h; rw [hValeq r']; exact hI.bind_succ r' v h
    · intro r' id' v hmem hcall; rw [hValeq r']; exact hI.call_prov r' id' v hmem hcall
    · intro r' id' hmem hround hphase v hest
      rw [hValeq r']; exact hI.est_prev r' id' hmem hround hphase v hest
    · intro r' h; rw [hValeq] at h ⊢; exact hI.w_order r' h
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.w_call_round r' id' hmem hcalled
    · intro r' h; rw [hValeq] at h; exact hI.flip_alock r' h
    · intro id' hmem hin r'; rw [hCalledEq]; exact hI.idle_no_wcall id' hmem hin r'
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.wcalled_residue r' id' hmem hcalled

end ABA
end PLTS
