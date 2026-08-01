/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Layered

/-!
# The deployment-shaped specification

The link of the refinement chain that replaces each round's graded-agreement
subsystem by its specification, and the row-by-row reading of the system that
results. The headlines that chain this with the earlier links are in
`ABA/Main.lean`.

`layeredSpec` is the deployed system with each round's graded-agreement subsystem
replaced by that round's specification, read at the deployed shape. The
substitution is one application of `ProbabilisticForwardSimulation.parallel_right`
under a syntactically identical context, followed by the three congruences the
deployed pipeline is built from — `abstract` for the rendezvous alphabet,
`relabel` for the read-back to `Lab n` (`Framework/Relabel.lean`), and
`abstract` again for the sub-protocol API — giving `substitution` and, past
the layered presentation, `deployed_layeredSpec`.

The rest of the file reads `layeredSpec` row by row, in both directions: the
rows of the specification side and of the coin oracle's family, the reading of
a joint transition of the four factors into its component rows and the
construction of one from them, and the three routes a labelled transition takes
through the two hiding layers. The core simulation of `ABA/CoreSim.lean` runs
from `layeredSpec` on this vocabulary, and the non-vacuity witnesses of
`ABA/Examples.lean` are built with it; `ABA/Main.lean` chains the simulation
with the substitution and, through `safety_transfer`, reads off the deployed
protocol's Validity and Agreement guarantee.
-/

namespace PLTS
namespace ABA

open Net Layer

/-! ## The deployment-shaped specification side

The layered system replaces its graded-agreement factor `GSub.gbcaSide` — the
family of round subsystems — by `specSide`, the family of round specifications
read over the deployed alphabet. The other three factors are reused verbatim,
so the substitution is `ProbabilisticForwardSimulation.parallel_right` applied
under the syntactically identical context, followed by the three remaining
congruences: `abstract` for the rendezvous alphabet, `relabel` for the read-back
to `Lab n`, and `abstract` again for the sub-protocol API. -/

/-- **The specification side of the deployed protocol**: the ℕ-indexed family
of round specifications, read over the deployed extended alphabet along
`GSub.gPull`. A round-tagged label — including a Byzantine drive of that
round — moves its round alone, `τ` moves one round, and `fail` is the
broadcast that keeps every round's copy of the corrupted set in lockstep. -/
noncomputable def specSide (P : Params) :
    System (ℕ → GBCA.SpecState P.n) (NLab P.n) :=
  System.family (GSub.liftedSpecG P) GSub.gOwns GSub.isFailN (GSub.gActSpec P)

@[simp] theorem specSide_init (P : Params) :
    (specSide P).init = fun _ => GBCA.SpecState.initial P.n := rfl

/-- The specification side is an LTS: every round's specification is. -/
theorem specSide_isLTS (P : Params) : (specSide P).IsLTS :=
  System.family_isLTS (GSub.liftedSpecG_isLTS P) _ _ _

/-- The state of the deployment-shaped specification: the round
specifications beside the layered system's other three factors. -/
abbrev LayeredSpecState (P : Params) : Type :=
  (ℕ → GBCA.SpecState P.n) ×
    ((∀ _ : Fin P.n, CoreNodeN P.n) × (ANetState P.n × (ℕ → WCC.SpecState P.n)))

/-- The four factors side by side, over the extended alphabet: `layeredPre`
with its graded-agreement factor replaced. -/
noncomputable def layeredSpecPre (P : Params) : System (LayeredSpecState P) (NLab P.n) :=
  (specSide P).parallel
    ((System.syncProduct (coreProcN P)).parallel ((aNet P).parallel (wccLift P)))

/-- **The deployment-shaped specification**: the rendezvous alphabet hidden,
the result read back over `Lab n`, the sub-protocol API hidden — the pipeline
of `layered`, factor for factor. -/
noncomputable def layeredSpec (P : Params) : System (LayeredSpecState P) (Lab P.n) :=
  (((layeredSpecPre P).abstract (netEvtLabels P.n)).relabel).abstract (Lab.hiddenAPI P.n)

/-! ### The substitution -/

/-- The pointwise round relation: every round's subsystem state is related to
that round's specification state. -/
def RsubAll (P : Params) (s : ℕ → GSub.GSubState P.n)
    (t : ℕ → GBCA.SpecState P.n) : Prop :=
  ∀ r, GSub.Rsub P r (s r) (t r)

/-- **The family substitution**: the graded-agreement side of the deployed
protocol is forward simulated by the specification side, round by round. The
per-round simulation is `GSub.subSim`; the broadcast compatibility is
`GSub.subSim_failAct`. -/
theorem famSubSim (P : Params) :
    ForwardSimulation (GSub.gbcaSide P) (specSide P) (RsubAll P) :=
  ForwardSimulation.family GSub.gOwns GSub.isFailN (GSub.gAct P) (GSub.gActSpec P)
    (GSub.subSim P) (GSub.subSim_failAct P)

/-- The family substitution as a probabilistic forward simulation: both sides
are LTS, and the relation holds at the initial states. -/
theorem famSubSimProb (P : Params) :
    ProbabilisticForwardSimulation (GSub.gbcaSide P) (specSide P)
      (diracRel (RsubAll P)) :=
  ForwardSimulation.toProbabilistic (GSub.gbcaSide_isLTS P) (specSide_isLTS P)
    (fun r => GSub.subSim_init P r) (famSubSim P)

/-- **The substitution simulation at the deployed shape**: the four
congruences applied to the family substitution under the layered system's own
context — `parallel_right` for the three untouched factors, `abstract` for the
rendezvous alphabet, `relabel` for the read-back over `Lab n`, and `abstract`
for the sub-protocol API. -/
noncomputable def substSim (P : Params) :
    ProbabilisticForwardSimulation (layered P) (layeredSpec P)
      (parallelRel (diracRel (RsubAll P))) :=
  ((((famSubSimProb P).parallel_right
    ((System.syncProduct (coreProcN P)).parallel
      ((aNet P).parallel (wccLift P)))).abstract
        (netEvtLabels P.n)).relabel).abstract (Lab.hiddenAPI P.n)

/-- **The substitution inclusion**: every trace distribution achievable by the
layered system is achievable by the deployment-shaped
specification. -/
theorem substitution (P : Params) :
    achievableTraceDists (layered P) ⊆ achievableTraceDists (layeredSpec P) :=
  (substSim P).achievableTraceDists_subset

/-- **The deployed protocol refines the deployment-shaped specification**:
every trace distribution achievable by the deployed reading is achievable once
each round's graded-agreement subsystem is replaced by its specification, the
other three factors untouched. -/
theorem deployed_layeredSpec (P : Params) :
    achievableTraceDists (deployed P) ⊆ achievableTraceDists (layeredSpec P) :=
  Set.Subset.trans (layered_atd P).subset (substitution P)

/-! ### The specification side's rows

The family routes a round-tagged label to its round, takes `τ` at any round,
broadcasts `fail`, and idles on everything else — `GSub.gbcaSide`'s rows with
the round subsystem replaced by its specification. -/

/-- The specification side idles on a label no round owns and no broadcast. -/
theorem specSide_idle (P : Params) (G : ℕ → GBCA.SpecState P.n) {L : NLab P.n}
    (hτ : L ≠ Silent.τ) (hown : GSub.gOwns L = none) (hf : ¬ GSub.isFailN L) :
    (specSide P).step G L (PMF.pure G) := by
  rw [specSide, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hτ, hown, hf, rfl⟩))

/-- Corruption is broadcast to every round specification. -/
theorem specSide_fail (P : Params) (G : ℕ → GBCA.SpecState P.n) (k : Fin P.n) :
    (specSide P).step G (Sum.inl (Lab.fail k)) (PMF.pure fun r => (G r).corrupt P k) := by
  rw [specSide, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl, trivial, rfl⟩))

/-- An owned label is answered by its round alone. -/
theorem specSide_owned_inv (P : Params) {G : ℕ → GBCA.SpecState P.n}
    {L : NLab P.n} {r : ℕ} (hL : GSub.gOwns L = some r) (hτ : L ≠ Silent.τ)
    {μ : PMF (ℕ → GBCA.SpecState P.n)} (h : (specSide P).step G L μ) :
    ∃ X, (GSub.liftedSpecG P r).step (G r) L (PMF.pure X) ∧
      μ = PMF.pure (Function.update G r X) := by
  rw [specSide, System.family_step_iff] at h
  rcases h with ⟨habs, -⟩ | ⟨r', hown, μr, hstep, rfl⟩ | ⟨-, hown, -, -⟩ | ⟨-, hown, -, -⟩
  · exact absurd habs hτ
  · obtain rfl : r' = r := by rw [hL] at hown; exact (Option.some.inj hown).symm
    obtain ⟨X, rfl⟩ := GSub.liftedSpecG_isLTS P r' _ _ _ hstep
    exact ⟨X, hstep, by rw [PMF.pure_map]⟩
  · rw [hL] at hown; exact absurd hown (by simp)
  · rw [hL] at hown; exact absurd hown (by simp)

/-- A round's own row, read into the specification side: the label the round
owns is answered by that round, every other round standing still. -/
theorem specSide_owned (P : Params) {G : ℕ → GBCA.SpecState P.n} {L : NLab P.n}
    {l₀ : Lab P.n} {r : ℕ} {X : GBCA.SpecState P.n}
    (hown : GSub.gOwns L = some r) (hpull : GSub.gPull P.n L = some l₀)
    (h : GBCA.Step P r (G r) l₀ (PMF.pure X)) :
    (specSide P).step G L (PMF.pure (Function.update G r X)) := by
  rw [specSide, System.family_step_iff]
  refine Or.inr (Or.inl ⟨r, hown, PMF.pure X, ?_, by rw [PMF.pure_map]⟩)
  rw [GSub.liftedSpecG, System.mapIdle_step_some hpull]
  exact h

/-- A round's own silent rule — the specification's binding kill — read into
the specification side. -/
theorem specSide_tau (P : Params) {G : ℕ → GBCA.SpecState P.n} {r : ℕ}
    {X : GBCA.SpecState P.n} (h : GBCA.Step P r (G r) Lab.tau (PMF.pure X)) :
    (specSide P).step G (Sum.inl Lab.tau) (PMF.pure (Function.update G r X)) := by
  rw [specSide, System.family_step_iff]
  refine Or.inl ⟨rfl, r, PMF.pure X, ?_, by rw [PMF.pure_map]⟩
  rw [GSub.liftedSpecG, System.mapIdle_step_some (GSub.gPull_inl (Lab.tau : Lab P.n))]
  exact h

/-- A label a round specification owns is answered by that round alone, read
back over the specification's own alphabet. -/
theorem specSide_owned_step (P : Params) {G G' : ℕ → GBCA.SpecState P.n}
    {L : NLab P.n} {l₀ : Lab P.n} {r : ℕ}
    (hown : GSub.gOwns L = some r) (hτ : L ≠ Silent.τ)
    (hpull : GSub.gPull P.n L = some l₀)
    (h : (specSide P).step G L (PMF.pure G')) :
    ∃ X, GBCA.Step P r (G r) l₀ (PMF.pure X) ∧ G' = Function.update G r X := by
  obtain ⟨X, hstep, heq⟩ := specSide_owned_inv P hown hτ h
  rw [GSub.liftedSpecG, System.mapIdle_step_some hpull] at hstep
  exact ⟨X, hstep, pureN_inj heq⟩

/-- Only the identity successor answers a label no round owns and no
broadcast. -/
theorem specSide_idle_inv (P : Params) {G : ℕ → GBCA.SpecState P.n} {L : NLab P.n}
    {μ : PMF (ℕ → GBCA.SpecState P.n)} (h : (specSide P).step G L μ)
    (hτ : L ≠ Silent.τ) (hown : GSub.gOwns L = none) (hf : ¬ GSub.isFailN L) :
    μ = PMF.pure G := by
  rw [specSide, System.family_step_iff] at h
  rcases h with ⟨habs, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
  · exact absurd habs hτ
  · rw [hown] at hr; exact absurd hr (by simp)
  · exact absurd hglob hf
  · rfl

/-- Corruption is broadcast to every round. -/
theorem specSide_fail_inv (P : Params) {G : ℕ → GBCA.SpecState P.n} (k : Fin P.n)
    {μ : PMF (ℕ → GBCA.SpecState P.n)}
    (h : (specSide P).step G (Sum.inl (Lab.fail k)) μ) :
    μ = PMF.pure (fun r => (G r).corrupt P k) := by
  rw [specSide, System.family_step_iff] at h
  rcases h with ⟨habs, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, hglob, -⟩
  · exact absurd habs (by simp)
  · exact absurd hr (by simp)
  · rfl
  · exact absurd trivial hglob

/-- A silent transition of the family is one round's own silent rule — the
specification's binding kill. -/
theorem specSide_tau_inv (P : Params) {G : ℕ → GBCA.SpecState P.n}
    {μ : PMF (ℕ → GBCA.SpecState P.n)}
    (h : (specSide P).step G (Sum.inl Lab.tau) μ) :
    ∃ (r : ℕ) (X : GBCA.SpecState P.n),
      (GSub.liftedSpecG P r).step (G r) (Sum.inl Lab.tau) (PMF.pure X) ∧
      μ = PMF.pure (Function.update G r X) := by
  rw [specSide, System.family_step_iff] at h
  rcases h with ⟨-, r, μr, hstep, rfl⟩ | ⟨r, hr, -⟩ | ⟨habs, -, -, -⟩ | ⟨habs, -, -, -⟩
  · obtain ⟨X, rfl⟩ := GSub.liftedSpecG_isLTS P r _ _ _ hstep
    exact ⟨r, X, hstep, by rw [PMF.pure_map]⟩
  · exact absurd hr (by simp)
  · exact absurd rfl habs
  · exact absurd rfl habs

/-! ### The coin oracle's rows

The oracle is a family over the same shape: a round-tagged label moves its
round, `fail` is broadcast, and everything else leaves it put. -/

/-- The coin oracle's family idles on a label outside its own API. -/
theorem wccFamily_idle_inv (P : Params) {o : ℕ → WCC.SpecState P.n} {l : Lab P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} (hl : l ≠ Lab.tau) (hr : Lab.wccRound l = none)
    (hf : ¬ Lab.isFail l) (h : (WCC.specFamily P).step o l ω) : ω = PMF.pure o := by
  rw [WCC.specFamily, System.family_step_iff] at h
  rcases h with ⟨hτ, -⟩ | ⟨r, hr', -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
  · exact absurd hτ hl
  · rw [hr] at hr'; exact absurd hr' (by simp)
  · exact absurd hglob hf
  · rfl

/-- A label the coin oracle's family owns is answered by its round alone. -/
theorem wccFamily_owned_inv (P : Params) {o : ℕ → WCC.SpecState P.n} {l : Lab P.n}
    {r : ℕ} {ω : PMF (ℕ → WCC.SpecState P.n)} (hl : l ≠ Lab.tau)
    (hr : Lab.wccRound l = some r) (h : (WCC.specFamily P).step o l ω) :
    ∃ μw', WCC.Step P r (o r) l μw' ∧ ω = μw'.map (Function.update o r) := by
  rw [WCC.specFamily, System.family_step_iff] at h
  rcases h with ⟨hτ, -⟩ | ⟨r', hr', μw', hstep, rfl⟩ | ⟨-, hr'', -, -⟩ | ⟨-, hr'', -, -⟩
  · exact absurd hτ hl
  · obtain rfl : r' = r := by rw [hr] at hr'; exact (Option.some.inj hr').symm
    exact ⟨μw', hstep, rfl⟩
  · rw [hr] at hr''; exact absurd hr'' (by simp)
  · rw [hr] at hr''; exact absurd hr'' (by simp)

/-- A round of the coin oracle answers the label it owns, every other round
standing still. -/
theorem wccFamily_owned (P : Params) (o : ℕ → WCC.SpecState P.n) {l : Lab P.n}
    {r : ℕ} {x : WCC.SpecState P.n} (hr : Lab.wccRound l = some r)
    (h : WCC.Step P r (o r) l (PMF.pure x)) :
    (WCC.specFamily P).step o l (PMF.pure (Function.update o r x)) := by
  rw [WCC.specFamily, System.family_step_iff]
  exact Or.inr (Or.inl ⟨r, hr, PMF.pure x, h, by rw [PMF.pure_map]⟩)

/-- A round of the coin oracle takes its own silent rule — the coin
resolution, the one transition of the development that is not a Dirac. -/
theorem wccFamily_tau (P : Params) (o : ℕ → WCC.SpecState P.n) {r : ℕ}
    {μw : PMF (WCC.SpecState P.n)} (h : WCC.Step P r (o r) Lab.tau μw) :
    (WCC.specFamily P).step o Lab.tau (μw.map (Function.update o r)) := by
  rw [WCC.specFamily, System.family_step_iff]
  exact Or.inl ⟨rfl, r, μw, h, rfl⟩

/-- Corruption is broadcast to every round of the coin oracle's family. -/
theorem wccFamily_fail (P : Params) (o : ℕ → WCC.SpecState P.n) (k : Fin P.n) :
    (WCC.specFamily P).step o (.fail k) (PMF.pure fun r => (o r).corrupt P k) := by
  rw [WCC.specFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl, trivial, rfl⟩))

/-- A corruption broadcast is answered by every round of the coin oracle's
family. -/
theorem wccFamily_fail_inv (P : Params) {o : ℕ → WCC.SpecState P.n} (k : Fin P.n)
    {ω : PMF (ℕ → WCC.SpecState P.n)} (h : (WCC.specFamily P).step o (.fail k) ω) :
    ω = PMF.pure fun r => (o r).corrupt P k := by
  rw [WCC.specFamily, System.family_step_iff] at h
  rcases h with ⟨hτ, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, hglob, -⟩
  · exact absurd hτ (by simp)
  · exact absurd hr (by simp [Lab.wccRound])
  · rfl
  · exact absurd trivial hglob

/-! ### Reading a deployment-shaped transition into its four factors -/

/-- Build a joint transition of the four factors on a visible label, the
oracle's successor left arbitrary. -/
theorem layeredSpecPre_vis_step (P : Params) {G G' : ℕ → GBCA.SpecState P.n}
    {C C' : ∀ _ : Fin P.n, CoreNodeN P.n} {A A' : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {ω : PMF (ℕ → WCC.SpecState P.n)} {L : NLab P.n}
    (hL : L ≠ Silent.τ)
    (hG : (specSide P).step G L (PMF.pure G'))
    (hC : ∀ i, CoreProcStepN P i (C i) L (PMF.pure (C' i)))
    (hA : ANetStep P A L (PMF.pure A'))
    (hW : (wccLift P).step o L ω) :
    (layeredSpecPre P).step (G, C, A, o) L
      (prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω))) := by
  rw [layeredSpecPre, System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure G', prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω),
    hG, ?_, rfl⟩
  rw [System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure C', prodPMF (PMF.pure A') ω, syncCore_pure hL hC, ?_, rfl⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure A', ω, hA, hW, rfl⟩

/-- A visible transition of the four factors: all of them move together, and
only the oracle's successor can fail to be a Dirac. -/
theorem layeredSpecPre_vis_inv (P : Params) {G : ℕ → GBCA.SpecState P.n}
    {C : ∀ _ : Fin P.n, CoreNodeN P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {L : NLab P.n} (hL : L ≠ Silent.τ)
    {μ : PMF (LayeredSpecState P)} (h : (layeredSpecPre P).step (G, C, A, o) L μ) :
    ∃ (G' : ℕ → GBCA.SpecState P.n) (C' : ∀ _ : Fin P.n, CoreNodeN P.n)
      (A' : ANetState P.n) (ω : PMF (ℕ → WCC.SpecState P.n)),
      (specSide P).step G L (PMF.pure G') ∧
      (∀ i, CoreProcStepN P i (C i) L (PMF.pure (C' i))) ∧
      ANetStep P A L (PMF.pure A') ∧ (wccLift P).step o L ω ∧
      μ = prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω)) := by
  rw [layeredSpecPre, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hG, hrest, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
  · obtain ⟨G', rfl⟩ := specSide_isLTS P _ _ _ hG
    rw [System.parallel_step] at hrest
    rcases hrest with ⟨-, μ₂, μ₃, hC, hrest, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
    · obtain ⟨C', rfl, hall⟩ := syncCore_inv hC
      rw [System.parallel_step] at hrest
      rcases hrest with ⟨-, μ₃, ω, hA, hW, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
      · obtain ⟨A', rfl⟩ := aNetStep_dirac hA
        exact ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩
      · exact absurd habs hL
      · exact absurd habs hL
    · exact absurd habs hL
    · exact absurd habs hL
  · exact absurd habs hL
  · exact absurd habs hL

/-- Build a silent transition of the four factors from a specification-side
one. -/
theorem layeredSpecPre_tau_spec (P : Params) {G G' : ℕ → GBCA.SpecState P.n}
    {C : ∀ _ : Fin P.n, CoreNodeN P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hG : (specSide P).step G (Sum.inl Lab.tau) (PMF.pure G')) :
    (layeredSpecPre P).step (G, C, A, o) (Sum.inl Lab.tau) (PMF.pure (G', C, A, o)) := by
  rw [layeredSpecPre, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure G', hG, ?_⟩)
  rw [prodPMF_pure_pure]

/-- Build a silent transition of the four factors from a coin resolution. -/
theorem layeredSpecPre_tau_wcc (P : Params) {G : ℕ → GBCA.SpecState P.n}
    {C : ∀ _ : Fin P.n, CoreNodeN P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {ω : PMF (ℕ → WCC.SpecState P.n)}
    (hW : (WCC.specFamily P).step o Lab.tau ω) :
    (layeredSpecPre P).step (G, C, A, o) (Sum.inl Lab.tau)
      (prodPMF (PMF.pure G) (prodPMF (PMF.pure C) (prodPMF (PMF.pure A) ω))) := by
  rw [layeredSpecPre, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, _, ?_, rfl⟩)
  rw [System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, _, ?_, rfl⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, ω,
    (System.mapIdle_step_some (wccPull_inl Lab.tau) ω).mpr hW, rfl⟩)

/-- A silent transition of the four factors: no round loop has a `τ` row, so it
is the specification family's binding kill, the ABA-side network's own
injection, or the coin resolution. -/
theorem layeredSpecPre_tau_inv (P : Params) {G : ℕ → GBCA.SpecState P.n}
    {C : ∀ _ : Fin P.n, CoreNodeN P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {μ : PMF (LayeredSpecState P)}
    (h : (layeredSpecPre P).step (G, C, A, o) (Sum.inl Lab.tau) μ) :
    (∃ G', (specSide P).step G (Sum.inl Lab.tau) (PMF.pure G') ∧
        μ = PMF.pure (G', C, A, o)) ∨
    (∃ A', ANetStep P A (Sum.inl Lab.tau) (PMF.pure A') ∧
        μ = PMF.pure (G, C, A', o)) ∨
    (∃ ω, (WCC.specFamily P).step o Lab.tau ω ∧
        μ = prodPMF (PMF.pure G) (prodPMF (PMF.pure C) (prodPMF (PMF.pure A) ω))) := by
  rw [layeredSpecPre, System.parallel_step] at h
  rcases h with ⟨habs, -⟩ | ⟨-, μ₁, hG, rfl⟩ | ⟨-, μ₂, hrest, rfl⟩
  · exact absurd rfl habs
  · obtain ⟨G', rfl⟩ := specSide_isLTS P _ _ _ hG
    exact Or.inl ⟨G', hG, by rw [prodPMF_pure_pure]⟩
  · rw [System.parallel_step] at hrest
    rcases hrest with ⟨habs, -⟩ | ⟨-, μ₂, hC, rfl⟩ | ⟨-, μ₃, hrest, rfl⟩
    · exact absurd rfl habs
    · exact (syncCore_no_tau hC).elim
    · rw [System.parallel_step] at hrest
      rcases hrest with ⟨habs, -⟩ | ⟨-, μ₃, hA, rfl⟩ | ⟨-, ω, hW, rfl⟩
      · exact absurd rfl habs
      · obtain ⟨A', rfl⟩ := aNetStep_dirac hA
        exact Or.inr (Or.inl ⟨A', hA,
          by rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure]⟩)
      · exact Or.inr (Or.inr ⟨ω,
          (System.mapIdle_step_some (wccPull_inl Lab.tau) ω).mp hW, rfl⟩)

/-! ### The two hiding layers -/

/-- **The deployment-shaped group**: the rendezvous alphabet hidden, the result
read back over `Lab n`. Scaffolding for the row-by-row reading below; nothing
outside this file names it. -/
private noncomputable def layeredSpecGroup (P : Params) : System (LayeredSpecState P) (Lab P.n) :=
  ((layeredSpecPre P).abstract (netEvtLabels P.n)).relabel

theorem layeredSpec_eqS (P : Params) :
    layeredSpec P = (layeredSpecGroup P).abstract (Lab.hiddenAPI P.n) := rfl

/-- The group's step relation, unfolded to the hidden rendezvous case and the
shared-label case. -/
theorem layeredSpecGroup_step_iff (P : Params) (q : LayeredSpecState P) (l : Lab P.n)
    (μ : PMF (LayeredSpecState P)) :
    (layeredSpecGroup P).step q l μ ↔
      (l = .tau ∧ ∃ e : NetEvt P.n, (layeredSpecPre P).step q (Sum.inr e) μ) ∨
      (layeredSpecPre P).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_netEvtLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_netEvtLabels l, hstep⟩

/-- The deployment-shaped specification's step relation: a sub-protocol API
label seen as `τ`, or a label that survives the hiding. -/
theorem layeredSpec_step_iff (P : Params) (q : LayeredSpecState P) (l : Lab P.n)
    (μ : PMF (LayeredSpecState P)) :
    (layeredSpec P).step q l μ ↔
      (l = .tau ∧ ∃ l' ∈ Lab.hiddenAPI P.n, (layeredSpecGroup P).step q l' μ) ∨
      (l ∉ Lab.hiddenAPI P.n ∧ (layeredSpecGroup P).step q l μ) :=
  System.abstract_step _ _ _ _ _

/-! ### Building a transition through the two hiding layers

A transition of the four factors reaches the deployment-shaped specification
along one of three routes, according to its label: a rendezvous label and a
sub-protocol API label are both hidden to `τ`, and every remaining label
survives both hidings. -/

/-- A rendezvous transition is silent: the rendezvous alphabet is hidden. -/
theorem layeredSpec_rendezvous (P : Params) {q : LayeredSpecState P} {e : NetEvt P.n}
    {μ : PMF (LayeredSpecState P)} (h : (layeredSpecPre P).step q (Sum.inr e) μ) :
    (layeredSpec P).step q Lab.tau μ := by
  rw [layeredSpec_step_iff]
  exact Or.inr ⟨by simp, (layeredSpecGroup_step_iff P q Lab.tau μ).mpr (Or.inl ⟨rfl, e, h⟩)⟩

/-- A sub-protocol API label is silent: the API is hidden. -/
theorem layeredSpec_hidden (P : Params) {q : LayeredSpecState P} {l : Lab P.n}
    {μ : PMF (LayeredSpecState P)} (hl : l ∈ Lab.hiddenAPI P.n)
    (h : (layeredSpecPre P).step q (Sum.inl l) μ) :
    (layeredSpec P).step q Lab.tau μ := by
  rw [layeredSpec_step_iff]
  exact Or.inl ⟨rfl, l, hl, (layeredSpecGroup_step_iff P q l μ).mpr (Or.inr h)⟩

/-- A label outside the sub-protocol API survives both hidings. -/
theorem layeredSpec_vis (P : Params) {q : LayeredSpecState P} {l : Lab P.n}
    {μ : PMF (LayeredSpecState P)} (hl : l ∉ Lab.hiddenAPI P.n)
    (h : (layeredSpecPre P).step q (Sum.inl l) μ) :
    (layeredSpec P).step q l μ := by
  rw [layeredSpec_step_iff]
  exact Or.inr ⟨hl, (layeredSpecGroup_step_iff P q l μ).mpr (Or.inr h)⟩

end ABA

end PLTS
