/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.CoreSim
import Leslie2Protocols.ABA.Layered

/-!
# The deployment-shaped specification

The last two links of the refinement chain. The headlines that chain them
together with the earlier links are in `ABA/Main.lean`.

`layeredSpec` is the deployed system with each round's graded-agreement subsystem
replaced by that round's specification, read at the deployed shape. The
substitution is one application of `ProbabilisticForwardSimulation.parallel_right`
under a syntactically identical context, followed by the three congruences the
deployed pipeline is built from — `abstract` for the rendezvous alphabet,
`relabel` for the read-back to `Lab n` (`Framework/Relabel.lean`), and
`abstract` again for the sub-protocol API — giving `substitution` and, past
the layered presentation, `deployed_layeredSpec`.

`layeredSpecDefl` then deflates the two ABA-side factors of `layeredSpec` — the
process nodes and the network adversary — into the monolithic core state, a
strong functional simulation into `hybridSpec` (`layeredSpec_refines`). That is
the last link before the core simulation of `ABA/CoreSim.lean`; `ABA/Main.lean`
chains the two and, through `safety_transfer`, reads off the deployed
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

/-! ## The spec-side deflation

`layeredSpec` and `hybridSpec` hold the same four layers under different
partitions. The round specifications and the coin oracle occupy the same
coordinate on both sides; the two ABA-side factors — the round-loop records
and the DECIDED-and-corruption network — are the monolithic `CoreState` cut
along the layer boundary. `layeredSpecDefl` is that repartition, and every row of
`layeredSpec` is a row of `hybridSpec` read through it. -/

private theorem coreStateS_ext {n : ℕ} {a b : CoreState n} (h1 : a.procs = b.procs)
    (h2 : a.decidedSent = b.decidedSent) (h3 : a.decidedRecv = b.decidedRecv)
    (h4 : a.F = b.F) : a = b := by
  cases a; cases b; cases h1; cases h2; cases h3; cases h4; rfl

/-- **The monolithic core state of an layered ABA side**: the round loops
supply the control records and the receipt pools, the ABA-side network the
sent pools and the corrupted set. -/
def deflCore {P : Params} (C : ∀ _ : Fin P.n, CoreNodeN P.n) (a : ANetState P.n) :
    CoreState P.n where
  procs := fun j => (C j).proc
  decidedSent := a.dpool
  decidedRecv := fun i => (C i).decIn
  F := a.F

@[simp] theorem deflCore_procs {P : Params} (C : ∀ _ : Fin P.n, CoreNodeN P.n)
    (a : ANetState P.n) : (deflCore C a).procs = fun j => (C j).proc := rfl
@[simp] theorem deflCore_decidedSent {P : Params} (C : ∀ _ : Fin P.n, CoreNodeN P.n)
    (a : ANetState P.n) : (deflCore C a).decidedSent = a.dpool := rfl
@[simp] theorem deflCore_decidedRecv {P : Params} (C : ∀ _ : Fin P.n, CoreNodeN P.n)
    (a : ANetState P.n) : (deflCore C a).decidedRecv = fun i => (C i).decIn := rfl
@[simp] theorem deflCore_F {P : Params} (C : ∀ _ : Fin P.n, CoreNodeN P.n)
    (a : ANetState P.n) : (deflCore C a).F = a.F := rfl

/-- The quorum count of the deflated state is the round loop's own count: the
receipt pools are the round loops'. -/
@[simp] theorem deflCore_decidedCount {P : Params}
    (C : ∀ _ : Fin P.n, CoreNodeN P.n) (a : ANetState P.n) (i : Fin P.n) (b : Bool) :
    (deflCore C a).decidedCount i b = (C i).decidedCount b := rfl

/-- **The spec-side deflation**: the round specifications and the coin oracle
untouched, the two ABA-side factors assembled into the monolithic core. -/
def layeredSpecDefl (P : Params) (s : LayeredSpecState P) :
    (ℕ → GBCA.SpecState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)) :=
  (s.1, deflCore s.2.1 s.2.2.1, s.2.2.2)

@[simp] theorem layeredSpecDefl_apply {P : Params} (G : ℕ → GBCA.SpecState P.n)
    (C : ∀ _ : Fin P.n, CoreNodeN P.n) (a : ANetState P.n)
    (o : ℕ → WCC.SpecState P.n) :
    layeredSpecDefl P (G, C, a, o) = (G, deflCore C a, o) := rfl

/-- The deflation carries the deployment-shaped initial state to the hybrid
one. -/
theorem layeredSpecDefl_init (P : Params) :
    layeredSpecDefl P (layeredSpec P).init = (hybridSpec P).init :=
  Prod.ext rfl (Prod.ext (coreStateS_ext rfl rfl rfl rfl) rfl)

/-! ### Deltas of the deflation

Each row writes one round-loop record and one network slot; read through the
deflation, the pair becomes the matching one-row update of the monolithic
core state. -/

/-- A control-record write is the monolithic one-row control write. -/
theorem deflCore_setProc {P : Params} (C : ∀ _ : Fin P.n, CoreNodeN P.n)
    (a : ANetState P.n) (id : Fin P.n) (p : ProcCore P.n) :
    deflCore (Function.update C id ((C id).setProc p)) a
      = (deflCore C a).setProc id p := by
  refine coreStateS_ext (funext fun i => ?_) rfl (funext fun i => ?_) rfl
  · change (Function.update C id ((C id).setProc p) i).proc
      = Function.update (fun j => (C j).proc) id p i
    by_cases hi : i = id
    · subst hi; simp only [Function.update_self]; rfl
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
  · change (Function.update C id ((C id).setProc p) i).decIn = (C i).decIn
    by_cases hi : i = id
    · subst hi; simp only [Function.update_self]; rfl
    · rw [Function.update_of_ne hi]

/-- A DECIDED receipt is the monolithic delivery. -/
theorem deflCore_recvDec {P : Params} (C : ∀ _ : Fin P.n, CoreNodeN P.n)
    (a : ANetState P.n) (i k : Fin P.n) (b : Bool) :
    deflCore (Function.update C i ((C i).recvDec k b)) a
      = (deflCore C a).deliverDecided i k b := by
  refine coreStateS_ext (funext fun i' => ?_) rfl (funext fun i' => ?_) rfl
  · change (Function.update C i ((C i).recvDec k b) i').proc = (C i').proc
    by_cases hi : i' = i
    · subst hi; simp only [Function.update_self]; rfl
    · rw [Function.update_of_ne hi]
  · change (Function.update C i ((C i).recvDec k b) i').decIn
      = Function.update (fun j => (C j).decIn) i
          (Function.update (C i).decIn k (insert b ((C i).decIn k))) i'
    by_cases hi : i' = i
    · subst hi; simp only [Function.update_self]; rfl
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]

/-- A DECIDED pool insert is the monolithic multicast. -/
theorem deflCore_dput {P : Params} (C : ∀ _ : Fin P.n, CoreNodeN P.n)
    (a : ANetState P.n) (j : Fin P.n) (b : Bool) :
    deflCore C (a.dput j b) = (deflCore C a).sendDecided j b := rfl

/-- The unfused coin return: the round advance publishes nothing. -/
theorem deflCore_stepRound_plain {P : Params} (C : ∀ _ : Fin P.n, CoreNodeN P.n)
    (a : ANetState P.n) (id : Fin P.n) (c : Bool)
    (hg : ∀ v : Bool, (C id).proc.lastGrade ≠ some (.A v)) :
    deflCore (Function.update C id ((C id).stepRound c)) a
      = (deflCore C a).stepRound id c := by
  rw [show (C id).stepRound c = (C id).setProc
      { (C id).proc with
        est := some ((C id).proc.est.getD c), lastGrade := none,
        round := (C id).proc.round + 1, phase := .toCallG } from rfl,
    deflCore_setProc]
  unfold CoreState.stepRound
  cases hlg : (C id).proc.lastGrade with
  | none => rw [show ((deflCore C a).procs id).lastGrade = none from hlg]; rfl
  | some out =>
    cases out with
    | A v => exact absurd hlg (hg v)
    | B v => rw [show ((deflCore C a).procs id).lastGrade = some (.B v) from hlg]; rfl
    | C => rw [show ((deflCore C a).procs id).lastGrade = some .C from hlg]; rfl

/-- **The rejoining of the fused coin return** (D10): the round loop's round
advance joined with the network's publication is the monolithic round advance
on an `A` grade. -/
theorem deflCore_stepRound_pub {P : Params} (C : ∀ _ : Fin P.n, CoreNodeN P.n)
    (a : ANetState P.n) (id : Fin P.n) (c b : Bool)
    (hg : (C id).proc.lastGrade = some (.A b)) :
    deflCore (Function.update C id ((C id).stepRound c)) (a.dput id b)
      = (deflCore C a).stepRound id c := by
  rw [show (C id).stepRound c = (C id).setProc
      { (C id).proc with
        est := some ((C id).proc.est.getD c), lastGrade := none,
        round := (C id).proc.round + 1, phase := .toCallG } from rfl,
    deflCore_setProc, deflCore_dput]
  unfold CoreState.stepRound
  rw [show ((deflCore C a).procs id).lastGrade = some (.A b) from hg]
  rfl

/-- Corruption commutes with the deflation: the ABA-side network's corrupted
set is the monolithic one, and the two guards `k ∉ F ∧ |F| < f` agree (D1). -/
theorem deflCore_corrupt {P : Params} (C : ∀ _ : Fin P.n, CoreNodeN P.n)
    (a : ANetState P.n) (k : Fin P.n) :
    deflCore C (ANetState.corrupt P k a) = (deflCore C a).corrupt P k := by
  unfold CoreState.corrupt ANetState.corrupt
  simp only [deflCore_F]
  by_cases hc : k ∉ a.F ∧ a.F.card < P.f
  · rw [if_pos hc, if_pos hc]; rfl
  · rw [if_neg hc, if_neg hc]

/-! ### Pushing the successor distribution forward

The only factor whose successor need not be a Dirac is the coin oracle, and it
occupies the same coordinate on both sides; the deflation is therefore applied
under one `map`. -/

theorem map_layeredSpecDefl_prod {P : Params} (G : ℕ → GBCA.SpecState P.n)
    (C : ∀ _ : Fin P.n, CoreNodeN P.n) (a : ANetState P.n)
    (ω : PMF (ℕ → WCC.SpecState P.n)) :
    (prodPMF (PMF.pure G) (prodPMF (PMF.pure C) (prodPMF (PMF.pure a) ω))).map
        (layeredSpecDefl P)
      = prodPMF (PMF.pure G) (prodPMF (PMF.pure (deflCore C a)) ω) := by
  simp only [prodPMF_pure_left, PMF.map_comp]
  rfl

/-! ### The specification side's rows

The family routes a round-tagged label to its round, takes `τ` at any round,
broadcasts `fail`, and idles on everything else — `GSub.gbcaSide`'s rows with
the round subsystem replaced by its specification. -/

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

/-- The family idles on a label no round owns and no broadcast. -/
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

/-! ### Assembling the hybrid's transitions

The hybrid is `(GBCA.specFamily ∥ (core ∥ WCC.specFamily))` with the
sub-protocol API hidden; the lemmas below build each of its rows out of the
component rows the deployment-shaped specification supplies. -/

/-- The system whose sub-protocol API `hybridSpec` hides. Scaffolding for the
row-by-row reading below; nothing outside this file names it. -/
private noncomputable def hybridSpecPre (P : Params) :
    System ((ℕ → GBCA.SpecState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))
      (Lab P.n) :=
  (GBCA.specFamily P).parallel (context P)

theorem hybridSpec_eqS (P : Params) :
    hybridSpec P = (hybridSpecPre P).abstract (Lab.hiddenAPI P.n) := rfl

/-- The round-`r` instance moves on a label it owns. -/
theorem specFamilyS_owned (P : Params) (S : ℕ → GBCA.SpecState P.n) (r : ℕ)
    {l : Lab P.n} (hl : Lab.gbcaRound l = some r) {X : GBCA.SpecState P.n}
    (h : GBCA.Step P r (S r) l (PMF.pure X)) :
    (GBCA.specFamily P).step S l (PMF.pure (Function.update S r X)) := by
  rw [GBCA.specFamily, System.family_step_iff]
  exact Or.inr (Or.inl ⟨r, hl, PMF.pure X, h, by rw [PMF.pure_map]⟩)

/-- An owned label whose instance stands still. -/
theorem specFamilyS_owned_id (P : Params) (S : ℕ → GBCA.SpecState P.n) (r : ℕ)
    {l : Lab P.n} (hl : Lab.gbcaRound l = some r)
    (h : GBCA.Step P r (S r) l (PMF.pure (S r))) :
    (GBCA.specFamily P).step S l (PMF.pure S) := by
  have hstep := specFamilyS_owned P S r hl h
  rwa [Function.update_eq_self] at hstep

/-- The round-`r` instance takes its own silent rule. -/
theorem specFamilyS_tau (P : Params) (S : ℕ → GBCA.SpecState P.n) (r : ℕ)
    {X : GBCA.SpecState P.n} (h : GBCA.Step P r (S r) .tau (PMF.pure X)) :
    (GBCA.specFamily P).step S Lab.tau (PMF.pure (Function.update S r X)) := by
  rw [GBCA.specFamily, System.family_step_iff]
  exact Or.inl ⟨rfl, r, PMF.pure X, h, by rw [PMF.pure_map]⟩

/-- A label no instance owns and no broadcast: the family idles. -/
theorem specFamilyS_idle (P : Params) (S : ℕ → GBCA.SpecState P.n) {l : Lab P.n}
    (hl : l ≠ Lab.tau) (hr : Lab.gbcaRound l = none) (hf : ¬ Lab.isFail l) :
    (GBCA.specFamily P).step S l (PMF.pure S) := by
  rw [GBCA.specFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hl, hr, hf, rfl⟩))

/-- Corruption is broadcast to every instance. -/
theorem specFamilyS_fail (P : Params) (S : ℕ → GBCA.SpecState P.n) (k : Fin P.n) :
    (GBCA.specFamily P).step S (.fail k)
      (PMF.pure (fun r => (S r).corrupt P k)) := by
  rw [GBCA.specFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl, trivial, rfl⟩))

/-- **The owned rows agree**: a label the round-indexed family of the deployed
alphabet owns is, pulled back to the specification's own alphabet, a label the
round-indexed family of specification instances owns — and the two rounds are
the same. -/
theorem specFamilyS_of_specSide (P : Params) {G : ℕ → GBCA.SpecState P.n}
    {L : NLab P.n} {r : ℕ} {l₀ : Lab P.n} (hown : GSub.gOwns L = some r)
    (hτ : L ≠ Silent.τ) (hpull : GSub.gPull P.n L = some l₀)
    (hl₀ : Lab.gbcaRound l₀ = some r) {μ : PMF (ℕ → GBCA.SpecState P.n)}
    (h : (specSide P).step G L μ) :
    ∃ G', (GBCA.specFamily P).step G l₀ (PMF.pure G') ∧ μ = PMF.pure G' := by
  obtain ⟨X, hstep, rfl⟩ := specSide_owned_inv P hown hτ h
  rw [GSub.liftedSpecG, System.mapIdle_step_some hpull] at hstep
  exact ⟨Function.update G r X, specFamilyS_owned P G r hl₀ hstep, rfl⟩

/-! #### The three factors together -/

/-- A visible joint step of the three hybrid factors. -/
theorem hybridSpecPre_lab (P : Params) {S S' : ℕ → GBCA.SpecState P.n}
    {C C' : CoreState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} {l : Lab P.n} (hl : l ≠ Lab.tau)
    (hI : (GBCA.specFamily P).step S l (PMF.pure S'))
    (hC : CoreStep P C l (PMF.pure C'))
    (hW : (WCC.specFamily P).step o l ω) :
    (hybridSpecPre P).step (S, C, o) l
      (prodPMF (PMF.pure S') (prodPMF (PMF.pure C') ω)) := by
  rw [hybridSpecPre, System.parallel_step]
  refine Or.inl ⟨hl, _, _, hI, ?_, rfl⟩
  rw [context, System.parallel_step]
  exact Or.inl ⟨hl, _, _, hC, hW, rfl⟩

/-- A silent step of the instance family alone. -/
theorem hybridSpecPre_tau_spec (P : Params) {S S' : ℕ → GBCA.SpecState P.n}
    {C : CoreState P.n} {o : ℕ → WCC.SpecState P.n}
    (hI : (GBCA.specFamily P).step S Lab.tau (PMF.pure S')) :
    (hybridSpecPre P).step (S, C, o) Lab.tau (PMF.pure (S', C, o)) := by
  rw [hybridSpecPre, System.parallel_step]
  exact Or.inr (Or.inl ⟨rfl, PMF.pure S', hI, (prodPMF_pure_pure _ _).symm⟩)

/-- A silent step of the round loop alone. -/
theorem hybridSpecPre_tau_core (P : Params) {S : ℕ → GBCA.SpecState P.n}
    {C C' : CoreState P.n} {o : ℕ → WCC.SpecState P.n}
    (hC : CoreStep P C Lab.tau (PMF.pure C')) :
    (hybridSpecPre P).step (S, C, o) Lab.tau (PMF.pure (S, C', o)) := by
  rw [hybridSpecPre, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure C') (PMF.pure o), ?_, ?_⟩)
  · rw [context, System.parallel_step]
    exact Or.inr (Or.inl ⟨rfl, PMF.pure C', hC, rfl⟩)
  · rw [prodPMF_pure_pure, prodPMF_pure_pure]

/-- The coin resolution, the one non-Dirac row. -/
theorem hybridSpecPre_tau_wcc (P : Params) {S : ℕ → GBCA.SpecState P.n}
    {C : CoreState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)}
    (hW : (WCC.specFamily P).step o Lab.tau ω) :
    (hybridSpecPre P).step (S, C, o) Lab.tau
      (prodPMF (PMF.pure S) (prodPMF (PMF.pure C) ω)) := by
  rw [hybridSpecPre, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure C) ω, ?_, rfl⟩)
  rw [context, System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, ω, hW, rfl⟩)

/-! #### Through the outer hiding -/

theorem hybridSpecS_of_tau (P : Params)
    {x : (ℕ → GBCA.SpecState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n))}
    {μ : PMF ((ℕ → GBCA.SpecState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (hybridSpecPre P).step x Lab.tau μ) :
    (hybridSpec P).step x Lab.tau μ := by
  rw [hybridSpec_eqS, System.abstract_step]
  exact Or.inr ⟨by simp, h⟩

theorem hybridSpecS_of_hidden (P : Params)
    {x : (ℕ → GBCA.SpecState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n))}
    {l : Lab P.n} (hl : l ∈ Lab.hiddenAPI P.n)
    {μ : PMF ((ℕ → GBCA.SpecState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (hybridSpecPre P).step x l μ) : (hybridSpec P).step x Lab.tau μ := by
  rw [hybridSpec_eqS, System.abstract_step]
  exact Or.inl ⟨rfl, l, hl, h⟩

/-! ### Reading a deployment-shaped transition into its four factors -/

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

/-! ### The hidden rendezvous, forwards

Each rendezvous of the deployment-shaped specification is a silent transition
of the hybrid: either one of its components' own silent rules, or — for the
Byzantine handshake drives, the call against an already-called instance and
the fused coin return — a genuine hybrid handshake that the outer hiding sends
to `τ`. The fused coin return is the case that forces the matching to be taken
at the fully hidden level: the deployed reading splits the round advance into
a rendezvous (`retWPub`, an auxiliary label) and the hybrid rejoins it into
the visible `retW`, so the two labels agree only after `Lab.hiddenAPI` has
sent both to `τ`. -/

theorem hybridSpecS_of_netEvt (P : Params) {G : ℕ → GBCA.SpecState P.n}
    {C : ∀ _ : Fin P.n, CoreNodeN P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} (e : NetEvt P.n) {μ : PMF (LayeredSpecState P)}
    (h : (layeredSpecPre P).step (G, C, A, o) (Sum.inr e) μ) :
    (hybridSpec P).step (layeredSpecDefl P (G, C, A, o)) Lab.tau
      (μ.map (layeredSpecDefl P)) := by
  obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ := layeredSpecPre_vis_inv P (by simp) h
  rw [map_layeredSpecDefl_prod, layeredSpecDefl_apply]
  cases e with
  | gsnd r j m => exact (aStep_gsnd_dead hA).elim
  | gdlv r i j m => exact (aStep_gdlv_dead hA).elim
  | dsnd j b =>
    obtain rfl : G' = G := pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)
    obtain ⟨hcnt, hx0⟩ := stepC_dsnd_self (hall j)
    obtain rfl : C' = C := coresN_id fun i => by
      by_cases hi : i = j
      · subst hi; exact hx0
      · exact stepC_dsnd_foreign (Ne.symm hi) (hall i)
    obtain ⟨hpool, hA'⟩ := aStep_dsnd hA
    obtain rfl : A' = A.dput j b := pureN_inj hA'
    obtain rfl : ω = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_dsnd j b) ω).mp hW
    rw [prodPMF_pure_pure, prodPMF_pure_pure, deflCore_dput]
    exact hybridSpecS_of_tau P (hybridSpecPre_tau_core P
      (CoreStep.echo _ j b hcnt hpool))
  | ddlv i j b =>
    obtain rfl : G' = G := pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)
    obtain ⟨hnr, hx0⟩ := stepC_ddlv_self (hall i)
    obtain rfl : C' = Function.update C i ((C i).recvDec j b) :=
      coresN_update hx0 (fun k hk => stepC_ddlv_foreign (Ne.symm hk) (hall k))
    obtain ⟨hmem, hA'⟩ := aStep_ddlv hA
    obtain rfl : A' = A := pureN_inj hA'
    obtain rfl : ω = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_ddlv i j b) ω).mp hW
    rw [prodPMF_pure_pure, prodPMF_pure_pure, deflCore_recvDec]
    exact hybridSpecS_of_tau P (hybridSpecPre_tau_core P
      (CoreStep.deliver _ i j b hmem hnr))
  | retWPub r id c b =>
    obtain rfl : G' = G := pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)
    obtain ⟨hph, hr, hg, hx0⟩ := stepC_retWPub_self (hall id)
    obtain rfl : C' = Function.update C id ((C id).stepRound c) :=
      coresN_update hx0 (fun k hk => stepC_retWPub_foreign (Ne.symm hk) (hall k))
    obtain rfl : A' = A.dput id b := pureN_inj (aStep_retWPub hA)
    have hWs := (System.mapIdle_step_some (wccPull_retWPub r id c b) ω).mp hW
    rw [deflCore_stepRound_pub C A id c b hg]
    exact hybridSpecS_of_hidden P (Lab.retW_mem_hiddenAPI r id c)
      (hybridSpecPre_lab P (by simp) (specFamilyS_idle P _ (by simp) rfl not_false)
        (CoreStep.retW _ r id c hph hr) hWs)
  | gcallLoop r id b =>
    obtain ⟨G₂, hspec, hGeq⟩ := specFamilyS_of_specSide P rfl (by simp) rfl rfl hG
    obtain rfl : G' = G₂ := pureN_inj hGeq
    obtain ⟨hph, hr, hest, hx0⟩ := stepC_gcallLoop_self (hall id)
    obtain rfl : C' = Function.update C id ((C id).setProc
        { (C id).proc with phase := .awaitG }) :=
      coresN_update hx0 (fun k hk => stepC_gcallLoop_foreign (Ne.symm hk) (hall k))
    obtain rfl : A' = A := pureN_inj (aStep_gcallLoop hA)
    obtain rfl : ω = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_gcallLoop r id b) ω).mp hW
    rw [deflCore_setProc]
    exact hybridSpecS_of_hidden P (Lab.callG_mem_hiddenAPI r id b)
      (hybridSpecPre_lab P (by simp) hspec (CoreStep.callG _ r id b hph hr hest)
        (wccFamilyN_idle P o (by simp) rfl not_false))
  | byzCallG r k b =>
    obtain ⟨G₂, hspec, hGeq⟩ := specFamilyS_of_specSide P rfl (by simp) rfl rfl hG
    obtain rfl : G' = G₂ := pureN_inj hGeq
    obtain rfl : C' = C := coresN_id fun i => stepC_byzCallG (hall i)
    obtain ⟨hF, hA'⟩ := aStep_byzCallG hA
    obtain rfl : A' = A := pureN_inj hA'
    obtain rfl : ω = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_byzCallG r k b) ω).mp hW
    exact hybridSpecS_of_hidden P (Lab.callG_mem_hiddenAPI r k b)
      (hybridSpecPre_lab P (by simp) hspec (CoreStep.callGByz _ r k b hF)
        (wccFamilyN_idle P o (by simp) rfl not_false))
  | byzCallGLoop r k b =>
    obtain ⟨G₂, hspec, hGeq⟩ := specFamilyS_of_specSide P rfl (by simp) rfl rfl hG
    obtain rfl : G' = G₂ := pureN_inj hGeq
    obtain rfl : C' = C := coresN_id fun i => stepC_byzCallGLoop (hall i)
    obtain ⟨hF, hA'⟩ := aStep_byzCallGLoop hA
    obtain rfl : A' = A := pureN_inj hA'
    obtain rfl : ω = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_byzCallGLoop r k b) ω).mp hW
    exact hybridSpecS_of_hidden P (Lab.callG_mem_hiddenAPI r k b)
      (hybridSpecPre_lab P (by simp) hspec (CoreStep.callGByz _ r k b hF)
        (wccFamilyN_idle P o (by simp) rfl not_false))
  | byzRetG r k out =>
    obtain ⟨G₂, hspec, hGeq⟩ := specFamilyS_of_specSide P rfl (by simp) rfl rfl hG
    obtain rfl : G' = G₂ := pureN_inj hGeq
    obtain rfl : C' = C := coresN_id fun i => stepC_byzRetG (hall i)
    obtain ⟨hF, hA'⟩ := aStep_byzRetG hA
    obtain rfl : A' = A := pureN_inj hA'
    obtain rfl : ω = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_byzRetG r k out) ω).mp hW
    exact hybridSpecS_of_hidden P (Lab.retG_mem_hiddenAPI r k out)
      (hybridSpecPre_lab P (by simp) hspec (CoreStep.retGByz _ r k out hF)
        (wccFamilyN_idle P o (by simp) rfl not_false))
  | byzCallW r k =>
    obtain rfl : G' = G := pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)
    obtain rfl : C' = C := coresN_id fun i => stepC_byzCallW (hall i)
    obtain ⟨hF, hA'⟩ := aStep_byzCallW hA
    obtain rfl : A' = A := pureN_inj hA'
    have hWs := (System.mapIdle_step_some (wccPull_byzCallW r k) ω).mp hW
    exact hybridSpecS_of_hidden P (Lab.callW_mem_hiddenAPI r k)
      (hybridSpecPre_lab P (by simp) (specFamilyS_idle P _ (by simp) rfl not_false)
        (CoreStep.callWByz _ r k hF) hWs)
  | byzRetW r k b =>
    obtain rfl : G' = G := pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)
    obtain rfl : C' = C := coresN_id fun i => stepC_byzRetW (hall i)
    obtain ⟨hF, hA'⟩ := aStep_byzRetW hA
    obtain rfl : A' = A := pureN_inj hA'
    have hWs := (System.mapIdle_step_some (wccPull_byzRetW r k b) ω).mp hW
    exact hybridSpecS_of_hidden P (Lab.retW_mem_hiddenAPI r k b)
      (hybridSpecPre_lab P (by simp) (specFamilyS_idle P _ (by simp) rfl not_false)
        (CoreStep.retWByz _ r k b hF) hWs)


/-! ### The shared labels, forwards

A label of the shared alphabet is answered by the hybrid on the same label:
the surviving ABA API and `fail` visibly, the sub-protocol API under the outer
hiding, and `τ` by the specification family's binding kill, the ABA-side
network's own injection, or the coin resolution. -/

theorem hybridSpecPre_of_layeredSpecPre (P : Params) {G : ℕ → GBCA.SpecState P.n}
    {C : ∀ _ : Fin P.n, CoreNodeN P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {l : Lab P.n} {μ : PMF (LayeredSpecState P)}
    (h : (layeredSpecPre P).step (G, C, A, o) (Sum.inl l) μ) :
    (hybridSpecPre P).step (layeredSpecDefl P (G, C, A, o)) l (μ.map (layeredSpecDefl P)) := by
  rw [layeredSpecDefl_apply]
  by_cases hl : l = Lab.tau
  · subst hl
    rcases layeredSpecPre_tau_inv P h with ⟨G', hspec, rfl⟩ | ⟨A', hnet, rfl⟩ | ⟨ω, hW, rfl⟩
    · rw [PMF.pure_map, layeredSpecDefl_apply]
      obtain ⟨r, X, hstep, hGeq⟩ := specSide_tau_inv P hspec
      obtain rfl : G' = Function.update G r X := pureN_inj hGeq
      rw [GSub.liftedSpecG, System.mapIdle_step_some (GSub.gPull_inl (Lab.tau : Lab P.n))]
        at hstep
      exact hybridSpecPre_tau_spec P (specFamilyS_tau P G r hstep)
    · rw [PMF.pure_map, layeredSpecDefl_apply]
      obtain ⟨k, b, hF, hA'⟩ := aStep_tau hnet
      obtain rfl : A' = A.dput k b := pureN_inj hA'
      rw [deflCore_dput]
      exact hybridSpecPre_tau_core P (CoreStep.byzDecided _ k b hF)
    · rw [map_layeredSpecDefl_prod]
      exact hybridSpecPre_tau_wcc P hW
  · obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
      layeredSpecPre_vis_inv P (by simpa using hl) h
    rw [map_layeredSpecDefl_prod]
    have hWs := (System.mapIdle_step_some (wccPull_inl l) ω).mp hW
    cases l with
    | tau => exact absurd rfl hl
    | callABA id b =>
      obtain rfl : G' = G := pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)
      obtain rfl : A' = A := pureN_inj (aStep_callABA hA)
      rcases stepC_callABA_own (hall id) with ⟨hin, hx0⟩ | hx0
      · have hx := coresN_update hx0
          (fun i hi => stepC_callABA_foreign (Ne.symm hi) (hall i))
        subst hx
        rw [deflCore_setProc]
        exact hybridSpecPre_lab P (by simp)
          (specFamilyS_idle P _ (by simp) rfl not_false)
          (CoreStep.input _ id b hin) hWs
      · have hx : C' = C := coresN_id fun i => by
          by_cases hi : i = id
          · subst hi; exact hx0
          · exact stepC_callABA_foreign (Ne.symm hi) (hall i)
        subst hx
        exact hybridSpecPre_lab P (by simp)
          (specFamilyS_idle P _ (by simp) rfl not_false)
          (CoreStep.inputLoop _ id b) hWs
    | retABA id b =>
      obtain rfl : G' = G := pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)
      obtain ⟨hpool, hA'⟩ := aStep_retABA hA
      obtain rfl : A' = A := pureN_inj hA'
      obtain ⟨hcnt, hret, hx0⟩ := stepC_retABA_own (hall id)
      have hx := coresN_update hx0
        (fun i hi => stepC_retABA_foreign (Ne.symm hi) (hall i))
      subst hx
      rw [deflCore_setProc]
      exact hybridSpecPre_lab P (by simp)
        (specFamilyS_idle P _ (by simp) rfl not_false)
        (CoreStep.ret _ id b hcnt hpool hret) hWs
    | callG r id b =>
      obtain ⟨G₂, hspec, hGeq⟩ := specFamilyS_of_specSide P rfl (by simp) rfl rfl hG
      obtain rfl : G' = G₂ := pureN_inj hGeq
      obtain rfl : A' = A := pureN_inj (aStep_callG hA)
      obtain ⟨hph, hr, hest, hx0⟩ := stepC_callG_own (hall id)
      have hx := coresN_update hx0
        (fun i hi => stepC_callG_foreign (Ne.symm hi) (hall i))
      subst hx
      rw [deflCore_setProc]
      exact hybridSpecPre_lab P (by simp) hspec
        (CoreStep.callG _ r id b hph hr hest) hWs
    | retG r id out =>
      obtain ⟨G₂, hspec, hGeq⟩ := specFamilyS_of_specSide P rfl (by simp) rfl rfl hG
      obtain rfl : G' = G₂ := pureN_inj hGeq
      obtain rfl : A' = A := pureN_inj (aStep_retG hA)
      obtain ⟨hph, hr, hx0⟩ := stepC_retG_own (hall id)
      have hx := coresN_update hx0
        (fun i hi => stepC_retG_foreign (Ne.symm hi) (hall i))
      subst hx
      rw [deflCore_setProc]
      exact hybridSpecPre_lab P (by simp) hspec
        (CoreStep.retG _ r id out hph hr) hWs
    | callW r id =>
      obtain rfl : G' = G := pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)
      obtain rfl : A' = A := pureN_inj (aStep_callW hA)
      obtain ⟨hph, hr, hx0⟩ := stepC_callW_own (hall id)
      have hx := coresN_update hx0
        (fun i hi => stepC_callW_foreign (Ne.symm hi) (hall i))
      subst hx
      rw [deflCore_setProc]
      exact hybridSpecPre_lab P (by simp)
        (specFamilyS_idle P _ (by simp) rfl not_false)
        (CoreStep.callW _ r id hph hr) hWs
    | retW r id c =>
      obtain rfl : G' = G := pureN_inj (specSide_idle_inv P hG (by simp) rfl not_false)
      obtain rfl : A' = A := pureN_inj (aStep_retW hA)
      obtain ⟨hph, hr, hgr, hx0⟩ := stepC_retW_own (hall id)
      have hx := coresN_update hx0
        (fun i hi => stepC_retW_foreign (Ne.symm hi) (hall i))
      subst hx
      rw [deflCore_stepRound_plain _ _ id c hgr]
      exact hybridSpecPre_lab P (by simp)
        (specFamilyS_idle P _ (by simp) rfl not_false)
        (CoreStep.retW _ r id c hph hr) hWs
    | fail k =>
      obtain rfl : G' = fun r => (G r).corrupt P k :=
        pureN_inj (specSide_fail_inv P k hG)
      obtain rfl : A' = ANetState.corrupt P k A := pureN_inj (aStep_fail hA)
      have hx : C' = C := coresN_id fun i => stepC_fail (hall i)
      subst hx
      rw [deflCore_corrupt]
      exact hybridSpecPre_lab P (by simp) (specFamilyS_fail P G k)
        (CoreStep.fail _ k) hWs

/-! ### The deflation simulation and the inclusion

The deflation is a step-commuting state map: every transition of the
deployment-shaped specification is the hybrid's transition on the same label,
its successor distribution pushed forward. That is exactly the hypothesis of
`ProbabilisticForwardSimulation.ofStrongFunctional`, and soundness (Result 1)
turns the resulting simulation into the trace-distribution inclusion. -/

/-- **The forward matching**: every transition of the deployment-shaped
specification is the matching transition of the hybrid along the deflation. -/
theorem layeredSpecForward (P : Params) :
    ∀ s l μ, (layeredSpec P).step s l μ →
      (hybridSpec P).step (layeredSpecDefl P s) l (μ.map (layeredSpecDefl P)) := by
  rintro ⟨G, C, A, o⟩ l μ h
  rw [layeredSpec_step_iff] at h
  rcases h with ⟨rfl, l', hl', hg⟩ | ⟨hn, hg⟩
  · rw [layeredSpecGroup_step_iff] at hg
    rcases hg with ⟨rfl, e, hpre⟩ | hpre
    · exact absurd hl' (by simp)
    · exact hybridSpecS_of_hidden P hl' (hybridSpecPre_of_layeredSpecPre P hpre)
  · rw [layeredSpecGroup_step_iff] at hg
    rcases hg with ⟨rfl, e, hpre⟩ | hpre
    · exact hybridSpecS_of_netEvt P e hpre
    · rw [hybridSpec_eqS, System.abstract_step]
      exact Or.inr ⟨hn, hybridSpecPre_of_layeredSpecPre P hpre⟩

/-- **The deployment-shaped specification simulates into the hybrid** along
the graph of the deflation. -/
noncomputable def layeredSpecSim (P : Params) :
    ProbabilisticForwardSimulation (layeredSpec P) (hybridSpec P)
      (fun s ν => ν = PMF.pure (layeredSpecDefl P s)) :=
  ProbabilisticForwardSimulation.ofStrongFunctional (layeredSpecDefl P)
    (layeredSpecDefl_init P) (layeredSpecForward P)

/-- **The deflation inclusion**: every trace distribution achievable by the
deployment-shaped specification is achievable by the specification-side
hybrid. -/
theorem layeredSpec_refines (P : Params) :
    achievableTraceDists (layeredSpec P) ⊆ achievableTraceDists (hybridSpec P) :=
  (layeredSpecSim P).achievableTraceDists_subset

end ABA

end PLTS
