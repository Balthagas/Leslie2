/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Components
import Leslie2Protocols.ABA.GBCAInstances
import Leslie2.Results

/-!
# The specification stages: the composed reading and the substitution

Two links of the refinement chain, and the row-by-row readings of the systems
they introduce. The headlines that chain these links with the earlier ones are
in `ABA/Results.lean`.

The first link is the composed reading. The protocol reading of
`ABA/Protocol.lean` presents the protocol as `n` corruption-blind programs
beside one network adversary and the coin oracle; each program runs its round
loop and a graded-agreement stage at once, and the single adversary holds both
kinds of message pool. The composed reading reads the same protocol as a
composition of components:

* the graded-agreement side is the round-indexed family `GSub.gbcaSide`. Its
  round-`r` factor is a parallel component in its own right: the stage
  programs of round `r` beside the message fabric of round `r`, which that
  component owns outright;
* the round loops are `n` separate automata (`coreProcN`), synchronised;
* what is left of the network adversary is the DECIDED pools beside the
  corrupted set (`aNet`);
* the coin oracle enters through the same label pullback as in the protocol
  reading (`Net.wccLift`).

The four factors speak the extended alphabet `Net.NLab n`, the rendezvous
labels are hidden, and the result is read back over `Lab n`. The round loops,
the ABA-side network and the lifted oracle are defined in `ABA/Components.lean`,
the round subsystems in `ABA/GBCAInstances.lean`; the composition pipeline
`composedPre` / `composedGroup` / `composed` is the first section below.

The second link is the substitution, which replaces each round's
graded-agreement subsystem by that round's specification. `hybrid` is the
system that results, read at the protocol shape. The substitution is one
application of `ProbabilisticForwardSimulation.parallel_right` under a
syntactically identical context, followed by the three congruences the protocol
pipeline is built from: `abstract` for the rendezvous alphabet, `relabel` for
the read-back to `Lab n` (`Framework/Relabel.lean`), and `abstract` again for
the sub-protocol API. The conclusion is `substitution`, the inclusion of the
composed system's achievable trace distributions in the specification's.

## Per-round memory

A round subsystem is a factor of the composite from the start, not an object
created by the round's first call, and it keeps its stage records and its
fabric for the whole run. The graded-agreement coordinate of a composed state
is therefore `ℕ → GBCA.ImplState n`: every round is present at every moment,
whichever round each process is in. That retained memory is specification-side
state. No process holds it. A protocol node carries the stage record of the
round its round loop is in and nothing else (D20).

## The authorisation relocation (D11)

A round subsystem carries no `k ∈ F` guard on the drive labels `byzCallG`,
`byzCallGLoop` and `byzRetG` (`GBCAInstances.lean`, D11). A drive label stays
visible at the subsystem boundary and is authorised outside it. Here `aNet` is
that outside, and it carries the guard on its own copy of the corrupted set.
The two copies are written by one broadcast: `fail` reaches every round's
fabric through the family (`gbcaSide_fail`) and `aNet` on its own `fail` row,
and `GSub.GNetState.corrupt` and `ANetState.corrupt` are the same
budget-guarded insertion.

## What this file supplies

The composed system and its rows, the protocol-shaped specification and its
rows, and the substitution between them. The builders assemble a transition of
a composite out of transitions of its factors (`composedPre_vis_step`,
`composedPre_tau_gbca`, `composedPre_tau_aNet`, `composedPre_tau_wcc`,
`gbcaSide_owned`, `gbcaSide_idle`, `gbcaSide_tau`, `gbcaSide_fail`,
`composedGroup_of_event`, `composedGroup_of_tau`, and their counterparts on the
specification side). On the specification side the reading also runs in the
inverse direction, from a composite transition back into the rows its factors
contributed, and a labelled transition takes one of three routes through the
two hiding frames. The per-factor rows these consume and produce are the tables
of `ABA/Components.lean` and `ABA/GBCAInstances.lean`.

The core simulation of `ABA/CoreSim.lean` runs from `hybrid` on this
vocabulary, and the non-vacuity witnesses of `ABA/NonVacuity.lean` are built
with it; `ABA/Results.lean` chains the simulation with the substitution and,
through `safety_transfer`, reads off the protocol's Validity and
Agreement guarantee.
-/

namespace PLTS
namespace ABA

open Net

/-! ## The composed reading

The protocol cut into its components: the graded-agreement side as a
round-indexed family of subsystems, the round loops as `n` synchronised
automata, the DECIDED pools beside the corrupted set, and the lifted coin
oracle. This section
composes the four factors and reads the rows of the composite. -/

namespace Comp

/-! ### The composition pipeline -/

/-- The state of the composed system: the round subsystems, the round loops,
the ABA-side network and the coin oracle. -/
abbrev ComposedState (P : Params) : Type :=
  (ℕ → GBCA.ImplState P.n) ×
    ((∀ _ : Fin P.n, CoreRec P.n) × (ANetState P.n × (ℕ → WCC.SpecState P.n)))

end Comp

/-- The four factors side by side, over the extended alphabet. -/
noncomputable def composedPre (P : Params) : System (Comp.ComposedState P) (NLab P.n) :=
  (GSub.gbcaSide P).parallel
    ((System.syncProduct (Comp.coreProcN P)).parallel
      ((Comp.aNet P).parallel (wccLift P)))

/-- **The composed group**: the rendezvous alphabet hidden, the result read
back over `Lab n`. -/
noncomputable def composedGroup (P : Params) :
    System (Comp.ComposedState P) (Lab P.n) :=
  ((composedPre P).abstract (netEvtLabels P.n)).relabel

/-- **The composed system**: the group with the sub-protocol API hidden. -/
noncomputable def composed (P : Params) : System (Comp.ComposedState P) (Lab P.n) :=
  (composedGroup P).abstract (Lab.hiddenAPI P.n)

namespace Comp

/-! ### Reading and building composite transitions of the composed system -/

/-- The composed group's step relation, unfolded to the hidden rendezvous case
and the shared-label case. -/
theorem composedGroup_step_iff (P : Params) (q : ComposedState P) (l : Lab P.n)
    (μ : PMF (ComposedState P)) :
    (composedGroup P).step q l μ ↔
      (l = .tau ∧ ∃ e : NetEvt P.n, (composedPre P).step q (Sum.inr e) μ) ∨
      (composedPre P).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_netEvtLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_netEvtLabels l, hstep⟩

/-- Build a joint transition of the four factors on a visible label, the
oracle's successor left arbitrary. -/
theorem composedPre_vis_step (P : Params) {G G' : ℕ → GBCA.ImplState P.n}
    {C C' : ∀ _ : Fin P.n, CoreRec P.n} {A A' : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {ω : PMF (ℕ → WCC.SpecState P.n)} {L : NLab P.n}
    (hL : L ≠ Silent.τ)
    (hG : (GSub.gbcaSide P).step G L (PMF.pure G'))
    (hC : ∀ i, CoreProcStepN P i (C i) L (PMF.pure (C' i)))
    (hA : ANetStep P A L (PMF.pure A'))
    (hW : (wccLift P).step o L ω) :
    (composedPre P).step (G, C, A, o) L
      (prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω))) := by
  rw [composedPre, System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure G', prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω),
    hG, ?_, rfl⟩
  rw [System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure C', prodPMF (PMF.pure A') ω, syncCore_pure hL hC, ?_, rfl⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure A', ω, hA, hW, rfl⟩

/-- Build a silent transition of the four factors from a graded-agreement-side
one. -/
theorem composedPre_tau_gbca (P : Params) {G G' : ℕ → GBCA.ImplState P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hG : (GSub.gbcaSide P).step G (Sum.inl Lab.tau) (PMF.pure G')) :
    (composedPre P).step (G, C, A, o) (Sum.inl Lab.tau) (PMF.pure (G', C, A, o)) := by
  rw [composedPre, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure G', hG, ?_⟩)
  rw [prodPMF_pure_pure]

/-- Build a silent transition of the four factors from an ABA-side network
injection. -/
theorem composedPre_tau_aNet (P : Params) {G : ℕ → GBCA.ImplState P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A A' : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hA : ANetStep P A (Sum.inl Lab.tau) (PMF.pure A')) :
    (composedPre P).step (G, C, A, o) (Sum.inl Lab.tau) (PMF.pure (G, C, A', o)) := by
  rw [composedPre, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl,
    prodPMF (PMF.pure C) (prodPMF (PMF.pure A') (PMF.pure o)), ?_, ?_⟩)
  · rw [System.parallel_step]
    refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure A') (PMF.pure o), ?_, rfl⟩)
    rw [System.parallel_step]
    exact Or.inr (Or.inl ⟨rfl, PMF.pure A', hA, rfl⟩)
  · rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure]

/-- Build a silent transition of the four factors from the coin resolution —
the one transition of the composite that is not Dirac. -/
theorem composedPre_tau_wcc (P : Params) {G : ℕ → GBCA.ImplState P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {ω : PMF (ℕ → WCC.SpecState P.n)}
    (hW : (WCC.specFamily P).step o Lab.tau ω) :
    (composedPre P).step (G, C, A, o) (Sum.inl Lab.tau)
      (prodPMF (PMF.pure G) (prodPMF (PMF.pure C) (prodPMF (PMF.pure A) ω))) := by
  rw [composedPre, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, _, ?_, rfl⟩)
  rw [System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure A) ω, ?_, rfl⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, ω, (System.mapIdle_step_some (by simp) ω).mpr hW, rfl⟩)

/-! ### The graded-agreement side's rows

The family routes a round-tagged label to its round, takes `τ` at any round,
broadcasts `fail`, and idles on everything else. -/

/-- The round-`r` subsystem moves on a label it owns. -/
theorem gbcaSide_owned (P : Params) (G : ℕ → GBCA.ImplState P.n) (r : ℕ)
    {L : NLab P.n} (hL : GSub.gOwns L = some r) {X : GBCA.ImplState P.n}
    (h : (GSub.sub P r).step (G r) L (PMF.pure X)) :
    (GSub.gbcaSide P).step G L (PMF.pure (Function.update G r X)) := by
  rw [GSub.gbcaSide, System.family_step_iff]
  exact Or.inr (Or.inl ⟨r, hL, PMF.pure X, h, by rw [PMF.pure_map]⟩)

/-- An owned label whose subsystem stands still. -/
theorem gbcaSide_owned_id (P : Params) (G : ℕ → GBCA.ImplState P.n) (r : ℕ)
    {L : NLab P.n} (hL : GSub.gOwns L = some r)
    (h : (GSub.sub P r).step (G r) L (PMF.pure (G r))) :
    (GSub.gbcaSide P).step G L (PMF.pure G) := by
  have hstep := gbcaSide_owned P G r hL h
  rwa [Function.update_eq_self] at hstep

/-- The round-`r` subsystem takes one of its own silent rules. -/
theorem gbcaSide_tau (P : Params) (G : ℕ → GBCA.ImplState P.n) (r : ℕ)
    {X : GBCA.ImplState P.n}
    (h : (GSub.sub P r).step (G r) (Sum.inl Lab.tau) (PMF.pure X)) :
    (GSub.gbcaSide P).step G (Sum.inl Lab.tau) (PMF.pure (Function.update G r X)) := by
  rw [GSub.gbcaSide, System.family_step_iff]
  exact Or.inl ⟨rfl, r, PMF.pure X, h, by rw [PMF.pure_map]⟩

/-- A label no round owns and no broadcast: the family idles. -/
theorem gbcaSide_idle (P : Params) (G : ℕ → GBCA.ImplState P.n) {L : NLab P.n}
    (hτ : L ≠ Silent.τ) (hown : GSub.gOwns L = none) (hf : ¬ GSub.isFailN L) :
    (GSub.gbcaSide P).step G L (PMF.pure G) := by
  rw [GSub.gbcaSide, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hτ, hown, hf, rfl⟩))

/-- Corruption is broadcast to every round's fabric. -/
theorem gbcaSide_fail (P : Params) (G : ℕ → GBCA.ImplState P.n) (k : Fin P.n) :
    (GSub.gbcaSide P).step G (Sum.inl (Lab.fail k))
      (PMF.pure (fun r => GSub.gAct P (Sum.inl (Lab.fail k)) (G r))) := by
  rw [GSub.gbcaSide, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl, trivial, rfl⟩))

/-! ### The stage-program tuple of one round -/

/-- One stage program moves and every other idles. -/
theorem gprocs_family {P : Params} {r : ℕ}
    {u : ∀ _ : Fin P.n, GBCA.StageRec P.n} {L : GSub.GLab P.n} (id : Fin P.n)
    (nd : GBCA.StageRec P.n)
    (hown : GSub.GProcStep P r id (u id) L (PMF.pure nd))
    (hfor : ∀ i, i ≠ id → GSub.GProcStep P r i (u i) L (PMF.pure (u i))) :
    ∀ i, GSub.GProcStep P r i (u i) L (PMF.pure (Function.update u id nd i)) := by
  intro i
  by_cases hi : i = id
  · subst hi; rw [Function.update_self]; exact hown
  · rw [Function.update_of_ne hi]; exact hfor i hi

/-! ### Hiding the rendezvous alphabet

The composition hides `NetEvt n`, so a transition of `composedPre` on a
rendezvous label is a silent transition of `composedGroup`, as is one on `τ`.
The two stage rendezvous never reach this point. They are internal to a round
subsystem, hidden inside `GSub.sub`, and reach the composite as the family's
own `τ`. -/

theorem composedGroup_of_event (P : Params) {q : ComposedState P} (e : NetEvt P.n)
    {μ : PMF (ComposedState P)} (h : (composedPre P).step q (Sum.inr e) μ) :
    (composedGroup P).step q Lab.tau μ :=
  (composedGroup_step_iff P _ _ _).mpr (Or.inl ⟨rfl, e, h⟩)

theorem composedGroup_of_tau (P : Params) {q : ComposedState P} {μ : PMF (ComposedState P)}
    (h : (composedPre P).step q (Sum.inl Lab.tau) μ) :
    (composedGroup P).step q Lab.tau μ :=
  (composedGroup_step_iff P _ _ _).mpr (Or.inr h)

end Comp

open Comp

/-! ## The protocol-shaped specification side

The composed system replaces its graded-agreement factor `GSub.gbcaSide` — the
family of round subsystems — by `specSide`, the family of round specifications
read over the protocol alphabet. The other three factors are reused verbatim,
so the substitution is `ProbabilisticForwardSimulation.parallel_right` applied
under the syntactically identical context, followed by the three remaining
congruences: `abstract` for the rendezvous alphabet, `relabel` for the read-back
to `Lab n`, and `abstract` again for the sub-protocol API. -/

/-- **The specification side of the protocol**: the ℕ-indexed family
of round specifications, read over the protocol extended alphabet along
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

/-- The state of the protocol-shaped specification: the round
specifications beside the composed system's other three factors. -/
abbrev HybridState (P : Params) : Type :=
  (ℕ → GBCA.SpecState P.n) ×
    ((∀ _ : Fin P.n, CoreRec P.n) × (ANetState P.n × (ℕ → WCC.SpecState P.n)))

/-- The four factors side by side, over the extended alphabet: `composedPre`
with its graded-agreement factor replaced. -/
noncomputable def hybridPre (P : Params) : System (HybridState P) (NLab P.n) :=
  (specSide P).parallel
    ((System.syncProduct (coreProcN P)).parallel ((aNet P).parallel (wccLift P)))

/-- **The protocol-shaped specification**: the rendezvous alphabet hidden,
the result read back over `Lab n`, the sub-protocol API hidden — the pipeline
of `composed`, factor for factor. -/
noncomputable def hybrid (P : Params) : System (HybridState P) (Lab P.n) :=
  (((hybridPre P).abstract (netEvtLabels P.n)).relabel).abstract (Lab.hiddenAPI P.n)

/-! ### The substitution -/

/-- The pointwise round relation: every round's subsystem state is related to
that round's specification state. -/
def RsubAll (P : Params) (s : ℕ → GBCA.ImplState P.n)
    (t : ℕ → GBCA.SpecState P.n) : Prop :=
  ∀ r, GSub.Rsub P r (s r) (t r)

/-- **The family substitution**: the graded-agreement side of the protocol is forward simulated by the specification side, round by round. The
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

/-- **The substitution simulation at the protocol shape**: the four
congruences applied to the family substitution under the composed system's own
context — `parallel_right` for the three untouched factors, `abstract` for the
rendezvous alphabet, `relabel` for the read-back over `Lab n`, and `abstract`
for the sub-protocol API. -/
noncomputable def substSim (P : Params) :
    ProbabilisticForwardSimulation (composed P) (hybrid P)
      (parallelRel (diracRel (RsubAll P))) :=
  ((((famSubSimProb P).parallel_right
    ((System.syncProduct (coreProcN P)).parallel
      ((aNet P).parallel (wccLift P)))).abstract
        (netEvtLabels P.n)).relabel).abstract (Lab.hiddenAPI P.n)

/-- **The substitution inclusion**: every trace distribution achievable by the
composed system is achievable by the protocol-shaped
specification. -/
theorem substitution (P : Params) :
    achievableTraceDists (composed P) ⊆ achievableTraceDists (hybrid P) :=
  (substSim P).achievableTraceDists_subset

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

/-! ### Reading a protocol-shaped transition into its four factors -/

/-- Build a joint transition of the four factors on a visible label, the
oracle's successor left arbitrary. -/
theorem hybridPre_vis_step (P : Params) {G G' : ℕ → GBCA.SpecState P.n}
    {C C' : ∀ _ : Fin P.n, CoreRec P.n} {A A' : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {ω : PMF (ℕ → WCC.SpecState P.n)} {L : NLab P.n}
    (hL : L ≠ Silent.τ)
    (hG : (specSide P).step G L (PMF.pure G'))
    (hC : ∀ i, CoreProcStepN P i (C i) L (PMF.pure (C' i)))
    (hA : ANetStep P A L (PMF.pure A'))
    (hW : (wccLift P).step o L ω) :
    (hybridPre P).step (G, C, A, o) L
      (prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω))) := by
  rw [hybridPre, System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure G', prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω),
    hG, ?_, rfl⟩
  rw [System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure C', prodPMF (PMF.pure A') ω, syncCore_pure hL hC, ?_, rfl⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure A', ω, hA, hW, rfl⟩

/-- A visible transition of the four factors: all of them move together, and
only the oracle's successor can fail to be a Dirac. -/
theorem hybridPre_vis_inv (P : Params) {G : ℕ → GBCA.SpecState P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {L : NLab P.n} (hL : L ≠ Silent.τ)
    {μ : PMF (HybridState P)} (h : (hybridPre P).step (G, C, A, o) L μ) :
    ∃ (G' : ℕ → GBCA.SpecState P.n) (C' : ∀ _ : Fin P.n, CoreRec P.n)
      (A' : ANetState P.n) (ω : PMF (ℕ → WCC.SpecState P.n)),
      (specSide P).step G L (PMF.pure G') ∧
      (∀ i, CoreProcStepN P i (C i) L (PMF.pure (C' i))) ∧
      ANetStep P A L (PMF.pure A') ∧ (wccLift P).step o L ω ∧
      μ = prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω)) := by
  rw [hybridPre, System.parallel_step] at h
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
theorem hybridPre_tau_spec (P : Params) {G G' : ℕ → GBCA.SpecState P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hG : (specSide P).step G (Sum.inl Lab.tau) (PMF.pure G')) :
    (hybridPre P).step (G, C, A, o) (Sum.inl Lab.tau) (PMF.pure (G', C, A, o)) := by
  rw [hybridPre, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure G', hG, ?_⟩)
  rw [prodPMF_pure_pure]

/-- Build a silent transition of the four factors from a coin resolution. -/
theorem hybridPre_tau_wcc (P : Params) {G : ℕ → GBCA.SpecState P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {ω : PMF (ℕ → WCC.SpecState P.n)}
    (hW : (WCC.specFamily P).step o Lab.tau ω) :
    (hybridPre P).step (G, C, A, o) (Sum.inl Lab.tau)
      (prodPMF (PMF.pure G) (prodPMF (PMF.pure C) (prodPMF (PMF.pure A) ω))) := by
  rw [hybridPre, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, _, ?_, rfl⟩)
  rw [System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, _, ?_, rfl⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, ω,
    (System.mapIdle_step_some (wccPull_inl Lab.tau) ω).mpr hW, rfl⟩)

/-- A silent transition of the four factors: no round loop has a `τ` row, so it
is the specification family's binding kill, the ABA-side network's own
injection, or the coin resolution. -/
theorem hybridPre_tau_inv (P : Params) {G : ℕ → GBCA.SpecState P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {μ : PMF (HybridState P)}
    (h : (hybridPre P).step (G, C, A, o) (Sum.inl Lab.tau) μ) :
    (∃ G', (specSide P).step G (Sum.inl Lab.tau) (PMF.pure G') ∧
        μ = PMF.pure (G', C, A, o)) ∨
    (∃ A', ANetStep P A (Sum.inl Lab.tau) (PMF.pure A') ∧
        μ = PMF.pure (G, C, A', o)) ∨
    (∃ ω, (WCC.specFamily P).step o Lab.tau ω ∧
        μ = prodPMF (PMF.pure G) (prodPMF (PMF.pure C) (prodPMF (PMF.pure A) ω))) := by
  rw [hybridPre, System.parallel_step] at h
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

/-! ### The two hiding frames -/

/-- **The protocol-shaped group**: the rendezvous alphabet hidden, the result
read back over `Lab n`. Scaffolding for the row-by-row reading below; nothing
outside this file names it. -/
private noncomputable def hybridGroup (P : Params) : System (HybridState P) (Lab P.n) :=
  ((hybridPre P).abstract (netEvtLabels P.n)).relabel

theorem hybrid_eqS (P : Params) :
    hybrid P = (hybridGroup P).abstract (Lab.hiddenAPI P.n) := rfl

/-- The group's step relation, unfolded to the hidden rendezvous case and the
shared-label case. -/
theorem hybridGroup_step_iff (P : Params) (q : HybridState P) (l : Lab P.n)
    (μ : PMF (HybridState P)) :
    (hybridGroup P).step q l μ ↔
      (l = .tau ∧ ∃ e : NetEvt P.n, (hybridPre P).step q (Sum.inr e) μ) ∨
      (hybridPre P).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_netEvtLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_netEvtLabels l, hstep⟩

/-- The protocol-shaped specification's step relation: a sub-protocol API
label seen as `τ`, or a label that survives the hiding. -/
theorem hybrid_step_iff (P : Params) (q : HybridState P) (l : Lab P.n)
    (μ : PMF (HybridState P)) :
    (hybrid P).step q l μ ↔
      (l = .tau ∧ ∃ l' ∈ Lab.hiddenAPI P.n, (hybridGroup P).step q l' μ) ∨
      (l ∉ Lab.hiddenAPI P.n ∧ (hybridGroup P).step q l μ) :=
  System.abstract_step _ _ _ _ _

/-! ### Building a transition through the two hiding frames

A transition of the four factors reaches the protocol-shaped specification
along one of three routes, according to its label: a rendezvous label and a
sub-protocol API label are both hidden to `τ`, and every remaining label
survives both hidings. -/

/-- A rendezvous transition is silent: the rendezvous alphabet is hidden. -/
theorem hybrid_rendezvous (P : Params) {q : HybridState P} {e : NetEvt P.n}
    {μ : PMF (HybridState P)} (h : (hybridPre P).step q (Sum.inr e) μ) :
    (hybrid P).step q Lab.tau μ := by
  rw [hybrid_step_iff]
  exact Or.inr ⟨by simp, (hybridGroup_step_iff P q Lab.tau μ).mpr (Or.inl ⟨rfl, e, h⟩)⟩

/-- A sub-protocol API label is silent: the API is hidden. -/
theorem hybrid_hidden (P : Params) {q : HybridState P} {l : Lab P.n}
    {μ : PMF (HybridState P)} (hl : l ∈ Lab.hiddenAPI P.n)
    (h : (hybridPre P).step q (Sum.inl l) μ) :
    (hybrid P).step q Lab.tau μ := by
  rw [hybrid_step_iff]
  exact Or.inl ⟨rfl, l, hl, (hybridGroup_step_iff P q l μ).mpr (Or.inr h)⟩

/-- A label outside the sub-protocol API survives both hidings. -/
theorem hybrid_vis (P : Params) {q : HybridState P} {l : Lab P.n}
    {μ : PMF (HybridState P)} (hl : l ∉ Lab.hiddenAPI P.n)
    (h : (hybridPre P).step q (Sum.inl l) μ) :
    (hybrid P).step q l μ := by
  rw [hybrid_step_iff]
  exact Or.inr ⟨hl, (hybridGroup_step_iff P q l μ).mpr (Or.inr h)⟩

end ABA

end PLTS
