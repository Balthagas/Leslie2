/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCASubsystem
import Leslie2.Results

/-!
# The layered presentation: layer boundaries as component boundaries

This is the first specification stage of the chain. The deployed reading of
`ABA/Deployed.lean` presents the protocol as `n` corruption-blind programs
beside one network adversary and the coin oracle; each program runs two layers
at once, and the single adversary holds both message layers. The present file
reads the same protocol with a *layer* boundary as a *component* boundary:

* the graded-agreement side is the round-indexed family `GSub.gbcaSide`. Its
  round-`r` factor is a parallel component in its own right: the stage
  programs of round `r` beside the message fabric of round `r`, which that
  component owns outright;
* the round loops are `n` separate automata (`coreProcN`), synchronised;
* what is left of the network adversary is the DECIDED layer beside the
  corrupted set (`aNet`);
* the coin oracle enters through the same label pullback as in the deployed
  reading (`Net.wccLift`).

The four factors speak the extended alphabet `Net.NLab n`, the rendezvous
labels are hidden, and the result is read back over `Lab n`.

## Per-round memory

A round subsystem is a factor of the composite from the start, not an object
created by the round's first call, and it keeps its stage records and its
fabric for the whole run. The graded-agreement coordinate of a layered state
is therefore `ℕ → GBCA.ImplState n`: every round is present at every moment,
whichever round each process is in. That retained memory is specification-side
state. No process holds it — a deployed node carries the stage record of the
round its round loop is in and nothing else (D20).

## The rule tables

`CoreProcStepN` is the round loop of one process: the API rows `callABA` and
`retABA`, the graded-agreement and coin handshakes, the DECIDED relay and its
delivery, and an idle row for every label the process does not act on. It has
no stage content. The five multicast levels and the stage delivery are
internal to a round subsystem, so their labels are dead at a round loop
(`stepC_gsnd_dead`, `stepC_gdlv_dead`), and the Byzantine graded-agreement
drives appear only as idle rows. The round loop's `retG` row fires on the
grade the label carries, at the right phase and round; the evidence for that
grade is the round subsystem's conjunct of the joint step.

`ANetStep` is what the network adversary retains once the round fabrics have
taken the stage pools: the DECIDED pools `dpool j`, the corrupted set `F` with
its budget, and the authorisation of the Byzantine drives.

## The authorisation relocation (D11)

A round subsystem carries no `k ∈ F` guard on the drive labels `byzCallG`,
`byzCallGLoop` and `byzRetG` (`GBCASubsystem.lean`, D11). A drive label stays
visible at the subsystem boundary and is authorised outside it. Here `aNet` is
that outside, and it carries the guard on its own copy of the corrupted set.
The two copies are written by one broadcast: `fail` reaches every round's
fabric through the family (`gbcaSide_fail`) and `aNet` on its own `fail` row,
and `GSub.GNetState.corrupt` and `ANetState.corrupt` are the same
budget-guarded insertion.

## What this file supplies

The rule tables of the round loops and of the ABA-side network, the
composition pipeline `layeredPre` / `layeredGroup` / `layered`, and the
readings of that pipeline in both directions. The builders assemble a
transition of the composite out of transitions of its factors
(`layeredPre_vis_step`, `layeredPre_tau_gbca`, `layeredPre_tau_aNet`,
`layeredPre_tau_wcc`, `gbcaSide_owned`, `gbcaSide_idle`, `gbcaSide_tau`,
`gbcaSide_fail`, `syncCore_pure`, `layeredGroup_of_event`,
`layeredGroup_of_tau`). The inversions read a composite transition back into
the rows its factors contributed (`layeredPre_vis_inv`, `layeredPre_tau_inv`,
`syncCore_inv`, the `stepC_*` table of one round loop and the `aStep_*` table
of the ABA-side network). The file defines the layered system and reads its
rows; it relates it to no other system. The chain past this reading continues
in `ABA/LayeredSpec.lean`.
-/

namespace PLTS
namespace ABA

open Net

/-! ## The `Layer` namespace

Everything the layer cut names lives under `PLTS.ABA.Layer`, so that `PLTS.ABA`
itself carries only what the chain cites. `Net` is the deployed reading's own
namespace; this is its layer-cut counterpart. -/

namespace Layer

/-! ### The round-loop program of one process

The layer that calls a round's graded-agreement subsystem and the coin, and
decides. It writes no stage record: the five multicast levels and the stage
delivery are internal to a round subsystem, so they leave no row here, and the
three Byzantine graded-agreement drives change no round-loop data, which is
why they appear below only as idle rows.

The programs sit under a full-synchronisation product, so every label that can
fire in the composite has a row: the participant's, or an idle one. Unlike the
round-indexed families, these programs are not round-filtered. A round loop
must answer every round's `callG`, its own as a participant and every other
process's as a bystander. -/

/-- The step relation of the round-loop program of process `j`. -/
inductive CoreProcStepN (P : Params) (j : Fin P.n) :
    CoreNodeN P.n → NLab P.n → PMF (CoreNodeN P.n) → Prop
  /-- `upon ABA(b)`: record input and estimate, open round `0`. -/
  | input (c : CoreNodeN P.n) (b : Bool) (h : c.proc.input = none) :
      CoreProcStepN P j c (Sum.inl (.callABA j b))
        (PMF.pure (c.setProc { c.proc with
          input := some b, est := some b, round := 0, phase := .toCallG }))
  /-- Input-enabledness loop on `j`'s own `callABA`. -/
  | inputLoop (c : CoreNodeN P.n) (b : Bool) :
      CoreProcStepN P j c (Sum.inl (.callABA j b)) (PMF.pure c)
  /-- An input addressed elsewhere: not `j`'s business. -/
  | callABAIdle (c : CoreNodeN P.n) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      CoreProcStepN P j c (Sum.inl (.callABA id b)) (PMF.pure c)
  /-- Return `b` on an `n − f` DECIDED quorum. Having multicast `b` oneself is
  a condition on the DECIDED pools, hence `aNet`'s conjunct. -/
  | ret (c : CoreNodeN P.n) (b : Bool)
      (hcnt : P.n - P.f ≤ c.decidedCount b) (hret : c.proc.returned = false) :
      CoreProcStepN P j c (Sum.inl (.retABA j b))
        (PMF.pure (c.setProc { c.proc with returned := true }))
  /-- A return by another process: not `j`'s business. -/
  | retABAIdle (c : CoreNodeN P.n) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      CoreProcStepN P j c (Sum.inl (.retABA id b)) (PMF.pure c)
  /-- The graded-agreement call, round-loop half: hand the estimate over and
  wait. Opening the stage record is the round subsystem's half. -/
  | callG (c : CoreNodeN P.n) (r : ℕ) (b : Bool)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r)
      (hest : c.proc.est = some b) :
      CoreProcStepN P j c (Sum.inl (.callG r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG }))
  /-- A graded-agreement call by another process: not `j`'s business. -/
  | callGIdle (c : CoreNodeN P.n) (r : ℕ) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      CoreProcStepN P j c (Sum.inl (.callG r id b)) (PMF.pure c)
  /-- The graded-agreement return, round-loop half: record the grade and head
  for the coin. The evidence for the grade is the round subsystem's conjunct. -/
  | retG (c : CoreNodeN P.n) (r : ℕ) (out : GbcaOut)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r) :
      CoreProcStepN P j c (Sum.inl (.retG r j out))
        (PMF.pure (c.setProc { c.proc with
          est := out.est, lastGrade := some out, phase := .toCallW }))
  /-- A graded-agreement return to another process: not `j`'s business. -/
  | retGIdle (c : CoreNodeN P.n) (r : ℕ) (id : Fin P.n) (out : GbcaOut)
      (hid : id ≠ j) :
      CoreProcStepN P j c (Sum.inl (.retG r id out)) (PMF.pure c)
  /-- `c ← WCC_r()`, the call half. -/
  | callW (c : CoreNodeN P.n) (r : ℕ)
      (hph : c.proc.phase = .toCallW) (hr : c.proc.round = r) :
      CoreProcStepN P j c (Sum.inl (.callW r j))
        (PMF.pure (c.setProc { c.proc with phase := .awaitW }))
  /-- A coin call by another process: not `j`'s business. -/
  | callWIdle (c : CoreNodeN P.n) (r : ℕ) (id : Fin P.n) (hid : id ≠ j) :
      CoreProcStepN P j c (Sum.inl (.callW r id)) (PMF.pure c)
  /-- The coin return without a publication: the round advances and nothing is
  multicast, the round's grade not being an `A` (D10). -/
  | retW (c : CoreNodeN P.n) (r : ℕ) (co : Bool)
      (hph : c.proc.phase = .awaitW) (hr : c.proc.round = r)
      (hgr : ∀ v : Bool, c.proc.lastGrade ≠ some (.A v)) :
      CoreProcStepN P j c (Sum.inl (.retW r j co)) (PMF.pure (c.stepRound co))
  /-- A coin return to another process: not `j`'s business. -/
  | retWIdle (c : CoreNodeN P.n) (r : ℕ) (id : Fin P.n) (co : Bool) (hid : id ≠ j) :
      CoreProcStepN P j c (Sum.inl (.retW r id co)) (PMF.pure c)
  /-- Corruption is not the round loop's business (D1). -/
  | failIdle (c : CoreNodeN P.n) (k : Fin P.n) :
      CoreProcStepN P j c (Sum.inl (.fail k)) (PMF.pure c)
  /-- The DECIDED relay on an `f + 1` quorum (D12′): the quorum is a condition
  on the node, the write-once condition and the pool insert are `aNet`'s. -/
  | dsndRelay (c : CoreNodeN P.n) (b : Bool)
      (hcnt : P.f + 1 ≤ c.decidedCount b) :
      CoreProcStepN P j c (Sum.inr (.dsnd j b)) (PMF.pure c)
  /-- A DECIDED relay by another process: not `j`'s business. -/
  | dsndIdle (c : CoreNodeN P.n) (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      CoreProcStepN P j c (Sum.inr (.dsnd k b)) (PMF.pure c)
  /-- DECIDED delivery, receiver's half: at most one receipt per (sender, bit)
  (D12′). Authenticity is `aNet`'s conjunct. -/
  | ddlvRecv (c : CoreNodeN P.n) (k : Fin P.n) (b : Bool) (hr : b ∉ c.decIn k) :
      CoreProcStepN P j c (Sum.inr (.ddlv j k b)) (PMF.pure (c.recvDec k b))
  /-- A DECIDED delivery to another process: not `j`'s business. -/
  | ddlvIdle (c : CoreNodeN P.n) (i k : Fin P.n) (b : Bool) (hi : i ≠ j) :
      CoreProcStepN P j c (Sum.inr (.ddlv i k b)) (PMF.pure c)
  /-- The coin return fused with the `⟨DECIDED, b⟩` publication (D10): the
  round's grade was `A b`, so the round advance publishes `b`, the pool insert
  being `aNet`'s half. -/
  | retWPub (c : CoreNodeN P.n) (r : ℕ) (co : Bool) (b : Bool)
      (hph : c.proc.phase = .awaitW) (hr : c.proc.round = r)
      (hgr : c.proc.lastGrade = some (.A b)) :
      CoreProcStepN P j c (Sum.inr (.retWPub r j co b)) (PMF.pure (c.stepRound co))
  /-- A fused coin return at another process: not `j`'s business. -/
  | retWPubIdle (c : CoreNodeN P.n) (r : ℕ) (id : Fin P.n) (co : Bool) (b : Bool)
      (hid : id ≠ j) :
      CoreProcStepN P j c (Sum.inr (.retWPub r id co b)) (PMF.pure c)
  /-- The graded-agreement call against an already-called stage record: the
  round loop moves and nothing else does — the whole row is core content. -/
  | gcallLoop (c : CoreNodeN P.n) (r : ℕ) (b : Bool)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r)
      (hest : c.proc.est = some b) :
      CoreProcStepN P j c (Sum.inr (.gcallLoop r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG }))
  /-- Such a call at another process: not `j`'s business. -/
  | gcallLoopIdle (c : CoreNodeN P.n) (r : ℕ) (id : Fin P.n) (b : Bool)
      (hid : id ≠ j) :
      CoreProcStepN P j c (Sum.inr (.gcallLoop r id b)) (PMF.pure c)
  /-- A Byzantine graded-agreement call (D11) writes a stage record and no
  round-loop data: every round loop, the driven one included, stands still. -/
  | byzCallGIdle (c : CoreNodeN P.n) (r : ℕ) (k : Fin P.n) (b : Bool) :
      CoreProcStepN P j c (Sum.inr (.byzCallG r k b)) (PMF.pure c)
  /-- A Byzantine graded-agreement call against an already-called stage record
  (D11): nothing moves anywhere. -/
  | byzCallGLoopIdle (c : CoreNodeN P.n) (r : ℕ) (k : Fin P.n) (b : Bool) :
      CoreProcStepN P j c (Sum.inr (.byzCallGLoop r k b)) (PMF.pure c)
  /-- A Byzantine graded-agreement return (D11): stage content only. -/
  | byzRetGIdle (c : CoreNodeN P.n) (r : ℕ) (k : Fin P.n) (out : GbcaOut) :
      CoreProcStepN P j c (Sum.inr (.byzRetG r k out)) (PMF.pure c)
  /-- A Byzantine coin call (D11): the coin oracle reacts through the pullback. -/
  | byzCallWIdle (c : CoreNodeN P.n) (r : ℕ) (k : Fin P.n) :
      CoreProcStepN P j c (Sum.inr (.byzCallW r k)) (PMF.pure c)
  /-- A Byzantine coin return (D11): the coin oracle reacts through the
  pullback. -/
  | byzRetWIdle (c : CoreNodeN P.n) (r : ℕ) (k : Fin P.n) (b : Bool) :
      CoreProcStepN P j c (Sum.inr (.byzRetW r k b)) (PMF.pure c)

/-! ### The DECIDED layer and the corrupted set

What is left of the network adversary once the round-tagged pools have gone to
the round fabrics: the DECIDED pools, the corrupted set with its budget, and
the authorisation of every Byzantine drive. -/

/-- The state of the ABA-side network: the DECIDED pools and the corrupted
set. -/
structure ANetState (n : ℕ) : Type where
  /-- `dpool j` — the DECIDED payloads process `j` has multicast (D12′). -/
  dpool : Fin n → Finset Bool
  /-- The corrupted set. -/
  F : Finset (Fin n)

namespace ANetState

variable {n : ℕ}

/-- The initial network: nothing multicast, nobody corrupted. -/
def initial (n : ℕ) : ANetState n where
  dpool := fun _ => ∅
  F := ∅

/-- Pool `⟨DECIDED, b⟩` under sender `j` (D12′). -/
def dput (a : ANetState n) (j : Fin n) (b : Bool) : ANetState n :=
  { a with dpool := Function.update a.dpool j (insert b (a.dpool j)) }

/-- Corruption (deviation D1): total, Dirac, budget-guarded. -/
def corrupt (P : Params) (id : Fin P.n) (a : ANetState P.n) : ANetState P.n :=
  if id ∉ a.F ∧ a.F.card < P.f then { a with F := insert id a.F } else a

@[simp] theorem dput_dpool (a : ANetState n) (j : Fin n) (b : Bool) :
    (a.dput j b).dpool = Function.update a.dpool j (insert b (a.dpool j)) := rfl

@[simp] theorem dput_F (a : ANetState n) (j : Fin n) (b : Bool) :
    (a.dput j b).F = a.F := rfl

end ANetState

/-- The step relation of the ABA-side network. All transitions are Dirac. -/
inductive ANetStep (P : Params) :
    ANetState P.n → NLab P.n → PMF (ANetState P.n) → Prop
  /-- The DECIDED relay's half: the payload must not be pooled yet (D12′). -/
  | dsnd (a : ANetState P.n) (j : Fin P.n) (b : Bool) (h : b ∉ a.dpool j) :
      ANetStep P a (Sum.inr (.dsnd j b)) (PMF.pure (a.dput j b))
  /-- The DECIDED delivery's half: the payload must be pooled under the named
  sender (D12′). -/
  | ddlv (a : ANetState P.n) (i j : Fin P.n) (b : Bool) (h : b ∈ a.dpool j) :
      ANetStep P a (Sum.inr (.ddlv i j b)) (PMF.pure a)
  /-- The fused coin return's half: pool the published payload (D10, D12′). -/
  | retWPub (a : ANetState P.n) (r : ℕ) (id : Fin P.n) (c : Bool) (b : Bool) :
      ANetStep P a (Sum.inr (.retWPub r id c b)) (PMF.pure (a.dput id b))
  /-- A graded-agreement call against an already-called stage record publishes
  nothing here. -/
  | gcallLoop (a : ANetState P.n) (r : ℕ) (id : Fin P.n) (b : Bool) :
      ANetStep P a (Sum.inr (.gcallLoop r id b)) (PMF.pure a)
  /-- The authorisation of a Byzantine graded-agreement call (D11): the round
  subsystem carries the effect, this component carries the guard. -/
  | byzCallG (a : ANetState P.n) (r : ℕ) (k : Fin P.n) (b : Bool) (hF : k ∈ a.F) :
      ANetStep P a (Sum.inr (.byzCallG r k b)) (PMF.pure a)
  /-- The authorisation of a Byzantine call against an already-called stage
  record (D11). -/
  | byzCallGLoop (a : ANetState P.n) (r : ℕ) (k : Fin P.n) (b : Bool)
      (hF : k ∈ a.F) :
      ANetStep P a (Sum.inr (.byzCallGLoop r k b)) (PMF.pure a)
  /-- The authorisation of a Byzantine graded-agreement return (D11). -/
  | byzRetG (a : ANetState P.n) (r : ℕ) (k : Fin P.n) (out : GbcaOut)
      (hF : k ∈ a.F) :
      ANetStep P a (Sum.inr (.byzRetG r k out)) (PMF.pure a)
  /-- The authorisation of a Byzantine coin call (D11). -/
  | byzCallW (a : ANetState P.n) (r : ℕ) (k : Fin P.n) (hF : k ∈ a.F) :
      ANetStep P a (Sum.inr (.byzCallW r k)) (PMF.pure a)
  /-- The authorisation of a Byzantine coin return (D11). -/
  | byzRetW (a : ANetState P.n) (r : ℕ) (k : Fin P.n) (b : Bool) (hF : k ∈ a.F) :
      ANetStep P a (Sum.inr (.byzRetW r k b)) (PMF.pure a)
  /-- An external input is not this component's business. -/
  | callABAIdle (a : ANetState P.n) (id : Fin P.n) (b : Bool) :
      ANetStep P a (Sum.inl (.callABA id b)) (PMF.pure a)
  /-- A return requires the returning process to have multicast the payload —
  a condition on its DECIDED pool (D12′). -/
  | retABA (a : ANetState P.n) (id : Fin P.n) (b : Bool) (h : b ∈ a.dpool id) :
      ANetStep P a (Sum.inl (.retABA id b)) (PMF.pure a)
  /-- The graded-agreement call's `⟨INPUT, b⟩` is pooled in the round's fabric,
  not here. -/
  | callGIdle (a : ANetState P.n) (r : ℕ) (id : Fin P.n) (b : Bool) :
      ANetStep P a (Sum.inl (.callG r id b)) (PMF.pure a)
  /-- A graded-agreement return publishes nothing here. -/
  | retGIdle (a : ANetState P.n) (r : ℕ) (id : Fin P.n) (out : GbcaOut) :
      ANetStep P a (Sum.inl (.retG r id out)) (PMF.pure a)
  /-- A coin call publishes nothing. -/
  | callWIdle (a : ANetState P.n) (r : ℕ) (id : Fin P.n) :
      ANetStep P a (Sum.inl (.callW r id)) (PMF.pure a)
  /-- An unfused coin return publishes nothing. -/
  | retWIdle (a : ANetState P.n) (r : ℕ) (id : Fin P.n) (c : Bool) :
      ANetStep P a (Sum.inl (.retW r id c)) (PMF.pure a)
  /-- Corruption (deviation D1): total, Dirac, budget-guarded. The budget is
  this component's own guard. -/
  | fail (a : ANetState P.n) (k : Fin P.n) :
      ANetStep P a (Sum.inl (.fail k)) (PMF.pure (ANetState.corrupt P k a))
  /-- Byzantine DECIDED injection (D12′): either or both bits, at any time, so
  a corrupted process may equivocate at the DECIDED layer. -/
  | byzD (a : ANetState P.n) (k : Fin P.n) (b : Bool) (hF : k ∈ a.F) :
      ANetStep P a (Sum.inl .tau) (PMF.pure (a.dput k b))

/-! ### The automata and the composition pipeline -/

/-- The round-loop program of process `j`. -/
noncomputable def coreProcN (P : Params) (j : Fin P.n) :
    System (CoreNodeN P.n) (NLab P.n) where
  init := CoreNodeN.initial P.n
  step := CoreProcStepN P j

@[simp] theorem coreProcN_init (P : Params) (j : Fin P.n) :
    (coreProcN P j).init = CoreNodeN.initial P.n := rfl

@[simp] theorem coreProcN_step (P : Params) (j : Fin P.n) (c : CoreNodeN P.n)
    (l : NLab P.n) (ν : PMF (CoreNodeN P.n)) :
    (coreProcN P j).step c l ν ↔ CoreProcStepN P j c l ν := Iff.rfl

/-- The ABA-side network. -/
noncomputable def aNet (P : Params) : System (ANetState P.n) (NLab P.n) where
  init := ANetState.initial P.n
  step := ANetStep P

@[simp] theorem aNet_init (P : Params) : (aNet P).init = ANetState.initial P.n := rfl

@[simp] theorem aNet_step (P : Params) (a : ANetState P.n) (l : NLab P.n)
    (μ : PMF (ANetState P.n)) : (aNet P).step a l μ ↔ ANetStep P a l μ := Iff.rfl

/-- The state of the layered system: the round subsystems, the round loops,
the ABA-side network and the coin oracle. -/
abbrev LayeredState (P : Params) : Type :=
  (ℕ → GBCA.ImplState P.n) ×
    ((∀ _ : Fin P.n, CoreNodeN P.n) × (ANetState P.n × (ℕ → WCC.SpecState P.n)))

/-- The four factors side by side, over the extended alphabet. -/
noncomputable def layeredPre (P : Params) : System (LayeredState P) (NLab P.n) :=
  (GSub.gbcaSide P).parallel
    ((System.syncProduct (coreProcN P)).parallel ((aNet P).parallel (wccLift P)))

/-- **The layered group**: the rendezvous alphabet hidden, the result read
back over `Lab n`. -/
noncomputable def layeredGroup (P : Params) : System (LayeredState P) (Lab P.n) :=
  ((layeredPre P).abstract (netEvtLabels P.n)).relabel

/-- **The layered system**: the group with the sub-protocol API hidden. -/
noncomputable def layered (P : Params) : System (LayeredState P) (Lab P.n) :=
  (layeredGroup P).abstract (Lab.hiddenAPI P.n)

/-! ### Determinacy of the two new rule tables -/

/-- Every round-loop transition is Dirac. -/
theorem coreProcStepN_dirac {P : Params} {j : Fin P.n} {c : CoreNodeN P.n}
    {l : NLab P.n} {ν : PMF (CoreNodeN P.n)} (h : CoreProcStepN P j c l ν) :
    ∃ c', ν = PMF.pure c' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every ABA-side network transition is Dirac. -/
theorem aNetStep_dirac {P : Params} {a : ANetState P.n} {l : NLab P.n}
    {μ : PMF (ANetState P.n)} (h : ANetStep P a l μ) : ∃ a', μ = PMF.pure a' := by
  cases h <;> exact ⟨_, rfl⟩

/-- A round-loop program is an LTS. -/
theorem coreProcN_isLTS (P : Params) (j : Fin P.n) : (coreProcN P j).IsLTS :=
  fun _ _ _ h => coreProcStepN_dirac h

/-- The ABA-side network is an LTS. -/
theorem aNet_isLTS (P : Params) : (aNet P).IsLTS := fun _ _ _ h => aNetStep_dirac h

/-- The synchronised group of round loops is an LTS. -/
theorem syncCore_isLTS (P : Params) : (System.syncProduct (coreProcN P)).IsLTS :=
  System.syncProduct_isLTS (coreProcN_isLTS P)

/-- No round-loop rule fires on `τ`: a round loop only ever moves in a
rendezvous or on a shared API label. -/
theorem coreProcStepN_no_tau {P : Params} {j : Fin P.n} {c : CoreNodeN P.n}
    {ν : PMF (CoreNodeN P.n)} (h : CoreProcStepN P j c (Silent.τ : NLab P.n) ν) :
    False := by
  rw [nlab_tau] at h; cases h

/-! ### Reading and building composite transitions of the layered system -/

/-- The layered group's step relation, unfolded to the hidden rendezvous case
and the shared-label case. -/
theorem layeredGroup_step_iff (P : Params) (q : LayeredState P) (l : Lab P.n)
    (μ : PMF (LayeredState P)) :
    (layeredGroup P).step q l μ ↔
      (l = .tau ∧ ∃ e : NetEvt P.n, (layeredPre P).step q (Sum.inr e) μ) ∨
      (layeredPre P).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_netEvtLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_netEvtLabels l, hstep⟩

/-- A synchronised transition of the round-loop group on a visible label. -/
theorem syncCore_inv {P : Params} {C : ∀ _ : Fin P.n, CoreNodeN P.n} {l : NLab P.n}
    {μ : PMF (∀ _ : Fin P.n, CoreNodeN P.n)}
    (h : (System.syncProduct (coreProcN P)).step C l μ) :
    ∃ y : ∀ _ : Fin P.n, CoreNodeN P.n,
      μ = PMF.pure y ∧ ∀ i, CoreProcStepN P i (C i) l (PMF.pure (y i)) := by
  rw [System.syncProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨rfl, i, μ_i, hstep, -⟩
  · have hy : ∀ i, ∃ c', μ_ i = PMF.pure c' := fun i => coreProcStepN_dirac (hall i)
    choose y hy using hy
    refine ⟨y, ?_, fun i => ?_⟩
    · rw [show μ_ = fun i => PMF.pure (y i) from funext hy]
      exact piPMF_pure y
    · rw [← hy i]; exact hall i
  · exact absurd hstep coreProcStepN_no_tau

/-- Build a synchronised transition of the round-loop group from per-process
Dirac steps. -/
theorem syncCore_pure {P : Params} {C y : ∀ _ : Fin P.n, CoreNodeN P.n}
    {l : NLab P.n} (hl : l ≠ Silent.τ)
    (h : ∀ i, CoreProcStepN P i (C i) l (PMF.pure (y i))) :
    (System.syncProduct (coreProcN P)).step C l (PMF.pure y) := by
  rw [System.syncProduct_step]
  exact Or.inl ⟨hl, fun i => PMF.pure (y i), h, (piPMF_pure y).symm⟩

/-- The round-loop group has no silent transition. -/
theorem syncCore_no_tau {P : Params} {C : ∀ _ : Fin P.n, CoreNodeN P.n}
    {μ : PMF (∀ _ : Fin P.n, CoreNodeN P.n)}
    (h : (System.syncProduct (coreProcN P)).step C (Silent.τ : NLab P.n) μ) :
    False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact coreProcStepN_no_tau hstep

/-- Build a joint transition of the four factors on a visible label, the
oracle's successor left arbitrary. -/
theorem layeredPre_vis_step (P : Params) {G G' : ℕ → GBCA.ImplState P.n}
    {C C' : ∀ _ : Fin P.n, CoreNodeN P.n} {A A' : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {ω : PMF (ℕ → WCC.SpecState P.n)} {L : NLab P.n}
    (hL : L ≠ Silent.τ)
    (hG : (GSub.gbcaSide P).step G L (PMF.pure G'))
    (hC : ∀ i, CoreProcStepN P i (C i) L (PMF.pure (C' i)))
    (hA : ANetStep P A L (PMF.pure A'))
    (hW : (wccLift P).step o L ω) :
    (layeredPre P).step (G, C, A, o) L
      (prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω))) := by
  rw [layeredPre, System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure G', prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω),
    hG, ?_, rfl⟩
  rw [System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure C', prodPMF (PMF.pure A') ω, syncCore_pure hL hC, ?_, rfl⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure A', ω, hA, hW, rfl⟩

/-- Build a silent transition of the four factors from a graded-agreement-side
one. -/
theorem layeredPre_tau_gbca (P : Params) {G G' : ℕ → GBCA.ImplState P.n}
    {C : ∀ _ : Fin P.n, CoreNodeN P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hG : (GSub.gbcaSide P).step G (Sum.inl Lab.tau) (PMF.pure G')) :
    (layeredPre P).step (G, C, A, o) (Sum.inl Lab.tau) (PMF.pure (G', C, A, o)) := by
  rw [layeredPre, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure G', hG, ?_⟩)
  rw [prodPMF_pure_pure]

/-- Build a silent transition of the four factors from an ABA-side network
injection. -/
theorem layeredPre_tau_aNet (P : Params) {G : ℕ → GBCA.ImplState P.n}
    {C : ∀ _ : Fin P.n, CoreNodeN P.n} {A A' : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hA : ANetStep P A (Sum.inl Lab.tau) (PMF.pure A')) :
    (layeredPre P).step (G, C, A, o) (Sum.inl Lab.tau) (PMF.pure (G, C, A', o)) := by
  rw [layeredPre, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl,
    prodPMF (PMF.pure C) (prodPMF (PMF.pure A') (PMF.pure o)), ?_, ?_⟩)
  · rw [System.parallel_step]
    refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure A') (PMF.pure o), ?_, rfl⟩)
    rw [System.parallel_step]
    exact Or.inr (Or.inl ⟨rfl, PMF.pure A', hA, rfl⟩)
  · rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure]

/-- Build a silent transition of the four factors from the coin resolution —
the one transition of the composite that is not Dirac. -/
theorem layeredPre_tau_wcc (P : Params) {G : ℕ → GBCA.ImplState P.n}
    {C : ∀ _ : Fin P.n, CoreNodeN P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {ω : PMF (ℕ → WCC.SpecState P.n)}
    (hW : (WCC.specFamily P).step o Lab.tau ω) :
    (layeredPre P).step (G, C, A, o) (Sum.inl Lab.tau)
      (prodPMF (PMF.pure G) (prodPMF (PMF.pure C) (prodPMF (PMF.pure A) ω))) := by
  rw [layeredPre, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, _, ?_, rfl⟩)
  rw [System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure A) ω, ?_, rfl⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, ω, (System.mapIdle_step_some (by simp) ω).mpr hW, rfl⟩)

/-- A visible transition of the four factors: all of them move together, and
only the oracle's successor can fail to be a Dirac. -/
theorem layeredPre_vis_inv (P : Params) {G : ℕ → GBCA.ImplState P.n}
    {C : ∀ _ : Fin P.n, CoreNodeN P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {L : NLab P.n} (hL : L ≠ Silent.τ)
    {μ : PMF (LayeredState P)} (h : (layeredPre P).step (G, C, A, o) L μ) :
    ∃ (G' : ℕ → GBCA.ImplState P.n) (C' : ∀ _ : Fin P.n, CoreNodeN P.n)
      (A' : ANetState P.n) (ω : PMF (ℕ → WCC.SpecState P.n)),
      (GSub.gbcaSide P).step G L (PMF.pure G') ∧
      (∀ i, CoreProcStepN P i (C i) L (PMF.pure (C' i))) ∧
      ANetStep P A L (PMF.pure A') ∧ (wccLift P).step o L ω ∧
      μ = prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω)) := by
  rw [layeredPre, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hG, hrest, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
  · obtain ⟨G', rfl⟩ := GSub.gbcaSide_isLTS P _ _ _ hG
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
is the graded-agreement side's, the ABA-side network's own injection, or the
coin resolution. -/
theorem layeredPre_tau_inv (P : Params) {G : ℕ → GBCA.ImplState P.n}
    {C : ∀ _ : Fin P.n, CoreNodeN P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {μ : PMF (LayeredState P)}
    (h : (layeredPre P).step (G, C, A, o) (Sum.inl Lab.tau) μ) :
    (∃ G', (GSub.gbcaSide P).step G (Sum.inl Lab.tau) (PMF.pure G') ∧
        μ = PMF.pure (G', C, A, o)) ∨
    (∃ A', ANetStep P A (Sum.inl Lab.tau) (PMF.pure A') ∧
        μ = PMF.pure (G, C, A', o)) ∨
    (∃ ω, (WCC.specFamily P).step o Lab.tau ω ∧
        μ = prodPMF (PMF.pure G) (prodPMF (PMF.pure C) (prodPMF (PMF.pure A) ω))) := by
  rw [layeredPre, System.parallel_step] at h
  rcases h with ⟨habs, -⟩ | ⟨-, μ₁, hG, rfl⟩ | ⟨-, μ₂, hrest, rfl⟩
  · exact absurd rfl habs
  · obtain ⟨G', rfl⟩ := GSub.gbcaSide_isLTS P _ _ _ hG
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

/-! ### One round loop's rules, by label class

Each lemma reads a row of `CoreProcStepN` off its label: the participant's row
as its guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. -/

section CoreInversion

variable {P : Params} {j : Fin P.n} {c : CoreNodeN P.n} {ν : PMF (CoreNodeN P.n)}

theorem stepC_callABA_own {b : Bool}
    (h : CoreProcStepN P j c (Sum.inl (.callABA j b)) ν) :
    (c.proc.input = none ∧
      ν = PMF.pure (c.setProc { c.proc with
        input := some b, est := some b, round := 0, phase := .toCallG })) ∨
    ν = PMF.pure c := by
  cases h
  case input => exact Or.inl ⟨by assumption, rfl⟩
  case inputLoop => exact Or.inr rfl
  case callABAIdle => exact absurd rfl ‹_ ≠ j›

theorem stepC_callABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : CoreProcStepN P j c (Sum.inl (.callABA id b)) ν) : ν = PMF.pure c := by
  cases h
  case input => exact absurd rfl hid
  case inputLoop => exact absurd rfl hid
  case callABAIdle => rfl

theorem stepC_retABA_own {b : Bool}
    (h : CoreProcStepN P j c (Sum.inl (.retABA j b)) ν) :
    P.n - P.f ≤ c.decidedCount b ∧ c.proc.returned = false ∧
      ν = PMF.pure (c.setProc { c.proc with returned := true }) := by
  cases h
  case ret => exact ⟨by assumption, by assumption, rfl⟩
  case retABAIdle => exact absurd rfl ‹_ ≠ j›

theorem stepC_retABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : CoreProcStepN P j c (Sum.inl (.retABA id b)) ν) : ν = PMF.pure c := by
  cases h
  case ret => exact absurd rfl hid
  case retABAIdle => rfl

theorem stepC_callG_own {r : ℕ} {b : Bool}
    (h : CoreProcStepN P j c (Sum.inl (.callG r j b)) ν) :
    c.proc.phase = .toCallG ∧ c.proc.round = r ∧ c.proc.est = some b ∧
      ν = PMF.pure (c.setProc { c.proc with phase := .awaitG }) := by
  cases h
  case callG => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case callGIdle => exact absurd rfl ‹_ ≠ j›

theorem stepC_callG_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : CoreProcStepN P j c (Sum.inl (.callG r id b)) ν) : ν = PMF.pure c := by
  cases h
  case callG => exact absurd rfl hid
  case callGIdle => rfl

theorem stepC_retG_own {r : ℕ} {out : GbcaOut}
    (h : CoreProcStepN P j c (Sum.inl (.retG r j out)) ν) :
    c.proc.phase = .awaitG ∧ c.proc.round = r ∧
      ν = PMF.pure (c.setProc { c.proc with
        est := out.est, lastGrade := some out, phase := .toCallW }) := by
  cases h
  case retG => exact ⟨by assumption, by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›

theorem stepC_retG_foreign {r : ℕ} {id : Fin P.n} {out : GbcaOut} (hid : id ≠ j)
    (h : CoreProcStepN P j c (Sum.inl (.retG r id out)) ν) : ν = PMF.pure c := by
  cases h
  case retG => exact absurd rfl hid
  case retGIdle => rfl

theorem stepC_callW_own {r : ℕ}
    (h : CoreProcStepN P j c (Sum.inl (.callW r j)) ν) :
    c.proc.phase = .toCallW ∧ c.proc.round = r ∧
      ν = PMF.pure (c.setProc { c.proc with phase := .awaitW }) := by
  cases h
  case callW => exact ⟨by assumption, by assumption, rfl⟩
  case callWIdle => exact absurd rfl ‹_ ≠ j›

theorem stepC_callW_foreign {r : ℕ} {id : Fin P.n} (hid : id ≠ j)
    (h : CoreProcStepN P j c (Sum.inl (.callW r id)) ν) : ν = PMF.pure c := by
  cases h
  case callW => exact absurd rfl hid
  case callWIdle => rfl

theorem stepC_retW_own {r : ℕ} {co : Bool}
    (h : CoreProcStepN P j c (Sum.inl (.retW r j co)) ν) :
    c.proc.phase = .awaitW ∧ c.proc.round = r ∧
      (∀ v : Bool, c.proc.lastGrade ≠ some (.A v)) ∧
      ν = PMF.pure (c.stepRound co) := by
  cases h
  case retW => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case retWIdle => exact absurd rfl ‹_ ≠ j›

theorem stepC_retW_foreign {r : ℕ} {id : Fin P.n} {co : Bool} (hid : id ≠ j)
    (h : CoreProcStepN P j c (Sum.inl (.retW r id co)) ν) : ν = PMF.pure c := by
  cases h
  case retW => exact absurd rfl hid
  case retWIdle => rfl

theorem stepC_fail {k : Fin P.n}
    (h : CoreProcStepN P j c (Sum.inl (.fail k)) ν) : ν = PMF.pure c := by
  cases h; rfl

theorem stepC_dsnd_self {b : Bool}
    (h : CoreProcStepN P j c (Sum.inr (.dsnd j b)) ν) :
    P.f + 1 ≤ c.decidedCount b ∧ ν = PMF.pure c := by
  cases h
  case dsndRelay => exact ⟨by assumption, rfl⟩
  case dsndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepC_dsnd_foreign {k : Fin P.n} {b : Bool} (hk : k ≠ j)
    (h : CoreProcStepN P j c (Sum.inr (.dsnd k b)) ν) : ν = PMF.pure c := by
  cases h
  case dsndRelay => exact absurd rfl hk
  case dsndIdle => rfl

theorem stepC_ddlv_self {k : Fin P.n} {b : Bool}
    (h : CoreProcStepN P j c (Sum.inr (.ddlv j k b)) ν) :
    b ∉ c.decIn k ∧ ν = PMF.pure (c.recvDec k b) := by
  cases h
  case ddlvRecv => exact ⟨by assumption, rfl⟩
  case ddlvIdle => exact absurd rfl ‹_ ≠ j›

theorem stepC_ddlv_foreign {i k : Fin P.n} {b : Bool} (hi : i ≠ j)
    (h : CoreProcStepN P j c (Sum.inr (.ddlv i k b)) ν) : ν = PMF.pure c := by
  cases h
  case ddlvRecv => exact absurd rfl hi
  case ddlvIdle => rfl

theorem stepC_retWPub_self {r : ℕ} {co b : Bool}
    (h : CoreProcStepN P j c (Sum.inr (.retWPub r j co b)) ν) :
    c.proc.phase = .awaitW ∧ c.proc.round = r ∧
      c.proc.lastGrade = some (.A b) ∧ ν = PMF.pure (c.stepRound co) := by
  cases h
  case retWPub => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case retWPubIdle => exact absurd rfl ‹_ ≠ j›

theorem stepC_retWPub_foreign {r : ℕ} {id : Fin P.n} {co b : Bool} (hid : id ≠ j)
    (h : CoreProcStepN P j c (Sum.inr (.retWPub r id co b)) ν) : ν = PMF.pure c := by
  cases h
  case retWPub => exact absurd rfl hid
  case retWPubIdle => rfl

theorem stepC_gcallLoop_self {r : ℕ} {b : Bool}
    (h : CoreProcStepN P j c (Sum.inr (.gcallLoop r j b)) ν) :
    c.proc.phase = .toCallG ∧ c.proc.round = r ∧ c.proc.est = some b ∧
      ν = PMF.pure (c.setProc { c.proc with phase := .awaitG }) := by
  cases h
  case gcallLoop => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case gcallLoopIdle => exact absurd rfl ‹_ ≠ j›

theorem stepC_gcallLoop_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : CoreProcStepN P j c (Sum.inr (.gcallLoop r id b)) ν) : ν = PMF.pure c := by
  cases h
  case gcallLoop => exact absurd rfl hid
  case gcallLoopIdle => rfl

theorem stepC_byzCallG {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : CoreProcStepN P j c (Sum.inr (.byzCallG r k b)) ν) : ν = PMF.pure c := by
  cases h; rfl

theorem stepC_byzCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : CoreProcStepN P j c (Sum.inr (.byzCallGLoop r k b)) ν) : ν = PMF.pure c := by
  cases h; rfl

theorem stepC_byzRetG {r : ℕ} {k : Fin P.n} {out : GbcaOut}
    (h : CoreProcStepN P j c (Sum.inr (.byzRetG r k out)) ν) : ν = PMF.pure c := by
  cases h; rfl

theorem stepC_byzCallW {r : ℕ} {k : Fin P.n}
    (h : CoreProcStepN P j c (Sum.inr (.byzCallW r k)) ν) : ν = PMF.pure c := by
  cases h; rfl

theorem stepC_byzRetW {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : CoreProcStepN P j c (Sum.inr (.byzRetW r k b)) ν) : ν = PMF.pure c := by
  cases h; rfl

/-! The two stage rendezvous are internal to a round subsystem: no round loop
offers them. -/

theorem stepC_gsnd_dead {r : ℕ} {k : Fin P.n} {m : GBCA.Msg}
    (h : CoreProcStepN P j c (Sum.inr (.gsnd r k m)) ν) : False := by cases h

theorem stepC_gdlv_dead {r : ℕ} {i k : Fin P.n} {m : GBCA.Msg}
    (h : CoreProcStepN P j c (Sum.inr (.gdlv r i k m)) ν) : False := by cases h

end CoreInversion

/-! ### The ABA-side network's rules, by label class -/

section ANetInversion

variable {P : Params} {a : ANetState P.n} {μ : PMF (ANetState P.n)}

theorem aStep_dsnd {j : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inr (.dsnd j b)) μ) :
    b ∉ a.dpool j ∧ μ = PMF.pure (a.dput j b) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem aStep_ddlv {i j : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inr (.ddlv i j b)) μ) :
    b ∈ a.dpool j ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem aStep_retWPub {r : ℕ} {id : Fin P.n} {c b : Bool}
    (h : ANetStep P a (Sum.inr (.retWPub r id c b)) μ) :
    μ = PMF.pure (a.dput id b) := by
  cases h; rfl

theorem aStep_gcallLoop {r : ℕ} {id : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inr (.gcallLoop r id b)) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem aStep_byzCallG {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inr (.byzCallG r k b)) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem aStep_byzCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inr (.byzCallGLoop r k b)) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem aStep_byzRetG {r : ℕ} {k : Fin P.n} {out : GbcaOut}
    (h : ANetStep P a (Sum.inr (.byzRetG r k out)) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem aStep_byzCallW {r : ℕ} {k : Fin P.n}
    (h : ANetStep P a (Sum.inr (.byzCallW r k)) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem aStep_byzRetW {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inr (.byzRetW r k b)) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem aStep_callABA {id : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inl (.callABA id b)) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem aStep_retABA {id : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inl (.retABA id b)) μ) :
    b ∈ a.dpool id ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem aStep_callG {r : ℕ} {id : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inl (.callG r id b)) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem aStep_retG {r : ℕ} {id : Fin P.n} {out : GbcaOut}
    (h : ANetStep P a (Sum.inl (.retG r id out)) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem aStep_callW {r : ℕ} {id : Fin P.n}
    (h : ANetStep P a (Sum.inl (.callW r id)) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem aStep_retW {r : ℕ} {id : Fin P.n} {c : Bool}
    (h : ANetStep P a (Sum.inl (.retW r id c)) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem aStep_fail {k : Fin P.n}
    (h : ANetStep P a (Sum.inl (.fail k)) μ) :
    μ = PMF.pure (ANetState.corrupt P k a) := by
  cases h; rfl

theorem aStep_tau (h : ANetStep P a (Sum.inl .tau) μ) :
    ∃ (k : Fin P.n) (b : Bool), k ∈ a.F ∧ μ = PMF.pure (a.dput k b) := by
  cases h
  case byzD => exact ⟨_, _, by assumption, rfl⟩

theorem aStep_gsnd_dead {r : ℕ} {k : Fin P.n} {m : GBCA.Msg}
    (h : ANetStep P a (Sum.inr (.gsnd r k m)) μ) : False := by cases h

theorem aStep_gdlv_dead {r : ℕ} {i k : Fin P.n} {m : GBCA.Msg}
    (h : ANetStep P a (Sum.inr (.gdlv r i k m)) μ) : False := by cases h

end ANetInversion

/-! ### Pinning the round-loop tuple -/

theorem coresN_update {P : Params} {C y : ∀ _ : Fin P.n, CoreNodeN P.n}
    {id : Fin P.n} {nd : CoreNodeN P.n}
    (hown : (PMF.pure (y id) : PMF (CoreNodeN P.n)) = PMF.pure nd)
    (hfor : ∀ i, i ≠ id → (PMF.pure (y i) : PMF (CoreNodeN P.n)) = PMF.pure (C i)) :
    y = Function.update C id nd := by
  funext i
  by_cases hi : i = id
  · subst hi; rw [Function.update_self]; exact pureN_inj hown
  · rw [Function.update_of_ne hi]; exact pureN_inj (hfor i hi)

theorem coresN_id {P : Params} {C y : ∀ _ : Fin P.n, CoreNodeN P.n}
    (hall : ∀ i, (PMF.pure (y i) : PMF (CoreNodeN P.n)) = PMF.pure (C i)) : y = C :=
  funext fun i => pureN_inj (hall i)

/-- One round loop moves and every other idles. -/
theorem coresN_family {P : Params} {C : ∀ _ : Fin P.n, CoreNodeN P.n}
    {L : NLab P.n} (id : Fin P.n) (nd : CoreNodeN P.n)
    (hown : CoreProcStepN P id (C id) L (PMF.pure nd))
    (hfor : ∀ i, i ≠ id → CoreProcStepN P i (C i) L (PMF.pure (C i))) :
    ∀ i, CoreProcStepN P i (C i) L (PMF.pure (Function.update C id nd i)) := by
  intro i
  by_cases hi : i = id
  · subst hi; rw [Function.update_self]; exact hown
  · rw [Function.update_of_ne hi]; exact hfor i hi

/-! ### Which labels the round-indexed family owns -/

section GOwns

variable {n : ℕ}

@[simp] theorem gOwns_callG (r : ℕ) (id : Fin n) (b : Bool) :
    GSub.gOwns (Sum.inl (Lab.callG r id b) : NLab n) = some r := rfl
@[simp] theorem gOwns_retG (r : ℕ) (id : Fin n) (out : GbcaOut) :
    GSub.gOwns (Sum.inl (Lab.retG r id out) : NLab n) = some r := rfl
@[simp] theorem gOwns_gcallLoop (r : ℕ) (id : Fin n) (b : Bool) :
    GSub.gOwns (Sum.inr (.gcallLoop r id b) : NLab n) = some r := rfl
@[simp] theorem gOwns_byzCallG (r : ℕ) (k : Fin n) (b : Bool) :
    GSub.gOwns (Sum.inr (.byzCallG r k b) : NLab n) = some r := rfl
@[simp] theorem gOwns_byzCallGLoop (r : ℕ) (k : Fin n) (b : Bool) :
    GSub.gOwns (Sum.inr (.byzCallGLoop r k b) : NLab n) = some r := rfl
@[simp] theorem gOwns_byzRetG (r : ℕ) (k : Fin n) (out : GbcaOut) :
    GSub.gOwns (Sum.inr (.byzRetG r k out) : NLab n) = some r := rfl

@[simp] theorem gOwns_tau : GSub.gOwns (Sum.inl Lab.tau : NLab n) = none := rfl
@[simp] theorem gOwns_callABA (id : Fin n) (b : Bool) :
    GSub.gOwns (Sum.inl (Lab.callABA id b) : NLab n) = none := rfl
@[simp] theorem gOwns_retABA (id : Fin n) (b : Bool) :
    GSub.gOwns (Sum.inl (Lab.retABA id b) : NLab n) = none := rfl
@[simp] theorem gOwns_callW (r : ℕ) (id : Fin n) :
    GSub.gOwns (Sum.inl (Lab.callW r id) : NLab n) = none := rfl
@[simp] theorem gOwns_retW (r : ℕ) (id : Fin n) (c : Bool) :
    GSub.gOwns (Sum.inl (Lab.retW r id c) : NLab n) = none := rfl
@[simp] theorem gOwns_fail (k : Fin n) :
    GSub.gOwns (Sum.inl (Lab.fail k) : NLab n) = none := rfl
@[simp] theorem gOwns_gsnd (r : ℕ) (j : Fin n) (m : GBCA.Msg) :
    GSub.gOwns (Sum.inr (.gsnd r j m) : NLab n) = none := rfl
@[simp] theorem gOwns_gdlv (r : ℕ) (i j : Fin n) (m : GBCA.Msg) :
    GSub.gOwns (Sum.inr (.gdlv r i j m) : NLab n) = none := rfl
@[simp] theorem gOwns_dsnd (j : Fin n) (b : Bool) :
    GSub.gOwns (Sum.inr (.dsnd j b) : NLab n) = none := rfl
@[simp] theorem gOwns_ddlv (i j : Fin n) (b : Bool) :
    GSub.gOwns (Sum.inr (.ddlv i j b) : NLab n) = none := rfl
@[simp] theorem gOwns_retWPub (r : ℕ) (id : Fin n) (c b : Bool) :
    GSub.gOwns (Sum.inr (.retWPub r id c b) : NLab n) = none := rfl
@[simp] theorem gOwns_byzCallW (r : ℕ) (k : Fin n) :
    GSub.gOwns (Sum.inr (.byzCallW r k) : NLab n) = none := rfl
@[simp] theorem gOwns_byzRetW (r : ℕ) (k : Fin n) (b : Bool) :
    GSub.gOwns (Sum.inr (.byzRetW r k b) : NLab n) = none := rfl

@[simp] theorem isFailN_fail (k : Fin n) :
    GSub.isFailN (Sum.inl (Lab.fail k) : NLab n) := trivial

theorem gAct_fail {P : Params} (k : Fin P.n) (s : GBCA.ImplState P.n) :
    GSub.gAct P (Sum.inl (Lab.fail k)) s = (s.1, s.2.corrupt P k) := rfl

end GOwns

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

/-- An owned label is answered by its round alone. -/
theorem gbcaSide_owned_inv (P : Params) {G : ℕ → GBCA.ImplState P.n}
    {L : NLab P.n} {r : ℕ} (hL : GSub.gOwns L = some r) (hτ : L ≠ Silent.τ)
    {μ : PMF (ℕ → GBCA.ImplState P.n)} (h : (GSub.gbcaSide P).step G L μ) :
    ∃ X, (GSub.sub P r).step (G r) L (PMF.pure X) ∧
      μ = PMF.pure (Function.update G r X) := by
  rw [GSub.gbcaSide, System.family_step_iff] at h
  rcases h with ⟨habs, -⟩ | ⟨r', hown, μr, hstep, rfl⟩ | ⟨-, hown, -, -⟩ | ⟨-, hown, -, -⟩
  · exact absurd habs hτ
  · obtain rfl : r' = r := by rw [hL] at hown; exact (Option.some.inj hown).symm
    obtain ⟨X, rfl⟩ := GSub.sub_isLTS P r' _ _ _ hstep
    exact ⟨X, hstep, by rw [PMF.pure_map]⟩
  · rw [hL] at hown; exact absurd hown (by simp)
  · rw [hL] at hown; exact absurd hown (by simp)

/-- The family idles on a label no round owns and no broadcast. -/
theorem gbcaSide_idle_inv (P : Params) {G : ℕ → GBCA.ImplState P.n} {L : NLab P.n}
    (hτ : L ≠ Silent.τ) (hown : GSub.gOwns L = none) (hf : ¬ GSub.isFailN L)
    {μ : PMF (ℕ → GBCA.ImplState P.n)} (h : (GSub.gbcaSide P).step G L μ) :
    μ = PMF.pure G := by
  rw [GSub.gbcaSide, System.family_step_iff] at h
  rcases h with ⟨habs, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
  · exact absurd habs hτ
  · rw [hown] at hr; exact absurd hr (by simp)
  · exact absurd hglob hf
  · rfl

/-- Corruption is broadcast to every round. -/
theorem gbcaSide_fail_inv (P : Params) {G : ℕ → GBCA.ImplState P.n} (k : Fin P.n)
    {μ : PMF (ℕ → GBCA.ImplState P.n)}
    (h : (GSub.gbcaSide P).step G (Sum.inl (Lab.fail k)) μ) :
    μ = PMF.pure (fun r => GSub.gAct P (Sum.inl (Lab.fail k)) (G r)) := by
  rw [GSub.gbcaSide, System.family_step_iff] at h
  rcases h with ⟨habs, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, hglob, -⟩
  · exact absurd habs (by simp)
  · exact absurd hr (by simp)
  · rfl
  · exact absurd trivial hglob

/-- A silent transition of the family is one round's own silent rule. -/
theorem gbcaSide_tau_inv (P : Params) {G : ℕ → GBCA.ImplState P.n}
    {μ : PMF (ℕ → GBCA.ImplState P.n)}
    (h : (GSub.gbcaSide P).step G (Sum.inl Lab.tau) μ) :
    ∃ (r : ℕ) (X : GBCA.ImplState P.n),
      (GSub.sub P r).step (G r) (Sum.inl Lab.tau) (PMF.pure X) ∧
      μ = PMF.pure (Function.update G r X) := by
  rw [GSub.gbcaSide, System.family_step_iff] at h
  rcases h with ⟨-, r, μr, hstep, rfl⟩ | ⟨r, hr, -⟩ | ⟨habs, -, -, -⟩ | ⟨habs, -, -, -⟩
  · obtain ⟨X, rfl⟩ := GSub.sub_isLTS P r _ _ _ hstep
    exact ⟨r, X, hstep, by rw [PMF.pure_map]⟩
  · exact absurd hr (by simp)
  · exact absurd rfl habs
  · exact absurd rfl habs

/-! ### Pinning the stage-record tuple of one round -/

theorem gprocs_update {P : Params}
    {u x : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n} {id : Fin P.n}
    {nd : GBCA.ProcNodeN P.n}
    (hown : (PMF.pure (x id) : PMF (GBCA.ProcNodeN P.n)) = PMF.pure nd)
    (hfor : ∀ i, i ≠ id →
      (PMF.pure (x i) : PMF (GBCA.ProcNodeN P.n)) = PMF.pure (u i)) :
    x = Function.update u id nd := by
  funext i
  by_cases hi : i = id
  · subst hi; rw [Function.update_self]; exact GSub.pure_inj hown
  · rw [Function.update_of_ne hi]; exact GSub.pure_inj (hfor i hi)

theorem gprocs_id {P : Params} {u x : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n}
    (hall : ∀ i, (PMF.pure (x i) : PMF (GBCA.ProcNodeN P.n)) = PMF.pure (u i)) :
    x = u :=
  funext fun i => GSub.pure_inj (hall i)

/-- One stage program moves and every other idles. -/
theorem gprocs_family {P : Params} {r : ℕ}
    {u : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n} {L : GSub.GLab P.n} (id : Fin P.n)
    (nd : GBCA.ProcNodeN P.n)
    (hown : GSub.GProcStep P r id (u id) L (PMF.pure nd))
    (hfor : ∀ i, i ≠ id → GSub.GProcStep P r i (u i) L (PMF.pure (u i))) :
    ∀ i, GSub.GProcStep P r i (u i) L (PMF.pure (Function.update u id nd i)) := by
  intro i
  by_cases hi : i = id
  · subst hi; rw [Function.update_self]; exact hown
  · rw [Function.update_of_ne hi]; exact hfor i hi

/-! ### Hiding the rendezvous alphabet

The composition hides `NetEvt n`, so a transition of `layeredPre` on a
rendezvous label is a silent transition of `layeredGroup`, as is one on `τ`.
The two stage rendezvous never reach this point. They are internal to a round
subsystem, hidden inside `GSub.sub`, and reach the composite as the family's
own `τ`. -/

theorem layeredGroup_of_event (P : Params) {q : LayeredState P} (e : NetEvt P.n)
    {μ : PMF (LayeredState P)} (h : (layeredPre P).step q (Sum.inr e) μ) :
    (layeredGroup P).step q Lab.tau μ :=
  (layeredGroup_step_iff P _ _ _).mpr (Or.inl ⟨rfl, e, h⟩)

theorem layeredGroup_of_tau (P : Params) {q : LayeredState P} {μ : PMF (LayeredState P)}
    (h : (layeredPre P).step q (Sum.inl Lab.tau) μ) :
    (layeredGroup P).step q Lab.tau μ :=
  (layeredGroup_step_iff P _ _ _).mpr (Or.inr h)

end Layer

end ABA
end PLTS
