/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCASubsystem
import Leslie2.Results

/-!
# The layered presentation: layer boundaries as component boundaries

`ABA/Deployed.lean` presents the deployed protocol as `n` corruption-blind
programs beside one network adversary and the coin oracle. Each program runs
two layers at once — the round loop and one graded-agreement stage record per
round — and the single network adversary holds both message layers. The
present file re-cuts the same system so that a *layer* boundary is a
*component* boundary:

* the graded-agreement side is the family of round subsystems
  (`GSub.gbcaSide`), each a group of stage programs beside that round's own
  message fabric;
* the round loops are `n` separate automata (`coreProcN`), synchronised;
* what is left of the network adversary is the DECIDED layer beside the
  corrupted set (`aNet`);
* the coin oracle enters through the same label pullback as before
  (`Net.wccLift`).

The four factors speak the extended alphabet `Net.NLab n`, the rendezvous
labels are hidden, and the result is read back over `Lab n` — the pipeline of
`deployed`, factor for factor.

## What moved where

Every row of `Net.ABAProcStepN` is split along the layer boundary. Its
core-slice half is a row of `CoreProcStepN`; its stage-slice half is already a
row of `GSub.GProcStep`. The multicast levels and the delivery leave no core
row at all — their events are internal to a round subsystem, so their outer
labels are dead here; rows without core content (the Byzantine drives) survive
only as idle rows, and rows without stage content (`gcallLoop`) idle on the
stage side. The two rows the fusion of layers created, `callG_call` and `retG_*`,
split into a core guard-and-write and a stage guard-and-write that are joined
again by the composition.

`Net.NetStep` splits the same way: the round-tagged pools and their Byzantine
injection are the round fabrics' (`GSub.GNetStep`), the DECIDED pools and the
corrupted set are `aNet`'s.

## The authorisation relocation (D11)

`Net.NetStep` carries the `k ∈ F` guard of every Byzantine drive. The round
subsystem deliberately drops it (`GBCASub.lean`, D11): a drive label stays
visible at the subsystem boundary and is authorised outside. Here `aNet` is
that outside, and it carries the guard on its own copy of the corrupted set.
Since every copy of the corrupted set on either side is the network
adversary's one set, read through `regroup`, the two guards are the same
proposition.

## The result

`regroup` re-partitions a deployed state into an layered one — the stage
slices and pools are gathered per round, the core slices are gathered per
process, the DECIDED pools and the corrupted set go to `aNet`, and the coin
oracle is carried across untouched. It both preserves (`layeredForward`) and
reflects (`layeredConverse`) transitions, so the two soundness inclusions
close `layered_atd`: the two presentations achieve exactly the same trace
distributions.
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

The core-slice half of every row of `Net.ABAProcStepN`. A row whose fused
counterpart writes only a stage record leaves no row here: the six multicast
levels and the delivery are now internal to a round subsystem, and the three
Byzantine graded-agreement drives change no round-loop data, which is why they
appear below only as idle rows.

The programs sit under a full-synchronisation product, so every label that can
fire in the composite has a row: the participant's, or an idle one. Unlike the
round-indexed families, these programs are not round-filtered — a round loop
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

/-! ### The regrouping map

A deployed state is re-partitioned into an layered one. The round-`r`
subsystem takes its stage records from the nodes' round-`r` stage slices and
its pools from the network's round-`r` pools; the round loops take the nodes'
round-loop slices; the ABA-side network takes the DECIDED pools; and every
copy of the corrupted set on the layered side is the network adversary's one
set. The coin oracle occupies the same slot on both sides. -/

/-- The graded-agreement side of the regrouping. -/
def regG {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w : NetState n) :
    ℕ → GBCA.ImplState n :=
  fun r => (fun j => (u j).2 r, ⟨w.pool r, w.F⟩)

/-- The round-loop side of the regrouping. -/
def regC {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) : ∀ _ : Fin n, CoreNodeN n :=
  fun j => (u j).1

/-- The ABA-side network of the regrouping. -/
def regA {n : ℕ} (w : NetState n) : ANetState n := ⟨w.dpool, w.F⟩

/-- **The regrouping**: the round subsystems, the round loops and the ABA-side
network beside the untouched coin oracle. -/
def regroup {P : Params}
    (s : (∀ _ : Fin P.n, ABANodeN P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n))) :
    LayeredState P :=
  (regG s.1 s.2.1, regC s.1, regA s.2.1, s.2.2)

@[simp] theorem regroup_apply {P : Params} (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) :
    regroup (P := P) (u, w, o) = (regG u w, regC u, regA w, o) := rfl

/-- The regrouping carries the deployed initial state to the layered one. -/
theorem regroup_init (P : Params) : regroup (deployed P).init = (layered P).init := by
  refine Prod.ext (funext fun r => ?_) (Prod.ext rfl (Prod.ext ?_ rfl))
  · exact Prod.ext rfl rfl
  · exact rfl

/-! ### Transporting a strong functional matching through the pipeline

The two presentations are hidden and read back by the same two operators, so a
state map that preserves — or reflects — transitions before the hiding does so
after it. Both operators act on labels alone, so the transport is a case split
on the operator's own disjunction. -/

/-- Abstraction preserves a strong functional matching. -/
theorem strongForward_abstract {S T L : Type} [Silent L] {sys₁ : System S L}
    {sys₂ : System T L} (f : S → T) (H : Set L)
    (h : ∀ s l μ, sys₁.step s l μ → sys₂.step (f s) l (μ.map f)) :
    ∀ s l μ, (sys₁.abstract H).step s l μ → (sys₂.abstract H).step (f s) l (μ.map f) := by
  rintro s l μ (⟨rfl, l', hl', hstep⟩ | ⟨hl, hstep⟩)
  · exact Or.inl ⟨rfl, l', hl', h s l' μ hstep⟩
  · exact Or.inr ⟨hl, h s l μ hstep⟩

/-- Abstraction preserves a strong functional reflection. -/
theorem strongConverse_abstract {S T L : Type} [Silent L] {sys₁ : System S L}
    {sys₂ : System T L} (f : S → T) (H : Set L)
    (h : ∀ q l μ, sys₂.step (f q) l μ → ∃ ν, sys₁.step q l ν ∧ μ = ν.map f) :
    ∀ q l μ, (sys₂.abstract H).step (f q) l μ →
      ∃ ν, (sys₁.abstract H).step q l ν ∧ μ = ν.map f := by
  rintro q l μ (⟨rfl, l', hl', hstep⟩ | ⟨hl, hstep⟩)
  · obtain ⟨ν, hν, rfl⟩ := h q l' μ hstep
    exact ⟨ν, Or.inl ⟨rfl, l', hl', hν⟩, rfl⟩
  · obtain ⟨ν, hν, rfl⟩ := h q l μ hstep
    exact ⟨ν, Or.inr ⟨hl, hν⟩, rfl⟩

/-- Restriction along the left embedding preserves a strong functional
matching. -/
theorem strongForward_relabel {S T L E : Type} [Silent L]
    {sys₁ : System S (L ⊕ E)} {sys₂ : System T (L ⊕ E)} (f : S → T)
    (h : ∀ s l μ, sys₁.step s l μ → sys₂.step (f s) l (μ.map f)) :
    ∀ s l μ, sys₁.relabel.step s l μ → sys₂.relabel.step (f s) l (μ.map f) :=
  fun s l μ hs => h s (Sum.inl l) μ hs

/-- Restriction along the left embedding preserves a strong functional
reflection. -/
theorem strongConverse_relabel {S T L E : Type} [Silent L]
    {sys₁ : System S (L ⊕ E)} {sys₂ : System T (L ⊕ E)} (f : S → T)
    (h : ∀ q l μ, sys₂.step (f q) l μ → ∃ ν, sys₁.step q l ν ∧ μ = ν.map f) :
    ∀ q l μ, sys₂.relabel.step (f q) l μ →
      ∃ ν, sys₁.relabel.step q l ν ∧ μ = ν.map f :=
  fun q l μ hq => h q (Sum.inl l) μ hq

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

/-! ### Pushing the successor distribution forward

The only factor whose successor need not be a Dirac is the coin oracle, and it
occupies the same coordinate on both sides; the regrouping is therefore applied
under one `map`. -/

theorem map_regroup_prod {P : Params} (x : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (ω : PMF (ℕ → WCC.SpecState P.n)) :
    (prodPMF (PMF.pure x) (prodPMF (PMF.pure w) ω)).map regroup
      = prodPMF (PMF.pure (regG x w))
          (prodPMF (PMF.pure (regC x)) (prodPMF (PMF.pure (regA w)) ω)) := by
  simp only [prodPMF_pure_left, PMF.map_comp]
  rfl

theorem map_regroup_pure {P : Params} (x : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) :
    (PMF.pure (x, w, o) : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
        (NetState P.n × (ℕ → WCC.SpecState P.n)))).map regroup
      = PMF.pure (regG x w, regC x, regA w, o) := by
  rw [PMF.pure_map]; rfl

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

/-! The two stage rendezvous of the deployed network are internal to a round
subsystem now: no round loop offers them. -/

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

/-! ### Deltas of the regrouping

Each row writes one node slice and one network slot; read through the
regrouping, the pair becomes the matching one-row update of one layered
factor, every other factor being left alone. -/

private theorem gnet_ext {n : ℕ} {a b : GSub.GNetState n} (h1 : a.pool = b.pool)
    (h2 : a.F = b.F) : a = b := by
  cases a; cases b; cases h1; cases h2; rfl

@[simp] theorem regG_apply {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w : NetState n)
    (r : ℕ) : regG u w r = (fun j => (u j).2 r, ⟨w.pool r, w.F⟩) := rfl

@[simp] theorem regC_apply {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (j : Fin n) :
    regC u j = (u j).1 := rfl

@[simp] theorem regA_dpool {n : ℕ} (w : NetState n) : (regA w).dpool = w.dpool := rfl

@[simp] theorem regA_F {n : ℕ} (w : NetState n) : (regA w).F = w.F := rfl

/-- A node update touching only the round-loop slice, over a network whose
pools and corrupted set are untouched, leaves the graded-agreement side
alone. -/
theorem regG_core {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w w' : NetState n)
    (j : Fin n) (c' : CoreNodeN n) (hp : w'.pool = w.pool) (hF : w'.F = w.F) :
    regG (Function.update u j (c', (u j).2)) w' = regG u w := by
  funext r
  refine Prod.ext (funext fun i => ?_) ?_
  · change (Function.update u j (c', (u j).2) i).2 r = (u i).2 r
    by_cases hi : i = j
    · subst hi; simp only [Function.update_self]
    · rw [Function.update_of_ne hi]
  · change (⟨w'.pool r, w'.F⟩ : GSub.GNetState n) = ⟨w.pool r, w.F⟩
    rw [hp, hF]

/-- A DECIDED pool insert leaves the graded-agreement side alone. -/
@[simp] theorem regG_dput {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w : NetState n)
    (j : Fin n) (b : Bool) : regG u (w.dput j b) = regG u w := rfl

/-- A node update at `j` whose stage-`r` slice becomes `p'`, joined with the
sender's own pool insert: the round-`r` subsystem's one-coordinate update. -/
theorem regG_stage_mcast {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w : NetState n)
    (j : Fin n) (c' : CoreNodeN n) (r : ℕ) (p' : GBCA.ProcNodeN n) (m : GBCA.Msg) :
    regG (Function.update u j (c', Function.update (u j).2 r p')) (w.gpool r j m)
      = Function.update (regG u w) r
          (Function.update (fun i => (u i).2 r) j p', (regG u w r).2.gpool j m) := by
  funext r'
  by_cases hr : r' = r
  · rw [hr, Function.update_self]
    refine Prod.ext (funext fun i => ?_) ?_
    · change (Function.update u j (c', Function.update (u j).2 r p') i).2 r
          = Function.update (fun i => (u i).2 r) j p' i
      by_cases hi : i = j
      · subst hi; simp only [Function.update_self]
      · rw [Function.update_of_ne hi, Function.update_of_ne hi]
    · change (⟨(w.gpool r j m).pool r, (w.gpool r j m).F⟩ : GSub.GNetState n)
          = (⟨w.pool r, w.F⟩ : GSub.GNetState n).gpool j m
      exact gnet_ext (gpool_pool_self w r j m) rfl
  · rw [Function.update_of_ne hr]
    refine Prod.ext (funext fun i => ?_) ?_
    · change (Function.update u j (c', Function.update (u j).2 r p') i).2 r' = (u i).2 r'
      by_cases hi : i = j
      · subst hi; simp only [Function.update_self, Function.update_of_ne hr]
      · rw [Function.update_of_ne hi]
    · change (⟨(w.gpool r j m).pool r', (w.gpool r j m).F⟩ : GSub.GNetState n)
          = ⟨w.pool r', w.F⟩
      exact gnet_ext (gpool_pool_ne w r j m hr) rfl

/-- A node update at `j` whose stage-`r` slice becomes `p'`, multicasting
nothing. -/
theorem regG_stage_still {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w : NetState n)
    (j : Fin n) (c' : CoreNodeN n) (r : ℕ) (p' : GBCA.ProcNodeN n) :
    regG (Function.update u j (c', Function.update (u j).2 r p')) w
      = Function.update (regG u w) r
          (Function.update (fun i => (u i).2 r) j p', (regG u w r).2) := by
  funext r'
  by_cases hr : r' = r
  · rw [hr, Function.update_self]
    refine Prod.ext (funext fun i => ?_) rfl
    change (Function.update u j (c', Function.update (u j).2 r p') i).2 r
        = Function.update (fun i => (u i).2 r) j p' i
    by_cases hi : i = j
    · subst hi; simp only [Function.update_self]
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
  · rw [Function.update_of_ne hr]
    refine Prod.ext (funext fun i => ?_) rfl
    change (Function.update u j (c', Function.update (u j).2 r p') i).2 r' = (u i).2 r'
    by_cases hi : i = j
    · subst hi; simp only [Function.update_self, Function.update_of_ne hr]
    · rw [Function.update_of_ne hi]

/-- A pool insert with no node write: the round-`r` fabric's own multicast. -/
theorem regG_mcast {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w : NetState n) (r : ℕ)
    (k : Fin n) (m : GBCA.Msg) :
    regG u (w.gpool r k m)
      = Function.update (regG u w) r ((regG u w r).1, (regG u w r).2.gpool k m) := by
  funext r'
  by_cases hr : r' = r
  · rw [hr, Function.update_self]
    exact Prod.ext rfl (gnet_ext (gpool_pool_self w r k m) rfl)
  · rw [Function.update_of_ne hr]
    exact Prod.ext rfl (gnet_ext (gpool_pool_ne w r k m hr) rfl)

/-- Corruption commutes with the regrouping on the graded-agreement side: every
round's fabric carries the network adversary's one corrupted set, and the two
guards `k ∉ F ∧ |F| < f` agree (D1). -/
theorem regG_corrupt {P : Params} (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (k : Fin P.n) :
    regG u (NetState.corrupt P k w)
      = fun r => GSub.gAct P (Sum.inl (Lab.fail k)) (regG u w r) := by
  funext r
  refine Prod.ext rfl ?_
  change (⟨(NetState.corrupt P k w).pool r, (NetState.corrupt P k w).F⟩ :
      GSub.GNetState P.n) = GSub.GNetState.corrupt P k ⟨w.pool r, w.F⟩
  unfold NetState.corrupt GSub.GNetState.corrupt
  by_cases hc : k ∉ w.F ∧ w.F.card < P.f
  · rw [if_pos hc, if_pos (by exact hc)]
  · rw [if_neg hc, if_neg (by exact hc)]

/-- A node update at `j` is the round loops' one-row update. -/
theorem regC_core {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (j : Fin n)
    (c' : CoreNodeN n) (g' : ℕ → GBCA.ProcNodeN n) :
    regC (Function.update u j (c', g')) = Function.update (regC u) j c' := by
  funext i
  change (Function.update u j (c', g') i).1 = Function.update (regC u) j c' i
  by_cases hi : i = j
  · subst hi; simp only [Function.update_self]
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]; rfl

/-- A node update touching only stage slices leaves the round loops alone. -/
theorem regC_stage {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (j : Fin n)
    (g' : ℕ → GBCA.ProcNodeN n) : regC (Function.update u j ((u j).1, g')) = regC u := by
  rw [regC_core]
  exact Function.update_eq_self j (regC u)

/-- A stage multicast leaves the ABA-side network alone. -/
@[simp] theorem regA_gpool {n : ℕ} (w : NetState n) (r : ℕ) (j : Fin n)
    (m : GBCA.Msg) : regA (w.gpool r j m) = regA w := rfl

/-- A DECIDED pool insert is the ABA-side network's own. -/
@[simp] theorem regA_dput {n : ℕ} (w : NetState n) (j : Fin n) (b : Bool) :
    regA (w.dput j b) = (regA w).dput j b := rfl

/-- Corruption commutes with the regrouping on the ABA-side network (D1). -/
theorem regA_corrupt {P : Params} (w : NetState P.n) (k : Fin P.n) :
    regA (NetState.corrupt P k w) = ANetState.corrupt P k (regA w) := by
  change (⟨(NetState.corrupt P k w).dpool, (NetState.corrupt P k w).F⟩ : ANetState P.n)
      = ANetState.corrupt P k ⟨w.dpool, w.F⟩
  unfold NetState.corrupt ANetState.corrupt
  by_cases hc : k ∉ w.F ∧ w.F.card < P.f
  · rw [if_pos hc, if_pos (by exact hc)]
  · rw [if_neg hc, if_neg (by exact hc)]

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

/-! ### The hidden rendezvous, forwards

Each rendezvous of the deployed system is a silent transition of the layered
one. The two stage rendezvous become *internal* to a round subsystem — they are
hidden inside `GSub.sub` and reach the composite as the family's own `τ` — and
every other rendezvous keeps its label, the four factors answering it
together. -/

theorem layeredGroup_of_event (P : Params) {q : LayeredState P} (e : NetEvt P.n)
    {μ : PMF (LayeredState P)} (h : (layeredPre P).step q (Sum.inr e) μ) :
    (layeredGroup P).step q Lab.tau μ :=
  (layeredGroup_step_iff P _ _ _).mpr (Or.inl ⟨rfl, e, h⟩)

theorem layeredGroup_of_tau (P : Params) {q : LayeredState P} {μ : PMF (LayeredState P)}
    (h : (layeredPre P).step q (Sum.inl Lab.tau) μ) :
    (layeredGroup P).step q Lab.tau μ :=
  (layeredGroup_step_iff P _ _ _).mpr (Or.inr h)

/-- A stage multicast or delivery, forwards: the round-`r` subsystem takes the
rendezvous internally and the other three factors are frozen. -/
theorem layeredGroup_of_gEvent (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n} (r : ℕ)
    {X : GBCA.ImplState P.n}
    (hs : (GSub.sub P r).step (regG u w r) (Sum.inl Lab.tau) (PMF.pure X)) :
    (layeredGroup P).step (regG u w, regC u, regA w, o) Lab.tau
      (PMF.pure (Function.update (regG u w) r X, regC u, regA w, o)) :=
  layeredGroup_of_tau P (layeredPre_tau_gbca P (gbcaSide_tau P _ r hs))

/-- **The forward matching on the rendezvous alphabet.** -/
theorem layeredGroup_of_netEvt (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n} (e : NetEvt P.n)
    {μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (deployedPre P).step (u, w, o) (Sum.inr e) μ) :
    (layeredGroup P).step (regroup (u, w, o)) Lab.tau (μ.map regroup) := by
  obtain ⟨x, w', μ₃, hall, hn, ho, rfl⟩ := deployedPre_event_inv P h
  rw [map_regroup_prod, regroup_apply]
  cases e with
  | gsnd r j m =>
    obtain rfl : w' = w.gpool r j m := pureN_inj (netStep_gsnd hn)
    obtain rfl : μ₃ = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_gsnd r j m) μ₃).mp ho
    rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure]
    have hgo : ∀ {p' : GBCA.ProcNodeN P.n},
        x = Function.update u j ((u j).1, Function.update (u j).2 r p') →
        (∀ i, GSub.GProcStep P r i ((u i).2 r) (Sum.inr (.snd j m))
          (PMF.pure (Function.update (fun i => (u i).2 r) j p' i))) →
        (layeredGroup P).step (regG u w, regC u, regA w, o) Lab.tau
          (PMF.pure (regG x (w.gpool r j m), regC x, regA (w.gpool r j m), o)) := by
      intro p' heq hfam
      subst heq
      rw [regG_stage_mcast u w j _ r p' m, regC_stage, regA_gpool]
      exact layeredGroup_of_gEvent P r
        (GSub.sub_event_step P r (.snd j m) hfam (GSub.GNetStep.snd _ j m))
    have hidle : ∀ i, i ≠ j → GSub.GProcStep P r i ((u i).2 r) (Sum.inr (.snd j m))
          (PMF.pure ((u i).2 r)) :=
      fun i hi => GSub.GProcStep.sndIdle _ j m (Ne.symm hi)
    cases m with
    | input b =>
      obtain ⟨hin, hcnt, hsend, hx0⟩ := stepN_gsnd_input_self (hall j)
      exact hgo (procsN_update hx0 (fun i hi => stepN_gsnd_foreign (Ne.symm hi) (hall i)))
        (gprocs_family (u := fun i => (u i).2 r) j _
          (GSub.GProcStep.sndRelay _ b hin hcnt hsend) hidle)
    | echo b =>
      obtain ⟨hin, hcnt, hsend, hx0⟩ := stepN_gsnd_echo_self (hall j)
      exact hgo (procsN_update hx0 (fun i hi => stepN_gsnd_foreign (Ne.symm hi) (hall i)))
        (gprocs_family (u := fun i => (u i).2 r) j _
          (GSub.GProcStep.sndEcho _ b hin hcnt hsend) hidle)
    | vote v =>
      cases v with
      | some b =>
        obtain ⟨hin, hcnt, hsend, hx0⟩ := stepN_gsnd_voteBit_self (hall j)
        exact hgo (procsN_update hx0 (fun i hi => stepN_gsnd_foreign (Ne.symm hi) (hall i)))
          (gprocs_family (u := fun i => (u i).2 r) j _
            (GSub.GProcStep.sndVoteBit _ b hin hcnt hsend) hidle)
      | none =>
        obtain ⟨hin, hcnt, hval, hsend, hx0⟩ := stepN_gsnd_voteBot_self (hall j)
        exact hgo (procsN_update hx0 (fun i hi => stepN_gsnd_foreign (Ne.symm hi) (hall i)))
          (gprocs_family (u := fun i => (u i).2 r) j _
            (GSub.GProcStep.sndVoteBot _ hin hcnt hval hsend) hidle)
    | bind v =>
      cases v with
      | some b =>
        obtain ⟨hin, hcnt, hsend, hx0⟩ := stepN_gsnd_bindBit_self (hall j)
        exact hgo (procsN_update hx0 (fun i hi => stepN_gsnd_foreign (Ne.symm hi) (hall i)))
          (gprocs_family (u := fun i => (u i).2 r) j _
            (GSub.GProcStep.sndBindBit _ b hin hcnt hsend) hidle)
      | none =>
        obtain ⟨hin, hcnt, hval, hsend, hx0⟩ := stepN_gsnd_bindBot_self (hall j)
        exact hgo (procsN_update hx0 (fun i hi => stepN_gsnd_foreign (Ne.symm hi) (hall i)))
          (gprocs_family (u := fun i => (u i).2 r) j _
            (GSub.GProcStep.sndBindBot _ hin hcnt hval hsend) hidle)
    | «seal» v =>
      cases v with
      | some b =>
        obtain ⟨hin, hcnt, hsend, hx0⟩ := stepN_gsnd_sealBit_self (hall j)
        exact hgo (procsN_update hx0 (fun i hi => stepN_gsnd_foreign (Ne.symm hi) (hall i)))
          (gprocs_family (u := fun i => (u i).2 r) j _
            (GSub.GProcStep.sndSealBit _ b hin hcnt hsend) hidle)
      | none =>
        obtain ⟨hin, hcnt, hval, hsend, hx0⟩ := stepN_gsnd_sealBot_self (hall j)
        exact hgo (procsN_update hx0 (fun i hi => stepN_gsnd_foreign (Ne.symm hi) (hall i)))
          (gprocs_family (u := fun i => (u i).2 r) j _
            (GSub.GProcStep.sndSealBot _ hin hcnt hval hsend) hidle)
  | gdlv r i j m =>
    obtain ⟨hmem, hw⟩ := netStep_gdlv hn
    obtain rfl : w = w' := (pureN_inj hw).symm
    obtain rfl : μ₃ = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_gdlv r i j m) μ₃).mp ho
    rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure]
    obtain rfl := procsN_update (stepN_gdlv_self (hall i))
      (fun k hk => stepN_gdlv_foreign (Ne.symm hk) (hall k))
    rw [regG_stage_still u w i _ r _, regC_stage]
    exact layeredGroup_of_gEvent P r
      (GSub.sub_event_step P r (.dlv i j m)
        (gprocs_family (u := fun k => (u k).2 r) i _
          (GSub.GProcStep.dlvRecv _ j m)
          (fun k hk => GSub.GProcStep.dlvIdle _ i j m (Ne.symm hk)))
        (GSub.GNetStep.dlv _ i j m hmem))
  | dsnd j b =>
    obtain ⟨hpool, hw⟩ := netStep_dsnd hn
    obtain rfl : w' = w.dput j b := pureN_inj hw
    obtain ⟨hcnt, hx0⟩ := stepN_dsnd_self (hall j)
    obtain rfl : u = x := (procsN_id fun i => by
      by_cases hi : i = j
      · subst hi; exact hx0
      · exact stepN_dsnd_foreign (Ne.symm hi) (hall i)).symm
    rw [regG_dput, regA_dput]
    refine layeredGroup_of_event P (.dsnd j b) (layeredPre_vis_step P (by simp)
      (gbcaSide_idle P _ (by simp) (by simp) (by simp [GSub.isFailN])) ?_
      (ANetStep.dsnd _ j b hpool) ho)
    intro i
    by_cases hi : i = j
    · subst hi; exact CoreProcStepN.dsndRelay _ b hcnt
    · exact CoreProcStepN.dsndIdle _ j b (Ne.symm hi)
  | ddlv i j b =>
    obtain ⟨hmem, hw⟩ := netStep_ddlv hn
    obtain rfl : w = w' := (pureN_inj hw).symm
    obtain ⟨hnr, hx0⟩ := stepN_ddlv_self (hall i)
    obtain rfl := procsN_update hx0 (fun k hk => stepN_ddlv_foreign (Ne.symm hk) (hall k))
    rw [regG_core u w w i _ rfl rfl, regC_core]
    exact layeredGroup_of_event P (.ddlv i j b) (layeredPre_vis_step P (by simp)
      (gbcaSide_idle P _ (by simp) (by simp) (by simp [GSub.isFailN]))
      (coresN_family (C := regC u) i _ (CoreProcStepN.ddlvRecv _ j b hnr)
        (fun k hk => CoreProcStepN.ddlvIdle _ i j b (Ne.symm hk)))
      (ANetStep.ddlv _ i j b hmem) ho)
  | retWPub r id c b =>
    obtain rfl : w' = w.dput id b := pureN_inj (netStep_retWPub hn)
    obtain ⟨hph, hr, hg, hx0⟩ := stepN_retWPub_self (hall id)
    obtain rfl := procsN_update hx0
      (fun i hi => stepN_retWPub_foreign (Ne.symm hi) (hall i))
    rw [regG_core u w (w.dput id b) id _ rfl rfl, regC_core, regA_dput]
    exact layeredGroup_of_event P (.retWPub r id c b) (layeredPre_vis_step P (by simp)
      (gbcaSide_idle P _ (by simp) (by simp) (by simp [GSub.isFailN]))
      (coresN_family (C := regC u) id _ (CoreProcStepN.retWPub _ r c b hph hr hg)
        (fun i hi => CoreProcStepN.retWPubIdle _ r id c b (Ne.symm hi)))
      (ANetStep.retWPub _ r id c b) ho)
  | gcallLoop r id b =>
    obtain rfl : w = w' := (pureN_inj (netStep_gcallLoop hn)).symm
    obtain ⟨hph, hr, hest, hx0⟩ := stepN_gcallLoop_self (hall id)
    obtain rfl := procsN_update hx0
      (fun i hi => stepN_gcallLoop_foreign (Ne.symm hi) (hall i))
    rw [regG_core u w w id _ rfl rfl, regC_core]
    refine layeredGroup_of_event P (.gcallLoop r id b) (layeredPre_vis_step P (by simp)
      (gbcaSide_owned_id P _ r (by simp) ?_)
      (coresN_family (C := regC u) id _ (CoreProcStepN.gcallLoop _ r b hph hr hest)
        (fun i hi => CoreProcStepN.gcallLoopIdle _ r id b (Ne.symm hi)))
      (ANetStep.gcallLoop _ r id b) ho)
    exact GSub.sub_lab_step P r (by simp)
      (fun i => GSub.GProcStep.callLoop _ id b) (GSub.GNetStep.gcallLoop _ id b)
  | byzCallG r k b =>
    obtain ⟨hF, hw⟩ := netStep_byzCallG hn
    obtain rfl : w' = w.gpool r k (.input b) := pureN_inj hw
    obtain ⟨hin, hx0⟩ := stepN_byzCallG_self (hall k)
    obtain rfl := procsN_update hx0
      (fun i hi => stepN_byzCallG_foreign (Ne.symm hi) (hall i))
    rw [regG_stage_mcast u w k _ r _ (.input b), regC_stage, regA_gpool]
    refine layeredGroup_of_event P (.byzCallG r k b) (layeredPre_vis_step P (by simp)
      (gbcaSide_owned P _ r (by simp) ?_)
      (fun i => CoreProcStepN.byzCallGIdle _ r k b)
      (ANetStep.byzCallG _ r k b hF) ho)
    exact GSub.sub_lab_step P r (by simp)
      (gprocs_family (u := fun i => (u i).2 r) k _ (GSub.GProcStep.byzCall _ b hin)
        (fun i hi => GSub.GProcStep.byzCallIdle _ k b (Ne.symm hi)))
      (GSub.GNetStep.byzCallG _ k b)
  | byzCallGLoop r k b =>
    obtain ⟨hF, hw⟩ := netStep_byzCallGLoop hn
    obtain rfl : w = w' := (pureN_inj hw).symm
    obtain rfl : u = x := (procsN_id fun i => stepN_byzCallGLoop (hall i)).symm
    refine layeredGroup_of_event P (.byzCallGLoop r k b)
      (layeredPre_vis_step P (by simp) (gbcaSide_owned_id P _ r (by simp) ?_)
        (fun i => CoreProcStepN.byzCallGLoopIdle _ r k b)
        (ANetStep.byzCallGLoop _ r k b hF) ho)
    exact GSub.sub_lab_step P r (by simp)
      (fun i => GSub.GProcStep.byzCallLoop _ k b) (GSub.GNetStep.byzCallGLoop _ k b)
  | byzRetG r k out =>
    obtain ⟨hF, hw⟩ := netStep_byzRetG hn
    obtain rfl : w = w' := (pureN_inj hw).symm
    have hgo : ∀ {p' : GBCA.ProcNodeN P.n},
        x = Function.update u k ((u k).1, Function.update (u k).2 r p') →
        (∀ i, GSub.GProcStep P r i ((u i).2 r) (Sum.inl (Sum.inr (.byzRetG r k out)))
          (PMF.pure (Function.update (fun i => (u i).2 r) k p' i))) →
        (layeredGroup P).step (regG u w, regC u, regA w, o) Lab.tau
          (prodPMF (PMF.pure (regG x w))
            (prodPMF (PMF.pure (regC x)) (prodPMF (PMF.pure (regA w)) μ₃))) := by
      intro p' heq hfam
      subst heq
      rw [regG_stage_still u w k _ r p', regC_stage]
      refine layeredGroup_of_event P (.byzRetG r k out) (layeredPre_vis_step P (by simp)
        (gbcaSide_owned P _ r (by simp) ?_)
        (fun i => CoreProcStepN.byzRetGIdle _ r k out)
        (ANetStep.byzRetG _ r k out hF) ho)
      exact GSub.sub_lab_step P r (by simp) hfam (GSub.GNetStep.byzRetG _ k out)
    have hidle : ∀ i, i ≠ k →
        GSub.GProcStep P r i ((u i).2 r) (Sum.inl (Sum.inr (.byzRetG r k out)))
          (PMF.pure ((u i).2 r)) :=
      fun i hi => GSub.GProcStep.byzRetIdle _ k out (Ne.symm hi)
    cases out with
    | A v =>
      obtain ⟨hcnt, hret, hx0⟩ := stepN_byzRetG_A_self (hall k)
      exact hgo (procsN_update hx0 (fun i hi => stepN_byzRetG_foreign (Ne.symm hi) (hall i)))
        (gprocs_family (u := fun i => (u i).2 r) k _
          (GSub.GProcStep.byzRetA _ v hcnt hret) hidle)
    | B v =>
      obtain ⟨hcnt, honce, hbind, hval, hret, hx0⟩ := stepN_byzRetG_B_self (hall k)
      exact hgo (procsN_update hx0 (fun i hi => stepN_byzRetG_foreign (Ne.symm hi) (hall i)))
        (gprocs_family (u := fun i => (u i).2 r) k _
          (GSub.GProcStep.byzRetB _ v hcnt honce hbind hval hret) hidle)
    | C =>
      obtain ⟨hcnt, hval, hret, hx0⟩ := stepN_byzRetG_C_self (hall k)
      exact hgo (procsN_update hx0 (fun i hi => stepN_byzRetG_foreign (Ne.symm hi) (hall i)))
        (gprocs_family (u := fun i => (u i).2 r) k _
          (GSub.GProcStep.byzRetC _ hcnt hval hret) hidle)
  | byzCallW r k =>
    obtain ⟨hF, hw⟩ := netStep_byzCallW hn
    obtain rfl : w = w' := (pureN_inj hw).symm
    obtain rfl : u = x := (procsN_id fun i => stepN_byzCallW (hall i)).symm
    exact layeredGroup_of_event P (.byzCallW r k) (layeredPre_vis_step P (by simp)
      (gbcaSide_idle P _ (by simp) (by simp) (by simp [GSub.isFailN]))
      (fun i => CoreProcStepN.byzCallWIdle _ r k)
      (ANetStep.byzCallW _ r k hF) ho)
  | byzRetW r k b =>
    obtain ⟨hF, hw⟩ := netStep_byzRetW hn
    obtain rfl : w = w' := (pureN_inj hw).symm
    obtain rfl : u = x := (procsN_id fun i => stepN_byzRetW (hall i)).symm
    exact layeredGroup_of_event P (.byzRetW r k b) (layeredPre_vis_step P (by simp)
      (gbcaSide_idle P _ (by simp) (by simp) (by simp [GSub.isFailN]))
      (fun i => CoreProcStepN.byzRetWIdle _ r k b)
      (ANetStep.byzRetW _ r k b hF) ho)

/-! ### The shared labels, forwards

A label of the shared alphabet is answered by the layered system on the same
label: the round subsystems take the graded-agreement handshakes, the round
loops take the ABA API and the coin handshakes, and `fail` is a broadcast on
one side and a joint step of all four factors on the other, every copy of the
corrupted set being the network adversary's one set. -/

/-- **The forward matching before the hiding.** -/
theorem layeredPre_of_deployedPre (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n} {l : Lab P.n}
    {μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (deployedPre P).step (u, w, o) (Sum.inl l) μ) :
    (layeredPre P).step (regroup (u, w, o)) (Sum.inl l) (μ.map regroup) := by
  rw [regroup_apply]
  by_cases hl : l = Lab.tau
  · subst hl
    rcases deployedPre_tau_inv P h with ⟨w', hnet, rfl⟩ | ⟨ω, hW, rfl⟩
    · rw [map_regroup_pure]
      rcases netStep_tau hnet with ⟨r, k, m, hF, hw⟩ | ⟨k, b, hF, hw⟩
      · obtain rfl : w' = w.gpool r k m := pureN_inj hw
        rw [regG_mcast u w r k m, regA_gpool]
        exact layeredPre_tau_gbca P (gbcaSide_tau P _ r
          (GSub.sub_tau_net P r (GSub.GNetStep.byzG _ k m hF)))
      · obtain rfl : w' = w.dput k b := pureN_inj hw
        rw [regG_dput, regA_dput]
        exact layeredPre_tau_aNet P (ANetStep.byzD _ k b hF)
    · rw [map_regroup_prod]
      exact layeredPre_tau_wcc P hW
  · obtain ⟨x, w', ω, hall, hn, hW, rfl⟩ := deployedPre_lab_inv P hl h
    rw [map_regroup_prod]
    cases l with
    | tau => exact absurd rfl hl
    | callABA id b =>
      obtain rfl : w = w' := (pureN_inj (netStep_callABA hn)).symm
      have hWl := (System.mapIdle_step_some (wccPull_inl (Lab.callABA id b)) ω).mpr hW
      rcases stepN_callABA_own (hall id) with ⟨hin, hx0⟩ | hx0
      · obtain rfl := procsN_update hx0
          (fun i hi => stepN_callABA_foreign (Ne.symm hi) (hall i))
        rw [regG_core u w w id _ rfl rfl, regC_core]
        exact layeredPre_vis_step P (by simp)
          (gbcaSide_idle P _ (by simp) (by simp) (by simp [GSub.isFailN]))
          (coresN_family (C := regC u) id _ (CoreProcStepN.input _ b hin)
            (fun i hi => CoreProcStepN.callABAIdle _ id b (Ne.symm hi)))
          (ANetStep.callABAIdle _ id b) hWl
      · obtain rfl : u = x := (procsN_id fun i => by
          by_cases hi : i = id
          · subst hi; exact hx0
          · exact stepN_callABA_foreign (Ne.symm hi) (hall i)).symm
        refine layeredPre_vis_step P (by simp)
          (gbcaSide_idle P _ (by simp) (by simp) (by simp [GSub.isFailN])) ?_
          (ANetStep.callABAIdle _ id b) hWl
        intro i
        by_cases hi : i = id
        · subst hi; exact CoreProcStepN.inputLoop _ b
        · exact CoreProcStepN.callABAIdle _ id b (Ne.symm hi)
    | retABA id b =>
      obtain ⟨hpool, hw⟩ := netStep_retABA hn
      obtain rfl : w = w' := (pureN_inj hw).symm
      obtain ⟨hcnt, hret, hx0⟩ := stepN_retABA_own (hall id)
      obtain rfl := procsN_update hx0
        (fun i hi => stepN_retABA_foreign (Ne.symm hi) (hall i))
      rw [regG_core u w w id _ rfl rfl, regC_core]
      exact layeredPre_vis_step P (by simp)
        (gbcaSide_idle P _ (by simp) (by simp) (by simp [GSub.isFailN]))
        (coresN_family (C := regC u) id _ (CoreProcStepN.ret _ b hcnt hret)
          (fun i hi => CoreProcStepN.retABAIdle _ id b (Ne.symm hi)))
        (ANetStep.retABA _ id b hpool)
        ((System.mapIdle_step_some (wccPull_inl (Lab.retABA id b)) ω).mpr hW)
    | callG r id b =>
      obtain rfl : w' = w.gpool r id (.input b) := pureN_inj (netStep_callG hn)
      obtain ⟨hph, hr, hest, hin, hx0⟩ := stepN_callG_own (hall id)
      obtain rfl := procsN_update hx0
        (fun i hi => stepN_callG_foreign (Ne.symm hi) (hall i))
      rw [regG_stage_mcast u w id _ r _ (.input b), regC_core, regA_gpool]
      refine layeredPre_vis_step P (by simp) (gbcaSide_owned P _ r (by simp) ?_)
        (coresN_family (C := regC u) id _ (CoreProcStepN.callG _ r b hph hr hest)
          (fun i hi => CoreProcStepN.callGIdle _ r id b (Ne.symm hi)))
        (ANetStep.callGIdle _ r id b)
        ((System.mapIdle_step_some (wccPull_inl (Lab.callG r id b)) ω).mpr hW)
      exact GSub.sub_lab_step P r (by simp)
        (gprocs_family (u := fun i => (u i).2 r) id _ (GSub.GProcStep.call _ b hin)
          (fun i hi => GSub.GProcStep.callIdle _ id b (Ne.symm hi)))
        (GSub.GNetStep.callG _ id b)
    | retG r id out =>
      obtain rfl : w = w' := (pureN_inj (netStep_retG hn)).symm
      have hWl := (System.mapIdle_step_some (wccPull_inl (Lab.retG r id out)) ω).mpr hW
      have hgo : ∀ {p' : GBCA.ProcNodeN P.n} {c' : CoreNodeN P.n},
          x = Function.update u id (c', Function.update (u id).2 r p') →
          (∀ i, GSub.GProcStep P r i ((u i).2 r) (Sum.inl (Sum.inl (.retG r id out)))
            (PMF.pure (Function.update (fun i => (u i).2 r) id p' i))) →
          (∀ i, CoreProcStepN P i (regC u i) (Sum.inl (.retG r id out))
            (PMF.pure (Function.update (regC u) id c' i))) →
          (layeredPre P).step (regG u w, regC u, regA w, o) (Sum.inl (.retG r id out))
            (prodPMF (PMF.pure (regG x w))
              (prodPMF (PMF.pure (regC x)) (prodPMF (PMF.pure (regA w)) ω))) := by
        intro p' c' heq hfam hcore
        subst heq
        rw [regG_stage_still u w id _ r p', regC_core]
        refine layeredPre_vis_step P (by simp) (gbcaSide_owned P _ r (by simp) ?_)
          hcore (ANetStep.retGIdle _ r id out) hWl
        exact GSub.sub_lab_step P r (by simp) hfam (GSub.GNetStep.retGIdle _ id out)
      have hidle : ∀ i, i ≠ id →
          GSub.GProcStep P r i ((u i).2 r) (Sum.inl (Sum.inl (.retG r id out)))
            (PMF.pure ((u i).2 r)) :=
        fun i hi => GSub.GProcStep.retIdle _ id out (Ne.symm hi)
      have hcidle : ∀ i, i ≠ id →
          CoreProcStepN P i (regC u i) (Sum.inl (.retG r id out)) (PMF.pure (regC u i)) :=
        fun i hi => CoreProcStepN.retGIdle _ r id out (Ne.symm hi)
      cases out with
      | A v =>
        obtain ⟨hph, hr, hcnt, hret, hx0⟩ := stepN_retG_A_own (hall id)
        exact hgo (procsN_update hx0 (fun i hi => stepN_retG_foreign (Ne.symm hi) (hall i)))
          (gprocs_family (u := fun i => (u i).2 r) id _
            (GSub.GProcStep.retA _ v hcnt hret) hidle)
          (coresN_family (C := regC u) id _ (CoreProcStepN.retG _ r (.A v) hph hr) hcidle)
      | B v =>
        obtain ⟨hph, hr, hcnt, honce, hbind, hval, hret, hx0⟩ := stepN_retG_B_own (hall id)
        exact hgo (procsN_update hx0 (fun i hi => stepN_retG_foreign (Ne.symm hi) (hall i)))
          (gprocs_family (u := fun i => (u i).2 r) id _
            (GSub.GProcStep.retB _ v hcnt honce hbind hval hret) hidle)
          (coresN_family (C := regC u) id _ (CoreProcStepN.retG _ r (.B v) hph hr) hcidle)
      | C =>
        obtain ⟨hph, hr, hcnt, hval, hret, hx0⟩ := stepN_retG_C_own (hall id)
        exact hgo (procsN_update hx0 (fun i hi => stepN_retG_foreign (Ne.symm hi) (hall i)))
          (gprocs_family (u := fun i => (u i).2 r) id _
            (GSub.GProcStep.retC _ hcnt hval hret) hidle)
          (coresN_family (C := regC u) id _ (CoreProcStepN.retG _ r .C hph hr) hcidle)
    | callW r id =>
      obtain rfl : w = w' := (pureN_inj (netStep_callW hn)).symm
      obtain ⟨hph, hr, hx0⟩ := stepN_callW_own (hall id)
      obtain rfl := procsN_update hx0
        (fun i hi => stepN_callW_foreign (Ne.symm hi) (hall i))
      rw [regG_core u w w id _ rfl rfl, regC_core]
      exact layeredPre_vis_step P (by simp)
        (gbcaSide_idle P _ (by simp) (by simp) (by simp [GSub.isFailN]))
        (coresN_family (C := regC u) id _ (CoreProcStepN.callW _ r hph hr)
          (fun i hi => CoreProcStepN.callWIdle _ r id (Ne.symm hi)))
        (ANetStep.callWIdle _ r id)
        ((System.mapIdle_step_some (wccPull_inl (Lab.callW r id)) ω).mpr hW)
    | retW r id c =>
      obtain rfl : w = w' := (pureN_inj (netStep_retW hn)).symm
      obtain ⟨hph, hr, hgr, hx0⟩ := stepN_retW_own (hall id)
      obtain rfl := procsN_update hx0
        (fun i hi => stepN_retW_foreign (Ne.symm hi) (hall i))
      rw [regG_core u w w id _ rfl rfl, regC_core]
      exact layeredPre_vis_step P (by simp)
        (gbcaSide_idle P _ (by simp) (by simp) (by simp [GSub.isFailN]))
        (coresN_family (C := regC u) id _ (CoreProcStepN.retW _ r c hph hr hgr)
          (fun i hi => CoreProcStepN.retWIdle _ r id c (Ne.symm hi)))
        (ANetStep.retWIdle _ r id c)
        ((System.mapIdle_step_some (wccPull_inl (Lab.retW r id c)) ω).mpr hW)
    | fail k =>
      obtain rfl : w' = NetState.corrupt P k w := pureN_inj (netStep_fail hn)
      obtain rfl : u = x := (procsN_id fun i => stepN_fail (hall i)).symm
      rw [regG_corrupt, regA_corrupt]
      exact layeredPre_vis_step P (by simp) (gbcaSide_fail P _ k)
        (fun i => CoreProcStepN.failIdle _ k) (ANetStep.fail _ k)
        ((System.mapIdle_step_some (wccPull_inl (Lab.fail k)) ω).mpr hW)

/-! ### The forward simulation

The regrouping is a step-commuting state map: every deployed transition is the
layered system's transition on the same label, its successor distribution
pushed forward. -/

/-- The forward matching at the level of the two groups. -/
theorem layeredGroupForward (P : Params) :
    ∀ s l μ, (deployedGroup P).step s l μ →
      (layeredGroup P).step (regroup s) l (μ.map regroup) := by
  rintro ⟨u, w, o⟩ l μ h
  rw [deployedGroup_step_iff] at h
  rcases h with ⟨rfl, e, hpre⟩ | hpre
  · exact layeredGroup_of_netEvt P e hpre
  · exact (layeredGroup_step_iff P _ _ _).mpr (Or.inr (layeredPre_of_deployedPre P hpre))

/-- **The forward matching**: every transition of the deployed system is the
matching transition of the layered system along the regrouping. -/
theorem layeredForward (P : Params) :
    ∀ s l μ, (deployed P).step s l μ →
      (layered P).step (regroup s) l (μ.map regroup) :=
  strongForward_abstract regroup (Lab.hiddenAPI P.n) (layeredGroupForward P)

/-! ### Building a deployed transition

The forward direction reads a deployed transition into the layered factors;
the converse must build one. -/

theorem deployedGroup_of_event (P : Params)
    {q : (∀ _ : Fin P.n, ABANodeN P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n))}
    (e : NetEvt P.n)
    {μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (deployedPre P).step q (Sum.inr e) μ) : (deployedGroup P).step q Lab.tau μ :=
  (deployedGroup_step_iff P _ _ _).mpr (Or.inl ⟨rfl, e, h⟩)

theorem deployedGroup_of_lab (P : Params)
    {q : (∀ _ : Fin P.n, ABANodeN P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n))}
    {l : Lab P.n}
    {μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (deployedPre P).step q (Sum.inl l) μ) : (deployedGroup P).step q l μ :=
  (deployedGroup_step_iff P _ _ _).mpr (Or.inr h)

/-- Build a joint transition of the three deployed factors on any visible
label, the oracle's successor left arbitrary. -/
theorem deployedPre_vis_step (P : Params) {u x : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} {L : NLab P.n} (hL : L ≠ Silent.τ)
    (hall : ∀ i, ABAProcStepN P i (u i) L (PMF.pure (x i)))
    (hn : NetStep P w L (PMF.pure w'))
    (ho : (wccLift P).step o L ω) :
    (deployedPre P).step (u, w, o) L
      (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω)) := by
  rw [deployedPre, System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure x, prodPMF (PMF.pure w') ω, syncN_pure hL hall, ?_, rfl⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure w', ω, hn, ho, rfl⟩

/-! ### Reading a round subsystem's transition backwards -/

/-- A visible transition of the round-`r` subsystem: every stage program and
the fabric move together. -/
theorem sub_vis_inv (P : Params) (r : ℕ) {U : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n}
    {W : GSub.GNetState P.n} {L : NLab P.n} (hL : L ≠ Sum.inl Lab.tau)
    {μ : PMF (GBCA.ImplState P.n)} (h : (GSub.sub P r).step (U, W) L μ) :
    ∃ (X : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n) (W' : GSub.GNetState P.n),
      μ = PMF.pure (X, W') ∧
      (∀ i, GSub.GProcStep P r i (U i) (Sum.inl L) (PMF.pure (X i))) ∧
      GSub.GNetStep P r W (Sum.inl L) (PMF.pure W') := by
  rcases (GSub.sub_step_iff P r (U, W) L μ).mp h with ⟨hτ, -⟩ | hlab
  · exact absurd hτ hL
  · exact GSub.subPre_joint_inv
      (by simp only [GSub.glab_tau]; exact fun hc => hL (Sum.inl_injective hc)) hlab

/-- A silent transition of the round-`r` subsystem: a hidden rendezvous of the
stage programs with the fabric, or the fabric's own injection. -/
theorem sub_tau_inv (P : Params) (r : ℕ) {U : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n}
    {W : GSub.GNetState P.n} {μ : PMF (GBCA.ImplState P.n)}
    (h : (GSub.sub P r).step (U, W) (Sum.inl Lab.tau) μ) :
    (∃ (e : GSub.GEvt P.n) (X : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n)
        (W' : GSub.GNetState P.n), μ = PMF.pure (X, W') ∧
      (∀ i, GSub.GProcStep P r i (U i) (Sum.inr e) (PMF.pure (X i))) ∧
      GSub.GNetStep P r W (Sum.inr e) (PMF.pure W')) ∨
    (∃ W' : GSub.GNetState P.n, μ = PMF.pure (U, W') ∧
      GSub.GNetStep P r W (Sum.inl (Sum.inl Lab.tau)) (PMF.pure W')) := by
  rcases (GSub.sub_step_iff P r (U, W) (Sum.inl Lab.tau) μ).mp h with ⟨-, e, hev⟩ | hlab
  · obtain ⟨X, W', hμ, hall, hn⟩ := GSub.subPre_joint_inv (by simp) hev
    exact Or.inl ⟨e, X, W', hμ, hall, hn⟩
  · obtain ⟨W', hμ, hn⟩ := GSub.subPre_tau_inv hlab
    exact Or.inr ⟨W', hμ, hn⟩

/-! ### The converse on the rendezvous alphabet

The two stage rendezvous of the deployed alphabet carry no transition of the
layered system — the ABA-side network has no row for them, so the
synchronisation is unsatisfiable. Every other rendezvous is answered by the
deployed system on the same label. -/

theorem deployedGroupConverse_netEvt (P : Params) (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) (e : NetEvt P.n)
    {μ : PMF (LayeredState P)}
    (h : (layeredPre P).step (regroup (u, w, o)) (Sum.inr e) μ) :
    ∃ ν, (deployedGroup P).step (u, w, o) Lab.tau ν ∧ μ = ν.map regroup := by
  rw [regroup_apply] at h
  obtain ⟨G', C', A', ω, hG, hC, hA, hW, rfl⟩ := layeredPre_vis_inv P (by simp) h
  cases e with
  | gsnd r j m => exact (aStep_gsnd_dead hA).elim
  | gdlv r i j m => exact (aStep_gdlv_dead hA).elim
  | dsnd j b =>
    obtain ⟨hpool, hA'⟩ := aStep_dsnd hA
    obtain rfl : A' = (regA w).dput j b := pureN_inj hA'
    obtain rfl : G' = regG u w :=
      pureN_inj (gbcaSide_idle_inv P (by simp) (by simp) (by simp [GSub.isFailN]) hG)
    obtain ⟨hcnt, hC0⟩ := stepC_dsnd_self (hC j)
    obtain rfl : C' = regC u := coresN_id fun i => by
      by_cases hi : i = j
      · subst hi; exact hC0
      · exact stepC_dsnd_foreign (Ne.symm hi) (hC i)
    have hall : ∀ i, ABAProcStepN P i (u i) (Sum.inr (NetEvt.dsnd j b))
        (PMF.pure (u i)) := by
      intro i
      by_cases hi : i = j
      · subst hi; exact ABAProcStepN.dsndRelay _ _ b hcnt
      · exact ABAProcStepN.dsndIdle _ _ j b (Ne.symm hi)
    refine ⟨_, deployedGroup_of_event P (.dsnd j b)
      (deployedPre_vis_step P (by simp) hall (NetStep.dsnd w j b hpool) hW), ?_⟩
    rw [map_regroup_prod, regG_dput, regA_dput]
  | ddlv i j b =>
    obtain ⟨hmem, hA'⟩ := aStep_ddlv hA
    obtain rfl : A' = regA w := pureN_inj hA'
    obtain rfl : G' = regG u w :=
      pureN_inj (gbcaSide_idle_inv P (by simp) (by simp) (by simp [GSub.isFailN]) hG)
    obtain ⟨hnr, hC0⟩ := stepC_ddlv_self (hC i)
    obtain rfl := coresN_update hC0 (fun k hk => stepC_ddlv_foreign (Ne.symm hk) (hC k))
    refine ⟨_, deployedGroup_of_event P (.ddlv i j b)
      (deployedPre_vis_step P (by simp)
        (procsN_family i _ (ABAProcStepN.ddlvRecv _ _ j b hnr)
          (fun k hk => ABAProcStepN.ddlvIdle _ _ i j b (Ne.symm hk)))
        (NetStep.ddlv w i j b hmem) hW), ?_⟩
    rw [map_regroup_prod, regG_core u w w i _ rfl rfl, regC_core]
    rfl
  | retWPub r id c b =>
    obtain rfl : A' = (regA w).dput id b := pureN_inj (aStep_retWPub hA)
    obtain rfl : G' = regG u w :=
      pureN_inj (gbcaSide_idle_inv P (by simp) (by simp) (by simp [GSub.isFailN]) hG)
    obtain ⟨hph, hr, hg, hC0⟩ := stepC_retWPub_self (hC id)
    obtain rfl := coresN_update hC0 (fun i hi => stepC_retWPub_foreign (Ne.symm hi) (hC i))
    refine ⟨_, deployedGroup_of_event P (.retWPub r id c b)
      (deployedPre_vis_step P (by simp)
        (procsN_family id _ (ABAProcStepN.retWPub _ _ r c b hph hr hg)
          (fun i hi => ABAProcStepN.retWPubIdle _ _ r id c b (Ne.symm hi)))
        (NetStep.retWPub w r id c b) hW), ?_⟩
    rw [map_regroup_prod, regG_core u w (w.dput id b) id _ rfl rfl, regC_core, regA_dput]
    rfl
  | gcallLoop r id b =>
    obtain rfl : A' = regA w := pureN_inj (aStep_gcallLoop hA)
    obtain ⟨X, hsub, hG'⟩ := gbcaSide_owned_inv P (r := r) (by simp) (by simp) hG
    obtain ⟨Y, W', hX, hgall, hgn⟩ := sub_vis_inv P r
      (U := fun i => (u i).2 r) (W := ⟨w.pool r, w.F⟩) (by simp) hsub
    obtain rfl : X = (Y, W') := pureN_inj (by rw [← hX])
    obtain rfl : W' = ⟨w.pool r, w.F⟩ := GSub.pure_inj (GSub.netG_gcallLoop hgn)
    obtain rfl : Y = fun i => (u i).2 r :=
      gprocs_id fun i => GSub.stepG_gcallLoop (hgall i)
    rw [show Function.update (regG u w) r
        ((fun i => (u i).2 r : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n),
          (⟨w.pool r, w.F⟩ : GSub.GNetState P.n)) = regG u w from
      Function.update_eq_self r (regG u w)] at hG'
    obtain rfl : G' = regG u w := pureN_inj hG'
    obtain ⟨hph, hr, hest, hC0⟩ := stepC_gcallLoop_self (hC id)
    obtain rfl := coresN_update hC0 (fun i hi => stepC_gcallLoop_foreign (Ne.symm hi) (hC i))
    refine ⟨_, deployedGroup_of_event P (.gcallLoop r id b)
      (deployedPre_vis_step P (by simp)
        (procsN_family id _ (ABAProcStepN.gcallLoop _ _ r b hph hr hest)
          (fun i hi => ABAProcStepN.gcallLoopIdle _ _ r id b (Ne.symm hi)))
        (NetStep.gcallLoop w r id b) hW), ?_⟩
    rw [map_regroup_prod, regG_core u w w id _ rfl rfl, regC_core]
    rfl
  | byzCallG r k b =>
    obtain ⟨hF, hA'⟩ := aStep_byzCallG hA
    obtain rfl : A' = regA w := pureN_inj hA'
    obtain ⟨X, hsub, hG'⟩ := gbcaSide_owned_inv P (r := r) (by simp) (by simp) hG
    obtain ⟨Y, W', hX, hgall, hgn⟩ := sub_vis_inv P r
      (U := fun i => (u i).2 r) (W := ⟨w.pool r, w.F⟩) (by simp) hsub
    obtain rfl : X = (Y, W') := pureN_inj (by rw [← hX])
    obtain rfl : W' = (⟨w.pool r, w.F⟩ : GSub.GNetState P.n).gpool k (.input b) :=
      GSub.pure_inj (GSub.netG_byzCallG hgn)
    obtain ⟨hin, hY⟩ := GSub.stepG_byzCallG_own (hgall k)
    obtain rfl := gprocs_update hY
      (fun i hi => GSub.stepG_byzCallG_foreign (Ne.symm hi) (hgall i))
    obtain rfl : C' = regC u := coresN_id fun i => stepC_byzCallG (hC i)
    obtain rfl := pureN_inj hG'
    refine ⟨_, deployedGroup_of_event P (.byzCallG r k b)
      (deployedPre_vis_step P (by simp)
        (procsN_family k _ (ABAProcStepN.byzCallG _ _ r b hin)
          (fun i hi => ABAProcStepN.byzCallGIdle _ _ r k b (Ne.symm hi)))
        (NetStep.byzCallG w r k b hF) hW), ?_⟩
    rw [map_regroup_prod, regG_stage_mcast u w k _ r _ (.input b), regC_stage, regA_gpool]
    rfl
  | byzCallGLoop r k b =>
    obtain ⟨hF, hA'⟩ := aStep_byzCallGLoop hA
    obtain rfl : A' = regA w := pureN_inj hA'
    obtain ⟨X, hsub, hG'⟩ := gbcaSide_owned_inv P (r := r) (by simp) (by simp) hG
    obtain ⟨Y, W', hX, hgall, hgn⟩ := sub_vis_inv P r
      (U := fun i => (u i).2 r) (W := ⟨w.pool r, w.F⟩) (by simp) hsub
    obtain rfl : X = (Y, W') := pureN_inj (by rw [← hX])
    obtain rfl : W' = ⟨w.pool r, w.F⟩ := GSub.pure_inj (GSub.netG_byzCallGLoop hgn)
    obtain rfl : Y = fun i => (u i).2 r :=
      gprocs_id fun i => GSub.stepG_byzCallGLoop (hgall i)
    rw [show Function.update (regG u w) r
        ((fun i => (u i).2 r : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n),
          (⟨w.pool r, w.F⟩ : GSub.GNetState P.n)) = regG u w from
      Function.update_eq_self r (regG u w)] at hG'
    obtain rfl : G' = regG u w := pureN_inj hG'
    obtain rfl : C' = regC u := coresN_id fun i => stepC_byzCallGLoop (hC i)
    refine ⟨_, deployedGroup_of_event P (.byzCallGLoop r k b)
      (deployedPre_vis_step P (by simp)
        (fun i => ABAProcStepN.byzCallGLoopIdle _ _ r k b)
        (NetStep.byzCallGLoop w r k b hF) hW), ?_⟩
    rw [map_regroup_prod]
  | byzRetG r k out =>
    obtain ⟨hF, hA'⟩ := aStep_byzRetG hA
    obtain rfl : A' = regA w := pureN_inj hA'
    obtain ⟨X, hsub, hG'⟩ := gbcaSide_owned_inv P (r := r) (by simp) (by simp) hG
    obtain ⟨Y, W', hX, hgall, hgn⟩ := sub_vis_inv P r
      (U := fun i => (u i).2 r) (W := ⟨w.pool r, w.F⟩) (by simp) hsub
    obtain rfl : X = (Y, W') := pureN_inj (by rw [← hX])
    obtain rfl : W' = ⟨w.pool r, w.F⟩ := GSub.pure_inj (GSub.netG_byzRetG hgn)
    obtain rfl : C' = regC u := coresN_id fun i => stepC_byzRetG (hC i)
    obtain rfl := pureN_inj hG'
    have hidle : ∀ i, i ≠ k →
        (PMF.pure (Y i) : PMF (GBCA.ProcNodeN P.n)) = PMF.pure ((u i).2 r) :=
      fun i hi => GSub.stepG_byzRetG_foreign (Ne.symm hi) (hgall i)
    have hgo : ∀ (nd : GBCA.ProcNodeN P.n),
        Y = Function.update (fun i => (u i).2 r) k nd →
        ABAProcStepN P k (u k) (Sum.inr (.byzRetG r k out))
          (PMF.pure ((u k).1, Function.update (u k).2 r nd)) →
        ∃ ν, (deployedGroup P).step (u, w, o) Lab.tau ν ∧
          prodPMF (PMF.pure (Function.update (regG u w) r (Y, ⟨w.pool r, w.F⟩)))
            (prodPMF (PMF.pure (regC u)) (prodPMF (PMF.pure (regA w)) ω))
            = ν.map regroup := by
      rintro nd rfl hown
      refine ⟨_, deployedGroup_of_event P (.byzRetG r k out)
        (deployedPre_vis_step P (by simp)
          (procsN_family k _ hown
            (fun i hi => ABAProcStepN.byzRetGIdle _ _ r k out (Ne.symm hi)))
          (NetStep.byzRetG w r k out hF) hW), ?_⟩
      rw [map_regroup_prod, regG_stage_still u w k _ r nd, regC_stage]
      rfl
    cases out with
    | A v =>
      obtain ⟨hcnt, hret, hY⟩ := GSub.stepG_byzRetG_A_own (hgall k)
      exact hgo _ (gprocs_update hY hidle) (ABAProcStepN.byzRetG_A _ _ r v hcnt hret)
    | B v =>
      obtain ⟨hcnt, honce, hbind, hval, hret, hY⟩ := GSub.stepG_byzRetG_B_own (hgall k)
      exact hgo _ (gprocs_update hY hidle)
        (ABAProcStepN.byzRetG_B _ _ r v hcnt honce hbind hval hret)
    | C =>
      obtain ⟨hcnt, hval, hret, hY⟩ := GSub.stepG_byzRetG_C_own (hgall k)
      exact hgo _ (gprocs_update hY hidle) (ABAProcStepN.byzRetG_C _ _ r hcnt hval hret)
  | byzCallW r k =>
    obtain ⟨hF, hA'⟩ := aStep_byzCallW hA
    obtain rfl : A' = regA w := pureN_inj hA'
    obtain rfl : G' = regG u w :=
      pureN_inj (gbcaSide_idle_inv P (by simp) (by simp) (by simp [GSub.isFailN]) hG)
    obtain rfl : C' = regC u := coresN_id fun i => stepC_byzCallW (hC i)
    refine ⟨_, deployedGroup_of_event P (.byzCallW r k)
      (deployedPre_vis_step P (by simp) (fun i => ABAProcStepN.byzCallWIdle _ _ r k)
        (NetStep.byzCallW w r k hF) hW), ?_⟩
    rw [map_regroup_prod]
  | byzRetW r k b =>
    obtain ⟨hF, hA'⟩ := aStep_byzRetW hA
    obtain rfl : A' = regA w := pureN_inj hA'
    obtain rfl : G' = regG u w :=
      pureN_inj (gbcaSide_idle_inv P (by simp) (by simp) (by simp [GSub.isFailN]) hG)
    obtain rfl : C' = regC u := coresN_id fun i => stepC_byzRetW (hC i)
    refine ⟨_, deployedGroup_of_event P (.byzRetW r k b)
      (deployedPre_vis_step P (by simp) (fun i => ABAProcStepN.byzRetWIdle _ _ r k b)
        (NetStep.byzRetW w r k b hF) hW), ?_⟩
    rw [map_regroup_prod]

/-! ### The converse on the silent label

A silent transition of the layered system is one factor's own silent rule.
The graded-agreement side's is a round subsystem's, which is either one of the
two rendezvous hidden inside it — reappearing as a deployed `gsnd` or `gdlv` —
or that round's fabric injection. -/

theorem deployedGroupConverse_tau (P : Params) (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) {μ : PMF (LayeredState P)}
    (h : (layeredPre P).step (regroup (u, w, o)) (Sum.inl Lab.tau) μ) :
    ∃ ν, (deployedGroup P).step (u, w, o) Lab.tau ν ∧ μ = ν.map regroup := by
  rw [regroup_apply] at h
  rcases layeredPre_tau_inv P h with ⟨G', hG, rfl⟩ | ⟨A', hA, rfl⟩ | ⟨ω, hW, rfl⟩
  · obtain ⟨r, X, hsub, hG'⟩ := gbcaSide_tau_inv P hG
    obtain rfl := pureN_inj hG'
    rcases sub_tau_inv P r (U := fun i => (u i).2 r) (W := ⟨w.pool r, w.F⟩) hsub with
      ⟨e, Y, W', hX, hgall, hgn⟩ | ⟨W', hX, hgn⟩
    · obtain rfl : X = (Y, W') := pureN_inj (by rw [← hX])
      cases e with
      | snd j m =>
        obtain rfl : W' = (⟨w.pool r, w.F⟩ : GSub.GNetState P.n).gpool j m :=
          GSub.pure_inj (GSub.netG_snd hgn)
        have hgo : ∀ {p' : GBCA.ProcNodeN P.n},
            Y = Function.update (fun i => (u i).2 r) j p' →
            ABAProcStepN P j (u j) (Sum.inr (.gsnd r j m))
              (PMF.pure ((u j).1, Function.update (u j).2 r p')) →
            ∃ ν, (deployedGroup P).step (u, w, o) Lab.tau ν ∧
              (PMF.pure (Function.update (regG u w) r
                  (Y, (⟨w.pool r, w.F⟩ : GSub.GNetState P.n).gpool j m),
                regC u, regA w, o) : PMF (LayeredState P)) = ν.map regroup := by
          intro p' heq hown
          subst heq
          refine ⟨_, deployedGroup_of_event P (.gsnd r j m)
            (deployedPre_vis_step P (by simp)
              (procsN_family j _ hown
                (fun i hi => ABAProcStepN.gsndIdle _ _ r j m (Ne.symm hi)))
              (NetStep.gsnd w r j m) (wccLift_idle P o (wccPull_gsnd r j m))), ?_⟩
          rw [map_regroup_prod, prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure,
            regG_stage_mcast u w j _ r p' m, regC_stage, regA_gpool]
          rfl
        have hidle : ∀ i, i ≠ j →
            (PMF.pure (Y i) : PMF (GBCA.ProcNodeN P.n)) = PMF.pure ((u i).2 r) :=
          fun i hi => GSub.stepG_snd_foreign (Ne.symm hi) (hgall i)
        cases m with
        | input b =>
          obtain ⟨hin, hcnt, hsend, hY⟩ := GSub.stepG_snd_input_own (hgall j)
          exact hgo (gprocs_update hY hidle)
            (ABAProcStepN.gsndRelay _ _ r b hin hcnt hsend)
        | echo b =>
          obtain ⟨hin, hcnt, hsend, hY⟩ := GSub.stepG_snd_echo_own (hgall j)
          exact hgo (gprocs_update hY hidle)
            (ABAProcStepN.gsndEcho _ _ r b hin hcnt hsend)
        | vote v =>
          cases v with
          | some b =>
            obtain ⟨hin, hcnt, hsend, hY⟩ := GSub.stepG_snd_voteBit_own (hgall j)
            exact hgo (gprocs_update hY hidle)
              (ABAProcStepN.gsndVoteBit _ _ r b hin hcnt hsend)
          | none =>
            obtain ⟨hin, hcnt, hval, hsend, hY⟩ := GSub.stepG_snd_voteBot_own (hgall j)
            exact hgo (gprocs_update hY hidle)
              (ABAProcStepN.gsndVoteBot _ _ r hin hcnt hval hsend)
        | bind v =>
          cases v with
          | some b =>
            obtain ⟨hin, hcnt, hsend, hY⟩ := GSub.stepG_snd_bindBit_own (hgall j)
            exact hgo (gprocs_update hY hidle)
              (ABAProcStepN.gsndBindBit _ _ r b hin hcnt hsend)
          | none =>
            obtain ⟨hin, hcnt, hval, hsend, hY⟩ := GSub.stepG_snd_bindBot_own (hgall j)
            exact hgo (gprocs_update hY hidle)
              (ABAProcStepN.gsndBindBot _ _ r hin hcnt hval hsend)
        | «seal» v =>
          cases v with
          | some b =>
            obtain ⟨hin, hcnt, hsend, hY⟩ := GSub.stepG_snd_sealBit_own (hgall j)
            exact hgo (gprocs_update hY hidle)
              (ABAProcStepN.gsndSealBit _ _ r b hin hcnt hsend)
          | none =>
            obtain ⟨hin, hcnt, hval, hsend, hY⟩ := GSub.stepG_snd_sealBot_own (hgall j)
            exact hgo (gprocs_update hY hidle)
              (ABAProcStepN.gsndSealBot _ _ r hin hcnt hval hsend)
      | dlv i j m =>
        obtain ⟨hmem, hW'⟩ := GSub.netG_dlv hgn
        obtain rfl : W' = (⟨w.pool r, w.F⟩ : GSub.GNetState P.n) := GSub.pure_inj hW'
        obtain rfl := gprocs_update (GSub.stepG_dlv_own (hgall i))
          (fun k hk => GSub.stepG_dlv_foreign (Ne.symm hk) (hgall k))
        refine ⟨_, deployedGroup_of_event P (.gdlv r i j m)
          (deployedPre_vis_step P (by simp)
            (procsN_family i _ (ABAProcStepN.gdlvRecv _ _ r j m)
              (fun k hk => ABAProcStepN.gdlvIdle _ _ r i j m (Ne.symm hk)))
            (NetStep.gdlv w r i j m hmem)
            (wccLift_idle P o (wccPull_gdlv r i j m))), ?_⟩
        rw [map_regroup_prod, prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure,
          regG_stage_still u w i _ r _, regC_stage]
        rfl
    · obtain rfl : X = ((fun i => (u i).2 r), W') := pureN_inj (by rw [← hX])
      obtain ⟨k, m, hF, hW'⟩ := GSub.netG_tau hgn
      obtain rfl : W' = (⟨w.pool r, w.F⟩ : GSub.GNetState P.n).gpool k m :=
        GSub.pure_inj hW'
      refine ⟨_, deployedGroup_of_lab P (deployedPre_tau_net P (NetStep.byzG w r k m hF)), ?_⟩
      rw [map_regroup_pure, regG_mcast u w r k m, regA_gpool]
      rfl
  · obtain ⟨k, b, hF, hA'⟩ := aStep_tau hA
    obtain rfl : A' = (regA w).dput k b := pureN_inj hA'
    refine ⟨_, deployedGroup_of_lab P (deployedPre_tau_net P (NetStep.byzD w k b hF)), ?_⟩
    rw [map_regroup_pure, regG_dput, regA_dput]
  · refine ⟨_, deployedGroup_of_lab P (deployedPre_tau_wcc P hW), ?_⟩
    rw [map_regroup_prod]

/-! ### The converse on the shared labels -/

theorem deployedGroupConverse_lab (P : Params) (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) (l : Lab P.n) (hl : l ≠ Lab.tau)
    {μ : PMF (LayeredState P)}
    (h : (layeredPre P).step (regroup (u, w, o)) (Sum.inl l) μ) :
    ∃ ν, (deployedGroup P).step (u, w, o) l ν ∧ μ = ν.map regroup := by
  rw [regroup_apply] at h
  have hL : (Sum.inl l : NLab P.n) ≠ Silent.τ := by simpa using hl
  obtain ⟨G', C', A', ω, hG, hC, hA, hW, rfl⟩ := layeredPre_vis_inv P hL h
  cases l with
  | tau => exact absurd rfl hl
  | callABA id b =>
    obtain rfl : A' = regA w := pureN_inj (aStep_callABA hA)
    obtain rfl : G' = regG u w :=
      pureN_inj (gbcaSide_idle_inv P (by simp) (by simp) (by simp [GSub.isFailN]) hG)
    rcases stepC_callABA_own (hC id) with ⟨hin, hC0⟩ | hC0
    · obtain rfl := coresN_update hC0
        (fun i hi => stepC_callABA_foreign (Ne.symm hi) (hC i))
      refine ⟨_, deployedGroup_of_lab P (deployedPre_vis_step P hL
        (procsN_family id _ (ABAProcStepN.input _ _ b hin)
          (fun i hi => ABAProcStepN.callABAIdle _ _ id b (Ne.symm hi)))
        (NetStep.callABAIdle w id b) hW), ?_⟩
      rw [map_regroup_prod, regG_core u w w id _ rfl rfl, regC_core]
      rfl
    · obtain rfl : C' = regC u := coresN_id fun i => by
        by_cases hi : i = id
        · subst hi; exact hC0
        · exact stepC_callABA_foreign (Ne.symm hi) (hC i)
      have hall : ∀ i, ABAProcStepN P i (u i) (Sum.inl (Lab.callABA id b))
          (PMF.pure (u i)) := by
        intro i
        by_cases hi : i = id
        · subst hi; exact ABAProcStepN.inputLoop _ _ b
        · exact ABAProcStepN.callABAIdle _ _ id b (Ne.symm hi)
      refine ⟨_, deployedGroup_of_lab P
        (deployedPre_vis_step P hL hall (NetStep.callABAIdle w id b) hW), ?_⟩
      rw [map_regroup_prod]
  | retABA id b =>
    obtain ⟨hpool, hA'⟩ := aStep_retABA hA
    obtain rfl : A' = regA w := pureN_inj hA'
    obtain rfl : G' = regG u w :=
      pureN_inj (gbcaSide_idle_inv P (by simp) (by simp) (by simp [GSub.isFailN]) hG)
    obtain ⟨hcnt, hret, hC0⟩ := stepC_retABA_own (hC id)
    obtain rfl := coresN_update hC0
      (fun i hi => stepC_retABA_foreign (Ne.symm hi) (hC i))
    refine ⟨_, deployedGroup_of_lab P (deployedPre_vis_step P hL
      (procsN_family id _ (ABAProcStepN.ret _ _ b hcnt hret)
        (fun i hi => ABAProcStepN.retABAIdle _ _ id b (Ne.symm hi)))
      (NetStep.retABA w id b hpool) hW), ?_⟩
    rw [map_regroup_prod, regG_core u w w id _ rfl rfl, regC_core]
    rfl
  | callG r id b =>
    obtain rfl : A' = regA w := pureN_inj (aStep_callG hA)
    obtain ⟨X, hsub, hG'⟩ := gbcaSide_owned_inv P (r := r) (by simp) hL hG
    obtain ⟨Y, W', hX, hgall, hgn⟩ := sub_vis_inv P r
      (U := fun i => (u i).2 r) (W := ⟨w.pool r, w.F⟩) (by simp) hsub
    obtain rfl : X = (Y, W') := pureN_inj (by rw [← hX])
    obtain rfl : W' = (⟨w.pool r, w.F⟩ : GSub.GNetState P.n).gpool id (.input b) :=
      GSub.pure_inj (GSub.netG_callG hgn)
    obtain ⟨hin, hY⟩ := GSub.stepG_callG_own (hgall id)
    obtain rfl := gprocs_update hY
      (fun i hi => GSub.stepG_callG_foreign (Ne.symm hi) (hgall i))
    obtain rfl := pureN_inj hG'
    obtain ⟨hph, hr, hest, hC0⟩ := stepC_callG_own (hC id)
    obtain rfl := coresN_update hC0
      (fun i hi => stepC_callG_foreign (Ne.symm hi) (hC i))
    refine ⟨_, deployedGroup_of_lab P (deployedPre_vis_step P hL
      (procsN_family id _ (ABAProcStepN.callG_call _ _ r b hph hr hest hin)
        (fun i hi => ABAProcStepN.callGIdle _ _ r id b (Ne.symm hi)))
      (NetStep.callG w r id b) hW), ?_⟩
    rw [map_regroup_prod, regG_stage_mcast u w id _ r _ (.input b), regC_core, regA_gpool]
    rfl
  | retG r id out =>
    obtain rfl : A' = regA w := pureN_inj (aStep_retG hA)
    obtain ⟨X, hsub, hG'⟩ := gbcaSide_owned_inv P (r := r) (by simp) hL hG
    obtain ⟨Y, W', hX, hgall, hgn⟩ := sub_vis_inv P r
      (U := fun i => (u i).2 r) (W := ⟨w.pool r, w.F⟩) (by simp) hsub
    obtain rfl : X = (Y, W') := pureN_inj (by rw [← hX])
    obtain rfl : W' = (⟨w.pool r, w.F⟩ : GSub.GNetState P.n) :=
      GSub.pure_inj (GSub.netG_retG hgn)
    obtain rfl := pureN_inj hG'
    obtain ⟨hph, hr, hC0⟩ := stepC_retG_own (hC id)
    obtain rfl := coresN_update hC0
      (fun i hi => stepC_retG_foreign (Ne.symm hi) (hC i))
    have hidle : ∀ i, i ≠ id →
        (PMF.pure (Y i) : PMF (GBCA.ProcNodeN P.n)) = PMF.pure ((u i).2 r) :=
      fun i hi => GSub.stepG_retG_foreign (Ne.symm hi) (hgall i)
    have hgo : ∀ {p' : GBCA.ProcNodeN P.n},
        Y = Function.update (fun i => (u i).2 r) id p' →
        ABAProcStepN P id (u id) (Sum.inl (.retG r id out))
          (PMF.pure ((u id).1.setProc { (u id).1.proc with
              est := out.est, lastGrade := some out, phase := .toCallW },
            Function.update (u id).2 r p')) →
        ∃ ν, (deployedGroup P).step (u, w, o) (Lab.retG r id out) ν ∧
          prodPMF (PMF.pure (Function.update (regG u w) r
              (Y, (⟨w.pool r, w.F⟩ : GSub.GNetState P.n))))
            (prodPMF (PMF.pure (Function.update (regC u) id
                ((regC u id).setProc { (regC u id).proc with
                  est := out.est, lastGrade := some out, phase := .toCallW })))
              (prodPMF (PMF.pure (regA w)) ω)) = ν.map regroup := by
      intro p' heq hown
      subst heq
      refine ⟨_, deployedGroup_of_lab P (deployedPre_vis_step P hL
        (procsN_family id _ hown
          (fun i hi => ABAProcStepN.retGIdle _ _ r id out (Ne.symm hi)))
        (NetStep.retGIdle w r id out) hW), ?_⟩
      rw [map_regroup_prod, regG_stage_still u w id _ r p', regC_core]
      rfl
    cases out with
    | A v =>
      obtain ⟨hcnt, hret, hY⟩ := GSub.stepG_retG_A_own (hgall id)
      exact hgo (gprocs_update hY hidle)
        (ABAProcStepN.retG_A _ _ r v hph hr hcnt hret)
    | B v =>
      obtain ⟨hcnt, honce, hbind, hval, hret, hY⟩ := GSub.stepG_retG_B_own (hgall id)
      exact hgo (gprocs_update hY hidle)
        (ABAProcStepN.retG_B _ _ r v hph hr hcnt honce hbind hval hret)
    | C =>
      obtain ⟨hcnt, hval, hret, hY⟩ := GSub.stepG_retG_C_own (hgall id)
      exact hgo (gprocs_update hY hidle)
        (ABAProcStepN.retG_C _ _ r hph hr hcnt hval hret)
  | callW r id =>
    obtain rfl : A' = regA w := pureN_inj (aStep_callW hA)
    obtain rfl : G' = regG u w :=
      pureN_inj (gbcaSide_idle_inv P (by simp) (by simp) (by simp [GSub.isFailN]) hG)
    obtain ⟨hph, hr, hC0⟩ := stepC_callW_own (hC id)
    obtain rfl := coresN_update hC0
      (fun i hi => stepC_callW_foreign (Ne.symm hi) (hC i))
    refine ⟨_, deployedGroup_of_lab P (deployedPre_vis_step P hL
      (procsN_family id _ (ABAProcStepN.callW _ _ r hph hr)
        (fun i hi => ABAProcStepN.callWIdle _ _ r id (Ne.symm hi)))
      (NetStep.callWIdle w r id) hW), ?_⟩
    rw [map_regroup_prod, regG_core u w w id _ rfl rfl, regC_core]
    rfl
  | retW r id c =>
    obtain rfl : A' = regA w := pureN_inj (aStep_retW hA)
    obtain rfl : G' = regG u w :=
      pureN_inj (gbcaSide_idle_inv P (by simp) (by simp) (by simp [GSub.isFailN]) hG)
    obtain ⟨hph, hr, hgr, hC0⟩ := stepC_retW_own (hC id)
    obtain rfl := coresN_update hC0
      (fun i hi => stepC_retW_foreign (Ne.symm hi) (hC i))
    refine ⟨_, deployedGroup_of_lab P (deployedPre_vis_step P hL
      (procsN_family id _ (ABAProcStepN.retW _ _ r c hph hr hgr)
        (fun i hi => ABAProcStepN.retWIdle _ _ r id c (Ne.symm hi)))
      (NetStep.retWIdle w r id c) hW), ?_⟩
    rw [map_regroup_prod, regG_core u w w id _ rfl rfl, regC_core]
    rfl
  | fail k =>
    obtain rfl : A' = ANetState.corrupt P k (regA w) := pureN_inj (aStep_fail hA)
    obtain rfl := pureN_inj (gbcaSide_fail_inv P k hG)
    obtain rfl : C' = regC u := coresN_id fun i => stepC_fail (hC i)
    refine ⟨_, deployedGroup_of_lab P (deployedPre_vis_step P hL
      (fun i => ABAProcStepN.failIdle _ _ k) (NetStep.fail w k) hW), ?_⟩
    rw [map_regroup_prod, regG_corrupt, regA_corrupt]

/-! ### The two simulations and the equality of trace distributions

The regrouping reflects transitions as well as it preserves them, so it is a
step-*bi*simulating state map and the two soundness inclusions close the two
halves of an equality. Every state is arbitrary throughout — no reachability
and no invariant enters, because every copy of the corrupted set on the
layered side *is* the network adversary's set, read through `regroup`. -/

/-- **The converse matching** at the level of the two groups. -/
theorem layeredGroupConverse (P : Params) :
    ∀ q l μ, (layeredGroup P).step (regroup q) l μ →
      ∃ ν, (deployedGroup P).step q l ν ∧ μ = ν.map regroup := by
  rintro ⟨u, w, o⟩ l μ h
  rw [layeredGroup_step_iff] at h
  rcases h with ⟨rfl, e, hpre⟩ | hpre
  · exact deployedGroupConverse_netEvt P u w o e hpre
  · by_cases hl : l = Lab.tau
    · subst hl; exact deployedGroupConverse_tau P u w o hpre
    · exact deployedGroupConverse_lab P u w o l hl hpre

/-- **The converse matching**: every transition of the layered system out of a
regrouped state is a transition of the deployed system, its successor
distribution pushed forward. -/
theorem layeredConverse (P : Params) :
    ∀ q l μ, (layered P).step (regroup q) l μ →
      ∃ ν, (deployed P).step q l ν ∧ μ = ν.map regroup :=
  strongConverse_abstract regroup (Lab.hiddenAPI P.n) (layeredGroupConverse P)

/-- **The deployed system simulates into the layered one** along the graph of
the regrouping. -/
noncomputable def layeredSim (P : Params) :
    ProbabilisticForwardSimulation (deployed P) (layered P)
      (fun s ν => ν = PMF.pure (regroup s)) :=
  ProbabilisticForwardSimulation.ofStrongFunctional regroup (regroup_init P)
    (layeredForward P)

/-- **The layered system simulates into the deployed one** along the converse
of the graph of the regrouping. -/
noncomputable def layeredSimConverse (P : Params) :
    ProbabilisticForwardSimulation (layered P) (deployed P)
      (fun p ν => ∃ q, ν = PMF.pure q ∧ p = regroup q) :=
  ProbabilisticForwardSimulation.ofStrongFunctional_converse regroup
    (regroup_init P) (layeredConverse P)

/-- **The layered presentation is exact**: cutting the deployed system along
its layer boundaries — the family of graded-agreement round subsystems, the
`n` round loops, the DECIDED layer with the corrupted set, and the coin
oracle — achieves exactly the trace distributions of the deployed reading. No
behaviour is added and none is lost. -/
theorem layered_atd (P : Params) :
    achievableTraceDists (deployed P) = achievableTraceDists (layered P) :=
  Set.Subset.antisymm (layeredSim P).achievableTraceDists_subset
    (layeredSimConverse P).achievableTraceDists_subset

/-! ### Mechanical axiom firewall

No headline may acquire a `sorryAx` dependence. -/

/-- info: 'PLTS.ABA.Layer.layered_atd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms layered_atd

/-- info: 'PLTS.ABA.Layer.layeredForward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms layeredForward

/-- info: 'PLTS.ABA.Layer.layeredConverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms layeredConverse

end Layer

end ABA
end PLTS
