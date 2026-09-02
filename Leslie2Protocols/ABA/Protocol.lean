/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Components
import Mathlib.Data.Finmap

/-!
# ABA as per-process programs beside a network adversary

The protocol reading of the protocol: `n` automata, each running one process's
code and nothing else, beside two boxes that are not processes — the network
adversary and the coin oracle.

A process record is exactly the data the program of that process may read: its
round-loop record, its stage-side record, and the flag that says whether its own
program has been replaced (D23). The stage-side record retains the
graded-agreement stage record of every round the process has touched, together
with the messages delivered into each of them, and says whether the process has
terminated. The record holds no copy of the corrupted set and no record of what
the process has sent. A guard of the rule table may therefore ask whether this
process's own program has been replaced, but never whether another process is
honest and never what the process has multicast. The sub-protocol ports of a
program not yet replaced are input-enabled — a return arrives when the evidence
for it is on the record, whoever asked for it.

Everything a process may not see lives in the network adversary
`NetState`: the round-tagged message pools `pool r j`, the DECIDED pools
`dpool j`, and the corrupted set `F` with its budget. Multicast is a joint
step of the sender and the network — the sender writes its own record, the
network inserts the message into the sender's pool — and delivery is a joint
step of the network, which checks that the message really is in the sender's
pool, and the receiver, which files it under that sender's inbox row. Whether
a process may be driven off-protocol is decided by the network's `k ∈ F`
guard on the Byzantine labels, never by the process.

The coin oracle `WCC.specFamily` is the third component and the only box whose
transitions are not Dirac. It enters as `Net.wccLift`, the oracle read over
the extended alphabet along the label pullback `Net.wccPull`
(`ABA/Components.lean`).

The extended alphabet is `Net.NLab n = Lab n ⊕ Net.NetEvt n`
(`ABA/Components.lean`). Its right summand is the rendezvous alphabet the
shared alphabet `Lab n` cannot name — the two networks, the Byzantine drives,
and the branches of a handshake that the shared label does not distinguish.
The composition hides it, so `protocolGroup` speaks exactly `Lab n`.

## Model and deviations

* **D1 (determinised `fail`).** `fail` is Dirac and guarded by
  `k ∉ F ∧ |F| < f`. The guard sits on the network's row as well as inside
  `NetState.corrupt`, so a corruption fires exactly when it takes effect and
  the named process may write its replacement flag outright (D23). Every other
  process takes the broadcast without moving. The coin oracle enters unchanged,
  keeping its own copy of the corrupted set and its budget-guarded `corrupt` —
  its resolution threshold reads it.
* **D5 (set-based network).** Multicasts are idempotent: `pool r j` is the
  set of messages `j` has multicast in stage `r`, and `inbox k` at a process record is
  the set of messages from `k` the adversary has delivered there. Thresholds
  count distinct senders. A corrupted sender's injections enter its pool
  through the network's own `byzG` transition.
* **D8 (participation gating).** Stage sends and the graded returns require the
  process's stage record to have received its input. The DECIDED relay and the
  ABA return require the round-loop record to have received its own.
* **D9 (0-based rounds).** `round : ℕ` starts at `0`.
* **D10 (fused DECIDED-send).** The coin return performs the round advance
  and, when the round's grade was `A b`, the `⟨DECIDED, b⟩` multicast, in one
  transition. The published payload is dictated by the process's own grade, so
  the fused case travels on its own rendezvous label `retWPub`, which carries
  the payload the network is to pool; the unfused case travels on the shared
  `retW` label.
* **D11 (Byzantine handshake drives).** A corrupted process may drive its
  sub-protocol handshakes arbitrarily. Each drive is a rendezvous label of
  its own, authorised by the network's `k ∈ F` guard, and no drive ever makes
  a round-loop write. The coin drives reach the oracle through the pullback;
  the stage drives have no process row at all (D22). A replaced program has no
  row on its own graded-agreement traffic (D23), so that traffic runs through
  the drives and through the network's `byzG` injection and nowhere else.
* **D12′ (per-process DECIDED pools, equivocation-capable).** The DECIDED
  state is the pool family `dpool j` beside the per-process receipt rows
  `decIn k`. The relay's write-once condition is a condition on the pool, so
  it is the network's conjunct of the relay rendezvous; the quorum condition
  is a condition on the record, so it is the process's. A corrupted process's
  injections (`byzD`) may put either or both bits into its pool, so the
  DECIDED pools admit equivocation.
* **D17 (δ-mass failure outcome).** Inherited from the coin oracle: a failed
  resolution enables no return.
* **D18 (the five-level ladder).** The stage rules are the five levels
  `INPUT / ECHO / VOTE / BIND / SEAL` and the three graded returns of the
  cited algorithm, not the four-round compression.
* **D22 (retention with termination).** A process record retains the stage
  record of every round in a finite map, and the process terminates once its
  own return has fired and `2f + 1` DECIDED receipts are on record;
  participation before that point is indefinite. A stage-side rule therefore
  reads and writes the stage record of the round its label tags, whichever
  round the round loop is in, and is guarded by `p.terminated = false` rather
  than by the round. Deliveries file into any round's record, and each
  stage-side send remains one-per-round-instance send-once. The DECIDED rules
  carry no termination guard, so a terminated process keeps relaying the
  payloads it holds. The Byzantine stage drives keep their labels and their
  network rows but have no row at the process they name; a corrupted process's
  stage traffic enters through the network's own `byzG` injection.
* **D23 (the corrupted process's replaced program).** A corruption replaces the
  program of the process it names. The flag `CoreRec.corrupted` carries the
  replacement: `failSelf` writes it on the process's own `fail`, every
  participant's row is guarded by `corrupted = false`, and in place of those
  rows the replaced program has the single self-loop `corruptedIdle`, taken on
  every label other than `τ` and the labels of `Net.actsAt j`. On the latter the
  replaced program has no row at all, so a corrupted process's graded-agreement
  traffic enters only through the drives (D11), and the stage and DECIDED
  deliveries addressed to it are dead. The network's `retByz` row pairs with the
  self-loop on `retABA`: a corrupted process returns whatever it likes, without
  DECIDED evidence. A replaced program has no `τ` row, so it never terminates.

## The pipeline

`ABAProcN P j` is the program of process `j`; the programs are composed under
full synchronisation (`System.syncProduct`) and set beside `netAdv P` and the
lifted oracle. Hiding `NetEvt` and reading the result back over `Lab n` gives
`protocolGroup P`; hiding the sub-protocol API gives `protocol P`.

## What this file supplies

`protocol` is the subject of the refinement chain, and this file is where its
transition relation is pinned down: the rule tables of the process programs
and of the network adversary, the composition pipeline, and the inversion
lemmas that read a composite transition back into the rows its components
contributed. `ABA/Hybrid.lean` re-cuts the same system into its components
and continues the chain to `ABA.spec` from there.
-/

namespace PLTS
namespace ABA

namespace Net

/-! ### The state of one process -/

/-- The stage-side record of one process: the stage record of every round the
process has touched, and whether it has terminated (D22). -/
structure StageSideRec (n : ℕ) : Type where
  /-- The finite map of stage records; a round off the map has the initial
  record. -/
  stages : Finmap (fun _ : ℕ => GBCA.StageRec n)
  /-- Whether this process has terminated (ABDY22 §3, Termination). `terminated`
  is not `returned`: the round-loop record's `returned` says the process has
  fired `retABA`; `terminated` says it has stopped participating. -/
  terminated : Bool
  deriving DecidableEq

namespace StageSideRec

variable {n : ℕ}

/-- The initial stage-side record: no round touched, not terminated. -/
def initial (n : ℕ) : StageSideRec n where
  stages := ∅
  terminated := false

/-- The stage record of round `r`: the retained record if the process has
touched round `r`, the initial record otherwise. -/
def stage (q : StageSideRec n) (r : ℕ) : GBCA.StageRec n :=
  (q.stages.lookup r).getD (GBCA.StageRec.initial n)

/-- Retain `p` as the stage record of round `r`. -/
def setStage (q : StageSideRec n) (r : ℕ) (p : GBCA.StageRec n) : StageSideRec n :=
  { q with stages := q.stages.insert r p }

/-- File `m` under the inbox row of sender `k` in the stage record of round
`r`. -/
def deliverTo (q : StageSideRec n) (r : ℕ) (k : Fin n) (m : GBCA.Msg) :
    StageSideRec n :=
  q.setStage r ((q.stage r).deliverTo k m)

@[simp] theorem initial_stage (n r : ℕ) :
    (initial n).stage r = GBCA.StageRec.initial n := by
  simp [stage, initial]

@[simp] theorem initial_terminated (n : ℕ) : (initial n).terminated = false := rfl

@[simp] theorem stage_setStage_self (q : StageSideRec n) (r : ℕ)
    (p : GBCA.StageRec n) : (q.setStage r p).stage r = p := by
  simp [stage, setStage, Finmap.lookup_insert]

@[simp] theorem stage_setStage_ne (q : StageSideRec n) (r : ℕ)
    (p : GBCA.StageRec n) {r' : ℕ} (h : r' ≠ r) :
    (q.setStage r p).stage r' = q.stage r' := by
  simp [stage, setStage, Finmap.lookup_insert_of_ne _ h]

@[simp] theorem terminated_setStage (q : StageSideRec n) (r : ℕ)
    (p : GBCA.StageRec n) : (q.setStage r p).terminated = q.terminated := rfl

@[simp] theorem terminated_deliverTo (q : StageSideRec n) (r : ℕ) (k : Fin n)
    (m : GBCA.Msg) : (q.deliverTo r k m).terminated = q.terminated := rfl

end StageSideRec

/-- The state of one process: its round-loop record and its stage-side record
(D22). -/
abbrev ProcRec (n : ℕ) : Type := CoreRec n × StageSideRec n

/-! ### The network adversary's state -/

/-- The state of the network adversary: the round-tagged message pools, the
DECIDED pools, and the corrupted set with its budget. -/
structure NetState (n : ℕ) : Type where
  /-- `pool r j` — the stage-`r` messages process `j` has multicast (D5). -/
  pool : ℕ → Fin n → Finset GBCA.Msg
  /-- `dpool j` — the DECIDED payloads process `j` has multicast (D12′). -/
  dpool : Fin n → Finset Bool
  /-- The corrupted set. -/
  F : Finset (Fin n)

namespace NetState

variable {n : ℕ}

/-- The initial network: nothing multicast, nobody corrupted. -/
def initial (n : ℕ) : NetState n where
  pool := fun _ _ => ∅
  dpool := fun _ => ∅
  F := ∅

/-- Pool `m` under sender `j` in stage `r` (D5). -/
def gpool (s : NetState n) (r : ℕ) (j : Fin n) (m : GBCA.Msg) : NetState n :=
  { s with
    pool :=
      Function.update s.pool r (Function.update (s.pool r) j (insert m (s.pool r j))) }

/-- Pool `⟨DECIDED, b⟩` under sender `j` (D12′). -/
def dput (s : NetState n) (j : Fin n) (b : Bool) : NetState n :=
  { s with dpool := Function.update s.dpool j (insert b (s.dpool j)) }

/-- Corruption (deviation D1): total, Dirac, budget-guarded. -/
def corrupt (P : Params) (id : Fin P.n) (s : NetState P.n) : NetState P.n :=
  if id ∉ s.F ∧ s.F.card < P.f then { s with F := insert id s.F } else s

end NetState

/-! ### The rule table

Process `j`'s program. Every guard reads the process's own record and nothing
else: none asks whether another process is honest, and none asks what this one
has multicast. A stage-side row reads and writes the stage record of the round its
label tags, whichever round the round loop is in, and is guarded by
`p.terminated = false` (D22). The stage rows are taken in the wait-until order
of Algorithm 6 from the `BIND` level down, each of those levels requiring the
process's own send at the level below; the `VOTE` rows ask for no own send, the
`ECHO` they read being sent by an `upon` handler that may still be pending. The
DECIDED relay and the ABA return are participation-gated (D8, D18). A
rendezvous row carries the process's half of a joint step with the network: on
a send the record write, on a delivery the inbox write. The DECIDED rows carry
no termination guard, so a terminated process keeps relaying the payloads it
holds. The Byzantine stage drives are the exception, having no row at the
process they name (D11, D22). Every other label of the extended alphabet has a
row: the participant's, or an idle one.

A corruption replaces the program of the process it names (D23). Every
participant's row above carries the health guard `c.corrupted = false`, so the
record freezes at the corruption; `failSelf` is the row that writes the flag,
and `corruptedIdle` is the replaced program. That self-loop is taken on every
label other than `τ` and the labels of `Net.actsAt j`, on which the replaced
program has no row at all. -/

/-- The step relation of the program of process `j`. -/
inductive ABAProcStepN (P : Params) (j : Fin P.n) :
    ProcRec P.n → NLab P.n → PMF (ProcRec P.n) → Prop
  /-- `upon ABA(b)`: record input and estimate, open round `0`. -/
  | input (c : CoreRec P.n) (p : StageSideRec P.n) (b : Bool)
      (hh : c.corrupted = false) (h : c.proc.input = none) :
      ABAProcStepN P j (c, p) (Sum.inl (.callABA j b))
        (PMF.pure (c.setProc { c.proc with
          input := some b, est := some b, round := 0, phase := .toCallG }, p))
  /-- Input-enabledness loop on `j`'s own `callABA`. -/
  | inputLoop (c : CoreRec P.n) (p : StageSideRec P.n) (b : Bool)
      (hh : c.corrupted = false) :
      ABAProcStepN P j (c, p) (Sum.inl (.callABA j b)) (PMF.pure (c, p))
  /-- An input addressed elsewhere: not `j`'s business. -/
  | callABAIdle (c : CoreRec P.n) (p : StageSideRec P.n)
      (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ABAProcStepN P j (c, p) (Sum.inl (.callABA id b)) (PMF.pure (c, p))
  /-- Return `b` on an `n − f` DECIDED quorum, the round-loop record having
  received its input (D8). Having multicast `b` oneself is a condition on the
  pool, hence the network's conjunct. -/
  | ret (c : CoreRec P.n) (p : StageSideRec P.n) (b : Bool)
      (hh : c.corrupted = false) (hin : c.proc.input ≠ none)
      (hcnt : P.n - P.f ≤ c.decidedCount b) (hret : c.proc.returned = false) :
      ABAProcStepN P j (c, p) (Sum.inl (.retABA j b))
        (PMF.pure (c.setProc { c.proc with returned := true }, p))
  /-- A return by another process: not `j`'s business. -/
  | retABAIdle (c : CoreRec P.n) (p : StageSideRec P.n)
      (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ABAProcStepN P j (c, p) (Sum.inl (.retABA id b)) (PMF.pure (c, p))
  /-- The process terminates (ABDY22 Definitions 3.1/3.2 and the p.7 note on
  termination): its own return is fired and DECIDED receipts from `2f + 1`
  distinct senders are on record, so every process still running will cross the
  relay threshold without further response from this one. -/
  | terminate (c : CoreRec P.n) (p : StageSideRec P.n) (b : Bool)
      (hh : c.corrupted = false) (hret : c.proc.returned = true)
      (hcnt : 2 * P.f + 1 ≤ c.decidedCount b)
      (hterm : p.terminated = false) :
      ABAProcStepN P j (c, p) (Sum.inl Lab.tau)
        (PMF.pure (c, { p with terminated := true }))
  /-- The graded-agreement call: the round loop hands its estimate to the stage
  record of round `r`, which opens. The `⟨INPUT, b⟩` multicast is the network's
  half. -/
  | callG_call (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r)
      (hterm : p.terminated = false)
      (hest : c.proc.est = some b) (hin : (p.stage r).proc.input = none) :
      ABAProcStepN P j (c, p) (Sum.inl (.callG r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG },
          p.setStage r ((p.stage r).setP { (p.stage r).proc with
            input := some b,
            sentInput := Function.update (p.stage r).proc.sentInput b true })))
  /-- A graded-agreement call by another process: not `j`'s business. -/
  | callGIdle (c : CoreRec P.n) (p : StageSideRec P.n)
      (r : ℕ) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ABAProcStepN P j (c, p) (Sum.inl (.callG r id b)) (PMF.pure (c, p))
  /-- Return with grade `A v`: an `n − f` `SEAL v` quorum. The stage record has
  been called and its own `SEAL` is out. Case (1) heads the algorithm's chain,
  so there is no higher case to deny. -/
  | retG_A (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (v : Bool)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hlv : (p.stage r).proc.sentSeal ≠ none)
      (hcnt : P.n - P.f ≤ (p.stage r).recvCount (.seal (some v)))
      (hret : (p.stage r).proc.returned = false) :
      ABAProcStepN P j (c, p) (Sum.inl (.retG r j (.A v)))
        (PMF.pure (c.setProc { c.proc with
            est := (GbcaOut.A v).est, lastGrade := some (.A v), phase := .toCallW },
          p.setStage r ((p.stage r).setP { (p.stage r).proc with returned := true })))
  /-- Return with grade `B v`: an `n − f` any-`SEAL` quorum containing
  `SEAL v`, `f + 1` `BIND v`s and `|Valid| > 1`. The stage record has been
  called, its own `SEAL` is out, and `hnotA` denies case (1) at either bit. -/
  | retG_B (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (v : Bool)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hlv : (p.stage r).proc.sentSeal ≠ none)
      (hnotA : ∀ v, (p.stage r).recvCount (.seal (some v)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ (p.stage r).sealCount)
      (honce : ∃ k, GBCA.Msg.seal (some v) ∈ (p.stage r).inbox k)
      (hbind : P.f + 1 ≤ (p.stage r).recvCount (.bind (some v)))
      (hval : (p.stage r).bothValid P)
      (hret : (p.stage r).proc.returned = false) :
      ABAProcStepN P j (c, p) (Sum.inl (.retG r j (.B v)))
        (PMF.pure (c.setProc { c.proc with
            est := (GbcaOut.B v).est, lastGrade := some (.B v), phase := .toCallW },
          p.setStage r ((p.stage r).setP { (p.stage r).proc with returned := true })))
  /-- Return with grade `C`: an `n − f` `SEAL ⊥` quorum and `|Valid| > 1`. The
  stage record has been called, its own `SEAL` is out, `hnotA` denies case (1)
  at either bit, and `hnotB` denies case (2) in the reduced form
  `GBCA.ImplStep.retC` states. -/
  | retG_C (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hlv : (p.stage r).proc.sentSeal ≠ none)
      (hnotA : ∀ v, (p.stage r).recvCount (.seal (some v)) < P.n - P.f)
      (hnotB : ∀ v, (∃ k, GBCA.Msg.seal (some v) ∈ (p.stage r).inbox k) →
        (p.stage r).recvCount (.bind (some v)) < P.f + 1)
      (hcnt : P.n - P.f ≤ (p.stage r).recvCount (.seal none))
      (hval : (p.stage r).bothValid P)
      (hret : (p.stage r).proc.returned = false) :
      ABAProcStepN P j (c, p) (Sum.inl (.retG r j .C))
        (PMF.pure (c.setProc { c.proc with
            est := GbcaOut.C.est, lastGrade := some .C, phase := .toCallW },
          p.setStage r ((p.stage r).setP { (p.stage r).proc with returned := true })))
  /-- A graded-agreement return to another process: not `j`'s business. -/
  | retGIdle (c : CoreRec P.n) (p : StageSideRec P.n)
      (r : ℕ) (id : Fin P.n) (out : GbcaOut) (hid : id ≠ j) :
      ABAProcStepN P j (c, p) (Sum.inl (.retG r id out)) (PMF.pure (c, p))
  /-- `c ← WCC_r()`, the call half at the round loop. -/
  | callW (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .toCallW) (hr : c.proc.round = r) :
      ABAProcStepN P j (c, p) (Sum.inl (.callW r j))
        (PMF.pure (c.setProc { c.proc with phase := .awaitW }, p))
  /-- A coin call by another process: not `j`'s business. -/
  | callWIdle (c : CoreRec P.n) (p : StageSideRec P.n)
      (r : ℕ) (id : Fin P.n) (hid : id ≠ j) :
      ABAProcStepN P j (c, p) (Sum.inl (.callW r id)) (PMF.pure (c, p))
  /-- The coin return without a publication: the round advances and nothing is
  multicast, the round's grade not being an `A` (D10). The advance opens a new
  round; the stage records the process holds are retained across it (D22). -/
  | retW (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (co : Bool)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .awaitW) (hr : c.proc.round = r)
      (hgr : ∀ v : Bool, c.proc.lastGrade ≠ some (.A v)) :
      ABAProcStepN P j (c, p) (Sum.inl (.retW r j co))
        (PMF.pure (c.stepRound co, p))
  /-- A coin return to another process: not `j`'s business. -/
  | retWIdle (c : CoreRec P.n) (p : StageSideRec P.n)
      (r : ℕ) (id : Fin P.n) (co : Bool) (hid : id ≠ j) :
      ABAProcStepN P j (c, p) (Sum.inl (.retW r id co)) (PMF.pure (c, p))
  /-- The process's own corruption: the program is replaced, and the flag that
  carries the replacement is the one write of the row (D23). -/
  | failSelf (c : CoreRec P.n) (p : StageSideRec P.n) (hh : c.corrupted = false) :
      ABAProcStepN P j (c, p) (Sum.inl (.fail j))
        (PMF.pure ({ c with corrupted := true }, p))
  /-- Another process's corruption is not this process's business. -/
  | failIdle (c : CoreRec P.n) (p : StageSideRec P.n) (k : Fin P.n) (hk : k ≠ j) :
      ABAProcStepN P j (c, p) (Sum.inl (.fail k)) (PMF.pure (c, p))
  /-- The replaced program (D23): a self-loop on every label other than `τ` and
  the labels of `actsAt j`, on which the process has no row at all. -/
  | corruptedIdle (c : CoreRec P.n) (p : StageSideRec P.n) (L : NLab P.n)
      (hh : c.corrupted = true) (hτ : L ≠ Sum.inl Lab.tau) (hown : ¬ actsAt j L) :
      ABAProcStepN P j (c, p) L (PMF.pure (c, p))
  /-- The stage `INPUT` relay: `f + 1` receipts of `⟨INPUT, b⟩` in the stage
  record of round `r`, not yet multicast there (D8, D18, D22). -/
  | gsndRelay (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hcnt : P.f + 1 ≤ (p.stage r).recvCount (.input b))
      (hsend : (p.stage r).proc.sentInput b = false) :
      ABAProcStepN P j (c, p) (Sum.inr (.gsnd r j (.input b)))
        (PMF.pure (c, p.setStage r ((p.stage r).setP { (p.stage r).proc with
          sentInput := Function.update (p.stage r).proc.sentInput b true })))
  /-- The stage `ECHO`: an `n − f` `INPUT b` quorum (D18, D22). -/
  | gsndEcho (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hcnt : P.n - P.f ≤ (p.stage r).recvCount (.input b))
      (hsend : (p.stage r).proc.sentEcho = none) :
      ABAProcStepN P j (c, p) (Sum.inr (.gsnd r j (.echo b)))
        (PMF.pure (c, p.setStage r
          ((p.stage r).setP { (p.stage r).proc with sentEcho := some b })))
  /-- The stage `VOTE b`: an `n − f` `ECHO b` quorum. The stage record's own
  `ECHO` is sent by one of the algorithm's `upon` handlers and may still be
  pending, so no own-send condition applies here (D18, D22). -/
  | gsndVoteBit (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hcnt : P.n - P.f ≤ (p.stage r).recvCount (.echo b))
      (hsend : (p.stage r).proc.sentVote = none) :
      ABAProcStepN P j (c, p) (Sum.inr (.gsnd r j (.vote (some b))))
        (PMF.pure (c, p.setStage r
          ((p.stage r).setP { (p.stage r).proc with sentVote := some (some b) })))
  /-- The stage `VOTE ⊥`: `n − f` `ECHO`s of any payload and `|Valid| > 1`, and
  no single-bit `ECHO` quorum on record. The stage record's own `ECHO` is sent
  by one of the algorithm's `upon` handlers and may still be pending, so no
  own-send condition applies here (D18, D22). -/
  | gsndVoteBot (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hnot : ∀ b, (p.stage r).recvCount (.echo b) < P.n - P.f)
      (hcnt : P.n - P.f ≤ (p.stage r).echoCount)
      (hval : (p.stage r).bothValid P) (hsend : (p.stage r).proc.sentVote = none) :
      ABAProcStepN P j (c, p) (Sum.inr (.gsnd r j (.vote none)))
        (PMF.pure (c, p.setStage r
          ((p.stage r).setP { (p.stage r).proc with sentVote := some none })))
  /-- The stage `BIND b`: an `n − f` `VOTE b` quorum, the stage record's own
  `VOTE` already out (D18, D22). -/
  | gsndBindBit (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hlv : (p.stage r).proc.sentVote ≠ none)
      (hcnt : P.n - P.f ≤ (p.stage r).recvCount (.vote (some b)))
      (hsend : (p.stage r).proc.sentBind = none) :
      ABAProcStepN P j (c, p) (Sum.inr (.gsnd r j (.bind (some b))))
        (PMF.pure (c, p.setStage r
          ((p.stage r).setP { (p.stage r).proc with sentBind := some (some b) })))
  /-- The stage `BIND ⊥`: `n − f` `VOTE`s of any payload and `|Valid| > 1`, the
  stage record's own `VOTE` already out, and no single-bit `VOTE` quorum on
  record (D18, D22). -/
  | gsndBindBot (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hlv : (p.stage r).proc.sentVote ≠ none)
      (hnot : ∀ b, (p.stage r).recvCount (.vote (some b)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ (p.stage r).voteCount)
      (hval : (p.stage r).bothValid P) (hsend : (p.stage r).proc.sentBind = none) :
      ABAProcStepN P j (c, p) (Sum.inr (.gsnd r j (.bind none)))
        (PMF.pure (c, p.setStage r
          ((p.stage r).setP { (p.stage r).proc with sentBind := some none })))
  /-- The stage `SEAL b`: an `n − f` `BIND b` quorum, the stage record's own
  `BIND` already out (D18, D22). -/
  | gsndSealBit (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hlv : (p.stage r).proc.sentBind ≠ none)
      (hcnt : P.n - P.f ≤ (p.stage r).recvCount (.bind (some b)))
      (hsend : (p.stage r).proc.sentSeal = none) :
      ABAProcStepN P j (c, p) (Sum.inr (.gsnd r j (.seal (some b))))
        (PMF.pure (c, p.setStage r
          ((p.stage r).setP { (p.stage r).proc with sentSeal := some (some b) })))
  /-- The stage `SEAL ⊥`: `n − f` `BIND`s of any payload and `|Valid| > 1`, the
  stage record's own `BIND` already out, and no single-bit `BIND` quorum on
  record (D18, D22). -/
  | gsndSealBot (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hlv : (p.stage r).proc.sentBind ≠ none)
      (hnot : ∀ b, (p.stage r).recvCount (.bind (some b)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ (p.stage r).bindCount)
      (hval : (p.stage r).bothValid P) (hsend : (p.stage r).proc.sentSeal = none) :
      ABAProcStepN P j (c, p) (Sum.inr (.gsnd r j (.seal none)))
        (PMF.pure (c, p.setStage r
          ((p.stage r).setP { (p.stage r).proc with sentSeal := some none })))
  /-- A stage multicast by another process: not `j`'s business. -/
  | gsndIdle (c : CoreRec P.n) (p : StageSideRec P.n)
      (r : ℕ) (k : Fin P.n) (m : GBCA.Msg) (hk : k ≠ j) :
      ABAProcStepN P j (c, p) (Sum.inr (.gsnd r k m)) (PMF.pure (c, p))
  /-- Stage delivery, receiver's half: file the message under the sender's
  inbox row in the stage record of round `r`, whichever round the round loop is
  in. Authenticity is the network's conjunct (D22). -/
  | gdlvRecv (c : CoreRec P.n) (p : StageSideRec P.n)
      (r : ℕ) (k : Fin P.n) (m : GBCA.Msg) (hh : c.corrupted = false)
      (hterm : p.terminated = false) :
      ABAProcStepN P j (c, p) (Sum.inr (.gdlv r j k m))
        (PMF.pure (c, p.deliverTo r k m))
  /-- A stage delivery to another process: not `j`'s business. -/
  | gdlvIdle (c : CoreRec P.n) (p : StageSideRec P.n)
      (r : ℕ) (i k : Fin P.n) (m : GBCA.Msg) (hi : i ≠ j) :
      ABAProcStepN P j (c, p) (Sum.inr (.gdlv r i k m)) (PMF.pure (c, p))
  /-- The DECIDED relay on an `f + 1` quorum, the round-loop record having
  received its input (D8, D12′). Not having multicast `b` is a condition on the
  pool, hence the network's conjunct; the pool insert is the network's half
  too. -/
  | dsndRelay (c : CoreRec P.n) (p : StageSideRec P.n) (b : Bool)
      (hh : c.corrupted = false) (hin : c.proc.input ≠ none)
      (hcnt : P.f + 1 ≤ c.decidedCount b) :
      ABAProcStepN P j (c, p) (Sum.inr (.dsnd j b)) (PMF.pure (c, p))
  /-- A DECIDED relay by another process: not `j`'s business. -/
  | dsndIdle (c : CoreRec P.n) (p : StageSideRec P.n)
      (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      ABAProcStepN P j (c, p) (Sum.inr (.dsnd k b)) (PMF.pure (c, p))
  /-- DECIDED delivery, receiver's half: at most one receipt per (sender, bit)
  (D12′). Authenticity is the network's conjunct. -/
  | ddlvRecv (c : CoreRec P.n) (p : StageSideRec P.n)
      (k : Fin P.n) (b : Bool) (hh : c.corrupted = false) (hr : b ∉ c.decIn k) :
      ABAProcStepN P j (c, p) (Sum.inr (.ddlv j k b))
        (PMF.pure (c.recvDec k b, p))
  /-- A DECIDED delivery to another process: not `j`'s business. -/
  | ddlvIdle (c : CoreRec P.n) (p : StageSideRec P.n)
      (i k : Fin P.n) (b : Bool) (hi : i ≠ j) :
      ABAProcStepN P j (c, p) (Sum.inr (.ddlv i k b)) (PMF.pure (c, p))
  /-- The coin return fused with the `⟨DECIDED, b⟩` publication (D10): the
  round's grade was `A b`, so the round advance publishes `b`, the pool insert
  being the network's half. The advance opens a new round; the stage records
  the process holds are retained across it (D22). -/
  | retWPub (c : CoreRec P.n) (p : StageSideRec P.n)
      (r : ℕ) (co : Bool) (b : Bool) (hh : c.corrupted = false)
      (hph : c.proc.phase = .awaitW) (hr : c.proc.round = r)
      (hgr : c.proc.lastGrade = some (.A b)) :
      ABAProcStepN P j (c, p) (Sum.inr (.retWPub r j co b))
        (PMF.pure (c.stepRound co, p))
  /-- A fused coin return at another process: not `j`'s business. -/
  | retWPubIdle (c : CoreRec P.n) (p : StageSideRec P.n)
      (r : ℕ) (id : Fin P.n) (co : Bool) (b : Bool) (hid : id ≠ j) :
      ABAProcStepN P j (c, p) (Sum.inr (.retWPub r id co b)) (PMF.pure (c, p))
  /-- The graded-agreement call against an already-called stage record: the
  round loop moves, the stage record does not. The row carries no termination
  guard, so a terminated process in `toCallG` whose stage record of round `r`
  is uncalled has no row on either call label, a dead region this reading
  accepts. -/
  | gcallLoop (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r)
      (hest : c.proc.est = some b)
      (hin : (p.stage r).proc.input ≠ none) :
      ABAProcStepN P j (c, p) (Sum.inr (.gcallLoop r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG }, p))
  /-- Such a call at another process: not `j`'s business. -/
  | gcallLoopIdle (c : CoreRec P.n) (p : StageSideRec P.n)
      (r : ℕ) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ABAProcStepN P j (c, p) (Sum.inr (.gcallLoop r id b)) (PMF.pure (c, p))
  /-- A Byzantine graded-agreement call at another process: not `j`'s
  business. The process the label names has no row either (D11, D22). -/
  | byzCallGIdle (c : CoreRec P.n) (p : StageSideRec P.n)
      (r : ℕ) (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      ABAProcStepN P j (c, p) (Sum.inr (.byzCallG r k b)) (PMF.pure (c, p))
  /-- A Byzantine graded-agreement call against an already-called stage record
  (D11): nothing moves anywhere. -/
  | byzCallGLoopIdle (c : CoreRec P.n) (p : StageSideRec P.n)
      (r : ℕ) (k : Fin P.n) (b : Bool) :
      ABAProcStepN P j (c, p) (Sum.inr (.byzCallGLoop r k b)) (PMF.pure (c, p))
  /-- A Byzantine graded-agreement return at another process: not `j`'s
  business. The process the label names has no row either (D11, D22). -/
  | byzRetGIdle (c : CoreRec P.n) (p : StageSideRec P.n)
      (r : ℕ) (k : Fin P.n) (out : GbcaOut) (hk : k ≠ j) :
      ABAProcStepN P j (c, p) (Sum.inr (.byzRetG r k out)) (PMF.pure (c, p))
  /-- A Byzantine coin call (D11): the coin oracle reacts through the pullback,
  no process moves. -/
  | byzCallWIdle (c : CoreRec P.n) (p : StageSideRec P.n)
      (r : ℕ) (k : Fin P.n) :
      ABAProcStepN P j (c, p) (Sum.inr (.byzCallW r k)) (PMF.pure (c, p))
  /-- A Byzantine coin return (D11): the coin oracle reacts through the
  pullback, no process moves. -/
  | byzRetWIdle (c : CoreRec P.n) (p : StageSideRec P.n)
      (r : ℕ) (k : Fin P.n) (b : Bool) :
      ABAProcStepN P j (c, p) (Sum.inr (.byzRetW r k b)) (PMF.pure (c, p))

/-! ### The network adversary

The one box that holds what no process may see: the pools, the corrupted set
and the budget. It participates in every send and every delivery — a send by
pooling the message, a delivery by checking that the message is pooled — and
it is the sole authority on the Byzantine labels, where its `k ∈ F` guard is
the whole authorisation. -/

/-- The step relation of the network adversary. All transitions are Dirac. -/
inductive NetStep (P : Params) :
    NetState P.n → NLab P.n → PMF (NetState P.n) → Prop
  /-- The network's half of a stage multicast: pool the message under its
  sender. Authenticity is the sender's joint participation (D5). -/
  | gsnd (s : NetState P.n) (r : ℕ) (j : Fin P.n) (m : GBCA.Msg) :
      NetStep P s (Sum.inr (.gsnd r j m)) (PMF.pure (s.gpool r j m))
  /-- The network's half of a stage delivery: the message must be pooled under
  the named sender. Delivery does not consume it (D5). -/
  | gdlv (s : NetState P.n) (r : ℕ) (i j : Fin P.n) (m : GBCA.Msg)
      (h : m ∈ s.pool r j) :
      NetStep P s (Sum.inr (.gdlv r i j m)) (PMF.pure s)
  /-- The network's half of a DECIDED relay: the payload must not be pooled
  yet (D12′). -/
  | dsnd (s : NetState P.n) (j : Fin P.n) (b : Bool) (h : b ∉ s.dpool j) :
      NetStep P s (Sum.inr (.dsnd j b)) (PMF.pure (s.dput j b))
  /-- The network's half of a DECIDED delivery: the payload must be pooled
  under the named sender (D12′). -/
  | ddlv (s : NetState P.n) (i j : Fin P.n) (b : Bool) (h : b ∈ s.dpool j) :
      NetStep P s (Sum.inr (.ddlv i j b)) (PMF.pure s)
  /-- The network's half of the fused coin return: pool the published payload
  (D10, D12′). -/
  | retWPub (s : NetState P.n) (r : ℕ) (id : Fin P.n) (c : Bool) (b : Bool) :
      NetStep P s (Sum.inr (.retWPub r id c b)) (PMF.pure (s.dput id b))
  /-- A graded-agreement call against an already-called stage record sends
  nothing. -/
  | gcallLoop (s : NetState P.n) (r : ℕ) (id : Fin P.n) (b : Bool) :
      NetStep P s (Sum.inr (.gcallLoop r id b)) (PMF.pure s)
  /-- A Byzantine graded-agreement call (D11): authorised here, and its
  `⟨INPUT, b⟩` multicast pooled here. -/
  | byzCallG (s : NetState P.n) (r : ℕ) (k : Fin P.n) (b : Bool) (hF : k ∈ s.F) :
      NetStep P s (Sum.inr (.byzCallG r k b)) (PMF.pure (s.gpool r k (.input b)))
  /-- A Byzantine graded-agreement call against an already-called stage record
  (D11). -/
  | byzCallGLoop (s : NetState P.n) (r : ℕ) (k : Fin P.n) (b : Bool)
      (hF : k ∈ s.F) :
      NetStep P s (Sum.inr (.byzCallGLoop r k b)) (PMF.pure s)
  /-- A Byzantine graded-agreement return (D11). -/
  | byzRetG (s : NetState P.n) (r : ℕ) (k : Fin P.n) (out : GbcaOut)
      (hF : k ∈ s.F) :
      NetStep P s (Sum.inr (.byzRetG r k out)) (PMF.pure s)
  /-- A Byzantine coin call (D11). -/
  | byzCallW (s : NetState P.n) (r : ℕ) (k : Fin P.n) (hF : k ∈ s.F) :
      NetStep P s (Sum.inr (.byzCallW r k)) (PMF.pure s)
  /-- A Byzantine coin return (D11). -/
  | byzRetW (s : NetState P.n) (r : ℕ) (k : Fin P.n) (b : Bool) (hF : k ∈ s.F) :
      NetStep P s (Sum.inr (.byzRetW r k b)) (PMF.pure s)
  /-- An external input is not the network's business. -/
  | callABAIdle (s : NetState P.n) (id : Fin P.n) (b : Bool) :
      NetStep P s (Sum.inl (.callABA id b)) (PMF.pure s)
  /-- A return requires the returning process to have multicast the payload —
  a condition on its pool (D12′). -/
  | retABA (s : NetState P.n) (id : Fin P.n) (b : Bool) (h : b ∈ s.dpool id) :
      NetStep P s (Sum.inl (.retABA id b)) (PMF.pure s)
  /-- A corrupted process returns whatever it likes (D23): its program has been
  replaced, so the DECIDED evidence the honest row asks for is not required of
  it. The authorisation is this component's `id ∈ F`, and the process's half is
  the replaced program's self-loop. -/
  | retByz (s : NetState P.n) (id : Fin P.n) (b : Bool) (hF : id ∈ s.F) :
      NetStep P s (Sum.inl (.retABA id b)) (PMF.pure s)
  /-- The graded-agreement call multicasts `⟨INPUT, b⟩`: the network pools it. -/
  | callG (s : NetState P.n) (r : ℕ) (id : Fin P.n) (b : Bool) :
      NetStep P s (Sum.inl (.callG r id b)) (PMF.pure (s.gpool r id (.input b)))
  /-- A graded-agreement return sends nothing. -/
  | retGIdle (s : NetState P.n) (r : ℕ) (id : Fin P.n) (out : GbcaOut) :
      NetStep P s (Sum.inl (.retG r id out)) (PMF.pure s)
  /-- A coin call sends nothing. -/
  | callWIdle (s : NetState P.n) (r : ℕ) (id : Fin P.n) :
      NetStep P s (Sum.inl (.callW r id)) (PMF.pure s)
  /-- An unfused coin return sends nothing. -/
  | retWIdle (s : NetState P.n) (r : ℕ) (id : Fin P.n) (c : Bool) :
      NetStep P s (Sum.inl (.retW r id c)) (PMF.pure s)
  /-- Corruption (deviation D1): total, Dirac, budget-guarded; no process
  record keeps a copy. -/
  | fail (s : NetState P.n) (k : Fin P.n) (hnew : k ∉ s.F) (hbud : s.F.card < P.f) :
      NetStep P s (Sum.inl (.fail k)) (PMF.pure (s.corrupt P k))
  /-- Byzantine stage injection (D5, D11): the network multicasts on behalf of
  a corrupted sender. -/
  | byzG (s : NetState P.n) (r : ℕ) (k : Fin P.n) (m : GBCA.Msg) (hF : k ∈ s.F) :
      NetStep P s (Sum.inl .tau) (PMF.pure (s.gpool r k m))
  /-- Byzantine DECIDED injection (D12′): either or both bits, at any time, so
  a corrupted process may equivocate. -/
  | byzD (s : NetState P.n) (k : Fin P.n) (b : Bool) (hF : k ∈ s.F) :
      NetStep P s (Sum.inl .tau) (PMF.pure (s.dput k b))

/-! ### The automata and the composition pipeline -/

/-- The program of process `j`. -/
noncomputable def ABAProcN (P : Params) (j : Fin P.n) :
    System (ProcRec P.n) (NLab P.n) where
  init := (CoreRec.initial P.n, StageSideRec.initial P.n)
  step := ABAProcStepN P j

@[simp] theorem ABAProcN_init (P : Params) (j : Fin P.n) :
    (ABAProcN P j).init = (CoreRec.initial P.n, StageSideRec.initial P.n) := rfl

@[simp] theorem ABAProcN_step (P : Params) (j : Fin P.n) (q : ProcRec P.n)
    (l : NLab P.n) (μ : PMF (ProcRec P.n)) :
    (ABAProcN P j).step q l μ ↔ ABAProcStepN P j q l μ := Iff.rfl

/-- The network adversary. -/
noncomputable def netAdv (P : Params) : System (NetState P.n) (NLab P.n) where
  init := NetState.initial P.n
  step := NetStep P

@[simp] theorem netAdv_init (P : Params) : (netAdv P).init = NetState.initial P.n := rfl

@[simp] theorem netAdv_step (P : Params) (s : NetState P.n) (l : NLab P.n)
    (μ : PMF (NetState P.n)) : (netAdv P).step s l μ ↔ NetStep P s l μ := Iff.rfl

end Net

/-- The state of the protocol: the process family, the network adversary and
the coin oracle. -/
abbrev ProtocolState (P : Params) : Type :=
  (∀ _ : Fin P.n, Net.ProcRec P.n) × (Net.NetState P.n × (ℕ → WCC.SpecState P.n))

/-- The three components side by side, over the extended alphabet: the
synchronised process group, the network adversary and the lifted oracle. -/
noncomputable def protocolPre (P : Params) : System (ProtocolState P) (Net.NLab P.n) :=
  (System.syncProduct (Net.ABAProcN P)).parallel
    ((Net.netAdv P).parallel (Net.wccLift P))

/-- **The protocol group**: the rendezvous alphabet hidden, the result read
back over `Lab n`. -/
noncomputable def protocolGroup (P : Params) : System (ProtocolState P) (Lab P.n) :=
  ((protocolPre P).abstract (Net.netEvtLabels P.n)).relabel

/-- **The protocol system**: the group with the sub-protocol API hidden. -/
noncomputable def protocol (P : Params) : System (ProtocolState P) (Lab P.n) :=
  (protocolGroup P).abstract (Lab.hiddenAPI P.n)

namespace Net

/-! ### Determinacy of the two rule tables

The composite is not an LTS — the coin resolution is probabilistic — but both
of the tables written here are Dirac. -/

/-- Every process transition is Dirac. -/
theorem procStepN_dirac {P : Params} {j : Fin P.n} {q : ProcRec P.n}
    {l : NLab P.n} {ν : PMF (ProcRec P.n)} (h : ABAProcStepN P j q l ν) :
    ∃ q', ν = PMF.pure q' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every network transition is Dirac. -/
theorem netStep_dirac {P : Params} {s : NetState P.n} {l : NLab P.n}
    {μ : PMF (NetState P.n)} (h : NetStep P s l μ) : ∃ s', μ = PMF.pure s' := by
  cases h <;> exact ⟨_, rfl⟩

/-- The one `τ` row of a process's table is `terminate`: a silent step of a
program is that program's own termination, taken on a fired return and DECIDED
receipts from `2f + 1` distinct senders (D22). A replaced program has no silent
row at all, so the reading carries `corrupted = false` (D23). -/
theorem stepN_tau_terminate {P : Params} {j : Fin P.n} {q : ProcRec P.n}
    {ν : PMF (ProcRec P.n)} (h : ABAProcStepN P j q (Silent.τ : NLab P.n) ν) :
    ∃ b : Bool, q.1.corrupted = false ∧ q.1.proc.returned = true ∧
      2 * P.f + 1 ≤ q.1.decidedCount b ∧ q.2.terminated = false ∧
      ν = PMF.pure (q.1, { q.2 with terminated := true }) := by
  rw [nlab_tau] at h
  cases h with
  | terminate c p b hh hret hcnt hterm => exact ⟨b, hh, hret, hcnt, hterm, rfl⟩
  | corruptedIdle c p L hh hτ hown => exact absurd rfl hτ

/-! ### Reading composite transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ parallel ∘ syncProduct`; the
lemmas below unfold it once and for all. -/

/-- A synchronised transition of the process group on a visible label: every
process steps, and the joint distribution is Dirac. -/
theorem syncN_inv {P : Params} {u : ∀ _ : Fin P.n, ProcRec P.n} {l : NLab P.n}
    {μ : PMF (∀ _ : Fin P.n, ProcRec P.n)} (hl : l ≠ Silent.τ)
    (h : (System.syncProduct (ABAProcN P)).step u l μ) :
    ∃ x : ∀ _ : Fin P.n, ProcRec P.n,
      μ = PMF.pure x ∧ ∀ i, ABAProcStepN P i (u i) l (PMF.pure (x i)) := by
  rw [System.syncProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨rfl, i, μ_i, hstep, -⟩
  · have hx : ∀ i, ∃ p', μ_ i = PMF.pure p' := fun i => procStepN_dirac (hall i)
    choose x hx using hx
    refine ⟨x, ?_, fun i => ?_⟩
    · rw [show μ_ = fun i => PMF.pure (x i) from funext hx]
      exact piPMF_pure x
    · rw [← hx i]; exact hall i
  · exact absurd rfl hl

/-- A silent transition of the process group: `τ` is interleaved, so exactly one
program moves and the rest hold their state. -/
theorem syncN_tau_inv {P : Params} {u : ∀ _ : Fin P.n, ProcRec P.n}
    {μ : PMF (∀ _ : Fin P.n, ProcRec P.n)}
    (h : (System.syncProduct (ABAProcN P)).step u (Silent.τ : NLab P.n) μ) :
    ∃ (i : Fin P.n) (y : ProcRec P.n),
      ABAProcStepN P i (u i) (Silent.τ : NLab P.n) (PMF.pure y) ∧
      μ = PMF.pure (Function.update u i y) := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, rfl⟩
  · exact absurd rfl hτ
  · obtain ⟨y, rfl⟩ := procStepN_dirac hstep
    exact ⟨i, y, hstep, by rw [piPMF_update_pure, PMF.pure_map]⟩

/-- The composite step relation of the protocol group, unfolded to the hidden
rendezvous case and the shared-label case. -/
theorem protocolGroup_step_iff (P : Params)
    (q : (∀ _ : Fin P.n, ProcRec P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n)))
    (l : Lab P.n)
    (μ : PMF ((∀ _ : Fin P.n, ProcRec P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))) :
    (protocolGroup P).step q l μ ↔
      (l = .tau ∧ ∃ e : NetEvt P.n, (protocolPre P).step q (Sum.inr e) μ) ∨
      (protocolPre P).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_netEvtLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_netEvtLabels l, hstep⟩

/-- The protocol system's step relation: a sub-protocol API label seen as `τ`,
or a label that survives the hiding. -/
theorem protocol_step_iff (P : Params)
    (q : (∀ _ : Fin P.n, ProcRec P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n)))
    (l : Lab P.n)
    (μ : PMF ((∀ _ : Fin P.n, ProcRec P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))) :
    (protocol P).step q l μ ↔
      (l = .tau ∧ ∃ l' ∈ Lab.hiddenAPI P.n, (protocolGroup P).step q l' μ) ∨
      (l ∉ Lab.hiddenAPI P.n ∧ (protocolGroup P).step q l μ) :=
  System.abstract_step _ _ _ _ _

/-! ### One process's rules, by label class

Each lemma reads a row of the table off its label: the participant's row as
its guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. The state and the distribution are
variables, so `cases` unifies against any record. A participant's row carries
the health guard `corrupted = false`, and on a label outside `actsAt j` the
replaced program's self-loop is a second reading of the same label (D23). -/

section ProcInversion

variable {P : Params} {j : Fin P.n} {q : ProcRec P.n} {ν : PMF (ProcRec P.n)}

theorem stepN_callABA_own {b : Bool}
    (h : ABAProcStepN P j q (Sum.inl (.callABA j b)) ν) :
    (q.1.corrupted = false ∧ q.1.proc.input = none ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with
        input := some b, est := some b, round := 0, phase := .toCallG }, q.2)) ∨
    ν = PMF.pure q := by
  cases h
  case input => exact Or.inl ⟨by assumption, by assumption, rfl⟩
  case inputLoop => exact Or.inr rfl
  case callABAIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr rfl

theorem stepN_callABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ABAProcStepN P j q (Sum.inl (.callABA id b)) ν) : ν = PMF.pure q := by
  cases h
  case input => exact absurd rfl hid
  case inputLoop => exact absurd rfl hid
  case callABAIdle => rfl
  case corruptedIdle => rfl

theorem stepN_retABA_own {b : Bool}
    (h : ABAProcStepN P j q (Sum.inl (.retABA j b)) ν) :
    (q.1.corrupted = false ∧ q.1.proc.input ≠ none ∧
      P.n - P.f ≤ q.1.decidedCount b ∧ q.1.proc.returned = false ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with returned := true }, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case ret =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retABAIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem stepN_retABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ABAProcStepN P j q (Sum.inl (.retABA id b)) ν) : ν = PMF.pure q := by
  cases h
  case ret => exact absurd rfl hid
  case retABAIdle => rfl
  case corruptedIdle => rfl

theorem stepN_callG_own {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inl (.callG r j b)) ν) :
    q.1.corrupted = false ∧
      q.1.proc.phase = .toCallG ∧ q.1.proc.round = r ∧ q.2.terminated = false ∧
      q.1.proc.est = some b ∧ (q.2.stage r).proc.input = none ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with phase := .awaitG },
        q.2.setStage r ((q.2.stage r).setP { (q.2.stage r).proc with
          input := some b,
          sentInput := Function.update (q.2.stage r).proc.sentInput b true })) := by
  cases h
  case callG_call =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case callGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_callG_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ABAProcStepN P j q (Sum.inl (.callG r id b)) ν) : ν = PMF.pure q := by
  cases h
  case callG_call => exact absurd rfl hid
  case callGIdle => rfl
  case corruptedIdle => rfl

theorem stepN_retG_A_own {r : ℕ} {v : Bool}
    (h : ABAProcStepN P j q (Sum.inl (.retG r j (.A v))) ν) :
    q.1.corrupted = false ∧
      q.1.proc.phase = .awaitG ∧ q.1.proc.round = r ∧ q.2.terminated = false ∧
      (q.2.stage r).proc.input ≠ none ∧ (q.2.stage r).proc.sentSeal ≠ none ∧
      P.n - P.f ≤ (q.2.stage r).recvCount (.seal (some v)) ∧
      (q.2.stage r).proc.returned = false ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with
          est := (GbcaOut.A v).est, lastGrade := some (.A v), phase := .toCallW },
        q.2.setStage r
          ((q.2.stage r).setP { (q.2.stage r).proc with returned := true })) := by
  cases h
  case retG_A =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_retG_B_own {r : ℕ} {v : Bool}
    (h : ABAProcStepN P j q (Sum.inl (.retG r j (.B v))) ν) :
    q.1.corrupted = false ∧
      q.1.proc.phase = .awaitG ∧ q.1.proc.round = r ∧ q.2.terminated = false ∧
      (q.2.stage r).proc.input ≠ none ∧ (q.2.stage r).proc.sentSeal ≠ none ∧
      (∀ v, (q.2.stage r).recvCount (.seal (some v)) < P.n - P.f) ∧
      P.n - P.f ≤ (q.2.stage r).sealCount ∧
      (∃ k, GBCA.Msg.seal (some v) ∈ (q.2.stage r).inbox k) ∧
      P.f + 1 ≤ (q.2.stage r).recvCount (.bind (some v)) ∧
      (q.2.stage r).bothValid P ∧
      (q.2.stage r).proc.returned = false ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with
          est := (GbcaOut.B v).est, lastGrade := some (.B v), phase := .toCallW },
        q.2.setStage r
          ((q.2.stage r).setP { (q.2.stage r).proc with returned := true })) := by
  cases h
  case retG_B =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_retG_C_own {r : ℕ}
    (h : ABAProcStepN P j q (Sum.inl (.retG r j .C)) ν) :
    q.1.corrupted = false ∧
      q.1.proc.phase = .awaitG ∧ q.1.proc.round = r ∧ q.2.terminated = false ∧
      (q.2.stage r).proc.input ≠ none ∧ (q.2.stage r).proc.sentSeal ≠ none ∧
      (∀ v, (q.2.stage r).recvCount (.seal (some v)) < P.n - P.f) ∧
      (∀ v, (∃ k, GBCA.Msg.seal (some v) ∈ (q.2.stage r).inbox k) →
        (q.2.stage r).recvCount (.bind (some v)) < P.f + 1) ∧
      P.n - P.f ≤ (q.2.stage r).recvCount (.seal none) ∧
      (q.2.stage r).bothValid P ∧
      (q.2.stage r).proc.returned = false ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with
          est := GbcaOut.C.est, lastGrade := some .C, phase := .toCallW },
        q.2.setStage r
          ((q.2.stage r).setP { (q.2.stage r).proc with returned := true })) := by
  cases h
  case retG_C =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_retG_foreign {r : ℕ} {id : Fin P.n} {out : GbcaOut} (hid : id ≠ j)
    (h : ABAProcStepN P j q (Sum.inl (.retG r id out)) ν) : ν = PMF.pure q := by
  cases h
  case retG_A => exact absurd rfl hid
  case retG_B => exact absurd rfl hid
  case retG_C => exact absurd rfl hid
  case retGIdle => rfl
  case corruptedIdle => rfl

theorem stepN_callW_own {r : ℕ}
    (h : ABAProcStepN P j q (Sum.inl (.callW r j)) ν) :
    (q.1.corrupted = false ∧ q.1.proc.phase = .toCallW ∧ q.1.proc.round = r ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with phase := .awaitW }, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case callW => exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case callWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem stepN_callW_foreign {r : ℕ} {id : Fin P.n} (hid : id ≠ j)
    (h : ABAProcStepN P j q (Sum.inl (.callW r id)) ν) : ν = PMF.pure q := by
  cases h
  case callW => exact absurd rfl hid
  case callWIdle => rfl
  case corruptedIdle => rfl

theorem stepN_retW_own {r : ℕ} {co : Bool}
    (h : ABAProcStepN P j q (Sum.inl (.retW r j co)) ν) :
    (q.1.corrupted = false ∧ q.1.proc.phase = .awaitW ∧ q.1.proc.round = r ∧
      (∀ v : Bool, q.1.proc.lastGrade ≠ some (.A v)) ∧
      ν = PMF.pure (q.1.stepRound co, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case retW =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem stepN_retW_foreign {r : ℕ} {id : Fin P.n} {co : Bool} (hid : id ≠ j)
    (h : ABAProcStepN P j q (Sum.inl (.retW r id co)) ν) : ν = PMF.pure q := by
  cases h
  case retW => exact absurd rfl hid
  case retWIdle => rfl
  case corruptedIdle => rfl

/-- The process's own corruption (D23): the flag goes up on a program not yet
replaced, and a replaced program stands still. -/
theorem stepN_fail_own (h : ABAProcStepN P j q (Sum.inl (.fail j)) ν) :
    (q.1.corrupted = false ∧
      ν = PMF.pure ({ q.1 with corrupted := true }, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case failSelf => exact Or.inl ⟨by assumption, rfl⟩
  case failIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem stepN_fail_foreign {k : Fin P.n} (hk : k ≠ j)
    (h : ABAProcStepN P j q (Sum.inl (.fail k)) ν) : ν = PMF.pure q := by
  cases h
  case failSelf => exact absurd rfl hk
  case failIdle => rfl
  case corruptedIdle => rfl

end ProcInversion

/-! ### One process's rules on the rendezvous alphabet

The Byzantine stage drives have no row at the process they name (D22, D23), so
on `byzCallG`, `byzCallGLoop` and `byzRetG` every process idles and there is no
participant's row to read. -/

section ProcNetInversion

variable {P : Params} {j : Fin P.n} {q : ProcRec P.n} {ν : PMF (ProcRec P.n)}

theorem stepN_gsnd_input_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.input b))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.stage r).proc.input ≠ none ∧
      P.f + 1 ≤ (q.2.stage r).recvCount (.input b) ∧
      (q.2.stage r).proc.sentInput b = false ∧
      ν = PMF.pure (q.1, q.2.setStage r ((q.2.stage r).setP { (q.2.stage r).proc with
        sentInput := Function.update (q.2.stage r).proc.sentInput b true })) := by
  cases h
  case gsndRelay =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gsnd_echo_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.echo b))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.stage r).proc.input ≠ none ∧
      P.n - P.f ≤ (q.2.stage r).recvCount (.input b) ∧
      (q.2.stage r).proc.sentEcho = none ∧
      ν = PMF.pure (q.1, q.2.setStage r
        ((q.2.stage r).setP { (q.2.stage r).proc with sentEcho := some b })) := by
  cases h
  case gsndEcho =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gsnd_voteBit_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.vote (some b)))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.stage r).proc.input ≠ none ∧
      P.n - P.f ≤ (q.2.stage r).recvCount (.echo b) ∧
      (q.2.stage r).proc.sentVote = none ∧
      ν = PMF.pure (q.1, q.2.setStage r
        ((q.2.stage r).setP { (q.2.stage r).proc with sentVote := some (some b) })) := by
  cases h
  case gsndVoteBit =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gsnd_voteBot_self {r : ℕ}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.vote none))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.stage r).proc.input ≠ none ∧
      (∀ b, (q.2.stage r).recvCount (.echo b) < P.n - P.f) ∧
      P.n - P.f ≤ (q.2.stage r).echoCount ∧
      (q.2.stage r).bothValid P ∧ (q.2.stage r).proc.sentVote = none ∧
      ν = PMF.pure (q.1, q.2.setStage r
        ((q.2.stage r).setP { (q.2.stage r).proc with sentVote := some none })) := by
  cases h
  case gsndVoteBot =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gsnd_bindBit_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.bind (some b)))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.stage r).proc.input ≠ none ∧
      (q.2.stage r).proc.sentVote ≠ none ∧
      P.n - P.f ≤ (q.2.stage r).recvCount (.vote (some b)) ∧
      (q.2.stage r).proc.sentBind = none ∧
      ν = PMF.pure (q.1, q.2.setStage r
        ((q.2.stage r).setP { (q.2.stage r).proc with sentBind := some (some b) })) := by
  cases h
  case gsndBindBit =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gsnd_bindBot_self {r : ℕ}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.bind none))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.stage r).proc.input ≠ none ∧
      (q.2.stage r).proc.sentVote ≠ none ∧
      (∀ b, (q.2.stage r).recvCount (.vote (some b)) < P.n - P.f) ∧
      P.n - P.f ≤ (q.2.stage r).voteCount ∧
      (q.2.stage r).bothValid P ∧ (q.2.stage r).proc.sentBind = none ∧
      ν = PMF.pure (q.1, q.2.setStage r
        ((q.2.stage r).setP { (q.2.stage r).proc with sentBind := some none })) := by
  cases h
  case gsndBindBot =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gsnd_sealBit_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.seal (some b)))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.stage r).proc.input ≠ none ∧
      (q.2.stage r).proc.sentBind ≠ none ∧
      P.n - P.f ≤ (q.2.stage r).recvCount (.bind (some b)) ∧
      (q.2.stage r).proc.sentSeal = none ∧
      ν = PMF.pure (q.1, q.2.setStage r
        ((q.2.stage r).setP { (q.2.stage r).proc with sentSeal := some (some b) })) := by
  cases h
  case gsndSealBit =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gsnd_sealBot_self {r : ℕ}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.seal none))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.stage r).proc.input ≠ none ∧
      (q.2.stage r).proc.sentBind ≠ none ∧
      (∀ b, (q.2.stage r).recvCount (.bind (some b)) < P.n - P.f) ∧
      P.n - P.f ≤ (q.2.stage r).bindCount ∧
      (q.2.stage r).bothValid P ∧ (q.2.stage r).proc.sentSeal = none ∧
      ν = PMF.pure (q.1, q.2.setStage r
        ((q.2.stage r).setP { (q.2.stage r).proc with sentSeal := some none })) := by
  cases h
  case gsndSealBot =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gsnd_foreign {r : ℕ} {k : Fin P.n} {m : GBCA.Msg} (hk : k ≠ j)
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r k m)) ν) : ν = PMF.pure q := by
  cases h
  case gsndRelay => exact absurd rfl hk
  case gsndEcho => exact absurd rfl hk
  case gsndVoteBit => exact absurd rfl hk
  case gsndVoteBot => exact absurd rfl hk
  case gsndBindBit => exact absurd rfl hk
  case gsndBindBot => exact absurd rfl hk
  case gsndSealBit => exact absurd rfl hk
  case gsndSealBot => exact absurd rfl hk
  case gsndIdle => rfl
  case corruptedIdle => rfl

theorem stepN_gdlv_self {r : ℕ} {k : Fin P.n} {m : GBCA.Msg}
    (h : ABAProcStepN P j q (Sum.inr (.gdlv r j k m)) ν) :
    q.1.corrupted = false ∧ q.2.terminated = false ∧
      ν = PMF.pure (q.1, q.2.deliverTo r k m) := by
  cases h
  case gdlvRecv => exact ⟨by assumption, by assumption, rfl⟩
  case gdlvIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gdlv_foreign {r : ℕ} {i k : Fin P.n} {m : GBCA.Msg} (hi : i ≠ j)
    (h : ABAProcStepN P j q (Sum.inr (.gdlv r i k m)) ν) : ν = PMF.pure q := by
  cases h
  case gdlvRecv => exact absurd rfl hi
  case gdlvIdle => rfl
  case corruptedIdle => rfl

theorem stepN_dsnd_self {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.dsnd j b)) ν) :
    (q.1.corrupted = false ∧ q.1.proc.input ≠ none ∧
      P.f + 1 ≤ q.1.decidedCount b ∧ ν = PMF.pure q) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case dsndRelay =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case dsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem stepN_dsnd_foreign {k : Fin P.n} {b : Bool} (hk : k ≠ j)
    (h : ABAProcStepN P j q (Sum.inr (.dsnd k b)) ν) : ν = PMF.pure q := by
  cases h
  case dsndRelay => exact absurd rfl hk
  case dsndIdle => rfl
  case corruptedIdle => rfl

theorem stepN_ddlv_self {k : Fin P.n} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.ddlv j k b)) ν) :
    q.1.corrupted = false ∧ b ∉ q.1.decIn k ∧
      ν = PMF.pure (q.1.recvDec k b, q.2) := by
  cases h
  case ddlvRecv => exact ⟨by assumption, by assumption, rfl⟩
  case ddlvIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_ddlv_foreign {i k : Fin P.n} {b : Bool} (hi : i ≠ j)
    (h : ABAProcStepN P j q (Sum.inr (.ddlv i k b)) ν) : ν = PMF.pure q := by
  cases h
  case ddlvRecv => exact absurd rfl hi
  case ddlvIdle => rfl
  case corruptedIdle => rfl

theorem stepN_retWPub_self {r : ℕ} {co b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.retWPub r j co b)) ν) :
    q.1.corrupted = false ∧
      q.1.proc.phase = .awaitW ∧ q.1.proc.round = r ∧
      q.1.proc.lastGrade = some (.A b) ∧
      ν = PMF.pure (q.1.stepRound co, q.2) := by
  cases h
  case retWPub =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retWPubIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_retWPub_foreign {r : ℕ} {id : Fin P.n} {co b : Bool} (hid : id ≠ j)
    (h : ABAProcStepN P j q (Sum.inr (.retWPub r id co b)) ν) : ν = PMF.pure q := by
  cases h
  case retWPub => exact absurd rfl hid
  case retWPubIdle => rfl
  case corruptedIdle => rfl

theorem stepN_gcallLoop_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gcallLoop r j b)) ν) :
    q.1.corrupted = false ∧
      q.1.proc.phase = .toCallG ∧ q.1.proc.round = r ∧ q.1.proc.est = some b ∧
      (q.2.stage r).proc.input ≠ none ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with phase := .awaitG }, q.2) := by
  cases h
  case gcallLoop =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case gcallLoopIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gcallLoop_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ABAProcStepN P j q (Sum.inr (.gcallLoop r id b)) ν) : ν = PMF.pure q := by
  cases h
  case gcallLoop => exact absurd rfl hid
  case gcallLoopIdle => rfl
  case corruptedIdle => rfl

theorem stepN_byzCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.byzCallGLoop r k b)) ν) : ν = PMF.pure q := by
  cases h <;> rfl

theorem stepN_byzCallW {r : ℕ} {k : Fin P.n}
    (h : ABAProcStepN P j q (Sum.inr (.byzCallW r k)) ν) : ν = PMF.pure q := by
  cases h <;> rfl

theorem stepN_byzRetW {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.byzRetW r k b)) ν) : ν = PMF.pure q := by
  cases h <;> rfl

/-- **The replaced program writes nothing** (D23). Whatever the label, a
process whose flag is up leaves both halves of its record where they stand.
The proof is by cases on the table: every row that writes carries the health
guard, so no row of a replaced program survives except a self-loop. -/
theorem stepN_inert {L : NLab P.n} (hc : q.1.corrupted = true)
    (h : ABAProcStepN P j q L ν) : ν = PMF.pure q := by
  cases h <;> simp_all

end ProcNetInversion

/-! ### The network adversary's rules, by label class -/

section NetInversion

variable {P : Params} {s : NetState P.n} {μ : PMF (NetState P.n)}

theorem netStep_gsnd {r : ℕ} {j : Fin P.n} {m : GBCA.Msg}
    (h : NetStep P s (Sum.inr (.gsnd r j m)) μ) : μ = PMF.pure (s.gpool r j m) := by
  cases h; rfl

theorem netStep_gdlv {r : ℕ} {i j : Fin P.n} {m : GBCA.Msg}
    (h : NetStep P s (Sum.inr (.gdlv r i j m)) μ) :
    m ∈ s.pool r j ∧ μ = PMF.pure s := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netStep_dsnd {j : Fin P.n} {b : Bool}
    (h : NetStep P s (Sum.inr (.dsnd j b)) μ) :
    b ∉ s.dpool j ∧ μ = PMF.pure (s.dput j b) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netStep_ddlv {i j : Fin P.n} {b : Bool}
    (h : NetStep P s (Sum.inr (.ddlv i j b)) μ) :
    b ∈ s.dpool j ∧ μ = PMF.pure s := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netStep_retWPub {r : ℕ} {id : Fin P.n} {c b : Bool}
    (h : NetStep P s (Sum.inr (.retWPub r id c b)) μ) :
    μ = PMF.pure (s.dput id b) := by
  cases h; rfl

theorem netStep_gcallLoop {r : ℕ} {id : Fin P.n} {b : Bool}
    (h : NetStep P s (Sum.inr (.gcallLoop r id b)) μ) : μ = PMF.pure s := by
  cases h; rfl

theorem netStep_byzCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : NetStep P s (Sum.inr (.byzCallGLoop r k b)) μ) :
    k ∈ s.F ∧ μ = PMF.pure s := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netStep_byzCallW {r : ℕ} {k : Fin P.n}
    (h : NetStep P s (Sum.inr (.byzCallW r k)) μ) :
    k ∈ s.F ∧ μ = PMF.pure s := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netStep_byzRetW {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : NetStep P s (Sum.inr (.byzRetW r k b)) μ) :
    k ∈ s.F ∧ μ = PMF.pure s := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netStep_callABA {id : Fin P.n} {b : Bool}
    (h : NetStep P s (Sum.inl (.callABA id b)) μ) : μ = PMF.pure s := by
  cases h; rfl

/-- A return is authorised either by the DECIDED pool of the returning process
or by its corruption (D23); the two rows share the label and the identity
successor. -/
theorem netStep_retABA {id : Fin P.n} {b : Bool}
    (h : NetStep P s (Sum.inl (.retABA id b)) μ) :
    (b ∈ s.dpool id ∨ id ∈ s.F) ∧ μ = PMF.pure s := by
  cases h
  case retABA => exact ⟨Or.inl (by assumption), rfl⟩
  case retByz => exact ⟨Or.inr (by assumption), rfl⟩

theorem netStep_callG {r : ℕ} {id : Fin P.n} {b : Bool}
    (h : NetStep P s (Sum.inl (.callG r id b)) μ) :
    μ = PMF.pure (s.gpool r id (.input b)) := by
  cases h; rfl

theorem netStep_retG {r : ℕ} {id : Fin P.n} {out : GbcaOut}
    (h : NetStep P s (Sum.inl (.retG r id out)) μ) : μ = PMF.pure s := by
  cases h; rfl

theorem netStep_callW {r : ℕ} {id : Fin P.n}
    (h : NetStep P s (Sum.inl (.callW r id)) μ) : μ = PMF.pure s := by
  cases h; rfl

theorem netStep_retW {r : ℕ} {id : Fin P.n} {c : Bool}
    (h : NetStep P s (Sum.inl (.retW r id c)) μ) : μ = PMF.pure s := by
  cases h; rfl

theorem netStep_fail {k : Fin P.n}
    (h : NetStep P s (Sum.inl (.fail k)) μ) :
    k ∉ s.F ∧ s.F.card < P.f ∧ μ = PMF.pure (s.corrupt P k) := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

theorem netStep_tau (h : NetStep P s (Sum.inl .tau) μ) :
    (∃ (r : ℕ) (k : Fin P.n) (m : GBCA.Msg), k ∈ s.F ∧ μ = PMF.pure (s.gpool r k m)) ∨
    (∃ (k : Fin P.n) (b : Bool), k ∈ s.F ∧ μ = PMF.pure (s.dput k b)) := by
  cases h
  case byzG => exact Or.inl ⟨_, _, _, by assumption, rfl⟩
  case byzD => exact Or.inr ⟨_, _, by assumption, rfl⟩

end NetInversion

/-! ### The network's own field algebra

Each of the network adversary's three writes — a stage multicast, a DECIDED
multicast, and corruption — touches one field of `NetState` and leaves the
other two alone. -/

@[simp] theorem gpool_pool_self {n : ℕ} (s : NetState n) (r : ℕ) (j : Fin n)
    (m : GBCA.Msg) :
    (s.gpool r j m).pool r = Function.update (s.pool r) j (insert m (s.pool r j)) := by
  simp [NetState.gpool]

theorem gpool_pool_ne {n : ℕ} (s : NetState n) (r : ℕ) (j : Fin n) (m : GBCA.Msg)
    {r' : ℕ} (h : r' ≠ r) : (s.gpool r j m).pool r' = s.pool r' := by
  simp [NetState.gpool, Function.update_of_ne h]

@[simp] theorem gpool_dpool {n : ℕ} (s : NetState n) (r : ℕ) (j : Fin n)
    (m : GBCA.Msg) : (s.gpool r j m).dpool = s.dpool := rfl

@[simp] theorem gpool_F {n : ℕ} (s : NetState n) (r : ℕ) (j : Fin n)
    (m : GBCA.Msg) : (s.gpool r j m).F = s.F := rfl

@[simp] theorem dput_pool {n : ℕ} (s : NetState n) (j : Fin n) (b : Bool) :
    (s.dput j b).pool = s.pool := rfl

@[simp] theorem dput_dpool {n : ℕ} (s : NetState n) (j : Fin n) (b : Bool) :
    (s.dput j b).dpool = Function.update s.dpool j (insert b (s.dpool j)) := rfl

@[simp] theorem dput_F {n : ℕ} (s : NetState n) (j : Fin n) (b : Bool) :
    (s.dput j b).F = s.F := rfl

@[simp] theorem netCorrupt_pool {P : Params} (s : NetState P.n) (k : Fin P.n) :
    (NetState.corrupt P k s).pool = s.pool := by
  unfold NetState.corrupt; split <;> rfl

@[simp] theorem netCorrupt_dpool {P : Params} (s : NetState P.n) (k : Fin P.n) :
    (NetState.corrupt P k s).dpool = s.dpool := by
  unfold NetState.corrupt; split <;> rfl

/-! ### Reading a protocol transition into its three components -/

/-- A rendezvous transition: every process, the network and the lifted oracle
move together, and only the oracle's successor can fail to be a Dirac. -/
theorem protocolPre_event_inv (P : Params) {u : ∀ _ : Fin P.n, ProcRec P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n} {e : NetEvt P.n}
    {μ : PMF ((∀ _ : Fin P.n, ProcRec P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (protocolPre P).step (u, w, o) (Sum.inr e) μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcRec P.n) (w' : NetState P.n)
      (μ₃ : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, ABAProcStepN P i (u i) (Sum.inr e) (PMF.pure (x i))) ∧
      NetStep P w (Sum.inr e) (PMF.pure w') ∧
      (wccLift P).step o (Sum.inr e) μ₃ ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') μ₃) := by
  rw [protocolPre, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂₃, hS, hNW, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
  · obtain ⟨x, rfl, hall⟩ := syncN_inv (by simp) hS
    rw [System.parallel_step] at hNW
    rcases hNW with ⟨-, μ₂, μ₃, hN, hO, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
    · obtain ⟨w', rfl⟩ := netStep_dirac hN
      exact ⟨x, w', μ₃, hall, hN, hO, rfl⟩
    · simp [nlab_tau] at habs
    · simp [nlab_tau] at habs
  · simp [nlab_tau] at habs
  · simp [nlab_tau] at habs

/-- A visible shared-label transition. -/
theorem protocolPre_lab_inv (P : Params) {u : ∀ _ : Fin P.n, ProcRec P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n} {l : Lab P.n} (hl : l ≠ Lab.tau)
    {μ : PMF ((∀ _ : Fin P.n, ProcRec P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (protocolPre P).step (u, w, o) (Sum.inl l) μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcRec P.n) (w' : NetState P.n)
      (ω : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, ABAProcStepN P i (u i) (Sum.inl l) (PMF.pure (x i))) ∧
      NetStep P w (Sum.inl l) (PMF.pure w') ∧
      (WCC.specFamily P).step o l ω ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω) := by
  rw [protocolPre, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂₃, hS, hNW, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
  · obtain ⟨x, rfl, hall⟩ :=
      syncN_inv (by rw [nlab_tau]; exact fun hh => hl (Sum.inl_injective hh)) hS
    rw [System.parallel_step] at hNW
    rcases hNW with ⟨-, μ₂, μ₃, hN, hO, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
    · obtain ⟨w', rfl⟩ := netStep_dirac hN
      exact ⟨x, w', μ₃, hall, hN,
        (System.mapIdle_step_some (wccPull_inl l) μ₃).mp hO, rfl⟩
    · rw [nlab_tau] at habs; exact absurd (Sum.inl_injective habs) hl
    · rw [nlab_tau] at habs; exact absurd (Sum.inl_injective habs) hl
  · rw [nlab_tau] at habs; exact absurd (Sum.inl_injective habs) hl
  · rw [nlab_tau] at habs; exact absurd (Sum.inl_injective habs) hl

/-- A silent shared-label transition: one process terminating, the network's own
injection, or the coin resolution. -/
theorem protocolPre_tau_inv (P : Params) {u : ∀ _ : Fin P.n, ProcRec P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {μ : PMF ((∀ _ : Fin P.n, ProcRec P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (protocolPre P).step (u, w, o) (Sum.inl Lab.tau) μ) :
    (∃ (i : Fin P.n) (y : ProcRec P.n),
      ABAProcStepN P i (u i) (Sum.inl Lab.tau) (PMF.pure y) ∧
      μ = PMF.pure (Function.update u i y, w, o)) ∨
    (∃ w', NetStep P w (Sum.inl .tau) (PMF.pure w') ∧ μ = PMF.pure (u, w', o)) ∨
    (∃ ω, (WCC.specFamily P).step o Lab.tau ω ∧
      μ = prodPMF (PMF.pure u) (prodPMF (PMF.pure w) ω)) := by
  rw [protocolPre, System.parallel_step] at h
  rcases h with ⟨habs, -⟩ | ⟨-, μ₁, hS, rfl⟩ | ⟨-, μ₂₃, hNW, rfl⟩
  · exact absurd rfl habs
  · obtain ⟨i, y, hstep, rfl⟩ := syncN_tau_inv hS
    exact Or.inl ⟨i, y, hstep, by rw [prodPMF_pure_pure]⟩
  · rw [System.parallel_step] at hNW
    rcases hNW with ⟨habs, -⟩ | ⟨-, μ₂, hN, rfl⟩ | ⟨-, μ₃, hO, rfl⟩
    · exact absurd rfl habs
    · obtain ⟨w', rfl⟩ := netStep_dirac hN
      exact Or.inr (Or.inl ⟨w', hN, by rw [prodPMF_pure_pure, prodPMF_pure_pure]⟩)
    · exact Or.inr (Or.inr ⟨μ₃,
        (System.mapIdle_step_some (wccPull_inl Lab.tau) μ₃).mp hO, rfl⟩)

end Net

end ABA
end PLTS
