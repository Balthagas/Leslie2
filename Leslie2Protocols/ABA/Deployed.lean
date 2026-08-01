/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Core
import Leslie2Protocols.ABA.GBCAImpl
import Leslie2Protocols.ABA.SpecSafety
import Leslie2Protocols.ABA.WCCSpec
import Leslie2Protocols.Framework.IdleFamily
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SyncProduct

/-!
# ABA as corruption-blind programs beside a network adversary

The deployed reading of the protocol: `n` automata, each running one process's
code and nothing else, beside two boxes that are not processes — the network
adversary and the coin oracle.

A process node is exactly the data the program of that process may read: the
its round-loop record, one graded-agreement stage record per
round, and the messages that have been delivered to it. It holds no copy of
the corrupted set, no corruption flag, and no record of what it has sent. A
program is therefore *corruption-blind*: no guard of its rule table can ask
whether the process is honest, and no guard can ask what the process has
multicast. Its sub-protocol ports are input-enabled — a return arrives when
the evidence for it is on the node, whoever asked for it.

Everything a process may not see lives in the network adversary
`NetState`: the round-tagged message pools `pool r j`, the DECIDED pools
`dpool j`, and the corrupted set `F` with its budget. Multicast is a joint
step of the sender and the network — the sender writes its own record, the
network inserts the message into the sender's pool — and delivery is a joint
step of the network, which checks that the message really is in the sender's
pool, and the receiver, which files it under that sender's inbox row. Whether
a process may be driven off-protocol is decided by the network's `k ∈ F`
guard on the Byzantine labels, never by the process.

The coin oracle `WCC.specFamily` is the third factor and the only box whose
transitions are not Dirac. It speaks the shared alphabet `Lab n`, so it is
joined to the extended alphabet through a label pullback
(`System.mapIdle wccPull`): the handshake labels of the extended alphabet
are mapped onto the oracle's own handshake rows and every other extended
label leaves it idle.

`NetEvt n` is the auxiliary rendezvous alphabet the shared alphabet `Lab n`
cannot name — the two networks, the Byzantine drives, and the branches of a
handshake that the shared label does not distinguish. It is hidden by the
composition, so the composite `deployedGroup` speaks exactly `Lab n`.

## Model and deviations

* **D1 (determinised `fail`).** `NetState.corrupt` is the total Dirac
  function guarded by `k ∉ F ∧ |F| < f`; no process node records corruption,
  and the processes take the `fail` broadcast without moving. The coin oracle
  enters unchanged, keeping its own copy of the corrupted set and its
  budget-guarded `corrupt` — its resolution threshold reads it.
* **D5 (set-based network).** Multicasts are idempotent: `pool r j` is the
  set of messages `j` has multicast in stage `r`, and `inbox k` at a node is
  the set of messages from `k` the adversary has delivered there. Thresholds
  count distinct senders. A corrupted sender's injections enter its pool
  through the network's own `byzG` transition.
* **D8 (participation gating).** Stage sends require the node's stage record
  to have received its input.
* **D9 (0-based rounds).** `round : ℕ` starts at `0`.
* **D10 (fused DECIDED-send).** The coin return performs the round advance
  and, when the round's grade was `A b`, the `⟨DECIDED, b⟩` multicast, in one
  transition. The published payload is dictated by the node's own grade, so
  the fused case travels on its own rendezvous label `retWPub`, which carries
  the payload the network is to pool; the unfused case travels on the shared
  `retW` label.
* **D11 (Byzantine handshake drives).** A corrupted process may drive its
  sub-protocol handshakes arbitrarily. Each drive is a rendezvous label of
  its own, authorised by the network's `k ∈ F` guard: the process contributes
  only the instance-side content the monolithic rule has (a stage record
  write, or nothing), never a round-loop write.
* **D12′ (per-process DECIDED pools, equivocation-capable).** The DECIDED
  layer is the pool family `dpool j` beside the per-node receipt rows
  `decIn k`. The relay's write-once condition is a condition on the pool, so
  it is the network's conjunct of the relay rendezvous; the quorum condition
  is a condition on the node, so it is the process's. A corrupted process's
  injections (`byzD`) may put either or both bits into its pool, so the
  DECIDED layer admits equivocation.
* **D17 (δ-mass failure outcome).** Inherited from the coin oracle: a failed
  resolution enables no return.
* **D18 (the six-level ladder).** The stage rules are the six levels
  `INPUT / ECHO / VOTE / BIND / SEAL` and the three graded returns of the
  cited algorithm, not the four-round compression.

## The pipeline

`ABAProcN P j` is the program of process `j`; the programs are composed under
full synchronisation (`System.syncProduct`) and set beside `netAdv P` and the
lifted oracle. Hiding `NetEvt` and reading the result back over `Lab n` gives
`deployedGroup P`; hiding the sub-protocol API gives `deployed P`.

## What this file supplies

`deployed` is the subject of the refinement chain, and this file is where its
transition relation is pinned down: the rule tables of the process programs,
of the network adversary and of the coin pullback, the composition pipeline,
and the inversion lemmas that read a composite transition back into the rows
its components contributed. `ABA/Layered.lean` re-cuts the same system along
its layer boundaries and shows the two presentations achieve exactly the same
trace distributions (`layered_atd`); the chain to `ABA.spec` continues from
there in `ABA/LayeredSpec.lean`.
-/

namespace PLTS
namespace ABA

/-! ### The corruption-blind records -/

/-- The round-loop record of one process: its own control record and the
DECIDED payloads delivered to it, indexed by sender. There is no record of
what it has multicast — the DECIDED pools live in the network. -/
structure CoreNodeN (n : ℕ) : Type where
  /-- The process's own control record. -/
  proc : ProcCore n
  /-- The DECIDED payloads delivered to this process, indexed by sender. -/
  decIn : Fin n → Finset Bool
  deriving DecidableEq

namespace CoreNodeN

variable {n : ℕ}

/-- The initial round-loop record: idle control record, no receipts. -/
def initial (n : ℕ) : CoreNodeN n where
  proc := ProcCore.initial n
  decIn := fun _ => ∅

/-- The number of distinct senders whose `⟨DECIDED, b⟩` this process holds. -/
def decidedCount (q : CoreNodeN n) (b : Bool) : ℕ :=
  (Finset.univ.filter (fun k => b ∈ q.decIn k)).card

/-- Update the control record. -/
def setProc (q : CoreNodeN n) (p : ProcCore n) : CoreNodeN n := { q with proc := p }

/-- Record a delivered `⟨DECIDED, b⟩` from sender `k`. -/
def recvDec (q : CoreNodeN n) (k : Fin n) (b : Bool) : CoreNodeN n :=
  { q with decIn := Function.update q.decIn k (insert b (q.decIn k)) }

/-- The round advance on receiving the coin `c`: adopt the coin if the
estimate is `⊥`, clear the grade, open the next round. The `⟨DECIDED, b⟩`
publication the advance carries on an `A` grade (D10) is the network's half of
the joint step, so no row of it appears here. -/
def stepRound (q : CoreNodeN n) (c : Bool) : CoreNodeN n :=
  q.setProc
    { q.proc with
      est := some (q.proc.est.getD c),
      lastGrade := none,
      round := q.proc.round + 1,
      phase := .toCallG }

end CoreNodeN

namespace Net

/-! ### The auxiliary alphabet -/

/-- The rendezvous alphabet: the two networks, the Byzantine drives, and the
handshake branches the shared alphabet does not distinguish. -/
inductive NetEvt (n : ℕ) : Type
  /-- Stage-`r` multicast: sender `j` writes its record and the network pools
  `m` under `j`. -/
  | gsnd (r : ℕ) (j : Fin n) (m : GBCA.Msg)
  /-- Stage-`r` delivery: `m`, pooled under sender `j`, reaches receiver `i`. -/
  | gdlv (r : ℕ) (i j : Fin n) (m : GBCA.Msg)
  /-- DECIDED relay: sender `j` publishes `⟨DECIDED, b⟩` on an `f + 1` quorum. -/
  | dsnd (j : Fin n) (b : Bool)
  /-- DECIDED delivery: sender `j`'s `⟨DECIDED, b⟩` reaches receiver `i`. -/
  | ddlv (i j : Fin n) (b : Bool)
  /-- The coin return fused with a `⟨DECIDED, b⟩` publication (D10): the
  round-`r` coin `c` returns to `id`, whose grade was `A b`. -/
  | retWPub (r : ℕ) (id : Fin n) (c : Bool) (b : Bool)
  /-- The graded-agreement call against an already-called stage record. -/
  | gcallLoop (r : ℕ) (id : Fin n) (b : Bool)
  /-- A corrupted process drives the graded-agreement call, opening the stage
  record (D11). -/
  | byzCallG (r : ℕ) (k : Fin n) (b : Bool)
  /-- A corrupted process drives the graded-agreement call against an
  already-called stage record (D11). -/
  | byzCallGLoop (r : ℕ) (k : Fin n) (b : Bool)
  /-- A corrupted process takes a graded-agreement return (D11). -/
  | byzRetG (r : ℕ) (k : Fin n) (out : GbcaOut)
  /-- A corrupted process drives the coin call (D11). -/
  | byzCallW (r : ℕ) (k : Fin n)
  /-- A corrupted process takes the coin return (D11). -/
  | byzRetW (r : ℕ) (k : Fin n) (b : Bool)
  deriving DecidableEq

/-- The extended alphabet. Its silent label is `Sum.inl τ`, so every
`Sum.inr` label is observable and hence hideable. -/
abbrev NLab (n : ℕ) : Type := Lab n ⊕ NetEvt n

/-- The rendezvous labels, hidden by the composition. -/
def netEvtLabels (n : ℕ) : Set (NLab n) := {l | ∃ e : NetEvt n, l = Sum.inr e}

@[simp] theorem inl_notMem_netEvtLabels {n : ℕ} (l : Lab n) :
    Sum.inl l ∉ netEvtLabels n := by
  simp [netEvtLabels]

@[simp] theorem inr_mem_netEvtLabels {n : ℕ} (e : NetEvt n) :
    Sum.inr e ∈ netEvtLabels n := ⟨e, rfl⟩

@[simp] theorem nlab_tau (n : ℕ) : (Silent.τ : NLab n) = Sum.inl Lab.tau := rfl

/-- The state of one corruption-blind process: the round-loop record and one
stage record per round. -/
abbrev ABANodeN (n : ℕ) : Type := CoreNodeN n × (ℕ → GBCA.ProcNodeN n)

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

Process `j`'s program. Every guard reads the node and nothing else: no guard
asks whether the process is honest, and none asks what it has multicast.
A rendezvous row carries the process's half of a joint step with the network —
on a send the record write, on a delivery the inbox write, on a Byzantine
drive the instance-side content that the label authorises. Every label of the
extended alphabet has a row: the participant's, or an idle one. -/

/-- The step relation of the corruption-blind program of process `j`. -/
inductive ABAProcStepN (P : Params) (j : Fin P.n) :
    ABANodeN P.n → NLab P.n → PMF (ABANodeN P.n) → Prop
  /-- `upon ABA(b)`: record input and estimate, open round `0`. -/
  | input (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (b : Bool)
      (h : c.proc.input = none) :
      ABAProcStepN P j (c, g) (Sum.inl (.callABA j b))
        (PMF.pure (c.setProc { c.proc with
          input := some b, est := some b, round := 0, phase := .toCallG }, g))
  /-- Input-enabledness loop on `j`'s own `callABA`. -/
  | inputLoop (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (b : Bool) :
      ABAProcStepN P j (c, g) (Sum.inl (.callABA j b)) (PMF.pure (c, g))
  /-- An input addressed elsewhere: not `j`'s business. -/
  | callABAIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ABAProcStepN P j (c, g) (Sum.inl (.callABA id b)) (PMF.pure (c, g))
  /-- Return `b` on an `n − f` DECIDED quorum. Having multicast `b` oneself is
  a condition on the pool, hence the network's conjunct. -/
  | ret (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (b : Bool)
      (hcnt : P.n - P.f ≤ c.decidedCount b) (hret : c.proc.returned = false) :
      ABAProcStepN P j (c, g) (Sum.inl (.retABA j b))
        (PMF.pure (c.setProc { c.proc with returned := true }, g))
  /-- A return by another process: not `j`'s business. -/
  | retABAIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ABAProcStepN P j (c, g) (Sum.inl (.retABA id b)) (PMF.pure (c, g))
  /-- The graded-agreement call: the round loop hands its estimate to the
  round's stage record, which opens. The `⟨INPUT, b⟩` multicast is the
  network's half. -/
  | callG_call (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ) (b : Bool)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r)
      (hest : c.proc.est = some b) (hin : (g r).proc.input = none) :
      ABAProcStepN P j (c, g) (Sum.inl (.callG r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG },
          Function.update g r ((g r).setP { (g r).proc with
            input := some b,
            sentInput := Function.update (g r).proc.sentInput b true })))
  /-- A graded-agreement call by another process: not `j`'s business. -/
  | callGIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (r : ℕ) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ABAProcStepN P j (c, g) (Sum.inl (.callG r id b)) (PMF.pure (c, g))
  /-- Return with grade `A v`. -/
  | retG_A (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ) (v : Bool)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r)
      (hcnt : P.n - P.f ≤ (g r).recvCount (.seal (some v)))
      (hret : (g r).proc.returned = false) :
      ABAProcStepN P j (c, g) (Sum.inl (.retG r j (.A v)))
        (PMF.pure (c.setProc { c.proc with
            est := (GbcaOut.A v).est, lastGrade := some (.A v), phase := .toCallW },
          Function.update g r ((g r).setP { (g r).proc with returned := true })))
  /-- Return with grade `B v`. -/
  | retG_B (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ) (v : Bool)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r)
      (hcnt : P.n - P.f ≤ (g r).sealCount)
      (honce : ∃ k, GBCA.Msg.seal (some v) ∈ (g r).inbox k)
      (hbind : P.f + 1 ≤ (g r).recvCount (.bind (some v)))
      (hval : (g r).bothValid P)
      (hret : (g r).proc.returned = false) :
      ABAProcStepN P j (c, g) (Sum.inl (.retG r j (.B v)))
        (PMF.pure (c.setProc { c.proc with
            est := (GbcaOut.B v).est, lastGrade := some (.B v), phase := .toCallW },
          Function.update g r ((g r).setP { (g r).proc with returned := true })))
  /-- Return with grade `C`. -/
  | retG_C (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r)
      (hcnt : P.n - P.f ≤ (g r).recvCount (.seal none))
      (hval : (g r).bothValid P)
      (hret : (g r).proc.returned = false) :
      ABAProcStepN P j (c, g) (Sum.inl (.retG r j .C))
        (PMF.pure (c.setProc { c.proc with
            est := GbcaOut.C.est, lastGrade := some .C, phase := .toCallW },
          Function.update g r ((g r).setP { (g r).proc with returned := true })))
  /-- A graded-agreement return to another process: not `j`'s business. -/
  | retGIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (r : ℕ) (id : Fin P.n) (out : GbcaOut) (hid : id ≠ j) :
      ABAProcStepN P j (c, g) (Sum.inl (.retG r id out)) (PMF.pure (c, g))
  /-- `c ← WCC_r()`, the call half at the round loop. -/
  | callW (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ)
      (hph : c.proc.phase = .toCallW) (hr : c.proc.round = r) :
      ABAProcStepN P j (c, g) (Sum.inl (.callW r j))
        (PMF.pure (c.setProc { c.proc with phase := .awaitW }, g))
  /-- A coin call by another process: not `j`'s business. -/
  | callWIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (r : ℕ) (id : Fin P.n) (hid : id ≠ j) :
      ABAProcStepN P j (c, g) (Sum.inl (.callW r id)) (PMF.pure (c, g))
  /-- The coin return without a publication: the round advances and nothing is
  multicast, the round's grade not being an `A` (D10). -/
  | retW (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ) (co : Bool)
      (hph : c.proc.phase = .awaitW) (hr : c.proc.round = r)
      (hgr : ∀ v : Bool, c.proc.lastGrade ≠ some (.A v)) :
      ABAProcStepN P j (c, g) (Sum.inl (.retW r j co))
        (PMF.pure (c.stepRound co, g))
  /-- A coin return to another process: not `j`'s business. -/
  | retWIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (r : ℕ) (id : Fin P.n) (co : Bool) (hid : id ≠ j) :
      ABAProcStepN P j (c, g) (Sum.inl (.retW r id co)) (PMF.pure (c, g))
  /-- Corruption is not the process's business: the broadcast is taken without
  moving, whoever it names. -/
  | failIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (k : Fin P.n) :
      ABAProcStepN P j (c, g) (Sum.inl (.fail k)) (PMF.pure (c, g))
  /-- Stage `r`'s `INPUT` relay: `f + 1` receipts of `⟨INPUT, b⟩`, not yet
  multicast (D8, D18). -/
  | gsndRelay (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ) (b : Bool)
      (hin : (g r).proc.input ≠ none)
      (hcnt : P.f + 1 ≤ (g r).recvCount (.input b))
      (hsend : (g r).proc.sentInput b = false) :
      ABAProcStepN P j (c, g) (Sum.inr (.gsnd r j (.input b)))
        (PMF.pure (c, Function.update g r ((g r).setP { (g r).proc with
          sentInput := Function.update (g r).proc.sentInput b true })))
  /-- Stage `r`'s `ECHO`: an `n − f` `INPUT b` quorum (D18). -/
  | gsndEcho (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ) (b : Bool)
      (hin : (g r).proc.input ≠ none)
      (hcnt : P.n - P.f ≤ (g r).recvCount (.input b))
      (hsend : (g r).proc.sentEcho = none) :
      ABAProcStepN P j (c, g) (Sum.inr (.gsnd r j (.echo b)))
        (PMF.pure (c, Function.update g r
          ((g r).setP { (g r).proc with sentEcho := some b })))
  /-- Stage `r`'s `VOTE b`: an `n − f` `ECHO b` quorum (D18). -/
  | gsndVoteBit (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ) (b : Bool)
      (hin : (g r).proc.input ≠ none)
      (hcnt : P.n - P.f ≤ (g r).recvCount (.echo b))
      (hsend : (g r).proc.sentVote = none) :
      ABAProcStepN P j (c, g) (Sum.inr (.gsnd r j (.vote (some b))))
        (PMF.pure (c, Function.update g r
          ((g r).setP { (g r).proc with sentVote := some (some b) })))
  /-- Stage `r`'s `VOTE ⊥`: `n − f` `ECHO`s of any payload and `|Valid| > 1`. -/
  | gsndVoteBot (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ)
      (hin : (g r).proc.input ≠ none) (hcnt : P.n - P.f ≤ (g r).echoCount)
      (hval : (g r).bothValid P) (hsend : (g r).proc.sentVote = none) :
      ABAProcStepN P j (c, g) (Sum.inr (.gsnd r j (.vote none)))
        (PMF.pure (c, Function.update g r
          ((g r).setP { (g r).proc with sentVote := some none })))
  /-- Stage `r`'s `BIND b`: an `n − f` `VOTE b` quorum (D18). -/
  | gsndBindBit (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ) (b : Bool)
      (hin : (g r).proc.input ≠ none)
      (hcnt : P.n - P.f ≤ (g r).recvCount (.vote (some b)))
      (hsend : (g r).proc.sentBind = none) :
      ABAProcStepN P j (c, g) (Sum.inr (.gsnd r j (.bind (some b))))
        (PMF.pure (c, Function.update g r
          ((g r).setP { (g r).proc with sentBind := some (some b) })))
  /-- Stage `r`'s `BIND ⊥`: `n − f` `VOTE`s of any payload and `|Valid| > 1`. -/
  | gsndBindBot (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ)
      (hin : (g r).proc.input ≠ none) (hcnt : P.n - P.f ≤ (g r).voteCount)
      (hval : (g r).bothValid P) (hsend : (g r).proc.sentBind = none) :
      ABAProcStepN P j (c, g) (Sum.inr (.gsnd r j (.bind none)))
        (PMF.pure (c, Function.update g r
          ((g r).setP { (g r).proc with sentBind := some none })))
  /-- Stage `r`'s `SEAL b`: an `n − f` `BIND b` quorum (D18). -/
  | gsndSealBit (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ) (b : Bool)
      (hin : (g r).proc.input ≠ none)
      (hcnt : P.n - P.f ≤ (g r).recvCount (.bind (some b)))
      (hsend : (g r).proc.sentSeal = none) :
      ABAProcStepN P j (c, g) (Sum.inr (.gsnd r j (.seal (some b))))
        (PMF.pure (c, Function.update g r
          ((g r).setP { (g r).proc with sentSeal := some (some b) })))
  /-- Stage `r`'s `SEAL ⊥`: `n − f` `BIND`s of any payload and `|Valid| > 1`. -/
  | gsndSealBot (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ)
      (hin : (g r).proc.input ≠ none) (hcnt : P.n - P.f ≤ (g r).bindCount)
      (hval : (g r).bothValid P) (hsend : (g r).proc.sentSeal = none) :
      ABAProcStepN P j (c, g) (Sum.inr (.gsnd r j (.seal none)))
        (PMF.pure (c, Function.update g r
          ((g r).setP { (g r).proc with sentSeal := some none })))
  /-- A stage multicast by another process: not `j`'s business. -/
  | gsndIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (r : ℕ) (k : Fin P.n) (m : GBCA.Msg) (hk : k ≠ j) :
      ABAProcStepN P j (c, g) (Sum.inr (.gsnd r k m)) (PMF.pure (c, g))
  /-- Stage-`r` delivery, receiver's half: file the message under the sender's
  inbox row. Authenticity is the network's conjunct. -/
  | gdlvRecv (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (r : ℕ) (k : Fin P.n) (m : GBCA.Msg) :
      ABAProcStepN P j (c, g) (Sum.inr (.gdlv r j k m))
        (PMF.pure (c, Function.update g r ((g r).deliverTo k m)))
  /-- A stage delivery to another process: not `j`'s business. -/
  | gdlvIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (r : ℕ) (i k : Fin P.n) (m : GBCA.Msg) (hi : i ≠ j) :
      ABAProcStepN P j (c, g) (Sum.inr (.gdlv r i k m)) (PMF.pure (c, g))
  /-- The DECIDED relay on an `f + 1` quorum (D12′). Not having multicast `b`
  is a condition on the pool, hence the network's conjunct; the pool insert is
  the network's half too. -/
  | dsndRelay (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (b : Bool)
      (hcnt : P.f + 1 ≤ c.decidedCount b) :
      ABAProcStepN P j (c, g) (Sum.inr (.dsnd j b)) (PMF.pure (c, g))
  /-- A DECIDED relay by another process: not `j`'s business. -/
  | dsndIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      ABAProcStepN P j (c, g) (Sum.inr (.dsnd k b)) (PMF.pure (c, g))
  /-- DECIDED delivery, receiver's half: at most one receipt per (sender, bit)
  (D12′). Authenticity is the network's conjunct. -/
  | ddlvRecv (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (k : Fin P.n) (b : Bool) (hr : b ∉ c.decIn k) :
      ABAProcStepN P j (c, g) (Sum.inr (.ddlv j k b))
        (PMF.pure (c.recvDec k b, g))
  /-- A DECIDED delivery to another process: not `j`'s business. -/
  | ddlvIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (i k : Fin P.n) (b : Bool) (hi : i ≠ j) :
      ABAProcStepN P j (c, g) (Sum.inr (.ddlv i k b)) (PMF.pure (c, g))
  /-- The coin return fused with the `⟨DECIDED, b⟩` publication (D10): the
  round's grade was `A b`, so the round advance publishes `b`, the pool insert
  being the network's half. -/
  | retWPub (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (r : ℕ) (co : Bool) (b : Bool)
      (hph : c.proc.phase = .awaitW) (hr : c.proc.round = r)
      (hgr : c.proc.lastGrade = some (.A b)) :
      ABAProcStepN P j (c, g) (Sum.inr (.retWPub r j co b))
        (PMF.pure (c.stepRound co, g))
  /-- A fused coin return at another process: not `j`'s business. -/
  | retWPubIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (r : ℕ) (id : Fin P.n) (co : Bool) (b : Bool) (hid : id ≠ j) :
      ABAProcStepN P j (c, g) (Sum.inr (.retWPub r id co b)) (PMF.pure (c, g))
  /-- The graded-agreement call against an already-called stage record: the
  round loop moves, the stage record does not. -/
  | gcallLoop (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ) (b : Bool)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r)
      (hest : c.proc.est = some b) :
      ABAProcStepN P j (c, g) (Sum.inr (.gcallLoop r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG }, g))
  /-- Such a call at another process: not `j`'s business. -/
  | gcallLoopIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (r : ℕ) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ABAProcStepN P j (c, g) (Sum.inr (.gcallLoop r id b)) (PMF.pure (c, g))
  /-- A Byzantine graded-agreement call (D11): the stage record opens on the
  driven bit, the round loop does not move. -/
  | byzCallG (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ) (b : Bool)
      (hin : (g r).proc.input = none) :
      ABAProcStepN P j (c, g) (Sum.inr (.byzCallG r j b))
        (PMF.pure (c, Function.update g r ((g r).setP { (g r).proc with
          input := some b,
          sentInput := Function.update (g r).proc.sentInput b true })))
  /-- A Byzantine graded-agreement call at another process: not `j`'s
  business. -/
  | byzCallGIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (r : ℕ) (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      ABAProcStepN P j (c, g) (Sum.inr (.byzCallG r k b)) (PMF.pure (c, g))
  /-- A Byzantine graded-agreement call against an already-called stage record
  (D11): nothing moves anywhere. -/
  | byzCallGLoopIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (r : ℕ) (k : Fin P.n) (b : Bool) :
      ABAProcStepN P j (c, g) (Sum.inr (.byzCallGLoop r k b)) (PMF.pure (c, g))
  /-- Grade-`A` return to a corrupted round loop (D11): the stage record
  returns, the round loop does not move. -/
  | byzRetG_A (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ) (v : Bool)
      (hcnt : P.n - P.f ≤ (g r).recvCount (.seal (some v)))
      (hret : (g r).proc.returned = false) :
      ABAProcStepN P j (c, g) (Sum.inr (.byzRetG r j (.A v)))
        (PMF.pure (c, Function.update g r
          ((g r).setP { (g r).proc with returned := true })))
  /-- Grade-`B` return to a corrupted round loop (D11). -/
  | byzRetG_B (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ) (v : Bool)
      (hcnt : P.n - P.f ≤ (g r).sealCount)
      (honce : ∃ k, GBCA.Msg.seal (some v) ∈ (g r).inbox k)
      (hbind : P.f + 1 ≤ (g r).recvCount (.bind (some v)))
      (hval : (g r).bothValid P)
      (hret : (g r).proc.returned = false) :
      ABAProcStepN P j (c, g) (Sum.inr (.byzRetG r j (.B v)))
        (PMF.pure (c, Function.update g r
          ((g r).setP { (g r).proc with returned := true })))
  /-- Grade-`C` return to a corrupted round loop (D11). -/
  | byzRetG_C (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n) (r : ℕ)
      (hcnt : P.n - P.f ≤ (g r).recvCount (.seal none))
      (hval : (g r).bothValid P)
      (hret : (g r).proc.returned = false) :
      ABAProcStepN P j (c, g) (Sum.inr (.byzRetG r j .C))
        (PMF.pure (c, Function.update g r
          ((g r).setP { (g r).proc with returned := true })))
  /-- A Byzantine graded-agreement return at another process: not `j`'s
  business. -/
  | byzRetGIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (r : ℕ) (k : Fin P.n) (out : GbcaOut) (hk : k ≠ j) :
      ABAProcStepN P j (c, g) (Sum.inr (.byzRetG r k out)) (PMF.pure (c, g))
  /-- A Byzantine coin call (D11): the coin oracle reacts through the pullback,
  no process moves. -/
  | byzCallWIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (r : ℕ) (k : Fin P.n) :
      ABAProcStepN P j (c, g) (Sum.inr (.byzCallW r k)) (PMF.pure (c, g))
  /-- A Byzantine coin return (D11): the coin oracle reacts through the
  pullback, no process moves. -/
  | byzRetWIdle (c : CoreNodeN P.n) (g : ℕ → GBCA.ProcNodeN P.n)
      (r : ℕ) (k : Fin P.n) (b : Bool) :
      ABAProcStepN P j (c, g) (Sum.inr (.byzRetW r k b)) (PMF.pure (c, g))

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
  node keeps a copy. -/
  | fail (s : NetState P.n) (k : Fin P.n) :
      NetStep P s (Sum.inl (.fail k)) (PMF.pure (s.corrupt P k))
  /-- Byzantine stage injection (D5, D11): the network multicasts on behalf of
  a corrupted sender. -/
  | byzG (s : NetState P.n) (r : ℕ) (k : Fin P.n) (m : GBCA.Msg) (hF : k ∈ s.F) :
      NetStep P s (Sum.inl .tau) (PMF.pure (s.gpool r k m))
  /-- Byzantine DECIDED injection (D12′): either or both bits, at any time, so
  a corrupted process may equivocate. -/
  | byzD (s : NetState P.n) (k : Fin P.n) (b : Bool) (hF : k ∈ s.F) :
      NetStep P s (Sum.inl .tau) (PMF.pure (s.dput k b))

/-! ### The label pullback of the coin oracle -/

/-- The pullback along which the coin oracle is read over the extended
alphabet: a shared label is its own, the Byzantine handshake drives and the
fused coin return are the oracle's own handshakes, and every other rendezvous
label leaves the oracle idle. -/
def wccPull (n : ℕ) : NLab n → Option (Lab n)
  | Sum.inl l => some l
  | Sum.inr (.byzCallW r k) => some (.callW r k)
  | Sum.inr (.byzRetW r k b) => some (.retW r k b)
  | Sum.inr (.retWPub r id c _) => some (.retW r id c)
  | Sum.inr _ => none

@[simp] theorem wccPull_inl {n : ℕ} (l : Lab n) : wccPull n (Sum.inl l) = some l := rfl

@[simp] theorem wccPull_byzCallW {n : ℕ} (r : ℕ) (k : Fin n) :
    wccPull n (Sum.inr (.byzCallW r k)) = some (.callW r k) := rfl

@[simp] theorem wccPull_byzRetW {n : ℕ} (r : ℕ) (k : Fin n) (b : Bool) :
    wccPull n (Sum.inr (.byzRetW r k b)) = some (.retW r k b) := rfl

@[simp] theorem wccPull_retWPub {n : ℕ} (r : ℕ) (id : Fin n) (c b : Bool) :
    wccPull n (Sum.inr (.retWPub r id c b)) = some (.retW r id c) := rfl

@[simp] theorem wccPull_gsnd {n : ℕ} (r : ℕ) (j : Fin n) (m : GBCA.Msg) :
    wccPull n (Sum.inr (.gsnd r j m)) = none := rfl

@[simp] theorem wccPull_gdlv {n : ℕ} (r : ℕ) (i j : Fin n) (m : GBCA.Msg) :
    wccPull n (Sum.inr (.gdlv r i j m)) = none := rfl

@[simp] theorem wccPull_dsnd {n : ℕ} (j : Fin n) (b : Bool) :
    wccPull n (Sum.inr (.dsnd j b)) = none := rfl

@[simp] theorem wccPull_ddlv {n : ℕ} (i j : Fin n) (b : Bool) :
    wccPull n (Sum.inr (.ddlv i j b)) = none := rfl

@[simp] theorem wccPull_gcallLoop {n : ℕ} (r : ℕ) (id : Fin n) (b : Bool) :
    wccPull n (Sum.inr (.gcallLoop r id b)) = none := rfl

@[simp] theorem wccPull_byzCallG {n : ℕ} (r : ℕ) (k : Fin n) (b : Bool) :
    wccPull n (Sum.inr (.byzCallG r k b)) = none := rfl

@[simp] theorem wccPull_byzCallGLoop {n : ℕ} (r : ℕ) (k : Fin n) (b : Bool) :
    wccPull n (Sum.inr (.byzCallGLoop r k b)) = none := rfl

@[simp] theorem wccPull_byzRetG {n : ℕ} (r : ℕ) (k : Fin n) (out : GbcaOut) :
    wccPull n (Sum.inr (.byzRetG r k out)) = none := rfl

/-! ### The automata and the composition pipeline -/

/-- The corruption-blind program of process `j`. -/
noncomputable def ABAProcN (P : Params) (j : Fin P.n) :
    System (ABANodeN P.n) (NLab P.n) where
  init := (CoreNodeN.initial P.n, fun _ => GBCA.ProcNodeN.initial P.n)
  step := ABAProcStepN P j

@[simp] theorem ABAProcN_init (P : Params) (j : Fin P.n) :
    (ABAProcN P j).init = (CoreNodeN.initial P.n, fun _ => GBCA.ProcNodeN.initial P.n) :=
  rfl

@[simp] theorem ABAProcN_step (P : Params) (j : Fin P.n) (q : ABANodeN P.n)
    (l : NLab P.n) (μ : PMF (ABANodeN P.n)) :
    (ABAProcN P j).step q l μ ↔ ABAProcStepN P j q l μ := Iff.rfl

/-- The network adversary. -/
noncomputable def netAdv (P : Params) : System (NetState P.n) (NLab P.n) where
  init := NetState.initial P.n
  step := NetStep P

@[simp] theorem netAdv_init (P : Params) : (netAdv P).init = NetState.initial P.n := rfl

@[simp] theorem netAdv_step (P : Params) (s : NetState P.n) (l : NLab P.n)
    (μ : PMF (NetState P.n)) : (netAdv P).step s l μ ↔ NetStep P s l μ := Iff.rfl

/-- The coin oracle, read over the extended alphabet through the pullback. -/
noncomputable def wccLift (P : Params) : System (ℕ → WCC.SpecState P.n) (NLab P.n) :=
  (WCC.specFamily P).mapIdle (wccPull P.n)

@[simp] theorem wccLift_init (P : Params) :
    (wccLift P).init = (WCC.specFamily P).init := rfl

/-- The three factors side by side, over the extended alphabet: the
synchronised process group, the network adversary and the lifted oracle. -/
noncomputable def deployedPre (P : Params) :
    System ((∀ _ : Fin P.n, ABANodeN P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n)))
      (NLab P.n) :=
  (System.syncProduct (ABAProcN P)).parallel ((netAdv P).parallel (wccLift P))

/-- **The deployed group**: the rendezvous alphabet hidden, the result read
back over `Lab n`. -/
noncomputable def deployedGroup (P : Params) :
    System ((∀ _ : Fin P.n, ABANodeN P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n)))
      (Lab P.n) :=
  ((deployedPre P).abstract (netEvtLabels P.n)).relabel

/-- **The deployed system**: the group with the sub-protocol API hidden. -/
noncomputable def deployed (P : Params) :
    System ((∀ _ : Fin P.n, ABANodeN P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n)))
      (Lab P.n) :=
  (deployedGroup P).abstract (Lab.hiddenAPI P.n)

/-! ### Determinacy of the two new rule tables

The composite is not an LTS — the coin resolution is probabilistic — but both
of the tables written here are Dirac. -/

/-- Every process transition is Dirac. -/
theorem procStepN_dirac {P : Params} {j : Fin P.n} {q : ABANodeN P.n}
    {l : NLab P.n} {ν : PMF (ABANodeN P.n)} (h : ABAProcStepN P j q l ν) :
    ∃ q', ν = PMF.pure q' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every network transition is Dirac. -/
theorem netStep_dirac {P : Params} {s : NetState P.n} {l : NLab P.n}
    {μ : PMF (NetState P.n)} (h : NetStep P s l μ) : ∃ s', μ = PMF.pure s' := by
  cases h <;> exact ⟨_, rfl⟩

/-- The program of a process is an LTS. -/
theorem ABAProcN_isLTS (P : Params) (j : Fin P.n) : (ABAProcN P j).IsLTS :=
  fun _ _ _ h => procStepN_dirac h

/-- The network adversary is an LTS. -/
theorem netAdv_isLTS (P : Params) : (netAdv P).IsLTS :=
  fun _ _ _ h => netStep_dirac h

/-- The synchronised process group is an LTS. -/
theorem syncN_isLTS (P : Params) : (System.syncProduct (ABAProcN P)).IsLTS :=
  System.syncProduct_isLTS (ABAProcN_isLTS P)

/-- No process rule fires on `τ`: a program only ever moves in a rendezvous or
on a shared API label. -/
theorem procStepN_no_tau {P : Params} {j : Fin P.n} {q : ABANodeN P.n}
    {ν : PMF (ABANodeN P.n)} (h : ABAProcStepN P j q (Silent.τ : NLab P.n) ν) :
    False := by
  rw [nlab_tau] at h; cases h

/-! ### Reading and building composite transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ parallel ∘ syncProduct`; the
lemmas below unfold it once and for all, in both directions. -/

/-- A synchronised transition of the process group on a visible label: every
process steps, and the joint distribution is Dirac. -/
theorem syncN_inv {P : Params} {u : ∀ _ : Fin P.n, ABANodeN P.n} {l : NLab P.n}
    {μ : PMF (∀ _ : Fin P.n, ABANodeN P.n)}
    (h : (System.syncProduct (ABAProcN P)).step u l μ) :
    ∃ x : ∀ _ : Fin P.n, ABANodeN P.n,
      μ = PMF.pure x ∧ ∀ i, ABAProcStepN P i (u i) l (PMF.pure (x i)) := by
  rw [System.syncProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨rfl, i, μ_i, hstep, -⟩
  · have hx : ∀ i, ∃ p', μ_ i = PMF.pure p' := fun i => procStepN_dirac (hall i)
    choose x hx using hx
    refine ⟨x, ?_, fun i => ?_⟩
    · rw [show μ_ = fun i => PMF.pure (x i) from funext hx]
      exact piPMF_pure x
    · rw [← hx i]; exact hall i
  · exact absurd hstep procStepN_no_tau

/-- Build a synchronised transition of the process group from per-process
Dirac steps. -/
theorem syncN_pure {P : Params} {u x : ∀ _ : Fin P.n, ABANodeN P.n} {l : NLab P.n}
    (hl : l ≠ Silent.τ)
    (h : ∀ i, ABAProcStepN P i (u i) l (PMF.pure (x i))) :
    (System.syncProduct (ABAProcN P)).step u l (PMF.pure x) := by
  rw [System.syncProduct_step]
  exact Or.inl ⟨hl, fun i => PMF.pure (x i), h, (piPMF_pure x).symm⟩

/-- A synchronised transition on a visible label, as a per-process family. -/
theorem syncN_visible_iff (P : Params) (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (l : NLab P.n) (hl : l ≠ Silent.τ)
    (μ : PMF (∀ _ : Fin P.n, ABANodeN P.n)) :
    (System.syncProduct (ABAProcN P)).step u l μ ↔
      ∃ μ_ : Fin P.n → PMF (ABANodeN P.n),
        (∀ m, ABAProcStepN P m (u m) l (μ_ m)) ∧ μ = piPMF μ_ := by
  constructor
  · rintro (⟨-, μ_, hall, rfl⟩ | ⟨hτ, -⟩)
    · exact ⟨μ_, hall, rfl⟩
    · exact absurd hτ hl
  · rintro ⟨μ_, hall, rfl⟩
    exact Or.inl ⟨hl, μ_, hall, rfl⟩

/-- The process group has no silent transition: no program has a `τ` row. -/
theorem syncN_no_tau {P : Params} {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {μ : PMF (∀ _ : Fin P.n, ABANodeN P.n)}
    (h : (System.syncProduct (ABAProcN P)).step u (Silent.τ : NLab P.n) μ) :
    False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact procStepN_no_tau hstep

/-- Build a joint transition of the three factors on a rendezvous label. -/
theorem deployedPre_event_step (P : Params) {u x : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o o' : ℕ → WCC.SpecState P.n} (e : NetEvt P.n)
    (hall : ∀ i, ABAProcStepN P i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : NetStep P w (Sum.inr e) (PMF.pure w'))
    (ho : (wccLift P).step o (Sum.inr e) (PMF.pure o')) :
    (deployedPre P).step (u, w, o) (Sum.inr e) (PMF.pure (x, w', o')) := by
  rw [deployedPre, System.parallel_step]
  refine Or.inl ⟨by simp, PMF.pure x, PMF.pure (w', o'),
    syncN_pure (by simp) hall, ?_, (prodPMF_pure_pure _ _).symm⟩
  rw [System.parallel_step]
  exact Or.inl ⟨by simp, PMF.pure w', PMF.pure o', hn, ho,
    (prodPMF_pure_pure _ _).symm⟩

/-- Build a joint transition of the three factors on a visible shared label. -/
theorem deployedPre_lab_step (P : Params) {u x : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} {l : Lab P.n} (hl : l ≠ Lab.tau)
    (hall : ∀ i, ABAProcStepN P i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hn : NetStep P w (Sum.inl l) (PMF.pure w'))
    (ho : (WCC.specFamily P).step o l ω) :
    (deployedPre P).step (u, w, o) (Sum.inl l)
      (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω)) := by
  have hne : (Sum.inl l : NLab P.n) ≠ Silent.τ := by simpa using hl
  rw [deployedPre, System.parallel_step]
  refine Or.inl ⟨hne, PMF.pure x, prodPMF (PMF.pure w') ω,
    syncN_pure hne hall, ?_, rfl⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hne, PMF.pure w', ω, hn,
    (System.mapIdle_step_some (by simp) ω).mpr ho, rfl⟩

/-- Build a silent transition of the three factors from a network-local one. -/
theorem deployedPre_tau_net (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    (hn : NetStep P w (Sum.inl .tau) (PMF.pure w')) :
    (deployedPre P).step (u, w, o) (Sum.inl .tau) (PMF.pure (u, w', o)) := by
  rw [deployedPre, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure w') (PMF.pure o), ?_, ?_⟩)
  · rw [System.parallel_step]
    exact Or.inr (Or.inl ⟨rfl, PMF.pure w', hn, rfl⟩)
  · rw [prodPMF_pure_pure, prodPMF_pure_pure]

/-- Build a silent transition of the three factors from an oracle-local one
(the coin resolution — the one transition of the composite that is not
Dirac). -/
theorem deployedPre_tau_wcc (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)}
    (ho : (WCC.specFamily P).step o Lab.tau ω) :
    (deployedPre P).step (u, w, o) (Sum.inl .tau)
      (prodPMF (PMF.pure u) (prodPMF (PMF.pure w) ω)) := by
  rw [deployedPre, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure w) ω, ?_, rfl⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, ω,
    (System.mapIdle_step_some (by simp) ω).mpr ho, rfl⟩)

/-- The composite step relation of the deployed group, unfolded to the hidden
rendezvous case and the shared-label case. -/
theorem deployedGroup_step_iff (P : Params)
    (q : (∀ _ : Fin P.n, ABANodeN P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n)))
    (l : Lab P.n)
    (μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))) :
    (deployedGroup P).step q l μ ↔
      (l = .tau ∧ ∃ e : NetEvt P.n, (deployedPre P).step q (Sum.inr e) μ) ∨
      (deployedPre P).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_netEvtLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_netEvtLabels l, hstep⟩

/-- The deployed system's step relation: a sub-protocol API label seen as `τ`,
or a label that survives the hiding. -/
theorem deployed_step_iff (P : Params)
    (q : (∀ _ : Fin P.n, ABANodeN P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n)))
    (l : Lab P.n)
    (μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))) :
    (deployed P).step q l μ ↔
      (l = .tau ∧ ∃ l' ∈ Lab.hiddenAPI P.n, (deployedGroup P).step q l' μ) ∨
      (l ∉ Lab.hiddenAPI P.n ∧ (deployedGroup P).step q l μ) :=
  System.abstract_step _ _ _ _ _

/-- A hidden rendezvous is a silent transition of the deployed group. -/
theorem deployedGroup_event_step (P : Params) {u x : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o o' : ℕ → WCC.SpecState P.n} (e : NetEvt P.n)
    (hall : ∀ i, ABAProcStepN P i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : NetStep P w (Sum.inr e) (PMF.pure w'))
    (ho : (wccLift P).step o (Sum.inr e) (PMF.pure o')) :
    (deployedGroup P).step (u, w, o) Lab.tau (PMF.pure (x, w', o')) :=
  (deployedGroup_step_iff P _ _ _).mpr
    (Or.inl ⟨rfl, e, deployedPre_event_step P e hall hn ho⟩)

/-- A shared visible label is a transition of the deployed group. -/
theorem deployedGroup_lab_step (P : Params) {u x : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} {l : Lab P.n} (hl : l ≠ Lab.tau)
    (hall : ∀ i, ABAProcStepN P i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hn : NetStep P w (Sum.inl l) (PMF.pure w'))
    (ho : (WCC.specFamily P).step o l ω) :
    (deployedGroup P).step (u, w, o) l
      (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω)) :=
  (deployedGroup_step_iff P _ _ _).mpr (Or.inr (deployedPre_lab_step P hl hall hn ho))

/-- A network-local injection is a silent transition of the deployed group. -/
theorem deployedGroup_tau_net (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    (hn : NetStep P w (Sum.inl .tau) (PMF.pure w')) :
    (deployedGroup P).step (u, w, o) Lab.tau (PMF.pure (u, w', o)) :=
  (deployedGroup_step_iff P _ _ _).mpr (Or.inr (deployedPre_tau_net P hn))

/-- The coin resolution is a silent transition of the deployed group. -/
theorem deployedGroup_tau_wcc (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)}
    (ho : (WCC.specFamily P).step o Lab.tau ω) :
    (deployedGroup P).step (u, w, o) Lab.tau
      (prodPMF (PMF.pure u) (prodPMF (PMF.pure w) ω)) :=
  (deployedGroup_step_iff P _ _ _).mpr (Or.inr (deployedPre_tau_wcc P ho))

/-! ### One process's rules, by label class

Each lemma reads a row of the table off its label: the participant's row as
its guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. The state and the distribution are
variables, so `cases` unifies against any node. -/

section ProcInversion

variable {P : Params} {j : Fin P.n} {q : ABANodeN P.n} {ν : PMF (ABANodeN P.n)}

theorem stepN_callABA_own {b : Bool}
    (h : ABAProcStepN P j q (Sum.inl (.callABA j b)) ν) :
    (q.1.proc.input = none ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with
        input := some b, est := some b, round := 0, phase := .toCallG }, q.2)) ∨
    ν = PMF.pure q := by
  cases h
  case input => exact Or.inl ⟨by assumption, rfl⟩
  case inputLoop => exact Or.inr rfl
  case callABAIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_callABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ABAProcStepN P j q (Sum.inl (.callABA id b)) ν) : ν = PMF.pure q := by
  cases h
  case input => exact absurd rfl hid
  case inputLoop => exact absurd rfl hid
  case callABAIdle => rfl

theorem stepN_retABA_own {b : Bool}
    (h : ABAProcStepN P j q (Sum.inl (.retABA j b)) ν) :
    P.n - P.f ≤ q.1.decidedCount b ∧ q.1.proc.returned = false ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with returned := true }, q.2) := by
  cases h
  case ret => exact ⟨by assumption, by assumption, rfl⟩
  case retABAIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_retABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ABAProcStepN P j q (Sum.inl (.retABA id b)) ν) : ν = PMF.pure q := by
  cases h
  case ret => exact absurd rfl hid
  case retABAIdle => rfl

theorem stepN_callG_own {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inl (.callG r j b)) ν) :
    q.1.proc.phase = .toCallG ∧ q.1.proc.round = r ∧ q.1.proc.est = some b ∧
      (q.2 r).proc.input = none ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with phase := .awaitG },
        Function.update q.2 r ((q.2 r).setP { (q.2 r).proc with
          input := some b,
          sentInput := Function.update (q.2 r).proc.sentInput b true })) := by
  cases h
  case callG_call =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case callGIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_callG_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ABAProcStepN P j q (Sum.inl (.callG r id b)) ν) : ν = PMF.pure q := by
  cases h
  case callG_call => exact absurd rfl hid
  case callGIdle => rfl

theorem stepN_retG_A_own {r : ℕ} {v : Bool}
    (h : ABAProcStepN P j q (Sum.inl (.retG r j (.A v))) ν) :
    q.1.proc.phase = .awaitG ∧ q.1.proc.round = r ∧
      P.n - P.f ≤ (q.2 r).recvCount (.seal (some v)) ∧
      (q.2 r).proc.returned = false ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with
          est := (GbcaOut.A v).est, lastGrade := some (.A v), phase := .toCallW },
        Function.update q.2 r ((q.2 r).setP { (q.2 r).proc with returned := true })) := by
  cases h
  case retG_A =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_retG_B_own {r : ℕ} {v : Bool}
    (h : ABAProcStepN P j q (Sum.inl (.retG r j (.B v))) ν) :
    q.1.proc.phase = .awaitG ∧ q.1.proc.round = r ∧
      P.n - P.f ≤ (q.2 r).sealCount ∧
      (∃ k, GBCA.Msg.seal (some v) ∈ (q.2 r).inbox k) ∧
      P.f + 1 ≤ (q.2 r).recvCount (.bind (some v)) ∧ (q.2 r).bothValid P ∧
      (q.2 r).proc.returned = false ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with
          est := (GbcaOut.B v).est, lastGrade := some (.B v), phase := .toCallW },
        Function.update q.2 r ((q.2 r).setP { (q.2 r).proc with returned := true })) := by
  cases h
  case retG_B =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_retG_C_own {r : ℕ}
    (h : ABAProcStepN P j q (Sum.inl (.retG r j .C)) ν) :
    q.1.proc.phase = .awaitG ∧ q.1.proc.round = r ∧
      P.n - P.f ≤ (q.2 r).recvCount (.seal none) ∧ (q.2 r).bothValid P ∧
      (q.2 r).proc.returned = false ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with
          est := GbcaOut.C.est, lastGrade := some .C, phase := .toCallW },
        Function.update q.2 r ((q.2 r).setP { (q.2 r).proc with returned := true })) := by
  cases h
  case retG_C =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
      rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_retG_foreign {r : ℕ} {id : Fin P.n} {out : GbcaOut} (hid : id ≠ j)
    (h : ABAProcStepN P j q (Sum.inl (.retG r id out)) ν) : ν = PMF.pure q := by
  cases h
  case retG_A => exact absurd rfl hid
  case retG_B => exact absurd rfl hid
  case retG_C => exact absurd rfl hid
  case retGIdle => rfl

theorem stepN_callW_own {r : ℕ}
    (h : ABAProcStepN P j q (Sum.inl (.callW r j)) ν) :
    q.1.proc.phase = .toCallW ∧ q.1.proc.round = r ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with phase := .awaitW }, q.2) := by
  cases h
  case callW => exact ⟨by assumption, by assumption, rfl⟩
  case callWIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_callW_foreign {r : ℕ} {id : Fin P.n} (hid : id ≠ j)
    (h : ABAProcStepN P j q (Sum.inl (.callW r id)) ν) : ν = PMF.pure q := by
  cases h
  case callW => exact absurd rfl hid
  case callWIdle => rfl

theorem stepN_retW_own {r : ℕ} {co : Bool}
    (h : ABAProcStepN P j q (Sum.inl (.retW r j co)) ν) :
    q.1.proc.phase = .awaitW ∧ q.1.proc.round = r ∧
      (∀ v : Bool, q.1.proc.lastGrade ≠ some (.A v)) ∧
      ν = PMF.pure (q.1.stepRound co, q.2) := by
  cases h
  case retW => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case retWIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_retW_foreign {r : ℕ} {id : Fin P.n} {co : Bool} (hid : id ≠ j)
    (h : ABAProcStepN P j q (Sum.inl (.retW r id co)) ν) : ν = PMF.pure q := by
  cases h
  case retW => exact absurd rfl hid
  case retWIdle => rfl

theorem stepN_fail {k : Fin P.n}
    (h : ABAProcStepN P j q (Sum.inl (.fail k)) ν) : ν = PMF.pure q := by
  cases h; rfl

end ProcInversion

/-! ### One process's rules on the rendezvous alphabet -/

section ProcNetInversion

variable {P : Params} {j : Fin P.n} {q : ABANodeN P.n} {ν : PMF (ABANodeN P.n)}

theorem stepN_gsnd_input_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.input b))) ν) :
    (q.2 r).proc.input ≠ none ∧ P.f + 1 ≤ (q.2 r).recvCount (.input b) ∧
      (q.2 r).proc.sentInput b = false ∧
      ν = PMF.pure (q.1, Function.update q.2 r ((q.2 r).setP { (q.2 r).proc with
        sentInput := Function.update (q.2 r).proc.sentInput b true })) := by
  cases h
  case gsndRelay => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_gsnd_echo_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.echo b))) ν) :
    (q.2 r).proc.input ≠ none ∧ P.n - P.f ≤ (q.2 r).recvCount (.input b) ∧
      (q.2 r).proc.sentEcho = none ∧
      ν = PMF.pure (q.1, Function.update q.2 r
        ((q.2 r).setP { (q.2 r).proc with sentEcho := some b })) := by
  cases h
  case gsndEcho => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_gsnd_voteBit_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.vote (some b)))) ν) :
    (q.2 r).proc.input ≠ none ∧ P.n - P.f ≤ (q.2 r).recvCount (.echo b) ∧
      (q.2 r).proc.sentVote = none ∧
      ν = PMF.pure (q.1, Function.update q.2 r
        ((q.2 r).setP { (q.2 r).proc with sentVote := some (some b) })) := by
  cases h
  case gsndVoteBit => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_gsnd_voteBot_self {r : ℕ}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.vote none))) ν) :
    (q.2 r).proc.input ≠ none ∧ P.n - P.f ≤ (q.2 r).echoCount ∧
      (q.2 r).bothValid P ∧ (q.2 r).proc.sentVote = none ∧
      ν = PMF.pure (q.1, Function.update q.2 r
        ((q.2 r).setP { (q.2 r).proc with sentVote := some none })) := by
  cases h
  case gsndVoteBot =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_gsnd_bindBit_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.bind (some b)))) ν) :
    (q.2 r).proc.input ≠ none ∧ P.n - P.f ≤ (q.2 r).recvCount (.vote (some b)) ∧
      (q.2 r).proc.sentBind = none ∧
      ν = PMF.pure (q.1, Function.update q.2 r
        ((q.2 r).setP { (q.2 r).proc with sentBind := some (some b) })) := by
  cases h
  case gsndBindBit => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_gsnd_bindBot_self {r : ℕ}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.bind none))) ν) :
    (q.2 r).proc.input ≠ none ∧ P.n - P.f ≤ (q.2 r).voteCount ∧
      (q.2 r).bothValid P ∧ (q.2 r).proc.sentBind = none ∧
      ν = PMF.pure (q.1, Function.update q.2 r
        ((q.2 r).setP { (q.2 r).proc with sentBind := some none })) := by
  cases h
  case gsndBindBot =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_gsnd_sealBit_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.seal (some b)))) ν) :
    (q.2 r).proc.input ≠ none ∧ P.n - P.f ≤ (q.2 r).recvCount (.bind (some b)) ∧
      (q.2 r).proc.sentSeal = none ∧
      ν = PMF.pure (q.1, Function.update q.2 r
        ((q.2 r).setP { (q.2 r).proc with sentSeal := some (some b) })) := by
  cases h
  case gsndSealBit => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_gsnd_sealBot_self {r : ℕ}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.seal none))) ν) :
    (q.2 r).proc.input ≠ none ∧ P.n - P.f ≤ (q.2 r).bindCount ∧
      (q.2 r).bothValid P ∧ (q.2 r).proc.sentSeal = none ∧
      ν = PMF.pure (q.1, Function.update q.2 r
        ((q.2 r).setP { (q.2 r).proc with sentSeal := some none })) := by
  cases h
  case gsndSealBot =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›

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

theorem stepN_gdlv_self {r : ℕ} {k : Fin P.n} {m : GBCA.Msg}
    (h : ABAProcStepN P j q (Sum.inr (.gdlv r j k m)) ν) :
    ν = PMF.pure (q.1, Function.update q.2 r ((q.2 r).deliverTo k m)) := by
  cases h
  case gdlvRecv => rfl
  case gdlvIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_gdlv_foreign {r : ℕ} {i k : Fin P.n} {m : GBCA.Msg} (hi : i ≠ j)
    (h : ABAProcStepN P j q (Sum.inr (.gdlv r i k m)) ν) : ν = PMF.pure q := by
  cases h
  case gdlvRecv => exact absurd rfl hi
  case gdlvIdle => rfl

theorem stepN_dsnd_self {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.dsnd j b)) ν) :
    P.f + 1 ≤ q.1.decidedCount b ∧ ν = PMF.pure q := by
  cases h
  case dsndRelay => exact ⟨by assumption, rfl⟩
  case dsndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_dsnd_foreign {k : Fin P.n} {b : Bool} (hk : k ≠ j)
    (h : ABAProcStepN P j q (Sum.inr (.dsnd k b)) ν) : ν = PMF.pure q := by
  cases h
  case dsndRelay => exact absurd rfl hk
  case dsndIdle => rfl

theorem stepN_ddlv_self {k : Fin P.n} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.ddlv j k b)) ν) :
    b ∉ q.1.decIn k ∧ ν = PMF.pure (q.1.recvDec k b, q.2) := by
  cases h
  case ddlvRecv => exact ⟨by assumption, rfl⟩
  case ddlvIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_ddlv_foreign {i k : Fin P.n} {b : Bool} (hi : i ≠ j)
    (h : ABAProcStepN P j q (Sum.inr (.ddlv i k b)) ν) : ν = PMF.pure q := by
  cases h
  case ddlvRecv => exact absurd rfl hi
  case ddlvIdle => rfl

theorem stepN_retWPub_self {r : ℕ} {co b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.retWPub r j co b)) ν) :
    q.1.proc.phase = .awaitW ∧ q.1.proc.round = r ∧
      q.1.proc.lastGrade = some (.A b) ∧ ν = PMF.pure (q.1.stepRound co, q.2) := by
  cases h
  case retWPub => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case retWPubIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_retWPub_foreign {r : ℕ} {id : Fin P.n} {co b : Bool} (hid : id ≠ j)
    (h : ABAProcStepN P j q (Sum.inr (.retWPub r id co b)) ν) : ν = PMF.pure q := by
  cases h
  case retWPub => exact absurd rfl hid
  case retWPubIdle => rfl

theorem stepN_gcallLoop_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gcallLoop r j b)) ν) :
    q.1.proc.phase = .toCallG ∧ q.1.proc.round = r ∧ q.1.proc.est = some b ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with phase := .awaitG }, q.2) := by
  cases h
  case gcallLoop => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case gcallLoopIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_gcallLoop_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ABAProcStepN P j q (Sum.inr (.gcallLoop r id b)) ν) : ν = PMF.pure q := by
  cases h
  case gcallLoop => exact absurd rfl hid
  case gcallLoopIdle => rfl

theorem stepN_byzCallG_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.byzCallG r j b)) ν) :
    (q.2 r).proc.input = none ∧
      ν = PMF.pure (q.1, Function.update q.2 r ((q.2 r).setP { (q.2 r).proc with
        input := some b,
        sentInput := Function.update (q.2 r).proc.sentInput b true })) := by
  cases h
  case byzCallG => exact ⟨by assumption, rfl⟩
  case byzCallGIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_byzCallG_foreign {r : ℕ} {k : Fin P.n} {b : Bool} (hk : k ≠ j)
    (h : ABAProcStepN P j q (Sum.inr (.byzCallG r k b)) ν) : ν = PMF.pure q := by
  cases h
  case byzCallG => exact absurd rfl hk
  case byzCallGIdle => rfl

theorem stepN_byzCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.byzCallGLoop r k b)) ν) : ν = PMF.pure q := by
  cases h; rfl

theorem stepN_byzRetG_A_self {r : ℕ} {v : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.byzRetG r j (.A v))) ν) :
    P.n - P.f ≤ (q.2 r).recvCount (.seal (some v)) ∧
      (q.2 r).proc.returned = false ∧
      ν = PMF.pure (q.1, Function.update q.2 r
        ((q.2 r).setP { (q.2 r).proc with returned := true })) := by
  cases h
  case byzRetG_A => exact ⟨by assumption, by assumption, rfl⟩
  case byzRetGIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_byzRetG_B_self {r : ℕ} {v : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.byzRetG r j (.B v))) ν) :
    P.n - P.f ≤ (q.2 r).sealCount ∧
      (∃ k, GBCA.Msg.seal (some v) ∈ (q.2 r).inbox k) ∧
      P.f + 1 ≤ (q.2 r).recvCount (.bind (some v)) ∧ (q.2 r).bothValid P ∧
      (q.2 r).proc.returned = false ∧
      ν = PMF.pure (q.1, Function.update q.2 r
        ((q.2 r).setP { (q.2 r).proc with returned := true })) := by
  cases h
  case byzRetG_B =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
      rfl⟩
  case byzRetGIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_byzRetG_C_self {r : ℕ}
    (h : ABAProcStepN P j q (Sum.inr (.byzRetG r j .C)) ν) :
    P.n - P.f ≤ (q.2 r).recvCount (.seal none) ∧ (q.2 r).bothValid P ∧
      (q.2 r).proc.returned = false ∧
      ν = PMF.pure (q.1, Function.update q.2 r
        ((q.2 r).setP { (q.2 r).proc with returned := true })) := by
  cases h
  case byzRetG_C => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case byzRetGIdle => exact absurd rfl ‹_ ≠ j›

theorem stepN_byzRetG_foreign {r : ℕ} {k : Fin P.n} {out : GbcaOut} (hk : k ≠ j)
    (h : ABAProcStepN P j q (Sum.inr (.byzRetG r k out)) ν) : ν = PMF.pure q := by
  cases h
  case byzRetG_A => exact absurd rfl hk
  case byzRetG_B => exact absurd rfl hk
  case byzRetG_C => exact absurd rfl hk
  case byzRetGIdle => rfl

theorem stepN_byzCallW {r : ℕ} {k : Fin P.n}
    (h : ABAProcStepN P j q (Sum.inr (.byzCallW r k)) ν) : ν = PMF.pure q := by
  cases h; rfl

theorem stepN_byzRetW {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.byzRetW r k b)) ν) : ν = PMF.pure q := by
  cases h; rfl

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

theorem netStep_byzCallG {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : NetStep P s (Sum.inr (.byzCallG r k b)) μ) :
    k ∈ s.F ∧ μ = PMF.pure (s.gpool r k (.input b)) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netStep_byzCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : NetStep P s (Sum.inr (.byzCallGLoop r k b)) μ) :
    k ∈ s.F ∧ μ = PMF.pure s := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netStep_byzRetG {r : ℕ} {k : Fin P.n} {out : GbcaOut}
    (h : NetStep P s (Sum.inr (.byzRetG r k out)) μ) :
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

theorem netStep_retABA {id : Fin P.n} {b : Bool}
    (h : NetStep P s (Sum.inl (.retABA id b)) μ) :
    b ∈ s.dpool id ∧ μ = PMF.pure s := by
  cases h; exact ⟨by assumption, rfl⟩

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
    (h : NetStep P s (Sum.inl (.fail k)) μ) : μ = PMF.pure (s.corrupt P k) := by
  cases h; rfl

theorem netStep_tau (h : NetStep P s (Sum.inl .tau) μ) :
    (∃ (r : ℕ) (k : Fin P.n) (m : GBCA.Msg), k ∈ s.F ∧ μ = PMF.pure (s.gpool r k m)) ∨
    (∃ (k : Fin P.n) (b : Bool), k ∈ s.F ∧ μ = PMF.pure (s.dput k b)) := by
  cases h
  case byzG => exact Or.inl ⟨_, _, _, by assumption, rfl⟩
  case byzD => exact Or.inr ⟨_, _, by assumption, rfl⟩

end NetInversion

/-! ### Dirac successors and the network's field algebra

A Dirac distribution determines its point, and each of the network
adversary's three writes — a stage multicast, a DECIDED multicast, and
corruption — touches one field of `NetState` and leaves the other two
alone. -/

theorem pureN_inj {α : Type} {a b : α}
    (h : (PMF.pure a : PMF α) = PMF.pure b) : a = b := by
  have hm : a ∈ (PMF.pure b).support := by rw [← h]; simp
  simpa using hm

/-! #### The network's own field algebra -/

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

theorem netCorrupt_F {P : Params} (s : NetState P.n) (k : Fin P.n) :
    (NetState.corrupt P k s).F =
      if k ∉ s.F ∧ s.F.card < P.f then insert k s.F else s.F := by
  unfold NetState.corrupt; split <;> rfl

/-! ### The coin oracle's idle row over the shared alphabet -/

/-- The coin oracle idles on a shared label that is neither `τ`, nor a
handshake of one of its own rounds, nor `fail`. Read through the pullback
`wccPull`, this is the oracle's row in every joint transition — of the
deployed system, of its layered presentation, and of the deployment-shaped
specification (`ABA/LayeredSpec.lean`) — that leaves the coin standing still. -/
theorem wccFamilyN_idle (P : Params) (o : ℕ → WCC.SpecState P.n) {l : Lab P.n}
    (hl : l ≠ Lab.tau) (hr : Lab.wccRound l = none) (hf : ¬ Lab.isFail l) :
    (WCC.specFamily P).step o l (PMF.pure o) := by
  rw [WCC.specFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hl, hr, hf, rfl⟩))

/-! ### Reading a deployed transition into its three factors -/

/-- A rendezvous transition: every process, the network and the lifted oracle
move together, and only the oracle's successor can fail to be a Dirac. -/
theorem deployedPre_event_inv (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n} {e : NetEvt P.n}
    {μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (deployedPre P).step (u, w, o) (Sum.inr e) μ) :
    ∃ (x : ∀ _ : Fin P.n, ABANodeN P.n) (w' : NetState P.n)
      (μ₃ : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, ABAProcStepN P i (u i) (Sum.inr e) (PMF.pure (x i))) ∧
      NetStep P w (Sum.inr e) (PMF.pure w') ∧
      (wccLift P).step o (Sum.inr e) μ₃ ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') μ₃) := by
  rw [deployedPre, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂₃, hS, hNW, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
  · obtain ⟨x, rfl, hall⟩ := syncN_inv hS
    rw [System.parallel_step] at hNW
    rcases hNW with ⟨-, μ₂, μ₃, hN, hO, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
    · obtain ⟨w', rfl⟩ := netStep_dirac hN
      exact ⟨x, w', μ₃, hall, hN, hO, rfl⟩
    · simp [nlab_tau] at habs
    · simp [nlab_tau] at habs
  · simp [nlab_tau] at habs
  · simp [nlab_tau] at habs

/-- A visible shared-label transition. -/
theorem deployedPre_lab_inv (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n} {l : Lab P.n} (hl : l ≠ Lab.tau)
    {μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (deployedPre P).step (u, w, o) (Sum.inl l) μ) :
    ∃ (x : ∀ _ : Fin P.n, ABANodeN P.n) (w' : NetState P.n)
      (ω : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, ABAProcStepN P i (u i) (Sum.inl l) (PMF.pure (x i))) ∧
      NetStep P w (Sum.inl l) (PMF.pure w') ∧
      (WCC.specFamily P).step o l ω ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω) := by
  rw [deployedPre, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂₃, hS, hNW, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
  · obtain ⟨x, rfl, hall⟩ := syncN_inv hS
    rw [System.parallel_step] at hNW
    rcases hNW with ⟨-, μ₂, μ₃, hN, hO, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
    · obtain ⟨w', rfl⟩ := netStep_dirac hN
      exact ⟨x, w', μ₃, hall, hN,
        (System.mapIdle_step_some (wccPull_inl l) μ₃).mp hO, rfl⟩
    · rw [nlab_tau] at habs; exact absurd (Sum.inl_injective habs) hl
    · rw [nlab_tau] at habs; exact absurd (Sum.inl_injective habs) hl
  · rw [nlab_tau] at habs; exact absurd (Sum.inl_injective habs) hl
  · rw [nlab_tau] at habs; exact absurd (Sum.inl_injective habs) hl

/-- A silent shared-label transition: no process has a `τ` row, so it is the
network's own injection or the coin resolution. -/
theorem deployedPre_tau_inv (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (deployedPre P).step (u, w, o) (Sum.inl Lab.tau) μ) :
    (∃ w', NetStep P w (Sum.inl .tau) (PMF.pure w') ∧ μ = PMF.pure (u, w', o)) ∨
    (∃ ω, (WCC.specFamily P).step o Lab.tau ω ∧
      μ = prodPMF (PMF.pure u) (prodPMF (PMF.pure w) ω)) := by
  rw [deployedPre, System.parallel_step] at h
  rcases h with ⟨habs, -⟩ | ⟨-, μ₁, hS, rfl⟩ | ⟨-, μ₂₃, hNW, rfl⟩
  · exact absurd rfl habs
  · exact (syncN_no_tau hS).elim
  · rw [System.parallel_step] at hNW
    rcases hNW with ⟨habs, -⟩ | ⟨-, μ₂, hN, rfl⟩ | ⟨-, μ₃, hO, rfl⟩
    · exact absurd rfl habs
    · obtain ⟨w', rfl⟩ := netStep_dirac hN
      exact Or.inl ⟨w', hN, by rw [prodPMF_pure_pure, prodPMF_pure_pure]⟩
    · exact Or.inr ⟨μ₃,
        (System.mapIdle_step_some (wccPull_inl Lab.tau) μ₃).mp hO, rfl⟩

/-! ### Pinning the process tuple -/

theorem procsN_update {P : Params} {u x : ∀ _ : Fin P.n, ABANodeN P.n}
    {id : Fin P.n} {nd : ABANodeN P.n}
    (hown : (PMF.pure (x id) : PMF (ABANodeN P.n)) = PMF.pure nd)
    (hfor : ∀ i, i ≠ id → (PMF.pure (x i) : PMF (ABANodeN P.n)) = PMF.pure (u i)) :
    x = Function.update u id nd := by
  funext i
  by_cases hi : i = id
  · subst hi; rw [Function.update_self]; exact pureN_inj hown
  · rw [Function.update_of_ne hi]; exact pureN_inj (hfor i hi)

theorem procsN_id {P : Params} {u x : ∀ _ : Fin P.n, ABANodeN P.n}
    (hall : ∀ i, (PMF.pure (x i) : PMF (ABANodeN P.n)) = PMF.pure (u i)) : x = u :=
  funext fun i => pureN_inj (hall i)

/-! ### Component rows for building a deployed transition

A builder of a deployed transition supplies, alongside the mover's own row,
the oracle's row on a rendezvous label the pullback does not carry and the
per-process family of a one-mover joint step. Both are used by the layered
presentation (`ABA/Layered.lean`). -/

/-- The oracle idles on a rendezvous label outside the pullback's domain. -/
theorem wccLift_idle (P : Params) (o : ℕ → WCC.SpecState P.n) {e : NetEvt P.n}
    (hφ : wccPull P.n (Sum.inr e) = none) :
    (wccLift P).step o (Sum.inr e) (PMF.pure o) :=
  (System.mapIdle_step_none hφ (PMF.pure o)).mpr rfl

/-- One process moves and every other idles: the per-process family of a
one-mover joint step. -/
theorem procsN_family {P : Params} {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {l : NLab P.n} (id : Fin P.n) (nd : ABANodeN P.n)
    (hown : ABAProcStepN P id (u id) l (PMF.pure nd))
    (hfor : ∀ i, i ≠ id → ABAProcStepN P i (u i) l (PMF.pure (u i))) :
    ∀ i, ABAProcStepN P i (u i) l (PMF.pure (Function.update u id nd i)) := by
  intro i
  by_cases hi : i = id
  · subst hi; rw [Function.update_self]; exact hown
  · rw [Function.update_of_ne hi]; exact hfor i hi

end Net

end ABA
end PLTS
