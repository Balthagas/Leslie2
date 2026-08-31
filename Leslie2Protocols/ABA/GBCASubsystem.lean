/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Factors
import Leslie2Protocols.ABA.GBCASim
import Leslie2Protocols.Framework.FamilySim
import Leslie2Protocols.Framework.IdleFamily

/-!
# The round's graded-agreement subsystem

One round of the deployed protocol, taken apart into the pieces that run it:
`n` corruption-blind local programs, one per process, beside the round's own
message fabric. The subsystem is the unit the analysis replaces by the graded
agreement specification, so it is drawn to be exactly what that replacement
may see — the round's handshake ports and nothing else.

A local program holds one stage record: the process's own protocol data and
the messages delivered to it, indexed by sender (`GBCA.ProcNodeN`). It holds
no corrupted set, no corruption flag and no record of what it has multicast;
its guards read the record and the inbox, never the identity of the caller.
The round loop that drives the ports is not here either — a call writes the
stage record alone, a return sets the record's `returned` flag alone.

The round's message fabric holds the per-sender pools and the corrupted set.
A multicast is a joint step of the sender, which writes its record, and the
fabric, which pools the message; a delivery is a joint step of the fabric,
which checks that the message is pooled under the named sender, and the
receiver, which files it under that sender's inbox row.

The two rendezvous — the multicast and the delivery — are labels of the
subsystem-internal alphabet `GLab n = NLab n ⊕ GEvt n`, and they are hidden
before anything outside sees the subsystem: `sub` speaks the shared extended
alphabet `NLab n`, in which the round's interface is `callG r`, `retG r`,
`gcallLoop r` and the three Byzantine graded-agreement drives of round `r`.
The stage-multicast and stage-delivery constructors of `NetEvt` are therefore
not part of that interface — no component offers them, so they carry no
transition of the subsystem (`sub_gsnd_dead`, `sub_gdlv_dead`).

`gbcaSide` is the ℕ-indexed family of these subsystems: `System.family`
routes a round-tagged label to its round, takes `τ` at any round, and
broadcasts `fail` to every round at once.

## Model and deviations

* **D1 (determinised `fail`).** `GNetState.corrupt` is the total Dirac
  function guarded by `k ∉ F ∧ |F| < f`. `fail` is not a row of any rule
  table here: it is the family's broadcast act, applied to every round's
  fabric simultaneously, which is what keeps the per-round copies of the
  corrupted set in lockstep.
* **D5 (set-based network).** Multicasts are idempotent: `pool j` is the set
  of messages `j` has multicast in this round, and `inbox k` at a program is
  the set of messages from `k` delivered there. Thresholds count distinct
  senders. A corrupted sender's injections enter its pool through the
  fabric's own `byzG` transition.
* **D8 (participation gating).** The protocol sends require the record to
  have received its input: the algorithm's handlers only run inside a called
  instance.
* **D11 (Byzantine handshake drives), split.** A drive is authorised by a
  `k ∈ F` guard and has an effect on the round's data. The subsystem carries
  the effect and not the authorisation: `byzCallG` opens the stage record and
  pools its `⟨INPUT, b⟩` without any `k ∈ F` guard, and `byzRetG` sets the
  `returned` flag on the same evidence an honest return needs. The guard
  belongs to the network that surrounds the subsystem, where it applies to
  the drive label that stays visible at this boundary.
* **D18 (the five-level ladder).** The send rows are the five levels
  `INPUT / ECHO / VOTE / BIND / SEAL` and the three graded returns of the
  cited algorithm, not the four-round compression.

## The interface

Every row mirrors the stage-visible half of one rule of the round instance
(`ABA/GBCAImpl.lean`), split between the program that owns the record and the
fabric that owns the pool. What the instance's rule writes on the core slice —
the round loop's phase, estimate and grade — appears nowhere here: that slice
is a different component of the deployed system.

## The replacement

`subSim` is what licenses replacing the round subsystem by the graded
agreement specification. It runs through the round instance in two legs.

The first leg is strong and functional. The subsystem and the instance run on
the same state: `GBCA.ImplState` is the pair of the stage records and the
fabric, which are exactly the boxes composed here. `sub_projects` says that
every transition of the subsystem is a transition of the instance at that same
state, one step for one step, with no stuttering: a joint call is the
instance's call, a hidden multicast or delivery is the protocol rule or the
delivery it carries, a fabric injection is the instance's Byzantine row. The
two are one round under two presentations — a single rule table on one side,
`n` programs beside a fabric on the other.

The second leg is the per-instance refinement `GBCA.implRefines`
(`ABA/GBCASim.lean`), used as it stands. Its answer is a weak run of the
specification over the shared alphabet `Lab n`, which is lifted to the
subsystem's interface along `gPull`: the projection that reads a Byzantine
call drive as a call, a Byzantine return drive as a return, and the two call
loops as calls, which the specification takes on its input-enabledness row
(D11). The lifted specification `liftedSpecG` — the specification read back
along `gPull` — is the system that replaces the subsystem, and `gActSpec` is
the broadcast corruption act it carries at that alphabet.
-/

namespace PLTS
namespace ABA
namespace GSub

open Net

/-! ### The subsystem-internal alphabet

The two rendezvous the shared alphabet cannot name. They are untagged: the
round is the identity of the instance they belong to, and they are hidden
before the family sees the subsystem at all. -/

/-- The internal rendezvous of one round: the multicast and the delivery. -/
inductive GEvt (n : ℕ) : Type
  /-- Process `j` hands `m` to the round's message fabric. -/
  | snd (j : Fin n) (m : GBCA.Msg)
  /-- The fabric delivers `j`'s `m` to `i`. -/
  | dlv (i j : Fin n) (m : GBCA.Msg)
  deriving DecidableEq

/-- The subsystem-internal alphabet: the shared extended alphabet plus the two
rendezvous. Its silent label is `Sum.inl τ`, so every `Sum.inr` label is
observable and hence hideable. -/
abbrev GLab (n : ℕ) : Type := NLab n ⊕ GEvt n

/-- The rendezvous labels, hidden by the subsystem. -/
def gEvents (n : ℕ) : Set (GLab n) := {l | ∃ e : GEvt n, l = Sum.inr e}

@[simp] theorem inl_notMem_gEvents {n : ℕ} (l : NLab n) :
    Sum.inl l ∉ gEvents n := by
  simp [gEvents]

@[simp] theorem inr_mem_gEvents {n : ℕ} (e : GEvt n) :
    Sum.inr e ∈ gEvents n := ⟨e, rfl⟩

@[simp] theorem glab_tau (n : ℕ) :
    (Silent.τ : GLab n) = Sum.inl (Sum.inl Lab.tau) := rfl

/-! ### The local graded-agreement program

Process `j`'s program in this round. Every guard reads the stage record and
the inbox and nothing else. A rendezvous row carries the program's half of a
joint step with the fabric — on a send the record write, on a delivery the
inbox write. The rows are exactly the labels that reach the round's instance:
the round's own handshake ports and the two rendezvous. -/

/-- The step relation of the local graded-agreement program of process `j` in
round `r`. -/
inductive GProcStep (P : Params) (r : ℕ) (j : Fin P.n) :
    GBCA.ProcNodeN P.n → GLab P.n → PMF (GBCA.ProcNodeN P.n) → Prop
  /-- The call arrives: record the input and mark `⟨INPUT, b⟩` as multicast.
  The pooling of that message is the fabric's half (`ImplStep.call`). -/
  | call (p : GBCA.ProcNodeN P.n) (b : Bool) (h : p.proc.input = none) :
      GProcStep P r j p (Sum.inl (Sum.inl (.callG r j b)))
        (PMF.pure (p.setP { p.proc with
          input := some b,
          sentInput := Function.update p.proc.sentInput b true }))
  /-- A call addressed elsewhere: not `j`'s business. -/
  | callIdle (p : GBCA.ProcNodeN P.n) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      GProcStep P r j p (Sum.inl (Sum.inl (.callG r id b))) (PMF.pure p)
  /-- A call against an already-called stage record: the record does not move
  (`ImplStep.callLoop`). -/
  | callLoop (p : GBCA.ProcNodeN P.n) (id : Fin P.n) (b : Bool) :
      GProcStep P r j p (Sum.inl (Sum.inr (.gcallLoop r id b))) (PMF.pure p)
  /-- Return with grade `A v`: an `n − f` `SEAL v` quorum (`ImplStep.retA`). -/
  | retA (p : GBCA.ProcNodeN P.n) (v : Bool)
      (hcnt : P.n - P.f ≤ p.recvCount (.seal (some v)))
      (hret : p.proc.returned = false) :
      GProcStep P r j p (Sum.inl (Sum.inl (.retG r j (.A v))))
        (PMF.pure (p.setP { p.proc with returned := true }))
  /-- Return with grade `B v`: an `n − f` any-`SEAL` quorum containing
  `SEAL v`, `f + 1` `BIND v`s and `|Valid| > 1` (`ImplStep.retB`). -/
  | retB (p : GBCA.ProcNodeN P.n) (v : Bool)
      (hcnt : P.n - P.f ≤ p.sealCount)
      (honce : ∃ k, GBCA.Msg.seal (some v) ∈ p.inbox k)
      (hbind : P.f + 1 ≤ p.recvCount (.bind (some v)))
      (hval : p.bothValid P)
      (hret : p.proc.returned = false) :
      GProcStep P r j p (Sum.inl (Sum.inl (.retG r j (.B v))))
        (PMF.pure (p.setP { p.proc with returned := true }))
  /-- Return with grade `C`: an `n − f` `SEAL ⊥` quorum and `|Valid| > 1`
  (`ImplStep.retC`). -/
  | retC (p : GBCA.ProcNodeN P.n)
      (hcnt : P.n - P.f ≤ p.recvCount (.seal none))
      (hval : p.bothValid P)
      (hret : p.proc.returned = false) :
      GProcStep P r j p (Sum.inl (Sum.inl (.retG r j .C)))
        (PMF.pure (p.setP { p.proc with returned := true }))
  /-- A return to another process: not `j`'s business. -/
  | retIdle (p : GBCA.ProcNodeN P.n) (id : Fin P.n) (out : GbcaOut) (hid : id ≠ j) :
      GProcStep P r j p (Sum.inl (Sum.inl (.retG r id out))) (PMF.pure p)
  /-- A driven call (D11): the stage record opens on the driven bit, exactly
  as an honest call opens it (`ImplStep.call`). -/
  | byzCall (p : GBCA.ProcNodeN P.n) (b : Bool) (h : p.proc.input = none) :
      GProcStep P r j p (Sum.inl (Sum.inr (.byzCallG r j b)))
        (PMF.pure (p.setP { p.proc with
          input := some b,
          sentInput := Function.update p.proc.sentInput b true }))
  /-- A driven call at another process: not `j`'s business. -/
  | byzCallIdle (p : GBCA.ProcNodeN P.n) (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      GProcStep P r j p (Sum.inl (Sum.inr (.byzCallG r k b))) (PMF.pure p)
  /-- A driven call against an already-called stage record (D11): the record
  does not move (`ImplStep.callLoop`). -/
  | byzCallLoop (p : GBCA.ProcNodeN P.n) (k : Fin P.n) (b : Bool) :
      GProcStep P r j p (Sum.inl (Sum.inr (.byzCallGLoop r k b))) (PMF.pure p)
  /-- A driven grade-`A` return (D11): the same evidence and the same record
  write as the honest return (`ImplStep.retA`). -/
  | byzRetA (p : GBCA.ProcNodeN P.n) (v : Bool)
      (hcnt : P.n - P.f ≤ p.recvCount (.seal (some v)))
      (hret : p.proc.returned = false) :
      GProcStep P r j p (Sum.inl (Sum.inr (.byzRetG r j (.A v))))
        (PMF.pure (p.setP { p.proc with returned := true }))
  /-- A driven grade-`B` return (D11) (`ImplStep.retB`). -/
  | byzRetB (p : GBCA.ProcNodeN P.n) (v : Bool)
      (hcnt : P.n - P.f ≤ p.sealCount)
      (honce : ∃ k, GBCA.Msg.seal (some v) ∈ p.inbox k)
      (hbind : P.f + 1 ≤ p.recvCount (.bind (some v)))
      (hval : p.bothValid P)
      (hret : p.proc.returned = false) :
      GProcStep P r j p (Sum.inl (Sum.inr (.byzRetG r j (.B v))))
        (PMF.pure (p.setP { p.proc with returned := true }))
  /-- A driven grade-`C` return (D11) (`ImplStep.retC`). -/
  | byzRetC (p : GBCA.ProcNodeN P.n)
      (hcnt : P.n - P.f ≤ p.recvCount (.seal none))
      (hval : p.bothValid P)
      (hret : p.proc.returned = false) :
      GProcStep P r j p (Sum.inl (Sum.inr (.byzRetG r j .C)))
        (PMF.pure (p.setP { p.proc with returned := true }))
  /-- A driven return at another process: not `j`'s business. -/
  | byzRetIdle (p : GBCA.ProcNodeN P.n) (k : Fin P.n) (out : GbcaOut) (hk : k ≠ j) :
      GProcStep P r j p (Sum.inl (Sum.inr (.byzRetG r k out))) (PMF.pure p)
  /-- `INPUT` relay: `f + 1` receipts of `⟨INPUT, b⟩`, not yet multicast
  (`ImplStep.relay`; D8, D18). -/
  | sndRelay (p : GBCA.ProcNodeN P.n) (b : Bool)
      (hin : p.proc.input ≠ none)
      (hcnt : P.f + 1 ≤ p.recvCount (.input b))
      (hsend : p.proc.sentInput b = false) :
      GProcStep P r j p (Sum.inr (.snd j (.input b)))
        (PMF.pure (p.setP { p.proc with
          sentInput := Function.update p.proc.sentInput b true }))
  /-- `ECHO b`: an `n − f` `INPUT b` quorum (`ImplStep.echo`; D18). -/
  | sndEcho (p : GBCA.ProcNodeN P.n) (b : Bool)
      (hin : p.proc.input ≠ none)
      (hcnt : P.n - P.f ≤ p.recvCount (.input b))
      (hsend : p.proc.sentEcho = none) :
      GProcStep P r j p (Sum.inr (.snd j (.echo b)))
        (PMF.pure (p.setP { p.proc with sentEcho := some b }))
  /-- `VOTE b`: an `n − f` `ECHO b` quorum (`ImplStep.voteBit`; D18). -/
  | sndVoteBit (p : GBCA.ProcNodeN P.n) (b : Bool)
      (hin : p.proc.input ≠ none)
      (hcnt : P.n - P.f ≤ p.recvCount (.echo b))
      (hsend : p.proc.sentVote = none) :
      GProcStep P r j p (Sum.inr (.snd j (.vote (some b))))
        (PMF.pure (p.setP { p.proc with sentVote := some (some b) }))
  /-- `VOTE ⊥`: `n − f` `ECHO`s of any payload and `|Valid| > 1`
  (`ImplStep.voteBot`; D18). -/
  | sndVoteBot (p : GBCA.ProcNodeN P.n)
      (hin : p.proc.input ≠ none)
      (hcnt : P.n - P.f ≤ p.echoCount)
      (hval : p.bothValid P)
      (hsend : p.proc.sentVote = none) :
      GProcStep P r j p (Sum.inr (.snd j (.vote none)))
        (PMF.pure (p.setP { p.proc with sentVote := some none }))
  /-- `BIND b`: an `n − f` `VOTE b` quorum (`ImplStep.bindBit`; D18). -/
  | sndBindBit (p : GBCA.ProcNodeN P.n) (b : Bool)
      (hin : p.proc.input ≠ none)
      (hcnt : P.n - P.f ≤ p.recvCount (.vote (some b)))
      (hsend : p.proc.sentBind = none) :
      GProcStep P r j p (Sum.inr (.snd j (.bind (some b))))
        (PMF.pure (p.setP { p.proc with sentBind := some (some b) }))
  /-- `BIND ⊥`: `n − f` `VOTE`s of any payload and `|Valid| > 1`
  (`ImplStep.bindBot`; D18). -/
  | sndBindBot (p : GBCA.ProcNodeN P.n)
      (hin : p.proc.input ≠ none)
      (hcnt : P.n - P.f ≤ p.voteCount)
      (hval : p.bothValid P)
      (hsend : p.proc.sentBind = none) :
      GProcStep P r j p (Sum.inr (.snd j (.bind none)))
        (PMF.pure (p.setP { p.proc with sentBind := some none }))
  /-- `SEAL b`: an `n − f` `BIND b` quorum (`ImplStep.sealBit`; D18). -/
  | sndSealBit (p : GBCA.ProcNodeN P.n) (b : Bool)
      (hin : p.proc.input ≠ none)
      (hcnt : P.n - P.f ≤ p.recvCount (.bind (some b)))
      (hsend : p.proc.sentSeal = none) :
      GProcStep P r j p (Sum.inr (.snd j (.seal (some b))))
        (PMF.pure (p.setP { p.proc with sentSeal := some (some b) }))
  /-- `SEAL ⊥`: `n − f` `BIND`s of any payload and `|Valid| > 1`
  (`ImplStep.sealBot`; D18). -/
  | sndSealBot (p : GBCA.ProcNodeN P.n)
      (hin : p.proc.input ≠ none)
      (hcnt : P.n - P.f ≤ p.bindCount)
      (hval : p.bothValid P)
      (hsend : p.proc.sentSeal = none) :
      GProcStep P r j p (Sum.inr (.snd j (.seal none)))
        (PMF.pure (p.setP { p.proc with sentSeal := some none }))
  /-- A multicast by another process: not `j`'s business. -/
  | sndIdle (p : GBCA.ProcNodeN P.n) (k : Fin P.n) (m : GBCA.Msg) (hk : k ≠ j) :
      GProcStep P r j p (Sum.inr (.snd k m)) (PMF.pure p)
  /-- Delivery, receiver's half: file the message under the sender's inbox row.
  Authenticity is the fabric's conjunct (`ImplStep.deliver`; D5). -/
  | dlvRecv (p : GBCA.ProcNodeN P.n) (k : Fin P.n) (m : GBCA.Msg) :
      GProcStep P r j p (Sum.inr (.dlv j k m)) (PMF.pure (p.deliverTo k m))
  /-- A delivery to another process: not `j`'s business. -/
  | dlvIdle (p : GBCA.ProcNodeN P.n) (i k : Fin P.n) (m : GBCA.Msg) (hi : i ≠ j) :
      GProcStep P r j p (Sum.inr (.dlv i k m)) (PMF.pure p)

/-! ### The round's message fabric

The one box of the subsystem that holds what no program may see: the per-sender
pools and the corrupted set. It participates in every send by pooling the
message and in every delivery by checking that the message is pooled, and it
is where a corrupted sender's injections enter (D5). Its state record
`GNetState` stands beside the stage record in `ABA/GBCAImpl.lean`, the two of
them being the factors of a round's state; what follows is its rule table. -/

/-- The step relation of the round's message fabric. All transitions are
Dirac. -/
inductive GNetStep (P : Params) (r : ℕ) :
    GNetState P.n → GLab P.n → PMF (GNetState P.n) → Prop
  /-- The fabric's half of a multicast: pool the message under its sender.
  Authenticity is the sender's joint participation (D5). -/
  | snd (w : GNetState P.n) (j : Fin P.n) (m : GBCA.Msg) :
      GNetStep P r w (Sum.inr (.snd j m)) (PMF.pure (w.gpool j m))
  /-- The fabric's half of a delivery: the message must be pooled under the
  named sender, and delivery does not consume it (`ImplStep.deliver`; D5). -/
  | dlv (w : GNetState P.n) (i j : Fin P.n) (m : GBCA.Msg) (h : m ∈ w.pool j) :
      GNetStep P r w (Sum.inr (.dlv i j m)) (PMF.pure w)
  /-- Byzantine injection: a corrupted sender multicasts anything, at any time
  (`ImplStep.byz`; D5, D11). -/
  | byzG (w : GNetState P.n) (k : Fin P.n) (m : GBCA.Msg) (hF : k ∈ w.F) :
      GNetStep P r w (Sum.inl (Sum.inl .tau)) (PMF.pure (w.gpool k m))
  /-- The fabric's half of the call: pool the caller's `⟨INPUT, b⟩`
  (`ImplStep.call`). -/
  | callG (w : GNetState P.n) (id : Fin P.n) (b : Bool) :
      GNetStep P r w (Sum.inl (Sum.inl (.callG r id b)))
        (PMF.pure (w.gpool id (.input b)))
  /-- A return sends nothing. -/
  | retGIdle (w : GNetState P.n) (id : Fin P.n) (out : GbcaOut) :
      GNetStep P r w (Sum.inl (Sum.inl (.retG r id out))) (PMF.pure w)
  /-- A call against an already-called stage record sends nothing
  (`ImplStep.callLoop`). -/
  | gcallLoop (w : GNetState P.n) (id : Fin P.n) (b : Bool) :
      GNetStep P r w (Sum.inl (Sum.inr (.gcallLoop r id b))) (PMF.pure w)
  /-- A driven call (D11): its `⟨INPUT, b⟩` is pooled here, and there is no
  `k ∈ F` guard on this row — the authorisation of the drive belongs to the
  network outside the subsystem, where the drive label stays visible. -/
  | byzCallG (w : GNetState P.n) (k : Fin P.n) (b : Bool) :
      GNetStep P r w (Sum.inl (Sum.inr (.byzCallG r k b)))
        (PMF.pure (w.gpool k (.input b)))
  /-- A driven call against an already-called stage record sends nothing
  (D11). -/
  | byzCallGLoop (w : GNetState P.n) (k : Fin P.n) (b : Bool) :
      GNetStep P r w (Sum.inl (Sum.inr (.byzCallGLoop r k b))) (PMF.pure w)
  /-- A driven return sends nothing (D11). -/
  | byzRetG (w : GNetState P.n) (k : Fin P.n) (out : GbcaOut) :
      GNetStep P r w (Sum.inl (Sum.inr (.byzRetG r k out))) (PMF.pure w)

/-! ### The subsystem and its family -/

/-- The local graded-agreement program of process `j` in round `r`. -/
noncomputable def gbcaProc (P : Params) (r : ℕ) (j : Fin P.n) :
    System (GBCA.ProcNodeN P.n) (GLab P.n) where
  init := GBCA.ProcNodeN.initial P.n
  step := GProcStep P r j

@[simp] theorem gbcaProc_init (P : Params) (r : ℕ) (j : Fin P.n) :
    (gbcaProc P r j).init = GBCA.ProcNodeN.initial P.n := rfl

@[simp] theorem gbcaProc_step (P : Params) (r : ℕ) (j : Fin P.n)
    (p : GBCA.ProcNodeN P.n) (l : GLab P.n) (ν : PMF (GBCA.ProcNodeN P.n)) :
    (gbcaProc P r j).step p l ν ↔ GProcStep P r j p l ν := Iff.rfl

/-- The round's message fabric. -/
noncomputable def gNet (P : Params) (r : ℕ) :
    System (GNetState P.n) (GLab P.n) where
  init := GNetState.initial P.n
  step := GNetStep P r

@[simp] theorem gNet_init (P : Params) (r : ℕ) :
    (gNet P r).init = GNetState.initial P.n := rfl

@[simp] theorem gNet_step (P : Params) (r : ℕ) (w : GNetState P.n)
    (l : GLab P.n) (μ : PMF (GNetState P.n)) :
    (gNet P r).step w l μ ↔ GNetStep P r w l μ := Iff.rfl

/-- The programs beside the fabric, over the subsystem-internal alphabet. -/
noncomputable def subPre (P : Params) (r : ℕ) :
    System (GBCA.ImplState P.n) (GLab P.n) :=
  (System.syncProduct (gbcaProc P r)).parallel (gNet P r)

/-- **The round-`r` subsystem**: the programs beside the fabric, the two
rendezvous hidden, the result read back over the shared extended alphabet. Its
interface is the round's ports — `callG r`, `retG r`, `gcallLoop r` and the
three graded-agreement drives of round `r`. -/
noncomputable def sub (P : Params) (r : ℕ) :
    System (GBCA.ImplState P.n) (NLab P.n) :=
  ((subPre P r).abstract (gEvents P.n)).relabel

/-- The round a label of the subsystem interface belongs to. Every other label
of the shared extended alphabet — the ABA API, the coin ports, `fail`, the
DECIDED layer, and the stage rendezvous of the deployed network — is owned by
no round. -/
def gOwns {n : ℕ} : NLab n → Option ℕ
  | Sum.inl (.callG r _ _) => some r
  | Sum.inl (.retG r _ _) => some r
  | Sum.inr (.gcallLoop r _ _) => some r
  | Sum.inr (.byzCallG r _ _) => some r
  | Sum.inr (.byzCallGLoop r _ _) => some r
  | Sum.inr (.byzRetG r _ _) => some r
  | _ => none

/-- Corruption is the one label every round takes at once. -/
def isFailN {n : ℕ} : NLab n → Prop
  | Sum.inl (.fail _) => True
  | _ => False

instance {n : ℕ} : DecidablePred (isFailN (n := n)) := fun l => by
  cases l with
  | inl l => cases l <;> simp only [isFailN] <;> infer_instance
  | inr e => cases e <;> simp only [isFailN] <;> infer_instance

/-- The broadcast corruption act on a subsystem state: the round's fabric
records it, the stage records do not (D1). -/
def gAct (P : Params) : NLab P.n → GBCA.ImplState P.n → GBCA.ImplState P.n
  | Sum.inl (.fail k), (u, w) => (u, w.corrupt P k)
  | _, s => s

/-- **The graded-agreement side of the deployed protocol**: the ℕ-indexed
family of round subsystems. A round-tagged label moves its round alone, `τ`
moves one round, and `fail` is the broadcast that keeps every round's copy of
the corrupted set in lockstep. -/
noncomputable def gbcaSide (P : Params) :
    System (ℕ → GBCA.ImplState P.n) (NLab P.n) :=
  System.family (sub P) gOwns isFailN (gAct P)

/-! ### Determinacy

Both rule tables written here are Dirac, so the subsystem and its family are
LTS: the probabilistic transition of the deployed protocol is the coin
resolution, which is not part of a graded-agreement round. -/

/-- Every program transition is Dirac. -/
theorem gProcStep_dirac {P : Params} {r : ℕ} {j : Fin P.n}
    {p : GBCA.ProcNodeN P.n} {l : GLab P.n} {ν : PMF (GBCA.ProcNodeN P.n)}
    (h : GProcStep P r j p l ν) : ∃ p', ν = PMF.pure p' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every fabric transition is Dirac. -/
theorem gNetStep_dirac {P : Params} {r : ℕ} {w : GNetState P.n} {l : GLab P.n}
    {μ : PMF (GNetState P.n)} (h : GNetStep P r w l μ) :
    ∃ w', μ = PMF.pure w' := by
  cases h <;> exact ⟨_, rfl⟩

/-- A local program is an LTS. -/
theorem gbcaProc_isLTS (P : Params) (r : ℕ) (j : Fin P.n) :
    (gbcaProc P r j).IsLTS :=
  fun _ _ _ h => gProcStep_dirac h

/-- The message fabric is an LTS. -/
theorem gNet_isLTS (P : Params) (r : ℕ) : (gNet P r).IsLTS :=
  fun _ _ _ h => gNetStep_dirac h

/-- The synchronised group of programs is an LTS. -/
theorem syncG_isLTS (P : Params) (r : ℕ) :
    (System.syncProduct (gbcaProc P r)).IsLTS :=
  System.syncProduct_isLTS (gbcaProc_isLTS P r)

/-- The programs beside the fabric form an LTS. -/
theorem subPre_isLTS (P : Params) (r : ℕ) : (subPre P r).IsLTS :=
  System.parallel_isLTS (syncG_isLTS P r) (gNet_isLTS P r)

/-- The subsystem is an LTS. -/
theorem sub_isLTS (P : Params) (r : ℕ) : (sub P r).IsLTS :=
  System.relabel_isLTS (System.abstract_isLTS (subPre_isLTS P r) _)

/-- The family of subsystems is an LTS. -/
theorem gbcaSide_isLTS (P : Params) : (gbcaSide P).IsLTS :=
  System.family_isLTS (sub_isLTS P) gOwns isFailN (gAct P)

/-- No program rule fires on `τ`: a program only ever moves in a rendezvous or
on one of the round's ports. The subsystem's silent transitions are therefore
exactly the fabric's injections and the hidden rendezvous. -/
theorem gProcStep_no_tau {P : Params} {r : ℕ} {j : Fin P.n}
    {p : GBCA.ProcNodeN P.n} {ν : PMF (GBCA.ProcNodeN P.n)}
    (h : GProcStep P r j p (Silent.τ : GLab P.n) ν) : False := by
  rw [glab_tau] at h; cases h

/-! ### Reading and building subsystem transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ syncProduct`; the lemmas
below unfold it once and for all, in both directions. -/

/-- A synchronised transition of the program group on a visible label: every
program steps, and the joint distribution is Dirac. -/
theorem syncG_inv {P : Params} {r : ℕ} {u : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n}
    {l : GLab P.n} {μ : PMF (∀ _ : Fin P.n, GBCA.ProcNodeN P.n)}
    (h : (System.syncProduct (gbcaProc P r)).step u l μ) :
    ∃ x : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n,
      μ = PMF.pure x ∧ ∀ i, GProcStep P r i (u i) l (PMF.pure (x i)) := by
  rw [System.syncProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨rfl, i, μ_i, hstep, -⟩
  · have hx : ∀ i, ∃ p', μ_ i = PMF.pure p' := fun i => gProcStep_dirac (hall i)
    choose x hx using hx
    refine ⟨x, ?_, fun i => ?_⟩
    · rw [show μ_ = fun i => PMF.pure (x i) from funext hx]
      exact piPMF_pure x
    · rw [← hx i]; exact hall i
  · exact absurd hstep gProcStep_no_tau

/-- Build a synchronised transition of the program group from per-process
Dirac steps. -/
theorem syncG_pure {P : Params} {r : ℕ}
    {u x : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n} {l : GLab P.n}
    (hl : l ≠ Silent.τ)
    (h : ∀ i, GProcStep P r i (u i) l (PMF.pure (x i))) :
    (System.syncProduct (gbcaProc P r)).step u l (PMF.pure x) := by
  rw [System.syncProduct_step]
  exact Or.inl ⟨hl, fun i => PMF.pure (x i), h, (piPMF_pure x).symm⟩

/-- The program group has no silent transition: no program has a `τ` row. -/
theorem syncG_no_tau {P : Params} {r : ℕ}
    {u : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n}
    {μ : PMF (∀ _ : Fin P.n, GBCA.ProcNodeN P.n)}
    (h : (System.syncProduct (gbcaProc P r)).step u (Silent.τ : GLab P.n) μ) :
    False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact gProcStep_no_tau hstep

/-- The subsystem's step relation, unfolded to the hidden-rendezvous case and
the shared-label case. -/
theorem sub_step_iff (P : Params) (r : ℕ) (q : GBCA.ImplState P.n) (l : NLab P.n)
    (μ : PMF (GBCA.ImplState P.n)) :
    (sub P r).step q l μ ↔
      (l = Sum.inl Lab.tau ∧ ∃ e : GEvt P.n, (subPre P r).step q (Sum.inr e) μ) ∨
      (subPre P r).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_gEvents e, hstep⟩
    · exact Or.inr ⟨inl_notMem_gEvents l, hstep⟩

/-- Build a joint transition of the programs and the fabric on a rendezvous
label. -/
theorem subPre_event_step (P : Params) (r : ℕ)
    {u x : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n} {w w' : GNetState P.n}
    (e : GEvt P.n)
    (hall : ∀ i, GProcStep P r i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : GNetStep P r w (Sum.inr e) (PMF.pure w')) :
    (subPre P r).step (u, w) (Sum.inr e) (PMF.pure (x, w')) := by
  rw [subPre, System.parallel_step]
  exact Or.inl ⟨by simp, PMF.pure x, PMF.pure w', syncG_pure (by simp) hall, hn,
    (prodPMF_pure_pure _ _).symm⟩

/-- Build a joint transition of the programs and the fabric on a visible
shared label. -/
theorem subPre_lab_step (P : Params) (r : ℕ)
    {u x : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n} {w w' : GNetState P.n}
    {l : NLab P.n} (hl : l ≠ Sum.inl Lab.tau)
    (hall : ∀ i, GProcStep P r i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hn : GNetStep P r w (Sum.inl l) (PMF.pure w')) :
    (subPre P r).step (u, w) (Sum.inl l) (PMF.pure (x, w')) := by
  have hne : (Sum.inl l : GLab P.n) ≠ Silent.τ := by
    rw [glab_tau]; simpa using hl
  rw [subPre, System.parallel_step]
  exact Or.inl ⟨hne, PMF.pure x, PMF.pure w', syncG_pure hne hall, hn,
    (prodPMF_pure_pure _ _).symm⟩

/-- Build a silent transition of the programs and the fabric from a
fabric-local one. -/
theorem subPre_tau_net (P : Params) (r : ℕ)
    {u : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n} {w w' : GNetState P.n}
    (hn : GNetStep P r w (Sum.inl (Sum.inl .tau)) (PMF.pure w')) :
    (subPre P r).step (u, w) (Sum.inl (Sum.inl .tau)) (PMF.pure (u, w')) := by
  rw [subPre, System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure w', hn, (prodPMF_pure_pure _ _).symm⟩)

/-- A hidden rendezvous is a silent transition of the subsystem. -/
theorem sub_event_step (P : Params) (r : ℕ)
    {u x : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n} {w w' : GNetState P.n}
    (e : GEvt P.n)
    (hall : ∀ i, GProcStep P r i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : GNetStep P r w (Sum.inr e) (PMF.pure w')) :
    (sub P r).step (u, w) (Sum.inl Lab.tau) (PMF.pure (x, w')) :=
  (sub_step_iff P r _ _ _).mpr
    (Or.inl ⟨rfl, e, subPre_event_step P r e hall hn⟩)

/-- A visible shared label is a transition of the subsystem. -/
theorem sub_lab_step (P : Params) (r : ℕ)
    {u x : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n} {w w' : GNetState P.n}
    {l : NLab P.n} (hl : l ≠ Sum.inl Lab.tau)
    (hall : ∀ i, GProcStep P r i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hn : GNetStep P r w (Sum.inl l) (PMF.pure w')) :
    (sub P r).step (u, w) l (PMF.pure (x, w')) :=
  (sub_step_iff P r _ _ _).mpr (Or.inr (subPre_lab_step P r hl hall hn))

/-- A fabric-local injection is a silent transition of the subsystem. -/
theorem sub_tau_net (P : Params) (r : ℕ)
    {u : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n} {w w' : GNetState P.n}
    (hn : GNetStep P r w (Sum.inl (Sum.inl .tau)) (PMF.pure w')) :
    (sub P r).step (u, w) (Sum.inl Lab.tau) (PMF.pure (u, w')) :=
  (sub_step_iff P r _ _ _).mpr (Or.inr (subPre_tau_net P r hn))

/-! ### One program's rules, by label class

Each lemma reads a row of the table off its label: the participant's row as
its guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. The record and the distribution are
variables, so `cases` unifies against any stage record. -/

section ProcInversion

variable {P : Params} {r : ℕ} {j : Fin P.n} {p : GBCA.ProcNodeN P.n}
  {ν : PMF (GBCA.ProcNodeN P.n)}

theorem stepG_callG_own {b : Bool}
    (h : GProcStep P r j p (Sum.inl (Sum.inl (.callG r j b))) ν) :
    p.proc.input = none ∧
      ν = PMF.pure (p.setP { p.proc with
        input := some b,
        sentInput := Function.update p.proc.sentInput b true }) := by
  cases h
  case call => exact ⟨by assumption, rfl⟩
  case callIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_callG_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : GProcStep P r j p (Sum.inl (Sum.inl (.callG r id b))) ν) :
    ν = PMF.pure p := by
  cases h
  case call => exact absurd rfl hid
  case callIdle => rfl

theorem stepG_gcallLoop {id : Fin P.n} {b : Bool}
    (h : GProcStep P r j p (Sum.inl (Sum.inr (.gcallLoop r id b))) ν) :
    ν = PMF.pure p := by
  cases h
  case callLoop => rfl

theorem stepG_retG_A_own {v : Bool}
    (h : GProcStep P r j p (Sum.inl (Sum.inl (.retG r j (.A v)))) ν) :
    P.n - P.f ≤ p.recvCount (.seal (some v)) ∧ p.proc.returned = false ∧
      ν = PMF.pure (p.setP { p.proc with returned := true }) := by
  cases h
  case retA => exact ⟨by assumption, by assumption, rfl⟩
  case retIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_retG_B_own {v : Bool}
    (h : GProcStep P r j p (Sum.inl (Sum.inl (.retG r j (.B v)))) ν) :
    P.n - P.f ≤ p.sealCount ∧ (∃ k, GBCA.Msg.seal (some v) ∈ p.inbox k) ∧
      P.f + 1 ≤ p.recvCount (.bind (some v)) ∧ p.bothValid P ∧
      p.proc.returned = false ∧
      ν = PMF.pure (p.setP { p.proc with returned := true }) := by
  cases h
  case retB =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case retIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_retG_C_own
    (h : GProcStep P r j p (Sum.inl (Sum.inl (.retG r j .C))) ν) :
    P.n - P.f ≤ p.recvCount (.seal none) ∧ p.bothValid P ∧
      p.proc.returned = false ∧
      ν = PMF.pure (p.setP { p.proc with returned := true }) := by
  cases h
  case retC => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case retIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_retG_foreign {id : Fin P.n} {out : GbcaOut} (hid : id ≠ j)
    (h : GProcStep P r j p (Sum.inl (Sum.inl (.retG r id out))) ν) :
    ν = PMF.pure p := by
  cases h
  case retIdle => rfl
  all_goals exact absurd rfl hid

theorem stepG_byzCallG_own {b : Bool}
    (h : GProcStep P r j p (Sum.inl (Sum.inr (.byzCallG r j b))) ν) :
    p.proc.input = none ∧
      ν = PMF.pure (p.setP { p.proc with
        input := some b,
        sentInput := Function.update p.proc.sentInput b true }) := by
  cases h
  case byzCall => exact ⟨by assumption, rfl⟩
  case byzCallIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_byzCallG_foreign {k : Fin P.n} {b : Bool} (hk : k ≠ j)
    (h : GProcStep P r j p (Sum.inl (Sum.inr (.byzCallG r k b))) ν) :
    ν = PMF.pure p := by
  cases h
  case byzCall => exact absurd rfl hk
  case byzCallIdle => rfl

theorem stepG_byzCallGLoop {k : Fin P.n} {b : Bool}
    (h : GProcStep P r j p (Sum.inl (Sum.inr (.byzCallGLoop r k b))) ν) :
    ν = PMF.pure p := by
  cases h
  case byzCallLoop => rfl

theorem stepG_byzRetG_A_own {v : Bool}
    (h : GProcStep P r j p (Sum.inl (Sum.inr (.byzRetG r j (.A v)))) ν) :
    P.n - P.f ≤ p.recvCount (.seal (some v)) ∧ p.proc.returned = false ∧
      ν = PMF.pure (p.setP { p.proc with returned := true }) := by
  cases h
  case byzRetA => exact ⟨by assumption, by assumption, rfl⟩
  case byzRetIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_byzRetG_B_own {v : Bool}
    (h : GProcStep P r j p (Sum.inl (Sum.inr (.byzRetG r j (.B v)))) ν) :
    P.n - P.f ≤ p.sealCount ∧ (∃ k, GBCA.Msg.seal (some v) ∈ p.inbox k) ∧
      P.f + 1 ≤ p.recvCount (.bind (some v)) ∧ p.bothValid P ∧
      p.proc.returned = false ∧
      ν = PMF.pure (p.setP { p.proc with returned := true }) := by
  cases h
  case byzRetB =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case byzRetIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_byzRetG_C_own
    (h : GProcStep P r j p (Sum.inl (Sum.inr (.byzRetG r j .C))) ν) :
    P.n - P.f ≤ p.recvCount (.seal none) ∧ p.bothValid P ∧
      p.proc.returned = false ∧
      ν = PMF.pure (p.setP { p.proc with returned := true }) := by
  cases h
  case byzRetC => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case byzRetIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_byzRetG_foreign {k : Fin P.n} {out : GbcaOut} (hk : k ≠ j)
    (h : GProcStep P r j p (Sum.inl (Sum.inr (.byzRetG r k out))) ν) :
    ν = PMF.pure p := by
  cases h
  case byzRetIdle => rfl
  all_goals exact absurd rfl hk

theorem stepG_snd_input_own {b : Bool}
    (h : GProcStep P r j p (Sum.inr (.snd j (.input b))) ν) :
    p.proc.input ≠ none ∧ P.f + 1 ≤ p.recvCount (.input b) ∧
      p.proc.sentInput b = false ∧
      ν = PMF.pure (p.setP { p.proc with
        sentInput := Function.update p.proc.sentInput b true }) := by
  cases h
  case sndRelay =>
    exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case sndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_snd_echo_own {b : Bool}
    (h : GProcStep P r j p (Sum.inr (.snd j (.echo b))) ν) :
    p.proc.input ≠ none ∧ P.n - P.f ≤ p.recvCount (.input b) ∧
      p.proc.sentEcho = none ∧
      ν = PMF.pure (p.setP { p.proc with sentEcho := some b }) := by
  cases h
  case sndEcho => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case sndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_snd_voteBit_own {b : Bool}
    (h : GProcStep P r j p (Sum.inr (.snd j (.vote (some b)))) ν) :
    p.proc.input ≠ none ∧ P.n - P.f ≤ p.recvCount (.echo b) ∧
      p.proc.sentVote = none ∧
      ν = PMF.pure (p.setP { p.proc with sentVote := some (some b) }) := by
  cases h
  case sndVoteBit => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case sndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_snd_voteBot_own
    (h : GProcStep P r j p (Sum.inr (.snd j (.vote none))) ν) :
    p.proc.input ≠ none ∧ P.n - P.f ≤ p.echoCount ∧ p.bothValid P ∧
      p.proc.sentVote = none ∧
      ν = PMF.pure (p.setP { p.proc with sentVote := some none }) := by
  cases h
  case sndVoteBot =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case sndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_snd_bindBit_own {b : Bool}
    (h : GProcStep P r j p (Sum.inr (.snd j (.bind (some b)))) ν) :
    p.proc.input ≠ none ∧ P.n - P.f ≤ p.recvCount (.vote (some b)) ∧
      p.proc.sentBind = none ∧
      ν = PMF.pure (p.setP { p.proc with sentBind := some (some b) }) := by
  cases h
  case sndBindBit => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case sndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_snd_bindBot_own
    (h : GProcStep P r j p (Sum.inr (.snd j (.bind none))) ν) :
    p.proc.input ≠ none ∧ P.n - P.f ≤ p.voteCount ∧ p.bothValid P ∧
      p.proc.sentBind = none ∧
      ν = PMF.pure (p.setP { p.proc with sentBind := some none }) := by
  cases h
  case sndBindBot =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case sndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_snd_sealBit_own {b : Bool}
    (h : GProcStep P r j p (Sum.inr (.snd j (.seal (some b)))) ν) :
    p.proc.input ≠ none ∧ P.n - P.f ≤ p.recvCount (.bind (some b)) ∧
      p.proc.sentSeal = none ∧
      ν = PMF.pure (p.setP { p.proc with sentSeal := some (some b) }) := by
  cases h
  case sndSealBit => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case sndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_snd_sealBot_own
    (h : GProcStep P r j p (Sum.inr (.snd j (.seal none))) ν) :
    p.proc.input ≠ none ∧ P.n - P.f ≤ p.bindCount ∧ p.bothValid P ∧
      p.proc.sentSeal = none ∧
      ν = PMF.pure (p.setP { p.proc with sentSeal := some none }) := by
  cases h
  case sndSealBot =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case sndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_snd_foreign {k : Fin P.n} {m : GBCA.Msg} (hk : k ≠ j)
    (h : GProcStep P r j p (Sum.inr (.snd k m)) ν) : ν = PMF.pure p := by
  cases h
  case sndIdle => rfl
  all_goals exact absurd rfl hk

theorem stepG_dlv_own {k : Fin P.n} {m : GBCA.Msg}
    (h : GProcStep P r j p (Sum.inr (.dlv j k m)) ν) :
    ν = PMF.pure (p.deliverTo k m) := by
  cases h
  case dlvRecv => rfl
  case dlvIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_dlv_foreign {i k : Fin P.n} {m : GBCA.Msg} (hi : i ≠ j)
    (h : GProcStep P r j p (Sum.inr (.dlv i k m)) ν) : ν = PMF.pure p := by
  cases h
  case dlvRecv => exact absurd rfl hi
  case dlvIdle => rfl

end ProcInversion

/-! ### The fabric's rules, by label class -/

section NetInversion

variable {P : Params} {r : ℕ} {w : GNetState P.n} {μ : PMF (GNetState P.n)}

theorem netG_snd {j : Fin P.n} {m : GBCA.Msg}
    (h : GNetStep P r w (Sum.inr (.snd j m)) μ) :
    μ = PMF.pure (w.gpool j m) := by
  cases h; rfl

theorem netG_dlv {i j : Fin P.n} {m : GBCA.Msg}
    (h : GNetStep P r w (Sum.inr (.dlv i j m)) μ) :
    m ∈ w.pool j ∧ μ = PMF.pure w := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netG_tau (h : GNetStep P r w (Sum.inl (Sum.inl .tau)) μ) :
    ∃ (k : Fin P.n) (m : GBCA.Msg), k ∈ w.F ∧ μ = PMF.pure (w.gpool k m) := by
  cases h
  case byzG k m hF => exact ⟨k, m, hF, rfl⟩

theorem netG_callG {id : Fin P.n} {b : Bool}
    (h : GNetStep P r w (Sum.inl (Sum.inl (.callG r id b))) μ) :
    μ = PMF.pure (w.gpool id (.input b)) := by
  cases h; rfl

theorem netG_retG {id : Fin P.n} {out : GbcaOut}
    (h : GNetStep P r w (Sum.inl (Sum.inl (.retG r id out))) μ) :
    μ = PMF.pure w := by
  cases h; rfl

theorem netG_gcallLoop {id : Fin P.n} {b : Bool}
    (h : GNetStep P r w (Sum.inl (Sum.inr (.gcallLoop r id b))) μ) :
    μ = PMF.pure w := by
  cases h; rfl

theorem netG_byzCallG {k : Fin P.n} {b : Bool}
    (h : GNetStep P r w (Sum.inl (Sum.inr (.byzCallG r k b))) μ) :
    μ = PMF.pure (w.gpool k (.input b)) := by
  cases h; rfl

theorem netG_byzCallGLoop {k : Fin P.n} {b : Bool}
    (h : GNetStep P r w (Sum.inl (Sum.inr (.byzCallGLoop r k b))) μ) :
    μ = PMF.pure w := by
  cases h; rfl

theorem netG_byzRetG {k : Fin P.n} {out : GbcaOut}
    (h : GNetStep P r w (Sum.inl (Sum.inr (.byzRetG r k out))) μ) :
    μ = PMF.pure w := by
  cases h; rfl

end NetInversion

/-! ### The labels that carry no transition

The stage rendezvous of the deployed network are not part of the subsystem's
interface: no component of the subsystem offers them, so under full
synchronisation the conjunction over the components is unsatisfiable. -/

theorem sub_gsnd_dead (P : Params) (r r' : ℕ) (j : Fin P.n) (m : GBCA.Msg)
    {q : GBCA.ImplState P.n} {μ : PMF (GBCA.ImplState P.n)}
    (h : (sub P r).step q (Sum.inr (.gsnd r' j m)) μ) : False := by
  rcases (sub_step_iff P r q _ μ).mp h with ⟨hτ, -⟩ | hstep
  · exact absurd hτ (by simp)
  · rw [subPre, System.parallel_step] at hstep
    rcases hstep with ⟨-, _μ₁, _μ₂, -, hn, -⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
    · cases hn
    · exact absurd hτ (by simp)
    · exact absurd hτ (by simp)

theorem sub_gdlv_dead (P : Params) (r r' : ℕ) (i j : Fin P.n) (m : GBCA.Msg)
    {q : GBCA.ImplState P.n} {μ : PMF (GBCA.ImplState P.n)}
    (h : (sub P r).step q (Sum.inr (.gdlv r' i j m)) μ) : False := by
  rcases (sub_step_iff P r q _ μ).mp h with ⟨hτ, -⟩ | hstep
  · exact absurd hτ (by simp)
  · rw [subPre, System.parallel_step] at hstep
    rcases hstep with ⟨-, _μ₁, _μ₂, -, hn, -⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
    · cases hn
    · exact absurd hτ (by simp)
    · exact absurd hτ (by simp)

/-! ### The specification read over the subsystem's interface

The graded agreement specification speaks the shared alphabet `Lab n`; the
subsystem speaks the extended alphabet `NLab n`, in which the three Byzantine
drives and the call loop of round `r` are separate labels. `gPull` is the
projection that identifies them with the specification labels they stand for:
a drive of the call is a call, a drive of the return is a return, and the two
call loops are calls, which the specification takes on its input-enabledness
row. Every other extended label — the deployed network's rendezvous, the coin
drives — is off the specification's interface and idles.

The lifted specification `liftedSpecG` is the specification read back along
`gPull`. It is what the subsystem is replaced by: the drive labels stay visible
at this boundary, and their authorisation is the surrounding network's business
(D11). -/

/-- The projection of the extended alphabet onto the specification's alphabet.
-/
def gPull (n : ℕ) : NLab n → Option (Lab n)
  | Sum.inl l => some l
  | Sum.inr (.gcallLoop r id b) => some (.callG r id b)
  | Sum.inr (.byzCallG r k b) => some (.callG r k b)
  | Sum.inr (.byzCallGLoop r k b) => some (.callG r k b)
  | Sum.inr (.byzRetG r k out) => some (.retG r k out)
  | Sum.inr _ => none

@[simp] theorem gPull_inl {n : ℕ} (l : Lab n) : gPull n (Sum.inl l) = some l := rfl

@[simp] theorem gPull_gcallLoop {n : ℕ} (r : ℕ) (id : Fin n) (b : Bool) :
    gPull n (Sum.inr (.gcallLoop r id b)) = some (.callG r id b) := rfl

@[simp] theorem gPull_byzCallG {n : ℕ} (r : ℕ) (k : Fin n) (b : Bool) :
    gPull n (Sum.inr (.byzCallG r k b)) = some (.callG r k b) := rfl

@[simp] theorem gPull_byzCallGLoop {n : ℕ} (r : ℕ) (k : Fin n) (b : Bool) :
    gPull n (Sum.inr (.byzCallGLoop r k b)) = some (.callG r k b) := rfl

@[simp] theorem gPull_byzRetG {n : ℕ} (r : ℕ) (k : Fin n) (out : GbcaOut) :
    gPull n (Sum.inr (.byzRetG r k out)) = some (.retG r k out) := rfl

@[simp] theorem gPull_gsnd {n : ℕ} (r : ℕ) (j : Fin n) (m : GBCA.Msg) :
    gPull n (Sum.inr (.gsnd r j m)) = none := rfl

@[simp] theorem gPull_gdlv {n : ℕ} (r : ℕ) (i j : Fin n) (m : GBCA.Msg) :
    gPull n (Sum.inr (.gdlv r i j m)) = none := rfl

@[simp] theorem gPull_dsnd {n : ℕ} (j : Fin n) (b : Bool) :
    gPull n (Sum.inr (.dsnd j b)) = none := rfl

@[simp] theorem gPull_ddlv {n : ℕ} (i j : Fin n) (b : Bool) :
    gPull n (Sum.inr (.ddlv i j b)) = none := rfl

@[simp] theorem gPull_retWPub {n : ℕ} (r : ℕ) (id : Fin n) (c b : Bool) :
    gPull n (Sum.inr (.retWPub r id c b)) = none := rfl

@[simp] theorem gPull_byzCallW {n : ℕ} (r : ℕ) (k : Fin n) :
    gPull n (Sum.inr (.byzCallW r k)) = none := rfl

@[simp] theorem gPull_byzRetW {n : ℕ} (r : ℕ) (k : Fin n) (b : Bool) :
    gPull n (Sum.inr (.byzRetW r k b)) = none := rfl

/-- The silent label projects to the silent label. -/
@[simp] theorem gPull_tau (n : ℕ) :
    gPull n (Silent.τ : NLab n) = some (Silent.τ : Lab n) := rfl

/-- Only the silent label projects to the silent label: a drive projects to a
handshake port, and every other extended label idles. -/
theorem gPull_eq_tau {n : ℕ} {l : NLab n} (h : gPull n l = some Lab.tau) :
    l = Sum.inl Lab.tau := by
  cases l with
  | inl l₀ => rw [Option.some.inj h]
  | inr e => cases e <;> simp at h

/-- **The lifted specification**: the round-`r` graded agreement specification
read over the subsystem's interface. -/
noncomputable def liftedSpecG (P : Params) (r : ℕ) :
    System (GBCA.SpecState P.n) (NLab P.n) :=
  (GBCA.specInst P r).mapIdle (gPull P.n)

@[simp] theorem liftedSpecG_init (P : Params) (r : ℕ) :
    (liftedSpecG P r).init = GBCA.SpecState.initial P.n := rfl

/-- The lifted specification is an LTS: the specification is, and reading it
back adds only Dirac self-loops. -/
theorem liftedSpecG_isLTS (P : Params) (r : ℕ) : (liftedSpecG P r).IsLTS :=
  System.mapIdle_isLTS _ (GBCA.specInst_isLTS P r)

/-! ### Weak runs of the lifted specification

A weak run of the specification is read back along a section of `gPull`. The
section sends every label to its own copy on the left, except the one label the
subsystem's step projects from, which is sent to the interface label the
subsystem actually took — this is what turns a specification `callG` run into
the answer to a Byzantine call drive. -/

/-- The section of `gPull` that answers the interface label `l` over the
specification label `l₀`. -/
def gSect {n : ℕ} (l₀ : Lab n) (l : NLab n) : Lab n → NLab n :=
  fun x => if x = l₀ then l else Sum.inl x

theorem gPull_gSect {n : ℕ} {l₀ : Lab n} {l : NLab n} (hl : gPull n l = some l₀)
    (x : Lab n) : gPull n (gSect l₀ l x) = some x := by
  unfold gSect
  by_cases hx : x = l₀
  · rw [if_pos hx, hl, hx]
  · rw [if_neg hx, gPull_inl]

theorem gSect_tau {n : ℕ} {l₀ : Lab n} {l : NLab n} (hl : gPull n l = some l₀)
    (hl₀ : l₀ ≠ (Silent.τ : Lab n)) (x : Lab n) :
    gSect l₀ l x = (Silent.τ : NLab n) ↔ x = (Silent.τ : Lab n) := by
  unfold gSect
  by_cases hx : x = l₀
  · rw [if_pos hx, hx]
    constructor
    · intro hlτ
      have h2 : some l₀ = some (Silent.τ : Lab n) := by rw [← hl, hlτ]; rfl
      exact absurd (Option.some.inj h2) hl₀
    · intro h; exact absurd h hl₀
  · rw [if_neg hx]
    simp [Lab.silent_eq]

/-- A silent weak run of the specification is a silent weak run of the lifted
specification. -/
theorem weakLSilent_liftedSpecG (P : Params) (r : ℕ) {s s' : GBCA.SpecState P.n}
    (h : (GBCA.specInst P r).weakLSilent s s') : (liftedSpecG P r).weakLSilent s s' :=
  System.weakLSilent_mapIdle Sum.inl (fun _ => rfl) (fun _ => by simp) h

/-- A labelled weak run of the specification is a weak run of the lifted
specification at any interface label projecting to the same specification
label. -/
theorem weakLStep_liftedSpecG (P : Params) (r : ℕ) {s s' : GBCA.SpecState P.n}
    {l₀ : Lab P.n} {l : NLab P.n} (hl₀ : l₀ ≠ (Silent.τ : Lab P.n))
    (hl : gPull P.n l = some l₀)
    (h : (GBCA.specInst P r).weakLStep s l₀ s') : (liftedSpecG P r).weakLStep s l s' :=
  System.weakLStep_mapIdle (gSect l₀ l) (gPull_gSect hl) (gSect_tau hl hl₀)
    (by simp [gSect]) h

/-! ### One state, two presentations

The stage records and the fabric are the two factors of `GBCA.ImplState`
(`ABA/GBCAImpl.lean`), so the subsystem and the round instance run on the same
state and every rule of the one is a rule of the other read in the instance's
accessors. What the joint steps deliver, though, is a program function pinned
pointwise — its value at the acting process, and its agreement with the old one
elsewhere — where the instance's rules write with `Function.update`. The lemmas
here close that gap. -/

section Frame

variable {P : Params} {u x : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n} {w : GNetState P.n}

/-- A program function pinned at `j` and unchanged elsewhere is the old one
updated at `j`. -/
theorem nodeFun_update {j : Fin P.n} {q : GBCA.ProcNodeN P.n}
    (hj : x j = q) (hne : ∀ i, i ≠ j → x i = u i) : x = Function.update u j q := by
  funext i
  by_cases hi : i = j
  · subst hi; rw [hj, Function.update_self]
  · rw [hne i hi, Function.update_of_ne hi]

/-- A record write at one program, with the fabric untouched. -/
theorem sub_setProc {j : Fin P.n} {pr : GBCA.ProcState}
    (hj : x j = (u j).setP pr) (hne : ∀ i, i ≠ j → x i = u i) :
    ((x, w) : GBCA.ImplState P.n) = GBCA.ImplState.setProc (u, w) j pr := by
  rw [nodeFun_update hj hne]
  rfl

/-- A record write at one program together with the fabric pooling the message
that write multicasts. -/
theorem sub_setProc_gpool {j : Fin P.n} {pr : GBCA.ProcState} {m : GBCA.Msg}
    (hj : x j = (u j).setP pr) (hne : ∀ i, i ≠ j → x i = u i) :
    ((x, w.gpool j m) : GBCA.ImplState P.n)
      = (GBCA.ImplState.setProc (u, w) j pr).mcast j m := by
  rw [nodeFun_update hj hne]
  rfl

/-- The programs stand still. -/
theorem sub_idle (hall : ∀ i, x i = u i) :
    ((x, w) : GBCA.ImplState P.n) = (u, w) := by
  rw [funext hall]

/-- A delivery: the receiver files the message under its sender's row. -/
theorem sub_deliver {i k : Fin P.n} {m : GBCA.Msg}
    (hi : x i = (u i).deliverTo k m) (hne : ∀ i', i' ≠ i → x i' = u i') :
    ((x, w) : GBCA.ImplState P.n) = GBCA.ImplState.recvMsg (u, w) i k m := by
  rw [nodeFun_update hi hne]
  rfl

/-- A Byzantine injection: the fabric pools a message under a corrupted
sender. -/
theorem sub_gpool {k : Fin P.n} {m : GBCA.Msg} :
    ((u, w.gpool k m) : GBCA.ImplState P.n)
      = GBCA.ImplState.mcast (u, w) k m := rfl

/-- Corruption is the fabric's own write, which is the instance's (D1). -/
theorem sub_corrupt (k : Fin P.n) :
    ((u, w.corrupt P k) : GBCA.ImplState P.n)
      = GBCA.ImplState.corrupt P k (u, w) := rfl

end Frame

/-! ### Reading a subsystem transition backwards

Two inversions of the composition, the counterparts of `subPre_event_step` /
`subPre_lab_step` / `subPre_tau_net`: on a visible label of the internal
alphabet every program and the fabric step together, and on the silent label
only the fabric moves. -/

/-- Diracs are equal only at equal states. -/
theorem pure_inj {α : Type} {a b : α} (h : (PMF.pure a : PMF α) = PMF.pure b) :
    a = b := by
  have ha : a ∈ (PMF.pure b).support := by
    rw [← h]; exact (PMF.mem_support_pure_iff a a).mpr rfl
  exact (PMF.mem_support_pure_iff b a).mp ha

/-- A visible transition of the programs beside the fabric: every program and
the fabric step on the label, and the joint distribution is their Dirac
product. -/
theorem subPre_joint_inv {P : Params} {r : ℕ}
    {u : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n} {w : GNetState P.n} {L : GLab P.n}
    {μ : PMF (GBCA.ImplState P.n)} (hL : L ≠ (Silent.τ : GLab P.n))
    (h : (subPre P r).step (u, w) L μ) :
    ∃ (x : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n) (w' : GNetState P.n),
      μ = PMF.pure (x, w') ∧ (∀ i, GProcStep P r i (u i) L (PMF.pure (x i))) ∧
        GNetStep P r w L (PMF.pure w') := by
  rw [subPre, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hs, hn, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · obtain ⟨x, rfl, hall⟩ := syncG_inv hs
    obtain ⟨w', rfl⟩ := gNetStep_dirac hn
    exact ⟨x, w', prodPMF_pure_pure _ _, hall, hn⟩
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- A silent transition of the programs beside the fabric is a fabric-local
injection: no program has a `τ` row. -/
theorem subPre_tau_inv {P : Params} {r : ℕ}
    {u : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n} {w : GNetState P.n}
    {μ : PMF (GBCA.ImplState P.n)}
    (h : (subPre P r).step (u, w) (Sum.inl (Sum.inl Lab.tau)) μ) :
    ∃ w' : GNetState P.n, μ = PMF.pure (u, w') ∧
      GNetStep P r w (Sum.inl (Sum.inl Lab.tau)) (PMF.pure w') := by
  rw [subPre, System.parallel_step] at h
  rcases h with ⟨hτ, -⟩ | ⟨-, μ₁, hs, rfl⟩ | ⟨-, μ₂, hn, rfl⟩
  · exact absurd rfl hτ
  · exact absurd hs syncG_no_tau
  · obtain ⟨w', rfl⟩ := gNetStep_dirac hn
    exact ⟨w', prodPMF_pure_pure _ _, hn⟩

/-! ### The fabric's rules read off a round-tagged label

The fabric has a row only for its own round: a handshake label of another round
carries no transition of the subsystem at all. These readers therefore return
the round equation together with the fabric's move. -/

section NetRound

variable {P : Params} {r : ℕ} {w : GNetState P.n} {μ : PMF (GNetState P.n)}

theorem netG_callG_round {r' : ℕ} {id : Fin P.n} {b : Bool}
    (h : GNetStep P r w (Sum.inl (Sum.inl (.callG r' id b))) μ) :
    r' = r ∧ μ = PMF.pure (w.gpool id (.input b)) := by
  cases h; exact ⟨rfl, rfl⟩

theorem netG_retG_round {r' : ℕ} {id : Fin P.n} {out : GbcaOut}
    (h : GNetStep P r w (Sum.inl (Sum.inl (.retG r' id out))) μ) :
    r' = r ∧ μ = PMF.pure w := by
  cases h; exact ⟨rfl, rfl⟩

theorem netG_gcallLoop_round {r' : ℕ} {id : Fin P.n} {b : Bool}
    (h : GNetStep P r w (Sum.inl (Sum.inr (.gcallLoop r' id b))) μ) :
    r' = r ∧ μ = PMF.pure w := by
  cases h; exact ⟨rfl, rfl⟩

theorem netG_byzCallG_round {r' : ℕ} {k : Fin P.n} {b : Bool}
    (h : GNetStep P r w (Sum.inl (Sum.inr (.byzCallG r' k b))) μ) :
    r' = r ∧ μ = PMF.pure (w.gpool k (.input b)) := by
  cases h; exact ⟨rfl, rfl⟩

theorem netG_byzCallGLoop_round {r' : ℕ} {k : Fin P.n} {b : Bool}
    (h : GNetStep P r w (Sum.inl (Sum.inr (.byzCallGLoop r' k b))) μ) :
    r' = r ∧ μ = PMF.pure w := by
  cases h; exact ⟨rfl, rfl⟩

theorem netG_byzRetG_round {r' : ℕ} {k : Fin P.n} {out : GbcaOut}
    (h : GNetStep P r w (Sum.inl (Sum.inr (.byzRetG r' k out))) μ) :
    r' = r ∧ μ = PMF.pure w := by
  cases h; exact ⟨rfl, rfl⟩

/-! The labels the fabric does not offer at all: the ABA API, the coin ports,
corruption, and the deployed network's own rendezvous. -/

theorem netG_callABA_dead {id : Fin P.n} {b : Bool}
    (h : GNetStep P r w (Sum.inl (Sum.inl (.callABA id b))) μ) : False := by cases h

theorem netG_retABA_dead {id : Fin P.n} {b : Bool}
    (h : GNetStep P r w (Sum.inl (Sum.inl (.retABA id b))) μ) : False := by cases h

theorem netG_callW_dead {r' : ℕ} {id : Fin P.n}
    (h : GNetStep P r w (Sum.inl (Sum.inl (.callW r' id))) μ) : False := by cases h

theorem netG_retW_dead {r' : ℕ} {id : Fin P.n} {b : Bool}
    (h : GNetStep P r w (Sum.inl (Sum.inl (.retW r' id b))) μ) : False := by cases h

theorem netG_fail_dead {k : Fin P.n}
    (h : GNetStep P r w (Sum.inl (Sum.inl (.fail k))) μ) : False := by cases h

theorem netG_gsnd_dead {r' : ℕ} {j : Fin P.n} {m : GBCA.Msg}
    (h : GNetStep P r w (Sum.inl (Sum.inr (.gsnd r' j m))) μ) : False := by cases h

theorem netG_gdlv_dead {r' : ℕ} {i j : Fin P.n} {m : GBCA.Msg}
    (h : GNetStep P r w (Sum.inl (Sum.inr (.gdlv r' i j m))) μ) : False := by cases h

theorem netG_dsnd_dead {j : Fin P.n} {b : Bool}
    (h : GNetStep P r w (Sum.inl (Sum.inr (.dsnd j b))) μ) : False := by cases h

theorem netG_ddlv_dead {i j : Fin P.n} {b : Bool}
    (h : GNetStep P r w (Sum.inl (Sum.inr (.ddlv i j b))) μ) : False := by cases h

theorem netG_retWPub_dead {r' : ℕ} {id : Fin P.n} {c b : Bool}
    (h : GNetStep P r w (Sum.inl (Sum.inr (.retWPub r' id c b))) μ) : False := by cases h

theorem netG_byzCallW_dead {r' : ℕ} {k : Fin P.n}
    (h : GNetStep P r w (Sum.inl (Sum.inr (.byzCallW r' k))) μ) : False := by cases h

theorem netG_byzRetW_dead {r' : ℕ} {k : Fin P.n} {b : Bool}
    (h : GNetStep P r w (Sum.inl (Sum.inr (.byzRetW r' k b))) μ) : False := by cases h

end NetRound

/-! ### The subsystem projects onto the round instance

Every rule of the subsystem is one rule of the round-`r` instance at the same
state, and the correspondence is strong — one step answers one step, at the
specification label the interface label projects to, with no stuttering
anywhere:

| subsystem | round instance |
| --- | --- |
| `callG` (caller writes, fabric pools) | `ImplStep.call` |
| `gcallLoop`, `byzCallGLoop` | `ImplStep.callLoop` |
| `byzCallG` (D11) | `ImplStep.call` |
| `retG` / `byzRetG`, by grade | `ImplStep.retA` / `retB` / `retC` |
| hidden `snd` rendezvous, by level | the eight protocol `τ` rules |
| hidden `dlv` rendezvous | `ImplStep.deliver` |
| fabric-local injection | `ImplStep.byz` |

The two hidden rendezvous and the fabric's injection are silent on both sides,
and `gPull` takes `τ` to `τ`. -/

/-- **The strong projection lemma.** -/
theorem sub_projects (P : Params) (r : ℕ) :
    ∀ (σ : GBCA.ImplState P.n) (l : NLab P.n) (μ : PMF (GBCA.ImplState P.n)),
      (sub P r).step σ l μ →
      ∃ l₀, gPull P.n l = some l₀ ∧
        (GBCA.implInst P r).step σ l₀ μ := by
  rintro ⟨u, w⟩ l μ hstep
  rcases (sub_step_iff P r (u, w) l μ).mp hstep with ⟨rfl, e, hev⟩ | hlab
  · -- a hidden rendezvous: an internal step of the instance
    obtain ⟨x, w', rfl, hall, hn⟩ := subPre_joint_inv (by simp) hev
    refine ⟨Lab.tau, rfl, ?_⟩
    cases e with
    | snd j m =>
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => pure_inj (stepG_snd_foreign (Ne.symm hi) (hall i))
      have hw : w' = w.gpool j m := pure_inj (netG_snd hn)
      subst hw
      cases m with
      | input b =>
        obtain ⟨hin, hcnt, hsend, hx⟩ := stepG_snd_input_own (hall j)
        rw [sub_setProc_gpool (pure_inj hx) hfor]
        exact GBCA.ImplStep.relay _ j b hin hcnt hsend
      | echo b =>
        obtain ⟨hin, hcnt, hsend, hx⟩ := stepG_snd_echo_own (hall j)
        rw [sub_setProc_gpool (pure_inj hx) hfor]
        exact GBCA.ImplStep.echo _ j b hin hcnt hsend
      | vote v =>
        cases v with
        | some b =>
          obtain ⟨hin, hcnt, hsend, hx⟩ := stepG_snd_voteBit_own (hall j)
          rw [sub_setProc_gpool (pure_inj hx) hfor]
          exact GBCA.ImplStep.voteBit _ j b hin hcnt hsend
        | none =>
          obtain ⟨hin, hcnt, hval, hsend, hx⟩ := stepG_snd_voteBot_own (hall j)
          rw [sub_setProc_gpool (pure_inj hx) hfor]
          exact GBCA.ImplStep.voteBot _ j hin hcnt hval hsend
      | bind v =>
        cases v with
        | some b =>
          obtain ⟨hin, hcnt, hsend, hx⟩ := stepG_snd_bindBit_own (hall j)
          rw [sub_setProc_gpool (pure_inj hx) hfor]
          exact GBCA.ImplStep.bindBit _ j b hin hcnt hsend
        | none =>
          obtain ⟨hin, hcnt, hval, hsend, hx⟩ := stepG_snd_bindBot_own (hall j)
          rw [sub_setProc_gpool (pure_inj hx) hfor]
          exact GBCA.ImplStep.bindBot _ j hin hcnt hval hsend
      | «seal» v =>
        cases v with
        | some b =>
          obtain ⟨hin, hcnt, hsend, hx⟩ := stepG_snd_sealBit_own (hall j)
          rw [sub_setProc_gpool (pure_inj hx) hfor]
          exact GBCA.ImplStep.sealBit _ j b hin hcnt hsend
        | none =>
          obtain ⟨hin, hcnt, hval, hsend, hx⟩ := stepG_snd_sealBot_own (hall j)
          rw [sub_setProc_gpool (pure_inj hx) hfor]
          exact GBCA.ImplStep.sealBot _ j hin hcnt hval hsend
    | dlv i j m =>
      obtain ⟨hmem, hw⟩ := netG_dlv hn
      have hw' : w' = w := pure_inj hw
      subst hw'
      have hfor : ∀ i', i' ≠ i → x i' = u i' :=
        fun i' hi' => pure_inj (stepG_dlv_foreign (Ne.symm hi') (hall i'))
      rw [sub_deliver (pure_inj (stepG_dlv_own (hall i))) hfor]
      exact GBCA.ImplStep.deliver _ i j m hmem
  · by_cases hlτ : l = Sum.inl Lab.tau
    · -- the fabric's own injection
      subst hlτ
      obtain ⟨w', rfl, hn⟩ := subPre_tau_inv hlab
      obtain ⟨k, m, hF, hw⟩ := netG_tau hn
      have hw' : w' = w.gpool k m := pure_inj hw
      subst hw'
      refine ⟨Lab.tau, rfl, ?_⟩
      rw [sub_gpool]
      exact GBCA.ImplStep.byz _ k m hF
    · obtain ⟨x, w', rfl, hall, hn⟩ := subPre_joint_inv (by simpa using hlτ) hlab
      cases l with
      | inl l₀ =>
        cases l₀ with
        | tau => exact absurd rfl hlτ
        | callABA id b => exact (netG_callABA_dead hn).elim
        | retABA id b => exact (netG_retABA_dead hn).elim
        | callW r' id => exact (netG_callW_dead hn).elim
        | retW r' id b => exact (netG_retW_dead hn).elim
        | fail k => exact (netG_fail_dead hn).elim
        | callG r' id b =>
          obtain ⟨rfl, hw⟩ := netG_callG_round hn
          have hw' : w' = w.gpool id (.input b) := pure_inj hw
          subst hw'
          obtain ⟨hin, hx⟩ := stepG_callG_own (hall id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => pure_inj (stepG_callG_foreign (Ne.symm hi) (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [sub_setProc_gpool (pure_inj hx) hfor]
          exact GBCA.ImplStep.call _ id b hin
        | retG r' id out =>
          obtain ⟨rfl, hw⟩ := netG_retG_round hn
          have hw' : w' = w := pure_inj hw
          subst hw'
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => pure_inj (stepG_retG_foreign (Ne.symm hi) (hall i))
          refine ⟨_, rfl, ?_⟩
          cases out with
          | A v =>
            obtain ⟨hcnt, hret, hx⟩ := stepG_retG_A_own (hall id)
            rw [sub_setProc (pure_inj hx) hfor]
            exact GBCA.ImplStep.retA _ id v hcnt hret
          | B v =>
            obtain ⟨hcnt, honce, hbind, hval, hret, hx⟩ := stepG_retG_B_own (hall id)
            rw [sub_setProc (pure_inj hx) hfor]
            exact GBCA.ImplStep.retB _ id v hcnt honce hbind hval hret
          | C =>
            obtain ⟨hcnt, hval, hret, hx⟩ := stepG_retG_C_own (hall id)
            rw [sub_setProc (pure_inj hx) hfor]
            exact GBCA.ImplStep.retC _ id hcnt hval hret
      | inr ev =>
        cases ev with
        | gsnd r' j m => exact (netG_gsnd_dead hn).elim
        | gdlv r' i j m => exact (netG_gdlv_dead hn).elim
        | dsnd j b => exact (netG_dsnd_dead hn).elim
        | ddlv i j b => exact (netG_ddlv_dead hn).elim
        | retWPub r' id c b => exact (netG_retWPub_dead hn).elim
        | byzCallW r' k => exact (netG_byzCallW_dead hn).elim
        | byzRetW r' k b => exact (netG_byzRetW_dead hn).elim
        | gcallLoop r' id b =>
          obtain ⟨rfl, hw⟩ := netG_gcallLoop_round hn
          have hw' : w' = w := pure_inj hw
          subst hw'
          have hidle : ∀ i, x i = u i := fun i => pure_inj (stepG_gcallLoop (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [sub_idle hidle]
          exact GBCA.ImplStep.callLoop _ id b
        | byzCallG r' k b =>
          obtain ⟨rfl, hw⟩ := netG_byzCallG_round hn
          have hw' : w' = w.gpool k (.input b) := pure_inj hw
          subst hw'
          obtain ⟨hin, hx⟩ := stepG_byzCallG_own (hall k)
          have hfor : ∀ i, i ≠ k → x i = u i :=
            fun i hi => pure_inj (stepG_byzCallG_foreign (Ne.symm hi) (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [sub_setProc_gpool (pure_inj hx) hfor]
          exact GBCA.ImplStep.call _ k b hin
        | byzCallGLoop r' k b =>
          obtain ⟨rfl, hw⟩ := netG_byzCallGLoop_round hn
          have hw' : w' = w := pure_inj hw
          subst hw'
          have hidle : ∀ i, x i = u i :=
            fun i => pure_inj (stepG_byzCallGLoop (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [sub_idle hidle]
          exact GBCA.ImplStep.callLoop _ k b
        | byzRetG r' k out =>
          obtain ⟨rfl, hw⟩ := netG_byzRetG_round hn
          have hw' : w' = w := pure_inj hw
          subst hw'
          have hfor : ∀ i, i ≠ k → x i = u i :=
            fun i hi => pure_inj (stepG_byzRetG_foreign (Ne.symm hi) (hall i))
          refine ⟨_, rfl, ?_⟩
          cases out with
          | A v =>
            obtain ⟨hcnt, hret, hx⟩ := stepG_byzRetG_A_own (hall k)
            rw [sub_setProc (pure_inj hx) hfor]
            exact GBCA.ImplStep.retA _ k v hcnt hret
          | B v =>
            obtain ⟨hcnt, honce, hbind, hval, hret, hx⟩ := stepG_byzRetG_B_own (hall k)
            rw [sub_setProc (pure_inj hx) hfor]
            exact GBCA.ImplStep.retB _ k v hcnt honce hbind hval hret
          | C =>
            obtain ⟨hcnt, hval, hret, hx⟩ := stepG_byzRetG_C_own (hall k)
            rw [sub_setProc (pure_inj hx) hfor]
            exact GBCA.ImplStep.retC _ k hcnt hval hret

/-! ### The round subsystem is refined by the graded agreement specification

The subsystem's answer to a step is the round instance's answer, read through
the per-instance refinement (`GBCA.implRefines`, `ABA/GBCASim.lean`): the first
leg is strong and functional, so nothing of that refinement is reproved here. The specification's
weak answer is finally lifted to the subsystem's interface along a section of
`gPull` — which is where a Byzantine drive is answered by the specification's
own call or return row (D11). -/

/-- **The simulation relation of the round subsystem**: the instance relation,
which the shared state lets it be verbatim. -/
def Rsub (P : Params) (r : ℕ) (σ : GBCA.ImplState P.n) (s : GBCA.SpecState P.n) : Prop :=
  GBCA.instRel P r σ s

/-- **The per-round subsystem simulation**: the round-`r` subsystem is forward
simulated by the round-`r` graded agreement specification, read over the
subsystem's interface. -/
theorem subSim (P : Params) (r : ℕ) :
    ForwardSimulation (sub P r) (liftedSpecG P r) (Rsub P r) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  obtain ⟨l₀, hpull, himpl⟩ := sub_projects P r q₁ l μ hstep
  obtain ⟨s', hdis, hrel⟩ := (GBCA.implRefines P r).step q₁ q₂ hR l₀ μ himpl q₁' hq₁'
  refine ⟨s', ?_, hrel⟩
  rcases hdis with ⟨hτ, hweak⟩ | ⟨hτ, hweak⟩
  · exact Or.inl ⟨gPull_eq_tau (by rw [hpull, hτ]; rfl),
      weakLSilent_liftedSpecG P r hweak⟩
  · refine Or.inr ⟨?_, weakLStep_liftedSpecG P r hτ hpull hweak⟩
    intro hl
    refine hτ ?_
    have h2 : gPull P.n (Silent.τ : NLab P.n) = some l₀ := by rw [← hl]; exact hpull
    rw [gPull_tau] at h2
    exact (Option.some.inj h2).symm

/-! ### What the family lift will need

The two side conditions of `ForwardSimulation.family` for the round-indexed
family: the relation holds at the initial states, and it survives the broadcast
corruption. Both are the round instance's own facts, which the shared state
lets stand verbatim. -/

/-- The broadcast corruption act on a specification state, over the extended
alphabet: `GBCA.failAct` taken on the extended `fail` label. -/
def gActSpec (P : Params) : NLab P.n → GBCA.SpecState P.n → GBCA.SpecState P.n
  | Sum.inl (.fail k), s => s.corrupt P k
  | _, s => s

/-- The initial states of the subsystem and of its specification are
related. -/
theorem subSim_init (P : Params) (r : ℕ) :
    Rsub P r (sub P r).init (GBCA.specInst P r).init :=
  GBCA.instRel_init P r

/-- **Broadcast compatibility**: corruption preserves the subsystem relation.
The fabric's corrupted set is the instance's, so the two guards
`k ∉ F ∧ |F| < f` agree and the instance-level statement
(`GBCA.instRel_corrupt`) applies verbatim (D1). -/
theorem subSim_failAct (P : Params) :
    ∀ l : NLab P.n, isFailN l → ∀ (r : ℕ) (σ : GBCA.ImplState P.n)
      (s : GBCA.SpecState P.n), Rsub P r σ s →
      Rsub P r (gAct P l σ) (gActSpec P l s) := by
  rintro l hl r ⟨u, w⟩ s hR
  cases l with
  | inr e => cases e <;> exact hl.elim
  | inl l₀ =>
    cases l₀ with
    | fail k =>
      have hs : gAct P (Sum.inl (Lab.fail k)) (u, w)
          = GBCA.ImplState.corrupt P k (u, w) := sub_corrupt k
      have hc := GBCA.instRel_corrupt P r k hR
      rw [← hs] at hc
      exact hc
    | tau => exact hl.elim
    | callABA id b => exact hl.elim
    | retABA id b => exact hl.elim
    | callG r' id b => exact hl.elim
    | retG r' id out => exact hl.elim
    | callW r' id => exact hl.elim
    | retW r' id b => exact hl.elim

/-! ### Mechanical axiom firewall -/

/-- info: 'PLTS.ABA.GSub.subSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subSim

/-- info: 'PLTS.ABA.GSub.sub_projects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sub_projects

end GSub

/-! ## The routing table, evaluated

`gOwns` and `isFailN` are decided by a `rfl` at every label of the extended
alphabet. The layered presentation composes `gbcaSide` with boxes that speak
that alphabet, so it discharges the routing side conditions by `simp`; the
table below is what `simp` uses, and it lives under `PLTS.ABA.Layer` with the
rest of the layer cut's vocabulary. -/

namespace Layer

open Net

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

end Layer

end ABA
end PLTS
