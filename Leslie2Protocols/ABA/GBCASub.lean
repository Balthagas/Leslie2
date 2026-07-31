/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.FlatNetwork
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
* **D18 (the six-level ladder).** The send rows are the six levels
  `INPUT / ECHO / VOTE / BIND / SEAL` and the three graded returns of the
  cited algorithm, not the four-round compression.

## The interface

Every row mirrors the stage-visible half of one rule of the monolithic
round-`r` instance (`ABA/GBCAImpl.lean`), split between the program that owns
the record and the fabric that owns the pool. What the monolithic rule writes
on the core slice — the round loop's phase, estimate and grade — appears
nowhere here: that slice is a different component of the deployed system.
-/

namespace PLTS

/-! ### Determinacy of a binary composition

Binary parallel composition preserves the LTS property, the companion of
`System.syncProduct_isLTS`: a synchronised step is a product of two Diracs and
an interleaved one holds the other component's state. -/

/-- **A binary composition of LTS components is an LTS.** -/
theorem System.parallel_isLTS {S₁ S₂ L : Type} [Silent L] {sys₁ : System S₁ L}
    {sys₂ : System S₂ L} (h₁ : sys₁.IsLTS) (h₂ : sys₂.IsLTS) :
    (sys₁.parallel sys₂).IsLTS := by
  rintro ⟨a, b⟩ l μ hstep
  rw [System.parallel_step] at hstep
  rcases hstep with ⟨-, μ₁, μ₂, ha, hb, rfl⟩ | ⟨-, μ₁, ha, rfl⟩ | ⟨-, μ₂, hb, rfl⟩
  · obtain ⟨a', rfl⟩ := h₁ _ _ _ ha
    obtain ⟨b', rfl⟩ := h₂ _ _ _ hb
    exact ⟨(a', b'), ABA.Net.prodPMF_pure_pure a' b'⟩
  · obtain ⟨a', rfl⟩ := h₁ _ _ _ ha
    exact ⟨(a', b), ABA.Net.prodPMF_pure_pure a' b⟩
  · obtain ⟨b', rfl⟩ := h₂ _ _ _ hb
    exact ⟨(a, b'), ABA.Net.prodPMF_pure_pure a b'⟩

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
is where a corrupted sender's injections enter (D5). -/

/-- The state of the round's message fabric: the per-sender pools and the
corrupted set. -/
structure GNetState (n : ℕ) : Type where
  /-- `pool j` — the messages process `j` has multicast in this round (D5). -/
  pool : Fin n → Finset GBCA.Msg
  /-- The corrupted set. -/
  F : Finset (Fin n)
  deriving DecidableEq

namespace GNetState

variable {n : ℕ}

/-- The initial fabric: nothing multicast, nobody corrupted. -/
def initial (n : ℕ) : GNetState n where
  pool := fun _ => ∅
  F := ∅

/-- Pool `m` under sender `j` (D5). -/
def gpool (w : GNetState n) (j : Fin n) (m : GBCA.Msg) : GNetState n :=
  { w with pool := Function.update w.pool j (insert m (w.pool j)) }

/-- Corruption (deviation D1): total, Dirac, budget-guarded. It is not a row
of any rule table — the family applies it to every round's fabric at once. -/
def corrupt (P : Params) (id : Fin P.n) (w : GNetState P.n) : GNetState P.n :=
  if id ∉ w.F ∧ w.F.card < P.f then { w with F := insert id w.F } else w

@[simp] theorem gpool_F (w : GNetState n) (j : Fin n) (m : GBCA.Msg) :
    (w.gpool j m).F = w.F := rfl

@[simp] theorem corrupt_pool {P : Params} (w : GNetState P.n) (id : Fin P.n) :
    (w.corrupt P id).pool = w.pool := by
  unfold corrupt; split <;> rfl

/-- Membership in a pool after a multicast. -/
theorem mem_gpool {w : GNetState n} {j : Fin n} {m : GBCA.Msg} {k : Fin n}
    {m' : GBCA.Msg} :
    m' ∈ (w.gpool j m).pool k ↔ (k = j ∧ m' = m) ∨ m' ∈ w.pool k := by
  change m' ∈ Function.update w.pool j (insert m (w.pool j)) k ↔ _
  by_cases hk : k = j
  · subst hk
    rw [Function.update_self, Finset.mem_insert]
    simp
  · rw [Function.update_of_ne hk]
    simp [hk]

end GNetState

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

/-- The state of one round's subsystem: the `n` stage records and the round's
message fabric. -/
abbrev GSubState (n : ℕ) : Type := (∀ _ : Fin n, GBCA.ProcNodeN n) × GNetState n

/-- The programs beside the fabric, over the subsystem-internal alphabet. -/
noncomputable def subPre (P : Params) (r : ℕ) :
    System (GSubState P.n) (GLab P.n) :=
  (System.syncProduct (gbcaProc P r)).parallel (gNet P r)

/-- **The round-`r` subsystem**: the programs beside the fabric, the two
rendezvous hidden, the result read back over the shared extended alphabet. Its
interface is the round's ports — `callG r`, `retG r`, `gcallLoop r` and the
three graded-agreement drives of round `r`. -/
noncomputable def sub (P : Params) (r : ℕ) :
    System (GSubState P.n) (NLab P.n) :=
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
def gAct (P : Params) : NLab P.n → GSubState P.n → GSubState P.n
  | Sum.inl (.fail k), (u, w) => (u, w.corrupt P k)
  | _, s => s

/-- **The graded-agreement side of the deployed protocol**: the ℕ-indexed
family of round subsystems. A round-tagged label moves its round alone, `τ`
moves one round, and `fail` is the broadcast that keeps every round's copy of
the corrupted set in lockstep. -/
noncomputable def gbcaSide (P : Params) :
    System (ℕ → GSubState P.n) (NLab P.n) :=
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
theorem sub_step_iff (P : Params) (r : ℕ) (q : GSubState P.n) (l : NLab P.n)
    (μ : PMF (GSubState P.n)) :
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
    (ABA.Net.prodPMF_pure_pure _ _).symm⟩

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
    (ABA.Net.prodPMF_pure_pure _ _).symm⟩

/-- Build a silent transition of the programs and the fabric from a
fabric-local one. -/
theorem subPre_tau_net (P : Params) (r : ℕ)
    {u : ∀ _ : Fin P.n, GBCA.ProcNodeN P.n} {w w' : GNetState P.n}
    (hn : GNetStep P r w (Sum.inl (Sum.inl .tau)) (PMF.pure w')) :
    (subPre P r).step (u, w) (Sum.inl (Sum.inl .tau)) (PMF.pure (u, w')) := by
  rw [subPre, System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure w', hn, (ABA.Net.prodPMF_pure_pure _ _).symm⟩)

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
    {q : GSubState P.n} {μ : PMF (GSubState P.n)}
    (h : (sub P r).step q (Sum.inr (.gsnd r' j m)) μ) : False := by
  rcases (sub_step_iff P r q _ μ).mp h with ⟨hτ, -⟩ | hstep
  · exact absurd hτ (by simp)
  · rw [subPre, System.parallel_step] at hstep
    rcases hstep with ⟨-, _μ₁, _μ₂, -, hn, -⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
    · cases hn
    · exact absurd hτ (by simp)
    · exact absurd hτ (by simp)

theorem sub_gdlv_dead (P : Params) (r r' : ℕ) (i j : Fin P.n) (m : GBCA.Msg)
    {q : GSubState P.n} {μ : PMF (GSubState P.n)}
    (h : (sub P r).step q (Sum.inr (.gdlv r' i j m)) μ) : False := by
  rcases (sub_step_iff P r q _ μ).mp h with ⟨hτ, -⟩ | hstep
  · exact absurd hτ (by simp)
  · rw [subPre, System.parallel_step] at hstep
    rcases hstep with ⟨-, _μ₁, _μ₂, -, hn, -⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
    · cases hn
    · exact absurd hτ (by simp)
    · exact absurd hτ (by simp)

end GSub
end ABA
end PLTS
