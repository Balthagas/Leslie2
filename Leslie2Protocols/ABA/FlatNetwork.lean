/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Main
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SyncProduct

/-!
# ABA as corruption-blind programs beside a network adversary

The deployed reading of the protocol: `n` automata, each running one process's
code and nothing else, beside two boxes that are not processes — the network
adversary and the coin oracle.

A process node is exactly the data the program of that process may read: the
round-loop record of the coordinator, one graded-agreement stage record per
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
composition, so the composite `netGroup` speaks exactly `Lab n`.

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
`netGroup P`; hiding the sub-protocol API gives `netFlat P`.

## The result

The deflation `deflNet` assembles a deployed state into a monolithic one, and
it both preserves (`netForward`) and reflects (`netConverse`) transitions.
The two soundness inclusions therefore close an equality of achievable trace
distributions, `netFlat_atd`: the deployed reading adds no behaviour and
loses none. Safety of the deployed reading (`netFlat_safe`) and its trace
conservativity (`netFlat_traces`) follow from the forward half alone, with no
side condition.
-/

namespace PLTS

/-! ### Pulling a system back along a partial label map -/

/-- Read a system over `L` as a system over `L'`: a label `l'` with
`φ l' = some l` delegates to the `l`-transitions, and a label outside the
image of `φ` leaves the system idle. -/
def System.mapIdle {S L L' : Type} (φ : L' → Option L) (sys : System S L) :
    System S L' where
  init := sys.init
  step s l' μ :=
    match φ l' with
    | some l => sys.step s l μ
    | none => μ = PMF.pure s

@[simp] theorem System.mapIdle_init {S L L' : Type} (φ : L' → Option L)
    (sys : System S L) : (sys.mapIdle φ).init = sys.init := rfl

theorem System.mapIdle_step {S L L' : Type} (φ : L' → Option L) (sys : System S L)
    (s : S) (l' : L') (μ : PMF S) :
    (sys.mapIdle φ).step s l' μ ↔
      (∃ l, φ l' = some l ∧ sys.step s l μ) ∨ (φ l' = none ∧ μ = PMF.pure s) := by
  change (match φ l' with
        | some l => sys.step s l μ
        | none => μ = PMF.pure s) ↔ _
  cases hφ : φ l' with
  | none => simp
  | some l => simp

/-- Delegated labels read off the underlying system. -/
theorem System.mapIdle_step_some {S L L' : Type} {φ : L' → Option L}
    {sys : System S L} {s : S} {l' : L'} {l : L} (hφ : φ l' = some l)
    (μ : PMF S) : (sys.mapIdle φ).step s l' μ ↔ sys.step s l μ := by
  rw [System.mapIdle_step]
  simp [hφ]

/-- Unmapped labels are idle self-loops. -/
theorem System.mapIdle_step_none {S L L' : Type} {φ : L' → Option L}
    {sys : System S L} {s : S} {l' : L'} (hφ : φ l' = none) (μ : PMF S) :
    (sys.mapIdle φ).step s l' μ ↔ μ = PMF.pure s := by
  rw [System.mapIdle_step]
  simp [hφ]

namespace ABA

/-! ### The corruption-blind records -/

namespace GBCA

/-- The stage record of one process: its own local state and the messages
delivered to it, indexed by sender. There is no record of what it has sent —
the sender's pool lives in the network. -/
structure ProcNodeN (n : ℕ) : Type where
  /-- The process's local record — the monolithic `proc j`. -/
  proc : ProcState
  /-- `inbox k` — the messages from sender `k` delivered here. -/
  inbox : Fin n → Finset Msg
  deriving DecidableEq

namespace ProcNodeN

variable {n : ℕ}

/-- The initial stage record: nothing received, nothing done. -/
def initial (n : ℕ) : ProcNodeN n where
  proc := ProcState.initial
  inbox := fun _ => ∅

/-- The number of distinct senders from which this process has received `m`. -/
def recvCount (p : ProcNodeN n) (m : Msg) : ℕ :=
  (Finset.univ.filter (fun k => m ∈ p.inbox k)).card

/-- The number of distinct senders of some received `ECHO`. -/
def echoCount (p : ProcNodeN n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ b, Msg.echo b ∈ p.inbox k)).card

/-- The number of distinct senders of some received `VOTE`. -/
def voteCount (p : ProcNodeN n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ v, Msg.vote v ∈ p.inbox k)).card

/-- The number of distinct senders of some received `BIND`. -/
def bindCount (p : ProcNodeN n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ v, Msg.bind v ∈ p.inbox k)).card

/-- The number of distinct senders of some received `SEAL`. -/
def sealCount (p : ProcNodeN n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ v, Msg.seal v ∈ p.inbox k)).card

/-- Both bits are backed by an `n − f` `INPUT` quorum among the delivered
messages. -/
def bothValid (P : Params) (p : ProcNodeN P.n) : Prop :=
  P.n - P.f ≤ p.recvCount (.input true) ∧ P.n - P.f ≤ p.recvCount (.input false)

/-- Overwrite the local record. -/
def setP (p : ProcNodeN n) (pr : ProcState) : ProcNodeN n := { p with proc := pr }

/-- File `m` under the inbox row of sender `k`. -/
def deliverTo (p : ProcNodeN n) (k : Fin n) (m : Msg) : ProcNodeN n :=
  { p with inbox := Function.update p.inbox k (insert m (p.inbox k)) }

end ProcNodeN

end GBCA

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
publication that the monolithic round advance fuses in (D10) is the network's
half of the joint step. -/
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

end Net


namespace Net

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

end Net


namespace Net

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
noncomputable def netPre (P : Params) :
    System ((∀ _ : Fin P.n, ABANodeN P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n)))
      (NLab P.n) :=
  (System.syncProduct (ABAProcN P)).parallel ((netAdv P).parallel (wccLift P))

/-- **The deployed group**: the rendezvous alphabet hidden, the result read
back over `Lab n`. -/
noncomputable def netGroup (P : Params) :
    System ((∀ _ : Fin P.n, ABANodeN P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n)))
      (Lab P.n) :=
  ((netPre P).abstract (netEvtLabels P.n)).relabel

/-- **The deployed system**: the group with the sub-protocol API hidden. -/
noncomputable def netFlat (P : Params) :
    System ((∀ _ : Fin P.n, ABANodeN P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n)))
      (Lab P.n) :=
  (netGroup P).abstract (Lab.hiddenAPI P.n)

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

end Net


namespace Net

/-! ### Reading and building composite transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ parallel ∘ syncProduct`; the
lemmas below unfold it once and for all, in both directions. -/

theorem prodPMF_pure_pure {α β : Type} (a : α) (b : β) :
    prodPMF (PMF.pure a) (PMF.pure b) = PMF.pure (a, b) := by
  rw [prodPMF_pure_left, PMF.pure_map]

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
theorem netPre_event_step (P : Params) {u x : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o o' : ℕ → WCC.SpecState P.n} (e : NetEvt P.n)
    (hall : ∀ i, ABAProcStepN P i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : NetStep P w (Sum.inr e) (PMF.pure w'))
    (ho : (wccLift P).step o (Sum.inr e) (PMF.pure o')) :
    (netPre P).step (u, w, o) (Sum.inr e) (PMF.pure (x, w', o')) := by
  rw [netPre, System.parallel_step]
  refine Or.inl ⟨by simp, PMF.pure x, PMF.pure (w', o'),
    syncN_pure (by simp) hall, ?_, (prodPMF_pure_pure _ _).symm⟩
  rw [System.parallel_step]
  exact Or.inl ⟨by simp, PMF.pure w', PMF.pure o', hn, ho,
    (prodPMF_pure_pure _ _).symm⟩

/-- Build a joint transition of the three factors on a visible shared label. -/
theorem netPre_lab_step (P : Params) {u x : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} {l : Lab P.n} (hl : l ≠ Lab.tau)
    (hall : ∀ i, ABAProcStepN P i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hn : NetStep P w (Sum.inl l) (PMF.pure w'))
    (ho : (WCC.specFamily P).step o l ω) :
    (netPre P).step (u, w, o) (Sum.inl l)
      (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω)) := by
  have hne : (Sum.inl l : NLab P.n) ≠ Silent.τ := by simpa using hl
  rw [netPre, System.parallel_step]
  refine Or.inl ⟨hne, PMF.pure x, prodPMF (PMF.pure w') ω,
    syncN_pure hne hall, ?_, rfl⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hne, PMF.pure w', ω, hn,
    (System.mapIdle_step_some (by simp) ω).mpr ho, rfl⟩

/-- Build a silent transition of the three factors from a network-local one. -/
theorem netPre_tau_net (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    (hn : NetStep P w (Sum.inl .tau) (PMF.pure w')) :
    (netPre P).step (u, w, o) (Sum.inl .tau) (PMF.pure (u, w', o)) := by
  rw [netPre, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure w') (PMF.pure o), ?_, ?_⟩)
  · rw [System.parallel_step]
    exact Or.inr (Or.inl ⟨rfl, PMF.pure w', hn, rfl⟩)
  · rw [prodPMF_pure_pure, prodPMF_pure_pure]

/-- Build a silent transition of the three factors from an oracle-local one
(the coin resolution — the one transition of the composite that is not
Dirac). -/
theorem netPre_tau_wcc (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)}
    (ho : (WCC.specFamily P).step o Lab.tau ω) :
    (netPre P).step (u, w, o) (Sum.inl .tau)
      (prodPMF (PMF.pure u) (prodPMF (PMF.pure w) ω)) := by
  rw [netPre, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure w) ω, ?_, rfl⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, ω,
    (System.mapIdle_step_some (by simp) ω).mpr ho, rfl⟩)

/-- The composite step relation of the deployed group, unfolded to the hidden
rendezvous case and the shared-label case. -/
theorem netGroup_step_iff (P : Params)
    (q : (∀ _ : Fin P.n, ABANodeN P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n)))
    (l : Lab P.n)
    (μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))) :
    (netGroup P).step q l μ ↔
      (l = .tau ∧ ∃ e : NetEvt P.n, (netPre P).step q (Sum.inr e) μ) ∨
      (netPre P).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_netEvtLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_netEvtLabels l, hstep⟩

/-- The deployed system's step relation: a sub-protocol API label seen as `τ`,
or a label that survives the hiding. -/
theorem netFlat_step_iff (P : Params)
    (q : (∀ _ : Fin P.n, ABANodeN P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n)))
    (l : Lab P.n)
    (μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))) :
    (netFlat P).step q l μ ↔
      (l = .tau ∧ ∃ l' ∈ Lab.hiddenAPI P.n, (netGroup P).step q l' μ) ∨
      (l ∉ Lab.hiddenAPI P.n ∧ (netGroup P).step q l μ) :=
  System.abstract_step _ _ _ _ _

/-- A hidden rendezvous is a silent transition of the deployed group. -/
theorem netGroup_event_step (P : Params) {u x : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o o' : ℕ → WCC.SpecState P.n} (e : NetEvt P.n)
    (hall : ∀ i, ABAProcStepN P i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : NetStep P w (Sum.inr e) (PMF.pure w'))
    (ho : (wccLift P).step o (Sum.inr e) (PMF.pure o')) :
    (netGroup P).step (u, w, o) Lab.tau (PMF.pure (x, w', o')) :=
  (netGroup_step_iff P _ _ _).mpr
    (Or.inl ⟨rfl, e, netPre_event_step P e hall hn ho⟩)

/-- A shared visible label is a transition of the deployed group. -/
theorem netGroup_lab_step (P : Params) {u x : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} {l : Lab P.n} (hl : l ≠ Lab.tau)
    (hall : ∀ i, ABAProcStepN P i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hn : NetStep P w (Sum.inl l) (PMF.pure w'))
    (ho : (WCC.specFamily P).step o l ω) :
    (netGroup P).step (u, w, o) l
      (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω)) :=
  (netGroup_step_iff P _ _ _).mpr (Or.inr (netPre_lab_step P hl hall hn ho))

/-- A network-local injection is a silent transition of the deployed group. -/
theorem netGroup_tau_net (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    (hn : NetStep P w (Sum.inl .tau) (PMF.pure w')) :
    (netGroup P).step (u, w, o) Lab.tau (PMF.pure (u, w', o)) :=
  (netGroup_step_iff P _ _ _).mpr (Or.inr (netPre_tau_net P hn))

/-- The coin resolution is a silent transition of the deployed group. -/
theorem netGroup_tau_wcc (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)}
    (ho : (WCC.specFamily P).step o Lab.tau ω) :
    (netGroup P).step (u, w, o) Lab.tau
      (prodPMF (PMF.pure u) (prodPMF (PMF.pure w) ω)) :=
  (netGroup_step_iff P _ _ _).mpr (Or.inr (netPre_tau_wcc P ho))

end Net


namespace Net

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

end Net


namespace Net

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

end Net


namespace Net

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

end Net


namespace Net

/-! ### The deflation map

A deployed state is read as one monolithic state by assembling the record
layers slice by slice. The round-`r` stage takes its local records from the
nodes' round-`r` stage slices and its receiver rows from those slices'
inboxes (the transposition), while its sender rows and its copy of the
corrupted set are the network's. The round loop takes its control records and
its receiver rows from the nodes' coordinator slices, and its sender rows and
corrupted set from the network again. The coin oracle occupies the same slot
on both sides and is carried across untouched. -/

private theorem implStateN_ext {n : ℕ} {a b : GBCA.ImplState n}
    (h1 : a.proc = b.proc) (h2 : a.sent = b.sent)
    (h3 : a.recv = b.recv) (h4 : a.F = b.F) : a = b := by
  cases a; cases b
  cases h1; cases h2; cases h3; cases h4
  rfl

private theorem coreStateN_ext {n : ℕ} {a b : CoreState n}
    (h1 : a.procs = b.procs) (h2 : a.decidedSent = b.decidedSent)
    (h3 : a.decidedRecv = b.decidedRecv) (h4 : a.F = b.F) : a = b := by
  cases a; cases b
  cases h1; cases h2; cases h3; cases h4
  rfl

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

/-! #### The map -/

/-- The round-`r` stage of the deflation. -/
def deflStageN {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w : NetState n) (r : ℕ) :
    GBCA.ImplState n where
  proc := fun j => ((u j).2 r).proc
  sent := w.pool r
  recv := fun i => ((u i).2 r).inbox
  F := w.F

@[simp] theorem deflStageN_proc {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n)
    (w : NetState n) (r : ℕ) :
    (deflStageN u w r).proc = fun j => ((u j).2 r).proc := rfl
@[simp] theorem deflStageN_sent {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n)
    (w : NetState n) (r : ℕ) : (deflStageN u w r).sent = w.pool r := rfl
@[simp] theorem deflStageN_recv {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n)
    (w : NetState n) (r : ℕ) :
    (deflStageN u w r).recv = fun i => ((u i).2 r).inbox := rfl
@[simp] theorem deflStageN_F {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n)
    (w : NetState n) (r : ℕ) : (deflStageN u w r).F = w.F := rfl

/-- The round-loop half of the deflation. -/
def deflCoreN {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w : NetState n) :
    CoreState n where
  procs := fun j => (u j).1.proc
  decidedSent := w.dpool
  decidedRecv := fun i => (u i).1.decIn
  F := w.F

@[simp] theorem deflCoreN_procs {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n)
    (w : NetState n) : (deflCoreN u w).procs = fun j => (u j).1.proc := rfl
@[simp] theorem deflCoreN_decidedSent {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n)
    (w : NetState n) : (deflCoreN u w).decidedSent = w.dpool := rfl
@[simp] theorem deflCoreN_decidedRecv {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n)
    (w : NetState n) : (deflCoreN u w).decidedRecv = fun i => (u i).1.decIn := rfl
@[simp] theorem deflCoreN_F {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n)
    (w : NetState n) : (deflCoreN u w).F = w.F := rfl

/-- **The deflation**: the assembled stages and round loop beside the
untouched coin oracle. -/
def deflNet {P : Params}
    (s : (∀ _ : Fin P.n, ABANodeN P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n))) :
    (ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)) :=
  (fun r => deflStageN s.1 s.2.1 r, deflCoreN s.1 s.2.1, s.2.2)

/-- The deflation carries the deployed initial state to the monolithic one. -/
theorem deflNet_init (P : Params) : deflNet (netFlat P).init = (hybridImpl P).init := by
  refine Prod.ext (funext fun r => ?_) (Prod.ext ?_ rfl)
  · exact implStateN_ext rfl rfl rfl rfl
  · exact coreStateN_ext rfl rfl rfl rfl

/-! #### The corruption commutation

All four copies of the corrupted set — the network's and the three the
monolithic state carries — are the network's one set, and the three `corrupt`
functions share the guard `k ∉ F ∧ |F| < f`, so corrupting the network
corrupts every deflated layer. -/

theorem deflStageN_corrupt {P : Params} (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (k : Fin P.n) (r : ℕ) :
    deflStageN u (NetState.corrupt P k w) r = (deflStageN u w r).corrupt P k := by
  unfold GBCA.ImplState.corrupt NetState.corrupt
  simp only [deflStageN_F]
  by_cases hc : k ∉ w.F ∧ w.F.card < P.f
  · rw [if_pos hc, if_pos hc]; rfl
  · rw [if_neg hc, if_neg hc]

theorem deflCoreN_corrupt {P : Params} (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (k : Fin P.n) :
    deflCoreN u (NetState.corrupt P k w) = (deflCoreN u w).corrupt P k := by
  unfold CoreState.corrupt NetState.corrupt
  simp only [deflCoreN_F]
  by_cases hc : k ∉ w.F ∧ w.F.card < P.f
  · rw [if_pos hc, if_pos hc]; rfl
  · rw [if_neg hc, if_neg hc]

/-! #### Deltas of the deflation

Each rendezvous or handshake writes one node slice and one network slot; read
through the deflation, the pair becomes the matching one-row update of one
monolithic layer, every other layer being left alone. -/

/-- A node update at `j` touching only the round-loop slice leaves every
deflated stage alone, over a network whose pools and corrupted set are. -/
theorem deflStagesN_core {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w w' : NetState n)
    (j : Fin n) (c' : CoreNodeN n) (hp : w'.pool = w.pool) (hF : w'.F = w.F) :
    (fun r => deflStageN (Function.update u j (c', (u j).2)) w' r)
      = fun r => deflStageN u w r := by
  funext r
  refine implStateN_ext ?_ (by simp only [deflStageN_sent, hp]) ?_
    (by simp only [deflStageN_F, hF])
  all_goals
    simp only [deflStageN_proc, deflStageN_recv]
    funext i
    by_cases hi : i = j
    · subst hi; simp only [Function.update_self]
    · rw [Function.update_of_ne hi]

/-- A node update at `j` deflates the round loop to the field-wise one-row
update; the node's stage slices do not enter. -/
theorem deflCoreN_core {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w w' : NetState n)
    (j : Fin n) (c' : CoreNodeN n) (g' : ℕ → GBCA.ProcNodeN n) (hF : w'.F = w.F) :
    deflCoreN (Function.update u j (c', g')) w'
      = { procs := Function.update (fun i => (u i).1.proc) j c'.proc,
          decidedSent := w'.dpool,
          decidedRecv := Function.update (fun i => (u i).1.decIn) j c'.decIn,
          F := w.F } := by
  refine coreStateN_ext ?_ rfl ?_ (by simp only [deflCoreN_F, hF])
  all_goals
    simp only [deflCoreN_procs, deflCoreN_decidedRecv]
    funext i
    by_cases hi : i = j
    · subst hi; simp only [Function.update_self]
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]

/-- A node update at `j` touching only stage slices leaves the deflated round
loop alone, over a network whose DECIDED pools and corrupted set are. -/
theorem deflCoreN_stage {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w w' : NetState n)
    (j : Fin n) (g' : ℕ → GBCA.ProcNodeN n) (hd : w'.dpool = w.dpool)
    (hF : w'.F = w.F) :
    deflCoreN (Function.update u j ((u j).1, g')) w' = deflCoreN u w := by
  refine coreStateN_ext ?_ (by simp only [deflCoreN_decidedSent, hd]) ?_
    (by simp only [deflCoreN_F, hF])
  all_goals
    simp only [deflCoreN_procs, deflCoreN_decidedRecv]
    funext i
    by_cases hi : i = j
    · subst hi; simp only [Function.update_self]
    · rw [Function.update_of_ne hi]

/-- A node update at `j` whose stage-`r` slice becomes `p'` deflates the stage
tuple to the one-coordinate update at `r`. -/
theorem deflStagesN_stage {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w w' : NetState n)
    (j : Fin n) (c' : CoreNodeN n) (r : ℕ) (p' : GBCA.ProcNodeN n)
    (hF : w'.F = w.F) (hne : ∀ r', r' ≠ r → w'.pool r' = w.pool r') :
    (fun r' => deflStageN
        (Function.update u j (c', Function.update (u j).2 r p')) w' r')
      = Function.update (fun r' => deflStageN u w r') r
          { proc := Function.update (fun i => ((u i).2 r).proc) j p'.proc,
            sent := w'.pool r,
            recv := Function.update (fun i => ((u i).2 r).inbox) j p'.inbox,
            F := w.F } := by
  funext r'
  by_cases hr : r' = r
  · subst hr
    rw [Function.update_self]
    refine implStateN_ext ?_ rfl ?_ (by simp only [deflStageN_F, hF])
    all_goals
      simp only [deflStageN_proc, deflStageN_recv]
      funext i
      by_cases hi : i = j
      · subst hi; simp only [Function.update_self]
      · rw [Function.update_of_ne hi, Function.update_of_ne hi]
  · rw [Function.update_of_ne hr]
    refine implStateN_ext ?_ (by simp only [deflStageN_sent, hne r' hr]) ?_
      (by simp only [deflStageN_F, hF])
    all_goals
      simp only [deflStageN_proc, deflStageN_recv]
      funext i
      by_cases hi : i = j
      · subst hi; simp only [Function.update_self, Function.update_of_ne hr]
      · rw [Function.update_of_ne hi]

/-- A network-only pool write deflates the stage tuple to the one-coordinate
update at the written round. -/
theorem deflStagesN_net {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w w' : NetState n)
    (r : ℕ) (hF : w'.F = w.F) (hne : ∀ r', r' ≠ r → w'.pool r' = w.pool r') :
    (fun r' => deflStageN u w' r')
      = Function.update (fun r' => deflStageN u w r') r
          { proc := fun i => ((u i).2 r).proc, sent := w'.pool r,
            recv := fun i => ((u i).2 r).inbox, F := w.F } := by
  funext r'
  by_cases hr : r' = r
  · subst hr
    rw [Function.update_self]
    exact implStateN_ext rfl rfl rfl (by simp only [deflStageN_F, hF])
  · rw [Function.update_of_ne hr]
    exact implStateN_ext rfl (by simp only [deflStageN_sent, hne r' hr]) rfl
      (by simp only [deflStageN_F, hF])

/-! ##### The stage deltas, rule by rule -/

/-- A stage-record write joined with the sender's own pool insert: the
monolithic local write followed by the monolithic multicast. -/
theorem deflStagesN_setP_mcast {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n)
    (w : NetState n) (j : Fin n) (c' : CoreNodeN n) (r : ℕ) (p : GBCA.ProcState)
    (m : GBCA.Msg) :
    (fun r' => deflStageN (Function.update u j (c',
        Function.update (u j).2 r (((u j).2 r).setP p))) (w.gpool r j m) r')
      = Function.update (fun r' => deflStageN u w r') r
          (((deflStageN u w r).setProc j p).mcast j m) := by
  rw [deflStagesN_stage u w (w.gpool r j m) j c' r _ rfl
    (fun r' h => gpool_pool_ne w r j m h)]
  congr 1
  refine implStateN_ext rfl (gpool_pool_self w r j m) ?_ rfl
  exact Function.update_eq_self j _

/-- A stage-record write that multicasts nothing. -/
theorem deflStagesN_setP {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w : NetState n)
    (j : Fin n) (c' : CoreNodeN n) (r : ℕ) (p : GBCA.ProcState) :
    (fun r' => deflStageN (Function.update u j (c',
        Function.update (u j).2 r (((u j).2 r).setP p))) w r')
      = Function.update (fun r' => deflStageN u w r') r
          ((deflStageN u w r).setProc j p) := by
  rw [deflStagesN_stage u w w j c' r _ rfl (fun _ _ => rfl)]
  congr 1
  exact implStateN_ext rfl rfl (Function.update_eq_self j _) rfl

/-- A stage delivery: the receiver's inbox row is the monolithic receiver
row. -/
theorem deflStagesN_deliverTo {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n)
    (w : NetState n) (i : Fin n) (c' : CoreNodeN n) (r : ℕ) (k : Fin n)
    (m : GBCA.Msg) :
    (fun r' => deflStageN (Function.update u i (c',
        Function.update (u i).2 r (((u i).2 r).deliverTo k m))) w r')
      = Function.update (fun r' => deflStageN u w r') r
          ((deflStageN u w r).recvMsg i k m) := by
  rw [deflStagesN_stage u w w i c' r _ rfl (fun _ _ => rfl)]
  congr 1
  exact implStateN_ext (Function.update_eq_self i _) rfl rfl rfl

/-- A pool insert with no node write: the monolithic Byzantine multicast. -/
theorem deflStagesN_mcast {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w : NetState n)
    (r : ℕ) (k : Fin n) (m : GBCA.Msg) :
    (fun r' => deflStageN u (w.gpool r k m) r')
      = Function.update (fun r' => deflStageN u w r') r
          ((deflStageN u w r).mcast k m) := by
  rw [deflStagesN_net u w (w.gpool r k m) r rfl (fun r' h => gpool_pool_ne w r k m h)]
  congr 1
  exact implStateN_ext rfl (gpool_pool_self w r k m) rfl rfl

/-! ##### The round-loop deltas, rule by rule -/

/-- A control-record write is the monolithic one-row control write. -/
theorem deflCoreN_setProc {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w : NetState n)
    (j : Fin n) (g' : ℕ → GBCA.ProcNodeN n) (p : ProcCore n) :
    deflCoreN (Function.update u j ((u j).1.setProc p, g')) w
      = (deflCoreN u w).setProc j p := by
  rw [deflCoreN_core u w w j _ g' rfl]
  exact coreStateN_ext rfl rfl (Function.update_eq_self j _) rfl

/-- A DECIDED receipt is the monolithic delivery. -/
theorem deflCoreN_recvDec {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w : NetState n)
    (i : Fin n) (g' : ℕ → GBCA.ProcNodeN n) (k : Fin n) (b : Bool) :
    deflCoreN (Function.update u i ((u i).1.recvDec k b, g')) w
      = (deflCoreN u w).deliverDecided i k b := by
  rw [deflCoreN_core u w w i _ g' rfl]
  exact coreStateN_ext (Function.update_eq_self i _) rfl rfl rfl

/-- A DECIDED pool insert is the monolithic multicast. -/
theorem deflCoreN_dput {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n) (w : NetState n)
    (j : Fin n) (b : Bool) :
    deflCoreN u (w.dput j b) = (deflCoreN u w).sendDecided j b := rfl

/-- The fused coin return (D10): the node's round advance joined with the
network's publication is the monolithic round advance on an `A` grade. -/
theorem deflCoreN_stepRound_pub {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n)
    (w : NetState n) (j : Fin n) (co b : Bool)
    (hg : (u j).1.proc.lastGrade = some (.A b)) :
    deflCoreN (Function.update u j ((u j).1.stepRound co, (u j).2)) (w.dput j b)
      = (deflCoreN u w).stepRound j co := by
  have h1 : deflCoreN (Function.update u j ((u j).1.stepRound co, (u j).2)) (w.dput j b)
      = (deflCoreN u (w.dput j b)).setProc j
        { (u j).1.proc with
          est := some ((u j).1.proc.est.getD co), lastGrade := none,
          round := (u j).1.proc.round + 1, phase := .toCallG } :=
    deflCoreN_setProc u (w.dput j b) j (u j).2 _
  rw [h1, deflCoreN_dput]
  unfold CoreState.stepRound
  rw [show ((deflCoreN u w).procs j).lastGrade = some (.A b) from hg]
  rfl

/-- The unfused coin return: the round advance publishes nothing. -/
theorem deflCoreN_stepRound_plain {n : ℕ} (u : ∀ _ : Fin n, ABANodeN n)
    (w : NetState n) (j : Fin n) (co : Bool)
    (hg : ∀ v : Bool, (u j).1.proc.lastGrade ≠ some (.A v)) :
    deflCoreN (Function.update u j ((u j).1.stepRound co, (u j).2)) w
      = (deflCoreN u w).stepRound j co := by
  have h1 : deflCoreN (Function.update u j ((u j).1.stepRound co, (u j).2)) w
      = (deflCoreN u w).setProc j
        { (u j).1.proc with
          est := some ((u j).1.proc.est.getD co), lastGrade := none,
          round := (u j).1.proc.round + 1, phase := .toCallG } :=
    deflCoreN_setProc u w j (u j).2 _
  rw [h1]
  unfold CoreState.stepRound
  cases hlg : (u j).1.proc.lastGrade with
  | none =>
    rw [show ((deflCoreN u w).procs j).lastGrade = none from hlg]; rfl
  | some out =>
    cases out with
    | A v => exact absurd hlg (hg v)
    | B v =>
      rw [show ((deflCoreN u w).procs j).lastGrade = some (.B v) from hlg]; rfl
    | C =>
      rw [show ((deflCoreN u w).procs j).lastGrade = some .C from hlg]; rfl

end Net


namespace Net

/-! ### Assembling the monolithic transitions

The monolithic hybrid is `(GBCA.implFamily ∥ (core ∥ WCC.specFamily))` with the
sub-protocol API hidden; the lemmas below build each of its rows out of the
component rows the deployed system supplies. -/

/-- The system whose sub-protocol API `hybridImpl` hides. -/
noncomputable def hybridPreN (P : Params) :
    System ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))
      (Lab P.n) :=
  (GBCA.implFamily P).parallel (context P)

theorem hybridImpl_eqN (P : Params) :
    hybridImpl P = (hybridPreN P).abstract (Lab.hiddenAPI P.n) := rfl

/-! #### The stage family's rows -/

/-- The round-`r` instance moves on a label it owns. -/
theorem implFamilyN_owned (P : Params) (S : ℕ → GBCA.ImplState P.n) (r : ℕ)
    {l : Lab P.n} (hl : Lab.gbcaRound l = some r) {X : GBCA.ImplState P.n}
    (h : GBCA.ImplStep P r (S r) l (PMF.pure X)) :
    (GBCA.implFamily P).step S l (PMF.pure (Function.update S r X)) := by
  rw [GBCA.implFamily, System.family_step_iff]
  exact Or.inr (Or.inl ⟨r, hl, PMF.pure X, h, by rw [PMF.pure_map]⟩)

/-- The round-`r` instance takes one of its own silent rules. -/
theorem implFamilyN_tau (P : Params) (S : ℕ → GBCA.ImplState P.n) (r : ℕ)
    {X : GBCA.ImplState P.n} (h : GBCA.ImplStep P r (S r) .tau (PMF.pure X)) :
    (GBCA.implFamily P).step S Lab.tau (PMF.pure (Function.update S r X)) := by
  rw [GBCA.implFamily, System.family_step_iff]
  exact Or.inl ⟨rfl, r, PMF.pure X, h, by rw [PMF.pure_map]⟩

/-- A label no instance owns and no broadcast: the family idles. -/
theorem implFamilyN_idle (P : Params) (S : ℕ → GBCA.ImplState P.n) {l : Lab P.n}
    (hl : l ≠ Lab.tau) (hr : Lab.gbcaRound l = none) (hf : ¬ Lab.isFail l) :
    (GBCA.implFamily P).step S l (PMF.pure S) := by
  rw [GBCA.implFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hl, hr, hf, rfl⟩))

/-- Corruption is broadcast to every instance. -/
theorem implFamilyN_fail (P : Params) (S : ℕ → GBCA.ImplState P.n) (k : Fin P.n) :
    (GBCA.implFamily P).step S (.fail k)
      (PMF.pure (fun r => (S r).corrupt P k)) := by
  rw [GBCA.implFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl, trivial, rfl⟩))

/-! #### The coin family's idle row -/

theorem wccFamilyN_idle (P : Params) (o : ℕ → WCC.SpecState P.n) {l : Lab P.n}
    (hl : l ≠ Lab.tau) (hr : Lab.wccRound l = none) (hf : ¬ Lab.isFail l) :
    (WCC.specFamily P).step o l (PMF.pure o) := by
  rw [WCC.specFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hl, hr, hf, rfl⟩))

/-! #### The three factors together -/

/-- A visible joint step of the three monolithic factors. -/
theorem hybridPreN_lab (P : Params) {S S' : ℕ → GBCA.ImplState P.n}
    {C C' : CoreState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} {l : Lab P.n} (hl : l ≠ Lab.tau)
    (hI : (GBCA.implFamily P).step S l (PMF.pure S'))
    (hC : CoreStep P C l (PMF.pure C'))
    (hW : (WCC.specFamily P).step o l ω) :
    (hybridPreN P).step (S, C, o) l
      (prodPMF (PMF.pure S') (prodPMF (PMF.pure C') ω)) := by
  rw [hybridPreN, System.parallel_step]
  refine Or.inl ⟨hl, _, _, hI, ?_, rfl⟩
  rw [context, System.parallel_step]
  exact Or.inl ⟨hl, _, _, hC, hW, rfl⟩

/-- A silent step of the stage family alone. -/
theorem hybridPreN_tau_impl (P : Params) {S S' : ℕ → GBCA.ImplState P.n}
    {C : CoreState P.n} {o : ℕ → WCC.SpecState P.n}
    (hI : (GBCA.implFamily P).step S Lab.tau (PMF.pure S')) :
    (hybridPreN P).step (S, C, o) Lab.tau (PMF.pure (S', C, o)) := by
  rw [hybridPreN, System.parallel_step]
  exact Or.inr (Or.inl ⟨rfl, PMF.pure S', hI, (prodPMF_pure_pure _ _).symm⟩)

/-- A silent step of the round loop alone. -/
theorem hybridPreN_tau_core (P : Params) {S : ℕ → GBCA.ImplState P.n}
    {C C' : CoreState P.n} {o : ℕ → WCC.SpecState P.n}
    (hC : CoreStep P C Lab.tau (PMF.pure C')) :
    (hybridPreN P).step (S, C, o) Lab.tau (PMF.pure (S, C', o)) := by
  rw [hybridPreN, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure C') (PMF.pure o), ?_, ?_⟩)
  · rw [context, System.parallel_step]
    exact Or.inr (Or.inl ⟨rfl, PMF.pure C', hC, rfl⟩)
  · rw [prodPMF_pure_pure, prodPMF_pure_pure]

/-- The coin resolution, the one non-Dirac row. -/
theorem hybridPreN_tau_wcc (P : Params) {S : ℕ → GBCA.ImplState P.n}
    {C : CoreState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)}
    (hW : (WCC.specFamily P).step o Lab.tau ω) :
    (hybridPreN P).step (S, C, o) Lab.tau
      (prodPMF (PMF.pure S) (prodPMF (PMF.pure C) ω)) := by
  rw [hybridPreN, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure C) ω, ?_, rfl⟩)
  rw [context, System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, ω, hW, rfl⟩)

/-! #### Through the outer hiding -/

theorem hybridImplN_of_tau (P : Params)
    {x : (ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n))}
    {μ : PMF ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (hybridPreN P).step x Lab.tau μ) :
    (hybridImpl P).step x Lab.tau μ := by
  rw [hybridImpl_eqN, System.abstract_step]
  exact Or.inr ⟨by simp, h⟩

theorem hybridImplN_of_hidden (P : Params)
    {x : (ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n))}
    {l : Lab P.n} (hl : l ∈ Lab.hiddenAPI P.n)
    {μ : PMF ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (hybridPreN P).step x l μ) : (hybridImpl P).step x Lab.tau μ := by
  rw [hybridImpl_eqN, System.abstract_step]
  exact Or.inl ⟨rfl, l, hl, h⟩

/-! #### Pushing the successor distribution forward

The only factor whose successor need not be a Dirac is the coin oracle, and it
occupies the same coordinate on both sides; the deflation is therefore applied
under one `map`. -/

theorem map_deflNet_prod {P : Params} (x : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (ω : PMF (ℕ → WCC.SpecState P.n)) :
    (prodPMF (PMF.pure x) (prodPMF (PMF.pure w) ω)).map deflNet
      = prodPMF (PMF.pure (fun r => deflStageN x w r))
          (prodPMF (PMF.pure (deflCoreN x w)) ω) := by
  rw [prodPMF_pure_left, prodPMF_pure_left, prodPMF_pure_left, prodPMF_pure_left,
    PMF.map_comp, PMF.map_comp, PMF.map_comp]
  rfl

theorem map_deflNet_pure {P : Params} (x : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) :
    (prodPMF (PMF.pure x) (prodPMF (PMF.pure w) (PMF.pure o))).map deflNet
      = PMF.pure ((fun r => deflStageN x w r), deflCoreN x w, o) := by
  rw [prodPMF_pure_pure, prodPMF_pure_pure, PMF.pure_map]
  rfl

end Net


namespace Net

/-! ### Reading a deployed transition into its three factors -/

/-- A rendezvous transition: every process, the network and the lifted oracle
move together, and only the oracle's successor can fail to be a Dirac. -/
theorem netPre_event_inv (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n} {e : NetEvt P.n}
    {μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (netPre P).step (u, w, o) (Sum.inr e) μ) :
    ∃ (x : ∀ _ : Fin P.n, ABANodeN P.n) (w' : NetState P.n)
      (μ₃ : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, ABAProcStepN P i (u i) (Sum.inr e) (PMF.pure (x i))) ∧
      NetStep P w (Sum.inr e) (PMF.pure w') ∧
      (wccLift P).step o (Sum.inr e) μ₃ ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') μ₃) := by
  rw [netPre, System.parallel_step] at h
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
theorem netPre_lab_inv (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n} {l : Lab P.n} (hl : l ≠ Lab.tau)
    {μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (netPre P).step (u, w, o) (Sum.inl l) μ) :
    ∃ (x : ∀ _ : Fin P.n, ABANodeN P.n) (w' : NetState P.n)
      (ω : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, ABAProcStepN P i (u i) (Sum.inl l) (PMF.pure (x i))) ∧
      NetStep P w (Sum.inl l) (PMF.pure w') ∧
      (WCC.specFamily P).step o l ω ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω) := by
  rw [netPre, System.parallel_step] at h
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
theorem netPre_tau_inv (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (netPre P).step (u, w, o) (Sum.inl Lab.tau) μ) :
    (∃ w', NetStep P w (Sum.inl .tau) (PMF.pure w') ∧ μ = PMF.pure (u, w', o)) ∨
    (∃ ω, (WCC.specFamily P).step o Lab.tau ω ∧
      μ = prodPMF (PMF.pure u) (prodPMF (PMF.pure w) ω)) := by
  rw [netPre, System.parallel_step] at h
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

@[simp] theorem deflNet_apply {P : Params} (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) :
    deflNet (u, w, o) = ((fun r => deflStageN u w r), deflCoreN u w, o) := rfl

/-- An owned label whose instance stands still. -/
theorem implFamilyN_owned_id (P : Params) (S : ℕ → GBCA.ImplState P.n) (r : ℕ)
    {l : Lab P.n} (hl : Lab.gbcaRound l = some r)
    (h : GBCA.ImplStep P r (S r) l (PMF.pure (S r))) :
    (GBCA.implFamily P).step S l (PMF.pure S) := by
  have hstep := implFamilyN_owned P S r hl h
  rwa [Function.update_eq_self] at hstep

end Net


namespace Net

/-! ### The hidden rendezvous labels

Each rendezvous of the deployed system is a silent transition of the
monolithic hybrid: either one of its components' own silent rules, or — for
the Byzantine handshake drives and the fused coin return — a genuine
monolithic handshake that the outer hiding sends to `τ`. -/

theorem hybridImplN_of_netEvt (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n} (e : NetEvt P.n)
    {μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (netPre P).step (u, w, o) (Sum.inr e) μ) :
    (hybridImpl P).step (deflNet (u, w, o)) Lab.tau (μ.map deflNet) := by
  obtain ⟨x, w', μ₃, hall, hn, ho, rfl⟩ := netPre_event_inv P h
  rw [map_deflNet_prod, deflNet_apply]
  cases e with
  | gsnd r j m =>
    obtain rfl : w' = w.gpool r j m := pureN_inj (netStep_gsnd hn)
    obtain rfl : μ₃ = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_gsnd r j m) μ₃).mp ho
    rw [prodPMF_pure_pure, prodPMF_pure_pure]
    cases m with
    | input b =>
      obtain ⟨hin, hcnt, hsend, hx0⟩ := stepN_gsnd_input_self (hall j)
      have hx := procsN_update hx0
        (fun i hi => stepN_gsnd_foreign (Ne.symm hi) (hall i))
      subst hx
      rw [deflStagesN_setP_mcast u w j _ r _ (.input b),
        deflCoreN_stage u w (w.gpool r j (.input b)) j _ rfl rfl]
      exact hybridImplN_of_tau P (hybridPreN_tau_impl P
        (implFamilyN_tau P _ r (GBCA.ImplStep.relay _ j b hin hcnt hsend)))
    | echo b =>
      obtain ⟨hin, hcnt, hsend, hx0⟩ := stepN_gsnd_echo_self (hall j)
      have hx := procsN_update hx0
        (fun i hi => stepN_gsnd_foreign (Ne.symm hi) (hall i))
      subst hx
      rw [deflStagesN_setP_mcast u w j _ r _ (.echo b),
        deflCoreN_stage u w (w.gpool r j (.echo b)) j _ rfl rfl]
      exact hybridImplN_of_tau P (hybridPreN_tau_impl P
        (implFamilyN_tau P _ r (GBCA.ImplStep.echo _ j b hin hcnt hsend)))
    | vote v =>
      cases v with
      | some b =>
        obtain ⟨hin, hcnt, hsend, hx0⟩ := stepN_gsnd_voteBit_self (hall j)
        have hx := procsN_update hx0
          (fun i hi => stepN_gsnd_foreign (Ne.symm hi) (hall i))
        subst hx
        rw [deflStagesN_setP_mcast u w j _ r _ (.vote (some b)),
          deflCoreN_stage u w (w.gpool r j (.vote (some b))) j _ rfl rfl]
        exact hybridImplN_of_tau P (hybridPreN_tau_impl P
          (implFamilyN_tau P _ r (GBCA.ImplStep.voteBit _ j b hin hcnt hsend)))
      | none =>
        obtain ⟨hin, hcnt, hval, hsend, hx0⟩ := stepN_gsnd_voteBot_self (hall j)
        have hx := procsN_update hx0
          (fun i hi => stepN_gsnd_foreign (Ne.symm hi) (hall i))
        subst hx
        rw [deflStagesN_setP_mcast u w j _ r _ (.vote none),
          deflCoreN_stage u w (w.gpool r j (.vote none)) j _ rfl rfl]
        exact hybridImplN_of_tau P (hybridPreN_tau_impl P
          (implFamilyN_tau P _ r (GBCA.ImplStep.voteBot _ j hin hcnt hval hsend)))
    | bind v =>
      cases v with
      | some b =>
        obtain ⟨hin, hcnt, hsend, hx0⟩ := stepN_gsnd_bindBit_self (hall j)
        have hx := procsN_update hx0
          (fun i hi => stepN_gsnd_foreign (Ne.symm hi) (hall i))
        subst hx
        rw [deflStagesN_setP_mcast u w j _ r _ (.bind (some b)),
          deflCoreN_stage u w (w.gpool r j (.bind (some b))) j _ rfl rfl]
        exact hybridImplN_of_tau P (hybridPreN_tau_impl P
          (implFamilyN_tau P _ r (GBCA.ImplStep.bindBit _ j b hin hcnt hsend)))
      | none =>
        obtain ⟨hin, hcnt, hval, hsend, hx0⟩ := stepN_gsnd_bindBot_self (hall j)
        have hx := procsN_update hx0
          (fun i hi => stepN_gsnd_foreign (Ne.symm hi) (hall i))
        subst hx
        rw [deflStagesN_setP_mcast u w j _ r _ (.bind none),
          deflCoreN_stage u w (w.gpool r j (.bind none)) j _ rfl rfl]
        exact hybridImplN_of_tau P (hybridPreN_tau_impl P
          (implFamilyN_tau P _ r (GBCA.ImplStep.bindBot _ j hin hcnt hval hsend)))
    | «seal» v =>
      cases v with
      | some b =>
        obtain ⟨hin, hcnt, hsend, hx0⟩ := stepN_gsnd_sealBit_self (hall j)
        have hx := procsN_update hx0
          (fun i hi => stepN_gsnd_foreign (Ne.symm hi) (hall i))
        subst hx
        rw [deflStagesN_setP_mcast u w j _ r _ (.seal (some b)),
          deflCoreN_stage u w (w.gpool r j (.seal (some b))) j _ rfl rfl]
        exact hybridImplN_of_tau P (hybridPreN_tau_impl P
          (implFamilyN_tau P _ r (GBCA.ImplStep.sealBit _ j b hin hcnt hsend)))
      | none =>
        obtain ⟨hin, hcnt, hval, hsend, hx0⟩ := stepN_gsnd_sealBot_self (hall j)
        have hx := procsN_update hx0
          (fun i hi => stepN_gsnd_foreign (Ne.symm hi) (hall i))
        subst hx
        rw [deflStagesN_setP_mcast u w j _ r _ (.seal none),
          deflCoreN_stage u w (w.gpool r j (.seal none)) j _ rfl rfl]
        exact hybridImplN_of_tau P (hybridPreN_tau_impl P
          (implFamilyN_tau P _ r (GBCA.ImplStep.sealBot _ j hin hcnt hval hsend)))
  | gdlv r i j m =>
    obtain ⟨hmem, hw⟩ := netStep_gdlv hn
    rw [show w' = w from pureN_inj hw]
    obtain rfl : μ₃ = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_gdlv r i j m) μ₃).mp ho
    rw [prodPMF_pure_pure, prodPMF_pure_pure]
    have hx := procsN_update (stepN_gdlv_self (hall i))
      (fun k hk => stepN_gdlv_foreign (Ne.symm hk) (hall k))
    subst hx
    rw [deflStagesN_deliverTo u w i _ r j m, deflCoreN_stage u w w i _ rfl rfl]
    exact hybridImplN_of_tau P (hybridPreN_tau_impl P
      (implFamilyN_tau P _ r (GBCA.ImplStep.deliver _ i j m hmem)))
  | dsnd j b =>
    obtain ⟨hpool, hw⟩ := netStep_dsnd hn
    obtain rfl : w' = w.dput j b := pureN_inj hw
    obtain rfl : μ₃ = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_dsnd j b) μ₃).mp ho
    rw [prodPMF_pure_pure, prodPMF_pure_pure]
    obtain ⟨hcnt, hx0⟩ := stepN_dsnd_self (hall j)
    have hx : x = u := procsN_id fun i => by
      by_cases hi : i = j
      · subst hi; exact hx0
      · exact stepN_dsnd_foreign (Ne.symm hi) (hall i)
    subst hx
    exact hybridImplN_of_tau P (hybridPreN_tau_core P
      (CoreStep.echo _ j b hcnt hpool))
  | ddlv i j b =>
    obtain ⟨hmem, hw⟩ := netStep_ddlv hn
    rw [show w' = w from pureN_inj hw]
    obtain rfl : μ₃ = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_ddlv i j b) μ₃).mp ho
    rw [prodPMF_pure_pure, prodPMF_pure_pure]
    obtain ⟨hnr, hx0⟩ := stepN_ddlv_self (hall i)
    have hx := procsN_update hx0
      (fun k hk => stepN_ddlv_foreign (Ne.symm hk) (hall k))
    subst hx
    rw [deflStagesN_core u w w i _ rfl rfl, deflCoreN_recvDec u w i _ j b]
    exact hybridImplN_of_tau P (hybridPreN_tau_core P
      (CoreStep.deliver _ i j b hmem hnr))
  | retWPub r id c b =>
    obtain rfl : w' = w.dput id b := pureN_inj (netStep_retWPub hn)
    obtain ⟨hph, hr, hg, hx0⟩ := stepN_retWPub_self (hall id)
    have hx := procsN_update hx0
      (fun i hi => stepN_retWPub_foreign (Ne.symm hi) (hall i))
    subst hx
    have hW := (System.mapIdle_step_some (wccPull_retWPub r id c b) μ₃).mp ho
    rw [deflStagesN_core u w (w.dput id b) id _ rfl rfl,
      deflCoreN_stepRound_pub u w id c b hg]
    exact hybridImplN_of_hidden P (Lab.retW_mem_hiddenAPI r id c)
      (hybridPreN_lab P (by simp) (implFamilyN_idle P _ (by simp) rfl not_false)
        (CoreStep.retW _ r id c hph hr) hW)
  | gcallLoop r id b =>
    rw [show w' = w from pureN_inj (netStep_gcallLoop hn)]
    obtain rfl : μ₃ = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_gcallLoop r id b) μ₃).mp ho
    obtain ⟨hph, hr, hest, hx0⟩ := stepN_gcallLoop_self (hall id)
    have hx := procsN_update hx0
      (fun i hi => stepN_gcallLoop_foreign (Ne.symm hi) (hall i))
    subst hx
    rw [deflStagesN_core u w w id _ rfl rfl, deflCoreN_setProc u w id _ _]
    exact hybridImplN_of_hidden P (Lab.callG_mem_hiddenAPI r id b)
      (hybridPreN_lab P (by simp)
        (implFamilyN_owned_id P _ r rfl (GBCA.ImplStep.callLoop _ id b))
        (CoreStep.callG _ r id b hph hr hest)
        (wccFamilyN_idle P o (by simp) rfl not_false))
  | byzCallG r k b =>
    obtain ⟨hF, hw⟩ := netStep_byzCallG hn
    obtain rfl : w' = w.gpool r k (.input b) := pureN_inj hw
    obtain rfl : μ₃ = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_byzCallG r k b) μ₃).mp ho
    obtain ⟨hin, hx0⟩ := stepN_byzCallG_self (hall k)
    have hx := procsN_update hx0
      (fun i hi => stepN_byzCallG_foreign (Ne.symm hi) (hall i))
    subst hx
    rw [deflStagesN_setP_mcast u w k _ r _ (.input b),
      deflCoreN_stage u w (w.gpool r k (.input b)) k _ rfl rfl]
    exact hybridImplN_of_hidden P (Lab.callG_mem_hiddenAPI r k b)
      (hybridPreN_lab P (by simp)
        (implFamilyN_owned P _ r rfl (GBCA.ImplStep.call _ k b hin))
        (CoreStep.callGByz _ r k b hF)
        (wccFamilyN_idle P o (by simp) rfl not_false))
  | byzCallGLoop r k b =>
    obtain ⟨hF, hw⟩ := netStep_byzCallGLoop hn
    rw [show w' = w from pureN_inj hw]
    obtain rfl : μ₃ = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_byzCallGLoop r k b) μ₃).mp ho
    have hx : x = u := procsN_id fun i => stepN_byzCallGLoop (hall i)
    subst hx
    exact hybridImplN_of_hidden P (Lab.callG_mem_hiddenAPI r k b)
      (hybridPreN_lab P (by simp)
        (implFamilyN_owned_id P _ r rfl (GBCA.ImplStep.callLoop _ k b))
        (CoreStep.callGByz _ r k b hF)
        (wccFamilyN_idle P o (by simp) rfl not_false))
  | byzRetG r k out =>
    obtain ⟨hF, hw⟩ := netStep_byzRetG hn
    rw [show w' = w from pureN_inj hw]
    obtain rfl : μ₃ = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_byzRetG r k out) μ₃).mp ho
    cases out with
    | A v =>
      obtain ⟨hcnt, hret, hx0⟩ := stepN_byzRetG_A_self (hall k)
      have hx := procsN_update hx0
        (fun i hi => stepN_byzRetG_foreign (Ne.symm hi) (hall i))
      subst hx
      rw [deflStagesN_setP u w k _ r _, deflCoreN_stage u w w k _ rfl rfl]
      exact hybridImplN_of_hidden P (Lab.retG_mem_hiddenAPI r k (.A v))
        (hybridPreN_lab P (by simp)
          (implFamilyN_owned P _ r rfl (GBCA.ImplStep.retA _ k v hcnt hret))
          (CoreStep.retGByz _ r k (.A v) hF)
          (wccFamilyN_idle P o (by simp) rfl not_false))
    | B v =>
      obtain ⟨hcnt, honce, hbind, hval, hret, hx0⟩ := stepN_byzRetG_B_self (hall k)
      have hx := procsN_update hx0
        (fun i hi => stepN_byzRetG_foreign (Ne.symm hi) (hall i))
      subst hx
      rw [deflStagesN_setP u w k _ r _, deflCoreN_stage u w w k _ rfl rfl]
      exact hybridImplN_of_hidden P (Lab.retG_mem_hiddenAPI r k (.B v))
        (hybridPreN_lab P (by simp)
          (implFamilyN_owned P _ r rfl
            (GBCA.ImplStep.retB _ k v hcnt honce hbind hval hret))
          (CoreStep.retGByz _ r k (.B v) hF)
          (wccFamilyN_idle P o (by simp) rfl not_false))
    | C =>
      obtain ⟨hcnt, hval, hret, hx0⟩ := stepN_byzRetG_C_self (hall k)
      have hx := procsN_update hx0
        (fun i hi => stepN_byzRetG_foreign (Ne.symm hi) (hall i))
      subst hx
      rw [deflStagesN_setP u w k _ r _, deflCoreN_stage u w w k _ rfl rfl]
      exact hybridImplN_of_hidden P (Lab.retG_mem_hiddenAPI r k .C)
        (hybridPreN_lab P (by simp)
          (implFamilyN_owned P _ r rfl (GBCA.ImplStep.retC _ k hcnt hval hret))
          (CoreStep.retGByz _ r k .C hF)
          (wccFamilyN_idle P o (by simp) rfl not_false))
  | byzCallW r k =>
    obtain ⟨hF, hw⟩ := netStep_byzCallW hn
    rw [show w' = w from pureN_inj hw]
    have hW := (System.mapIdle_step_some (wccPull_byzCallW r k) μ₃).mp ho
    have hx : x = u := procsN_id fun i => stepN_byzCallW (hall i)
    subst hx
    exact hybridImplN_of_hidden P (Lab.callW_mem_hiddenAPI r k)
      (hybridPreN_lab P (by simp) (implFamilyN_idle P _ (by simp) rfl not_false)
        (CoreStep.callWByz _ r k hF) hW)
  | byzRetW r k b =>
    obtain ⟨hF, hw⟩ := netStep_byzRetW hn
    rw [show w' = w from pureN_inj hw]
    have hW := (System.mapIdle_step_some (wccPull_byzRetW r k b) μ₃).mp ho
    have hx : x = u := procsN_id fun i => stepN_byzRetW (hall i)
    subst hx
    exact hybridImplN_of_hidden P (Lab.retW_mem_hiddenAPI r k b)
      (hybridPreN_lab P (by simp) (implFamilyN_idle P _ (by simp) rfl not_false)
        (CoreStep.retWByz _ r k b hF) hW)

end Net


namespace Net

/-! ### The shared labels

A label of the shared alphabet is answered by the monolithic hybrid on the
same label: the surviving ABA API and `fail` visibly, the sub-protocol API
under the outer hiding, and `τ` by the network's own injections or by the coin
resolution. -/

theorem hybridPreN_of_netPre (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n} {l : Lab P.n}
    {μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (netPre P).step (u, w, o) (Sum.inl l) μ) :
    (hybridPreN P).step (deflNet (u, w, o)) l (μ.map deflNet) := by
  rw [deflNet_apply]
  by_cases hl : l = Lab.tau
  · subst hl
    rcases netPre_tau_inv P h with ⟨w', hnet, rfl⟩ | ⟨ω, hW, rfl⟩
    · rw [PMF.pure_map, deflNet_apply]
      rcases netStep_tau hnet with ⟨r, k, m, hF, hw⟩ | ⟨k, b, hF, hw⟩
      · obtain rfl : w' = w.gpool r k m := pureN_inj hw
        rw [deflStagesN_mcast u w r k m]
        exact hybridPreN_tau_impl P
          (implFamilyN_tau P _ r (GBCA.ImplStep.byz _ k m hF))
      · obtain rfl : w' = w.dput k b := pureN_inj hw
        exact hybridPreN_tau_core P (CoreStep.byzDecided _ k b hF)
    · rw [map_deflNet_prod]
      exact hybridPreN_tau_wcc P hW
  · obtain ⟨x, w', ω, hall, hn, hW, rfl⟩ := netPre_lab_inv P hl h
    rw [map_deflNet_prod]
    cases l with
    | tau => exact absurd rfl hl
    | callABA id b =>
      rw [show w' = w from pureN_inj (netStep_callABA hn)]
      rcases stepN_callABA_own (hall id) with ⟨hin, hx0⟩ | hx0
      · have hx := procsN_update hx0
          (fun i hi => stepN_callABA_foreign (Ne.symm hi) (hall i))
        subst hx
        rw [deflStagesN_core u w w id _ rfl rfl, deflCoreN_setProc u w id _ _]
        exact hybridPreN_lab P (by simp)
          (implFamilyN_idle P _ (by simp) rfl not_false)
          (CoreStep.input _ id b hin) hW
      · have hx : x = u := procsN_id fun i => by
          by_cases hi : i = id
          · subst hi; exact hx0
          · exact stepN_callABA_foreign (Ne.symm hi) (hall i)
        subst hx
        exact hybridPreN_lab P (by simp)
          (implFamilyN_idle P _ (by simp) rfl not_false)
          (CoreStep.inputLoop _ id b) hW
    | retABA id b =>
      obtain ⟨hpool, hw⟩ := netStep_retABA hn
      rw [show w' = w from pureN_inj hw]
      obtain ⟨hcnt, hret, hx0⟩ := stepN_retABA_own (hall id)
      have hx := procsN_update hx0
        (fun i hi => stepN_retABA_foreign (Ne.symm hi) (hall i))
      subst hx
      rw [deflStagesN_core u w w id _ rfl rfl, deflCoreN_setProc u w id _ _]
      exact hybridPreN_lab P (by simp)
        (implFamilyN_idle P _ (by simp) rfl not_false)
        (CoreStep.ret _ id b hcnt hpool hret) hW
    | callG r id b =>
      obtain rfl : w' = w.gpool r id (.input b) := pureN_inj (netStep_callG hn)
      obtain ⟨hph, hr, hest, hin, hx0⟩ := stepN_callG_own (hall id)
      have hx := procsN_update hx0
        (fun i hi => stepN_callG_foreign (Ne.symm hi) (hall i))
      subst hx
      rw [deflStagesN_setP_mcast u w id _ r _ (.input b),
        deflCoreN_setProc u (w.gpool r id (.input b)) id _ _]
      exact hybridPreN_lab P (by simp)
        (implFamilyN_owned P _ r rfl (GBCA.ImplStep.call _ id b hin))
        (CoreStep.callG _ r id b hph hr hest) hW
    | retG r id out =>
      rw [show w' = w from pureN_inj (netStep_retG hn)]
      cases out with
      | A v =>
        obtain ⟨hph, hr, hcnt, hret, hx0⟩ := stepN_retG_A_own (hall id)
        have hx := procsN_update hx0
          (fun i hi => stepN_retG_foreign (Ne.symm hi) (hall i))
        subst hx
        rw [deflStagesN_setP u w id _ r _, deflCoreN_setProc u w id _ _]
        exact hybridPreN_lab P (by simp)
          (implFamilyN_owned P _ r rfl (GBCA.ImplStep.retA _ id v hcnt hret))
          (CoreStep.retG _ r id (.A v) hph hr) hW
      | B v =>
        obtain ⟨hph, hr, hcnt, honce, hbind, hval, hret, hx0⟩ :=
          stepN_retG_B_own (hall id)
        have hx := procsN_update hx0
          (fun i hi => stepN_retG_foreign (Ne.symm hi) (hall i))
        subst hx
        rw [deflStagesN_setP u w id _ r _, deflCoreN_setProc u w id _ _]
        exact hybridPreN_lab P (by simp)
          (implFamilyN_owned P _ r rfl
            (GBCA.ImplStep.retB _ id v hcnt honce hbind hval hret))
          (CoreStep.retG _ r id (.B v) hph hr) hW
      | C =>
        obtain ⟨hph, hr, hcnt, hval, hret, hx0⟩ := stepN_retG_C_own (hall id)
        have hx := procsN_update hx0
          (fun i hi => stepN_retG_foreign (Ne.symm hi) (hall i))
        subst hx
        rw [deflStagesN_setP u w id _ r _, deflCoreN_setProc u w id _ _]
        exact hybridPreN_lab P (by simp)
          (implFamilyN_owned P _ r rfl (GBCA.ImplStep.retC _ id hcnt hval hret))
          (CoreStep.retG _ r id .C hph hr) hW
    | callW r id =>
      rw [show w' = w from pureN_inj (netStep_callW hn)]
      obtain ⟨hph, hr, hx0⟩ := stepN_callW_own (hall id)
      have hx := procsN_update hx0
        (fun i hi => stepN_callW_foreign (Ne.symm hi) (hall i))
      subst hx
      rw [deflStagesN_core u w w id _ rfl rfl, deflCoreN_setProc u w id _ _]
      exact hybridPreN_lab P (by simp)
        (implFamilyN_idle P _ (by simp) rfl not_false)
        (CoreStep.callW _ r id hph hr) hW
    | retW r id c =>
      rw [show w' = w from pureN_inj (netStep_retW hn)]
      obtain ⟨hph, hr, hgr, hx0⟩ := stepN_retW_own (hall id)
      have hx := procsN_update hx0
        (fun i hi => stepN_retW_foreign (Ne.symm hi) (hall i))
      subst hx
      rw [deflStagesN_core u w w id _ rfl rfl,
        deflCoreN_stepRound_plain u w id c hgr]
      exact hybridPreN_lab P (by simp)
        (implFamilyN_idle P _ (by simp) rfl not_false)
        (CoreStep.retW _ r id c hph hr) hW
    | fail k =>
      obtain rfl : w' = NetState.corrupt P k w := pureN_inj (netStep_fail hn)
      rw [show x = u from procsN_id fun i => stepN_fail (hall i),
        show (fun r => deflStageN u (NetState.corrupt P k w) r)
            = fun r => (deflStageN u w r).corrupt P k from
          funext (fun r => deflStageN_corrupt u w k r),
        deflCoreN_corrupt u w k]
      exact hybridPreN_lab P (by simp) (implFamilyN_fail P _ k)
        (CoreStep.fail _ k) hW

end Net


namespace Net

/-! ### The forward simulation and the inclusion

The deflation is a step-commuting state map: every deployed transition is the
monolithic hybrid's transition on the same label, its successor distribution
pushed forward. That is exactly the hypothesis of
`ProbabilisticForwardSimulation.ofStrongFunctional`, and soundness (Result 1)
turns the resulting simulation into the trace-distribution inclusion. -/

/-- **The forward matching**: every transition of the deployed system is the
matching transition of the monolithic hybrid along the deflation. -/
theorem netForward (P : Params) :
    ∀ s l μ, (netFlat P).step s l μ →
      (hybridImpl P).step (deflNet s) l (μ.map deflNet) := by
  rintro ⟨u, w, o⟩ l μ h
  rw [netFlat_step_iff] at h
  rcases h with ⟨rfl, l', hl', hg⟩ | ⟨hn, hg⟩
  · rw [netGroup_step_iff] at hg
    rcases hg with ⟨rfl, e, hpre⟩ | hpre
    · exact absurd hl' (by simp)
    · exact hybridImplN_of_hidden P hl' (hybridPreN_of_netPre P hpre)
  · rw [netGroup_step_iff] at hg
    rcases hg with ⟨rfl, e, hpre⟩ | hpre
    · exact hybridImplN_of_netEvt P e hpre
    · rw [hybridImpl_eqN, System.abstract_step]
      exact Or.inr ⟨hn, hybridPreN_of_netPre P hpre⟩

/-- **The deployed system simulates into the hybrid** along the graph of the
deflation. -/
noncomputable def netSim (P : Params) :
    ProbabilisticForwardSimulation (netFlat P) (hybridImpl P)
      (fun s ν => ν = PMF.pure (deflNet s)) :=
  ProbabilisticForwardSimulation.ofStrongFunctional deflNet (deflNet_init P)
    (netForward P)

/-- **The deployed reading refines the hybrid**: every trace distribution
achievable by the `n` corruption-blind programs beside the network adversary
and the coin oracle is achievable by the monolithic hybrid. -/
theorem netFlat_refines (P : Params) :
    achievableTraceDists (netFlat P) ⊆ achievableTraceDists (hybridImpl P) :=
  (netSim P).achievableTraceDists_subset

end Net


namespace Net

/-! ### Building a deployed transition

The forward direction reads a deployed transition into its factors; the
converse must build one. Each builder below takes the participant's row, the
idle rows of the other processes, the network's row and the oracle's, and
returns the deployed transition on the label the flat table gives that joint
step. The oracle's successor is left arbitrary throughout: it is the one
factor whose transitions need not be Dirac, and it occupies the same
coordinate on both sides. -/

/-- A sub-protocol API label of the deployed group is a silent transition of
the deployed system. -/
theorem netFlat_of_hidden (P : Params)
    {q : (∀ _ : Fin P.n, ABANodeN P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n))}
    {l : Lab P.n} (hl : l ∈ Lab.hiddenAPI P.n)
    {μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (netGroup P).step q l μ) : (netFlat P).step q Lab.tau μ :=
  (netFlat_step_iff P _ _ _).mpr (Or.inl ⟨rfl, l, hl, h⟩)

/-- A label outside the sub-protocol API survives the outer hiding. -/
theorem netFlat_of_visible (P : Params)
    {q : (∀ _ : Fin P.n, ABANodeN P.n) × (NetState P.n × (ℕ → WCC.SpecState P.n))}
    {l : Lab P.n} (hl : l ∉ Lab.hiddenAPI P.n)
    {μ : PMF ((∀ _ : Fin P.n, ABANodeN P.n) ×
      (NetState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (netGroup P).step q l μ) : (netFlat P).step q l μ :=
  (netFlat_step_iff P _ _ _).mpr (Or.inr ⟨hl, h⟩)

/-- The oracle idles on a rendezvous label outside the pullback's domain. -/
theorem wccLift_idle (P : Params) (o : ℕ → WCC.SpecState P.n) {e : NetEvt P.n}
    (hφ : wccPull P.n (Sum.inr e) = none) :
    (wccLift P).step o (Sum.inr e) (PMF.pure o) :=
  (System.mapIdle_step_none hφ (PMF.pure o)).mpr rfl

/-- The oracle answers a rendezvous label the pullback carries into its own
alphabet. -/
theorem wccLift_of_pull (P : Params) {o : ℕ → WCC.SpecState P.n} {e : NetEvt P.n}
    {l : Lab P.n} (hφ : wccPull P.n (Sum.inr e) = some l)
    {ω : PMF (ℕ → WCC.SpecState P.n)} (hW : (WCC.specFamily P).step o l ω) :
    (wccLift P).step o (Sum.inr e) ω :=
  (System.mapIdle_step_some hφ ω).mpr hW

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

/-- Build a joint transition of the three factors on a rendezvous label, the
oracle's successor left arbitrary. -/
theorem netPre_event_stepW (P : Params) {u x : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} (e : NetEvt P.n)
    (hall : ∀ i, ABAProcStepN P i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : NetStep P w (Sum.inr e) (PMF.pure w'))
    (ho : (wccLift P).step o (Sum.inr e) ω) :
    (netPre P).step (u, w, o) (Sum.inr e)
      (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω)) := by
  rw [netPre, System.parallel_step]
  refine Or.inl ⟨by simp, PMF.pure x, prodPMF (PMF.pure w') ω,
    syncN_pure (by simp) hall, ?_, rfl⟩
  rw [System.parallel_step]
  exact Or.inl ⟨by simp, PMF.pure w', ω, hn, ho, rfl⟩

/-- A hidden rendezvous is a silent transition of the deployed group. -/
theorem netGroup_event_stepW (P : Params) {u x : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} (e : NetEvt P.n)
    (hall : ∀ i, ABAProcStepN P i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : NetStep P w (Sum.inr e) (PMF.pure w'))
    (ho : (wccLift P).step o (Sum.inr e) ω) :
    (netGroup P).step (u, w, o) Lab.tau
      (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω)) :=
  (netGroup_step_iff P _ _ _).mpr
    (Or.inl ⟨rfl, e, netPre_event_stepW P e hall hn ho⟩)

/-- A rendezvous with one moving process. -/
theorem netFlat_event_one (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} (e : NetEvt P.n) (id : Fin P.n)
    {nd : ABANodeN P.n}
    (hown : ABAProcStepN P id (u id) (Sum.inr e) (PMF.pure nd))
    (hfor : ∀ i, i ≠ id → ABAProcStepN P i (u i) (Sum.inr e) (PMF.pure (u i)))
    (hn : NetStep P w (Sum.inr e) (PMF.pure w'))
    (ho : (wccLift P).step o (Sum.inr e) ω) :
    (netFlat P).step (u, w, o) Lab.tau
      (prodPMF (PMF.pure (Function.update u id nd)) (prodPMF (PMF.pure w') ω)) :=
  netFlat_of_visible P (by simp)
    (netGroup_event_stepW P e (procsN_family id nd hown hfor) hn ho)

/-- A rendezvous no process participates in. -/
theorem netFlat_event_all (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} (e : NetEvt P.n)
    (hall : ∀ i, ABAProcStepN P i (u i) (Sum.inr e) (PMF.pure (u i)))
    (hn : NetStep P w (Sum.inr e) (PMF.pure w'))
    (ho : (wccLift P).step o (Sum.inr e) ω) :
    (netFlat P).step (u, w, o) Lab.tau
      (prodPMF (PMF.pure u) (prodPMF (PMF.pure w') ω)) :=
  netFlat_of_visible P (by simp) (netGroup_event_stepW P e hall hn ho)

/-- A sub-protocol API handshake with one moving process. -/
theorem netFlat_labH_one (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} {l : Lab P.n}
    (hl : l ∈ Lab.hiddenAPI P.n) (hlt : l ≠ Lab.tau) (id : Fin P.n)
    {nd : ABANodeN P.n}
    (hown : ABAProcStepN P id (u id) (Sum.inl l) (PMF.pure nd))
    (hfor : ∀ i, i ≠ id → ABAProcStepN P i (u i) (Sum.inl l) (PMF.pure (u i)))
    (hn : NetStep P w (Sum.inl l) (PMF.pure w'))
    (hW : (WCC.specFamily P).step o l ω) :
    (netFlat P).step (u, w, o) Lab.tau
      (prodPMF (PMF.pure (Function.update u id nd)) (prodPMF (PMF.pure w') ω)) :=
  netFlat_of_hidden P hl
    (netGroup_lab_step P hlt (procsN_family id nd hown hfor) hn hW)

/-- A sub-protocol API handshake no process participates in. -/
theorem netFlat_labH_all (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} {l : Lab P.n}
    (hl : l ∈ Lab.hiddenAPI P.n) (hlt : l ≠ Lab.tau)
    (hall : ∀ i, ABAProcStepN P i (u i) (Sum.inl l) (PMF.pure (u i)))
    (hn : NetStep P w (Sum.inl l) (PMF.pure w'))
    (hW : (WCC.specFamily P).step o l ω) :
    (netFlat P).step (u, w, o) Lab.tau
      (prodPMF (PMF.pure u) (prodPMF (PMF.pure w') ω)) :=
  netFlat_of_hidden P hl (netGroup_lab_step P hlt hall hn hW)

/-- A surviving visible handshake with one moving process. -/
theorem netFlat_labV_one (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} {l : Lab P.n}
    (hl : l ∉ Lab.hiddenAPI P.n) (hlt : l ≠ Lab.tau) (id : Fin P.n)
    {nd : ABANodeN P.n}
    (hown : ABAProcStepN P id (u id) (Sum.inl l) (PMF.pure nd))
    (hfor : ∀ i, i ≠ id → ABAProcStepN P i (u i) (Sum.inl l) (PMF.pure (u i)))
    (hn : NetStep P w (Sum.inl l) (PMF.pure w'))
    (hW : (WCC.specFamily P).step o l ω) :
    (netFlat P).step (u, w, o) l
      (prodPMF (PMF.pure (Function.update u id nd)) (prodPMF (PMF.pure w') ω)) :=
  netFlat_of_visible P hl
    (netGroup_lab_step P hlt (procsN_family id nd hown hfor) hn hW)

/-- A surviving visible handshake no process moves on. -/
theorem netFlat_labV_all (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} {l : Lab P.n}
    (hl : l ∉ Lab.hiddenAPI P.n) (hlt : l ≠ Lab.tau)
    (hall : ∀ i, ABAProcStepN P i (u i) (Sum.inl l) (PMF.pure (u i)))
    (hn : NetStep P w (Sum.inl l) (PMF.pure w'))
    (hW : (WCC.specFamily P).step o l ω) :
    (netFlat P).step (u, w, o) l
      (prodPMF (PMF.pure u) (prodPMF (PMF.pure w') ω)) :=
  netFlat_of_visible P hl (netGroup_lab_step P hlt hall hn hW)

/-- A network-local injection. -/
theorem netFlat_tau_net (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    (hn : NetStep P w (Sum.inl .tau) (PMF.pure w')) :
    (netFlat P).step (u, w, o) Lab.tau (PMF.pure (u, w', o)) :=
  netFlat_of_visible P (by simp) (netGroup_tau_net P hn)

/-- The coin resolution. -/
theorem netFlat_tau_wcc (P : Params) {u : ∀ _ : Fin P.n, ABANodeN P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)}
    (hW : (WCC.specFamily P).step o Lab.tau ω) :
    (netFlat P).step (u, w, o) Lab.tau
      (prodPMF (PMF.pure u) (prodPMF (PMF.pure w) ω)) :=
  netFlat_of_visible P (by simp) (netGroup_tau_wcc P hW)

end Net


namespace Net

/-! ### Reading a monolithic transition into its factors

The converse-direction readers of the three monolithic factors. The stage
family and the round loop are Dirac, so their successors are pinned; the coin
oracle's is carried along as it stands. -/

/-- The stage family idles on a label no instance owns and no broadcast. -/
theorem implFamilyN_idle_inv (P : Params) {S : ℕ → GBCA.ImplState P.n}
    {l : Lab P.n} (hl : l ≠ Lab.tau) (hr : Lab.gbcaRound l = none)
    (hf : ¬ Lab.isFail l) {μ : PMF (ℕ → GBCA.ImplState P.n)}
    (h : (GBCA.implFamily P).step S l μ) : μ = PMF.pure S := by
  rw [GBCA.implFamily, System.family_step_iff] at h
  rcases h with ⟨habs, -⟩ | ⟨r, hown, -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
  · exact absurd habs hl
  · rw [hr] at hown; exact absurd hown (by simp)
  · exact absurd hglob hf
  · rfl

/-- The round-`r` instance answers a label it owns. -/
theorem implFamilyN_owned_inv (P : Params) {S : ℕ → GBCA.ImplState P.n}
    {l : Lab P.n} {r : ℕ} (hr : Lab.gbcaRound l = some r) (hl : l ≠ Lab.tau)
    {μ : PMF (ℕ → GBCA.ImplState P.n)} (h : (GBCA.implFamily P).step S l μ) :
    ∃ μr, GBCA.ImplStep P r (S r) l μr ∧ μ = μr.map (Function.update S r) := by
  rw [GBCA.implFamily, System.family_step_iff] at h
  rcases h with ⟨habs, -⟩ | ⟨r', hown, μr, hstep, rfl⟩ | ⟨-, hown, -, -⟩ |
    ⟨-, hown, -, -⟩
  · exact absurd habs hl
  · have hrr : r' = r := by rw [hr] at hown; exact (Option.some.inj hown).symm
    subst hrr
    exact ⟨μr, hstep, rfl⟩
  · rw [hr] at hown; exact absurd hown (by simp)
  · rw [hr] at hown; exact absurd hown (by simp)

/-- A silent transition of the stage family is one instance's own silent
rule. -/
theorem implFamilyN_tau_inv (P : Params) {S : ℕ → GBCA.ImplState P.n}
    {μ : PMF (ℕ → GBCA.ImplState P.n)}
    (h : (GBCA.implFamily P).step S Lab.tau μ) :
    ∃ (r : ℕ) (μr : PMF (GBCA.ImplState P.n)),
      GBCA.ImplStep P r (S r) Lab.tau μr ∧ μ = μr.map (Function.update S r) := by
  rw [GBCA.implFamily, System.family_step_iff] at h
  rcases h with ⟨-, r, μr, hstep, rfl⟩ | ⟨r, hown, -⟩ | ⟨habs, -, -, -⟩ |
    ⟨habs, -, -, -⟩
  · exact ⟨r, μr, hstep, rfl⟩
  · exact absurd hown (by simp [Lab.gbcaRound])
  · exact absurd rfl habs
  · exact absurd rfl habs

/-- Corruption is broadcast to every instance. -/
theorem implFamilyN_fail_inv (P : Params) {S : ℕ → GBCA.ImplState P.n}
    (k : Fin P.n) {μ : PMF (ℕ → GBCA.ImplState P.n)}
    (h : (GBCA.implFamily P).step S (.fail k) μ) :
    μ = PMF.pure (fun r => (S r).corrupt P k) := by
  rw [GBCA.implFamily, System.family_step_iff] at h
  rcases h with ⟨habs, -⟩ | ⟨r, hown, -⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, hglob, -⟩
  · exact absurd habs (by simp)
  · exact absurd hown (by simp [Lab.gbcaRound])
  · rfl
  · exact absurd trivial hglob

/-- The coin family idles on a label no instance owns and no broadcast. -/
theorem wccFamilyN_idle_inv (P : Params) {o : ℕ → WCC.SpecState P.n}
    {l : Lab P.n} (hl : l ≠ Lab.tau) (hr : Lab.wccRound l = none)
    (hf : ¬ Lab.isFail l) {ω : PMF (ℕ → WCC.SpecState P.n)}
    (h : (WCC.specFamily P).step o l ω) : ω = PMF.pure o := by
  rw [WCC.specFamily, System.family_step_iff] at h
  rcases h with ⟨habs, -⟩ | ⟨r, hown, -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
  · exact absurd habs hl
  · rw [hr] at hown; exact absurd hown (by simp)
  · exact absurd hglob hf
  · rfl

/-- A visible transition of the monolithic hybrid before the outer hiding:
the three factors move together. -/
theorem hybridPreN_lab_inv (P : Params) {S : ℕ → GBCA.ImplState P.n}
    {C : CoreState P.n} {o : ℕ → WCC.SpecState P.n} {l : Lab P.n}
    (hl : l ≠ Lab.tau)
    {μ : PMF ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (hybridPreN P).step (S, C, o) l μ) :
    ∃ (μ₁ : PMF (ℕ → GBCA.ImplState P.n)) (μ₂ : PMF (CoreState P.n))
      (ω : PMF (ℕ → WCC.SpecState P.n)),
      (GBCA.implFamily P).step S l μ₁ ∧ CoreStep P C l μ₂ ∧
      (WCC.specFamily P).step o l ω ∧ μ = prodPMF μ₁ (prodPMF μ₂ ω) := by
  rw [hybridPreN, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂₃, hI, hCW, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
  · rw [context, System.parallel_step] at hCW
    rcases hCW with ⟨-, μ₂, ω, hC, hW, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
    · exact ⟨μ₁, μ₂, ω, hI, hC, hW, rfl⟩
    · exact absurd habs hl
    · exact absurd habs hl
  · exact absurd habs hl
  · exact absurd habs hl

/-- A silent transition of the monolithic hybrid before the outer hiding: one
factor's own silent rule. -/
theorem hybridPreN_tau_inv (P : Params) {S : ℕ → GBCA.ImplState P.n}
    {C : CoreState P.n} {o : ℕ → WCC.SpecState P.n}
    {μ : PMF ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (hybridPreN P).step (S, C, o) Lab.tau μ) :
    (∃ (r : ℕ) (μr : PMF (GBCA.ImplState P.n)),
        GBCA.ImplStep P r (S r) Lab.tau μr ∧
        μ = prodPMF (μr.map (Function.update S r)) (PMF.pure (C, o))) ∨
    (∃ μ₂, CoreStep P C Lab.tau μ₂ ∧
        μ = prodPMF (PMF.pure S) (prodPMF μ₂ (PMF.pure o))) ∨
    (∃ ω, (WCC.specFamily P).step o Lab.tau ω ∧
        μ = prodPMF (PMF.pure S) (prodPMF (PMF.pure C) ω)) := by
  rw [hybridPreN, System.parallel_step] at h
  rcases h with ⟨habs, -⟩ | ⟨-, μ₁, hI, rfl⟩ | ⟨-, μ₂₃, hCW, rfl⟩
  · exact absurd rfl habs
  · obtain ⟨r, μr, hstep, rfl⟩ := implFamilyN_tau_inv P hI
    exact Or.inl ⟨r, μr, hstep, rfl⟩
  · rw [context, System.parallel_step] at hCW
    rcases hCW with ⟨habs, -⟩ | ⟨-, μ₂, hC, rfl⟩ | ⟨-, ω, hW, rfl⟩
    · exact absurd rfl habs
    · exact Or.inr (Or.inl ⟨μ₂, hC, rfl⟩)
    · exact Or.inr (Or.inr ⟨ω, hW, rfl⟩)

end Net


namespace Net

/-! ### The converse, label class by label class

Each lemma below answers one label of the monolithic hybrid with the deployed
transition the flat table gives it. The state is an arbitrary deployed state:
no reachability and no invariant is used anywhere — every copy of the
corrupted set the monolithic state carries is literally the network's, so the
Byzantine guards translate definitionally. -/

/-- The coin return. The monolithic rule publishes `⟨DECIDED, b⟩` exactly when
the round's grade was `A b` (D10), and the deployed table splits accordingly:
the fused case is the rendezvous `retWPub`, which carries the payload to the
network, the unfused case the shared `retW`. -/
theorem netConverse_retW (P : Params) (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) (r : ℕ) (id : Fin P.n)
    (c : Bool)
    {μ : PMF ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (hybridPreN P).step ((fun r' => deflStageN u w r'), deflCoreN u w, o)
      (Lab.retW r id c) μ) :
    ∃ ν, (netFlat P).step (u, w, o) Lab.tau ν ∧ μ = ν.map deflNet := by
  obtain ⟨μ₁, μ₂, ω, hI, hC, hW, rfl⟩ := hybridPreN_lab_inv P (by simp) h
  obtain rfl := implFamilyN_idle_inv P (l := Lab.retW r id c) (by simp) rfl not_false hI
  cases hC
  case retW =>
    rename_i hph hr
    cases hlg : (u id).1.proc.lastGrade with
    | some out =>
      cases out with
      | A b =>
        refine ⟨_, netFlat_event_one P (.retWPub r id c b) id
          (ABAProcStepN.retWPub (u id).1 (u id).2 r c b hph hr hlg)
          (fun i hi => ABAProcStepN.retWPubIdle (u i).1 (u i).2 r id c b
            (Ne.symm hi))
          (NetStep.retWPub w r id c b)
          (wccLift_of_pull P (wccPull_retWPub r id c b) hW), ?_⟩
        rw [map_deflNet_prod, deflStagesN_core u w (w.dput id b) id _ rfl rfl,
          deflCoreN_stepRound_pub u w id c b hlg]
      | B v =>
        have hgr : ∀ v' : Bool, (u id).1.proc.lastGrade ≠ some (.A v') := by
          intro v'; rw [hlg]; simp
        refine ⟨_, netFlat_labH_one P (by simp) (by simp) id
          (ABAProcStepN.retW (u id).1 (u id).2 r c hph hr hgr)
          (fun i hi => ABAProcStepN.retWIdle (u i).1 (u i).2 r id c (Ne.symm hi))
          (NetStep.retWIdle w r id c) hW, ?_⟩
        rw [map_deflNet_prod, deflStagesN_core u w w id _ rfl rfl,
          deflCoreN_stepRound_plain u w id c hgr]
      | C =>
        have hgr : ∀ v' : Bool, (u id).1.proc.lastGrade ≠ some (.A v') := by
          intro v'; rw [hlg]; simp
        refine ⟨_, netFlat_labH_one P (by simp) (by simp) id
          (ABAProcStepN.retW (u id).1 (u id).2 r c hph hr hgr)
          (fun i hi => ABAProcStepN.retWIdle (u i).1 (u i).2 r id c (Ne.symm hi))
          (NetStep.retWIdle w r id c) hW, ?_⟩
        rw [map_deflNet_prod, deflStagesN_core u w w id _ rfl rfl,
          deflCoreN_stepRound_plain u w id c hgr]
    | none =>
      have hgr : ∀ v' : Bool, (u id).1.proc.lastGrade ≠ some (.A v') := by
        intro v'; rw [hlg]; simp
      refine ⟨_, netFlat_labH_one P (by simp) (by simp) id
        (ABAProcStepN.retW (u id).1 (u id).2 r c hph hr hgr)
        (fun i hi => ABAProcStepN.retWIdle (u i).1 (u i).2 r id c (Ne.symm hi))
        (NetStep.retWIdle w r id c) hW, ?_⟩
      rw [map_deflNet_prod, deflStagesN_core u w w id _ rfl rfl,
        deflCoreN_stepRound_plain u w id c hgr]
  case retWByz =>
    rename_i hF
    refine ⟨_, netFlat_event_all P (.byzRetW r id c)
      (fun i => ABAProcStepN.byzRetWIdle (u i).1 (u i).2 r id c)
      (NetStep.byzRetW w r id c hF)
      (wccLift_of_pull P (wccPull_byzRetW r id c) hW), ?_⟩
    rw [map_deflNet_prod]

/-- The graded-agreement call. The stage instance either opens on the call or
takes its input-enabledness loop, and the round loop either makes the honest
call or is driven by a corrupted process; the four combinations are the real
`callG`, the loop rendezvous, and the two Byzantine drives. -/
theorem netConverse_callG (P : Params) (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) (r : ℕ) (id : Fin P.n)
    (b : Bool)
    {μ : PMF ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (hybridPreN P).step ((fun r' => deflStageN u w r'), deflCoreN u w, o)
      (Lab.callG r id b) μ) :
    ∃ ν, (netFlat P).step (u, w, o) Lab.tau ν ∧ μ = ν.map deflNet := by
  obtain ⟨μ₁, μ₂, ω, hI, hC, hW, rfl⟩ := hybridPreN_lab_inv P (by simp) h
  obtain ⟨μr, hX, rfl⟩ :=
    implFamilyN_owned_inv P (l := Lab.callG r id b) (r := r) rfl (by simp) hI
  cases hX
  case call =>
    rename_i hin
    cases hC
    case callG =>
      rename_i hph hr hest
      refine ⟨_, netFlat_labH_one P (by simp) (by simp) id
        (ABAProcStepN.callG_call (u id).1 (u id).2 r b hph hr hest hin)
        (fun i hi => ABAProcStepN.callGIdle (u i).1 (u i).2 r id b (Ne.symm hi))
        (NetStep.callG w r id b) hW, ?_⟩
      rw [PMF.pure_map, map_deflNet_prod,
        deflStagesN_setP_mcast u w id _ r _ (.input b),
        deflCoreN_setProc u (w.gpool r id (.input b)) id _ _]
      rfl
    case callGByz =>
      rename_i hF
      obtain rfl :=
        wccFamilyN_idle_inv P (l := Lab.callG r id b) (by simp) rfl not_false hW
      refine ⟨_, netFlat_event_one P (.byzCallG r id b) id
        (ABAProcStepN.byzCallG (u id).1 (u id).2 r b hin)
        (fun i hi => ABAProcStepN.byzCallGIdle (u i).1 (u i).2 r id b (Ne.symm hi))
        (NetStep.byzCallG w r id b hF)
        (wccLift_idle P o (wccPull_byzCallG r id b)), ?_⟩
      rw [PMF.pure_map, map_deflNet_prod,
        deflStagesN_setP_mcast u w id _ r _ (.input b),
        deflCoreN_stage u w (w.gpool r id (.input b)) id _ rfl rfl]
      rfl
  case callLoop =>
    cases hC
    case callG =>
      rename_i hph hr hest
      obtain rfl :=
        wccFamilyN_idle_inv P (l := Lab.callG r id b) (by simp) rfl not_false hW
      refine ⟨_, netFlat_event_one P (.gcallLoop r id b) id
        (ABAProcStepN.gcallLoop (u id).1 (u id).2 r b hph hr hest)
        (fun i hi => ABAProcStepN.gcallLoopIdle (u i).1 (u i).2 r id b (Ne.symm hi))
        (NetStep.gcallLoop w r id b)
        (wccLift_idle P o (wccPull_gcallLoop r id b)), ?_⟩
      rw [PMF.pure_map, Function.update_eq_self, map_deflNet_prod,
        deflStagesN_core u w w id _ rfl rfl, deflCoreN_setProc u w id _ _]
      rfl
    case callGByz =>
      rename_i hF
      obtain rfl :=
        wccFamilyN_idle_inv P (l := Lab.callG r id b) (by simp) rfl not_false hW
      refine ⟨_, netFlat_event_all P (.byzCallGLoop r id b)
        (fun i => ABAProcStepN.byzCallGLoopIdle (u i).1 (u i).2 r id b)
        (NetStep.byzCallGLoop w r id b hF)
        (wccLift_idle P o (wccPull_byzCallGLoop r id b)), ?_⟩
      rw [PMF.pure_map, Function.update_eq_self, map_deflNet_prod]

/-- The graded-agreement return. The stage instance's three decide cases meet
the honest round-loop return and its Byzantine drive; the latter travels on
the rendezvous `byzRetG`, which carries the stage-side content alone. -/
theorem netConverse_retG (P : Params) (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) (r : ℕ) (id : Fin P.n)
    (out : GbcaOut)
    {μ : PMF ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (hybridPreN P).step ((fun r' => deflStageN u w r'), deflCoreN u w, o)
      (Lab.retG r id out) μ) :
    ∃ ν, (netFlat P).step (u, w, o) Lab.tau ν ∧ μ = ν.map deflNet := by
  obtain ⟨μ₁, μ₂, ω, hI, hC, hW, rfl⟩ := hybridPreN_lab_inv P (by simp) h
  obtain ⟨μr, hX, rfl⟩ :=
    implFamilyN_owned_inv P (l := Lab.retG r id out) (r := r) rfl (by simp) hI
  cases hX
  case retA =>
    rename_i v hcnt hret
    cases hC
    case retG =>
      rename_i hph hr
      refine ⟨_, netFlat_labH_one P (by simp) (by simp) id
        (ABAProcStepN.retG_A (u id).1 (u id).2 r v hph hr hcnt hret)
        (fun i hi => ABAProcStepN.retGIdle (u i).1 (u i).2 r id (.A v) (Ne.symm hi))
        (NetStep.retGIdle w r id (.A v)) hW, ?_⟩
      rw [PMF.pure_map, map_deflNet_prod, deflStagesN_setP u w id _ r _,
        deflCoreN_setProc u w id _ _]
      rfl
    case retGByz =>
      rename_i hF
      obtain rfl := wccFamilyN_idle_inv P (l := Lab.retG r id (.A v))
        (by simp) rfl not_false hW
      refine ⟨_, netFlat_event_one P (.byzRetG r id (.A v)) id
        (ABAProcStepN.byzRetG_A (u id).1 (u id).2 r v hcnt hret)
        (fun i hi =>
          ABAProcStepN.byzRetGIdle (u i).1 (u i).2 r id (.A v) (Ne.symm hi))
        (NetStep.byzRetG w r id (.A v) hF)
        (wccLift_idle P o (wccPull_byzRetG r id (.A v))), ?_⟩
      rw [PMF.pure_map, map_deflNet_prod, deflStagesN_setP u w id _ r _,
        deflCoreN_stage u w w id _ rfl rfl]
      rfl
  case retB =>
    rename_i v hcnt honce hbind hval hret
    cases hC
    case retG =>
      rename_i hph hr
      refine ⟨_, netFlat_labH_one P (by simp) (by simp) id
        (ABAProcStepN.retG_B (u id).1 (u id).2 r v hph hr hcnt honce hbind hval hret)
        (fun i hi => ABAProcStepN.retGIdle (u i).1 (u i).2 r id (.B v) (Ne.symm hi))
        (NetStep.retGIdle w r id (.B v)) hW, ?_⟩
      rw [PMF.pure_map, map_deflNet_prod, deflStagesN_setP u w id _ r _,
        deflCoreN_setProc u w id _ _]
      rfl
    case retGByz =>
      rename_i hF
      obtain rfl := wccFamilyN_idle_inv P (l := Lab.retG r id (.B v))
        (by simp) rfl not_false hW
      refine ⟨_, netFlat_event_one P (.byzRetG r id (.B v)) id
        (ABAProcStepN.byzRetG_B (u id).1 (u id).2 r v hcnt honce hbind hval hret)
        (fun i hi =>
          ABAProcStepN.byzRetGIdle (u i).1 (u i).2 r id (.B v) (Ne.symm hi))
        (NetStep.byzRetG w r id (.B v) hF)
        (wccLift_idle P o (wccPull_byzRetG r id (.B v))), ?_⟩
      rw [PMF.pure_map, map_deflNet_prod, deflStagesN_setP u w id _ r _,
        deflCoreN_stage u w w id _ rfl rfl]
      rfl
  case retC =>
    rename_i hcnt hval hret
    cases hC
    case retG =>
      rename_i hph hr
      refine ⟨_, netFlat_labH_one P (by simp) (by simp) id
        (ABAProcStepN.retG_C (u id).1 (u id).2 r hph hr hcnt hval hret)
        (fun i hi => ABAProcStepN.retGIdle (u i).1 (u i).2 r id .C (Ne.symm hi))
        (NetStep.retGIdle w r id .C) hW, ?_⟩
      rw [PMF.pure_map, map_deflNet_prod, deflStagesN_setP u w id _ r _,
        deflCoreN_setProc u w id _ _]
      rfl
    case retGByz =>
      rename_i hF
      obtain rfl := wccFamilyN_idle_inv P (l := Lab.retG r id .C)
        (by simp) rfl not_false hW
      refine ⟨_, netFlat_event_one P (.byzRetG r id .C) id
        (ABAProcStepN.byzRetG_C (u id).1 (u id).2 r hcnt hval hret)
        (fun i hi => ABAProcStepN.byzRetGIdle (u i).1 (u i).2 r id .C (Ne.symm hi))
        (NetStep.byzRetG w r id .C hF)
        (wccLift_idle P o (wccPull_byzRetG r id .C)), ?_⟩
      rw [PMF.pure_map, map_deflNet_prod, deflStagesN_setP u w id _ r _,
        deflCoreN_stage u w w id _ rfl rfl]
      rfl

/-- The coin call: the honest handshake on the shared label, the Byzantine
drive on the rendezvous `byzCallW`, which the pullback carries onto the
oracle's own `callW` row. -/
theorem netConverse_callW (P : Params) (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) (r : ℕ) (id : Fin P.n)
    {μ : PMF ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (hybridPreN P).step ((fun r' => deflStageN u w r'), deflCoreN u w, o)
      (Lab.callW r id) μ) :
    ∃ ν, (netFlat P).step (u, w, o) Lab.tau ν ∧ μ = ν.map deflNet := by
  obtain ⟨μ₁, μ₂, ω, hI, hC, hW, rfl⟩ := hybridPreN_lab_inv P (by simp) h
  obtain rfl :=
    implFamilyN_idle_inv P (l := Lab.callW r id) (by simp) rfl not_false hI
  cases hC
  case callW =>
    rename_i hph hr
    refine ⟨_, netFlat_labH_one P (by simp) (by simp) id
      (ABAProcStepN.callW (u id).1 (u id).2 r hph hr)
      (fun i hi => ABAProcStepN.callWIdle (u i).1 (u i).2 r id (Ne.symm hi))
      (NetStep.callWIdle w r id) hW, ?_⟩
    rw [map_deflNet_prod, deflStagesN_core u w w id _ rfl rfl,
      deflCoreN_setProc u w id _ _]
    rfl
  case callWByz =>
    rename_i hF
    refine ⟨_, netFlat_event_all P (.byzCallW r id)
      (fun i => ABAProcStepN.byzCallWIdle (u i).1 (u i).2 r id)
      (NetStep.byzCallW w r id hF)
      (wccLift_of_pull P (wccPull_byzCallW r id) hW), ?_⟩
    rw [map_deflNet_prod]

/-- The external input. -/
theorem netConverse_callABA (P : Params) (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) (id : Fin P.n) (b : Bool)
    {μ : PMF ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (hybridPreN P).step ((fun r' => deflStageN u w r'), deflCoreN u w, o)
      (Lab.callABA id b) μ) :
    ∃ ν, (netFlat P).step (u, w, o) (Lab.callABA id b) ν ∧ μ = ν.map deflNet := by
  obtain ⟨μ₁, μ₂, ω, hI, hC, hW, rfl⟩ := hybridPreN_lab_inv P (by simp) h
  obtain rfl :=
    implFamilyN_idle_inv P (l := Lab.callABA id b) (by simp) rfl not_false hI
  rw [coreStep_callABA_iff] at hC
  rcases hC with ⟨hin, rfl⟩ | rfl
  · refine ⟨_, netFlat_labV_one P (by simp) (by simp) id
      (ABAProcStepN.input (u id).1 (u id).2 b hin)
      (fun i hi => ABAProcStepN.callABAIdle (u i).1 (u i).2 id b (Ne.symm hi))
      (NetStep.callABAIdle w id b) hW, ?_⟩
    rw [map_deflNet_prod, deflStagesN_core u w w id _ rfl rfl,
      deflCoreN_setProc u w id _ _]
    rfl
  · have hall : ∀ i, ABAProcStepN P i (u i) (Sum.inl (Lab.callABA id b))
        (PMF.pure (u i)) := by
      intro i
      by_cases hi : i = id
      · subst hi; exact ABAProcStepN.inputLoop (u i).1 (u i).2 b
      · exact ABAProcStepN.callABAIdle (u i).1 (u i).2 id b (Ne.symm hi)
    refine ⟨_, netFlat_labV_all P (by simp) (by simp) hall
      (NetStep.callABAIdle w id b) hW, ?_⟩
    rw [map_deflNet_prod]

/-- The ABA return: the `n − f` DECIDED quorum is the node's condition, having
published the payload oneself the network's (D12′). -/
theorem netConverse_retABA (P : Params) (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) (id : Fin P.n) (b : Bool)
    {μ : PMF ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (hybridPreN P).step ((fun r' => deflStageN u w r'), deflCoreN u w, o)
      (Lab.retABA id b) μ) :
    ∃ ν, (netFlat P).step (u, w, o) (Lab.retABA id b) ν ∧ μ = ν.map deflNet := by
  obtain ⟨μ₁, μ₂, ω, hI, hC, hW, rfl⟩ := hybridPreN_lab_inv P (by simp) h
  obtain rfl :=
    implFamilyN_idle_inv P (l := Lab.retABA id b) (by simp) rfl not_false hI
  rw [coreStep_retABA_iff] at hC
  obtain ⟨hcnt, hs, hret, rfl⟩ := hC
  refine ⟨_, netFlat_labV_one P (by simp) (by simp) id
    (ABAProcStepN.ret (u id).1 (u id).2 b hcnt hret)
    (fun i hi => ABAProcStepN.retABAIdle (u i).1 (u i).2 id b (Ne.symm hi))
    (NetStep.retABA w id b hs) hW, ?_⟩
  rw [map_deflNet_prod, deflStagesN_core u w w id _ rfl rfl,
    deflCoreN_setProc u w id _ _]
  rfl

/-- Corruption (D1): the budget lives in the network alone, and the three
copies of the corrupted set the monolithic state carries are that one set. -/
theorem netConverse_fail (P : Params) (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) (k : Fin P.n)
    {μ : PMF ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (hybridPreN P).step ((fun r' => deflStageN u w r'), deflCoreN u w, o)
      (Lab.fail k) μ) :
    ∃ ν, (netFlat P).step (u, w, o) (Lab.fail k) ν ∧ μ = ν.map deflNet := by
  obtain ⟨μ₁, μ₂, ω, hI, hC, hW, rfl⟩ := hybridPreN_lab_inv P (by simp) h
  obtain rfl := implFamilyN_fail_inv P k hI
  rw [coreStep_fail_iff] at hC
  subst hC
  refine ⟨_, netFlat_labV_all P (by simp) (by simp)
    (fun i => ABAProcStepN.failIdle (u i).1 (u i).2 k) (NetStep.fail w k) hW, ?_⟩
  rw [map_deflNet_prod,
    show (fun r => deflStageN u (NetState.corrupt P k w) r)
        = fun r => (deflStageN u w r).corrupt P k from
      funext (fun r => deflStageN_corrupt u w k r),
    deflCoreN_corrupt u w k]

/-- A silent rule of the round-`r` stage instance. The nine multicast and
delivery rules are joint steps of a node and the network; the Byzantine
injection is the network's own, no node taking part. -/
theorem netConverse_tau_impl (P : Params) (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) (r : ℕ)
    {μr : PMF (GBCA.ImplState P.n)}
    (hX : GBCA.ImplStep P r (deflStageN u w r) Lab.tau μr) :
    ∃ ν, (netFlat P).step (u, w, o) Lab.tau ν ∧
      prodPMF (μr.map (Function.update (fun r' => deflStageN u w r') r))
        (PMF.pure (deflCoreN u w, o)) = ν.map deflNet := by
  cases hX
  case deliver =>
    rename_i i j m hm
    refine ⟨_, netFlat_event_one P (.gdlv r i j m) i
      (ABAProcStepN.gdlvRecv (u i).1 (u i).2 r j m)
      (fun i' hi => ABAProcStepN.gdlvIdle (u i').1 (u i').2 r i j m (Ne.symm hi))
      (NetStep.gdlv w r i j m hm)
      (wccLift_idle P o (wccPull_gdlv r i j m)), ?_⟩
    simp only [PMF.pure_map, prodPMF_pure_pure, deflNet_apply]
    rw [deflStagesN_deliverTo u w i _ r j m, deflCoreN_stage u w w i _ rfl rfl]
  case relay =>
    rename_i j b hin hcnt hsend
    refine ⟨_, netFlat_event_one P (.gsnd r j (.input b)) j
      (ABAProcStepN.gsndRelay (u j).1 (u j).2 r b hin hcnt hsend)
      (fun i hi => ABAProcStepN.gsndIdle (u i).1 (u i).2 r j (.input b) (Ne.symm hi))
      (NetStep.gsnd w r j (.input b))
      (wccLift_idle P o (wccPull_gsnd r j (.input b))), ?_⟩
    simp only [PMF.pure_map, prodPMF_pure_pure, deflNet_apply]
    rw [deflStagesN_setP_mcast u w j _ r _ (.input b),
      deflCoreN_stage u w (w.gpool r j (.input b)) j _ rfl rfl]
    rfl
  case echo =>
    rename_i j b hin hcnt hsend
    refine ⟨_, netFlat_event_one P (.gsnd r j (.echo b)) j
      (ABAProcStepN.gsndEcho (u j).1 (u j).2 r b hin hcnt hsend)
      (fun i hi => ABAProcStepN.gsndIdle (u i).1 (u i).2 r j (.echo b) (Ne.symm hi))
      (NetStep.gsnd w r j (.echo b))
      (wccLift_idle P o (wccPull_gsnd r j (.echo b))), ?_⟩
    simp only [PMF.pure_map, prodPMF_pure_pure, deflNet_apply]
    rw [deflStagesN_setP_mcast u w j _ r _ (.echo b),
      deflCoreN_stage u w (w.gpool r j (.echo b)) j _ rfl rfl]
    rfl
  case voteBit =>
    rename_i j b hin hcnt hsend
    refine ⟨_, netFlat_event_one P (.gsnd r j (.vote (some b))) j
      (ABAProcStepN.gsndVoteBit (u j).1 (u j).2 r b hin hcnt hsend)
      (fun i hi =>
        ABAProcStepN.gsndIdle (u i).1 (u i).2 r j (.vote (some b)) (Ne.symm hi))
      (NetStep.gsnd w r j (.vote (some b)))
      (wccLift_idle P o (wccPull_gsnd r j (.vote (some b)))), ?_⟩
    simp only [PMF.pure_map, prodPMF_pure_pure, deflNet_apply]
    rw [deflStagesN_setP_mcast u w j _ r _ (.vote (some b)),
      deflCoreN_stage u w (w.gpool r j (.vote (some b))) j _ rfl rfl]
    rfl
  case voteBot =>
    rename_i j hin hcnt hval hsend
    refine ⟨_, netFlat_event_one P (.gsnd r j (.vote none)) j
      (ABAProcStepN.gsndVoteBot (u j).1 (u j).2 r hin hcnt hval hsend)
      (fun i hi =>
        ABAProcStepN.gsndIdle (u i).1 (u i).2 r j (.vote none) (Ne.symm hi))
      (NetStep.gsnd w r j (.vote none))
      (wccLift_idle P o (wccPull_gsnd r j (.vote none))), ?_⟩
    simp only [PMF.pure_map, prodPMF_pure_pure, deflNet_apply]
    rw [deflStagesN_setP_mcast u w j _ r _ (.vote none),
      deflCoreN_stage u w (w.gpool r j (.vote none)) j _ rfl rfl]
    rfl
  case bindBit =>
    rename_i j b hin hcnt hsend
    refine ⟨_, netFlat_event_one P (.gsnd r j (.bind (some b))) j
      (ABAProcStepN.gsndBindBit (u j).1 (u j).2 r b hin hcnt hsend)
      (fun i hi =>
        ABAProcStepN.gsndIdle (u i).1 (u i).2 r j (.bind (some b)) (Ne.symm hi))
      (NetStep.gsnd w r j (.bind (some b)))
      (wccLift_idle P o (wccPull_gsnd r j (.bind (some b)))), ?_⟩
    simp only [PMF.pure_map, prodPMF_pure_pure, deflNet_apply]
    rw [deflStagesN_setP_mcast u w j _ r _ (.bind (some b)),
      deflCoreN_stage u w (w.gpool r j (.bind (some b))) j _ rfl rfl]
    rfl
  case bindBot =>
    rename_i j hin hcnt hval hsend
    refine ⟨_, netFlat_event_one P (.gsnd r j (.bind none)) j
      (ABAProcStepN.gsndBindBot (u j).1 (u j).2 r hin hcnt hval hsend)
      (fun i hi =>
        ABAProcStepN.gsndIdle (u i).1 (u i).2 r j (.bind none) (Ne.symm hi))
      (NetStep.gsnd w r j (.bind none))
      (wccLift_idle P o (wccPull_gsnd r j (.bind none))), ?_⟩
    simp only [PMF.pure_map, prodPMF_pure_pure, deflNet_apply]
    rw [deflStagesN_setP_mcast u w j _ r _ (.bind none),
      deflCoreN_stage u w (w.gpool r j (.bind none)) j _ rfl rfl]
    rfl
  case sealBit =>
    rename_i j b hin hcnt hsend
    refine ⟨_, netFlat_event_one P (.gsnd r j (.seal (some b))) j
      (ABAProcStepN.gsndSealBit (u j).1 (u j).2 r b hin hcnt hsend)
      (fun i hi =>
        ABAProcStepN.gsndIdle (u i).1 (u i).2 r j (.seal (some b)) (Ne.symm hi))
      (NetStep.gsnd w r j (.seal (some b)))
      (wccLift_idle P o (wccPull_gsnd r j (.seal (some b)))), ?_⟩
    simp only [PMF.pure_map, prodPMF_pure_pure, deflNet_apply]
    rw [deflStagesN_setP_mcast u w j _ r _ (.seal (some b)),
      deflCoreN_stage u w (w.gpool r j (.seal (some b))) j _ rfl rfl]
    rfl
  case sealBot =>
    rename_i j hin hcnt hval hsend
    refine ⟨_, netFlat_event_one P (.gsnd r j (.seal none)) j
      (ABAProcStepN.gsndSealBot (u j).1 (u j).2 r hin hcnt hval hsend)
      (fun i hi =>
        ABAProcStepN.gsndIdle (u i).1 (u i).2 r j (.seal none) (Ne.symm hi))
      (NetStep.gsnd w r j (.seal none))
      (wccLift_idle P o (wccPull_gsnd r j (.seal none))), ?_⟩
    simp only [PMF.pure_map, prodPMF_pure_pure, deflNet_apply]
    rw [deflStagesN_setP_mcast u w j _ r _ (.seal none),
      deflCoreN_stage u w (w.gpool r j (.seal none)) j _ rfl rfl]
    rfl
  case byz =>
    rename_i j m hF
    refine ⟨_, netFlat_tau_net P (NetStep.byzG w r j m hF), ?_⟩
    simp only [PMF.pure_map, prodPMF_pure_pure, deflNet_apply]
    rw [deflStagesN_mcast u w r j m]
    rfl

/-- A silent rule of the round loop: the two DECIDED-layer rendezvous and the
network's own Byzantine injection (D12′). -/
theorem netConverse_tau_core (P : Params) (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) {μ₂ : PMF (CoreState P.n)}
    (hC : CoreStep P (deflCoreN u w) Lab.tau μ₂) :
    ∃ ν, (netFlat P).step (u, w, o) Lab.tau ν ∧
      prodPMF (PMF.pure (fun r' => deflStageN u w r'))
        (prodPMF μ₂ (PMF.pure o)) = ν.map deflNet := by
  rw [coreStep_tau_iff] at hC
  rcases hC with ⟨i, j, b, hs, hr, rfl⟩ | ⟨id, b, hcnt, hs, rfl⟩ | ⟨id, b, hF, rfl⟩
  · refine ⟨_, netFlat_event_one P (.ddlv i j b) i
      (ABAProcStepN.ddlvRecv (u i).1 (u i).2 j b hr)
      (fun i' hi => ABAProcStepN.ddlvIdle (u i').1 (u i').2 i j b (Ne.symm hi))
      (NetStep.ddlv w i j b hs)
      (wccLift_idle P o (wccPull_ddlv i j b)), ?_⟩
    simp only [PMF.pure_map, prodPMF_pure_pure, deflNet_apply]
    rw [deflStagesN_core u w w i _ rfl rfl, deflCoreN_recvDec u w i _ j b]
  · have hall : ∀ i, ABAProcStepN P i (u i) (Sum.inr (NetEvt.dsnd id b))
        (PMF.pure (u i)) := by
      intro i
      by_cases hi : i = id
      · subst hi; exact ABAProcStepN.dsndRelay (u i).1 (u i).2 b hcnt
      · exact ABAProcStepN.dsndIdle (u i).1 (u i).2 id b (Ne.symm hi)
    refine ⟨_, netFlat_event_all P (.dsnd id b) hall (NetStep.dsnd w id b hs)
      (wccLift_idle P o (wccPull_dsnd id b)), ?_⟩
    simp only [PMF.pure_map, prodPMF_pure_pure, deflNet_apply]
    rw [deflCoreN_dput u w id b]
    rfl
  · refine ⟨_, netFlat_tau_net P (NetStep.byzD w id b hF), ?_⟩
    simp only [PMF.pure_map, prodPMF_pure_pure, deflNet_apply]
    rw [deflCoreN_dput u w id b]
    rfl

/-- The silent label: one factor's own silent rule. The coin resolution — the
one row of the composite that is not Dirac — passes through untouched, the
oracle occupying the same coordinate on both sides. -/
theorem netConverse_tau (P : Params) (u : ∀ _ : Fin P.n, ABANodeN P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n)
    {μ : PMF ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (hybridPreN P).step ((fun r' => deflStageN u w r'), deflCoreN u w, o)
      Lab.tau μ) :
    ∃ ν, (netFlat P).step (u, w, o) Lab.tau ν ∧ μ = ν.map deflNet := by
  rcases hybridPreN_tau_inv P h with ⟨r, μr, hX, rfl⟩ | ⟨μ₂, hC, rfl⟩ |
    ⟨ω, hW, rfl⟩
  · exact netConverse_tau_impl P u w o r hX
  · exact netConverse_tau_core P u w o hC
  · refine ⟨_, netFlat_tau_wcc P hW, ?_⟩
    rw [map_deflNet_prod]

end Net


namespace Net

/-! ### The converse simulation and the equality of trace distributions

The deflation reflects transitions as well as it preserves them: every
transition of the monolithic hybrid out of a deflated state is the image of a
transition of the deployed system. With the forward matching of the previous
section this makes the deflation a step-*bi*simulating state map, and the two
soundness inclusions close the two halves of an equality. -/

/-- **The converse matching**: every transition of the monolithic hybrid out of
a deflated state is a transition of the deployed system, its successor
distribution pushed forward along the deflation. The state is arbitrary — no
reachability and no invariant enters. -/
theorem netConverse (P : Params) :
    ∀ q l μ, (hybridImpl P).step (deflNet q) l μ →
      ∃ ν, (netFlat P).step q l ν ∧ μ = ν.map deflNet := by
  rintro ⟨u, w, o⟩ l μ h
  have h' : ((hybridPreN P).abstract (Lab.hiddenAPI P.n)).step
      ((fun r' => deflStageN u w r'), deflCoreN u w, o) l μ := h
  rw [System.abstract_step] at h'
  rcases h' with ⟨rfl, l', hl', hpre⟩ | ⟨hl, hpre⟩
  · cases l' with
    | tau => exact absurd hl' (by simp)
    | callABA id b => exact absurd hl' (by simp)
    | retABA id b => exact absurd hl' (by simp)
    | callG r id b => exact netConverse_callG P u w o r id b hpre
    | retG r id out => exact netConverse_retG P u w o r id out hpre
    | callW r id => exact netConverse_callW P u w o r id hpre
    | retW r id c => exact netConverse_retW P u w o r id c hpre
    | fail k => exact absurd hl' (by simp)
  · cases l with
    | tau => exact netConverse_tau P u w o hpre
    | callABA id b => exact netConverse_callABA P u w o id b hpre
    | retABA id b => exact netConverse_retABA P u w o id b hpre
    | callG r id b => exact absurd (Lab.callG_mem_hiddenAPI r id b) hl
    | retG r id out => exact absurd (Lab.retG_mem_hiddenAPI r id out) hl
    | callW r id => exact absurd (Lab.callW_mem_hiddenAPI r id) hl
    | retW r id c => exact absurd (Lab.retW_mem_hiddenAPI r id c) hl
    | fail k => exact netConverse_fail P u w o k hpre

/-- **The hybrid simulates into the deployed system** along the converse of
the graph of the deflation. -/
noncomputable def netSimConverse (P : Params) :
    ProbabilisticForwardSimulation (hybridImpl P) (netFlat P)
      (fun p ν => ∃ q, ν = PMF.pure q ∧ p = deflNet q) :=
  ProbabilisticForwardSimulation.ofStrongFunctional_converse deflNet
    (deflNet_init P) (netConverse P)

/-- **The deployed reading is exact**: the `n` corruption-blind programs
beside the network adversary and the coin oracle achieve exactly the trace
distributions of the monolithic hybrid — no behaviour is added and none is
lost. -/
theorem netFlat_atd (P : Params) :
    achievableTraceDists (netFlat P) = achievableTraceDists (hybridImpl P) :=
  Set.Subset.antisymm (netSim P).achievableTraceDists_subset
    (netSimConverse P).achievableTraceDists_subset

/-! ### Headlines

The deployed reading inherits the safety of the monolithic hybrid without a
side condition: the corruption budget is a guard of the network adversary's
own `fail` row, so every deployed execution is in budget by construction and
nothing has to be assumed about the traces. -/

/-- **Safety of the deployed reading**: every positive-probability trace of
every achievable trace distribution of the `n` corruption-blind programs
beside the network adversary and the coin oracle satisfies Validity and
Agreement. -/
theorem netFlat_safe (P : Params) :
    ∀ D ∈ achievableTraceDists (netFlat P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace t :=
  safety_transfer (netFlat_refines P) (main P)

/-- **Trace conservativity of the deployed reading**: every
positive-probability trace of the deployed system has positive probability
under an achievable trace distribution of the monolithic hybrid. -/
theorem netFlat_traces (P : Params) :
    ∀ D ∈ achievableTraceDists (netFlat P), ∀ t, D t ≠ 0 →
      ∃ D' ∈ achievableTraceDists (hybridImpl P), D' t ≠ 0 :=
  fun D hD _ ht => ⟨D, netFlat_refines P hD, ht⟩

/-! ### Mechanical axiom firewall

No headline may acquire a `sorryAx` dependence. -/

/-- info: 'PLTS.ABA.Net.netFlat_atd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms netFlat_atd

/-- info: 'PLTS.ABA.Net.netFlat_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms netFlat_safe

/-- info: 'PLTS.ABA.Net.netFlat_traces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms netFlat_traces

end Net

end ABA
end PLTS
