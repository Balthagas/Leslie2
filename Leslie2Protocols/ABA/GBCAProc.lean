/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCAImpl
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SyncProduct
import Leslie2.Simulation.ForwardLTS
import Leslie2.Results

/-!
# GBCA as a composition of per-process automata

The round-`r` GBCA instance presented the way the algorithm is written: one
automaton per process, running that process's code and nothing else, composed
over a network of rendezvous labels.

* `GBCA.ProcNode` is the state of a single process — its local record
  (`ProcState`), its outbox, its inbox rows, and its copy of the corrupted set.
  Every guard of `GBCA.ProcStep` reads that node and nothing else: there is no
  syntactic access to another process's state anywhere in the per-process code.
* `GBCA.GNet` is the network alphabet. `GNet.net i j m` is the rendezvous on
  which the sender `j` offers `m` from its outbox and the receiver `i` files it
  under row `j`. The per-process automata live over the extended alphabet
  `Lab n ⊕ GNet n`, whose silent label is `Sum.inl τ` (`PLTS.instSilentSum`).
* `GBCA.procInst P r j` is process `j`'s automaton, and `GBCA.perProcInst P r`
  the composite: full synchronisation of the whole family
  (`System.syncProduct`), the network labels hidden (`System.abstract`), the
  result read back over `Lab n` (`System.relabel`).

Ownership of a label is expressed on the automata, not on the composition
operator. A process idles on calls and returns addressed to somebody else and on
network rendezvous it takes no part in, so a shared visible label moves exactly
its genuine participants; a label no automaton offers — a foreign round, the ABA
or WCC API — is blocked, matching the monolithic instance. Corruption is the one
label every automaton acts on, which is what keeps the local copies of the
corrupted set equal.

The locality claim is a theorem, not a convention: `GBCA.perProcInst_atd` states
that the composite and the monolithic instance `GBCA.implInst` (ABDY22
Algorithm 6, deviation D18) achieve exactly the same trace distributions. It is
proved by two
LTS forward simulations along the packing map `GBCA.unpack` — the
composite state `p` corresponds to the monolithic state `q` iff `p = unpack q`,
which pins each node's fields to the matching monolithic components and makes
every node's copy of the corrupted set equal to `q.F`. The step matching is
one-to-one in both directions:

* an interleaved `τ` of the composite is one process's local send (`relay`,
  `echo`, `vote*`, `bind*`, `seal*`, `byz`) — the monolithic rule of the same
  name;
* a hidden network rendezvous is `ImplStep.deliver`, the sender's outbox guard
  supplied by the sender component and the inbox update by the receiver
  component;
* a visible `callG` / `retG` / `fail` moves the addressed process (all of them,
  for `fail`) and idles the rest, matching the monolithic rule with the same
  guards, which the counting bridges (`GBCA.unpack_recvCount` and friends)
  transport verbatim between the two state shapes.

Both systems are LTS, so the two matchings lift to probabilistic forward
simulations through `ForwardSimulation.toProbabilistic` and the equality of
achievable trace distributions follows from soundness applied twice.
-/

open Stream'

namespace PLTS
namespace ABA
namespace GBCA

/-! ### The network alphabet -/

/-- The auxiliary alphabet of point-to-point deliveries: `net i j m` is the
rendezvous on which sender `j` hands the message `m` to receiver `i`. The index
order mirrors the monolithic `ImplStep.deliver i j m`. -/
inductive GNet (n : ℕ) : Type
  /-- Receiver `i` takes delivery of `m` from sender `j`. -/
  | net (i j : Fin n) (m : Msg)
  deriving DecidableEq

/-- The extended alphabet of the per-process presentation: the shared ABA
alphabet together with the network rendezvous labels. Its silent label is
`Sum.inl τ` (`PLTS.instSilentSum`), so every `Sum.inr` label is observable and
hence hideable. -/
abbrev PLab (n : ℕ) : Type := Lab n ⊕ GNet n

@[simp] theorem silent_sum_eq (n : ℕ) : (Silent.τ : PLab n) = Sum.inl Lab.tau := rfl

/-! ### One process's state -/

/-- The state of one process's automaton: its local record, its outbox, its
inbox rows, and its own copy of the corrupted set. -/
structure ProcNode (n : ℕ) : Type where
  /-- The process's local record — the monolithic `proc j`. -/
  proc : ProcState
  /-- The messages the process has multicast — the monolithic `sent j`. -/
  out : Finset Msg
  /-- `inbox k` — the messages from sender `k` delivered here; the monolithic
  row `recv j k`. -/
  inbox : Fin n → Finset Msg
  /-- The corrupted set (local copy, kept in lockstep by the `fail` broadcast). -/
  F : Finset (Fin n)
  deriving DecidableEq

namespace ProcNode

variable {n : ℕ}

/-- The initial node: nothing received, nothing sent, nobody corrupted. -/
def initial (n : ℕ) : ProcNode n where
  proc := ProcState.initial
  out := ∅
  inbox := fun _ => ∅
  F := ∅

/-- The number of distinct senders from which this process has received `m`
(the local reading of `ImplState.recvCount`). -/
def recvCount (p : ProcNode n) (m : Msg) : ℕ :=
  (Finset.univ.filter (fun k => m ∈ p.inbox k)).card

/-- The number of distinct senders from which this process has received some
`ECHO`. -/
def echoCount (p : ProcNode n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ b, Msg.echo b ∈ p.inbox k)).card

/-- The number of distinct senders from which this process has received some
`VOTE`. -/
def voteCount (p : ProcNode n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ v, Msg.vote v ∈ p.inbox k)).card

/-- The number of distinct senders from which this process has received some
`BIND`. -/
def bindCount (p : ProcNode n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ v, Msg.bind v ∈ p.inbox k)).card

/-- The number of distinct senders from which this process has received some
`SEAL`. -/
def sealCount (p : ProcNode n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ v, Msg.seal v ∈ p.inbox k)).card

/-- `Valid = {0, 1}` here: both bits are backed by an `n − f` `INPUT` quorum
among this process's delivered messages. -/
def bothValid (P : Params) (p : ProcNode P.n) : Prop :=
  P.n - P.f ≤ p.recvCount (.input true) ∧ P.n - P.f ≤ p.recvCount (.input false)

/-- Overwrite the local record. -/
def setP (p : ProcNode n) (pr : ProcState) : ProcNode n := { p with proc := pr }

/-- Multicast `m`: add it to the outbox. -/
def send (p : ProcNode n) (m : Msg) : ProcNode n := { p with out := insert m p.out }

/-- File `m` under the inbox row of sender `k`. -/
def deliverTo (p : ProcNode n) (k : Fin n) (m : Msg) : ProcNode n :=
  { p with inbox := Function.update p.inbox k (insert m (p.inbox k)) }

/-- Corruption of `k`, applied to this node's copy of the corrupted set. The
guard is the monolithic one (deviation D1), read off the local copy. -/
def corrupt (P : Params) (k : Fin P.n) (p : ProcNode P.n) : ProcNode P.n :=
  if k ∉ p.F ∧ p.F.card < P.f then { p with F := insert k p.F } else p

end ProcNode

/-! ### One process's code -/

/-- The step relation of process `j`'s automaton in the round-`r` GBCA instance.
Every guard reads the node `p` — this process's record, outbox, inbox and copy
of the corrupted set — and nothing else. All transitions are Dirac. -/
inductive ProcStep (P : Params) (r : ℕ) (j : Fin P.n) :
    ProcNode P.n → PLab P.n → PMF (ProcNode P.n) → Prop
  /-- The environment call arrives at this process: the input is recorded and
  `⟨INPUT, b⟩` goes into the outbox. -/
  | call (p : ProcNode P.n) (b : Bool) (h : p.proc.input = none) :
      ProcStep P r j p (Sum.inl (.callG r j b))
        (PMF.pure ((p.setP { p.proc with
            input := some b,
            sentInput := Function.update p.proc.sentInput b true }).send (.input b)))
  /-- Input-enabledness loop for the call at this process. -/
  | callLoop (p : ProcNode P.n) (b : Bool) :
      ProcStep P r j p (Sum.inl (.callG r j b)) (PMF.pure p)
  /-- A call addressed to somebody else: this process stands still. -/
  | callIdle (p : ProcNode P.n) (id : Fin P.n) (b : Bool) (h : id ≠ j) :
      ProcStep P r j p (Sum.inl (.callG r id b)) (PMF.pure p)
  /-- Algorithm 6 decide case (1), at this process: an `n − f` `SEAL v` quorum
  in the inbox returns `(v, A)`. -/
  | retA (p : ProcNode P.n) (v : Bool)
      (hcnt : P.n - P.f ≤ p.recvCount (.seal (some v)))
      (hr : p.proc.returned = false) :
      ProcStep P r j p (Sum.inl (.retG r j (.A v)))
        (PMF.pure (p.setP { p.proc with returned := true }))
  /-- Algorithm 6 decide case (2), at this process: an `n − f` any-`SEAL` quorum
  containing `SEAL v`, `f + 1` `BIND v`s and `|Valid| > 1` return `(v, B)`. -/
  | retB (p : ProcNode P.n) (v : Bool)
      (hcnt : P.n - P.f ≤ p.sealCount)
      (honce : ∃ k, Msg.seal (some v) ∈ p.inbox k)
      (hbind : P.f + 1 ≤ p.recvCount (.bind (some v)))
      (hval : p.bothValid P)
      (hr : p.proc.returned = false) :
      ProcStep P r j p (Sum.inl (.retG r j (.B v)))
        (PMF.pure (p.setP { p.proc with returned := true }))
  /-- Algorithm 6 decide case (3), at this process: an `n − f` `SEAL ⊥` quorum
  with `|Valid| > 1` returns `(⊥, C)`. -/
  | retC (p : ProcNode P.n)
      (hcnt : P.n - P.f ≤ p.recvCount (.seal none))
      (hval : p.bothValid P)
      (hr : p.proc.returned = false) :
      ProcStep P r j p (Sum.inl (.retG r j .C))
        (PMF.pure (p.setP { p.proc with returned := true }))
  /-- A return addressed to somebody else: this process stands still. -/
  | retIdle (p : ProcNode P.n) (id : Fin P.n) (o : GbcaOut) (h : id ≠ j) :
      ProcStep P r j p (Sum.inl (.retG r id o)) (PMF.pure p)
  /-- Corruption (deviation D1). Every automaton acts on every `fail` label, so
  the local copies of the corrupted set stay equal. -/
  | fail (p : ProcNode P.n) (k : Fin P.n) :
      ProcStep P r j p (Sum.inl (.fail k)) (PMF.pure (p.corrupt P k))
  /-- Algorithm 6's `INPUT` relay, at this process: `f + 1` receipts of
  `⟨INPUT, b⟩` in the inbox and no `⟨INPUT, b⟩` multicast yet. -/
  | relay (p : ProcNode P.n) (b : Bool)
      (hin : p.proc.input ≠ none)
      (hcnt : P.f + 1 ≤ p.recvCount (.input b))
      (hsend : p.proc.sentInput b = false) :
      ProcStep P r j p (Sum.inl .tau)
        (PMF.pure ((p.setP { p.proc with
          sentInput := Function.update p.proc.sentInput b true }).send (.input b)))
  /-- Algorithm 6's `ECHO`, at this process: an `n − f` `INPUT b` quorum in the
  inbox and no `ECHO` multicast yet. -/
  | echo (p : ProcNode P.n) (b : Bool)
      (hin : p.proc.input ≠ none)
      (hcnt : P.n - P.f ≤ p.recvCount (.input b))
      (hsend : p.proc.sentEcho = none) :
      ProcStep P r j p (Sum.inl .tau)
        (PMF.pure ((p.setP { p.proc with sentEcho := some b }).send (.echo b)))
  /-- Algorithm 6's `VOTE b` (wait case (a)), at this process: an `n − f`
  `ECHO b` quorum in the inbox. -/
  | voteBit (p : ProcNode P.n) (b : Bool)
      (hin : p.proc.input ≠ none)
      (hcnt : P.n - P.f ≤ p.recvCount (.echo b))
      (hsend : p.proc.sentVote = none) :
      ProcStep P r j p (Sum.inl .tau)
        (PMF.pure ((p.setP { p.proc with sentVote := some (some b) }).send
          (.vote (some b))))
  /-- Algorithm 6's `VOTE ⊥` (wait case (b)), at this process: `n − f` `ECHO`s
  of any payload in the inbox and `|Valid| > 1`. -/
  | voteBot (p : ProcNode P.n)
      (hin : p.proc.input ≠ none)
      (hcnt : P.n - P.f ≤ p.echoCount)
      (hval : p.bothValid P)
      (hsend : p.proc.sentVote = none) :
      ProcStep P r j p (Sum.inl .tau)
        (PMF.pure ((p.setP { p.proc with sentVote := some none }).send (.vote none)))
  /-- Algorithm 6's `BIND b` (wait case (a) one level up), at this process: an
  `n − f` `VOTE b` quorum in the inbox. -/
  | bindBit (p : ProcNode P.n) (b : Bool)
      (hin : p.proc.input ≠ none)
      (hcnt : P.n - P.f ≤ p.recvCount (.vote (some b)))
      (hsend : p.proc.sentBind = none) :
      ProcStep P r j p (Sum.inl .tau)
        (PMF.pure ((p.setP { p.proc with sentBind := some (some b) }).send
          (.bind (some b))))
  /-- Algorithm 6's `BIND ⊥` (wait case (b) one level up), at this process:
  `n − f` `VOTE`s of any payload in the inbox and `|Valid| > 1`. -/
  | bindBot (p : ProcNode P.n)
      (hin : p.proc.input ≠ none)
      (hcnt : P.n - P.f ≤ p.voteCount)
      (hval : p.bothValid P)
      (hsend : p.proc.sentBind = none) :
      ProcStep P r j p (Sum.inl .tau)
        (PMF.pure ((p.setP { p.proc with sentBind := some none }).send (.bind none)))
  /-- Algorithm 6's `SEAL b` (wait case (a) one level up again), at this
  process: an `n − f` `BIND b` quorum in the inbox. -/
  | sealBit (p : ProcNode P.n) (b : Bool)
      (hin : p.proc.input ≠ none)
      (hcnt : P.n - P.f ≤ p.recvCount (.bind (some b)))
      (hsend : p.proc.sentSeal = none) :
      ProcStep P r j p (Sum.inl .tau)
        (PMF.pure ((p.setP { p.proc with sentSeal := some (some b) }).send
          (.seal (some b))))
  /-- Algorithm 6's `SEAL ⊥` (wait case (b) one level up again), at this
  process: `n − f` `BIND`s of any payload in the inbox and `|Valid| > 1`. -/
  | sealBot (p : ProcNode P.n)
      (hin : p.proc.input ≠ none)
      (hcnt : P.n - P.f ≤ p.bindCount)
      (hval : p.bothValid P)
      (hsend : p.proc.sentSeal = none) :
      ProcStep P r j p (Sum.inl .tau)
        (PMF.pure ((p.setP { p.proc with sentSeal := some none }).send (.seal none)))
  /-- Byzantine injection (deviation D5): a process that its own copy of the
  corrupted set lists may put anything into its outbox. -/
  | byz (p : ProcNode P.n) (m : Msg) (h : j ∈ p.F) :
      ProcStep P r j p (Sum.inl .tau) (PMF.pure (p.send m))
  /-- Self-delivery: this process is both the sender and the receiver, so it
  supplies the outbox guard and files the message itself. -/
  | netSelf (p : ProcNode P.n) (m : Msg) (h : m ∈ p.out) :
      ProcStep P r j p (Sum.inr (.net j j m)) (PMF.pure (p.deliverTo j m))
  /-- Sender role: this process permits the delivery of a message it has
  multicast, and its own state is untouched. -/
  | netSend (p : ProcNode P.n) (i : Fin P.n) (m : Msg) (hi : i ≠ j) (h : m ∈ p.out) :
      ProcStep P r j p (Sum.inr (.net i j m)) (PMF.pure p)
  /-- Receiver role: this process files the message under the sender's row. The
  outbox guard is the sender component's business, so there is none here. -/
  | netRecv (p : ProcNode P.n) (k : Fin P.n) (m : Msg) (hk : k ≠ j) :
      ProcStep P r j p (Sum.inr (.net j k m)) (PMF.pure (p.deliverTo k m))
  /-- A delivery between two other processes: this process stands still. -/
  | netIdle (p : ProcNode P.n) (i k : Fin P.n) (m : Msg) (hi : i ≠ j) (hk : k ≠ j) :
      ProcStep P r j p (Sum.inr (.net i k m)) (PMF.pure p)

/-- Process `j`'s automaton in the round-`r` GBCA instance. -/
noncomputable def procInst (P : Params) (r : ℕ) (j : Fin P.n) :
    System (ProcNode P.n) (PLab P.n) where
  init := ProcNode.initial P.n
  step := ProcStep P r j

@[simp] theorem procInst_init (P : Params) (r : ℕ) (j : Fin P.n) :
    (procInst P r j).init = ProcNode.initial P.n := rfl

@[simp] theorem procInst_step (P : Params) (r : ℕ) (j : Fin P.n) (p : ProcNode P.n)
    (l : PLab P.n) (μ : PMF (ProcNode P.n)) :
    (procInst P r j).step p l μ ↔ ProcStep P r j p l μ := Iff.rfl

/-- Every per-process transition is Dirac. -/
theorem procInst_isLTS (P : Params) (r : ℕ) (j : Fin P.n) : (procInst P r j).IsLTS := by
  rintro p l μ hstep
  cases hstep <;> exact ⟨_, rfl⟩

/-! ### The composition -/

/-- The network labels — the ones the composition hides. -/
def netLabels (n : ℕ) : Set (PLab n) := {l | ∃ i j m, l = Sum.inr (GNet.net i j m)}

@[simp] theorem inl_notMem_netLabels {n : ℕ} (l : Lab n) : Sum.inl l ∉ netLabels n := by
  simp [netLabels]

@[simp] theorem inr_mem_netLabels {n : ℕ} (g : GNet n) : Sum.inr g ∈ netLabels n := by
  obtain ⟨i, j, m⟩ := g
  exact ⟨i, j, m, rfl⟩

/-- **The per-process GBCA instance**: the whole family of per-process automata
under full synchronisation, with the network rendezvous hidden and the result
read back over the shared alphabet `Lab n`. -/
noncomputable def perProcInst (P : Params) (r : ℕ) :
    System (∀ _ : Fin P.n, ProcNode P.n) (Lab P.n) :=
  ((System.syncProduct (procInst P r)).abstract (netLabels P.n)).relabel

@[simp] theorem perProcInst_init (P : Params) (r : ℕ) :
    (perProcInst P r).init = fun _ => ProcNode.initial P.n := rfl

/-- Every transition of the per-process composition is Dirac. -/
theorem perProcInst_isLTS (P : Params) (r : ℕ) : (perProcInst P r).IsLTS :=
  System.relabel_isLTS
    (System.abstract_isLTS (System.syncProduct_isLTS (procInst_isLTS P r)) _)

/-- **The composite's transitions, unfolded.** A visible label is a synchronised
move of the whole family on `Sum.inl l`; a `τ` is either an interleaved
`Sum.inl τ` of one automaton or a hidden network rendezvous of the family. -/
theorem perProcInst_step_iff (P : Params) (r : ℕ) (p : ∀ _ : Fin P.n, ProcNode P.n)
    (l : Lab P.n) (μ : PMF (∀ _ : Fin P.n, ProcNode P.n)) :
    (perProcInst P r).step p l μ ↔
      (l = Lab.tau ∧ ∃ i j m,
        (System.syncProduct (procInst P r)).step p (Sum.inr (GNet.net i j m)) μ) ∨
      (System.syncProduct (procInst P r)).step p (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨i, j, m, rfl⟩, hs⟩ | ⟨-, hs⟩)
    · exact Or.inl ⟨Sum.inl.inj hτ, i, j, m, hs⟩
    · exact Or.inr hs
  · rintro (⟨rfl, i, j, m, hs⟩ | hs)
    · exact Or.inl ⟨rfl, _, inr_mem_netLabels _, hs⟩
    · exact Or.inr ⟨inl_notMem_netLabels l, hs⟩

/-! ### Packing -/

/-- **The packing map.** The monolithic state `q` read as one node per process:
each node gets that process's record, sent pool and delivered rows, and a copy
of the corrupted set. -/
def unpack {n : ℕ} (q : ImplState n) : ∀ _ : Fin n, ProcNode n :=
  fun j => { proc := q.proc j, out := q.sent j, inbox := q.recv j, F := q.F }

section Unpack

variable {n : ℕ}

@[simp] theorem unpack_proc (q : ImplState n) (j : Fin n) : (unpack q j).proc = q.proc j := rfl
@[simp] theorem unpack_out (q : ImplState n) (j : Fin n) : (unpack q j).out = q.sent j := rfl
@[simp] theorem unpack_inbox (q : ImplState n) (j : Fin n) : (unpack q j).inbox = q.recv j := rfl
@[simp] theorem unpack_F (q : ImplState n) (j : Fin n) : (unpack q j).F = q.F := rfl

/-! The counting bridges: the local counts of a packed node are the monolithic
counts at that process, by definition — the two shapes hold the same rows. -/

@[simp] theorem unpack_recvCount (q : ImplState n) (j : Fin n) (m : Msg) :
    (unpack q j).recvCount m = q.recvCount j m := rfl

@[simp] theorem unpack_echoCount (q : ImplState n) (j : Fin n) :
    (unpack q j).echoCount = q.echoCount j := rfl

@[simp] theorem unpack_voteCount (q : ImplState n) (j : Fin n) :
    (unpack q j).voteCount = q.voteCount j := rfl

@[simp] theorem unpack_bindCount (q : ImplState n) (j : Fin n) :
    (unpack q j).bindCount = q.bindCount j := rfl

@[simp] theorem unpack_sealCount (q : ImplState n) (j : Fin n) :
    (unpack q j).sealCount = q.sealCount j := rfl

@[simp] theorem unpack_bothValid (P : Params) (q : ImplState P.n) (j : Fin P.n) :
    (unpack q j).bothValid P ↔ q.bothValid P j := Iff.rfl

@[simp] theorem unpack_initial (n : ℕ) :
    unpack (ImplState.initial n) = fun _ => ProcNode.initial n := rfl

/-- Packing a local-record update: only the addressed node moves. -/
theorem unpack_setProc (q : ImplState n) (j : Fin n) (pr : ProcState) :
    unpack (q.setProc j pr) = Function.update (unpack q) j ((unpack q j).setP pr) := by
  funext k
  by_cases hk : k = j
  · subst hk; simp [unpack, ImplState.setProc, ProcNode.setP]
  · simp [unpack, ImplState.setProc, ProcNode.setP, Function.update_of_ne hk]

/-- Packing a bare multicast: only the sender's outbox grows. -/
theorem unpack_mcast (q : ImplState n) (j : Fin n) (m : Msg) :
    unpack (q.mcast j m) = Function.update (unpack q) j ((unpack q j).send m) := by
  funext k
  by_cases hk : k = j
  · subst hk; simp [unpack, ImplState.mcast, ProcNode.send]
  · simp [unpack, ImplState.mcast, ProcNode.send, Function.update_of_ne hk]

/-- Packing a protocol send — record update plus multicast, the shape of every
`τ`-send of Algorithm 6: only the sending node moves. -/
theorem unpack_send (q : ImplState n) (j : Fin n) (pr : ProcState) (m : Msg) :
    unpack ((q.setProc j pr).mcast j m) =
      Function.update (unpack q) j (((unpack q j).setP pr).send m) := by
  rw [unpack_mcast, unpack_setProc]
  funext k
  by_cases hk : k = j
  · subst hk; simp
  · simp [Function.update_of_ne hk]

/-- Packing a delivery: only the receiving node moves, and only in the sender's
inbox row. -/
theorem unpack_recvMsg (q : ImplState n) (i j : Fin n) (m : Msg) :
    unpack (q.recvMsg i j m) = Function.update (unpack q) i ((unpack q i).deliverTo j m) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [unpack, ImplState.recvMsg, ProcNode.deliverTo]
  · simp [unpack, ImplState.recvMsg, ProcNode.deliverTo, Function.update_of_ne hk]

/-- Packing a corruption: every node applies the same local transform to its own
copy of the corrupted set, and the copies were equal. -/
theorem unpack_corrupt (P : Params) (q : ImplState P.n) (k : Fin P.n) :
    unpack (q.corrupt P k) = fun j => ProcNode.corrupt P k (unpack q j) := by
  funext j
  unfold ImplState.corrupt ProcNode.corrupt
  by_cases hc : k ∉ q.F ∧ q.F.card < P.f
  · rw [if_pos hc, if_pos (by simpa [unpack] using hc)]; rfl
  · rw [if_neg hc, if_neg (by simpa [unpack] using hc)]

end Unpack

/-! ### Assembling composite steps -/

section Assemble

variable {P : Params} {r : ℕ}

/-- A synchronised visible move of the whole family, every component Dirac. -/
private theorem sync_visible {l : PLab P.n} (hl : l ≠ Silent.τ)
    {p p' : ∀ _ : Fin P.n, ProcNode P.n}
    (h : ∀ k, ProcStep P r k (p k) l (PMF.pure (p' k))) :
    (System.syncProduct (procInst P r)).step p l (PMF.pure p') :=
  Or.inl ⟨hl, fun k => PMF.pure (p' k), h, (piPMF_pure p').symm⟩

/-- An interleaved `τ` of the family: component `k` moves, the rest hold. -/
private theorem sync_tau {p : ∀ _ : Fin P.n, ProcNode P.n} {k : Fin P.n} {y : ProcNode P.n}
    (h : ProcStep P r k (p k) (Sum.inl Lab.tau) (PMF.pure y)) :
    (System.syncProduct (procInst P r)).step p (Sum.inl Lab.tau)
      (PMF.pure (Function.update p k y)) := by
  refine Or.inr ⟨rfl, k, PMF.pure y, h, ?_⟩
  rw [piPMF_update_pure, PMF.pure_map]

/-- **Every monolithic transition is a composite transition.** Each rule of
Algorithm 6 is assembled from the per-process code of its participants and the
idling of everybody else. -/
theorem perProc_step_of_impl {q : ImplState P.n} {l : Lab P.n} {μ : PMF (ImplState P.n)}
    (h : ImplStep P r q l μ) :
    ∃ q', μ = PMF.pure q' ∧ (perProcInst P r).step (unpack q) l (PMF.pure (unpack q')) := by
  suffices hh : ∃ q', μ = PMF.pure q' ∧
      ((l = Lab.tau ∧ ∃ i j m, (System.syncProduct (procInst P r)).step (unpack q)
          (Sum.inr (GNet.net i j m)) (PMF.pure (unpack q'))) ∨
        (System.syncProduct (procInst P r)).step (unpack q) (Sum.inl l)
          (PMF.pure (unpack q'))) by
    obtain ⟨q', hμ, hs⟩ := hh
    exact ⟨q', hμ, (perProcInst_step_iff P r _ l _).mpr hs⟩
  cases h with
  | call id b hin =>
    refine ⟨_, rfl, Or.inr ?_⟩
    rw [unpack_send]
    refine sync_visible (by simp) fun k => ?_
    by_cases hk : k = id
    · subst hk; rw [Function.update_self]; exact ProcStep.call _ b hin
    · rw [Function.update_of_ne hk]; exact ProcStep.callIdle _ id b (Ne.symm hk)
  | callLoop id b =>
    refine ⟨_, rfl, Or.inr (sync_visible (by simp) fun k => ?_)⟩
    by_cases hk : k = id
    · subst hk; exact ProcStep.callLoop _ b
    · exact ProcStep.callIdle _ id b (Ne.symm hk)
  | deliver i j m hm =>
    refine ⟨_, rfl, Or.inl ⟨rfl, i, j, m, ?_⟩⟩
    rw [unpack_recvMsg]
    refine sync_visible (by simp) fun k => ?_
    by_cases hki : k = i
    · subst hki
      rw [Function.update_self]
      by_cases hkj : j = k
      · subst hkj; exact ProcStep.netSelf _ m hm
      · exact ProcStep.netRecv _ j m hkj
    · rw [Function.update_of_ne hki]
      by_cases hkj : j = k
      · subst hkj; exact ProcStep.netSend _ i m (fun hc => hki hc.symm) hm
      · exact ProcStep.netIdle _ i j m (fun hc => hki hc.symm) hkj
  | relay j b hin hcnt hsend =>
    refine ⟨_, rfl, Or.inr ?_⟩
    rw [unpack_send]
    exact sync_tau (ProcStep.relay _ b hin hcnt hsend)
  | echo j b hin hcnt hsend =>
    refine ⟨_, rfl, Or.inr ?_⟩
    rw [unpack_send]
    exact sync_tau (ProcStep.echo _ b hin hcnt hsend)
  | voteBit j b hin hcnt hsend =>
    refine ⟨_, rfl, Or.inr ?_⟩
    rw [unpack_send]
    exact sync_tau (ProcStep.voteBit _ b hin hcnt hsend)
  | voteBot j hin hcnt hval hsend =>
    refine ⟨_, rfl, Or.inr ?_⟩
    rw [unpack_send]
    exact sync_tau (ProcStep.voteBot _ hin hcnt hval hsend)
  | bindBit j b hin hcnt hsend =>
    refine ⟨_, rfl, Or.inr ?_⟩
    rw [unpack_send]
    exact sync_tau (ProcStep.bindBit _ b hin hcnt hsend)
  | bindBot j hin hcnt hval hsend =>
    refine ⟨_, rfl, Or.inr ?_⟩
    rw [unpack_send]
    exact sync_tau (ProcStep.bindBot _ hin hcnt hval hsend)
  | sealBit j b hin hcnt hsend =>
    refine ⟨_, rfl, Or.inr ?_⟩
    rw [unpack_send]
    exact sync_tau (ProcStep.sealBit _ b hin hcnt hsend)
  | sealBot j hin hcnt hval hsend =>
    refine ⟨_, rfl, Or.inr ?_⟩
    rw [unpack_send]
    exact sync_tau (ProcStep.sealBot _ hin hcnt hval hsend)
  | byz j m hj =>
    refine ⟨_, rfl, Or.inr ?_⟩
    rw [unpack_mcast]
    exact sync_tau (ProcStep.byz _ m hj)
  | retA id v hcnt hr =>
    refine ⟨_, rfl, Or.inr ?_⟩
    rw [unpack_setProc]
    refine sync_visible (by simp) fun k => ?_
    by_cases hk : k = id
    · subst hk; rw [Function.update_self]; exact ProcStep.retA _ v hcnt hr
    · rw [Function.update_of_ne hk]; exact ProcStep.retIdle _ id _ (Ne.symm hk)
  | retB id v hcnt honce hbind hval hr =>
    refine ⟨_, rfl, Or.inr ?_⟩
    rw [unpack_setProc]
    refine sync_visible (by simp) fun k => ?_
    by_cases hk : k = id
    · subst hk; rw [Function.update_self]; exact ProcStep.retB _ v hcnt honce hbind hval hr
    · rw [Function.update_of_ne hk]; exact ProcStep.retIdle _ id _ (Ne.symm hk)
  | retC id hcnt hval hr =>
    refine ⟨_, rfl, Or.inr ?_⟩
    rw [unpack_setProc]
    refine sync_visible (by simp) fun k => ?_
    by_cases hk : k = id
    · subst hk; rw [Function.update_self]; exact ProcStep.retC _ hcnt hval hr
    · rw [Function.update_of_ne hk]; exact ProcStep.retIdle _ id _ (Ne.symm hk)
  | fail id =>
    refine ⟨_, rfl, Or.inr ?_⟩
    rw [unpack_corrupt]
    exact sync_visible (by simp) fun k => ProcStep.fail _ id

end Assemble

/-! ### Reading composite steps back -/

section Invert

variable {P : Params} {r : ℕ}

private theorem pure_inj {α : Type} {a b : α} (h : (PMF.pure a : PMF α) = PMF.pure b) : a = b := by
  have hm : a ∈ (PMF.pure b).support := by rw [← h]; simp
  simpa using hm

/-- The target of an interleaved `τ`, read off the family distribution. -/
private theorem interleave_target {p p' : ∀ _ : Fin P.n, ProcNode P.n} {k : Fin P.n}
    {y : ProcNode P.n}
    (h : (PMF.pure p' : PMF (∀ _ : Fin P.n, ProcNode P.n))
      = piPMF (Function.update (fun j => PMF.pure (p j)) k (PMF.pure y))) :
    p' = Function.update p k y := by
  rw [piPMF_update_pure, PMF.pure_map] at h
  exact pure_inj h

/-- The target of a synchronised visible move, read off componentwise. -/
private theorem sync_target {μ_ : ∀ _ : Fin P.n, PMF (ProcNode P.n)}
    {p' x : ∀ _ : Fin P.n, ProcNode P.n}
    (hμ : (PMF.pure p' : PMF (∀ _ : Fin P.n, ProcNode P.n)) = piPMF μ_)
    (h : ∀ k, μ_ k = PMF.pure (x k)) : p' = x := by
  rw [funext h, piPMF_pure] at hμ
  exact pure_inj hμ

/-- A call addressed elsewhere leaves a process where it is. -/
private theorem callG_idle {k id : Fin P.n} {r' : ℕ} {b : Bool} {p : ProcNode P.n}
    {μ : PMF (ProcNode P.n)} (hk : id ≠ k)
    (h : ProcStep P r k p (Sum.inl (Lab.callG r' id b)) μ) : μ = PMF.pure p := by
  cases h with
  | call => exact absurd rfl hk
  | callLoop => rfl
  | callIdle => rfl

/-- The addressed process answers a call by its own `call` or its own
`callLoop`; either way the monolithic instance has the matching rule. -/
private theorem callG_self {k : Fin P.n} {r' : ℕ} {b : Bool} {q : ImplState P.n}
    {μ : PMF (ProcNode P.n)}
    (h : ProcStep P r k (unpack q k) (Sum.inl (Lab.callG r' k b)) μ) :
    (μ = PMF.pure (unpack q k) ∧ ImplStep P r q (Lab.callG r' k b) (PMF.pure q)) ∨
      (μ = PMF.pure (((unpack q k).setP { (unpack q k).proc with
            input := some b,
            sentInput := Function.update (unpack q k).proc.sentInput b true }).send (.input b)) ∧
        ImplStep P r q (Lab.callG r' k b)
          (PMF.pure ((q.setProc k { q.proc k with
            input := some b,
            sentInput := Function.update (q.proc k).sentInput b true }).mcast k (.input b)))) := by
  cases h with
  | call _ hin => exact Or.inr ⟨rfl, ImplStep.call q k b hin⟩
  | callLoop => exact Or.inl ⟨rfl, ImplStep.callLoop q k b⟩
  | callIdle _ _ hne => exact absurd rfl hne

/-- A return addressed elsewhere leaves a process where it is. -/
private theorem retG_idle {k id : Fin P.n} {r' : ℕ} {o : GbcaOut} {p : ProcNode P.n}
    {μ : PMF (ProcNode P.n)} (hk : id ≠ k)
    (h : ProcStep P r k p (Sum.inl (Lab.retG r' id o)) μ) : μ = PMF.pure p := by
  cases h with
  | retA => exact absurd rfl hk
  | retB => exact absurd rfl hk
  | retC => exact absurd rfl hk
  | retIdle => rfl

/-- Whichever of the three wait cases the addressed process closes, its local
evidence is the monolithic rule's evidence. -/
private theorem retG_self {k : Fin P.n} {r' : ℕ} {o : GbcaOut} {q : ImplState P.n}
    {μ : PMF (ProcNode P.n)}
    (h : ProcStep P r k (unpack q k) (Sum.inl (Lab.retG r' k o)) μ) :
    μ = PMF.pure ((unpack q k).setP { (unpack q k).proc with returned := true }) ∧
      ImplStep P r q (Lab.retG r' k o)
        (PMF.pure (q.setProc k { q.proc k with returned := true })) := by
  cases h with
  | retA v hcnt hr => exact ⟨rfl, ImplStep.retA q k v hcnt hr⟩
  | retB v hcnt honce hbind hval hr => exact ⟨rfl, ImplStep.retB q k v hcnt honce hbind hval hr⟩
  | retC hcnt hval hr => exact ⟨rfl, ImplStep.retC q k hcnt hval hr⟩
  | retIdle => rename_i hne; exact absurd rfl hne

/-- On a corruption label every process applies the same local transform. -/
private theorem fail_inv {k id : Fin P.n} {p : ProcNode P.n} {μ : PMF (ProcNode P.n)}
    (h : ProcStep P r k p (Sum.inl (Lab.fail id)) μ) : μ = PMF.pure (p.corrupt P id) := by
  cases h with
  | fail => rfl

/-- **The four network roles at once.** On `net i j m` a process files the
message iff it is the receiver, and offers the outbox guard iff it is the
sender. -/
private theorem net_inv {k i j : Fin P.n} {m : Msg} {p : ProcNode P.n}
    {μ : PMF (ProcNode P.n)} (h : ProcStep P r k p (Sum.inr (GNet.net i j m)) μ) :
    μ = PMF.pure (if k = i then p.deliverTo j m else p) ∧ (k = j → m ∈ p.out) := by
  cases h with
  | netSelf =>
    rename_i hm
    exact ⟨by rw [if_pos rfl], fun _ => hm⟩
  | netSend =>
    rename_i hi hm
    exact ⟨by rw [if_neg fun hc => hi hc.symm], fun _ => hm⟩
  | netRecv =>
    rename_i hk
    exact ⟨by rw [if_pos rfl], fun hc => absurd hc.symm hk⟩
  | netIdle =>
    rename_i hi hk
    exact ⟨by rw [if_neg fun hc => hi hc.symm], fun hc => absurd hc.symm hk⟩

end Invert

/-- **Every composite transition is a monolithic transition.** Reading a
composite step back is a case analysis on the label: on a hidden rendezvous the
sender component supplies `ImplStep.deliver`'s outbox guard and the receiver
component its effect; on `callG` / `retG` the addressed component supplies the
rule and its guards while `callG_idle` / `retG_idle` pin every other component
to a standstill; on `fail` every component performs the same transform. A label
no component offers has no composite transition at all. -/
theorem impl_step_of_perProc {P : Params} {r : ℕ} {q : ImplState P.n} {l : Lab P.n}
    {p' : ∀ _ : Fin P.n, ProcNode P.n}
    (h : (perProcInst P r).step (unpack q) l (PMF.pure p')) :
    ∃ q', p' = unpack q' ∧ ImplStep P r q l (PMF.pure q') := by
  rw [perProcInst_step_iff] at h
  rcases h with ⟨rfl, i, j, m, hs⟩ | hs
  · rcases hs with ⟨-, μ_, hstep, hμ⟩ | ⟨hτ, -⟩
    · have hxj : ProcStep P r j (unpack q j) (Sum.inr (GNet.net i j m)) (μ_ j) := hstep j
      refine ⟨q.recvMsg i j m, ?_, ImplStep.deliver q i j m ((net_inv hxj).2 rfl)⟩
      rw [unpack_recvMsg]
      refine sync_target hμ fun k => ?_
      have hxk : ProcStep P r k (unpack q k) (Sum.inr (GNet.net i j m)) (μ_ k) := hstep k
      rw [(net_inv hxk).1]
      by_cases hk : k = i
      · subst hk; rw [if_pos rfl, Function.update_self]
      · rw [if_neg hk, Function.update_of_ne hk]
    · exact absurd hτ (by simp)
  · by_cases hl : l = Lab.tau
    · subst hl
      rcases hs with ⟨hne, -⟩ | ⟨-, k, μ_k, hstepk, hμ⟩
      · exact absurd rfl hne
      · have hx : ProcStep P r k (unpack q k) (Sum.inl Lab.tau) μ_k := hstepk
        cases hx with
        | relay =>
          rename_i b hin hcnt hsend
          refine ⟨_, ?_, ImplStep.relay q k b hin hcnt hsend⟩
          rw [unpack_send]; exact interleave_target hμ
        | echo =>
          rename_i b hin hcnt hsend
          refine ⟨_, ?_, ImplStep.echo q k b hin hcnt hsend⟩
          rw [unpack_send]; exact interleave_target hμ
        | voteBit =>
          rename_i b hin hcnt hsend
          refine ⟨_, ?_, ImplStep.voteBit q k b hin hcnt hsend⟩
          rw [unpack_send]; exact interleave_target hμ
        | voteBot =>
          rename_i hin hcnt hval hsend
          refine ⟨_, ?_, ImplStep.voteBot q k hin hcnt hval hsend⟩
          rw [unpack_send]; exact interleave_target hμ
        | bindBit =>
          rename_i b hin hcnt hsend
          refine ⟨_, ?_, ImplStep.bindBit q k b hin hcnt hsend⟩
          rw [unpack_send]; exact interleave_target hμ
        | bindBot =>
          rename_i hin hcnt hval hsend
          refine ⟨_, ?_, ImplStep.bindBot q k hin hcnt hval hsend⟩
          rw [unpack_send]; exact interleave_target hμ
        | sealBit =>
          rename_i b hin hcnt hsend
          refine ⟨_, ?_, ImplStep.sealBit q k b hin hcnt hsend⟩
          rw [unpack_send]; exact interleave_target hμ
        | sealBot =>
          rename_i hin hcnt hval hsend
          refine ⟨_, ?_, ImplStep.sealBot q k hin hcnt hval hsend⟩
          rw [unpack_send]; exact interleave_target hμ
        | byz =>
          rename_i m hj
          refine ⟨_, ?_, ImplStep.byz q k m hj⟩
          rw [unpack_mcast]; exact interleave_target hμ
    · rcases hs with ⟨-, μ_, hstep, hμ⟩ | ⟨hτ, -⟩
      · cases l with
        | tau => exact absurd rfl hl
        | callABA id b =>
          have hx : ProcStep P r ⟨0, P.n_pos⟩ (unpack q ⟨0, P.n_pos⟩)
            (Sum.inl (Lab.callABA id b)) (μ_ ⟨0, P.n_pos⟩) := hstep _
          cases hx
        | retABA id b =>
          have hx : ProcStep P r ⟨0, P.n_pos⟩ (unpack q ⟨0, P.n_pos⟩)
            (Sum.inl (Lab.retABA id b)) (μ_ ⟨0, P.n_pos⟩) := hstep _
          cases hx
        | callW r' id =>
          have hx : ProcStep P r ⟨0, P.n_pos⟩ (unpack q ⟨0, P.n_pos⟩)
            (Sum.inl (Lab.callW r' id)) (μ_ ⟨0, P.n_pos⟩) := hstep _
          cases hx
        | retW r' id b =>
          have hx : ProcStep P r ⟨0, P.n_pos⟩ (unpack q ⟨0, P.n_pos⟩)
            (Sum.inl (Lab.retW r' id b)) (μ_ ⟨0, P.n_pos⟩) := hstep _
          cases hx
        | callG r' id b =>
          have hx : ProcStep P r id (unpack q id) (Sum.inl (Lab.callG r' id b)) (μ_ id) :=
            hstep id
          rcases callG_self hx with ⟨hd, himpl⟩ | ⟨hd, himpl⟩
          · refine ⟨q, ?_, himpl⟩
            refine sync_target hμ fun k => ?_
            by_cases hk : k = id
            · subst hk; exact hd
            · exact callG_idle (Ne.symm hk) (hstep k)
          · refine ⟨_, ?_, himpl⟩
            rw [unpack_send]
            refine sync_target hμ fun k => ?_
            by_cases hk : k = id
            · subst hk; rw [Function.update_self]; exact hd
            · rw [Function.update_of_ne hk]; exact callG_idle (Ne.symm hk) (hstep k)
        | retG r' id o =>
          have hx : ProcStep P r id (unpack q id) (Sum.inl (Lab.retG r' id o)) (μ_ id) :=
            hstep id
          obtain ⟨hd, himpl⟩ := retG_self hx
          refine ⟨_, ?_, himpl⟩
          rw [unpack_setProc]
          refine sync_target hμ fun k => ?_
          by_cases hk : k = id
          · subst hk; rw [Function.update_self]; exact hd
          · rw [Function.update_of_ne hk]; exact retG_idle (Ne.symm hk) (hstep k)
        | fail id =>
          refine ⟨q.corrupt P id, ?_, ImplStep.fail q id⟩
          rw [unpack_corrupt]
          exact sync_target hμ fun k => fail_inv (hstep k)
      · exact absurd (Sum.inl.inj hτ) hl

/-! ### Single-step weak transitions -/

section WeakHelpers

variable {S L : Type} [Silent L] {sys : System S L}

omit [Silent L] in
private theorem singleStep_partial_exec {q q' : S} {l : L} (h : sys.LStep q l q') :
    is_partial_exec ⟨q, Seq.cons (l, q') Seq.nil⟩ sys := by
  intro k l' s' hk
  cases k with
  | zero =>
    rw [Stream'.Seq.get?_cons_zero] at hk
    injection hk with hk
    injection hk with h1 h2
    subst h1
    subst h2
    exact ⟨q, PMF.pure q', rfl, h, by rw [PMF.mem_support_pure_iff]⟩
  | succ k =>
    rw [Stream'.Seq.get?_cons_succ, Stream'.Seq.get?_nil] at hk
    exact absurd hk (by simp)

/-- A single external `LStep` is a weak transition. -/
private theorem weakLStep_single {q q' : S} {l : L} (h : sys.LStep q l q')
    (hl : ¬ l = Silent.τ) : sys.weakLStep q l q' :=
  ⟨⟨q, Seq.cons (l, q') Seq.nil⟩,
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil,
    singleStep_partial_exec h, rfl,
    AlterSeq.endState_singleton_cons q l q',
    by rw [System.trace_cons_external sys q l q' Seq.nil hl, System.trace_init]⟩

/-- A single internal `LStep` is a silent weak transition. -/
private theorem weakLSilent_single {q q' : S} (h : sys.LStep q Silent.τ q') :
    sys.weakLSilent q q' :=
  ⟨⟨q, Seq.cons (Silent.τ, q') Seq.nil⟩,
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil,
    singleStep_partial_exec h, rfl,
    AlterSeq.endState_singleton_cons q Silent.τ q',
    by
      unfold System.trace
      rw [Stream'.Seq.filter_cons_neg _ _ (by simp)]
      exact System.trace_init sys q'⟩

end WeakHelpers

/-! ### The two refinements -/

/-- **The composition refines the monolithic instance.** Each composite step is
answered by the single monolithic step of `impl_step_of_perProc`; no stuttering
is needed in either direction, the matching being one-to-one. -/
theorem perProcRefines (P : Params) (r : ℕ) :
    ForwardSimulation (perProcInst P r) (implInst P r) (fun p q => p = unpack q) where
  step := by
    rintro p q rfl l μ hstep p' hmem
    obtain ⟨s', rfl⟩ := perProcInst_isLTS P r _ l μ hstep
    rw [PMF.mem_support_pure_iff] at hmem
    subst hmem
    obtain ⟨q', rfl, himpl⟩ := impl_step_of_perProc hstep
    refine ⟨q', ?_, rfl⟩
    by_cases hl : l = Silent.τ
    · subst hl
      exact Or.inl ⟨rfl, weakLSilent_single (sys := implInst P r) himpl⟩
    · exact Or.inr ⟨hl, weakLStep_single (sys := implInst P r) himpl hl⟩

/-- **The monolithic instance refines the composition.** Each rule of Algorithm 6
is answered by the composite step assembled in `perProc_step_of_impl`. -/
theorem implRefinesPerProc (P : Params) (r : ℕ) :
    ForwardSimulation (implInst P r) (perProcInst P r) (fun q p => p = unpack q) where
  step := by
    rintro q p rfl l μ hstep q' hmem
    obtain ⟨q'', rfl, hcomp⟩ := perProc_step_of_impl hstep
    rw [PMF.mem_support_pure_iff] at hmem
    subst hmem
    refine ⟨unpack q', ?_, rfl⟩
    by_cases hl : l = Silent.τ
    · subst hl
      exact Or.inl ⟨rfl, weakLSilent_single (sys := perProcInst P r) hcomp⟩
    · exact Or.inr ⟨hl, weakLStep_single (sys := perProcInst P r) hcomp hl⟩

/-- **The headline.** The per-process composition and the monolithic instance
achieve exactly the same trace distributions: presenting GBCA as one automaton
per process, communicating only through the network labels, neither adds nor
removes observable behaviour. -/
theorem perProcInst_atd (P : Params) (r : ℕ) :
    achievableTraceDists (perProcInst P r) = achievableTraceDists (implInst P r) :=
  Set.Subset.antisymm
    (ForwardSimulation.toProbabilistic (perProcInst_isLTS P r) (implInst_isLTS P r) rfl
      (perProcRefines P r)).achievableTraceDists_subset
    (ForwardSimulation.toProbabilistic (implInst_isLTS P r) (perProcInst_isLTS P r) rfl
      (implRefinesPerProc P r)).achievableTraceDists_subset

end GBCA
end ABA
end PLTS
