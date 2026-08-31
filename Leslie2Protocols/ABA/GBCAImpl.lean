/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCASpec

/-!
# The GBCA implementation instance (ABDY22 Algorithm 6)

The round-`r` instance of the Graded Binding Crusader Agreement protocol, as an
LTS over the shared alphabet `ABA.Lab n`.

*Attribution.* The file transcribes ABDY22's Algorithm 6 — the 6-round Graded
Binding Crusader Agreement for Byzantine faults — directly. The level mapping is

```
INPUT = echo,  ECHO = echo2,  VOTE = echo3,  BIND = echo4,  SEAL = echo5
```

and the three returns are the decide conditions of lines 23–29.

Each process runs the message pattern

* `INPUT b` — multicast on being called; relayed after `f + 1` receipts;
* `ECHO b` — multicast once `INPUT b` was received from `n − f` senders
  (which also puts `b` into the derived set `Valid`);
* `VOTE v` (`v ∈ {0,1,⊥}`) — a real bit after an `n − f` `ECHO b` quorum, `⊥`
  after `n − f` `ECHO`s of any payload with `|Valid| > 1`;
* `BIND v` — the same pattern one level up, over `VOTE`s;
* `SEAL v` — the same pattern one level up again, over `BIND`s;
* return — grade `A b` after an `n − f` `SEAL b` quorum, `B b` after an
  `n − f` any-`SEAL` quorum containing `b` with `f + 1` `BIND b`s and
  `|Valid| > 1`, and `C` after an `n − f` `SEAL ⊥` quorum with `|Valid| > 1`.

Every transition is Dirac (`implInst_isLTS`); asynchrony and Byzantine
behaviour are modelled by nondeterministic `τ`-transitions.

## Why the cited algorithm and not the blueprint's `alg:GBCA` (D18)

* **D18 (the five-level ladder).** This is a deviation from the source
  blueprint's `alg:GBCA`, which presents a **4-round compression** of
  Algorithm 6: the `echo5` round is elided, the decide conditions read one level
  down, and the grade-1 evidence is `f + 1` `VOTE v` where Algorithm 6 has
  `t + 1` `echo4 v`. The compression violates the paper's Graded Binding. One
  process held at the echo stage through a grade-0 decision can afterwards
  direct its write-once echo at either bit, and one corruption completes
  `f + 1` `VOTE v` for the bit of the adversary's choice — so two extensions of
  a single `C`-return hand out two different bits. The encoding therefore
  follows the cited algorithm rather than the blueprint's compression; the
  upstream blueprint carries a matching red annotation.

The grade-1 evidence is what the depth buys. `f + 1` `BIND v` receipts exceed
the corruption budget, so they guarantee an honest `BIND v` sender, whose own
wait-condition is an `n − f` `VOTE v` receipt quorum over the write-once `VOTE`
level — and that quorum is the object the paper's binding argument counts
(Lemmas 4.8/4.9 through E.9).

*Transcription note.* The prose preceding Algorithm 6 says "upon receiving
`echo4` messages from `2t + 1` parties" where the pseudocode's lines 19–20 say
`n − t`; the two coincide only at `n = 3t + 1`. The encoding follows the
pseudocode (`n − f`).

## Model and deviations (continuing the project's D1–D4)

* **D1 (determinised `fail`).** As in the spec instance, corruption is the
  total Dirac function `ImplState.corrupt` — `F` stays in lockstep with every
  other component under the `fail` broadcast.
* **D5 (set-based network).** Multicasts are idempotent: each sender owns a
  *set* `sent j` of messages it has multicast, and `recv i j` is the set of
  messages from `j` that the adversary has delivered to `i` (`deliver` is a
  `τ`-transition requiring `m ∈ sent j`). Thresholds count *distinct senders*
  in the receiver's delivered sets, so message duplication and point-to-point
  scheduling are absorbed into the set model. A corrupted sender may inject
  any message into its `sent` pool (`byz`).
* **D8 (participation gating).** Protocol sends (`relay`, `echo`, `vote*`,
  `bind*`, `seal*`) require the process to have received its input
  (`input ≠ none`): the algorithm's handlers only run inside a called instance.

The state is exactly the protocol's own data, held in two boxes: each process
keeps its own local state beside the messages delivered to it, and the round's
message fabric keeps the per-sender pools and the corrupted set. `ImplState` is
their pair, so the network is a factor of the state and not a field of it — a
weaker fabric is a different second factor and leaves the rest of the round
alone. The three return transitions are cases
(1), (2), (3) of Algorithm 6's lines 23–29 and read nothing beyond the receipts
those cases name — case (1) an `n − f` `SEAL v` quorum, case (2) an `n − f`
any-`SEAL` quorum containing `SEAL v` together with `f + 1` `BIND v`s and
`|Valid| > 1`, case (3) an `n − f` `SEAL ⊥` quorum with `|Valid| > 1`. The
binding and grade information that the specification tracks is an abstraction
of these receipt patterns and lives only on the specification side; the
refinement (`ABA/GBCASim.lean`) supplies it from the receipts.
-/

namespace PLTS
namespace ABA
namespace GBCA

/-- The five-level message ladder of Algorithm 6. `VOTE`, `BIND` and `SEAL` may
carry the non-bit payload `⊥` (`none`). -/
inductive Msg : Type
  /-- `⟨INPUT, b⟩`. -/
  | input (b : Bool)
  /-- `⟨ECHO, b⟩`. -/
  | echo (b : Bool)
  /-- `⟨VOTE, v⟩` with `v ∈ {0, 1, ⊥}`. -/
  | vote (v : Option Bool)
  /-- `⟨BIND, v⟩` with `v ∈ {0, 1, ⊥}`. -/
  | bind (v : Option Bool)
  /-- `⟨echo5, v⟩` with `v ∈ {0, 1, ⊥}` (Algorithm 6 lines 21–22). -/
  | seal (v : Option Bool)
  deriving DecidableEq

/-- The local state of one process in one GBCA instance. -/
structure ProcState : Type where
  /-- The input bit received via `callG` (`none` before the call). -/
  input : Option Bool
  /-- Which `INPUT` payloads this process has multicast (own input or relay). -/
  sentInput : Bool → Bool
  /-- The `ECHO` payload multicast, if any (write-once). -/
  sentEcho : Option Bool
  /-- The `VOTE` payload multicast, if any (write-once; payload may be `⊥`). -/
  sentVote : Option (Option Bool)
  /-- The `BIND` payload multicast, if any (write-once; payload may be `⊥`). -/
  sentBind : Option (Option Bool)
  /-- The `SEAL` (`echo5`) payload multicast, if any (write-once; payload may
  be `⊥`). -/
  sentSeal : Option (Option Bool)
  /-- Whether this process has returned. -/
  returned : Bool
  deriving DecidableEq

/-- The initial local state: nothing received, nothing sent. -/
def ProcState.initial : ProcState where
  input := none
  sentInput := fun _ => false
  sentEcho := none
  sentVote := none
  sentBind := none
  sentSeal := none
  returned := false

/-! ### The two boxes of a round

The data of one round sits in two records. Each process holds its own protocol
state together with the messages delivered to it, and nothing else — there is
no record there of what it has multicast. The round's message fabric holds the
per-sender pools and the corrupted set. The instance's state below is their
pair, so every field of the algorithm is a field of one box or the other.

The fabric carries the name of the subsystem that composes it beside the
programs (`ABA/GBCAInstances.lean`). -/

/-- The stage record of one process: its own local state and the messages
delivered to it, indexed by sender. There is no record of what it has sent —
the sender's pool lives in the network. -/
structure StageRec (n : ℕ) : Type where
  /-- The process's own protocol state. -/
  proc : ProcState
  /-- `inbox k` — the messages from sender `k` delivered here. -/
  inbox : Fin n → Finset Msg
  deriving DecidableEq

namespace StageRec

variable {n : ℕ}

/-- The initial stage record: nothing received, nothing done. -/
def initial (n : ℕ) : StageRec n where
  proc := ProcState.initial
  inbox := fun _ => ∅

/-- The number of distinct senders from which this process has received `m`. -/
def recvCount (p : StageRec n) (m : Msg) : ℕ :=
  (Finset.univ.filter (fun k => m ∈ p.inbox k)).card

/-- The number of distinct senders of some received `ECHO`. -/
def echoCount (p : StageRec n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ b, Msg.echo b ∈ p.inbox k)).card

/-- The number of distinct senders of some received `VOTE`. -/
def voteCount (p : StageRec n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ v, Msg.vote v ∈ p.inbox k)).card

/-- The number of distinct senders of some received `BIND`. -/
def bindCount (p : StageRec n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ v, Msg.bind v ∈ p.inbox k)).card

/-- The number of distinct senders of some received `SEAL`. -/
def sealCount (p : StageRec n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ v, Msg.seal v ∈ p.inbox k)).card

/-- Both bits are backed by an `n − f` `INPUT` quorum among the delivered
messages. -/
def bothValid (P : Params) (p : StageRec P.n) : Prop :=
  P.n - P.f ≤ p.recvCount (.input true) ∧ P.n - P.f ≤ p.recvCount (.input false)

/-- Overwrite the local record. -/
def setP (p : StageRec n) (pr : ProcState) : StageRec n := { p with proc := pr }

/-- File `m` under the inbox row of sender `k`. -/
def deliverTo (p : StageRec n) (k : Fin n) (m : Msg) : StageRec n :=
  { p with inbox := Function.update p.inbox k (insert m (p.inbox k)) }

end StageRec

end GBCA

namespace GSub

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

end GSub

namespace GBCA

/-- **The state of one GBCA implementation instance**: the `n` stage records
beside the round's message fabric. -/
abbrev ImplState (n : ℕ) : Type := (∀ _ : Fin n, StageRec n) × GSub.GNetState n

namespace ImplState

variable {n : ℕ}

/-- Per-process local states. -/
def proc (s : ImplState n) : Fin n → ProcState := fun j => (s.1 j).proc

/-- `sent j` — the messages process `j` has multicast (D5). -/
def sent (s : ImplState n) : Fin n → Finset Msg := s.2.pool

/-- `recv i j` — the messages from sender `j` delivered to receiver `i`. -/
def recv (s : ImplState n) : Fin n → Fin n → Finset Msg := fun i => (s.1 i).inbox

/-- The corrupted set (the fabric's, kept in lockstep by `fail` broadcast). -/
def F (s : ImplState n) : Finset (Fin n) := s.2.F

@[simp] theorem proc_apply (u : ∀ _ : Fin n, StageRec n) (w : GSub.GNetState n)
    (j : Fin n) : proc (u, w) j = (u j).proc := rfl
@[simp] theorem sent_apply (u : ∀ _ : Fin n, StageRec n) (w : GSub.GNetState n) :
    sent (u, w) = w.pool := rfl
@[simp] theorem recv_apply (u : ∀ _ : Fin n, StageRec n) (w : GSub.GNetState n)
    (i : Fin n) : recv (u, w) i = (u i).inbox := rfl
@[simp] theorem F_apply (u : ∀ _ : Fin n, StageRec n) (w : GSub.GNetState n) :
    F (u, w) = w.F := rfl

/-- Dot notation resolves against `ImplState`, so the rule table and the
refinement read the pair in the four names the algorithm uses. -/
example (s : ImplState n) (i j : Fin n) : s.recv i j = (s.1 i).inbox j := rfl

/-- The initial implementation state. -/
def initial (n : ℕ) : ImplState n :=
  (fun _ => StageRec.initial n, GSub.GNetState.initial n)

/-! The two factors' own initial states project componentwise, so unfolding
`initial` leaves no residue. -/

@[simp] theorem _root_.PLTS.ABA.GBCA.StageRec.initial_proc (n : ℕ) :
    (StageRec.initial n).proc = ProcState.initial := rfl
@[simp] theorem _root_.PLTS.ABA.GBCA.StageRec.initial_inbox (n : ℕ) (k : Fin n) :
    (StageRec.initial n).inbox k = ∅ := rfl
@[simp] theorem _root_.PLTS.ABA.GSub.GNetState.initial_pool (n : ℕ) (j : Fin n) :
    (GSub.GNetState.initial n).pool j = ∅ := rfl
@[simp] theorem _root_.PLTS.ABA.GSub.GNetState.initial_F (n : ℕ) :
    (GSub.GNetState.initial n).F = ∅ := rfl

@[simp] theorem initial_proc (j : Fin n) : (initial n).proc j = ProcState.initial := rfl
@[simp] theorem initial_sent (j : Fin n) : (initial n).sent j = ∅ := rfl
@[simp] theorem initial_recv (i j : Fin n) : (initial n).recv i j = ∅ := rfl
@[simp] theorem initial_F : (initial n).F = ∅ := rfl

/-- The number of distinct senders from which `i` has received `m`. -/
def recvCount (s : ImplState n) (i : Fin n) (m : Msg) : ℕ :=
  (Finset.univ.filter (fun j => m ∈ s.recv i j)).card

/-- The number of distinct senders from which `i` has received some `ECHO`. -/
def echoCount (s : ImplState n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => ∃ b, Msg.echo b ∈ s.recv i j)).card

/-- The number of distinct senders from which `i` has received some `VOTE`. -/
def voteCount (s : ImplState n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => ∃ v, Msg.vote v ∈ s.recv i j)).card

/-- The number of distinct senders from which `i` has received some `BIND`. -/
def bindCount (s : ImplState n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => ∃ v, Msg.bind v ∈ s.recv i j)).card

/-- The number of distinct senders from which `i` has received some `SEAL`. -/
def sealCount (s : ImplState n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => ∃ v, Msg.seal v ∈ s.recv i j)).card

/-- `Valid = {0, 1}` at process `i`: both bits are backed by an `n − f`
`INPUT` quorum among `i`'s delivered messages. -/
def bothValid (P : Params) (s : ImplState P.n) (i : Fin P.n) : Prop :=
  P.n - P.f ≤ s.recvCount i (.input true) ∧ P.n - P.f ≤ s.recvCount i (.input false)

/-- Both bits of a `bothValid` evidence, indexed by the bit. -/
theorem bothValid_le {P : Params} {s : ImplState P.n} {i : Fin P.n}
    (h : s.bothValid P i) (b : Bool) : P.n - P.f ≤ s.recvCount i (.input b) := by
  cases b
  · exact h.2
  · exact h.1

/-! ### State update helpers -/

/-- Update the local state of process `j`. -/
def setProc (s : ImplState n) (j : Fin n) (p : ProcState) : ImplState n :=
  (Function.update s.1 j ((s.1 j).setP p), s.2)

@[simp] theorem setProc_sent (s : ImplState n) (j : Fin n) (p : ProcState) :
    (s.setProc j p).sent = s.sent := rfl
@[simp] theorem setProc_F (s : ImplState n) (j : Fin n) (p : ProcState) :
    (s.setProc j p).F = s.F := rfl

@[simp] theorem setProc_recv (s : ImplState n) (j : Fin n) (p : ProcState) :
    (s.setProc j p).recv = s.recv := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [setProc, recv, StageRec.setP]
  · simp [setProc, recv, Function.update_of_ne hi]

@[simp] theorem setProc_proc_self (s : ImplState n) (j : Fin n) (p : ProcState) :
    (s.setProc j p).proc j = p := by
  simp [setProc, proc, StageRec.setP]

theorem setProc_proc_ne (s : ImplState n) (j : Fin n) (p : ProcState)
    {k : Fin n} (h : k ≠ j) : (s.setProc j p).proc k = s.proc k := by
  simp [setProc, proc, Function.update_of_ne h]

/-! A record write leaves every reading of the delivered sets alone. -/

@[simp] theorem setProc_recvCount (s : ImplState n) (j : Fin n) (p : ProcState)
    (i : Fin n) (m : Msg) : (s.setProc j p).recvCount i m = s.recvCount i m := by
  simp [recvCount, setProc_recv]
@[simp] theorem setProc_echoCount (s : ImplState n) (j : Fin n) (p : ProcState)
    (i : Fin n) : (s.setProc j p).echoCount i = s.echoCount i := by
  simp [echoCount, setProc_recv]
@[simp] theorem setProc_voteCount (s : ImplState n) (j : Fin n) (p : ProcState)
    (i : Fin n) : (s.setProc j p).voteCount i = s.voteCount i := by
  simp [voteCount, setProc_recv]
@[simp] theorem setProc_bindCount (s : ImplState n) (j : Fin n) (p : ProcState)
    (i : Fin n) : (s.setProc j p).bindCount i = s.bindCount i := by
  simp [bindCount, setProc_recv]
@[simp] theorem setProc_sealCount (s : ImplState n) (j : Fin n) (p : ProcState)
    (i : Fin n) : (s.setProc j p).sealCount i = s.sealCount i := by
  simp [sealCount, setProc_recv]
@[simp] theorem setProc_bothValid {P : Params} (s : ImplState P.n) (j : Fin P.n)
    (p : ProcState) (i : Fin P.n) :
    (s.setProc j p).bothValid P i ↔ s.bothValid P i := by
  simp [bothValid]

/-- Process `j` multicasts `m`: the fabric pools it under `j`. -/
def mcast (s : ImplState n) (j : Fin n) (m : Msg) : ImplState n :=
  (s.1, s.2.gpool j m)

@[simp] theorem mcast_proc (s : ImplState n) (j : Fin n) (m : Msg) :
    (s.mcast j m).proc = s.proc := rfl
@[simp] theorem mcast_recv (s : ImplState n) (j : Fin n) (m : Msg) :
    (s.mcast j m).recv = s.recv := rfl
@[simp] theorem mcast_F (s : ImplState n) (j : Fin n) (m : Msg) :
    (s.mcast j m).F = s.F := rfl

/-! A multicast is the fabric's write alone, so no reading of the delivered
sets moves. -/

@[simp] theorem mcast_recvCount (s : ImplState n) (j : Fin n) (m : Msg)
    (i : Fin n) (m' : Msg) : (s.mcast j m).recvCount i m' = s.recvCount i m' := rfl
@[simp] theorem mcast_echoCount (s : ImplState n) (j : Fin n) (m : Msg) (i : Fin n) :
    (s.mcast j m).echoCount i = s.echoCount i := rfl
@[simp] theorem mcast_voteCount (s : ImplState n) (j : Fin n) (m : Msg) (i : Fin n) :
    (s.mcast j m).voteCount i = s.voteCount i := rfl
@[simp] theorem mcast_bindCount (s : ImplState n) (j : Fin n) (m : Msg) (i : Fin n) :
    (s.mcast j m).bindCount i = s.bindCount i := rfl
@[simp] theorem mcast_sealCount (s : ImplState n) (j : Fin n) (m : Msg) (i : Fin n) :
    (s.mcast j m).sealCount i = s.sealCount i := rfl
@[simp] theorem mcast_bothValid {P : Params} (s : ImplState P.n) (j : Fin P.n)
    (m : Msg) (i : Fin P.n) : (s.mcast j m).bothValid P i ↔ s.bothValid P i := Iff.rfl

/-- Membership in a sent pool after a multicast. -/
theorem mem_mcast_sent {s : ImplState n} {j : Fin n} {m : Msg} {k : Fin n} {m' : Msg} :
    m' ∈ (s.mcast j m).sent k ↔ (k = j ∧ m' = m) ∨ m' ∈ s.sent k := by
  change m' ∈ (s.2.gpool j m).pool k ↔ (k = j ∧ m' = m) ∨ m' ∈ s.2.pool k
  exact GSub.GNetState.mem_gpool

theorem sent_subset_mcast (s : ImplState n) (j : Fin n) (m : Msg) (k : Fin n) :
    s.sent k ⊆ (s.mcast j m).sent k :=
  fun _ h => mem_mcast_sent.mpr (Or.inr h)

/-- The adversary delivers `m` from sender `j` to receiver `i`: the receiver's
stage record files it under `j`'s row. -/
def recvMsg (s : ImplState n) (i j : Fin n) (m : Msg) : ImplState n :=
  (Function.update s.1 i ((s.1 i).deliverTo j m), s.2)

@[simp] theorem recvMsg_sent (s : ImplState n) (i j : Fin n) (m : Msg) :
    (s.recvMsg i j m).sent = s.sent := rfl
@[simp] theorem recvMsg_F (s : ImplState n) (i j : Fin n) (m : Msg) :
    (s.recvMsg i j m).F = s.F := rfl

@[simp] theorem recvMsg_proc (s : ImplState n) (i j : Fin n) (m : Msg) :
    (s.recvMsg i j m).proc = s.proc := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [recvMsg, proc, StageRec.deliverTo]
  · simp [recvMsg, proc, Function.update_of_ne hk]

/-- Membership in a delivered set after a delivery. -/
theorem mem_recvMsg_recv {s : ImplState n} {i j : Fin n} {m : Msg}
    {i' j' : Fin n} {m' : Msg} :
    m' ∈ (s.recvMsg i j m).recv i' j' ↔
      (i' = i ∧ j' = j ∧ m' = m) ∨ m' ∈ s.recv i' j' := by
  by_cases hi : i' = i
  · subst hi
    change m' ∈ (Function.update s.1 i' ((s.1 i').deliverTo j m) i').inbox j' ↔ _
    rw [Function.update_self]
    change m' ∈ Function.update ((s.1 i').inbox) j (insert m ((s.1 i').inbox j)) j' ↔ _
    by_cases hj : j' = j
    · subst hj
      rw [Function.update_self, Finset.mem_insert]
      simp [recv]
    · rw [Function.update_of_ne hj]
      simp [hj, recv]
  · change m' ∈ (Function.update s.1 i ((s.1 i).deliverTo j m) i').inbox j' ↔ _
    rw [Function.update_of_ne hi]
    simp [hi, recv]

/-- Deliveries only grow the receiver counts. -/
theorem recvCount_le_recvMsg (s : ImplState n) (i j : Fin n) (m : Msg)
    (i' : Fin n) (m' : Msg) :
    s.recvCount i' m' ≤ (s.recvMsg i j m).recvCount i' m' := by
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, mem_recvMsg_recv.mpr (Or.inr hk.2)⟩

/-- Corruption (deviation D1): total, Dirac, in lockstep with the spec's, and
the fabric's own row — the stage records are corruption-blind. -/
def corrupt (P : Params) (id : Fin P.n) (s : ImplState P.n) : ImplState P.n :=
  (s.1, GSub.GNetState.corrupt P id s.2)

@[simp] theorem corrupt_proc {P : Params} (s : ImplState P.n) (id : Fin P.n) :
    (s.corrupt P id).proc = s.proc := rfl
@[simp] theorem corrupt_recv {P : Params} (s : ImplState P.n) (id : Fin P.n) :
    (s.corrupt P id).recv = s.recv := rfl
@[simp] theorem corrupt_recvCount {P : Params} (s : ImplState P.n) (id : Fin P.n)
    (i : Fin P.n) (m : Msg) :
    (s.corrupt P id).recvCount i m = s.recvCount i m := rfl
@[simp] theorem corrupt_sent {P : Params} (s : ImplState P.n) (id : Fin P.n) :
    (s.corrupt P id).sent = s.sent := by
  unfold corrupt sent GSub.GNetState.corrupt; split <;> rfl

/-- The corrupted set after a corruption. `F` is the one field corruption
writes, and the budget guard sits in the fabric, so the reading is stated here
rather than reached by unfolding. Not a simp lemma: it introduces an `ite`. -/
theorem corrupt_F {P : Params} (s : ImplState P.n) (id : Fin P.n) :
    (s.corrupt P id).F = if id ∉ s.F ∧ s.F.card < P.f then insert id s.F else s.F := by
  unfold corrupt F GSub.GNetState.corrupt
  split_ifs <;> rfl

theorem corrupt_F_subset {P : Params} (s : ImplState P.n) (id : Fin P.n) :
    s.F ⊆ (s.corrupt P id).F := by
  rw [corrupt_F]
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

theorem corrupt_card_le {P : Params} (s : ImplState P.n) (id : Fin P.n)
    (hF : s.F.card ≤ P.f) : (s.corrupt P id).F.card ≤ P.f := by
  rw [corrupt_F]
  split
  · next hc =>
    have h2 := hc.2
    have h3 := Finset.card_insert_le id s.F
    omega
  · exact hF

/-! ### Quorum counting -/

/-- A set strictly larger than `F` has a member outside `F`. -/
theorem exists_honest_of_card_lt {Q F : Finset (Fin n)} (h : F.card < Q.card) :
    ∃ j ∈ Q, j ∉ F := by
  by_contra hc
  refine absurd (Finset.card_le_card fun j hj => ?_) (not_le.mpr h)
  by_contra hjF
  exact hc ⟨j, hj, hjF⟩

/-- A receipt count exceeding `|G|` yields a sender outside `G`. -/
theorem exists_sender_notMem {P : Params} {s : ImplState P.n} (G : Finset (Fin P.n))
    {i : Fin P.n} {m : Msg} (h : G.card < s.recvCount i m) :
    ∃ j, j ∉ G ∧ m ∈ s.recv i j := by
  unfold recvCount at h
  obtain ⟨j, hjQ, hjF⟩ := exists_honest_of_card_lt h
  rw [Finset.mem_filter] at hjQ
  exact ⟨j, hjF, hjQ.2⟩

/-- Two `n − f` receipt quorums (at possibly different receivers) share an
honest sender: `(n−f) + (n−f) − n = n − 2f > f ≥ |F|`. -/
theorem exists_honest_recv₂ {P : Params} {s : ImplState P.n} (hF : s.F.card ≤ P.f)
    {i i' : Fin P.n} {m m' : Msg}
    (h : P.n - P.f ≤ s.recvCount i m) (h' : P.n - P.f ≤ s.recvCount i' m') :
    ∃ j, j ∉ s.F ∧ m ∈ s.recv i j ∧ m' ∈ s.recv i' j := by
  unfold recvCount at h h'
  have hcard := Finset.card_union_add_card_inter
    (Finset.univ.filter (fun j => m ∈ s.recv i j))
    (Finset.univ.filter (fun j => m' ∈ s.recv i' j))
  have hun : ((Finset.univ.filter (fun j => m ∈ s.recv i j)) ∪
      (Finset.univ.filter (fun j => m' ∈ s.recv i' j))).card ≤ P.n := by
    refine le_trans (Finset.card_le_univ _) ?_
    simp
  have hf := P.hf
  have hlt : s.F.card < ((Finset.univ.filter (fun j => m ∈ s.recv i j)) ∩
      (Finset.univ.filter (fun j => m' ∈ s.recv i' j))).card := by omega
  obtain ⟨j, hj, hjF⟩ := exists_honest_of_card_lt hlt
  rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hj
  exact ⟨j, hjF, hj.1.2, hj.2.2⟩

end ImplState

/-- The step relation of the round-`r` GBCA implementation instance
(ABDY22 Algorithm 6, the full five-level ladder). All transitions are Dirac. -/
inductive ImplStep (P : Params) (r : ℕ) :
    ImplState P.n → Lab P.n → PMF (ImplState P.n) → Prop
  /-- The environment call arrives: record the input and multicast
  `⟨INPUT, b⟩`. -/
  | call (s : ImplState P.n) (id : Fin P.n) (b : Bool)
      (h : (s.proc id).input = none) :
      ImplStep P r s (.callG r id b)
        (PMF.pure ((s.setProc id { s.proc id with
            input := some b,
            sentInput := Function.update (s.proc id).sentInput b true }).mcast
          id (.input b)))
  /-- Input-enabledness loop for `call`. -/
  | callLoop (s : ImplState P.n) (id : Fin P.n) (b : Bool) :
      ImplStep P r s (.callG r id b) (PMF.pure s)
  /-- Asynchronous delivery: the adversary moves a multicast message into a
  receiver's delivered set. -/
  | deliver (s : ImplState P.n) (i j : Fin P.n) (m : Msg) (h : m ∈ s.sent j) :
      ImplStep P r s .tau (PMF.pure (s.recvMsg i j m))
  /-- `INPUT` relay: `f + 1` receipts of `⟨INPUT, b⟩`, not yet multicast. -/
  | relay (s : ImplState P.n) (j : Fin P.n) (b : Bool)
      (hin : (s.proc j).input ≠ none)
      (hcnt : P.f + 1 ≤ s.recvCount j (.input b))
      (hsend : (s.proc j).sentInput b = false) :
      ImplStep P r s .tau
        (PMF.pure ((s.setProc j { s.proc j with
            sentInput := Function.update (s.proc j).sentInput b true }).mcast
          j (.input b)))
  /-- `ECHO`: an `n − f` `INPUT b` quorum puts `b` into `Valid` and, if no
  `ECHO` was sent yet, multicasts `⟨ECHO, b⟩`. -/
  | echo (s : ImplState P.n) (j : Fin P.n) (b : Bool)
      (hin : (s.proc j).input ≠ none)
      (hcnt : P.n - P.f ≤ s.recvCount j (.input b))
      (hsend : (s.proc j).sentEcho = none) :
      ImplStep P r s .tau
        (PMF.pure ((s.setProc j { s.proc j with sentEcho := some b }).mcast
          j (.echo b)))
  /-- `VOTE b` (wait case (a)): an `n − f` `ECHO b` quorum. -/
  | voteBit (s : ImplState P.n) (j : Fin P.n) (b : Bool)
      (hin : (s.proc j).input ≠ none)
      (hcnt : P.n - P.f ≤ s.recvCount j (.echo b))
      (hsend : (s.proc j).sentVote = none) :
      ImplStep P r s .tau
        (PMF.pure ((s.setProc j { s.proc j with sentVote := some (some b) }).mcast
          j (.vote (some b))))
  /-- `VOTE ⊥` (wait case (b)): `n − f` `ECHO`s of any payload and
  `|Valid| > 1`. -/
  | voteBot (s : ImplState P.n) (j : Fin P.n)
      (hin : (s.proc j).input ≠ none)
      (hcnt : P.n - P.f ≤ s.echoCount j)
      (hval : s.bothValid P j)
      (hsend : (s.proc j).sentVote = none) :
      ImplStep P r s .tau
        (PMF.pure ((s.setProc j { s.proc j with sentVote := some none }).mcast
          j (.vote none)))
  /-- `BIND b` (wait case (a)): an `n − f` `VOTE b` quorum. -/
  | bindBit (s : ImplState P.n) (j : Fin P.n) (b : Bool)
      (hin : (s.proc j).input ≠ none)
      (hcnt : P.n - P.f ≤ s.recvCount j (.vote (some b)))
      (hsend : (s.proc j).sentBind = none) :
      ImplStep P r s .tau
        (PMF.pure ((s.setProc j { s.proc j with sentBind := some (some b) }).mcast
          j (.bind (some b))))
  /-- `BIND ⊥` (wait case (b)): `n − f` `VOTE`s of any payload and
  `|Valid| > 1`. -/
  | bindBot (s : ImplState P.n) (j : Fin P.n)
      (hin : (s.proc j).input ≠ none)
      (hcnt : P.n - P.f ≤ s.voteCount j)
      (hval : s.bothValid P j)
      (hsend : (s.proc j).sentBind = none) :
      ImplStep P r s .tau
        (PMF.pure ((s.setProc j { s.proc j with sentBind := some none }).mcast
          j (.bind none)))
  /-- `SEAL b` (wait case (a)): an `n − f` `BIND b` quorum. -/
  | sealBit (s : ImplState P.n) (j : Fin P.n) (b : Bool)
      (hin : (s.proc j).input ≠ none)
      (hcnt : P.n - P.f ≤ s.recvCount j (.bind (some b)))
      (hsend : (s.proc j).sentSeal = none) :
      ImplStep P r s .tau
        (PMF.pure ((s.setProc j { s.proc j with sentSeal := some (some b) }).mcast
          j (.seal (some b))))
  /-- `SEAL ⊥` (wait case (b)): `n − f` `BIND`s of any payload and
  `|Valid| > 1`. -/
  | sealBot (s : ImplState P.n) (j : Fin P.n)
      (hin : (s.proc j).input ≠ none)
      (hcnt : P.n - P.f ≤ s.bindCount j)
      (hval : s.bothValid P j)
      (hsend : (s.proc j).sentSeal = none) :
      ImplStep P r s .tau
        (PMF.pure ((s.setProc j { s.proc j with sentSeal := some none }).mcast
          j (.seal none)))
  /-- Byzantine injection: a corrupted sender multicasts anything. -/
  | byz (s : ImplState P.n) (j : Fin P.n) (m : Msg) (h : j ∈ s.F) :
      ImplStep P r s .tau (PMF.pure (s.mcast j m))
  /-- `A`-return (decide case (1)): an `n − f` `SEAL v` quorum. -/
  | retA (s : ImplState P.n) (id : Fin P.n) (v : Bool)
      (hcnt : P.n - P.f ≤ s.recvCount id (.seal (some v)))
      (hr : (s.proc id).returned = false) :
      ImplStep P r s (.retG r id (.A v))
        (PMF.pure (s.setProc id { s.proc id with returned := true }))
  /-- `B`-return (decide case (2)): an `n − f` any-`SEAL` quorum containing
  `SEAL v`, `f + 1` `BIND v`s and `|Valid| > 1`. The `f + 1` `BIND v` receipts
  put an honest `BIND v` sender — hence an `n − f` `VOTE v` receipt quorum —
  behind every grade-1 output. -/
  | retB (s : ImplState P.n) (id : Fin P.n) (v : Bool)
      (hcnt : P.n - P.f ≤ s.sealCount id)
      (honce : ∃ k, Msg.seal (some v) ∈ s.recv id k)
      (hbind : P.f + 1 ≤ s.recvCount id (.bind (some v)))
      (hval : s.bothValid P id)
      (hr : (s.proc id).returned = false) :
      ImplStep P r s (.retG r id (.B v))
        (PMF.pure (s.setProc id { s.proc id with returned := true }))
  /-- `C`-return (decide case (3)): an `n − f` `SEAL ⊥` quorum and
  `|Valid| > 1`. -/
  | retC (s : ImplState P.n) (id : Fin P.n)
      (hcnt : P.n - P.f ≤ s.recvCount id (.seal none))
      (hval : s.bothValid P id)
      (hr : (s.proc id).returned = false) :
      ImplStep P r s (.retG r id .C)
        (PMF.pure (s.setProc id { s.proc id with returned := true }))
  /-- Corruption (deviation D1). -/
  | fail (s : ImplState P.n) (id : Fin P.n) :
      ImplStep P r s (.fail id) (PMF.pure (s.corrupt P id))

/-- The round-`r` GBCA implementation instance. -/
noncomputable def implInst (P : Params) (r : ℕ) : System (ImplState P.n) (Lab P.n) where
  init := ImplState.initial P.n
  step := ImplStep P r

@[simp] theorem implInst_init (P : Params) (r : ℕ) :
    (implInst P r).init = ImplState.initial P.n := rfl

@[simp] theorem implInst_step (P : Params) (r : ℕ) (s : ImplState P.n)
    (l : Lab P.n) (μ : PMF (ImplState P.n)) :
    (implInst P r).step s l μ ↔ ImplStep P r s l μ := Iff.rfl

/-- Every GBCA implementation transition is Dirac: the instance is an LTS. -/
theorem implInst_isLTS (P : Params) (r : ℕ) : (implInst P r).IsLTS := by
  rintro s l μ hstep
  cases hstep <;> exact ⟨_, rfl⟩

end GBCA
end ABA
end PLTS
