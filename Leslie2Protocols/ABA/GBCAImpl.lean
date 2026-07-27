/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCASpec

/-!
# The GBCA implementation instance (blueprint `alg:GBCA`)

The round-`r` instance of the **blueprint's** Graded Binding Crusader Agreement
protocol (`alg:GBCA`), as an LTS over the shared alphabet `ABA.Lab n`.

*Attribution.* `alg:GBCA` is a **4-round compression** of
ABDY22's 5-round Algorithm 6, not a transcription of it: ABDY22 adds an `echo4`
*and* an `echo5` round to BCA and decides on `echo5` evidence (`⟨echo4,·,v⟩`
from `≥ t+1`), whereas the blueprint elides the `echo5` round and reads the
decide conditions one level down (`f + 1` `VOTE b` where ABDY22 has `t + 1`
`echo4 v`). Graded agreement and validity still go through for the 4-round
variant under `n > 3f` (and the machine-checked `GBCA.Impl ⊑ GBCA.Spec`
corroborates it), so no theorem here is false; but this is the blueprint's
algorithm, not the cited ABDY22 Algorithm 6.

Each process runs the message pattern

* `INPUT b` — multicast on being called; relayed after `f + 1` receipts;
* `ECHO b` — multicast once `INPUT b` was received from `n − f` senders
  (which also puts `b` into the derived set `Valid`);
* `VOTE v` (`v ∈ {0,1,⊥}`) — a real bit after an `n − f` `ECHO b` quorum, `⊥`
  after `n − f` `ECHO`s of any payload with `|Valid| > 1`;
* `BIND v` — same pattern one level up, over `VOTE`s;
* return — grade `A b` after an `n − f` `BIND b` quorum, `B b` after an
  `n − f` any-`BIND` quorum containing `b` with `f + 1` `VOTE b`s and
  `|Valid| > 1`, and `C` after an `n − f` `BIND ⊥` quorum with `|Valid| > 1`.

Every transition is Dirac (`implInst_isLTS`); asynchrony and Byzantine
behaviour are modelled by nondeterministic `τ`-transitions.

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
  `bind*`) require the process to have received its input
  (`input ≠ none`): Algorithm 2's handlers only run inside a called instance.

The state is exactly the protocol's own data: the per-process local states,
the network, and the corrupted set. The three return transitions are
Algorithm 2's three wait-until cases and read nothing beyond the receipts
those cases name — case (a) an `n − f` `BIND v` quorum, case (b) an `n − f`
any-`BIND` quorum containing `BIND v` together with `f + 1` `VOTE v`s and
`|Valid| > 1`, case (c) an `n − f` `BIND ⊥` quorum with `|Valid| > 1`. The
`bind` and `grade` fields that the specification tracks are abstractions of
these receipt patterns and live only on the specification side; the
refinement (`ABA/GBCASim.lean`) supplies them from the receipts.
-/

namespace PLTS
namespace ABA
namespace GBCA

/-- The protocol messages of Algorithm 2. `VOTE` and `BIND` may carry the
non-bit payload `⊥` (`none`). -/
inductive Msg : Type
  /-- `⟨INPUT, b⟩`. -/
  | input (b : Bool)
  /-- `⟨ECHO, b⟩`. -/
  | echo (b : Bool)
  /-- `⟨VOTE, v⟩` with `v ∈ {0, 1, ⊥}`. -/
  | vote (v : Option Bool)
  /-- `⟨BIND, v⟩` with `v ∈ {0, 1, ⊥}`. -/
  | bind (v : Option Bool)
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
  returned := false

/-- The state of one GBCA implementation instance: the local states, the
set-based network (D5) and the corrupted set. -/
structure ImplState (n : ℕ) : Type where
  /-- Per-process local states. -/
  proc : Fin n → ProcState
  /-- `sent j` — the messages process `j` has multicast. -/
  sent : Fin n → Finset Msg
  /-- `recv i j` — the messages from sender `j` delivered to receiver `i`. -/
  recv : Fin n → Fin n → Finset Msg
  /-- The corrupted set (local copy, kept in lockstep by `fail` broadcast). -/
  F : Finset (Fin n)
  deriving DecidableEq

namespace ImplState

variable {n : ℕ}

/-- The initial implementation state. -/
def initial (n : ℕ) : ImplState n where
  proc := fun _ => ProcState.initial
  sent := fun _ => ∅
  recv := fun _ _ => ∅
  F := ∅

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
  { s with proc := Function.update s.proc j p }

@[simp] theorem setProc_sent (s : ImplState n) (j : Fin n) (p : ProcState) :
    (s.setProc j p).sent = s.sent := rfl
@[simp] theorem setProc_recv (s : ImplState n) (j : Fin n) (p : ProcState) :
    (s.setProc j p).recv = s.recv := rfl
@[simp] theorem setProc_F (s : ImplState n) (j : Fin n) (p : ProcState) :
    (s.setProc j p).F = s.F := rfl

@[simp] theorem setProc_proc_self (s : ImplState n) (j : Fin n) (p : ProcState) :
    (s.setProc j p).proc j = p := by
  simp [setProc]

theorem setProc_proc_ne (s : ImplState n) (j : Fin n) (p : ProcState)
    {k : Fin n} (h : k ≠ j) : (s.setProc j p).proc k = s.proc k := by
  simp [setProc, Function.update_of_ne h]

/-- Process `j` multicasts `m`: add it to `j`'s sent pool. -/
def mcast (s : ImplState n) (j : Fin n) (m : Msg) : ImplState n :=
  { s with sent := Function.update s.sent j (insert m (s.sent j)) }

@[simp] theorem mcast_proc (s : ImplState n) (j : Fin n) (m : Msg) :
    (s.mcast j m).proc = s.proc := rfl
@[simp] theorem mcast_recv (s : ImplState n) (j : Fin n) (m : Msg) :
    (s.mcast j m).recv = s.recv := rfl
@[simp] theorem mcast_F (s : ImplState n) (j : Fin n) (m : Msg) :
    (s.mcast j m).F = s.F := rfl

/-- Membership in a sent pool after a multicast. -/
theorem mem_mcast_sent {s : ImplState n} {j : Fin n} {m : Msg} {k : Fin n} {m' : Msg} :
    m' ∈ (s.mcast j m).sent k ↔ (k = j ∧ m' = m) ∨ m' ∈ s.sent k := by
  change m' ∈ Function.update s.sent j (insert m (s.sent j)) k ↔ _
  by_cases hk : k = j
  · subst hk
    rw [Function.update_self, Finset.mem_insert]
    simp
  · rw [Function.update_of_ne hk]
    simp [hk]

theorem sent_subset_mcast (s : ImplState n) (j : Fin n) (m : Msg) (k : Fin n) :
    s.sent k ⊆ (s.mcast j m).sent k :=
  fun _ h => mem_mcast_sent.mpr (Or.inr h)

/-- The adversary delivers `m` from sender `j` to receiver `i`. -/
def recvMsg (s : ImplState n) (i j : Fin n) (m : Msg) : ImplState n :=
  { s with recv :=
      Function.update s.recv i (Function.update (s.recv i) j (insert m (s.recv i j))) }

@[simp] theorem recvMsg_proc (s : ImplState n) (i j : Fin n) (m : Msg) :
    (s.recvMsg i j m).proc = s.proc := rfl
@[simp] theorem recvMsg_sent (s : ImplState n) (i j : Fin n) (m : Msg) :
    (s.recvMsg i j m).sent = s.sent := rfl
@[simp] theorem recvMsg_F (s : ImplState n) (i j : Fin n) (m : Msg) :
    (s.recvMsg i j m).F = s.F := rfl

/-- Membership in a delivered set after a delivery. -/
theorem mem_recvMsg_recv {s : ImplState n} {i j : Fin n} {m : Msg}
    {i' j' : Fin n} {m' : Msg} :
    m' ∈ (s.recvMsg i j m).recv i' j' ↔
      (i' = i ∧ j' = j ∧ m' = m) ∨ m' ∈ s.recv i' j' := by
  change m' ∈ Function.update s.recv i
      (Function.update (s.recv i) j (insert m (s.recv i j))) i' j' ↔ _
  by_cases hi : i' = i
  · subst hi
    rw [Function.update_self]
    by_cases hj : j' = j
    · subst hj
      rw [Function.update_self, Finset.mem_insert]
      simp
    · rw [Function.update_of_ne hj]
      simp [hj]
  · rw [Function.update_of_ne hi]
    simp [hi]

/-- Deliveries only grow the receiver counts. -/
theorem recvCount_le_recvMsg (s : ImplState n) (i j : Fin n) (m : Msg)
    (i' : Fin n) (m' : Msg) :
    s.recvCount i' m' ≤ (s.recvMsg i j m).recvCount i' m' := by
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, mem_recvMsg_recv.mpr (Or.inr hk.2)⟩

/-- Corruption (deviation D1): total, Dirac, in lockstep with the spec's. -/
def corrupt (P : Params) (id : Fin P.n) (s : ImplState P.n) : ImplState P.n :=
  if id ∉ s.F ∧ s.F.card < P.f then { s with F := insert id s.F } else s

@[simp] theorem corrupt_proc {P : Params} (s : ImplState P.n) (id : Fin P.n) :
    (s.corrupt P id).proc = s.proc := by
  unfold corrupt; split <;> rfl
@[simp] theorem corrupt_sent {P : Params} (s : ImplState P.n) (id : Fin P.n) :
    (s.corrupt P id).sent = s.sent := by
  unfold corrupt; split <;> rfl
@[simp] theorem corrupt_recv {P : Params} (s : ImplState P.n) (id : Fin P.n) :
    (s.corrupt P id).recv = s.recv := by
  unfold corrupt; split <;> rfl
@[simp] theorem corrupt_recvCount {P : Params} (s : ImplState P.n) (id : Fin P.n)
    (i : Fin P.n) (m : Msg) :
    (s.corrupt P id).recvCount i m = s.recvCount i m := by
  unfold corrupt; split <;> rfl

theorem corrupt_F_subset {P : Params} (s : ImplState P.n) (id : Fin P.n) :
    s.F ⊆ (s.corrupt P id).F := by
  unfold corrupt
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

theorem corrupt_card_le {P : Params} (s : ImplState P.n) (id : Fin P.n)
    (hF : s.F.card ≤ P.f) : (s.corrupt P id).F.card ≤ P.f := by
  unfold corrupt
  split
  · next hc =>
    change (insert id s.F).card ≤ P.f
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
(blueprint Algorithm 2). All transitions are Dirac. -/
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
  /-- Byzantine injection: a corrupted sender multicasts anything. -/
  | byz (s : ImplState P.n) (j : Fin P.n) (m : Msg) (h : j ∈ s.F) :
      ImplStep P r s .tau (PMF.pure (s.mcast j m))
  /-- `A`-return (wait case (a)): an `n − f` `BIND v` quorum. -/
  | retA (s : ImplState P.n) (id : Fin P.n) (v : Bool)
      (hcnt : P.n - P.f ≤ s.recvCount id (.bind (some v)))
      (hr : (s.proc id).returned = false) :
      ImplStep P r s (.retG r id (.A v))
        (PMF.pure (s.setProc id { s.proc id with returned := true }))
  /-- `B`-return (wait case (b)): an `n − f` any-`BIND` quorum containing
  `BIND v`, `f + 1` `VOTE v`s and `|Valid| > 1`. -/
  | retB (s : ImplState P.n) (id : Fin P.n) (v : Bool)
      (hcnt : P.n - P.f ≤ s.bindCount id)
      (honce : ∃ k, Msg.bind (some v) ∈ s.recv id k)
      (hvote : P.f + 1 ≤ s.recvCount id (.vote (some v)))
      (hval : s.bothValid P id)
      (hr : (s.proc id).returned = false) :
      ImplStep P r s (.retG r id (.B v))
        (PMF.pure (s.setProc id { s.proc id with returned := true }))
  /-- `C`-return (wait case (c)): an `n − f` `BIND ⊥` quorum and
  `|Valid| > 1`. -/
  | retC (s : ImplState P.n) (id : Fin P.n)
      (hcnt : P.n - P.f ≤ s.recvCount id (.bind none))
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
