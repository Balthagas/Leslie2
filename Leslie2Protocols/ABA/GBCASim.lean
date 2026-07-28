/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCAImpl
import Leslie2.Simulation.ForwardLTS

/-!
# The per-instance GBCA refinement

The round-`r` implementation instance (`GBCA.implInst`, ABDY22 Algorithm 6 —
the full six-level ladder, D18) forward-simulates the round-`r` specification
instance (`GBCA.specInst`, the exclusion-set specification, D19):
`GBCA.implRefines`.

The implementation state is the protocol's own data, so only `call`, `ret` and
`F` are read off it directly (`InstRel.call_eq`, `ret_eq`, `F_eq`). The
specification's `dead` and `grade` are bookkeeping the protocol never stores;
the relation carries receipt evidence for them instead:

* `dead_cert` — every dead bit `b` is covered by a monotone *kill certificate*
  `DeadCert P s b`: either the opposite bit owns the unique `n − f` `ECHO`
  receipt quorum (`EchoQuorum P s (!b)`, Case A), or an `n − f` wall of
  processes is each corrupted or committed, write-once, to a `VOTE` payload
  other than `some b` (`VoteWall P s b`, Case B). Both disjuncts make an
  `n − f` `VOTE b` receipt quorum — the sole gateway to any grade-≥1 evidence
  for `b` — impossible forever: a `VOTE b` quorum against Case A yields an
  honest double-`ECHO` sender (`echoQuorum_unique`, write-once `sentEcho`),
  and against Case B meets the wall only inside `F`, contradicting
  `2(n − f) > n + f` (`no_disjoint_quorums`). The relation bounds `dead` from
  above and never from below: which bits are actually dead is recovered by
  case analysis at the return rows, not stored.
* `gradeA_ev` / `gradeC_ev` — an `A`-side grade lock is backed by an `n − f`
  `SEAL v` receipt quorum, a `C`-side lock by an `n − f` `SEAL ⊥` quorum. Two
  opposing quorums intersect in an honest process that would have multicast
  two different `SEAL` payloads, contradicting the write-once `seal_once` —
  which is the A/C exclusivity the specification's grade latch demands
  (`grade_ne_false_of_seal_quorum`, `grade_ne_true_of_sealBot_quorum`).

The specification kills a bit by the internal τ-transition `bindUnset`, so an
implementation return that needs a not-yet-dead bit killed is answered by a
two-step weak burst (`weakLStep_tauThen`; `killThenRetA_burst`,
`killThenRetB_burst`, `killThenRetC_burst`). Every return row does the same
decidable case split on the specification's `dead`, and the burst fires
whenever the kill is missing. Each return's own evidence harvests the
certificate: `retA`'s `SEAL v` quorum and `retB`'s `f + 1` `BIND v` receipts
both route to an `n − f` `VOTE v` receipt quorum at an honest process
(`bind_receipts_of_seal_quorum`, `voteQuorum_of_bind_receipts`), which kills
`!v` — the quorum itself is a `VoteWall` (`deadCert_of_voteQuorum`) — and
certifies `v` alive (`not_deadCert_of_voteQuorum`, which is what discharges
the guard pair `v ∉ dead ∧ (!v) ∈ dead` and with it value agreement between
successive returns). The `C`-return's `SEAL ⊥` quorum yields a certificate
for *some* bit (`deadCert_of_sealBot_quorum`): if an honest bit-voter exists
anywhere, its `vote_conf` receipt quorum is Case A for the opposite bit;
otherwise the honest vote prefix is all-⊥ and the `VoteWall` holds for both
bits at once.

Both `bindUnset` guards come from one `ECHO` certificate (`bindUnset_guards`):
refine it to an `n − f` `INPUT v` receipt quorum (`inputQuorum_of_echoQuorum`),
whose honest senders hold an input (`input_called`, D8) — that is the quorum
guard (`quorum_of_msg_quorum`) — and whose count feeds
`Inv.supp_of_input_receipts` for the `f + 1` SuppOK count (D15). At the
`C`-return the guards read the returner's own `|Valid| > 1` evidence instead
(`suppI_of_valid` closes both bits at once), so they are available whichever
bit the certificate names. `InstRel.spec_supp` transports the counts to the
specification side along `call_eq`/`F_eq`.

The invariant carries

* the corruption budget (`F_card`) and delivery soundness (`recv_sub`);
* protocol conformance of honest multicasts (`echo_conf`, `vote_input`,
  `vote_conf`, `bind_conf`, `bindBot_conf`, `seal_input`, `seal_conf`,
  `sealBot_conf`): each honest `ECHO`/`VOTE`/`BIND`/`SEAL` is backed by the
  receipt evidence that Algorithm 6 demands (receipts only grow, so the
  historical evidence persists in the current state);
* write-once recording of honest multicasts (`echo_once`, `vote_once`,
  `bind_once`, `seal_once`): an honest payload is the one held in the
  sender's write-once slot, so an honest process speaks at most one payload
  per level — `echo_once` carries Case A, `vote_once` the `VoteWall`
  counting, `seal_once` the grade exclusivity;
* participation (`input_called`, D8): an honest `INPUT` sender has been
  called;
* the *budget-robust* input-origin clause (`input_orig`): for **every**
  potential corruption superset `G ⊇ F` within the budget, an `INPUT b`
  multicast by a sender outside `G` traces back to a process outside `G`
  whose own input is `b`. The quantification over `G` is what makes the
  clause inductive: the classical "first honest sender of `INPUT b` is an
  originator" argument is temporal, but a relayer's `f + 1` receipt quorum
  always contains a sender outside `G`, so the pre-state clause — already
  quantified over the same `G` — supplies the witness, and corruption steps
  only shrink the range of `G`;
* the first-relayer support clause (`input_supp`, D15): an honest
  `INPUT b` multicast is by a genuine holder of `b` or already certifies
  `f + 1` F-blind genuine-holder support (`ImplSupp`) — inductive because
  the first honest relayer's `f + 1` `INPUT b` receipt senders are each in
  `F` or genuine holders, and the count is monotone under every step.
-/

open Stream'

namespace PLTS
namespace ABA
namespace GBCA

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

omit [Silent L] in
private theorem terminates₂ {l₀ l₁ : L} {q₁ q₂ : S} :
    (Seq.cons (l₀, q₁) (Seq.cons (l₁, q₂) Seq.nil) : Seq (L × S)).Terminates :=
  Seq.terminates_cons_iff.mpr (Seq.terminates_cons_iff.mpr Seq.terminates_nil)

omit [Silent L] in
/-- `endState` of a two-transition alternating sequence. -/
private theorem endState₂ (q₀ : S) (l₀ : L) (q₁ : S) (l₁ : L) (q₂ : S) :
    (⟨q₀, Seq.cons (l₀, q₁) (Seq.cons (l₁, q₂) Seq.nil)⟩ : AlterSeq S L).endState
      terminates₂ = q₂ := by
  classical
  set e : AlterSeq S L := ⟨q₀, Seq.cons (l₀, q₁) (Seq.cons (l₁, q₂) Seq.nil)⟩ with he
  have hterm : e.trans.Terminates := terminates₂
  have hfind : Nat.find hterm = 2 := by
    refine le_antisymm (Nat.find_le (show e.trans.TerminatedAt 2 from rfl)) ?_
    rw [Nat.le_find_iff]
    intro m hm
    interval_cases m
    · exact Seq.cons_not_terminatedAt_zero
    · intro hc
      exact absurd (hc : e.trans.get? 1 = none) (by simp [he])
  have hstate := AlterSeq.stateAt_find_eq_endState e hterm
  rw [hfind] at hstate
  have h2 : e.stateAt 2 = some q₂ := rfl
  rw [h2] at hstate
  exact (Option.some.inj hstate).symm

/-- **The burst.** A silent step followed by an external step is a weak
`l`-transition: the τ-step is the leading τ-closure. -/
theorem weakLStep_tauThen {q q₁ q' : S} {l : L}
    (h1 : sys.LStep q Silent.τ q₁) (h2 : sys.LStep q₁ l q')
    (hl : ¬ l = Silent.τ) : sys.weakLStep q l q' := by
  refine ⟨⟨q, Seq.cons (Silent.τ, q₁) (Seq.cons (l, q') Seq.nil)⟩, terminates₂,
    ?_, rfl, endState₂ q Silent.τ q₁ l q', ?_⟩
  · intro k l' s' hk
    match k with
    | 0 =>
      rw [Seq.get?_cons_zero] at hk
      injection hk with hk
      injection hk with ha hb
      subst ha; subst hb
      exact ⟨q, PMF.pure q₁, rfl, h1, by rw [PMF.mem_support_pure_iff]⟩
    | 1 =>
      rw [Seq.get?_cons_succ, Seq.get?_cons_zero] at hk
      injection hk with hk
      injection hk with ha hb
      subst ha; subst hb
      exact ⟨q₁, PMF.pure q', rfl, h2, by rw [PMF.mem_support_pure_iff]⟩
    | (k + 2) =>
      rw [Seq.get?_cons_succ, Seq.get?_cons_succ, Seq.get?_nil] at hk
      exact absurd hk (by simp)
  · have htail : sys.trace ⟨q₁, Seq.cons (l, q') Seq.nil⟩ = Seq.cons l Seq.nil := by
      rw [System.trace_cons_external sys q₁ l q' Seq.nil hl, System.trace_init]
    unfold System.trace at htail ⊢
    rw [Seq.filter_cons_neg _ _ (by simp)]
    exact htail

end WeakHelpers

/-! ### Counting kit: any-payload monotonicity and harvest variants -/

/-- Deliveries only grow the any-payload `ECHO` count. -/
theorem ImplState.echoCount_le_recvMsg {n : ℕ} (s : ImplState n) (i j : Fin n)
    (m : Msg) (i' : Fin n) : s.echoCount i' ≤ (s.recvMsg i j m).echoCount i' := by
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  obtain ⟨b, hb⟩ := hk.2
  exact ⟨hk.1, b, ImplState.mem_recvMsg_recv.mpr (Or.inr hb)⟩

/-- Deliveries only grow the any-payload `VOTE` count. -/
theorem ImplState.voteCount_le_recvMsg {n : ℕ} (s : ImplState n) (i j : Fin n)
    (m : Msg) (i' : Fin n) : s.voteCount i' ≤ (s.recvMsg i j m).voteCount i' := by
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  obtain ⟨v, hv⟩ := hk.2
  exact ⟨hk.1, v, ImplState.mem_recvMsg_recv.mpr (Or.inr hv)⟩

/-- Deliveries only grow the any-payload `BIND` count. -/
theorem ImplState.bindCount_le_recvMsg {n : ℕ} (s : ImplState n) (i j : Fin n)
    (m : Msg) (i' : Fin n) : s.bindCount i' ≤ (s.recvMsg i j m).bindCount i' := by
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  obtain ⟨v, hv⟩ := hk.2
  exact ⟨hk.1, v, ImplState.mem_recvMsg_recv.mpr (Or.inr hv)⟩

/-- Deliveries only grow the any-payload `SEAL` count. -/
theorem ImplState.sealCount_le_recvMsg {n : ℕ} (s : ImplState n) (i j : Fin n)
    (m : Msg) (i' : Fin n) : s.sealCount i' ≤ (s.recvMsg i j m).sealCount i' := by
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  obtain ⟨v, hv⟩ := hk.2
  exact ⟨hk.1, v, ImplState.mem_recvMsg_recv.mpr (Or.inr hv)⟩

/-- Corruption is blind to the any-payload `VOTE` count. -/
theorem ImplState.corrupt_voteCount {P : Params} (s : ImplState P.n)
    (id : Fin P.n) (i : Fin P.n) :
    (s.corrupt P id).voteCount i = s.voteCount i := by
  unfold ImplState.voteCount
  rw [ImplState.corrupt_recv]

/-- Corruption is blind to the any-payload `BIND` count. -/
theorem ImplState.corrupt_bindCount {P : Params} (s : ImplState P.n)
    (id : Fin P.n) (i : Fin P.n) :
    (s.corrupt P id).bindCount i = s.bindCount i := by
  unfold ImplState.bindCount
  rw [ImplState.corrupt_recv]

/-- Any-payload analogue of `exists_sender_notMem` at the `BIND` level: a
`bindCount` exceeding `|G|` yields a sender outside `G` together with its
payload. -/
theorem ImplState.exists_bind_sender_notMem {P : Params} {s : ImplState P.n}
    (G : Finset (Fin P.n)) {i : Fin P.n} (h : G.card < s.bindCount i) :
    ∃ j w, j ∉ G ∧ Msg.bind w ∈ s.recv i j := by
  unfold ImplState.bindCount at h
  obtain ⟨j, hjQ, hjG⟩ := ImplState.exists_honest_of_card_lt h
  rw [Finset.mem_filter] at hjQ
  obtain ⟨w, hw⟩ := hjQ.2
  exact ⟨j, w, hjG, hw⟩

/-! ### The concrete inductive invariant -/

variable {P : Params}

/-- `f + 1` F-blind genuine-holder support for `b` (D15): the impl-side
counterpart of the spec guards' SuppOK counts — the spec-side count follows
along `call_eq`/`F_eq` (`InstRel.spec_supp`). -/
def ImplSupp (P : Params) (s : ImplState P.n) (b : Bool) : Prop :=
  P.f + 1 ≤ (Finset.univ.filter
    (fun id => (s.proc id).input = some b ∨ id ∈ s.F)).card

/-- The support count is monotone: it survives any step that preserves
genuine holders and grows `F`. -/
theorem ImplSupp.mono {s s' : ImplState P.n} {b : Bool}
    (hproc : ∀ id, (s.proc id).input = some b → (s'.proc id).input = some b)
    (hF : s.F ⊆ s'.F) (h : ImplSupp P s b) : ImplSupp P s' b := by
  unfold ImplSupp at h ⊢
  refine le_trans h (Finset.card_le_card fun id hid => ?_)
  rw [Finset.mem_filter] at hid ⊢
  exact ⟨hid.1, hid.2.imp (hproc id) (fun hm => hF hm)⟩

/-- The inductive invariant of the GBCA implementation instance. See the
module docstring for the role of each clause. -/
structure Inv (P : Params) (s : ImplState P.n) : Prop where
  /-- Corruption budget. -/
  F_card : s.F.card ≤ P.f
  /-- Delivery soundness: everything delivered was multicast. -/
  recv_sub : ∀ i j m, m ∈ s.recv i j → m ∈ s.sent j
  /-- Honest `ECHO b` is backed by an `n − f` `INPUT b` receipt quorum. -/
  echo_conf : ∀ j b, j ∉ s.F → Msg.echo b ∈ s.sent j →
    P.n - P.f ≤ s.recvCount j (.input b)
  /-- Honest `ECHO` multicasts are recorded in the write-once `sentEcho`
  slot; in particular an honest process echoes at most one payload. -/
  echo_once : ∀ j b, j ∉ s.F → Msg.echo b ∈ s.sent j →
    (s.proc j).sentEcho = some b
  /-- Honest voters hold an input (D8). -/
  vote_input : ∀ j w, j ∉ s.F → Msg.vote w ∈ s.sent j → (s.proc j).input ≠ none
  /-- Honest `VOTE b` is backed by an `n − f` `ECHO b` receipt quorum. -/
  vote_conf : ∀ j b, j ∉ s.F → Msg.vote (some b) ∈ s.sent j →
    P.n - P.f ≤ s.recvCount j (.echo b)
  /-- Honest `VOTE` multicasts are recorded in the write-once `sentVote`
  slot; this is the level the `VoteWall` certificate counts. -/
  vote_once : ∀ j w, j ∉ s.F → Msg.vote w ∈ s.sent j →
    (s.proc j).sentVote = some w
  /-- Honest `BIND` multicasts are recorded in the write-once `sentBind`
  slot; in particular an honest process multicasts at most one payload. -/
  bind_once : ∀ j w, j ∉ s.F → Msg.bind w ∈ s.sent j →
    (s.proc j).sentBind = some w
  /-- Honest `BIND b` is backed by an `n − f` `VOTE b` receipt quorum. -/
  bind_conf : ∀ j b, j ∉ s.F → Msg.bind (some b) ∈ s.sent j →
    P.n - P.f ≤ s.recvCount j (.vote (some b))
  /-- Honest `BIND ⊥` is backed by `n − f` any-payload `VOTE` receipts. -/
  bindBot_conf : ∀ j, j ∉ s.F → Msg.bind none ∈ s.sent j →
    P.n - P.f ≤ s.voteCount j
  /-- Honest sealers hold an input (D8, one level up). -/
  seal_input : ∀ j w, j ∉ s.F → Msg.seal w ∈ s.sent j → (s.proc j).input ≠ none
  /-- Honest `SEAL` multicasts are recorded in the write-once `sentSeal`
  slot; this is the level that carries the A/C grade exclusivity. -/
  seal_once : ∀ j w, j ∉ s.F → Msg.seal w ∈ s.sent j →
    (s.proc j).sentSeal = some w
  /-- Honest `SEAL b` is backed by an `n − f` `BIND b` receipt quorum. -/
  seal_conf : ∀ j b, j ∉ s.F → Msg.seal (some b) ∈ s.sent j →
    P.n - P.f ≤ s.recvCount j (.bind (some b))
  /-- Honest `SEAL ⊥` is backed by `n − f` any-payload `BIND` receipts. -/
  sealBot_conf : ∀ j, j ∉ s.F → Msg.seal none ∈ s.sent j →
    P.n - P.f ≤ s.bindCount j
  /-- Budget-robust input origin: for every corruption superset `G` within
  the budget, an `INPUT b` multicast outside `G` traces back to an input `b`
  outside `G`. -/
  input_orig : ∀ (b : Bool) (G : Finset (Fin P.n)), s.F ⊆ G → G.card ≤ P.f →
    ∀ j, j ∉ G → Msg.input b ∈ s.sent j →
    ∃ m, m ∉ G ∧ (s.proc m).input = some b
  /-- Relayer-inductivized first-relayer support (D15): an honest `INPUT b`
  multicast is by a genuine holder of `b`, or certifies the `f + 1` F-blind
  genuine-holder support outright — the first honest relayer's `f + 1`
  `INPUT b` receipt senders are each in `F` or genuine holders. -/
  input_supp : ∀ (b : Bool) (j : Fin P.n), j ∉ s.F → Msg.input b ∈ s.sent j →
    (s.proc j).input = some b ∨ ImplSupp P s b
  /-- Participation one level down (D8): an honest `INPUT` sender has been
  called. -/
  input_called : ∀ j b, j ∉ s.F → Msg.input b ∈ s.sent j →
    (s.proc j).input ≠ none

theorem Inv.initial (P : Params) : Inv P (ImplState.initial P.n) where
  F_card := by simp [ImplState.initial]
  recv_sub := fun i j m h => absurd h (by simp [ImplState.initial])
  echo_conf := fun j b _ h => absurd h (by simp [ImplState.initial])
  echo_once := fun j b _ h => absurd h (by simp [ImplState.initial])
  vote_input := fun j w _ h => absurd h (by simp [ImplState.initial])
  vote_conf := fun j b _ h => absurd h (by simp [ImplState.initial])
  vote_once := fun j w _ h => absurd h (by simp [ImplState.initial])
  bind_once := fun j w _ h => absurd h (by simp [ImplState.initial])
  bind_conf := fun j b _ h => absurd h (by simp [ImplState.initial])
  bindBot_conf := fun j _ h => absurd h (by simp [ImplState.initial])
  seal_input := fun j w _ h => absurd h (by simp [ImplState.initial])
  seal_once := fun j w _ h => absurd h (by simp [ImplState.initial])
  seal_conf := fun j b _ h => absurd h (by simp [ImplState.initial])
  sealBot_conf := fun j _ h => absurd h (by simp [ImplState.initial])
  input_orig := fun b G _ _ j _ h => absurd h (by simp [ImplState.initial])
  input_supp := fun b j _ h => absurd h (by simp [ImplState.initial])
  input_called := fun j b _ h => absurd h (by simp [ImplState.initial])

/-- Harvest (D15): any `f + 1` `INPUT b` receipt count yields the F-blind
genuine-holder support — some honest non-holder sender's `input_supp` clause
closes, or else every sender is a holder-or-`F`-member and the senders
themselves witness the count. -/
theorem Inv.supp_of_input_receipts {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {b : Bool} (h : P.f + 1 ≤ s.recvCount i (.input b)) :
    ImplSupp P s b := by
  by_cases hc : ∃ k, Msg.input b ∈ s.recv i k ∧ k ∉ s.F ∧ (s.proc k).input ≠ some b
  · obtain ⟨k, hkr, hkF, hkin⟩ := hc
    rcases hI.input_supp b k hkF (hI.recv_sub i k _ hkr) with h' | h'
    · exact absurd h' hkin
    · exact h'
  · push Not at hc
    unfold ImplState.recvCount at h
    unfold ImplSupp
    refine le_trans h (Finset.card_le_card fun k hk => ?_)
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    by_cases hkF : k ∈ s.F
    · exact Or.inr hkF
    · exact Or.inl (hc k hk.2 hkF)

/-- The sender's `setProc` in a send step does not affect other processes. -/
private theorem proc_send_ne {s : ImplState P.n} {j : Fin P.n} {p : ProcState}
    {m : Msg} {k : Fin P.n} (hk : k ≠ j) :
    ((s.setProc j p).mcast j m).proc k = s.proc k := by
  rw [ImplState.mcast_proc, ImplState.setProc_proc_ne _ _ _ hk]

/-- **Invariant preservation, honest-send schema.** Process `j` updates its
local state to `p` and multicasts `m`. The hypotheses collect, clause by
clause, what the new message and the touched slot must satisfy; every frame
condition is discharged here once for all nine send rules (`call`, `relay`,
`echo`, `voteBit`, `voteBot`, `bindBit`, `bindBot`, `sealBit`, `sealBot`). -/
private theorem Inv.send {s : ImplState P.n} (hI : Inv P s) {j : Fin P.n}
    {p : ProcState} {m : Msg}
    (hpne : p.input ≠ none)
    (hpmono : ∀ b, (s.proc j).input = some b → p.input = some b)
    (hInp : ∀ b, m = .input b →
      p.input = some b ∨ P.f + 1 ≤ s.recvCount j (.input b))
    (hEchoC : ∀ b, m = .echo b → P.n - P.f ≤ s.recvCount j (.input b))
    (hVoteC : ∀ b, m = .vote (some b) → P.n - P.f ≤ s.recvCount j (.echo b))
    (hBindC : ∀ b, m = .bind (some b) →
      P.n - P.f ≤ s.recvCount j (.vote (some b)))
    (hBindBotC : m = .bind none → P.n - P.f ≤ s.voteCount j)
    (hSealC : ∀ b, m = .seal (some b) →
      P.n - P.f ≤ s.recvCount j (.bind (some b)))
    (hSealBotC : m = .seal none → P.n - P.f ≤ s.bindCount j)
    (hEchoO : ((∀ b, m ≠ .echo b) ∧ p.sentEcho = (s.proc j).sentEcho) ∨
      (∃ b, m = .echo b ∧ p.sentEcho = some b ∧ (s.proc j).sentEcho = none))
    (hVoteO : ((∀ w, m ≠ .vote w) ∧ p.sentVote = (s.proc j).sentVote) ∨
      (∃ w, m = .vote w ∧ p.sentVote = some w ∧ (s.proc j).sentVote = none))
    (hBindO : ((∀ w, m ≠ .bind w) ∧ p.sentBind = (s.proc j).sentBind) ∨
      (∃ w, m = .bind w ∧ p.sentBind = some w ∧ (s.proc j).sentBind = none))
    (hSealO : ((∀ w, m ≠ .seal w) ∧ p.sentSeal = (s.proc j).sentSeal) ∨
      (∃ w, m = .seal w ∧ p.sentSeal = some w ∧ (s.proc j).sentSeal = none)) :
    Inv P ((s.setProc j p).mcast j m) := by
  have htrans : ∀ (b : Bool) (k : Fin P.n), (s.proc k).input = some b →
      (((s.setProc j p).mcast j m).proc k).input = some b := by
    intro b k hk
    by_cases hkj : k = j
    · subst hkj
      rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
      exact hpmono b hk
    · rw [proc_send_ne hkj]
      exact hk
  refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- recv_sub
    intro i' j' m' hm'
    exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
  · -- echo_conf
    intro j' b hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · exact hEchoC b heq.symm
    · exact hI.echo_conf j' b hF hold
  · -- echo_once
    intro j' b hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
      rcases hEchoO with ⟨hne, _⟩ | ⟨b₀, hm0, hpe, _⟩
      · exact absurd heq.symm (hne b)
      · rw [hm0] at heq
        injection heq with hb
        rw [hpe, hb]
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        have hbase := hI.echo_once j' b hF hold
        rcases hEchoO with ⟨_, hpe⟩ | ⟨b₀, _, _, hnone⟩
        · rw [hpe]; exact hbase
        · rw [hnone] at hbase; exact absurd hbase (by simp)
      · rw [proc_send_ne hkj]
        exact hI.echo_once j' b hF hold
  · -- vote_input
    intro j' w hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, _⟩ | hold
    · rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
      exact hpne
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        exact hpne
      · rw [proc_send_ne hkj]
        exact hI.vote_input j' w hF hold
  · -- vote_conf
    intro j' b hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · exact hVoteC b heq.symm
    · exact hI.vote_conf j' b hF hold
  · -- vote_once
    intro j' w hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
      rcases hVoteO with ⟨hne, _⟩ | ⟨w₀, hm0, hpe, _⟩
      · exact absurd heq.symm (hne w)
      · rw [hm0] at heq
        injection heq with hw
        rw [hpe, hw]
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        have hbase := hI.vote_once j' w hF hold
        rcases hVoteO with ⟨_, hpe⟩ | ⟨w₀, _, _, hnone⟩
        · rw [hpe]; exact hbase
        · rw [hnone] at hbase; exact absurd hbase (by simp)
      · rw [proc_send_ne hkj]
        exact hI.vote_once j' w hF hold
  · -- bind_once
    intro j' w hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
      rcases hBindO with ⟨hne, _⟩ | ⟨w₀, hm0, hpe, _⟩
      · exact absurd heq.symm (hne w)
      · rw [hm0] at heq
        injection heq with hw
        rw [hpe, hw]
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        have hbase := hI.bind_once j' w hF hold
        rcases hBindO with ⟨_, hpe⟩ | ⟨w₀, _, _, hnone⟩
        · rw [hpe]; exact hbase
        · rw [hnone] at hbase; exact absurd hbase (by simp)
      · rw [proc_send_ne hkj]
        exact hI.bind_once j' w hF hold
  · -- bind_conf
    intro j' b hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · exact hBindC b heq.symm
    · exact hI.bind_conf j' b hF hold
  · -- bindBot_conf
    intro j' hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · exact hBindBotC heq.symm
    · exact hI.bindBot_conf j' hF hold
  · -- seal_input
    intro j' w hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, _⟩ | hold
    · rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
      exact hpne
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        exact hpne
      · rw [proc_send_ne hkj]
        exact hI.seal_input j' w hF hold
  · -- seal_once
    intro j' w hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
      rcases hSealO with ⟨hne, _⟩ | ⟨w₀, hm0, hpe, _⟩
      · exact absurd heq.symm (hne w)
      · rw [hm0] at heq
        injection heq with hw
        rw [hpe, hw]
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        have hbase := hI.seal_once j' w hF hold
        rcases hSealO with ⟨_, hpe⟩ | ⟨w₀, _, _, hnone⟩
        · rw [hpe]; exact hbase
        · rw [hnone] at hbase; exact absurd hbase (by simp)
      · rw [proc_send_ne hkj]
        exact hI.seal_once j' w hF hold
  · -- seal_conf
    intro j' b hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · exact hSealC b heq.symm
    · exact hI.seal_conf j' b hF hold
  · -- sealBot_conf
    intro j' hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · exact hSealBotC heq.symm
    · exact hI.sealBot_conf j' hF hold
  · -- input_orig
    intro b G hFG hGc j' hjG hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rcases hInp b heq.symm with hp | hcnt
      · refine ⟨j', hjG, ?_⟩
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        exact hp
      · have hcnt' : G.card < s.recvCount j' (Msg.input b) := by omega
        obtain ⟨k, hkG, hkr⟩ := ImplState.exists_sender_notMem G hcnt'
        obtain ⟨m0, hmG, hmi⟩ :=
          hI.input_orig b G hFG hGc k hkG (hI.recv_sub j' k _ hkr)
        exact ⟨m0, hmG, htrans b m0 hmi⟩
    · obtain ⟨m0, hmG, hmi⟩ := hI.input_orig b G hFG hGc j' hjG hold
      exact ⟨m0, hmG, htrans b m0 hmi⟩
  · -- input_supp
    intro b j' hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rcases hInp b heq.symm with hp | hcnt
      · left
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        exact hp
      · right
        exact ImplSupp.mono (fun k hk => htrans b k hk) (fun _ hh => hh)
          (hI.supp_of_input_receipts hcnt)
    · rcases hI.input_supp b j' hF hold with hin | hsupp
      · left
        by_cases hkj : j' = j
        · subst hkj
          rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
          exact hpmono b hin
        · rw [proc_send_ne hkj]
          exact hin
      · right
        exact ImplSupp.mono (fun k hk => htrans b k hk) (fun _ hh => hh) hsupp
  · -- input_called
    intro j' b hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, _⟩ | hold
    · rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
      exact hpne
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        exact hpne
      · rw [proc_send_ne hkj]
        exact hI.input_called j' b hF hold

/-- **Invariant preservation, local-frame schema.** A `setProc` that keeps
the input and all four write-once slots (the return rules, which flip only
`returned`) preserves every clause. -/
private theorem Inv.setProc_frame {s : ImplState P.n} (hI : Inv P s)
    {id : Fin P.n} {p : ProcState}
    (h1 : p.input = (s.proc id).input)
    (h2 : p.sentEcho = (s.proc id).sentEcho)
    (h3 : p.sentVote = (s.proc id).sentVote)
    (h4 : p.sentBind = (s.proc id).sentBind)
    (h5 : p.sentSeal = (s.proc id).sentSeal) :
    Inv P (s.setProc id p) := by
  have hin : ∀ k, ((s.setProc id p).proc k).input = (s.proc k).input := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [ImplState.setProc_proc_self, h1]
    · rw [ImplState.setProc_proc_ne _ _ _ hk]
  have hech : ∀ k, ((s.setProc id p).proc k).sentEcho = (s.proc k).sentEcho := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [ImplState.setProc_proc_self, h2]
    · rw [ImplState.setProc_proc_ne _ _ _ hk]
  have hvot : ∀ k, ((s.setProc id p).proc k).sentVote = (s.proc k).sentVote := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [ImplState.setProc_proc_self, h3]
    · rw [ImplState.setProc_proc_ne _ _ _ hk]
  have hbin : ∀ k, ((s.setProc id p).proc k).sentBind = (s.proc k).sentBind := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [ImplState.setProc_proc_self, h4]
    · rw [ImplState.setProc_proc_ne _ _ _ hk]
  have hsea : ∀ k, ((s.setProc id p).proc k).sentSeal = (s.proc k).sentSeal := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [ImplState.setProc_proc_self, h5]
    · rw [ImplState.setProc_proc_ne _ _ _ hk]
  refine ⟨hI.F_card, hI.recv_sub, hI.echo_conf, ?_, ?_, hI.vote_conf, ?_, ?_,
    hI.bind_conf, hI.bindBot_conf, ?_, ?_, hI.seal_conf, hI.sealBot_conf,
    ?_, ?_, ?_⟩
  · intro j' b hF hm'
    rw [hech j']
    exact hI.echo_once j' b hF hm'
  · intro j' w hF hm'
    rw [hin j']
    exact hI.vote_input j' w hF hm'
  · intro j' w hF hm'
    rw [hvot j']
    exact hI.vote_once j' w hF hm'
  · intro j' w hF hm'
    rw [hbin j']
    exact hI.bind_once j' w hF hm'
  · intro j' w hF hm'
    rw [hin j']
    exact hI.seal_input j' w hF hm'
  · intro j' w hF hm'
    rw [hsea j']
    exact hI.seal_once j' w hF hm'
  · intro b G hFG hGc j' hjG hm'
    obtain ⟨m0, hmG, hmi⟩ := hI.input_orig b G hFG hGc j' hjG hm'
    exact ⟨m0, hmG, by rw [hin m0]; exact hmi⟩
  · intro b j' hF hm'
    rcases hI.input_supp b j' hF hm' with hji | hsupp
    · left
      rw [hin j']
      exact hji
    · right
      exact ImplSupp.mono (s := s) (fun k hk => by rw [hin k]; exact hk)
        (fun _ hh => hh) hsupp
  · intro j' b hF hm'
    rw [hin j']
    exact hI.input_called j' b hF hm'

/-- **Invariant preservation.** `Inv` is preserved by every implementation
step. -/
theorem Inv.step {r : ℕ} {s : ImplState P.n} {l : Lab P.n}
    {μ : PMF (ImplState P.n)} {s' : ImplState P.n} (hI : Inv P s)
    (hstep : ImplStep P r s l μ) (hs' : s' ∈ μ.support) : Inv P s' := by
  cases hstep with
  | call id b h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send (by simp) (fun b' hb' => absurd hb' (by rw [h]; simp))
      (fun b' heq => by injection heq with hb; subst hb; exact Or.inl rfl)
      (fun b' heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (Or.inl ⟨fun b' heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
  | callLoop id b =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hI
  | deliver i j m hsent =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, hI.echo_once, hI.vote_input, ?_, hI.vote_once,
      hI.bind_once, ?_, ?_, hI.seal_input, hI.seal_once, ?_, ?_, hI.input_orig,
      hI.input_supp, hI.input_called⟩
    · intro i' j' m' hm'
      rcases ImplState.mem_recvMsg_recv.mp hm' with ⟨rfl, rfl, rfl⟩ | hold
      · exact hsent
      · exact hI.recv_sub i' j' m' hold
    · intro j' b hF hm'
      exact le_trans (hI.echo_conf j' b hF hm')
        (ImplState.recvCount_le_recvMsg s i j m j' _)
    · intro j' b hF hm'
      exact le_trans (hI.vote_conf j' b hF hm')
        (ImplState.recvCount_le_recvMsg s i j m j' _)
    · intro j' b hF hm'
      exact le_trans (hI.bind_conf j' b hF hm')
        (ImplState.recvCount_le_recvMsg s i j m j' _)
    · intro j' hF hm'
      exact le_trans (hI.bindBot_conf j' hF hm')
        (ImplState.voteCount_le_recvMsg s i j m j')
    · intro j' b hF hm'
      exact le_trans (hI.seal_conf j' b hF hm')
        (ImplState.recvCount_le_recvMsg s i j m j' _)
    · intro j' hF hm'
      exact le_trans (hI.sealBot_conf j' hF hm')
        (ImplState.bindCount_le_recvMsg s i j m j')
  | relay j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send hin (fun _ hb => hb)
      (fun b' heq => by injection heq with hb; subst hb; exact Or.inr hcnt)
      (fun b' heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (Or.inl ⟨fun b' heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
  | echo j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send hin (fun _ hb => hb) (fun b' heq => by simp at heq)
      (fun b' heq => by injection heq with hb; subst hb; exact hcnt)
      (fun b' heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun heq => by simp at heq)
      (Or.inr ⟨b, rfl, rfl, hsend⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
  | voteBit j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send hin (fun _ hb => hb) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq)
      (fun b' heq => by
        injection heq with hw; injection hw with hb; subst hb; exact hcnt)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (Or.inl ⟨fun b' heq => by simp at heq, rfl⟩)
      (Or.inr ⟨some b, rfl, rfl, hsend⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
  | voteBot j hin hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send hin (fun _ hb => hb) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (Or.inl ⟨fun b' heq => by simp at heq, rfl⟩)
      (Or.inr ⟨none, rfl, rfl, hsend⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
  | bindBit j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send hin (fun _ hb => hb) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun b' heq => by
        injection heq with hw; injection hw with hb; subst hb; exact hcnt)
      (fun heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun heq => by simp at heq)
      (Or.inl ⟨fun b' heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inr ⟨some b, rfl, rfl, hsend⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
  | bindBot j hin hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send hin (fun _ hb => hb) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun _ => hcnt)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (Or.inl ⟨fun b' heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inr ⟨none, rfl, rfl, hsend⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
  | sealBit j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send hin (fun _ hb => hb) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (fun b' heq => by
        injection heq with hw; injection hw with hb; subst hb; exact hcnt)
      (fun heq => by simp at heq)
      (Or.inl ⟨fun b' heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inr ⟨some b, rfl, rfl, hsend⟩)
  | sealBot j hin hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send hin (fun _ hb => hb) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun _ => hcnt)
      (Or.inl ⟨fun b' heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inr ⟨none, rfl, rfl, hsend⟩)
  | byz j m hjF =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hsentG : ∀ (G : Finset (Fin P.n)), s.F ⊆ G → ∀ j' m', j' ∉ G →
        m' ∈ (s.mcast j m).sent j' → m' ∈ s.sent j' := by
      intro G hFG j' m' hjG hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, _⟩ | hold
      · exact absurd (hFG hjF) hjG
      · exact hold
    have hs := fun j' m' (hF : j' ∉ s.F) =>
      hsentG s.F (Finset.Subset.refl _) j' m' hF
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · exact fun j' b hF hm' => hI.echo_conf j' b hF (hs j' _ hF hm')
    · exact fun j' b hF hm' => hI.echo_once j' b hF (hs j' _ hF hm')
    · exact fun j' w hF hm' => hI.vote_input j' w hF (hs j' _ hF hm')
    · exact fun j' b hF hm' => hI.vote_conf j' b hF (hs j' _ hF hm')
    · exact fun j' w hF hm' => hI.vote_once j' w hF (hs j' _ hF hm')
    · exact fun j' w hF hm' => hI.bind_once j' w hF (hs j' _ hF hm')
    · exact fun j' b hF hm' => hI.bind_conf j' b hF (hs j' _ hF hm')
    · exact fun j' hF hm' => hI.bindBot_conf j' hF (hs j' _ hF hm')
    · exact fun j' w hF hm' => hI.seal_input j' w hF (hs j' _ hF hm')
    · exact fun j' w hF hm' => hI.seal_once j' w hF (hs j' _ hF hm')
    · exact fun j' b hF hm' => hI.seal_conf j' b hF (hs j' _ hF hm')
    · exact fun j' hF hm' => hI.sealBot_conf j' hF (hs j' _ hF hm')
    · exact fun b G hFG hGc j' hjG hm' =>
        hI.input_orig b G hFG hGc j' hjG (hsentG G hFG j' _ hjG hm')
    · exact fun b j' hF hm' => hI.input_supp b j' hF (hs j' _ hF hm')
    · exact fun j' b hF hm' => hI.input_called j' b hF (hs j' _ hF hm')
  | retA id v hcnt hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hI.setProc_frame rfl rfl rfl rfl rfl
  | retB id v hcnt honce hbind hval hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hI.setProc_frame rfl rfl rfl rfl rfl
  | retC id hcnt hval hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hI.setProc_frame rfl rfl rfl rfl rfl
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hsub := ImplState.corrupt_F_subset s id
    have hFtr : ∀ j' : Fin P.n, j' ∉ (s.corrupt P id).F → j' ∉ s.F :=
      fun j' hF hj => hF (hsub hj)
    refine ⟨ImplState.corrupt_card_le s id hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      rw [ImplState.corrupt_recv] at hm'
      rw [ImplState.corrupt_sent]
      exact hI.recv_sub i' j' m' hm'
    · intro j' b hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_recvCount]
      exact hI.echo_conf j' b (hFtr j' hF) hm'
    · intro j' b hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.echo_once j' b (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.vote_input j' w (hFtr j' hF) hm'
    · intro j' b hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_recvCount]
      exact hI.vote_conf j' b (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.vote_once j' w (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.bind_once j' w (hFtr j' hF) hm'
    · intro j' b hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_recvCount]
      exact hI.bind_conf j' b (hFtr j' hF) hm'
    · intro j' hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_voteCount]
      exact hI.bindBot_conf j' (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.seal_input j' w (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.seal_once j' w (hFtr j' hF) hm'
    · intro j' b hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_recvCount]
      exact hI.seal_conf j' b (hFtr j' hF) hm'
    · intro j' hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_bindCount]
      exact hI.sealBot_conf j' (hFtr j' hF) hm'
    · intro b G hFG hGc j' hjG hm'
      rw [ImplState.corrupt_sent] at hm'
      obtain ⟨m0, hmG, hmi⟩ :=
        hI.input_orig b G (Finset.Subset.trans hsub hFG) hGc j' hjG hm'
      exact ⟨m0, hmG, by rw [ImplState.corrupt_proc]; exact hmi⟩
    · intro b j' hF' hm'
      rw [ImplState.corrupt_sent] at hm'
      rcases hI.input_supp b j' (hFtr j' hF') hm' with hin | hsupp
      · left
        rw [ImplState.corrupt_proc]
        exact hin
      · right
        refine ImplSupp.mono (s := s) (fun k hk => ?_) hsub hsupp
        rw [ImplState.corrupt_proc]
        exact hk
    · intro j' b hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.input_called j' b (hFtr j' hF) hm'

/-! ### The kill certificates -/

/-- Case A carrier: some process holds an `n − f` `ECHO v` receipt quorum.
The certificate is `F`-blind and receipt-monotone, hence stable under `fail`
and under every implementation step, and at most one bit can carry it
(`echoQuorum_unique`). -/
def EchoQuorum (P : Params) (s : ImplState P.n) (v : Bool) : Prop :=
  ∃ i, P.n - P.f ≤ s.recvCount i (.echo v)

/-- Harvest from `f + 1` `VOTE v` receipts: they contain an honest `VOTE v`
sender, whose `vote_conf` receipt quorum is the certificate. -/
theorem echoQuorum_of_vote_receipts {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.f + 1 ≤ s.recvCount i (.vote (some v))) :
    EchoQuorum P s v := by
  have hFc := hI.F_card
  have h' : s.F.card < s.recvCount i (Msg.vote (some v)) := by omega
  obtain ⟨k, hkF, hkr⟩ := ImplState.exists_sender_notMem s.F h'
  exact ⟨k, hI.vote_conf k v hkF (hI.recv_sub i k _ hkr)⟩

/-- Convenience corollary: an `n − f` `BIND v` receipt quorum refines to the
certificate through an honest binder's `bind_conf` quorum. -/
theorem echoQuorum_of_bind_quorum {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.recvCount i (.bind (some v))) :
    EchoQuorum P s v := by
  have hFc := hI.F_card
  have hfn := P.f_lt_n_sub_f
  have h' : s.F.card < s.recvCount i (Msg.bind (some v)) := by omega
  obtain ⟨j, hjF, hjr⟩ := ImplState.exists_sender_notMem s.F h'
  have h2 := hI.bind_conf j v hjF (hI.recv_sub i j _ hjr)
  exact echoQuorum_of_vote_receipts hI (i := j) (by omega)

/-- The certificate refines to an `n − f` `INPUT v` receipt quorum. -/
theorem inputQuorum_of_echoQuorum {s : ImplState P.n} (hI : Inv P s)
    {v : Bool} (h : EchoQuorum P s v) :
    ∃ m, P.n - P.f ≤ s.recvCount m (.input v) := by
  obtain ⟨i, hi⟩ := h
  have hFc := hI.F_card
  have hfn := P.f_lt_n_sub_f
  have h' : s.F.card < s.recvCount i (Msg.echo v) := by omega
  obtain ⟨m, hmF, hmr⟩ := ImplState.exists_sender_notMem s.F h'
  exact ⟨m, hI.echo_conf m v hmF (hI.recv_sub i m _ hmr)⟩

/-- At most one bit carries an `n − f` `ECHO` quorum: the two quorums
intersect in an honest sender, and `sentEcho` is write-once. -/
theorem echoQuorum_unique {s : ImplState P.n} (hI : Inv P s) {v v' : Bool}
    (h : EchoQuorum P s v) (h' : EchoQuorum P s v') : v = v' := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨i', hi'⟩ := h'
  obtain ⟨j, hjF, hj1, hj2⟩ := ImplState.exists_honest_recv₂ hI.F_card hi hi'
  have e1 := hI.echo_once j v hjF (hI.recv_sub i j _ hj1)
  have e2 := hI.echo_once j v' hjF (hI.recv_sub i' j _ hj2)
  rw [e1] at e2
  exact Option.some.inj e2

/-- Case B carrier: an `n − f` wall of processes each of which is corrupted
or has committed its write-once `VOTE` slot to a payload other than
`some b`. -/
def VoteWall (P : Params) (s : ImplState P.n) (b : Bool) : Prop :=
  P.n - P.f ≤ (Finset.univ.filter
    (fun j => j ∈ s.F ∨ ∃ w, (s.proc j).sentVote = some w ∧ w ≠ some b)).card

/-- The kill certificate licensing `b ∈ dead` on the specification side:
either the opposite bit owns the (unique) `n − f` `ECHO` receipt quorum, or
a `VoteWall` blocks `b` at the `VOTE` level. Both disjuncts make an `n − f`
`VOTE b` receipt quorum — the sole gateway to any grade-≥1 evidence for `b`
— impossible forever. -/
def DeadCert (P : Params) (s : ImplState P.n) (b : Bool) : Prop :=
  EchoQuorum P s (!b) ∨ VoteWall P s b

/-- The counting core: two `n − f`-sized subsets of `Fin n` meeting only
inside `F` contradict `|F| ≤ f` and `3f < n` (`2(n − f) > n + f`). The same
arithmetic as `exists_honest_recv₂`, exposed as a set statement because
`VoteWall` is a set of processes, not a receipt row. -/
theorem no_disjoint_quorums {Q D F : Finset (Fin P.n)}
    (hQ : P.n - P.f ≤ Q.card) (hD : P.n - P.f ≤ D.card)
    (hQD : Q ∩ D ⊆ F) (hF : F.card ≤ P.f) : False := by
  have hf := P.hf
  have hcard := Finset.card_union_add_card_inter Q D
  have hun : (Q ∪ D).card ≤ P.n := by
    refine le_trans (Finset.card_le_univ _) ?_
    simp
  have hint : (Q ∩ D).card ≤ F.card := Finset.card_le_card hQD
  omega

/-- **Certificate monotonicity**: receipts only grow, `sentVote` is
write-once, `F` only grows — so a kill certificate never expires. -/
theorem DeadCert.mono {s s' : ImplState P.n} {b : Bool}
    (hrecv : ∀ i j m, m ∈ s.recv i j → m ∈ s'.recv i j)
    (hvote : ∀ j w, (s.proc j).sentVote = some w → (s'.proc j).sentVote = some w)
    (hF : s.F ⊆ s'.F) : DeadCert P s b → DeadCert P s' b := by
  rintro (⟨i, hi⟩ | hw)
  · refine Or.inl ⟨i, le_trans hi (Finset.card_le_card fun k hk => ?_)⟩
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, hrecv i k _ hk.2⟩
  · refine Or.inr (le_trans hw (Finset.card_le_card fun k hk => ?_))
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    rcases hk.2 with hkF | ⟨w, hsv, hne⟩
    · exact Or.inl (hF hkF)
    · exact Or.inr ⟨w, hvote k w hsv, hne⟩

/-- `DeadCert` is stable under an honest send that respects the write-once
`sentVote` slot. -/
private theorem deadCert_send {s : ImplState P.n} {j : Fin P.n} {p : ProcState}
    {m : Msg} (hvote : ∀ w, (s.proc j).sentVote = some w → p.sentVote = some w)
    {b : Bool} (h : DeadCert P s b) :
    DeadCert P ((s.setProc j p).mcast j m) b :=
  DeadCert.mono (s := s) (fun _ _ _ hm => hm)
    (fun k w hk => by
      by_cases hkj : k = j
      · subst hkj
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        exact hvote w hk
      · rw [proc_send_ne hkj]
        exact hk)
    (Finset.Subset.refl _) h

/-- `DeadCert` is stable under a return (only `returned` flips). -/
private theorem deadCert_ret {s : ImplState P.n} {id : Fin P.n} {b : Bool}
    (h : DeadCert P s b) :
    DeadCert P (s.setProc id { s.proc id with returned := true }) b :=
  DeadCert.mono (s := s) (fun _ _ _ hm => hm)
    (fun k w hk => by
      by_cases hkj : k = id
      · subst hkj
        rw [ImplState.setProc_proc_self]
        exact hk
      · rw [ImplState.setProc_proc_ne _ _ _ hkj]
        exact hk)
    (Finset.Subset.refl _) h

/-! ### The harvest chains -/

/-- `f + 1` `BIND v` receipts exceed the corruption budget, so they contain
an honest binder, whose `bind_conf` wait-condition is an honest `n − f`
`VOTE v` receipt quorum — the object the binding argument counts. -/
theorem voteQuorum_of_bind_receipts {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.f + 1 ≤ s.recvCount i (.bind (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.recvCount k (.vote (some v)) := by
  have hFc := hI.F_card
  have h' : s.F.card < s.recvCount i (Msg.bind (some v)) := by omega
  obtain ⟨k, hkF, hkr⟩ := ImplState.exists_sender_notMem s.F h'
  exact ⟨k, hkF, hI.bind_conf k v hkF (hI.recv_sub i k _ hkr)⟩

/-- An `n − f` `SEAL v` receipt quorum contains an honest sealer, whose
`seal_conf` wait-condition is an honest `n − f` `BIND v` receipt quorum. -/
theorem bind_receipts_of_seal_quorum {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.recvCount i (.seal (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.recvCount k (.bind (some v)) := by
  have hFc := hI.F_card
  have hfn := P.f_lt_n_sub_f
  have h' : s.F.card < s.recvCount i (Msg.seal (some v)) := by omega
  obtain ⟨k, hkF, hkr⟩ := ImplState.exists_sender_notMem s.F h'
  exact ⟨k, hkF, hI.seal_conf k v hkF (hI.recv_sub i k _ hkr)⟩

/-- **Availability, kill side**: any `n − f` `VOTE v` receipt quorum kills
the opposite bit — the quorum's members are each corrupted or committed
(write-once) to `some v`, so the quorum itself is a `VoteWall` for `!v`. -/
theorem deadCert_of_voteQuorum {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.recvCount i (.vote (some v))) :
    DeadCert P s (!v) := by
  refine Or.inr (le_trans h (Finset.card_le_card fun k hk => ?_))
  rw [Finset.mem_filter] at hk ⊢
  refine ⟨hk.1, ?_⟩
  by_cases hkF : k ∈ s.F
  · exact Or.inl hkF
  · refine Or.inr ⟨some v, hI.vote_once k (some v) hkF (hI.recv_sub i k _ hk.2), ?_⟩
    intro hc
    injection hc with hc
    cases v <;> simp at hc

/-- **Availability, live side**: an `n − f` `VOTE v` receipt quorum refutes
both certificate cases for `v` itself — against Case A the harvested
`ECHO v` quorum meets the `ECHO (!v)` quorum in an honest double-echoer, and
against Case B the quorum meets the wall only inside `F`. -/
theorem not_deadCert_of_voteQuorum {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.recvCount i (.vote (some v))) :
    ¬ DeadCert P s v := by
  have hfn := P.f_lt_n_sub_f
  rintro (hq | hw)
  · have hv : EchoQuorum P s v := echoQuorum_of_vote_receipts hI (i := i) (by omega)
    have hvv := echoQuorum_unique hI hv hq
    cases v <;> simp at hvv
  · refine no_disjoint_quorums (F := s.F) h hw ?_ hI.F_card
    intro k hk
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hk
    obtain ⟨⟨-, hrecv⟩, -, hd⟩ := hk
    rcases hd with hkF | ⟨w, hsv, hne⟩
    · exact hkF
    · by_contra hkF
      have hcommit := hI.vote_once k (some v) hkF (hI.recv_sub i k _ hrecv)
      rw [hsv] at hcommit
      exact hne (Option.some.inj hcommit)

/-- **Availability at the `C`-return**: an `n − f` `SEAL ⊥` receipt quorum
certifies *some* dead bit. Classical dichotomy on "an honest bit-voter
exists somewhere": if yes, its `vote_conf` receipt quorum is Case A for the
opposite bit; if no, the quorum's honest sealer holds `n − f` any-`BIND`
receipts, its honest `BIND` sender can only have sent `BIND ⊥` (a bit `BIND`
needs an honest bit-voter), and that sender's `bindBot_conf` receipts pin an
`n − f` set of processes each corrupted or committed to `VOTE ⊥` — a
`VoteWall` for both bits at once. -/
theorem deadCert_of_sealBot_quorum {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} (h : P.n - P.f ≤ s.recvCount i (.seal none)) :
    ∃ b, DeadCert P s b := by
  classical
  have hFc := hI.F_card
  have hfn := P.f_lt_n_sub_f
  by_cases hcase : ∃ (k : Fin P.n) (b : Bool), k ∉ s.F ∧ Msg.vote (some b) ∈ s.sent k
  · obtain ⟨k, b, hkF, hks⟩ := hcase
    refine ⟨!b, Or.inl ?_⟩
    rw [Bool.not_not]
    exact ⟨k, hI.vote_conf k b hkF hks⟩
  · have h1 : s.F.card < s.recvCount i (Msg.seal none) := by omega
    obtain ⟨p, hpF, hpr⟩ := ImplState.exists_sender_notMem s.F h1
    have hbc : P.n - P.f ≤ s.bindCount p :=
      hI.sealBot_conf p hpF (hI.recv_sub i p _ hpr)
    have h2 : s.F.card < s.bindCount p := by omega
    obtain ⟨k, w, hkF, hkr⟩ := ImplState.exists_bind_sender_notMem s.F h2
    have hksent := hI.recv_sub p k _ hkr
    have hw : w = none := by
      cases w with
      | none => rfl
      | some v' =>
        exfalso
        have hvq := hI.bind_conf k v' hkF hksent
        have h3 : s.F.card < s.recvCount k (Msg.vote (some v')) := by omega
        obtain ⟨m', hmF, hmr⟩ := ImplState.exists_sender_notMem s.F h3
        exact hcase ⟨m', v', hmF, hI.recv_sub k m' _ hmr⟩
    subst hw
    have hvc : P.n - P.f ≤ s.voteCount k := hI.bindBot_conf k hkF hksent
    refine ⟨false, Or.inr (le_trans hvc (Finset.card_le_card fun q hq => ?_))⟩
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨hq.1, ?_⟩
    obtain ⟨wv, hwv⟩ := hq.2
    by_cases hqF : q ∈ s.F
    · exact Or.inl hqF
    · have hqs := hI.recv_sub k q _ hwv
      have hnone : wv = none := by
        cases wv with
        | none => rfl
        | some v' => exact absurd ⟨q, v', hqF, hqs⟩ hcase
      subst hnone
      exact Or.inr ⟨none, hI.vote_once q none hqF hqs, by simp⟩

/-! ### The simulation relation -/

/-- The simulation relation: the concrete invariant, the abstraction map for
the fields the protocol itself holds (spec `call` = concrete input, spec
`ret` = concrete return flags, spec `F` = concrete `F`), and receipt evidence
for the two fields it does not. `dead_cert` bounds `dead` from above — a kill
certificate for every dead bit — and never from below. -/
structure InstRel (P : Params) (s : ImplState P.n) (t : SpecState P.n) : Prop where
  /-- The concrete inductive invariant. -/
  inv : Inv P s
  /-- Spec inputs are the concrete inputs. -/
  call_eq : ∀ id, t.call id = (s.proc id).input
  /-- Spec return flags are the concrete return flags. -/
  ret_eq : ∀ id, t.ret id = (s.proc id).returned
  /-- The corrupted sets agree. -/
  F_eq : t.F = s.F
  /-- Every dead bit carries a monotone kill certificate. -/
  dead_cert : ∀ b, b ∈ t.dead → DeadCert P s b
  /-- An `A`-side grade lock is backed by an `n − f` `SEAL v` receipt quorum
  for some bit `v`. -/
  gradeA_ev : t.grade = some true →
    ∃ v i, P.n - P.f ≤ s.recvCount i (.seal (some v))
  /-- A `C`-side grade lock is backed by an `n − f` `SEAL ⊥` receipt
  quorum. -/
  gradeC_ev : t.grade = some false →
    ∃ i, P.n - P.f ≤ s.recvCount i (.seal none)

/-- The simulation relation of the round-`r` instance (the round index is
phantom: every round runs the same protocol). -/
def instRel (P : Params) (_r : ℕ) (s : ImplState P.n) (t : SpecState P.n) : Prop :=
  InstRel P s t

/-- The initial states are related. -/
theorem instRel_init (P : Params) (r : ℕ) :
    instRel P r (implInst P r).init (specInst P r).init where
  inv := Inv.initial P
  call_eq := fun _ => rfl
  ret_eq := fun _ => rfl
  F_eq := rfl
  dead_cert := fun b hb => absurd hb (Finset.notMem_empty b)
  gradeA_ev := fun h => absurd h (by simp [SpecState.initial])
  gradeC_ev := fun h => absurd h (by simp [SpecState.initial])

/-! ### Deriving the spec guards -/

/-- D15 harvest at `retB`/`retC`: `|Valid| > 1` evidence yields the
`f + 1` F-blind genuine-holder support for either bit — its `n − f ≥ f + 1`
`INPUT` receipt quorum for that bit sits at the returner itself. -/
theorem suppI_of_valid {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} (hv : s.bothValid P i) (b : Bool) : ImplSupp P s b := by
  have hfn := P.f_lt_n_sub_f
  exact hI.supp_of_input_receipts
    (le_trans (by omega) (ImplState.bothValid_le hv b))

/-- Transport an impl-side support count to the spec side along
`call_eq`/`F_eq`: the spec guards' SuppOK counts (D15). -/
theorem InstRel.spec_supp {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {b : Bool} (h : ImplSupp P s b) :
    P.f + 1 ≤ (Finset.univ.filter
      (fun id => t.call id = some b ∨ id ∈ t.F)).card := by
  unfold ImplSupp at h
  refine le_trans h (Finset.card_le_card fun k hk => ?_)
  rw [Finset.mem_filter] at hk ⊢
  refine ⟨hk.1, ?_⟩
  rw [hR.call_eq, hR.F_eq]
  exact hk.2

/-- D8 quorum harvest: any `n − f` receipt quorum of a message whose honest
senders must hold an input yields the spec's call quorum; corrupted senders
are absorbed into the `∪ F`. -/
theorem quorum_of_msg_quorum {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {i : Fin P.n} {m : Msg}
    (hpart : ∀ j, j ∉ s.F → m ∈ s.sent j → (s.proc j).input ≠ none)
    (h : P.n - P.f ≤ s.recvCount i m) : t.quorum P := by
  unfold SpecState.quorum
  unfold ImplState.recvCount at h
  refine le_trans h (Finset.card_le_card ?_)
  intro k hk
  rw [Finset.mem_filter] at hk
  rw [Finset.mem_union]
  by_cases hkF : k ∈ t.F
  · exact Or.inr hkF
  · refine Or.inl ?_
    rw [Finset.mem_filter]
    have hkF' : k ∉ s.F := by rwa [hR.F_eq] at hkF
    refine ⟨Finset.mem_univ _, hkF, ?_⟩
    rw [hR.call_eq]
    exact hpart k hkF' (hR.inv.recv_sub i k _ hk.2)

/-- **Both `bindUnset` guards from the single certificate.** -/
theorem bindUnset_guards {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {v : Bool} (hq : EchoQuorum P s v) :
    t.quorum P ∧ P.f + 1 ≤ (Finset.univ.filter
      (fun id => t.call id = some v ∨ id ∈ t.F)).card := by
  obtain ⟨m, hm⟩ := inputQuorum_of_echoQuorum hR.inv hq
  have hfn := P.f_lt_n_sub_f
  refine ⟨quorum_of_msg_quorum hR
    (fun j hj hm' => hR.inv.input_called j v hj hm') hm, ?_⟩
  exact hR.spec_supp (hR.inv.supp_of_input_receipts (le_trans (by omega) hm))

/-- A/C-exclusivity, `A`-side: an `n − f` `SEAL v` receipt quorum rules out
a `C`-side grade lock (the two `SEAL` quorums would intersect in an honest
process with two different `SEAL` payloads, against `seal_once`). -/
theorem grade_ne_false_of_seal_quorum {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {id : Fin P.n} {v : Bool}
    (hcnt : P.n - P.f ≤ s.recvCount id (.seal (some v))) :
    t.grade ≠ some false := by
  intro hg
  obtain ⟨i', hc⟩ := hR.gradeC_ev hg
  obtain ⟨j, hjF, hj1, hj2⟩ := ImplState.exists_honest_recv₂ hR.inv.F_card hcnt hc
  have e1 := hR.inv.seal_once j (some v) hjF (hR.inv.recv_sub id j _ hj1)
  have e2 := hR.inv.seal_once j none hjF (hR.inv.recv_sub i' j _ hj2)
  rw [e1] at e2
  exact absurd (Option.some.inj e2) (by simp)

/-- A/C-exclusivity, `C`-side: an `n − f` `SEAL ⊥` receipt quorum rules out
an `A`-side grade lock. -/
theorem grade_ne_true_of_sealBot_quorum {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {id : Fin P.n}
    (hcnt : P.n - P.f ≤ s.recvCount id (.seal none)) :
    t.grade ≠ some true := by
  intro hg
  obtain ⟨v', i', hc⟩ := hR.gradeA_ev hg
  obtain ⟨j, hjF, hj1, hj2⟩ := ImplState.exists_honest_recv₂ hR.inv.F_card hc hcnt
  have e1 := hR.inv.seal_once j (some v') hjF (hR.inv.recv_sub i' j _ hj1)
  have e2 := hR.inv.seal_once j none hjF (hR.inv.recv_sub id j _ hj2)
  rw [e1] at e2
  exact absurd (Option.some.inj e2) (by simp)

/-! ### Answering a return by a kill burst -/

/-- `bindUnset (!v) ; retA v` from a state where `!v` is still alive. The
`bindUnset (!v)` support guard reads `some (!(!v))`; `Bool.not_not` rewrites
it to `hw`'s `some v`. -/
theorem killThenRetA_burst {r : ℕ} {t : SpecState P.n} {id : Fin P.n} {v : Bool}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some v ∨ k ∈ t.F)).card)
    (hlive : v ∉ t.dead) (hkill : (!v) ∉ t.dead)
    (hg : t.grade = none ∨ t.grade = some true)
    (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id (.A v))
      { t with dead := insert (!v) t.dead, grade := some true,
               ret := Function.update t.ret id true } := by
  have h1 : (specInst P r).LStep t Silent.τ { t with dead := insert (!v) t.dead } :=
    Step.bindUnset t (!v) hq (by simpa only [Bool.not_not] using hw) hkill
  have h2 : (specInst P r).LStep { t with dead := insert (!v) t.dead }
      (.retG r id (.A v))
      { t with dead := insert (!v) t.dead, grade := some true,
               ret := Function.update t.ret id true } := by
    refine Step.retA { t with dead := insert (!v) t.dead } id v ?_
      (Finset.mem_insert_self (!v) t.dead) hg hr
    rw [Finset.mem_insert]
    rintro (hv | hv)
    · cases v <;> exact absurd hv (by decide)
    · exact hlive hv
  exact weakLStep_tauThen h1 h2 (by simp)

/-- `bindUnset (!v) ; retB v`: the same burst with the dissent count in
place of the grade latch. -/
theorem killThenRetB_burst {r : ℕ} {t : SpecState P.n} {id : Fin P.n} {v : Bool}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some v ∨ k ∈ t.F)).card)
    (hlive : v ∉ t.dead) (hkill : (!v) ∉ t.dead)
    (hd : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some (!v) ∨ k ∈ t.F)).card)
    (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id (.B v))
      { t with dead := insert (!v) t.dead,
               ret := Function.update t.ret id true } := by
  have h1 : (specInst P r).LStep t Silent.τ { t with dead := insert (!v) t.dead } :=
    Step.bindUnset t (!v) hq (by simpa only [Bool.not_not] using hw) hkill
  have h2 : (specInst P r).LStep { t with dead := insert (!v) t.dead }
      (.retG r id (.B v))
      { t with dead := insert (!v) t.dead,
               ret := Function.update t.ret id true } := by
    refine Step.retB { t with dead := insert (!v) t.dead } id v ?_
      (Finset.mem_insert_self (!v) t.dead) hd hr
    rw [Finset.mem_insert]
    rintro (hv | hv)
    · cases v <;> exact absurd hv (by decide)
    · exact hlive hv
  exact weakLStep_tauThen h1 h2 (by simp)

/-- `bindUnset b ; retC` from an all-alive state: the kill supplies the
`1 ≤ |dead|` witness (`insert` is nonempty). -/
theorem killThenRetC_burst {r : ℕ} {t : SpecState P.n} {id : Fin P.n} {b : Bool}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some (!b) ∨ k ∈ t.F)).card)
    (hkill : b ∉ t.dead)
    (hwT : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some true ∨ k ∈ t.F)).card)
    (hwF : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some false ∨ k ∈ t.F)).card)
    (hg : t.grade = none ∨ t.grade = some false)
    (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id .C)
      { t with dead := insert b t.dead, grade := some false,
               ret := Function.update t.ret id true } := by
  have h1 : (specInst P r).LStep t Silent.τ { t with dead := insert b t.dead } :=
    Step.bindUnset t b hq hw hkill
  have h2 : (specInst P r).LStep { t with dead := insert b t.dead }
      (.retG r id .C)
      { t with dead := insert b t.dead, grade := some false,
               ret := Function.update t.ret id true } :=
    Step.retC { t with dead := insert b t.dead } id
      (Finset.card_pos.mpr ⟨b, Finset.mem_insert_self b t.dead⟩) hwT hwF hg hr
  exact weakLStep_tauThen h1 h2 (by simp)

/-! ### The refinement -/

private theorem spec_corrupt_call (t : SpecState P.n) (id : Fin P.n) :
    (t.corrupt P id).call = t.call := by
  unfold SpecState.corrupt; split <;> rfl

private theorem spec_corrupt_ret (t : SpecState P.n) (id : Fin P.n) :
    (t.corrupt P id).ret = t.ret := by
  unfold SpecState.corrupt; split <;> rfl

private theorem spec_corrupt_dead (t : SpecState P.n) (id : Fin P.n) :
    (t.corrupt P id).dead = t.dead := by
  unfold SpecState.corrupt; split <;> rfl

private theorem spec_corrupt_grade (t : SpecState P.n) (id : Fin P.n) :
    (t.corrupt P id).grade = t.grade := by
  unfold SpecState.corrupt; split <;> rfl

/-- The two `corrupt` functions stay in lockstep on aligned corrupted sets
(a strong per-coordinate `fail` match, as required by the family lift). -/
private theorem corrupt_F_eq {t : SpecState P.n} {s : ImplState P.n}
    (hF : t.F = s.F) (id : Fin P.n) :
    (t.corrupt P id).F = (s.corrupt P id).F := by
  unfold SpecState.corrupt ImplState.corrupt
  by_cases hc : id ∉ s.F ∧ s.F.card < P.f
  · rw [if_pos (by rw [hF]; exact hc), if_pos hc]
    simp [hF]
  · rw [if_neg (by rw [hF]; exact hc), if_neg hc]
    exact hF

/-- **The per-instance GBCA refinement**: the round-`r` implementation
instance refines the round-`r` specification instance — a forward simulation
of the implementation by the specification along `instRel`. -/
theorem implRefines (P : Params) (r : ℕ) :
    ForwardSimulation (implInst P r) (specInst P r) (instRel P r) := by
  constructor
  intro q1 q2 hR l μ1 hstep q1' hq1'
  have hRR : InstRel P q1 q2 := hR
  have hI' : Inv P q1' := hRR.inv.step hstep hq1'
  cases hstep with
  | call id b h =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨{ q2 with call := Function.update q2.call id (some b) },
      Or.inr ⟨by simp, weakLStep_single
        (Step.call q2 id b (by rw [hRR.call_eq]; exact h)) (by simp)⟩,
      hI', ?_, ?_, hRR.F_eq, ?_,
      hRR.gradeA_ev, hRR.gradeC_ev⟩
    · intro k
      change Function.update q2.call id (some b) k = _
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        simp
      · rw [Function.update_of_ne hk, proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = id
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
    · intro b' hb'
      exact deadCert_send (by intro w hw; exact hw) (hRR.dead_cert b' hb')
  | callLoop id b =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    exact ⟨q2, Or.inr ⟨by simp,
      weakLStep_single (Step.callLoop q2 id b) (by simp)⟩, hRR⟩
  | deliver i j m hsent =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', hRR.call_eq, hRR.ret_eq, hRR.F_eq, ?_, ?_, ?_⟩
    · intro b hb
      exact DeadCert.mono (s := q1)
        (fun i' j' m' hm' => ImplState.mem_recvMsg_recv.mpr (Or.inr hm'))
        (fun k w hk => hk) (Finset.Subset.refl _) (hRR.dead_cert b hb)
    · intro hg
      obtain ⟨v0, i0, hi0⟩ := hRR.gradeA_ev hg
      exact ⟨v0, i0, le_trans hi0 (ImplState.recvCount_le_recvMsg q1 i j m i0 _)⟩
    · intro hg
      obtain ⟨i0, hi0⟩ := hRR.gradeC_ev hg
      exact ⟨i0, le_trans hi0 (ImplState.recvCount_le_recvMsg q1 i j m i0 _)⟩
  | relay j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => deadCert_send (by intro w hw; exact hw)
        (hRR.dead_cert b' hb'),
      hRR.gradeA_ev, hRR.gradeC_ev⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
  | echo j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => deadCert_send (by intro w hw; exact hw)
        (hRR.dead_cert b' hb'),
      hRR.gradeA_ev, hRR.gradeC_ev⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
  | voteBit j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => deadCert_send
        (by intro w hw; rw [hsend] at hw; simp at hw)
        (hRR.dead_cert b' hb'),
      hRR.gradeA_ev, hRR.gradeC_ev⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
  | voteBot j hin hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => deadCert_send
        (by intro w hw; rw [hsend] at hw; simp at hw)
        (hRR.dead_cert b' hb'),
      hRR.gradeA_ev, hRR.gradeC_ev⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
  | bindBit j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => deadCert_send (by intro w hw; exact hw)
        (hRR.dead_cert b' hb'),
      hRR.gradeA_ev, hRR.gradeC_ev⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
  | bindBot j hin hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => deadCert_send (by intro w hw; exact hw)
        (hRR.dead_cert b' hb'),
      hRR.gradeA_ev, hRR.gradeC_ev⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
  | sealBit j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => deadCert_send (by intro w hw; exact hw)
        (hRR.dead_cert b' hb'),
      hRR.gradeA_ev, hRR.gradeC_ev⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
  | sealBot j hin hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => deadCert_send (by intro w hw; exact hw)
        (hRR.dead_cert b' hb'),
      hRR.gradeA_ev, hRR.gradeC_ev⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
  | byz j m hjF =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    exact ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', hRR.call_eq, hRR.ret_eq, hRR.F_eq, hRR.dead_cert, hRR.gradeA_ev,
      hRR.gradeC_ev⟩
  | retA id v hcnt hr =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hret : q2.ret id = false := by rw [hRR.ret_eq]; exact hr
    have hfn := P.f_lt_n_sub_f
    obtain ⟨k₁, hk₁F, hbq⟩ := bind_receipts_of_seal_quorum hRR.inv hcnt
    obtain ⟨k, hkF, hvq⟩ :=
      voteQuorum_of_bind_receipts hRR.inv (i := k₁) (v := v) (by omega)
    have hlive : v ∉ q2.dead := fun hv =>
      not_deadCert_of_voteQuorum hRR.inv hvq (hRR.dead_cert v hv)
    have hgr : q2.grade = none ∨ q2.grade = some true := by
      have hne := grade_ne_false_of_seal_quorum hRR hcnt
      cases hg : q2.grade with
      | none => exact Or.inl rfl
      | some gb =>
        cases gb
        · exact absurd hg hne
        · exact Or.inr rfl
    by_cases hdead : (!v) ∈ q2.dead
    · refine ⟨{ q2 with grade := some true,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, weakLStep_single
          (Step.retA q2 id v hlive hdead hgr hret) (by simp)⟩,
        hI', ?_, ?_, hRR.F_eq,
        fun b hb => deadCert_ret (hRR.dead_cert b hb),
        fun _ => ⟨v, id, hcnt⟩,
        fun hgf => absurd hgf (by simp)⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.ret_eq k'
    · obtain ⟨hq, hw⟩ := bindUnset_guards hRR
        (echoQuorum_of_vote_receipts hRR.inv (i := k) (v := v) (by omega))
      refine ⟨{ q2 with dead := insert (!v) q2.dead, grade := some true,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, killThenRetA_burst hq hw hlive hdead hgr hret⟩,
        hI', ?_, ?_, hRR.F_eq, ?_,
        fun _ => ⟨v, id, hcnt⟩,
        fun hgf => absurd hgf (by simp)⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.ret_eq k'
      · intro b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact deadCert_ret (deadCert_of_voteQuorum hRR.inv hvq)
        · exact deadCert_ret (hRR.dead_cert b hb)
  | retB id v hcnt honce hbind hval hr =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hret : q2.ret id = false := by rw [hRR.ret_eq]; exact hr
    have hfn := P.f_lt_n_sub_f
    obtain ⟨k, hkF, hvq⟩ := voteQuorum_of_bind_receipts hRR.inv hbind
    have hlive : v ∉ q2.dead := fun hv =>
      not_deadCert_of_voteQuorum hRR.inv hvq (hRR.dead_cert v hv)
    have hd : P.f + 1 ≤ (Finset.univ.filter
        (fun k' => q2.call k' = some (!v) ∨ k' ∈ q2.F)).card :=
      hRR.spec_supp (suppI_of_valid hRR.inv hval (!v))
    by_cases hdead : (!v) ∈ q2.dead
    · refine ⟨{ q2 with ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, weakLStep_single
          (Step.retB q2 id v hlive hdead hd hret) (by simp)⟩,
        hI', ?_, ?_, hRR.F_eq,
        fun b hb => deadCert_ret (hRR.dead_cert b hb),
        hRR.gradeA_ev, hRR.gradeC_ev⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.ret_eq k'
    · obtain ⟨hq, hw⟩ := bindUnset_guards hRR
        (echoQuorum_of_vote_receipts hRR.inv (i := k) (v := v) (by omega))
      refine ⟨{ q2 with dead := insert (!v) q2.dead,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, killThenRetB_burst hq hw hlive hdead hd hret⟩,
        hI', ?_, ?_, hRR.F_eq, ?_, hRR.gradeA_ev, hRR.gradeC_ev⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.ret_eq k'
      · intro b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact deadCert_ret (deadCert_of_voteQuorum hRR.inv hvq)
        · exact deadCert_ret (hRR.dead_cert b hb)
  | retC id hcnt hval hr =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hret : q2.ret id = false := by rw [hRR.ret_eq]; exact hr
    have hwT : P.f + 1 ≤ (Finset.univ.filter
        (fun k' => q2.call k' = some true ∨ k' ∈ q2.F)).card :=
      hRR.spec_supp (suppI_of_valid hRR.inv hval true)
    have hwF : P.f + 1 ≤ (Finset.univ.filter
        (fun k' => q2.call k' = some false ∨ k' ∈ q2.F)).card :=
      hRR.spec_supp (suppI_of_valid hRR.inv hval false)
    have hgr : q2.grade = none ∨ q2.grade = some false := by
      have hne := grade_ne_true_of_sealBot_quorum hRR hcnt
      cases hg : q2.grade with
      | none => exact Or.inl rfl
      | some gb =>
        cases gb
        · exact Or.inr rfl
        · exact absurd hg hne
    rcases Finset.eq_empty_or_nonempty q2.dead with hde | hdne
    · -- `dead = ∅`: kill the certified bit, then return
      obtain ⟨b, hcert⟩ := deadCert_of_sealBot_quorum hRR.inv hcnt
      have hkill : b ∉ q2.dead := by
        rw [hde]
        exact Finset.notMem_empty b
      have hq : q2.quorum P := quorum_of_msg_quorum hRR
        (fun j hj hm' => hRR.inv.input_called j true hj hm')
        (ImplState.bothValid_le hval true)
      have hw : P.f + 1 ≤ (Finset.univ.filter
          (fun k' => q2.call k' = some (!b) ∨ k' ∈ q2.F)).card :=
        hRR.spec_supp (suppI_of_valid hRR.inv hval (!b))
      refine ⟨{ q2 with dead := insert b q2.dead, grade := some false,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, killThenRetC_burst hq hw hkill hwT hwF hgr hret⟩,
        hI', ?_, ?_, hRR.F_eq, ?_,
        fun hgt => absurd hgt (by simp),
        fun _ => ⟨id, hcnt⟩⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.ret_eq k'
      · intro b' hb'
        rw [Finset.mem_insert] at hb'
        rcases hb' with rfl | hb'
        · exact deadCert_ret hcert
        · exact deadCert_ret (hRR.dead_cert b' hb')
    · -- some bit is already dead: a single labelled step answers
      have hd1 : 1 ≤ q2.dead.card := Finset.card_pos.mpr hdne
      refine ⟨{ q2 with grade := some false,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, weakLStep_single
          (Step.retC q2 id hd1 hwT hwF hgr hret) (by simp)⟩,
        hI', ?_, ?_, hRR.F_eq,
        fun b hb => deadCert_ret (hRR.dead_cert b hb),
        fun hgt => absurd hgt (by simp),
        fun _ => ⟨id, hcnt⟩⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.ret_eq k'
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2.corrupt P id,
      Or.inr ⟨by simp, weakLStep_single (Step.fail q2 id) (by simp)⟩,
      hI', ?_, ?_, corrupt_F_eq hRR.F_eq id, ?_, ?_, ?_⟩
    · intro k
      rw [spec_corrupt_call, ImplState.corrupt_proc]
      exact hRR.call_eq k
    · intro k
      rw [spec_corrupt_ret, ImplState.corrupt_proc]
      exact hRR.ret_eq k
    · intro b hb
      rw [spec_corrupt_dead] at hb
      refine DeadCert.mono (s := q1) (fun i' j' m' hm' => ?_) (fun k w hk => ?_)
        (ImplState.corrupt_F_subset q1 id) (hRR.dead_cert b hb)
      · rw [ImplState.corrupt_recv]
        exact hm'
      · rw [ImplState.corrupt_proc]
        exact hk
    · intro hg
      rw [spec_corrupt_grade] at hg
      obtain ⟨v0, i0, hi0⟩ := hRR.gradeA_ev hg
      exact ⟨v0, i0, by rw [ImplState.corrupt_recvCount]; exact hi0⟩
    · intro hg
      rw [spec_corrupt_grade] at hg
      obtain ⟨i0, hi0⟩ := hRR.gradeC_ev hg
      exact ⟨i0, by rw [ImplState.corrupt_recvCount]; exact hi0⟩

end GBCA
end ABA
end PLTS
