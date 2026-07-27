/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCAImpl
import Leslie2.Simulation.ForwardLTS

/-!
# The per-instance GBCA refinement

The round-`r` implementation instance (`GBCA.implInst`, blueprint Algorithm 2)
forward-simulates the round-`r` specification instance (`GBCA.specInst`,
blueprint Transition System 2): `GBCA.implRefines`.

The implementation state is the protocol's own data, so only `call`, `ret` and
`F` are read off it directly (`InstRel.call_eq`, `ret_eq`, `F_eq`). The
specification's `bind` and `grade` are bookkeeping the protocol never stores;
the relation carries receipt evidence for them instead:

* `bind_cert` — whenever the specification is bound to `v`, some process holds
  an `n − f` `ECHO v` receipt quorum (`EchoQuorum`). The certificate is
  `F`-blind and receipt-monotone, hence stable under `fail` and under every
  implementation step, and at most one bit can carry it (`echoQuorum_unique`,
  from the write-once `sentEcho`), which pins the value a return hands out to
  the value already bound (`retA_value_agrees`, `retB_value_agrees`).
* `gradeA_ev` / `gradeC_ev` — an `A`-side grade lock is backed by an `n − f`
  `BIND v` receipt quorum, a `C`-side lock by an `n − f` `BIND ⊥` quorum. Two
  opposing quorums intersect in an honest process that would have multicast
  two different `BIND` payloads, contradicting `bind_once`; that is exactly
  the A/C exclusivity the specification's grade lock demands
  (`grade_ne_false_of_bind_quorum`, `grade_ne_true_of_bot_quorum`).

The specification binds by an internal τ-transition, so an implementation
return that meets a still-unbound specification state is answered by the
two-step weak burst `bindSet ; retA` (resp. `bindSet ; retB`) —
`weakLStep_tauThen`, `firstRetA_burst`, `firstRetB_burst`. Both `bindSet`
guards come from the single `ECHO` certificate (`bindSet_guards`): refine it
to an `n − f` `INPUT v` receipt quorum (`inputQuorum_of_echoQuorum`), whose
honest senders hold an input (`input_called`, D8) — that is the quorum guard
(`quorum_of_msg_quorum`) — and whose count also feeds
`Inv.supp_of_input_receipts` for the `f + 1` SuppOK count (D15). Each
return's own evidence harvests the certificate:
`echoQuorum_of_bind_quorum` for case (a), `echoQuorum_of_vote_receipts` for
case (b).

The invariant carries

* the corruption budget (`F_card`) and delivery soundness (`recv_sub`);
* protocol conformance of honest multicasts (`echo_conf`, `vote_input`,
  `vote_conf`, `bind_conf`): each honest `ECHO`/`VOTE`/`BIND` is
  backed by the receipt quorum that Algorithm 2 demands (receipts only grow,
  so the historical evidence persists in the current state);
* write-once recording of honest multicasts (`echo_once`, `bind_once`): an
  honest `ECHO`/`BIND` payload is the one held in the sender's `sentEcho` /
  `sentBind` field, so an honest process speaks at most one payload per
  layer;
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

The `retB`/`retC` dissent guards come from the `|Valid| > 1` evidence: the
`n − f` `INPUT` receipt quorum for each bit sits at the returner itself, and
`n − f ≥ f + 1`, so `suppI_of_valid` closes both bits at once — which is what
the `C`-return's two per-bit guards need. `InstRel.spec_supp` transports the
counts to the specification side along `call_eq`/`F_eq`.
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
  field; in particular an honest process echoes at most one payload. -/
  echo_once : ∀ j b, j ∉ s.F → Msg.echo b ∈ s.sent j →
    (s.proc j).sentEcho = some b
  /-- Honest voters hold an input (D8). -/
  vote_input : ∀ j w, j ∉ s.F → Msg.vote w ∈ s.sent j → (s.proc j).input ≠ none
  /-- Honest `VOTE b` is backed by an `n − f` `ECHO b` receipt quorum. -/
  vote_conf : ∀ j b, j ∉ s.F → Msg.vote (some b) ∈ s.sent j →
    P.n - P.f ≤ s.recvCount j (.echo b)
  /-- Honest `BIND` multicasts are recorded in the write-once `sentBind`
  flag; in particular an honest process multicasts at most one payload. -/
  bind_once : ∀ j w, j ∉ s.F → Msg.bind w ∈ s.sent j →
    (s.proc j).sentBind = some w
  /-- Honest `BIND b` is backed by an `n − f` `VOTE b` receipt quorum. -/
  bind_conf : ∀ j b, j ∉ s.F → Msg.bind (some b) ∈ s.sent j →
    P.n - P.f ≤ s.recvCount j (.vote (some b))
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
  bind_once := fun j w _ h => absurd h (by simp [ImplState.initial])
  bind_conf := fun j b _ h => absurd h (by simp [ImplState.initial])
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

/-- `input_supp` is preserved by an honest non-`INPUT` send that keeps the
sender's input. -/
private theorem input_supp_send {s : ImplState P.n} (hI : Inv P s) {j : Fin P.n}
    {p : ProcState} {m : Msg} (hp : p.input = (s.proc j).input)
    (hm : ∀ b, m ≠ .input b) (b : Bool) (j' : Fin P.n)
    (hF : j' ∉ ((s.setProc j p).mcast j m).F)
    (hm' : Msg.input b ∈ ((s.setProc j p).mcast j m).sent j') :
    (((s.setProc j p).mcast j m).proc j').input = some b ∨
      ImplSupp P ((s.setProc j p).mcast j m) b := by
  rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
  · exact absurd heq.symm (hm b)
  · rcases hI.input_supp b j' hF hold with hin | hsupp
    · left
      by_cases hk : j' = j
      · subst hk
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self, hp]
        exact hin
      · rw [proc_send_ne hk]
        exact hin
    · right
      refine ImplSupp.mono (s := s) (fun k hk => ?_) (fun _ hh => hh) hsupp
      by_cases hk0 : k = j
      · subst hk0
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self, hp]
        exact hk
      · rw [proc_send_ne hk0]
        exact hk

/-- `input_supp` is preserved by a local update that keeps the process's
input (the return steps). -/
private theorem input_supp_setProc {s : ImplState P.n} (hI : Inv P s)
    {j : Fin P.n} {p : ProcState} (hp : p.input = (s.proc j).input)
    (b : Bool) (j' : Fin P.n) (hF : j' ∉ (s.setProc j p).F)
    (hm' : Msg.input b ∈ (s.setProc j p).sent j') :
    ((s.setProc j p).proc j').input = some b ∨ ImplSupp P (s.setProc j p) b := by
  rcases hI.input_supp b j' hF hm' with hin | hsupp
  · left
    by_cases hk : j' = j
    · subst hk
      rw [ImplState.setProc_proc_self, hp]
      exact hin
    · rw [ImplState.setProc_proc_ne _ _ _ hk]
      exact hin
  · right
    refine ImplSupp.mono (s := s) (fun k hk => ?_) (fun _ hh => hh) hsupp
    by_cases hk0 : k = j
    · subst hk0
      rw [ImplState.setProc_proc_self, hp]
      exact hk
    · rw [ImplState.setProc_proc_ne _ _ _ hk0]
      exact hk

/-- **Invariant preservation.** `Inv` is preserved by every implementation
step. -/
theorem Inv.step {r : ℕ} {s : ImplState P.n} {l : Lab P.n}
    {μ : PMF (ImplState P.n)} {s' : ImplState P.n} (hI : Inv P s)
    (hstep : ImplStep P r s l μ) (hs' : s' ∈ μ.support) : Inv P s' := by
  cases hstep with
  | call id b h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.echo_conf j' b' hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = id
        · subst hk; simpa using hI.echo_once j' b' hF hold
        · rw [proc_send_ne hk]
          exact hI.echo_once j' b' hF hold
    · intro j' w hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = id
        · subst hk; simp
        · rw [proc_send_ne hk]
          exact hI.vote_input j' w hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.vote_conf j' b' hF hold
    · intro j' w hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = id
        · subst hk; simpa using hI.bind_once j' w hF hold
        · rw [proc_send_ne hk]
          exact hI.bind_once j' w hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.bind_conf j' b' hF hold
    · intro b' G hFG hGc j' hjG hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · injection heq with heq
        subst heq
        exact ⟨j', hjG, by simp⟩
      · obtain ⟨m0, hmG, hmi⟩ := hI.input_orig b' G hFG hGc j' hjG hold
        refine ⟨m0, hmG, ?_⟩
        have hne : m0 ≠ id := by
          rintro rfl
          rw [h] at hmi
          exact absurd hmi (by simp)
        rw [proc_send_ne hne]
        exact hmi
    · intro b' j' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · injection heq with heq
        subst heq
        left
        simp
      · rcases hI.input_supp b' j' hF hold with hin | hsupp
        · left
          have hne : j' ≠ id := by
            rintro rfl
            rw [h] at hin
            exact absurd hin (by simp)
          rw [proc_send_ne hne]
          exact hin
        · right
          refine ImplSupp.mono (s := s) (fun k hk => ?_) (fun _ hh => hh) hsupp
          have hne : k ≠ id := by
            rintro rfl
            rw [h] at hk
            exact absurd hk (by simp)
          rw [proc_send_ne hne]
          exact hk
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp
      · by_cases hk : j' = id
        · subst hk; simp
        · rw [proc_send_ne hk]
          exact hI.input_called j' b' hF hold
  | callLoop id b =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hI
  | deliver i j m hsent =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, hI.echo_once, hI.vote_input, ?_, hI.bind_once, ?_,
      hI.input_orig, hI.input_supp, hI.input_called⟩
    · intro i' j' m' hm'
      rcases ImplState.mem_recvMsg_recv.mp hm' with ⟨rfl, rfl, rfl⟩ | hold
      · exact hsent
      · exact hI.recv_sub i' j' m' hold
    · intro j' b' hF hm'
      exact le_trans (hI.echo_conf j' b' hF hm')
        (ImplState.recvCount_le_recvMsg s i j m j' _)
    · intro j' b' hF hm'
      exact le_trans (hI.vote_conf j' b' hF hm')
        (ImplState.recvCount_le_recvMsg s i j m j' _)
    · intro j' b' hF hm'
      exact le_trans (hI.bind_conf j' b' hF hm')
        (ImplState.recvCount_le_recvMsg s i j m j' _)
  | relay j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.echo_conf j' b' hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.echo_once j' b' hF hold
        · rw [proc_send_ne hk]
          exact hI.echo_once j' b' hF hold
    · intro j' w hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.vote_input j' w hF hold
        · rw [proc_send_ne hk]
          exact hI.vote_input j' w hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.vote_conf j' b' hF hold
    · intro j' w hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.bind_once j' w hF hold
        · rw [proc_send_ne hk]
          exact hI.bind_once j' w hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.bind_conf j' b' hF hold
    · intro b' G hFG hGc j' hjG hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · injection heq with heq
        subst heq
        have hcnt' : G.card < s.recvCount j' (Msg.input b') := by omega
        obtain ⟨k, hkG, hkr⟩ := ImplState.exists_sender_notMem G hcnt'
        obtain ⟨m0, hmG, hmi⟩ :=
          hI.input_orig b' G hFG hGc k hkG (hI.recv_sub j' k _ hkr)
        refine ⟨m0, hmG, ?_⟩
        by_cases hm0 : m0 = j'
        · subst hm0; simpa using hmi
        · rw [proc_send_ne hm0]; exact hmi
      · obtain ⟨m0, hmG, hmi⟩ := hI.input_orig b' G hFG hGc j' hjG hold
        refine ⟨m0, hmG, ?_⟩
        by_cases hm0 : m0 = j
        · subst hm0; simpa using hmi
        · rw [proc_send_ne hm0]; exact hmi
    · intro b' j' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · injection heq with heq
        subst heq
        right
        refine ImplSupp.mono (s := s) (fun k hk => ?_) (fun _ hh => hh)
          (hI.supp_of_input_receipts hcnt)
        by_cases hk0 : k = j'
        · subst hk0; simpa using hk
        · rw [proc_send_ne hk0]; exact hk
      · rcases hI.input_supp b' j' hF hold with hji | hsupp
        · left
          by_cases hk : j' = j
          · subst hk; simpa using hji
          · rw [proc_send_ne hk]; exact hji
        · right
          refine ImplSupp.mono (s := s) (fun k hk => ?_) (fun _ hh => hh) hsupp
          by_cases hk0 : k = j
          · subst hk0; simpa using hk
          · rw [proc_send_ne hk0]; exact hk
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simpa using hin
      · by_cases hk : j' = j
        · subst hk; simpa using hI.input_called j' b' hF hold
        · rw [proc_send_ne hk]
          exact hI.input_called j' b' hF hold
  | echo j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · injection heq with heq
        subst heq
        exact hcnt
      · exact hI.echo_conf j' b' hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · injection heq with heq
        subst heq
        simp
      · by_cases hk : j' = j
        · subst hk
          have hcontra := hI.echo_once j' b' hF hold
          rw [hsend] at hcontra
          exact absurd hcontra (by simp)
        · rw [proc_send_ne hk]
          exact hI.echo_once j' b' hF hold
    · intro j' w hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.vote_input j' w hF hold
        · rw [proc_send_ne hk]
          exact hI.vote_input j' w hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.vote_conf j' b' hF hold
    · intro j' w hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.bind_once j' w hF hold
        · rw [proc_send_ne hk]
          exact hI.bind_once j' w hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.bind_conf j' b' hF hold
    · intro b' G hFG hGc j' hjG hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · obtain ⟨m0, hmG, hmi⟩ := hI.input_orig b' G hFG hGc j' hjG hold
        refine ⟨m0, hmG, ?_⟩
        by_cases hm0 : m0 = j
        · subst hm0; simpa using hmi
        · rw [proc_send_ne hm0]; exact hmi
    · exact input_supp_send hI rfl (by simp)
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.input_called j' b' hF hold
        · rw [proc_send_ne hk]
          exact hI.input_called j' b' hF hold
  | voteBit j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.echo_conf j' b' hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.echo_once j' b' hF hold
        · rw [proc_send_ne hk]
          exact hI.echo_once j' b' hF hold
    · intro j' w hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simpa using hin
      · by_cases hk : j' = j
        · subst hk; simpa using hI.vote_input j' w hF hold
        · rw [proc_send_ne hk]
          exact hI.vote_input j' w hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · injection heq with heq
        injection heq with heq
        subst heq
        exact hcnt
      · exact hI.vote_conf j' b' hF hold
    · intro j' w hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.bind_once j' w hF hold
        · rw [proc_send_ne hk]
          exact hI.bind_once j' w hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.bind_conf j' b' hF hold
    · intro b' G hFG hGc j' hjG hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · obtain ⟨m0, hmG, hmi⟩ := hI.input_orig b' G hFG hGc j' hjG hold
        refine ⟨m0, hmG, ?_⟩
        by_cases hm0 : m0 = j
        · subst hm0; simpa using hmi
        · rw [proc_send_ne hm0]; exact hmi
    · exact input_supp_send hI rfl (by simp)
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.input_called j' b' hF hold
        · rw [proc_send_ne hk]
          exact hI.input_called j' b' hF hold
  | voteBot j hin hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.echo_conf j' b' hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.echo_once j' b' hF hold
        · rw [proc_send_ne hk]
          exact hI.echo_once j' b' hF hold
    · intro j' w hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simpa using hin
      · by_cases hk : j' = j
        · subst hk; simpa using hI.vote_input j' w hF hold
        · rw [proc_send_ne hk]
          exact hI.vote_input j' w hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.vote_conf j' b' hF hold
    · intro j' w hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.bind_once j' w hF hold
        · rw [proc_send_ne hk]
          exact hI.bind_once j' w hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.bind_conf j' b' hF hold
    · intro b' G hFG hGc j' hjG hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · obtain ⟨m0, hmG, hmi⟩ := hI.input_orig b' G hFG hGc j' hjG hold
        refine ⟨m0, hmG, ?_⟩
        by_cases hm0 : m0 = j
        · subst hm0; simpa using hmi
        · rw [proc_send_ne hm0]; exact hmi
    · exact input_supp_send hI rfl (by simp)
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.input_called j' b' hF hold
        · rw [proc_send_ne hk]
          exact hI.input_called j' b' hF hold
  | bindBit j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.echo_conf j' b' hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.echo_once j' b' hF hold
        · rw [proc_send_ne hk]
          exact hI.echo_once j' b' hF hold
    · intro j' w hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.vote_input j' w hF hold
        · rw [proc_send_ne hk]
          exact hI.vote_input j' w hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.vote_conf j' b' hF hold
    · intro j' w hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · injection heq with heq
        subst heq
        simp
      · by_cases hk : j' = j
        · subst hk
          have hcontra := hI.bind_once j' w hF hold
          rw [hsend] at hcontra
          exact absurd hcontra (by simp)
        · rw [proc_send_ne hk]
          exact hI.bind_once j' w hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · injection heq with heq
        injection heq with heq
        subst heq
        exact hcnt
      · exact hI.bind_conf j' b' hF hold
    · intro b' G hFG hGc j' hjG hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · obtain ⟨m0, hmG, hmi⟩ := hI.input_orig b' G hFG hGc j' hjG hold
        refine ⟨m0, hmG, ?_⟩
        by_cases hm0 : m0 = j
        · subst hm0; simpa using hmi
        · rw [proc_send_ne hm0]; exact hmi
    · exact input_supp_send hI rfl (by simp)
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.input_called j' b' hF hold
        · rw [proc_send_ne hk]
          exact hI.input_called j' b' hF hold
  | bindBot j hin hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.echo_conf j' b' hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.echo_once j' b' hF hold
        · rw [proc_send_ne hk]
          exact hI.echo_once j' b' hF hold
    · intro j' w hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.vote_input j' w hF hold
        · rw [proc_send_ne hk]
          exact hI.vote_input j' w hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.vote_conf j' b' hF hold
    · intro j' w hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · injection heq with heq
        subst heq
        simp
      · by_cases hk : j' = j
        · subst hk
          have hcontra := hI.bind_once j' w hF hold
          rw [hsend] at hcontra
          exact absurd hcontra (by simp)
        · rw [proc_send_ne hk]
          exact hI.bind_once j' w hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.bind_conf j' b' hF hold
    · intro b' G hFG hGc j' hjG hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · obtain ⟨m0, hmG, hmi⟩ := hI.input_orig b' G hFG hGc j' hjG hold
        refine ⟨m0, hmG, ?_⟩
        by_cases hm0 : m0 = j
        · subst hm0; simpa using hmi
        · rw [proc_send_ne hm0]; exact hmi
    · exact input_supp_send hI rfl (by simp)
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · by_cases hk : j' = j
        · subst hk; simpa using hI.input_called j' b' hF hold
        · rw [proc_send_ne hk]
          exact hI.input_called j' b' hF hold
  | byz j m hjF =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · exact absurd hjF hF
      · exact hI.echo_conf j' b' hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · exact absurd hjF hF
      · exact hI.echo_once j' b' hF hold
    · intro j' w hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · exact absurd hjF hF
      · exact hI.vote_input j' w hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · exact absurd hjF hF
      · exact hI.vote_conf j' b' hF hold
    · intro j' w hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · exact absurd hjF hF
      · exact hI.bind_once j' w hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · exact absurd hjF hF
      · exact hI.bind_conf j' b' hF hold
    · intro b' G hFG hGc j' hjG hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · exact absurd (hFG hjF) hjG
      · exact hI.input_orig b' G hFG hGc j' hjG hold
    · intro b' j' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · exact absurd hjF hF
      · exact hI.input_supp b' j' hF hold
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · exact absurd hjF hF
      · exact hI.input_called j' b' hF hold
  | retA id v hcnt hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, hI.recv_sub, hI.echo_conf, ?_, ?_, hI.vote_conf, ?_,
      hI.bind_conf, ?_, ?_, ?_⟩
    · intro j' b' hF hm'
      by_cases hk : j' = id
      · subst hk; simpa using hI.echo_once j' b' hF hm'
      · rw [ImplState.setProc_proc_ne _ _ _ hk]
        exact hI.echo_once j' b' hF hm'
    · intro j' w hF hm'
      by_cases hk : j' = id
      · subst hk; simpa using hI.vote_input j' w hF hm'
      · rw [ImplState.setProc_proc_ne _ _ _ hk]
        exact hI.vote_input j' w hF hm'
    · intro j' w hF hm'
      by_cases hk : j' = id
      · subst hk; simpa using hI.bind_once j' w hF hm'
      · rw [ImplState.setProc_proc_ne _ _ _ hk]
        exact hI.bind_once j' w hF hm'
    · intro b' G hFG hGc j' hjG hm'
      obtain ⟨m0, hmG, hmi⟩ := hI.input_orig b' G hFG hGc j' hjG hm'
      refine ⟨m0, hmG, ?_⟩
      by_cases hm0 : m0 = id
      · subst hm0; simpa using hmi
      · rw [ImplState.setProc_proc_ne _ _ _ hm0]; exact hmi
    · exact input_supp_setProc hI rfl
    · intro j' b' hF hm'
      by_cases hk : j' = id
      · subst hk; simpa using hI.input_called j' b' hF hm'
      · rw [ImplState.setProc_proc_ne _ _ _ hk]
        exact hI.input_called j' b' hF hm'
  | retB id v hcnt honce hvote hval hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, hI.recv_sub, hI.echo_conf, ?_, ?_, hI.vote_conf, ?_,
      hI.bind_conf, ?_, ?_, ?_⟩
    · intro j' b' hF hm'
      by_cases hk : j' = id
      · subst hk; simpa using hI.echo_once j' b' hF hm'
      · rw [ImplState.setProc_proc_ne _ _ _ hk]
        exact hI.echo_once j' b' hF hm'
    · intro j' w hF hm'
      by_cases hk : j' = id
      · subst hk; simpa using hI.vote_input j' w hF hm'
      · rw [ImplState.setProc_proc_ne _ _ _ hk]
        exact hI.vote_input j' w hF hm'
    · intro j' w hF hm'
      by_cases hk : j' = id
      · subst hk; simpa using hI.bind_once j' w hF hm'
      · rw [ImplState.setProc_proc_ne _ _ _ hk]
        exact hI.bind_once j' w hF hm'
    · intro b' G hFG hGc j' hjG hm'
      obtain ⟨m0, hmG, hmi⟩ := hI.input_orig b' G hFG hGc j' hjG hm'
      refine ⟨m0, hmG, ?_⟩
      by_cases hm0 : m0 = id
      · subst hm0; simpa using hmi
      · rw [ImplState.setProc_proc_ne _ _ _ hm0]; exact hmi
    · exact input_supp_setProc hI rfl
    · intro j' b' hF hm'
      by_cases hk : j' = id
      · subst hk; simpa using hI.input_called j' b' hF hm'
      · rw [ImplState.setProc_proc_ne _ _ _ hk]
        exact hI.input_called j' b' hF hm'
  | retC id hcnt hval hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, hI.recv_sub, hI.echo_conf, ?_, ?_, hI.vote_conf, ?_,
      hI.bind_conf, ?_, ?_, ?_⟩
    · intro j' b' hF hm'
      by_cases hk : j' = id
      · subst hk; simpa using hI.echo_once j' b' hF hm'
      · rw [ImplState.setProc_proc_ne _ _ _ hk]
        exact hI.echo_once j' b' hF hm'
    · intro j' w hF hm'
      by_cases hk : j' = id
      · subst hk; simpa using hI.vote_input j' w hF hm'
      · rw [ImplState.setProc_proc_ne _ _ _ hk]
        exact hI.vote_input j' w hF hm'
    · intro j' w hF hm'
      by_cases hk : j' = id
      · subst hk; simpa using hI.bind_once j' w hF hm'
      · rw [ImplState.setProc_proc_ne _ _ _ hk]
        exact hI.bind_once j' w hF hm'
    · intro b' G hFG hGc j' hjG hm'
      obtain ⟨m0, hmG, hmi⟩ := hI.input_orig b' G hFG hGc j' hjG hm'
      refine ⟨m0, hmG, ?_⟩
      by_cases hm0 : m0 = id
      · subst hm0; simpa using hmi
      · rw [ImplState.setProc_proc_ne _ _ _ hm0]; exact hmi
    · exact input_supp_setProc hI rfl
    · intro j' b' hF hm'
      by_cases hk : j' = id
      · subst hk; simpa using hI.input_called j' b' hF hm'
      · rw [ImplState.setProc_proc_ne _ _ _ hk]
        exact hI.input_called j' b' hF hm'
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hsub := ImplState.corrupt_F_subset s id
    refine ⟨ImplState.corrupt_card_le s id hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      rw [ImplState.corrupt_recv] at hm'
      rw [ImplState.corrupt_sent]
      exact hI.recv_sub i' j' m' hm'
    · intro j' b' hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_recvCount]
      exact hI.echo_conf j' b' (fun hj => hF (hsub hj)) hm'
    · intro j' b' hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.echo_once j' b' (fun hj => hF (hsub hj)) hm'
    · intro j' w hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.vote_input j' w (fun hj => hF (hsub hj)) hm'
    · intro j' b' hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_recvCount]
      exact hI.vote_conf j' b' (fun hj => hF (hsub hj)) hm'
    · intro j' w hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.bind_once j' w (fun hj => hF (hsub hj)) hm'
    · intro j' b' hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_recvCount]
      exact hI.bind_conf j' b' (fun hj => hF (hsub hj)) hm'
    · intro b' G hFG hGc j' hjG hm'
      rw [ImplState.corrupt_sent] at hm'
      obtain ⟨m0, hmG, hmi⟩ :=
        hI.input_orig b' G (Finset.Subset.trans hsub hFG) hGc j' hjG hm'
      exact ⟨m0, hmG, by rw [ImplState.corrupt_proc]; exact hmi⟩
    · intro b' j' hF' hm'
      rw [ImplState.corrupt_sent] at hm'
      rcases hI.input_supp b' j' (fun hj => hF' (hsub hj)) hm' with hin | hsupp
      · left
        rw [ImplState.corrupt_proc]
        exact hin
      · right
        refine ImplSupp.mono (s := s) (fun k hk => ?_) hsub hsupp
        rw [ImplState.corrupt_proc]
        exact hk
    · intro j' b' hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.input_called j' b' (fun hj => hF (hsub hj)) hm'

/-! ### The phase-2 certificate -/

/-- The certificate that stands in for the specification's `bind` field:
somebody holds an `n − f` `ECHO v` receipt quorum. It is `F`-blind and
receipt-monotone, hence stable under `fail` and under every implementation
step. -/
def EchoQuorum (P : Params) (s : ImplState P.n) (v : Bool) : Prop :=
  ∃ i, P.n - P.f ≤ s.recvCount i (.echo v)

/-- Harvest from `retB` evidence: `f + 1` `VOTE v` receipts. -/
theorem echoQuorum_of_vote_receipts {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.f + 1 ≤ s.recvCount i (.vote (some v))) :
    EchoQuorum P s v := by
  have hFc := hI.F_card
  have h' : s.F.card < s.recvCount i (Msg.vote (some v)) := by omega
  obtain ⟨k, hkF, hkr⟩ := ImplState.exists_sender_notMem s.F h'
  exact ⟨k, hI.vote_conf k v hkF (hI.recv_sub i k _ hkr)⟩

/-- Harvest from `retA` evidence: an `n − f` `BIND v` receipt quorum. -/
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

/-- **Value agreement.** At most one bit carries an `n − f` `ECHO` quorum:
the two quorums intersect in an honest sender, and `sentEcho` is
write-once. -/
theorem echoQuorum_unique {s : ImplState P.n} (hI : Inv P s) {v v' : Bool}
    (h : EchoQuorum P s v) (h' : EchoQuorum P s v') : v = v' := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨i', hi'⟩ := h'
  obtain ⟨j, hjF, hj1, hj2⟩ := ImplState.exists_honest_recv₂ hI.F_card hi hi'
  have e1 := hI.echo_once j v hjF (hI.recv_sub i j _ hj1)
  have e2 := hI.echo_once j v' hjF (hI.recv_sub i' j _ hj2)
  rw [e1] at e2
  exact Option.some.inj e2

/-! ### The simulation relation -/

/-- The simulation relation: the concrete invariant, the abstraction map for
the fields the protocol itself holds (spec `call` = concrete input, spec
`ret` = concrete return flags, spec `F` = concrete `F`), and receipt evidence
for the two fields it does not. -/
structure InstRel (P : Params) (s : ImplState P.n) (t : SpecState P.n) : Prop where
  /-- The concrete inductive invariant. -/
  inv : Inv P s
  /-- Spec inputs are the concrete inputs. -/
  call_eq : ∀ id, t.call id = (s.proc id).input
  /-- Spec return flags are the concrete return flags. -/
  ret_eq : ∀ id, t.ret id = (s.proc id).returned
  /-- The corrupted sets agree. -/
  F_eq : t.F = s.F
  /-- A bound specification state is certified by an `n − f` `ECHO` quorum
  for the bound bit. -/
  bind_cert : ∀ v, t.bind = some v → EchoQuorum P s v
  /-- An `A`-side grade lock is backed by an `n − f` `BIND v` receipt quorum
  for some bit `v`. -/
  gradeA_ev : t.grade = some true →
    ∃ v i, P.n - P.f ≤ s.recvCount i (.bind (some v))
  /-- A `C`-side grade lock is backed by an `n − f` `BIND ⊥` receipt
  quorum. -/
  gradeC_ev : t.grade = some false →
    ∃ i, P.n - P.f ≤ s.recvCount i (.bind none)

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
  bind_cert := fun v h => absurd h (by simp [SpecState.initial])
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

/-- **Both `bindSet` guards from the single certificate.** -/
theorem bindSet_guards {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {v : Bool} (hq : EchoQuorum P s v) :
    t.quorum P ∧ P.f + 1 ≤ (Finset.univ.filter
      (fun id => t.call id = some v ∨ id ∈ t.F)).card := by
  obtain ⟨m, hm⟩ := inputQuorum_of_echoQuorum hR.inv hq
  have hfn := P.f_lt_n_sub_f
  refine ⟨quorum_of_msg_quorum hR
    (fun j hj hm' => hR.inv.input_called j v hj hm') hm, ?_⟩
  exact hR.spec_supp (hR.inv.supp_of_input_receipts (le_trans (by omega) hm))

/-- A/C-exclusivity, `A`-side: an `n − f` `BIND v` receipt quorum rules out
a `C`-side grade lock (the two `BIND` quorums would intersect in an honest
process with two different `BIND` payloads). -/
theorem grade_ne_false_of_bind_quorum {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {id : Fin P.n} {v : Bool}
    (hcnt : P.n - P.f ≤ s.recvCount id (.bind (some v))) :
    t.grade ≠ some false := by
  intro hg
  obtain ⟨i', hc⟩ := hR.gradeC_ev hg
  obtain ⟨j, hjF, hj1, hj2⟩ := ImplState.exists_honest_recv₂ hR.inv.F_card hcnt hc
  have e1 := hR.inv.bind_once j (some v) hjF (hR.inv.recv_sub id j _ hj1)
  have e2 := hR.inv.bind_once j none hjF (hR.inv.recv_sub i' j _ hj2)
  rw [e1] at e2
  exact absurd (Option.some.inj e2) (by simp)

/-- A/C-exclusivity, `C`-side: an `n − f` `BIND ⊥` receipt quorum rules out
an `A`-side grade lock. -/
theorem grade_ne_true_of_bot_quorum {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {id : Fin P.n}
    (hcnt : P.n - P.f ≤ s.recvCount id (.bind none)) :
    t.grade ≠ some true := by
  intro hg
  obtain ⟨v', i', hc⟩ := hR.gradeA_ev hg
  obtain ⟨j, hjF, hj1, hj2⟩ := ImplState.exists_honest_recv₂ hR.inv.F_card hc hcnt
  have e1 := hR.inv.bind_once j (some v') hjF (hR.inv.recv_sub i' j _ hj1)
  have e2 := hR.inv.bind_once j none hjF (hR.inv.recv_sub id j _ hj2)
  rw [e1] at e2
  exact absurd (Option.some.inj e2) (by simp)

/-! ### Value agreement against an already bound specification state -/

/-- Case (a): the `A`-return's `BIND v` quorum names the bound bit. -/
theorem retA_value_agrees {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {id : Fin P.n} {v v₀ : Bool} (hb : t.bind = some v₀)
    (hcnt : P.n - P.f ≤ s.recvCount id (.bind (some v))) : t.bind = some v := by
  have h1 := hR.bind_cert v₀ hb
  have h2 := echoQuorum_of_bind_quorum hR.inv hcnt
  rw [echoQuorum_unique hR.inv h1 h2] at hb
  exact hb

/-- Case (b): the `B`-return's `f + 1` `VOTE v` receipts name the bound
bit. -/
theorem retB_value_agrees {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {id : Fin P.n} {v v₀ : Bool} (hb : t.bind = some v₀)
    (hvote : P.f + 1 ≤ s.recvCount id (.vote (some v))) : t.bind = some v := by
  have h1 := hR.bind_cert v₀ hb
  have h2 := echoQuorum_of_vote_receipts hR.inv hvote
  rw [echoQuorum_unique hR.inv h1 h2] at hb
  exact hb

/-! ### Answering a first return by a two-step burst -/

/-- Phase-1 `A`-return: an unbound specification state answers with
`bindSet` followed by `retA`. -/
theorem firstRetA_burst {r : ℕ} {t : SpecState P.n} {id : Fin P.n} {v : Bool}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some v ∨ k ∈ t.F)).card)
    (hb : t.bind = none)
    (hg : t.grade = none ∨ t.grade = some true)
    (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id (.A v))
      { t with bind := some v, grade := some true,
               ret := Function.update t.ret id true } := by
  have h1 : (specInst P r).LStep t Silent.τ { t with bind := some v } :=
    Step.bindSet t v hq hw hb
  have h2 : (specInst P r).LStep { t with bind := some v } (.retG r id (.A v))
      { t with bind := some v, grade := some true,
               ret := Function.update t.ret id true } :=
    Step.retA { t with bind := some v } id v rfl hg hr
  exact weakLStep_tauThen h1 h2 (by simp)

/-- Phase-1 `B`-return: the same burst, with the `retB` dissent guard. -/
theorem firstRetB_burst {r : ℕ} {t : SpecState P.n} {id : Fin P.n} {v : Bool}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some v ∨ k ∈ t.F)).card)
    (hb : t.bind = none)
    (hd : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some (!v) ∨ k ∈ t.F)).card)
    (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id (.B v))
      { t with bind := some v, ret := Function.update t.ret id true } := by
  have h1 : (specInst P r).LStep t Silent.τ { t with bind := some v } :=
    Step.bindSet t v hq hw hb
  have h2 : (specInst P r).LStep { t with bind := some v } (.retG r id (.B v))
      { t with bind := some v, ret := Function.update t.ret id true } :=
    Step.retB { t with bind := some v } id v rfl hd hr
  exact weakLStep_tauThen h1 h2 (by simp)

/-! ### The refinement -/

private theorem spec_corrupt_call (t : SpecState P.n) (id : Fin P.n) :
    (t.corrupt P id).call = t.call := by
  unfold SpecState.corrupt; split <;> rfl

private theorem spec_corrupt_ret (t : SpecState P.n) (id : Fin P.n) :
    (t.corrupt P id).ret = t.ret := by
  unfold SpecState.corrupt; split <;> rfl

private theorem spec_corrupt_bind (t : SpecState P.n) (id : Fin P.n) :
    (t.corrupt P id).bind = t.bind := by
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
instance forward-simulates the round-`r` specification instance along
`instRel`. -/
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
      hI', ?_, ?_, hRR.F_eq, hRR.bind_cert, hRR.gradeA_ev, hRR.gradeC_ev⟩
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
    · intro v hv
      obtain ⟨i0, hi0⟩ := hRR.bind_cert v hv
      exact ⟨i0, le_trans hi0 (ImplState.recvCount_le_recvMsg q1 i j m i0 _)⟩
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
      hI', ?_, ?_, hRR.F_eq, hRR.bind_cert, hRR.gradeA_ev, hRR.gradeC_ev⟩
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
      hI', ?_, ?_, hRR.F_eq, hRR.bind_cert, hRR.gradeA_ev, hRR.gradeC_ev⟩
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
      hI', ?_, ?_, hRR.F_eq, hRR.bind_cert, hRR.gradeA_ev, hRR.gradeC_ev⟩
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
      hI', ?_, ?_, hRR.F_eq, hRR.bind_cert, hRR.gradeA_ev, hRR.gradeC_ev⟩
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
      hI', ?_, ?_, hRR.F_eq, hRR.bind_cert, hRR.gradeA_ev, hRR.gradeC_ev⟩
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
      hI', ?_, ?_, hRR.F_eq, hRR.bind_cert, hRR.gradeA_ev, hRR.gradeC_ev⟩
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
      hI', hRR.call_eq, hRR.ret_eq, hRR.F_eq, hRR.bind_cert, hRR.gradeA_ev,
      hRR.gradeC_ev⟩
  | retA id v hcnt hr =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hret : q2.ret id = false := by rw [hRR.ret_eq]; exact hr
    have hgr : q2.grade = none ∨ q2.grade = some true := by
      have hne := grade_ne_false_of_bind_quorum hRR hcnt
      cases hg : q2.grade with
      | none => exact Or.inl rfl
      | some gb =>
        cases gb
        · exact absurd hg hne
        · exact Or.inr rfl
    cases hb : q2.bind with
    | none =>
      obtain ⟨hq, hw⟩ := bindSet_guards hRR (echoQuorum_of_bind_quorum hRR.inv hcnt)
      refine ⟨{ q2 with bind := some v, grade := some true,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, firstRetA_burst hq hw hb hgr hret⟩,
        hI', ?_, ?_, hRR.F_eq, ?_, ?_, ?_⟩
      · intro k
        by_cases hk : k = id
        · subst hk
          simpa using hRR.call_eq k
        · rw [ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.call_eq k
      · intro k
        change Function.update q2.ret id true k = _
        by_cases hk : k = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.ret_eq k
      · intro v' hv'
        obtain rfl : v = v' := Option.some.inj hv'
        exact echoQuorum_of_bind_quorum hRR.inv hcnt
      · exact fun _ => ⟨v, id, hcnt⟩
      · exact fun hgf => absurd hgf (by simp)
    | some v₀ =>
      have hbnd : q2.bind = some v := retA_value_agrees hRR hb hcnt
      refine ⟨{ q2 with grade := some true, ret := Function.update q2.ret id true },
        Or.inr ⟨by simp,
          weakLStep_single (Step.retA q2 id v hbnd hgr hret) (by simp)⟩,
        hI', ?_, ?_, hRR.F_eq, hRR.bind_cert, ?_, ?_⟩
      · intro k
        by_cases hk : k = id
        · subst hk
          simpa using hRR.call_eq k
        · rw [ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.call_eq k
      · intro k
        change Function.update q2.ret id true k = _
        by_cases hk : k = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.ret_eq k
      · exact fun _ => ⟨v, id, hcnt⟩
      · exact fun hgf => absurd hgf (by simp)
  | retB id v hcnt honce hvote hval hr =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hret : q2.ret id = false := by rw [hRR.ret_eq]; exact hr
    have hd : P.f + 1 ≤ (Finset.univ.filter
        (fun k => q2.call k = some (!v) ∨ k ∈ q2.F)).card :=
      hRR.spec_supp (suppI_of_valid hRR.inv hval (!v))
    cases hb : q2.bind with
    | none =>
      obtain ⟨hq, hw⟩ := bindSet_guards hRR (echoQuorum_of_vote_receipts hRR.inv hvote)
      refine ⟨{ q2 with bind := some v, ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, firstRetB_burst hq hw hb hd hret⟩,
        hI', ?_, ?_, hRR.F_eq, ?_, hRR.gradeA_ev, hRR.gradeC_ev⟩
      · intro k
        by_cases hk : k = id
        · subst hk
          simpa using hRR.call_eq k
        · rw [ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.call_eq k
      · intro k
        change Function.update q2.ret id true k = _
        by_cases hk : k = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.ret_eq k
      · intro v' hv'
        obtain rfl : v = v' := Option.some.inj hv'
        exact echoQuorum_of_vote_receipts hRR.inv hvote
    | some v₀ =>
      have hbnd : q2.bind = some v := retB_value_agrees hRR hb hvote
      refine ⟨{ q2 with ret := Function.update q2.ret id true },
        Or.inr ⟨by simp,
          weakLStep_single (Step.retB q2 id v hbnd hd hret) (by simp)⟩,
        hI', ?_, ?_, hRR.F_eq, hRR.bind_cert, hRR.gradeA_ev, hRR.gradeC_ev⟩
      · intro k
        by_cases hk : k = id
        · subst hk
          simpa using hRR.call_eq k
        · rw [ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.call_eq k
      · intro k
        change Function.update q2.ret id true k = _
        by_cases hk : k = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.ret_eq k
  | retC id hcnt hval hr =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hret : q2.ret id = false := by rw [hRR.ret_eq]; exact hr
    have hwT : P.f + 1 ≤ (Finset.univ.filter
        (fun k => q2.call k = some true ∨ k ∈ q2.F)).card :=
      hRR.spec_supp (suppI_of_valid hRR.inv hval true)
    have hwF : P.f + 1 ≤ (Finset.univ.filter
        (fun k => q2.call k = some false ∨ k ∈ q2.F)).card :=
      hRR.spec_supp (suppI_of_valid hRR.inv hval false)
    have hgr : q2.grade = none ∨ q2.grade = some false := by
      have hne := grade_ne_true_of_bot_quorum hRR hcnt
      cases hg : q2.grade with
      | none => exact Or.inl rfl
      | some gb =>
        cases gb
        · exact Or.inr rfl
        · exact absurd hg hne
    refine ⟨{ q2 with grade := some false, ret := Function.update q2.ret id true },
      Or.inr ⟨by simp,
        weakLStep_single (Step.retC q2 id hwT hwF hgr hret) (by simp)⟩,
      hI', ?_, ?_, hRR.F_eq, hRR.bind_cert, ?_, ?_⟩
    · intro k
      by_cases hk : k = id
      · subst hk
        simpa using hRR.call_eq k
      · rw [ImplState.setProc_proc_ne _ _ _ hk]
        exact hRR.call_eq k
    · intro k
      change Function.update q2.ret id true k = _
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        simp
      · rw [Function.update_of_ne hk, ImplState.setProc_proc_ne _ _ _ hk]
        exact hRR.ret_eq k
    · exact fun hgt => absurd hgt (by simp)
    · exact fun _ => ⟨id, hcnt⟩
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
    · intro v hv
      rw [spec_corrupt_bind] at hv
      obtain ⟨i0, hi0⟩ := hRR.bind_cert v hv
      exact ⟨i0, by rw [ImplState.corrupt_recvCount]; exact hi0⟩
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
