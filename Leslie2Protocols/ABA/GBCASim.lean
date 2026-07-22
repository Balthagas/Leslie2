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

The simulation relation `instRel` pairs the concrete inductive invariant
`GBCA.Inv` with the abstraction map: the spec's `call` is the concrete input,
`ret` the concrete return flags, `bind`/`grade` the concrete ghost fields
(D6/D7), and `F` the concrete corrupted set. The invariant carries

* the corruption budget (`F_card`) and delivery soundness (`recv_sub`);
* protocol conformance of honest multicasts (`echo_conf`, `vote_input`,
  `vote_conf`, `bind_once`, `bind_conf`): each honest `ECHO`/`VOTE`/`BIND` is
  backed by the receipt quorum that Algorithm 2 demands (receipts only grow,
  so the historical evidence persists in the current state);
* the *budget-robust* input-origin clause (`input_orig`): for **every**
  potential corruption superset `G ⊇ F` within the budget, an `INPUT b`
  multicast by a sender outside `G` traces back to a process outside `G`
  whose own input is `b`. The quantification over `G` is what makes the
  clause inductive: the classical "first honest sender of `INPUT b` is an
  originator" argument is temporal, but a relayer's `f + 1` receipt quorum
  always contains a sender outside `G`, so the pre-state clause — already
  quantified over the same `G` — supplies the witness, and corruption steps
  only shrink the range of `G`;
* the grade witnesses (`gradeA`, `gradeC`): a recorded `A`- or `C`-return is
  backed by the `n − f` `BIND` receipt quorum that fired it, which is how
  A/C-exclusivity (the spec's grade lock) is discharged: two opposing
  quorums would intersect in an honest process that multicast two different
  `BIND` payloads, contradicting `bind_once`.

The spec guards are derived as follows. `bindSet`'s quorum: the honest
`BIND b` sender's `n − f` `VOTE b` receipt quorum consists of senders that,
when honest, hold an input (`vote_input`, D8), and corrupted members are
absorbed into the `∪ F` of the spec's quorum. `bindSet`'s honest witness:
chase `BIND b → VOTE b → ECHO b → INPUT b` quorums through conformance,
extracting an honest sender at each level (`n − f > f ≥ |F|`), and finish
with `input_orig`. The honest dissent of `retB`/`retC` comes from the
`|Valid| > 1` guard: the `n − f` `INPUT (¬v)` receipt quorum contains an
honest sender, and `input_orig` produces an honest process whose input is
`¬v`.
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

end WeakHelpers

/-! ### The concrete inductive invariant -/

variable {P : Params}

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
  /-- An `A`-side grade lock is backed by an `n − f` `BIND v` receipt quorum
  for the bound value `v`. -/
  gradeA : s.grade = some true →
    ∃ v i, s.bound = some v ∧ P.n - P.f ≤ s.recvCount i (.bind (some v))
  /-- A `C`-side grade lock is backed by an `n − f` `BIND ⊥` receipt
  quorum. -/
  gradeC : s.grade = some false →
    ∃ i, P.n - P.f ≤ s.recvCount i (.bind none)

theorem Inv.initial (P : Params) : Inv P (ImplState.initial P.n) where
  F_card := by simp [ImplState.initial]
  recv_sub := fun i j m h => absurd h (by simp [ImplState.initial])
  echo_conf := fun j b _ h => absurd h (by simp [ImplState.initial])
  vote_input := fun j w _ h => absurd h (by simp [ImplState.initial])
  vote_conf := fun j b _ h => absurd h (by simp [ImplState.initial])
  bind_once := fun j w _ h => absurd h (by simp [ImplState.initial])
  bind_conf := fun j b _ h => absurd h (by simp [ImplState.initial])
  input_orig := fun b G _ _ j _ h => absurd h (by simp [ImplState.initial])
  gradeA := fun h => absurd h (by simp [ImplState.initial])
  gradeC := fun h => absurd h (by simp [ImplState.initial])

/-- The sender's `setProc` in a send step does not affect other processes. -/
private theorem proc_send_ne {s : ImplState P.n} {j : Fin P.n} {p : ProcState}
    {m : Msg} {k : Fin P.n} (hk : k ≠ j) :
    ((s.setProc j p).mcast j m).proc k = s.proc k := by
  rw [ImplState.mcast_proc, ImplState.setProc_proc_ne _ _ _ hk]

/-- The returner's `setProc` in a graded return does not affect other
processes. -/
private theorem proc_ret_ne {s : ImplState P.n} {j : Fin P.n} {p : ProcState}
    {g : Option Bool} {k : Fin P.n} (hk : k ≠ j) :
    ((s.setProc j p).setGrade g).proc k = s.proc k := by
  rw [ImplState.setGrade_proc, ImplState.setProc_proc_ne _ _ _ hk]

/-- **Invariant preservation.** `Inv` is preserved by every implementation
step. -/
theorem Inv.step {r : ℕ} {s : ImplState P.n} {l : Lab P.n}
    {μ : PMF (ImplState P.n)} {s' : ImplState P.n} (hI : Inv P s)
    (hstep : ImplStep P r s l μ) (hs' : s' ∈ μ.support) : Inv P s' := by
  cases hstep with
  | call id b h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.gradeA, hI.gradeC⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.echo_conf j' b' hF hold
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
  | callLoop id b =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hI
  | deliver i j m hsent =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, hI.vote_input, ?_, hI.bind_once, ?_,
      hI.input_orig, ?_, ?_⟩
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
    · intro hg
      obtain ⟨v, i', hbv, hcv⟩ := hI.gradeA hg
      exact ⟨v, i', hbv, le_trans hcv (ImplState.recvCount_le_recvMsg s i j m i' _)⟩
    · intro hg
      obtain ⟨i', hcv⟩ := hI.gradeC hg
      exact ⟨i', le_trans hcv (ImplState.recvCount_le_recvMsg s i j m i' _)⟩
  | relay j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.gradeA, hI.gradeC⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.echo_conf j' b' hF hold
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
  | echo j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.gradeA, hI.gradeC⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · injection heq with heq
        subst heq
        exact hcnt
      · exact hI.echo_conf j' b' hF hold
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
  | voteBit j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.gradeA, hI.gradeC⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.echo_conf j' b' hF hold
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
  | voteBot j hin hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.gradeA, hI.gradeC⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.echo_conf j' b' hF hold
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
  | bindBit j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.gradeA, hI.gradeC⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.echo_conf j' b' hF hold
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
  | bindBot j hin hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.gradeA, hI.gradeC⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · simp at heq
      · exact hI.echo_conf j' b' hF hold
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
  | byz j m hjF =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.gradeA, hI.gradeC⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · intro j' b' hF hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
      · exact absurd hjF hF
      · exact hI.echo_conf j' b' hF hold
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
  | bindGhost i b hi hm hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, hI.recv_sub, hI.echo_conf, hI.vote_input, hI.vote_conf,
      hI.bind_once, hI.bind_conf, hI.input_orig, ?_, hI.gradeC⟩
    intro hg
    obtain ⟨v, i', hbv, _⟩ := hI.gradeA hg
    rw [hb] at hbv
    exact absurd hbv (by simp)
  | retA id v hb hcnt hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, hI.recv_sub, hI.echo_conf, ?_, hI.vote_conf, ?_,
      hI.bind_conf, ?_, ?_, ?_⟩
    · intro j' w hF hm'
      by_cases hk : j' = id
      · subst hk; simpa using hI.vote_input j' w hF hm'
      · rw [proc_ret_ne hk]
        exact hI.vote_input j' w hF hm'
    · intro j' w hF hm'
      by_cases hk : j' = id
      · subst hk; simpa using hI.bind_once j' w hF hm'
      · rw [proc_ret_ne hk]
        exact hI.bind_once j' w hF hm'
    · intro b' G hFG hGc j' hjG hm'
      obtain ⟨m0, hmG, hmi⟩ := hI.input_orig b' G hFG hGc j' hjG hm'
      refine ⟨m0, hmG, ?_⟩
      by_cases hm0 : m0 = id
      · subst hm0; simpa using hmi
      · rw [proc_ret_ne hm0]; exact hmi
    · intro _
      exact ⟨v, id, hb, hcnt⟩
    · intro hg
      simp at hg
  | retB id v hb hcnt honce hvote hval hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, hI.recv_sub, hI.echo_conf, ?_, hI.vote_conf, ?_,
      hI.bind_conf, ?_, hI.gradeA, hI.gradeC⟩
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
  | retC id v hb hcnt hval hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, hI.recv_sub, hI.echo_conf, ?_, hI.vote_conf, ?_,
      hI.bind_conf, ?_, ?_, ?_⟩
    · intro j' w hF hm'
      by_cases hk : j' = id
      · subst hk; simpa using hI.vote_input j' w hF hm'
      · rw [proc_ret_ne hk]
        exact hI.vote_input j' w hF hm'
    · intro j' w hF hm'
      by_cases hk : j' = id
      · subst hk; simpa using hI.bind_once j' w hF hm'
      · rw [proc_ret_ne hk]
        exact hI.bind_once j' w hF hm'
    · intro b' G hFG hGc j' hjG hm'
      obtain ⟨m0, hmG, hmi⟩ := hI.input_orig b' G hFG hGc j' hjG hm'
      refine ⟨m0, hmG, ?_⟩
      by_cases hm0 : m0 = id
      · subst hm0; simpa using hmi
      · rw [proc_ret_ne hm0]; exact hmi
    · intro hg
      simp at hg
    · intro _
      exact ⟨id, hcnt⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hsub := ImplState.corrupt_F_subset s id
    refine ⟨ImplState.corrupt_card_le s id hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      rw [ImplState.corrupt_recv] at hm'
      rw [ImplState.corrupt_sent]
      exact hI.recv_sub i' j' m' hm'
    · intro j' b' hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_recvCount]
      exact hI.echo_conf j' b' (fun hj => hF (hsub hj)) hm'
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
    · intro hg
      rw [ImplState.corrupt_grade] at hg
      obtain ⟨v, i', h1, h2⟩ := hI.gradeA hg
      exact ⟨v, i', by rw [ImplState.corrupt_bound]; exact h1,
        by rw [ImplState.corrupt_recvCount]; exact h2⟩
    · intro hg
      rw [ImplState.corrupt_grade] at hg
      obtain ⟨i', h2⟩ := hI.gradeC hg
      exact ⟨i', by rw [ImplState.corrupt_recvCount]; exact h2⟩

/-! ### The simulation relation -/

/-- The simulation relation: the concrete invariant together with the
abstraction map (spec `call` = concrete input, spec `ret` = concrete return
flags, spec `bind`/`grade` = concrete ghosts, spec `F` = concrete `F`). -/
structure InstRel (P : Params) (s : ImplState P.n) (t : SpecState P.n) : Prop where
  /-- The concrete inductive invariant. -/
  inv : Inv P s
  /-- Spec inputs are the concrete inputs. -/
  call_eq : ∀ id, t.call id = (s.proc id).input
  /-- Spec return flags are the concrete return flags. -/
  ret_eq : ∀ id, t.ret id = (s.proc id).returned
  /-- The spec bound value is the concrete ghost `bound` (D6). -/
  bind_eq : t.bind = s.bound
  /-- The spec grade lock is the concrete ghost `grade` (D7). -/
  grade_eq : t.grade = s.grade
  /-- The corrupted sets agree. -/
  F_eq : t.F = s.F

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
  bind_eq := rfl
  grade_eq := rfl
  F_eq := rfl

/-! ### Deriving the spec guards -/

/-- An `n − f` receipt quorum of `VOTE`s (any fixed payload) at an honest
process yields the spec's call quorum: honest voters hold an input (D8),
and corrupted senders are absorbed into the `∪ F`. -/
theorem quorum_of_vote_quorum {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {i : Fin P.n} {w : Option Bool}
    (h : P.n - P.f ≤ s.recvCount i (.vote w)) : t.quorum P := by
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
    exact hR.inv.vote_input k w hkF' (hR.inv.recv_sub i k _ hk.2)

/-- From an honest `BIND b` multicast (a real bit), an honest process whose
input is `b`: chase the `VOTE`, `ECHO`, `INPUT` quorums and close with
`input_orig`. -/
theorem exists_honest_input_of_bind {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {b : Bool} (hiF : i ∉ s.F) (hm : Msg.bind (some b) ∈ s.sent i) :
    ∃ m, m ∉ s.F ∧ (s.proc m).input = some b := by
  have hfn := P.f_lt_n_sub_f
  have hFc := hI.F_card
  -- the `VOTE b` quorum at `i`
  have h1 := hI.bind_conf i b hiF hm
  have h1' : s.F.card < s.recvCount i (Msg.vote (some b)) := by omega
  obtain ⟨j, hjF, hjr⟩ := ImplState.exists_sender_notMem s.F h1'
  -- the `ECHO b` quorum at `j`
  have h2 := hI.vote_conf j b hjF (hI.recv_sub i j _ hjr)
  have h2' : s.F.card < s.recvCount j (Msg.echo b) := by omega
  obtain ⟨k, hkF, hkr⟩ := ImplState.exists_sender_notMem s.F h2'
  -- the `INPUT b` quorum at `k`
  have h3 := hI.echo_conf k b hkF (hI.recv_sub j k _ hkr)
  have h3' : s.F.card < s.recvCount k (Msg.input b) := by omega
  obtain ⟨m0, hmF, hmr⟩ := ImplState.exists_sender_notMem s.F h3'
  exact hI.input_orig b s.F (Finset.Subset.refl _) hFc m0 hmF
    (hI.recv_sub k m0 _ hmr)

/-- From `|Valid| > 1` evidence at any process, an honest process whose
input is `b` — for either bit `b`. -/
theorem exists_honest_input_of_valid {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} (hv : s.bothValid P i) (b : Bool) :
    ∃ m, m ∉ s.F ∧ (s.proc m).input = some b := by
  have hfn := P.f_lt_n_sub_f
  have hFc := hI.F_card
  have h1 := ImplState.bothValid_le hv b
  have h1' : s.F.card < s.recvCount i (Msg.input b) := by omega
  obtain ⟨j, hjF, hjr⟩ := ImplState.exists_sender_notMem s.F h1'
  exact hI.input_orig b s.F (Finset.Subset.refl _) hFc j hjF
    (hI.recv_sub i j _ hjr)

/-- A/C-exclusivity, `A`-side: an `n − f` `BIND v` receipt quorum rules out
a `C`-side grade lock (the two `BIND` quorums would intersect in an honest
process with two different `BIND` payloads). -/
theorem grade_ne_false_of_bind_quorum {s : ImplState P.n} (hI : Inv P s)
    {id : Fin P.n} {v : Bool}
    (hcnt : P.n - P.f ≤ s.recvCount id (.bind (some v))) :
    s.grade ≠ some false := by
  intro hg
  obtain ⟨i', hc⟩ := hI.gradeC hg
  obtain ⟨j, hjF, hj1, hj2⟩ := ImplState.exists_honest_recv₂ hI.F_card hcnt hc
  have e1 := hI.bind_once j (some v) hjF (hI.recv_sub id j _ hj1)
  have e2 := hI.bind_once j none hjF (hI.recv_sub i' j _ hj2)
  rw [e1] at e2
  exact absurd (Option.some.inj e2) (by simp)

/-- A/C-exclusivity, `C`-side: an `n − f` `BIND ⊥` receipt quorum rules out
an `A`-side grade lock. -/
theorem grade_ne_true_of_bot_quorum {s : ImplState P.n} (hI : Inv P s)
    {id : Fin P.n} (hcnt : P.n - P.f ≤ s.recvCount id (.bind none)) :
    s.grade ≠ some true := by
  intro hg
  obtain ⟨v', i', _, hc⟩ := hI.gradeA hg
  obtain ⟨j, hjF, hj1, hj2⟩ := ImplState.exists_honest_recv₂ hI.F_card hc hcnt
  have e1 := hI.bind_once j (some v') hjF (hI.recv_sub i' j _ hj1)
  have e2 := hI.bind_once j none hjF (hI.recv_sub id j _ hj2)
  rw [e1] at e2
  exact absurd (Option.some.inj e2) (by simp)

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
      hI', ?_, ?_, hRR.bind_eq, hRR.grade_eq, hRR.F_eq⟩
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
    exact ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', hRR.call_eq, hRR.ret_eq, hRR.bind_eq, hRR.grade_eq, hRR.F_eq⟩
  | relay j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.bind_eq, hRR.grade_eq, hRR.F_eq⟩
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
      hI', ?_, ?_, hRR.bind_eq, hRR.grade_eq, hRR.F_eq⟩
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
      hI', ?_, ?_, hRR.bind_eq, hRR.grade_eq, hRR.F_eq⟩
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
      hI', ?_, ?_, hRR.bind_eq, hRR.grade_eq, hRR.F_eq⟩
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
      hI', ?_, ?_, hRR.bind_eq, hRR.grade_eq, hRR.F_eq⟩
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
      hI', ?_, ?_, hRR.bind_eq, hRR.grade_eq, hRR.F_eq⟩
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
      hI', hRR.call_eq, hRR.ret_eq, hRR.bind_eq, hRR.grade_eq, hRR.F_eq⟩
  | bindGhost i b hi hm hb =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hq : q2.quorum P :=
      quorum_of_vote_quorum hRR (hRR.inv.bind_conf i b hi hm)
    have hw : ∃ id', id' ∉ q2.F ∧ q2.call id' = some b := by
      obtain ⟨m0, hmF, hmi⟩ := exists_honest_input_of_bind hRR.inv hi hm
      exact ⟨m0, by rw [hRR.F_eq]; exact hmF, by rw [hRR.call_eq]; exact hmi⟩
    have hbnone : q2.bind = none := by rw [hRR.bind_eq]; exact hb
    exact ⟨{ q2 with bind := some b },
      Or.inl ⟨rfl, weakLSilent_single (Step.bindSet q2 b hq hw hbnone)⟩,
      hI', hRR.call_eq, hRR.ret_eq, rfl, hRR.grade_eq, hRR.F_eq⟩
  | retA id v hb hcnt hr =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hbnd : q2.bind = some v := by rw [hRR.bind_eq]; exact hb
    have hgr : q2.grade = none ∨ q2.grade = some true := by
      have hne := grade_ne_false_of_bind_quorum hRR.inv hcnt
      rw [hRR.grade_eq]
      cases hg : q1.grade with
      | none => exact Or.inl rfl
      | some gb =>
        cases gb
        · exact absurd hg hne
        · exact Or.inr rfl
    have hret : q2.ret id = false := by rw [hRR.ret_eq]; exact hr
    refine ⟨{ q2 with grade := some true, ret := Function.update q2.ret id true },
      Or.inr ⟨by simp,
        weakLStep_single (Step.retA q2 id v hbnd hgr hret) (by simp)⟩,
      hI', ?_, ?_, hRR.bind_eq, rfl, hRR.F_eq⟩
    · intro k
      by_cases hk : k = id
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_ret_ne hk]
        exact hRR.call_eq k
    · intro k
      change Function.update q2.ret id true k = _
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        simp
      · rw [Function.update_of_ne hk, proc_ret_ne hk]
        exact hRR.ret_eq k
  | retB id v hb hcnt honce hvote hval hr =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hbnd : q2.bind = some v := by rw [hRR.bind_eq]; exact hb
    have hw : ∃ id', id' ∉ q2.F ∧ q2.call id' = some (!v) := by
      obtain ⟨m0, hmF, hmi⟩ := exists_honest_input_of_valid hRR.inv hval (!v)
      exact ⟨m0, by rw [hRR.F_eq]; exact hmF, by rw [hRR.call_eq]; exact hmi⟩
    have hret : q2.ret id = false := by rw [hRR.ret_eq]; exact hr
    refine ⟨{ q2 with ret := Function.update q2.ret id true },
      Or.inr ⟨by simp,
        weakLStep_single (Step.retB q2 id v hbnd hw hret) (by simp)⟩,
      hI', ?_, ?_, hRR.bind_eq, hRR.grade_eq, hRR.F_eq⟩
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
  | retC id v hb hcnt hval hr =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hbnd : q2.bind = some v := by rw [hRR.bind_eq]; exact hb
    have hw : ∃ id', id' ∉ q2.F ∧ q2.call id' = some (!v) := by
      obtain ⟨m0, hmF, hmi⟩ := exists_honest_input_of_valid hRR.inv hval (!v)
      exact ⟨m0, by rw [hRR.F_eq]; exact hmF, by rw [hRR.call_eq]; exact hmi⟩
    have hgr : q2.grade = none ∨ q2.grade = some false := by
      have hne := grade_ne_true_of_bot_quorum hRR.inv hcnt
      rw [hRR.grade_eq]
      cases hg : q1.grade with
      | none => exact Or.inl rfl
      | some gb =>
        cases gb
        · exact Or.inr rfl
        · exact absurd hg hne
    have hret : q2.ret id = false := by rw [hRR.ret_eq]; exact hr
    refine ⟨{ q2 with grade := some false, ret := Function.update q2.ret id true },
      Or.inr ⟨by simp,
        weakLStep_single (Step.retC q2 id v hbnd hw hgr hret) (by simp)⟩,
      hI', ?_, ?_, hRR.bind_eq, rfl, hRR.F_eq⟩
    · intro k
      by_cases hk : k = id
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_ret_ne hk]
        exact hRR.call_eq k
    · intro k
      change Function.update q2.ret id true k = _
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        simp
      · rw [Function.update_of_ne hk, proc_ret_ne hk]
        exact hRR.ret_eq k
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2.corrupt P id,
      Or.inr ⟨by simp, weakLStep_single (Step.fail q2 id) (by simp)⟩,
      hI', ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      rw [spec_corrupt_call, ImplState.corrupt_proc]
      exact hRR.call_eq k
    · intro k
      rw [spec_corrupt_ret, ImplState.corrupt_proc]
      exact hRR.ret_eq k
    · rw [spec_corrupt_bind, ImplState.corrupt_bound]
      exact hRR.bind_eq
    · rw [spec_corrupt_grade, ImplState.corrupt_grade]
      exact hRR.grade_eq
    · exact corrupt_F_eq hRR.F_eq id

end GBCA
end ABA
end PLTS
