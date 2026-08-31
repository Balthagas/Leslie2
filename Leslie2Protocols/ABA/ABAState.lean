/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Components

/-!
# The ABA-side state of the composed reading

The round-loop records beside the ABA-side network, read as one object.

`ABAState` is the pair `(∀ j, CoreRec) × ANetState`. Its accessors gather the
data the two components hold apart: `procs` reads each process's control
record, `decidedRecv` its receipts, and `decidedSent` and `F` the network's
sent pools and corrupted set. The invariant of the core simulation is stated
through these accessors, so it reads the composed state without a change of
system.
-/

namespace PLTS
namespace ABA

open Net Comp

variable {P : Params}

/-- **The ABA-side state**: the `n` round-loop records beside the ABA-side
network. -/
abbrev ABAState (P : Params) : Type :=
  (∀ _ : Fin P.n, CoreRec P.n) × ANetState P.n

namespace ABAState

/-- The control record of process `id`. -/
def procs (s : ABAState P) : Fin P.n → ProcCore P.n := fun j => (s.1 j).proc

/-- `b ∈ s.decidedSent id` — process `id` has multicast `⟨DECIDED, b⟩`. -/
def decidedSent (s : ABAState P) : Fin P.n → Finset Bool := s.2.dpool

/-- `b ∈ s.decidedRecv i j` — `j`'s `⟨DECIDED, b⟩` has been delivered to `i`. -/
def decidedRecv (s : ABAState P) : Fin P.n → Fin P.n → Finset Bool :=
  fun i => (s.1 i).decIn

/-- The corrupted set. -/
def F (s : ABAState P) : Finset (Fin P.n) := s.2.F

@[simp] theorem procs_apply (C : ∀ _ : Fin P.n, CoreRec P.n) (a : ANetState P.n)
    (j : Fin P.n) : procs (P := P) (C, a) j = (C j).proc := rfl
@[simp] theorem decidedSent_apply (C : ∀ _ : Fin P.n, CoreRec P.n) (a : ANetState P.n) :
    decidedSent (P := P) (C, a) = a.dpool := rfl
@[simp] theorem decidedRecv_apply (C : ∀ _ : Fin P.n, CoreRec P.n) (a : ANetState P.n)
    (i : Fin P.n) : decidedRecv (P := P) (C, a) i = (C i).decIn := rfl
@[simp] theorem F_apply (C : ∀ _ : Fin P.n, CoreRec P.n) (a : ANetState P.n) :
    F (P := P) (C, a) = a.F := rfl

/-- Dot notation resolves against `ABAState`, so the invariant reads the
composed state in the accessors' own names. -/
example (s : ABAState P) (j : Fin P.n) : s.procs j = (s.1 j).proc := rfl

/-! ### State update helpers -/

/-- The initial ABA-side state: all round loops idle, nothing multicast,
nobody corrupted. -/
def initial (P : Params) : ABAState P :=
  (fun _ => CoreRec.initial P.n, ANetState.initial P.n)

/-! The two components' own initial states project componentwise, so unfolding
`initial` leaves no residue. -/

@[simp] theorem _root_.PLTS.ABA.CoreRec.initial_proc (n : ℕ) :
    (CoreRec.initial n).proc = ProcCore.initial n := rfl
@[simp] theorem _root_.PLTS.ABA.CoreRec.initial_decIn (n : ℕ) (j : Fin n) :
    (CoreRec.initial n).decIn j = ∅ := rfl
@[simp] theorem _root_.PLTS.ABA.Comp.ANetState.initial_dpool (n : ℕ) (j : Fin n) :
    (ANetState.initial n).dpool j = ∅ := rfl
@[simp] theorem _root_.PLTS.ABA.Comp.ANetState.initial_F (n : ℕ) :
    (ANetState.initial n).F = ∅ := rfl

@[simp] theorem initial_procs (id : Fin P.n) :
    (initial P).procs id = ProcCore.initial P.n := rfl
@[simp] theorem initial_decidedSent (id : Fin P.n) :
    (initial P).decidedSent id = ∅ := rfl
@[simp] theorem initial_decidedRecv (i j : Fin P.n) :
    (initial P).decidedRecv i j = ∅ := rfl
@[simp] theorem initial_F : (initial P).F = ∅ := rfl

/-- The number of distinct senders whose `⟨DECIDED, b⟩` has been delivered to
receiver `id`. -/
def decidedCount (s : ABAState P) (id : Fin P.n) (b : Bool) : ℕ :=
  (Finset.univ.filter (fun j => b ∈ s.decidedRecv id j)).card

@[simp] theorem initial_decidedCount (id : Fin P.n) (b : Bool) :
    (initial P).decidedCount id b = 0 := by
  simp [decidedCount]

/-- Update the control record of process `id`. -/
def setProc (s : ABAState P) (id : Fin P.n) (p : ProcCore P.n) : ABAState P :=
  (Function.update s.1 id ((s.1 id).setProc p), s.2)

@[simp] theorem setProc_decidedSent (s : ABAState P) (id : Fin P.n) (p : ProcCore P.n) :
    (s.setProc id p).decidedSent = s.decidedSent := rfl
@[simp] theorem setProc_F (s : ABAState P) (id : Fin P.n) (p : ProcCore P.n) :
    (s.setProc id p).F = s.F := rfl

@[simp] theorem setProc_decidedRecv (s : ABAState P) (id : Fin P.n) (p : ProcCore P.n) :
    (s.setProc id p).decidedRecv = s.decidedRecv := by
  funext i
  by_cases hi : i = id
  · subst hi; simp [setProc, decidedRecv, CoreRec.setProc]
  · simp [setProc, decidedRecv, Function.update_of_ne hi]

@[simp] theorem setProc_decidedCount (s : ABAState P) (id : Fin P.n) (p : ProcCore P.n)
    (i : Fin P.n) (b : Bool) :
    (s.setProc id p).decidedCount i b = s.decidedCount i b := by
  simp [decidedCount]

@[simp] theorem setProc_procs_self (s : ABAState P) (id : Fin P.n) (p : ProcCore P.n) :
    (s.setProc id p).procs id = p := by
  simp [setProc, procs, CoreRec.setProc]

theorem setProc_procs_ne (s : ABAState P) (id : Fin P.n) (p : ProcCore P.n)
    {k : Fin P.n} (h : k ≠ id) : (s.setProc id p).procs k = s.procs k := by
  simp [setProc, procs, Function.update_of_ne h]

/-- Process `id` multicasts `⟨DECIDED, b⟩`: the network pools `b` under `id`
(deviation D12′ — the pool only ever grows). -/
def sendDecided (s : ABAState P) (id : Fin P.n) (b : Bool) : ABAState P :=
  (s.1, s.2.dput id b)

@[simp] theorem sendDecided_procs (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.sendDecided id b).procs = s.procs := rfl
@[simp] theorem sendDecided_decidedRecv (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.sendDecided id b).decidedRecv = s.decidedRecv := rfl
@[simp] theorem sendDecided_F (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.sendDecided id b).F = s.F := rfl
@[simp] theorem sendDecided_decidedSent (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.sendDecided id b).decidedSent =
      Function.update s.decidedSent id (insert b (s.decidedSent id)) := rfl
@[simp] theorem sendDecided_decidedCount (s : ABAState P) (id : Fin P.n) (b : Bool)
    (i : Fin P.n) (b' : Bool) :
    (s.sendDecided id b).decidedCount i b' = s.decidedCount i b' := rfl

/-- Sent pools only grow under `sendDecided`. -/
theorem sendDecided_decidedSent_mono (s : ABAState P) (id : Fin P.n) (b : Bool)
    {k : Fin P.n} {b' : Bool} (h : b' ∈ s.decidedSent k) :
    b' ∈ (s.sendDecided id b).decidedSent k := by
  by_cases hk : k = id
  · subst hk
    simp only [sendDecided_decidedSent, Function.update_self]
    exact Finset.mem_insert_of_mem h
  · simp only [sendDecided_decidedSent, Function.update_of_ne hk]
    exact h

/-- Membership in a post-`sendDecided` sent pool: the fresh bit at `id`, or an
old pool member. -/
theorem mem_sendDecided_decidedSent_iff (s : ABAState P) (id : Fin P.n) (b : Bool)
    (k : Fin P.n) (b' : Bool) :
    b' ∈ (s.sendDecided id b).decidedSent k ↔
      (k = id ∧ b' = b) ∨ b' ∈ s.decidedSent k := by
  by_cases hk : k = id
  · subst hk
    simp [sendDecided_decidedSent, Function.update_self, Finset.mem_insert]
  · simp [sendDecided_decidedSent, hk]

/-- The adversary delivers `⟨DECIDED, b⟩` from sender `j` to receiver `i`:
the receiver's record files `b` under `j` (per-(receiver, sender, bit),
deviation D12′). -/
def deliverDecided (s : ABAState P) (i j : Fin P.n) (b : Bool) : ABAState P :=
  (Function.update s.1 i ((s.1 i).recvDec j b), s.2)

@[simp] theorem deliverDecided_decidedSent (s : ABAState P) (i j : Fin P.n) (b : Bool) :
    (s.deliverDecided i j b).decidedSent = s.decidedSent := rfl
@[simp] theorem deliverDecided_F (s : ABAState P) (i j : Fin P.n) (b : Bool) :
    (s.deliverDecided i j b).F = s.F := rfl

@[simp] theorem deliverDecided_procs (s : ABAState P) (i j : Fin P.n) (b : Bool) :
    (s.deliverDecided i j b).procs = s.procs := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [deliverDecided, procs, CoreRec.recvDec]
  · simp [deliverDecided, procs, Function.update_of_ne hk]

@[simp] theorem deliverDecided_decidedRecv_self (s : ABAState P) (i j : Fin P.n) (b : Bool) :
    (s.deliverDecided i j b).decidedRecv i j = insert b (s.decidedRecv i j) := by
  simp [deliverDecided, decidedRecv, CoreRec.recvDec]

/-- Deliveries to other (receiver, sender) edges are untouched. -/
theorem deliverDecided_decidedRecv_of_ne (s : ABAState P) (i j : Fin P.n) (b : Bool)
    {i' j' : Fin P.n} (h : i' ≠ i ∨ j' ≠ j) :
    (s.deliverDecided i j b).decidedRecv i' j' = s.decidedRecv i' j' := by
  rcases h with h | h
  · simp [deliverDecided, decidedRecv, Function.update_of_ne h]
  · by_cases hi : i' = i
    · subst hi
      simp [deliverDecided, decidedRecv, CoreRec.recvDec, Function.update_of_ne h]
    · simp [deliverDecided, decidedRecv, Function.update_of_ne hi]

/-- The round advance of process `id` on receiving the coin `c` (fused
DECIDED-send, deviation D10): adopt the coin when the estimate is `⊥`,
multicast `⟨DECIDED, b⟩` when the round's grade was `A b`, clear the grade and
move to `toCallG` of the next round. -/
def stepRound (s : ABAState P) (id : Fin P.n) (c : Bool) : ABAState P :=
  (match (s.procs id).lastGrade with
    | some (.A b) => s.sendDecided id b
    | _ => s).setProc id
    { s.procs id with
      est := some ((s.procs id).est.getD c),
      lastGrade := none,
      round := (s.procs id).round + 1,
      phase := .toCallG }

@[simp] theorem stepRound_procs_self (s : ABAState P) (id : Fin P.n) (c : Bool) :
    (s.stepRound id c).procs id =
      { s.procs id with
        est := some ((s.procs id).est.getD c),
        lastGrade := none,
        round := (s.procs id).round + 1,
        phase := .toCallG } := by
  unfold stepRound
  exact setProc_procs_self _ _ _

theorem stepRound_procs_ne (s : ABAState P) (id : Fin P.n) (c : Bool)
    {k : Fin P.n} (h : k ≠ id) : (s.stepRound id c).procs k = s.procs k := by
  unfold stepRound
  cases (s.procs id).lastGrade with
  | none => exact setProc_procs_ne _ _ _ h
  | some out => cases out <;> exact setProc_procs_ne _ _ _ h

@[simp] theorem stepRound_decidedRecv (s : ABAState P) (id : Fin P.n) (c : Bool) :
    (s.stepRound id c).decidedRecv = s.decidedRecv := by
  unfold stepRound
  cases (s.procs id).lastGrade with
  | none => exact setProc_decidedRecv _ _ _
  | some out => cases out <;> exact setProc_decidedRecv _ _ _

@[simp] theorem stepRound_F (s : ABAState P) (id : Fin P.n) (c : Bool) :
    (s.stepRound id c).F = s.F := by
  unfold stepRound
  cases (s.procs id).lastGrade with
  | none => rfl
  | some out => cases out <;> rfl

@[simp] theorem stepRound_decidedCount (s : ABAState P) (id : Fin P.n) (c : Bool)
    (i : Fin P.n) (b : Bool) :
    (s.stepRound id c).decidedCount i b = s.decidedCount i b := by
  unfold decidedCount
  rw [stepRound_decidedRecv]

/-- On an `A b` grade the round advance multicasts `⟨DECIDED, b⟩`. -/
theorem stepRound_decidedSent_of_A (s : ABAState P) (id : Fin P.n) (c b : Bool)
    (h : (s.procs id).lastGrade = some (.A b)) :
    (s.stepRound id c).decidedSent =
      Function.update s.decidedSent id (insert b (s.decidedSent id)) := by
  unfold stepRound
  rw [h]
  rfl

/-- Without an `A` grade the round advance leaves the DECIDED slots alone. -/
theorem stepRound_decidedSent_of_not_A (s : ABAState P) (id : Fin P.n) (c : Bool)
    (h : ∀ b, (s.procs id).lastGrade ≠ some (.A b)) :
    (s.stepRound id c).decidedSent = s.decidedSent := by
  unfold stepRound
  cases hg : (s.procs id).lastGrade with
  | none => rfl
  | some out =>
    cases out with
    | A b => exact absurd hg (h b)
    | B b => rfl
    | C => rfl

/-- The round advance when the round carried no `A` grade: the round loop's
own advance, the network untouched. -/
theorem stepRound_plain (C : ∀ _ : Fin P.n, CoreRec P.n) (A : ANetState P.n)
    (id : Fin P.n) (co : Bool)
    (hg : ∀ v : Bool, (C id).proc.lastGrade ≠ some (.A v)) :
    stepRound (P := P) (C, A) id co
      = (Function.update C id ((C id).stepRound co), A) := by
  unfold stepRound
  cases hlg : (C id).proc.lastGrade with
  | none => rw [show (procs (P := P) (C, A) id).lastGrade = none from hlg]; rfl
  | some out =>
    cases out with
    | A v => exact absurd hlg (hg v)
    | B v => rw [show (procs (P := P) (C, A) id).lastGrade = some (.B v) from hlg]; rfl
    | C => rw [show (procs (P := P) (C, A) id).lastGrade = some .C from hlg]; rfl

/-- The round advance on an `A b` grade: the round loop's advance joined with
the network's publication of `b` (the fused DECIDED-send, D10). -/
theorem stepRound_pub (C : ∀ _ : Fin P.n, CoreRec P.n) (A : ANetState P.n)
    (id : Fin P.n) (co b : Bool) (hg : (C id).proc.lastGrade = some (.A b)) :
    stepRound (P := P) (C, A) id co
      = (Function.update C id ((C id).stepRound co), A.dput id b) := by
  unfold stepRound
  rw [show (procs (P := P) (C, A) id).lastGrade = some (.A b) from hg]
  rfl

/-- Corruption (deviation D1): total, Dirac, monotone in `F`, and the
network's own row — the round loops are corruption-blind. -/
def corrupt (P : Params) (id : Fin P.n) (s : ABAState P) : ABAState P :=
  (s.1, ANetState.corrupt P id s.2)

@[simp] theorem corrupt_procs (s : ABAState P) (id : Fin P.n) :
    (s.corrupt P id).procs = s.procs := rfl
@[simp] theorem corrupt_decidedRecv (s : ABAState P) (id : Fin P.n) :
    (s.corrupt P id).decidedRecv = s.decidedRecv := rfl
@[simp] theorem corrupt_decidedSent (s : ABAState P) (id : Fin P.n) :
    (s.corrupt P id).decidedSent = s.decidedSent := by
  unfold corrupt decidedSent ANetState.corrupt; split <;> rfl
@[simp] theorem corrupt_decidedCount (s : ABAState P) (id : Fin P.n)
    (i : Fin P.n) (b : Bool) :
    (s.corrupt P id).decidedCount i b = s.decidedCount i b := rfl

/-- The corrupted set after a corruption. `F` is the one field corruption
writes, and the budget guard sits in the network component, so the reading is
stated here rather than reached by unfolding. Not a simp lemma: it introduces
an `ite`. -/
theorem corrupt_F (P : Params) (id : Fin P.n) (s : ABAState P) :
    (s.corrupt P id).F = if id ∉ s.F ∧ s.F.card < P.f then insert id s.F else s.F := by
  unfold corrupt F ANetState.corrupt
  split_ifs <;> rfl

end ABAState

end ABA
end PLTS
