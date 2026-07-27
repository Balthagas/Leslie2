/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2.Results
import Leslie2Protocols.ABA.Core
import Leslie2Protocols.Framework.FamilySim
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SyncProduct

/-!
# The ABA core, one process at a time

`ABA.core` (`ABA/Core.lean`) is a single automaton whose state is the whole
system: an array of control records, an array of DECIDED pools, a matrix of
receipt pools. Its rules therefore read fields of processes other than the one
they move — `deliver i j b` inspects `j`'s pool and `i`'s receipt row in one
guard. That is a modelling convenience, not a property of the algorithm.

This file presents the same protocol as the code one process runs.
`ABA.CoreProc P j` is the automaton of process `j` alone: its control record,
its own DECIDED pool, the rows of DECIDED receipts addressed to it, and its
copy of the corrupted set. Every guard reads only those fields. The processes
are composed under full synchronisation (`System.syncProduct`), which turns a
shared label into a handshake: the process that owns the label moves by its own
rule, and every other process answers with an idle self-loop.

Gossip is the one interaction the shared alphabet `Lab n` cannot express, since
`Lab n` has no name for "`j`'s DECIDED reaches `i`". The alphabet is therefore
extended to `Lab n ⊕ DNet n`, where `DNet.net i j b` is the delivery of `j`'s
`⟨DECIDED, b⟩` to `i`. That label is a genuine two-party rendezvous: the sender
copy contributes the soundness guard `b ∈ decOut`, the receiver copy the
freshness guard `b ∉ decIn j` and the write. Composition hides the whole
`Sum.inr` block (`System.abstract`), and `System.relabel` reads the result back
over `Lab n`, so the composite speaks exactly the alphabet every other
component of the development speaks.

`perProcCore_atd` is the theorem the presentation exists for: the composite and
the monolithic core achieve the same trace distributions. Locality of the
guards is then not a stylistic claim about the model but a statement with a
proof — the global rules of `ABA/Core.lean` are recovered from rules that read
one process's fields.

## The rule correspondence

Each rule of `CoreProcStep` localises one rule of `CoreStep`, under the packing
`procs j = (q j).proc`, `decidedSent j = (q j).decOut`,
`decidedRecv i j = (q i).decIn j` and `F = (q j).F` (every copy agreeing).

| `CoreStep` | `CoreProcStep` at the owner | at the others |
| --- | --- | --- |
| `input`, `inputLoop` | `input`, `inputLoop` | `callABAIdle` |
| `ret` | `ret` | `retABAIdle` |
| `callG`, `callGByz` | `callG`, `callGByz` | `callGIdle` |
| `retG`, `retGByz` | `retG`, `retGByz` | `retGIdle` |
| `callW`, `callWByz` | `callW`, `callWByz` | `callWIdle` |
| `retW`, `retWByz` | `retW`, `retWByz` | `retWIdle` |
| `fail` | `fail` (every copy) | — |
| `echo`, `byzDecided` | `echo`, `byzDecided` (interleaved) | — |
| `deliver i j b` | `netSelf` / `netSend` / `netRecv` | `netIdle` |

A label that no process owns is blocked by the product, because the conjunction
over all components has no witness. That is how the composite reproduces a
failed monolithic guard: on `retABA j b` with the quorum count too low, the
owner offers nothing, so the product offers nothing, exactly as `CoreStep` has
no `retABA` transition there. Idle self-loops are given on every label the
process does not own, since full synchronisation otherwise blocks the label
outright — an idle loop is a component saying "not my business", never a
component enabling a step of its own.

## Model notes

The deviations of `ABA/Core.lean` (D9 0-based rounds, D10 fused DECIDED-send,
D11 byzantine handshake drivers, D12′ per-process DECIDED pools) are inherited
verbatim; the per-process presentation changes no guard. D12′ is what makes the
split possible: the DECIDED pools are already indexed by process, so `decOut`
is one process's field and `decIn` one process's rows.
-/

namespace PLTS
namespace ABA

/-! ### The gossip alphabet -/

/-- The auxiliary alphabet of DECIDED deliveries: `net i j b` carries `j`'s
`⟨DECIDED, b⟩` multicast to receiver `i`, mirroring the receiver/sender order of
the monolithic `CoreStep.deliver`. These labels exist only to let the sender and
receiver copies rendezvous, and are hidden by `perProcCore`. -/
inductive DNet (n : ℕ) : Type
  /-- Delivery of `j`'s `⟨DECIDED, b⟩` to receiver `i`. -/
  | net (i j : Fin n) (b : Bool)
  deriving DecidableEq, Repr

/-- The extended alphabet of the per-process presentation: the shared alphabet
of the development together with the gossip labels. Its silent label is
`Sum.inl Lab.tau` (`PLTS.instSilentSum`). -/
abbrev CoreLab (n : ℕ) : Type := Lab n ⊕ DNet n

/-! ### The state of one process -/

/-- The state of one core process: its control record, its own DECIDED pool,
the DECIDED receipts addressed to it (one row per sender) and its copy of the
corrupted set. Nothing here mentions another process's control or pool. -/
structure CoreNode (n : ℕ) : Type where
  /-- The process's own control record (the record of `ABA/Core.lean`). -/
  proc : ProcCore n
  /-- The process's own DECIDED pool: the payloads it has multicast
  (`decidedSent` at this process, deviation D12′). -/
  decOut : Finset Bool
  /-- The DECIDED payloads delivered to this process, indexed by sender
  (`decidedRecv` at this receiver). -/
  decIn : Fin n → Finset Bool
  /-- The process's copy of the corrupted set, kept in lockstep by the `fail`
  broadcast. -/
  F : Finset (Fin n)

namespace CoreNode

variable {n : ℕ}

/-- The initial state of one process: idle control record, empty pools, nobody
corrupted. -/
def initial (n : ℕ) : CoreNode n where
  proc := ProcCore.initial n
  decOut := ∅
  decIn := fun _ => ∅
  F := ∅

@[simp] theorem initial_proc (n : ℕ) : (initial n).proc = ProcCore.initial n := rfl
@[simp] theorem initial_decOut (n : ℕ) : (initial n).decOut = ∅ := rfl
@[simp] theorem initial_decIn (n : ℕ) (k : Fin n) : (initial n).decIn k = ∅ := rfl
@[simp] theorem initial_F (n : ℕ) : (initial n).F = ∅ := rfl

/-- The number of distinct senders whose `⟨DECIDED, b⟩` this process holds — the
local reading of `CoreState.decidedCount` at this receiver. -/
def decidedCount (q : CoreNode n) (b : Bool) : ℕ :=
  (Finset.univ.filter (fun k => b ∈ q.decIn k)).card

/-- Update the control record. -/
def setProc (q : CoreNode n) (p : ProcCore n) : CoreNode n := { q with proc := p }

@[simp] theorem setProc_proc (q : CoreNode n) (p : ProcCore n) :
    (q.setProc p).proc = p := rfl
@[simp] theorem setProc_decOut (q : CoreNode n) (p : ProcCore n) :
    (q.setProc p).decOut = q.decOut := rfl
@[simp] theorem setProc_decIn (q : CoreNode n) (p : ProcCore n) :
    (q.setProc p).decIn = q.decIn := rfl
@[simp] theorem setProc_F (q : CoreNode n) (p : ProcCore n) :
    (q.setProc p).F = q.F := rfl

/-- Multicast `⟨DECIDED, b⟩`: insert `b` into the own pool (deviation D12′ — the
pool only grows). -/
def sendDec (q : CoreNode n) (b : Bool) : CoreNode n :=
  { q with decOut := insert b q.decOut }

@[simp] theorem sendDec_proc (q : CoreNode n) (b : Bool) : (q.sendDec b).proc = q.proc := rfl
@[simp] theorem sendDec_decOut (q : CoreNode n) (b : Bool) :
    (q.sendDec b).decOut = insert b q.decOut := rfl
@[simp] theorem sendDec_decIn (q : CoreNode n) (b : Bool) : (q.sendDec b).decIn = q.decIn := rfl
@[simp] theorem sendDec_F (q : CoreNode n) (b : Bool) : (q.sendDec b).F = q.F := rfl

/-- Record a delivered `⟨DECIDED, b⟩` from sender `k`. -/
def recvDec (q : CoreNode n) (k : Fin n) (b : Bool) : CoreNode n :=
  { q with decIn := Function.update q.decIn k (insert b (q.decIn k)) }

@[simp] theorem recvDec_proc (q : CoreNode n) (k : Fin n) (b : Bool) :
    (q.recvDec k b).proc = q.proc := rfl
@[simp] theorem recvDec_decOut (q : CoreNode n) (k : Fin n) (b : Bool) :
    (q.recvDec k b).decOut = q.decOut := rfl
@[simp] theorem recvDec_F (q : CoreNode n) (k : Fin n) (b : Bool) :
    (q.recvDec k b).F = q.F := rfl
@[simp] theorem recvDec_decIn_self (q : CoreNode n) (k : Fin n) (b : Bool) :
    (q.recvDec k b).decIn k = insert b (q.decIn k) := by
  simp [recvDec]

theorem recvDec_decIn_of_ne (q : CoreNode n) (k : Fin n) (b : Bool) {k' : Fin n}
    (h : k' ≠ k) : (q.recvDec k b).decIn k' = q.decIn k' := by
  simp [recvDec, Function.update_of_ne h]

/-- The round advance on receiving the coin `c` (deviation D10, fused
DECIDED-send): adopt the coin when the estimate is `⊥`, multicast
`⟨DECIDED, b⟩` when the round's grade was `A b`, clear the grade and move to
`toCallG` of the next round. The local reading of `CoreState.stepRound`. -/
def stepRound (q : CoreNode n) (c : Bool) : CoreNode n :=
  (match q.proc.lastGrade with
    | some (.A b) => q.sendDec b
    | _ => q).setProc
    { q.proc with
      est := some (q.proc.est.getD c),
      lastGrade := none,
      round := q.proc.round + 1,
      phase := .toCallG }

@[simp] theorem stepRound_proc (q : CoreNode n) (c : Bool) :
    (q.stepRound c).proc =
      { q.proc with
        est := some (q.proc.est.getD c),
        lastGrade := none,
        round := q.proc.round + 1,
        phase := .toCallG } := by
  unfold stepRound
  cases q.proc.lastGrade with
  | none => rfl
  | some out => cases out <;> rfl

@[simp] theorem stepRound_decIn (q : CoreNode n) (c : Bool) :
    (q.stepRound c).decIn = q.decIn := by
  unfold stepRound
  cases q.proc.lastGrade with
  | none => rfl
  | some out => cases out <;> rfl

@[simp] theorem stepRound_F (q : CoreNode n) (c : Bool) : (q.stepRound c).F = q.F := by
  unfold stepRound
  cases q.proc.lastGrade with
  | none => rfl
  | some out => cases out <;> rfl

@[simp] theorem stepRound_decidedCount (q : CoreNode n) (c : Bool) (b : Bool) :
    (q.stepRound c).decidedCount b = q.decidedCount b := by
  unfold decidedCount
  rw [stepRound_decIn]

/-- On an `A b` grade the round advance multicasts `⟨DECIDED, b⟩`. -/
theorem stepRound_decOut_of_A (q : CoreNode n) (c b : Bool)
    (h : q.proc.lastGrade = some (.A b)) :
    (q.stepRound c).decOut = insert b q.decOut := by
  unfold stepRound
  rw [h]
  rfl

/-- Without an `A` grade the round advance leaves the DECIDED pool alone. -/
theorem stepRound_decOut_of_not_A (q : CoreNode n) (c : Bool)
    (h : ∀ b, q.proc.lastGrade ≠ some (.A b)) :
    (q.stepRound c).decOut = q.decOut := by
  unfold stepRound
  cases hg : q.proc.lastGrade with
  | none => rfl
  | some out =>
    cases out with
    | A b => exact absurd hg (h b)
    | B b => rfl
    | C => rfl

/-- Corruption (deviation D1) on one process's copy of the corrupted set: the
same guard `id ∉ F ∧ |F| < f` as `CoreState.corrupt`, so copies that start
equal stay equal. -/
def corrupt (P : Params) (id : Fin P.n) (q : CoreNode P.n) : CoreNode P.n :=
  if id ∉ q.F ∧ q.F.card < P.f then { q with F := insert id q.F } else q

@[simp] theorem corrupt_proc {P : Params} (q : CoreNode P.n) (id : Fin P.n) :
    (q.corrupt P id).proc = q.proc := by
  unfold corrupt; split <;> rfl
@[simp] theorem corrupt_decOut {P : Params} (q : CoreNode P.n) (id : Fin P.n) :
    (q.corrupt P id).decOut = q.decOut := by
  unfold corrupt; split <;> rfl
@[simp] theorem corrupt_decIn {P : Params} (q : CoreNode P.n) (id : Fin P.n) :
    (q.corrupt P id).decIn = q.decIn := by
  unfold corrupt; split <;> rfl

end CoreNode

/-! ### The automaton of one process -/

/-- The step relation of process `j`'s automaton (blueprint Algorithm 1, read as
the code of a single process). Every guard reads only `j`'s own fields; labels
`j` does not own carry idle self-loops so that full synchronisation lets their
owner move. All transitions are Dirac. -/
inductive CoreProcStep (P : Params) (j : Fin P.n) :
    CoreNode P.n → CoreLab P.n → PMF (CoreNode P.n) → Prop
  /-- `upon ABA(b)`: the external input arrives at `j`. Record it as input and
  estimate and enter round `0` (deviation D9). -/
  | input (q : CoreNode P.n) (b : Bool) (h : q.proc.input = none) :
      CoreProcStep P j q (Sum.inl (.callABA j b))
        (PMF.pure (q.setProc { q.proc with
          input := some b, est := some b, round := 0, phase := .toCallG }))
  /-- Input-enabledness loop on `j`'s own `callABA` (the spec's rule 2). -/
  | inputLoop (q : CoreNode P.n) (b : Bool) :
      CoreProcStep P j q (Sum.inl (.callABA j b)) (PMF.pure q)
  /-- Another process receives its input: not `j`'s business. -/
  | callABAIdle (q : CoreNode P.n) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      CoreProcStep P j q (Sum.inl (.callABA id b)) (PMF.pure q)
  /-- `upon ⟨DECIDED, b⟩ from n − f senders, having multicast ⟨DECIDED, b⟩:
  return b`. The quorum counts distinct senders in `j`'s own receipt rows; no
  honesty check, as in the monolithic rule. -/
  | ret (q : CoreNode P.n) (b : Bool) (hcnt : P.n - P.f ≤ q.decidedCount b)
      (hs : b ∈ q.decOut) (hret : q.proc.returned = false) :
      CoreProcStep P j q (Sum.inl (.retABA j b))
        (PMF.pure (q.setProc { q.proc with returned := true }))
  /-- Another process returns: not `j`'s business. -/
  | retABAIdle (q : CoreNode P.n) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      CoreProcStep P j q (Sum.inl (.retABA id b)) (PMF.pure q)
  /-- `(b, g) ← GBCA_r(b)`, the call half: emit the current estimate to the
  current round's GBCA (input coherence — the emitted bit *is* the estimate). -/
  | callG (q : CoreNode P.n) (r : ℕ) (b : Bool) (hph : q.proc.phase = .toCallG)
      (hr : q.proc.round = r) (hest : q.proc.est = some b) :
      CoreProcStep P j q (Sum.inl (.callG r j b))
        (PMF.pure (q.setProc { q.proc with phase := .awaitG }))
  /-- Byzantine GBCA-call driver (deviation D11): once corrupted, `j` may emit
  any `callG`, with no state change. -/
  | callGByz (q : CoreNode P.n) (r : ℕ) (b : Bool) (hF : j ∈ q.F) :
      CoreProcStep P j q (Sum.inl (.callG r j b)) (PMF.pure q)
  /-- A GBCA call of another process: not `j`'s business. -/
  | callGIdle (q : CoreNode P.n) (r : ℕ) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      CoreProcStep P j q (Sum.inl (.callG r id b)) (PMF.pure q)
  /-- `(b, g) ← GBCA_r(b)`, the return half: record the graded outcome — `A b`
  and `B b` set the estimate to `b`, `C` clears it to `⊥` — and head for the
  coin. -/
  | retG (q : CoreNode P.n) (r : ℕ) (out : GbcaOut) (hph : q.proc.phase = .awaitG)
      (hr : q.proc.round = r) :
      CoreProcStep P j q (Sum.inl (.retG r j out))
        (PMF.pure (q.setProc { q.proc with
          est := out.est, lastGrade := some out, phase := .toCallW }))
  /-- Byzantine GBCA-return driver (deviation D11). -/
  | retGByz (q : CoreNode P.n) (r : ℕ) (out : GbcaOut) (hF : j ∈ q.F) :
      CoreProcStep P j q (Sum.inl (.retG r j out)) (PMF.pure q)
  /-- A GBCA return to another process: not `j`'s business. -/
  | retGIdle (q : CoreNode P.n) (r : ℕ) (id : Fin P.n) (out : GbcaOut) (hid : id ≠ j) :
      CoreProcStep P j q (Sum.inl (.retG r id out)) (PMF.pure q)
  /-- `c ← WCC_r()`, the call half. -/
  | callW (q : CoreNode P.n) (r : ℕ) (hph : q.proc.phase = .toCallW)
      (hr : q.proc.round = r) :
      CoreProcStep P j q (Sum.inl (.callW r j))
        (PMF.pure (q.setProc { q.proc with phase := .awaitW }))
  /-- Byzantine WCC-call driver (deviation D11). -/
  | callWByz (q : CoreNode P.n) (r : ℕ) (hF : j ∈ q.F) :
      CoreProcStep P j q (Sum.inl (.callW r j)) (PMF.pure q)
  /-- A WCC call of another process: not `j`'s business. -/
  | callWIdle (q : CoreNode P.n) (r : ℕ) (id : Fin P.n) (hid : id ≠ j) :
      CoreProcStep P j q (Sum.inl (.callW r id)) (PMF.pure q)
  /-- `c ← WCC_r()`, the return half, together with `if b = ⊥ then b ← c`,
  `elif g = A then multicast ⟨DECIDED, b⟩` and `r ← r + 1` (deviation D10). The
  multicast writes `j`'s own pool. -/
  | retW (q : CoreNode P.n) (r : ℕ) (c : Bool) (hph : q.proc.phase = .awaitW)
      (hr : q.proc.round = r) :
      CoreProcStep P j q (Sum.inl (.retW r j c)) (PMF.pure (q.stepRound c))
  /-- Byzantine WCC-return driver (deviation D11). -/
  | retWByz (q : CoreNode P.n) (r : ℕ) (c : Bool) (hF : j ∈ q.F) :
      CoreProcStep P j q (Sum.inl (.retW r j c)) (PMF.pure q)
  /-- A WCC return to another process: not `j`'s business. -/
  | retWIdle (q : CoreNode P.n) (r : ℕ) (id : Fin P.n) (c : Bool) (hid : id ≠ j) :
      CoreProcStep P j q (Sum.inl (.retW r id c)) (PMF.pure q)
  /-- Corruption (deviation D1): a broadcast every process answers, updating its
  own copy of the corrupted set. -/
  | fail (q : CoreNode P.n) (id : Fin P.n) :
      CoreProcStep P j q (Sum.inl (.fail id)) (PMF.pure (q.corrupt P id))
  /-- `upon ⟨DECIDED, b⟩ from f + 1 senders, not having multicast: multicast
  ⟨DECIDED, b⟩`. Payload-specific, as in the monolithic rule: a pool holding the
  other bit does not block the echo of `b`. -/
  | echo (q : CoreNode P.n) (b : Bool) (hcnt : P.f + 1 ≤ q.decidedCount b)
      (hs : b ∉ q.decOut) :
      CoreProcStep P j q (Sum.inl .tau) (PMF.pure (q.sendDec b))
  /-- Byzantine DECIDED injection (deviation D12′): once corrupted, `j` may
  insert either bit into its own pool at any time, and so equivocate. -/
  | byzDecided (q : CoreNode P.n) (b : Bool) (hF : j ∈ q.F) :
      CoreProcStep P j q (Sum.inl .tau) (PMF.pure (q.sendDec b))
  /-- Gossip, sender and receiver in one process: `j` delivers its own
  `⟨DECIDED, b⟩` to itself. Both halves of the monolithic `deliver` guard are
  `j`'s own fields here. -/
  | netSelf (q : CoreNode P.n) (b : Bool) (hs : b ∈ q.decOut) (hr : b ∉ q.decIn j) :
      CoreProcStep P j q (Sum.inr (.net j j b)) (PMF.pure (q.recvDec j b))
  /-- Gossip, sender half: `j`'s `⟨DECIDED, b⟩` reaches some other receiver.
  `j` contributes the soundness guard `b ∈ decOut` and does not move. -/
  | netSend (q : CoreNode P.n) (i : Fin P.n) (b : Bool) (hi : i ≠ j)
      (hs : b ∈ q.decOut) :
      CoreProcStep P j q (Sum.inr (.net i j b)) (PMF.pure q)
  /-- Gossip, receiver half: `j` receives `⟨DECIDED, b⟩` from another sender
  `k`. `j` contributes the freshness guard and performs the write. -/
  | netRecv (q : CoreNode P.n) (k : Fin P.n) (b : Bool) (hk : k ≠ j)
      (hr : b ∉ q.decIn k) :
      CoreProcStep P j q (Sum.inr (.net j k b)) (PMF.pure (q.recvDec k b))
  /-- Gossip between two other processes: not `j`'s business. -/
  | netIdle (q : CoreNode P.n) (i k : Fin P.n) (b : Bool) (hi : i ≠ j) (hk : k ≠ j) :
      CoreProcStep P j q (Sum.inr (.net i k b)) (PMF.pure q)

/-- The automaton of core process `j`, over the extended alphabet. -/
noncomputable def CoreProc (P : Params) (j : Fin P.n) :
    System (CoreNode P.n) (CoreLab P.n) where
  init := CoreNode.initial P.n
  step := CoreProcStep P j

@[simp] theorem CoreProc_init (P : Params) (j : Fin P.n) :
    (CoreProc P j).init = CoreNode.initial P.n := rfl

@[simp] theorem CoreProc_step (P : Params) (j : Fin P.n) (q : CoreNode P.n)
    (l : CoreLab P.n) (μ : PMF (CoreNode P.n)) :
    (CoreProc P j).step q l μ ↔ CoreProcStep P j q l μ := Iff.rfl

/-- Every transition of one process is Dirac. -/
theorem CoreProc_isLTS (P : Params) (j : Fin P.n) : (CoreProc P j).IsLTS := by
  rintro q l μ hstep
  cases hstep <;> exact ⟨_, rfl⟩

/-! ### Step inversion, by label class

Two readings of each label class: what the process that owns the label may do,
and what a process that does not own it may do — namely nothing but idle. The
second family is what makes the product's behaviour on a label the owner's
behaviour. -/

section Inversion

variable {P : Params} {j : Fin P.n} {q : CoreNode P.n} {μ : PMF (CoreNode P.n)}

theorem coreProcStep_callABA_own {b : Bool}
    (h : CoreProcStep P j q (Sum.inl (.callABA j b)) μ) :
    (q.proc.input = none ∧
      μ = PMF.pure (q.setProc { q.proc with
        input := some b, est := some b, round := 0, phase := .toCallG })) ∨
    μ = PMF.pure q := by
  cases h
  case input hin => exact Or.inl ⟨hin, rfl⟩
  case inputLoop => exact Or.inr rfl
  case callABAIdle hid => exact absurd rfl hid

theorem coreProcStep_callABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : CoreProcStep P j q (Sum.inl (.callABA id b)) μ) : μ = PMF.pure q := by
  cases h
  case input => exact absurd rfl hid
  case inputLoop => exact absurd rfl hid
  case callABAIdle => rfl

theorem coreProcStep_retABA_own {b : Bool}
    (h : CoreProcStep P j q (Sum.inl (.retABA j b)) μ) :
    P.n - P.f ≤ q.decidedCount b ∧ b ∈ q.decOut ∧ q.proc.returned = false ∧
      μ = PMF.pure (q.setProc { q.proc with returned := true }) := by
  cases h
  case ret => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case retABAIdle hid => exact absurd rfl hid

theorem coreProcStep_retABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : CoreProcStep P j q (Sum.inl (.retABA id b)) μ) : μ = PMF.pure q := by
  cases h
  case ret => exact absurd rfl hid
  case retABAIdle => rfl

theorem coreProcStep_callG_own {r : ℕ} {b : Bool}
    (h : CoreProcStep P j q (Sum.inl (.callG r j b)) μ) :
    (q.proc.phase = .toCallG ∧ q.proc.round = r ∧ q.proc.est = some b ∧
      μ = PMF.pure (q.setProc { q.proc with phase := .awaitG })) ∨
    (j ∈ q.F ∧ μ = PMF.pure q) := by
  cases h
  case callG hph hr hest => exact Or.inl ⟨hph, hr, hest, rfl⟩
  case callGByz hF => exact Or.inr ⟨hF, rfl⟩
  case callGIdle hid => exact absurd rfl hid

theorem coreProcStep_callG_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : CoreProcStep P j q (Sum.inl (.callG r id b)) μ) : μ = PMF.pure q := by
  cases h
  case callG => exact absurd rfl hid
  case callGByz => exact absurd rfl hid
  case callGIdle => rfl

theorem coreProcStep_retG_own {r : ℕ} {out : GbcaOut}
    (h : CoreProcStep P j q (Sum.inl (.retG r j out)) μ) :
    (q.proc.phase = .awaitG ∧ q.proc.round = r ∧
      μ = PMF.pure (q.setProc { q.proc with
        est := out.est, lastGrade := some out, phase := .toCallW })) ∨
    (j ∈ q.F ∧ μ = PMF.pure q) := by
  cases h
  case retG hph hr => exact Or.inl ⟨hph, hr, rfl⟩
  case retGByz hF => exact Or.inr ⟨hF, rfl⟩
  case retGIdle hid => exact absurd rfl hid

theorem coreProcStep_retG_foreign {r : ℕ} {id : Fin P.n} {out : GbcaOut} (hid : id ≠ j)
    (h : CoreProcStep P j q (Sum.inl (.retG r id out)) μ) : μ = PMF.pure q := by
  cases h
  case retG => exact absurd rfl hid
  case retGByz => exact absurd rfl hid
  case retGIdle => rfl

theorem coreProcStep_callW_own {r : ℕ}
    (h : CoreProcStep P j q (Sum.inl (.callW r j)) μ) :
    (q.proc.phase = .toCallW ∧ q.proc.round = r ∧
      μ = PMF.pure (q.setProc { q.proc with phase := .awaitW })) ∨
    (j ∈ q.F ∧ μ = PMF.pure q) := by
  cases h
  case callW hph hr => exact Or.inl ⟨hph, hr, rfl⟩
  case callWByz hF => exact Or.inr ⟨hF, rfl⟩
  case callWIdle hid => exact absurd rfl hid

theorem coreProcStep_callW_foreign {r : ℕ} {id : Fin P.n} (hid : id ≠ j)
    (h : CoreProcStep P j q (Sum.inl (.callW r id)) μ) : μ = PMF.pure q := by
  cases h
  case callW => exact absurd rfl hid
  case callWByz => exact absurd rfl hid
  case callWIdle => rfl

theorem coreProcStep_retW_own {r : ℕ} {c : Bool}
    (h : CoreProcStep P j q (Sum.inl (.retW r j c)) μ) :
    (q.proc.phase = .awaitW ∧ q.proc.round = r ∧ μ = PMF.pure (q.stepRound c)) ∨
    (j ∈ q.F ∧ μ = PMF.pure q) := by
  cases h
  case retW hph hr => exact Or.inl ⟨hph, hr, rfl⟩
  case retWByz hF => exact Or.inr ⟨hF, rfl⟩
  case retWIdle hid => exact absurd rfl hid

theorem coreProcStep_retW_foreign {r : ℕ} {id : Fin P.n} {c : Bool} (hid : id ≠ j)
    (h : CoreProcStep P j q (Sum.inl (.retW r id c)) μ) : μ = PMF.pure q := by
  cases h
  case retW => exact absurd rfl hid
  case retWByz => exact absurd rfl hid
  case retWIdle => rfl

theorem coreProcStep_fail_inv {id : Fin P.n}
    (h : CoreProcStep P j q (Sum.inl (.fail id)) μ) : μ = PMF.pure (q.corrupt P id) := by
  cases h
  rfl

theorem coreProcStep_tau_inv (h : CoreProcStep P j q (Sum.inl .tau) μ) :
    (∃ b, P.f + 1 ≤ q.decidedCount b ∧ b ∉ q.decOut ∧ μ = PMF.pure (q.sendDec b)) ∨
    (∃ b, j ∈ q.F ∧ μ = PMF.pure (q.sendDec b)) := by
  cases h
  case echo b hcnt hs => exact Or.inl ⟨b, hcnt, hs, rfl⟩
  case byzDecided b hF => exact Or.inr ⟨b, hF, rfl⟩

theorem coreProcStep_netSelf_inv {b : Bool}
    (h : CoreProcStep P j q (Sum.inr (.net j j b)) μ) :
    b ∈ q.decOut ∧ b ∉ q.decIn j ∧ μ = PMF.pure (q.recvDec j b) := by
  cases h
  case netSelf hs hr => exact ⟨hs, hr, rfl⟩
  case netSend hi _ => exact absurd rfl hi
  case netRecv hk _ => exact absurd rfl hk
  case netIdle hi _ => exact absurd rfl hi

theorem coreProcStep_netSend_inv {i : Fin P.n} {b : Bool} (hi : i ≠ j)
    (h : CoreProcStep P j q (Sum.inr (.net i j b)) μ) :
    b ∈ q.decOut ∧ μ = PMF.pure q := by
  cases h
  case netSelf => exact absurd rfl hi
  case netSend hs => exact ⟨hs, rfl⟩
  case netRecv hk _ => exact absurd rfl hk
  case netIdle hk => exact absurd rfl hk

theorem coreProcStep_netRecv_inv {k : Fin P.n} {b : Bool} (hk : k ≠ j)
    (h : CoreProcStep P j q (Sum.inr (.net j k b)) μ) :
    b ∉ q.decIn k ∧ μ = PMF.pure (q.recvDec k b) := by
  cases h
  case netSelf => exact absurd rfl hk
  case netSend hi _ => exact absurd rfl hi
  case netRecv hr => exact ⟨hr, rfl⟩
  case netIdle hi _ => exact absurd rfl hi

theorem coreProcStep_netIdle_inv {i k : Fin P.n} {b : Bool} (hi : i ≠ j) (hk : k ≠ j)
    (h : CoreProcStep P j q (Sum.inr (.net i k b)) μ) : μ = PMF.pure q := by
  cases h
  case netSelf => exact absurd rfl hi
  case netSend => exact absurd rfl hk
  case netRecv => exact absurd rfl hi
  case netIdle => rfl

end Inversion

/-! ### The composition -/

/-- The gossip labels, hidden by the composition. -/
def gossipLabels (n : ℕ) : Set (CoreLab n) := {l | ∃ i j b, l = Sum.inr (DNet.net i j b)}

/-- **The per-process core.** The processes are composed under full
synchronisation, the gossip labels are hidden, and the result is read back over
the shared alphabet `Lab n`. -/
noncomputable def perProcCore (P : Params) :
    System (∀ _ : Fin P.n, CoreNode P.n) (Lab P.n) :=
  ((System.syncProduct (CoreProc P)).abstract (gossipLabels P.n)).relabel

/-! ### The packing relation -/

/-- The packing relation between a tuple of process states and a monolithic core
state: the control records, the DECIDED pools and the receipt rows are the same
data read two ways, and every process's copy of the corrupted set is the
monolithic one. -/
structure CoreRel (P : Params) (q : ∀ _ : Fin P.n, CoreNode P.n)
    (s : CoreState P.n) : Prop where
  /-- Control records. -/
  proc_eq : ∀ k, (q k).proc = s.procs k
  /-- Own DECIDED pools. -/
  out_eq : ∀ k, (q k).decOut = s.decidedSent k
  /-- Receipt rows, indexed by receiver then sender. -/
  in_eq : ∀ i k, (q i).decIn k = s.decidedRecv i k
  /-- Every copy of the corrupted set agrees with the monolithic one. -/
  F_eq : ∀ k, (q k).F = s.F

/-! ### Reading the composite step relation

Abstraction discards no state and only relabels transitions, so it preserves
`System.IsLTS`, by the argument `System.relabel_isLTS` makes for restriction.
-/

theorem perProcCore_isLTS (P : Params) : (perProcCore P).IsLTS :=
  System.relabel_isLTS
    (System.abstract_isLTS (System.syncProduct_isLTS (CoreProc_isLTS P)) _)

/-- **The composite step relation.** A transition of `perProcCore` on `l` is
either a hidden gossip rendezvous (only at `l = τ`) or a synchronised transition
on `Sum.inl l`. -/
theorem perProcCore_step_iff (P : Params) (q : ∀ _ : Fin P.n, CoreNode P.n)
    (l : Lab P.n) (μ : PMF (∀ _ : Fin P.n, CoreNode P.n)) :
    (perProcCore P).step q l μ ↔
      (l = .tau ∧ ∃ i k b,
        (System.syncProduct (CoreProc P)).step q (Sum.inr (DNet.net i k b)) μ) ∨
      (System.syncProduct (CoreProc P)).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨i, k, b, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, i, k, b, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, i, k, b, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, ⟨i, k, b, rfl⟩, hstep⟩
    · exact Or.inr ⟨by simp [gossipLabels], hstep⟩

/-- A synchronised transition on a visible label: every process steps on it. -/
theorem sync_visible_iff (P : Params) (q : ∀ _ : Fin P.n, CoreNode P.n)
    (l : CoreLab P.n) (hl : l ≠ Sum.inl .tau) (μ : PMF (∀ _ : Fin P.n, CoreNode P.n)) :
    (System.syncProduct (CoreProc P)).step q l μ ↔
      ∃ μ_ : Fin P.n → PMF (CoreNode P.n),
        (∀ m, CoreProcStep P m (q m) l (μ_ m)) ∧ μ = piPMF μ_ := by
  constructor
  · rintro (⟨-, μ_, hall, rfl⟩ | ⟨hτ, -⟩)
    · exact ⟨μ_, hall, rfl⟩
    · exact absurd hτ hl
  · rintro ⟨μ_, hall, rfl⟩
    exact Or.inl ⟨hl, μ_, hall, rfl⟩

/-- A synchronised transition on a label of the shared alphabet other than `τ`. -/
theorem sync_inl_iff (P : Params) (q : ∀ _ : Fin P.n, CoreNode P.n) (l : Lab P.n)
    (hl : l ≠ .tau) (μ : PMF (∀ _ : Fin P.n, CoreNode P.n)) :
    (System.syncProduct (CoreProc P)).step q (Sum.inl l) μ ↔
      ∃ μ_ : Fin P.n → PMF (CoreNode P.n),
        (∀ m, CoreProcStep P m (q m) (Sum.inl l) (μ_ m)) ∧ μ = piPMF μ_ :=
  sync_visible_iff P q (Sum.inl l) (by simpa using hl) μ

/-- A synchronised transition on the silent label: exactly one process steps and
the others hold their state. -/
theorem sync_tau_iff (P : Params) (q : ∀ _ : Fin P.n, CoreNode P.n)
    (μ : PMF (∀ _ : Fin P.n, CoreNode P.n)) :
    (System.syncProduct (CoreProc P)).step q (Sum.inl .tau) μ ↔
      ∃ (m : Fin P.n) (ν : PMF (CoreNode P.n)),
        CoreProcStep P m (q m) (Sum.inl .tau) ν ∧
        μ = piPMF (Function.update (fun k => PMF.pure (q k)) m ν) := by
  constructor
  · rintro (⟨hτ, -⟩ | ⟨-, m, ν, hstep, rfl⟩)
    · exact absurd rfl hτ
    · exact ⟨m, ν, hstep, rfl⟩
  · rintro ⟨m, ν, hstep, rfl⟩
    exact Or.inr ⟨rfl, m, ν, hstep, rfl⟩

/-! ### Products of Diracs -/

/-- A family of Diracs multiplies to the Dirac on the tuple of their points. -/
private theorem piPMF_eq_pure {P : Params} {μ_ : Fin P.n → PMF (CoreNode P.n)}
    {x : ∀ _ : Fin P.n, CoreNode P.n} (h : ∀ m, μ_ m = PMF.pure (x m)) :
    piPMF μ_ = PMF.pure x := by
  rw [funext h]
  exact piPMF_pure x

/-- The one-mover case: process `i` lands on `y` and every other process holds
its state. -/
private theorem piPMF_eq_pure_update {P : Params} {μ_ : Fin P.n → PMF (CoreNode P.n)}
    (q : ∀ _ : Fin P.n, CoreNode P.n) (i : Fin P.n) (y : CoreNode P.n)
    (hi : μ_ i = PMF.pure y) (hoth : ∀ m, m ≠ i → μ_ m = PMF.pure (q m)) :
    piPMF μ_ = PMF.pure (Function.update q i y) := by
  refine piPMF_eq_pure (fun m => ?_)
  by_cases hm : m = i
  · subst hm; rw [hi, Function.update_self]
  · rw [hoth m hm, Function.update_of_ne hm]

/-- The silent-interleaving distribution of a Dirac mover. -/
private theorem piPMF_update_eq_pure {P : Params} (q : ∀ _ : Fin P.n, CoreNode P.n)
    (i : Fin P.n) (y : CoreNode P.n) :
    piPMF (Function.update (fun k => PMF.pure (q k)) i (PMF.pure y))
      = PMF.pure (Function.update q i y) := by
  rw [piPMF_update_pure, PMF.pure_map]

/-! ### Building composite transitions -/

/-- A visible transition of the composite: every process steps on `Sum.inl l`. -/
private theorem perProcCore_visible_step (P : Params) (q : ∀ _ : Fin P.n, CoreNode P.n)
    (l : Lab P.n) (hl : l ≠ .tau) (x : ∀ _ : Fin P.n, CoreNode P.n)
    (hall : ∀ m, CoreProcStep P m (q m) (Sum.inl l) (PMF.pure (x m))) :
    (perProcCore P).step q l (PMF.pure x) := by
  refine (perProcCore_step_iff P q l _).mpr (Or.inr ?_)
  refine (sync_visible_iff P q (Sum.inl l) (fun h => hl (Sum.inl_injective h)) _).mpr
    ⟨fun m => PMF.pure (x m), hall, (piPMF_eq_pure (fun _ => rfl)).symm⟩

/-- A silent transition of the composite by one process's own `τ`-rule. -/
private theorem perProcCore_tau_step (P : Params) (q : ∀ _ : Fin P.n, CoreNode P.n)
    (i : Fin P.n) (y : CoreNode P.n)
    (h : CoreProcStep P i (q i) (Sum.inl .tau) (PMF.pure y)) :
    (perProcCore P).step q .tau (PMF.pure (Function.update q i y)) := by
  refine (perProcCore_step_iff P q .tau _).mpr (Or.inr ?_)
  exact (sync_tau_iff P q _).mpr ⟨i, PMF.pure y, h, (piPMF_update_eq_pure q i y).symm⟩

/-- A hidden gossip rendezvous of the composite, which the shared alphabet sees
as a `τ`-transition. -/
private theorem perProcCore_gossip_step (P : Params) (q : ∀ _ : Fin P.n, CoreNode P.n)
    (i k : Fin P.n) (b : Bool) (x : ∀ _ : Fin P.n, CoreNode P.n)
    (hall : ∀ m, CoreProcStep P m (q m) (Sum.inr (DNet.net i k b)) (PMF.pure (x m))) :
    (perProcCore P).step q .tau (PMF.pure x) := by
  refine (perProcCore_step_iff P q .tau _).mpr (Or.inl ⟨rfl, i, k, b, ?_⟩)
  refine (sync_visible_iff P q (Sum.inr (DNet.net i k b)) (by simp) _).mpr
    ⟨fun m => PMF.pure (x m), hall, (piPMF_eq_pure (fun _ => rfl)).symm⟩

/-! ### The packing relation, rule by rule -/

section Packing

variable {P : Params} {q : ∀ _ : Fin P.n, CoreNode P.n} {s : CoreState P.n}

/-- Packed receipt rows have packed sender counts. -/
theorem CoreRel.decidedCount_eq (hR : CoreRel P q s) (i : Fin P.n) (b : Bool) :
    (q i).decidedCount b = s.decidedCount i b := by
  unfold CoreNode.decidedCount CoreState.decidedCount
  congr 1
  ext k
  simp only [Finset.mem_filter, hR.in_eq i k]

/-- A control-record write at one process. -/
theorem CoreRel.setProc (hR : CoreRel P q s) (id : Fin P.n) (p : ProcCore P.n) :
    CoreRel P (Function.update q id ((q id).setProc p)) (s.setProc id p) := by
  refine ⟨fun m => ?_, fun m => ?_, fun i k => ?_, fun m => ?_⟩
  · by_cases hm : m = id
    · subst hm; rw [Function.update_self, CoreNode.setProc_proc, CoreState.setProc_procs_self]
    · rw [Function.update_of_ne hm, CoreState.setProc_procs_ne _ _ _ hm]; exact hR.proc_eq m
  · rw [CoreState.setProc_decidedSent]
    by_cases hm : m = id
    · subst hm; rw [Function.update_self, CoreNode.setProc_decOut]; exact hR.out_eq m
    · rw [Function.update_of_ne hm]; exact hR.out_eq m
  · rw [CoreState.setProc_decidedRecv]
    by_cases hi : i = id
    · subst hi; rw [Function.update_self, CoreNode.setProc_decIn]; exact hR.in_eq i k
    · rw [Function.update_of_ne hi]; exact hR.in_eq i k
  · rw [CoreState.setProc_F]
    by_cases hm : m = id
    · subst hm; rw [Function.update_self, CoreNode.setProc_F]; exact hR.F_eq m
    · rw [Function.update_of_ne hm]; exact hR.F_eq m

/-- A DECIDED multicast at one process. -/
theorem CoreRel.sendDec (hR : CoreRel P q s) (id : Fin P.n) (b : Bool) :
    CoreRel P (Function.update q id ((q id).sendDec b)) (s.sendDecided id b) := by
  refine ⟨fun m => ?_, fun m => ?_, fun i k => ?_, fun m => ?_⟩
  · by_cases hm : m = id
    · subst hm; rw [Function.update_self, CoreNode.sendDec_proc, CoreState.sendDecided_procs]
      exact hR.proc_eq m
    · rw [Function.update_of_ne hm, CoreState.sendDecided_procs]; exact hR.proc_eq m
  · rw [CoreState.sendDecided_decidedSent]
    by_cases hm : m = id
    · subst hm
      rw [Function.update_self, Function.update_self, CoreNode.sendDec_decOut, hR.out_eq m]
    · rw [Function.update_of_ne hm, Function.update_of_ne hm]; exact hR.out_eq m
  · rw [CoreState.sendDecided_decidedRecv]
    by_cases hi : i = id
    · subst hi; rw [Function.update_self, CoreNode.sendDec_decIn]; exact hR.in_eq i k
    · rw [Function.update_of_ne hi]; exact hR.in_eq i k
  · rw [CoreState.sendDecided_F]
    by_cases hm : m = id
    · subst hm; rw [Function.update_self, CoreNode.sendDec_F]; exact hR.F_eq m
    · rw [Function.update_of_ne hm]; exact hR.F_eq m

/-- A DECIDED delivery at one receiver. -/
theorem CoreRel.recvDec (hR : CoreRel P q s) (i k : Fin P.n) (b : Bool) :
    CoreRel P (Function.update q i ((q i).recvDec k b)) (s.deliverDecided i k b) := by
  refine ⟨fun m => ?_, fun m => ?_, fun i' k' => ?_, fun m => ?_⟩
  · rw [CoreState.deliverDecided_procs]
    by_cases hm : m = i
    · subst hm; rw [Function.update_self, CoreNode.recvDec_proc]; exact hR.proc_eq m
    · rw [Function.update_of_ne hm]; exact hR.proc_eq m
  · rw [CoreState.deliverDecided_decidedSent]
    by_cases hm : m = i
    · subst hm; rw [Function.update_self, CoreNode.recvDec_decOut]; exact hR.out_eq m
    · rw [Function.update_of_ne hm]; exact hR.out_eq m
  · by_cases hi : i' = i
    · subst hi
      rw [Function.update_self]
      by_cases hk : k' = k
      · subst hk
        rw [CoreNode.recvDec_decIn_self, CoreState.deliverDecided_decidedRecv_self,
          hR.in_eq i' k']
      · rw [CoreNode.recvDec_decIn_of_ne _ _ _ hk,
          CoreState.deliverDecided_decidedRecv_of_ne _ _ _ _ (Or.inr hk)]
        exact hR.in_eq i' k'
    · rw [Function.update_of_ne hi,
        CoreState.deliverDecided_decidedRecv_of_ne _ _ _ _ (Or.inl hi)]
      exact hR.in_eq i' k'
  · rw [CoreState.deliverDecided_F]
    by_cases hm : m = i
    · subst hm; rw [Function.update_self, CoreNode.recvDec_F]; exact hR.F_eq m
    · rw [Function.update_of_ne hm]; exact hR.F_eq m

/-- The fused round advance at one process (deviation D10). -/
theorem CoreRel.stepRound (hR : CoreRel P q s) (id : Fin P.n) (c : Bool) :
    CoreRel P (Function.update q id ((q id).stepRound c)) (s.stepRound id c) := by
  refine ⟨fun m => ?_, fun m => ?_, fun i k => ?_, fun m => ?_⟩
  · by_cases hm : m = id
    · subst hm
      rw [Function.update_self, CoreNode.stepRound_proc, CoreState.stepRound_procs_self,
        hR.proc_eq m]
    · rw [Function.update_of_ne hm, CoreState.stepRound_procs_ne _ _ _ hm]; exact hR.proc_eq m
  · by_cases hm : m = id
    · subst hm
      rw [Function.update_self]
      cases hg : (q m).proc.lastGrade with
      | none =>
        rw [CoreNode.stepRound_decOut_of_not_A _ _ (by rw [hg]; exact fun b => by simp),
          CoreState.stepRound_decidedSent_of_not_A _ _ _
            (by rw [← hR.proc_eq m, hg]; exact fun b => by simp)]
        exact hR.out_eq m
      | some out =>
        cases out with
        | A b =>
          rw [CoreNode.stepRound_decOut_of_A _ _ _ hg,
            CoreState.stepRound_decidedSent_of_A _ _ _ _ (by rw [← hR.proc_eq m]; exact hg),
            Function.update_self, hR.out_eq m]
        | B b =>
          rw [CoreNode.stepRound_decOut_of_not_A _ _ (by rw [hg]; exact fun b => by simp),
            CoreState.stepRound_decidedSent_of_not_A _ _ _
              (by rw [← hR.proc_eq m, hg]; exact fun b => by simp)]
          exact hR.out_eq m
        | C =>
          rw [CoreNode.stepRound_decOut_of_not_A _ _ (by rw [hg]; exact fun b => by simp),
            CoreState.stepRound_decidedSent_of_not_A _ _ _
              (by rw [← hR.proc_eq m, hg]; exact fun b => by simp)]
          exact hR.out_eq m
    · rw [Function.update_of_ne hm]
      cases hg : (q id).proc.lastGrade with
      | none =>
        rw [CoreState.stepRound_decidedSent_of_not_A _ _ _
          (by rw [← hR.proc_eq id, hg]; exact fun b => by simp)]
        exact hR.out_eq m
      | some out =>
        cases out with
        | A b =>
          rw [CoreState.stepRound_decidedSent_of_A _ _ _ _ (by rw [← hR.proc_eq id]; exact hg),
            Function.update_of_ne hm]
          exact hR.out_eq m
        | B b =>
          rw [CoreState.stepRound_decidedSent_of_not_A _ _ _
            (by rw [← hR.proc_eq id, hg]; exact fun b => by simp)]
          exact hR.out_eq m
        | C =>
          rw [CoreState.stepRound_decidedSent_of_not_A _ _ _
            (by rw [← hR.proc_eq id, hg]; exact fun b => by simp)]
          exact hR.out_eq m
  · rw [CoreState.stepRound_decidedRecv]
    by_cases hi : i = id
    · subst hi; rw [Function.update_self, CoreNode.stepRound_decIn]; exact hR.in_eq i k
    · rw [Function.update_of_ne hi]; exact hR.in_eq i k
  · rw [CoreState.stepRound_F]
    by_cases hm : m = id
    · subst hm; rw [Function.update_self, CoreNode.stepRound_F]; exact hR.F_eq m
    · rw [Function.update_of_ne hm]; exact hR.F_eq m

/-- The corruption broadcast: every copy of the corrupted set is updated under
the same guard, so the copies stay in lockstep. -/
theorem CoreRel.corrupt (hR : CoreRel P q s) (id : Fin P.n) :
    CoreRel P (fun m => (q m).corrupt P id) (s.corrupt P id) := by
  have hguard : ∀ m, (id ∉ (q m).F ∧ ((q m).F).card < P.f) ↔ (id ∉ s.F ∧ s.F.card < P.f) :=
    fun m => by rw [hR.F_eq m]
  refine ⟨fun m => ?_, fun m => ?_, fun i k => ?_, fun m => ?_⟩
  · rw [CoreNode.corrupt_proc, CoreState.corrupt_procs]; exact hR.proc_eq m
  · rw [CoreNode.corrupt_decOut, CoreState.corrupt_decidedSent]; exact hR.out_eq m
  · rw [CoreNode.corrupt_decIn, CoreState.corrupt_decidedRecv]; exact hR.in_eq i k
  · unfold CoreNode.corrupt CoreState.corrupt
    by_cases hc : id ∉ s.F ∧ s.F.card < P.f
    · rw [if_pos ((hguard m).mpr hc), if_pos hc]
      exact congrArg (insert id) (hR.F_eq m)
    · rw [if_neg (fun h => hc ((hguard m).mp h)), if_neg hc]
      exact hR.F_eq m

end Packing

/-! ### The equivalence -/

theorem coreRel_init (P : Params) : CoreRel P (perProcCore P).init (core P).init :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- **The composite refines the core.** Every transition of the per-process
composition is a transition of `ABA.core` on the same label: the process that
owns the label supplies the monolithic rule's guard on its own fields, and the
gossip rendezvous supplies the two halves of `CoreStep.deliver`'s guard. -/
theorem perProcCore_sim (P : Params) :
    ForwardSimulation (perProcCore P) (core P) (CoreRel P) := by
  constructor
  intro q s hR l μ hstep q' hq'
  rw [perProcCore_step_iff] at hstep
  rcases hstep with ⟨rfl, i, k, b, hsync⟩ | hsync
  · -- Hidden gossip rendezvous ↔ `CoreStep.deliver`.
    rw [sync_visible_iff P q (Sum.inr (DNet.net i k b)) (by simp)] at hsync
    obtain ⟨μ_, hall, rfl⟩ := hsync
    have key : b ∈ (q k).decOut ∧ b ∉ (q i).decIn k ∧
        μ_ i = PMF.pure ((q i).recvDec k b) ∧ ∀ m, m ≠ i → μ_ m = PMF.pure (q m) := by
      by_cases hik : i = k
      · subst hik
        obtain ⟨hs, hr, hμ⟩ := coreProcStep_netSelf_inv (hall i)
        exact ⟨hs, hr, hμ, fun m hm =>
          coreProcStep_netIdle_inv (Ne.symm hm) (Ne.symm hm) (hall m)⟩
      · obtain ⟨hr, hμi⟩ := coreProcStep_netRecv_inv (Ne.symm hik) (hall i)
        obtain ⟨hs, hμk⟩ := coreProcStep_netSend_inv hik (hall k)
        refine ⟨hs, hr, hμi, fun m hm => ?_⟩
        by_cases hmk : m = k
        · subst hmk; exact hμk
        · exact coreProcStep_netIdle_inv (Ne.symm hm) (Ne.symm hmk) (hall m)
    obtain ⟨hs, hr, hμi, hoth⟩ := key
    rw [piPMF_eq_pure_update q i _ hμi hoth, PMF.mem_support_pure_iff] at hq'
    subst hq'
    exact ⟨s.deliverDecided i k b,
      Or.inl ⟨rfl, System.weakLSilent_of_step (CoreStep.deliver s i k b
        (by rw [← hR.out_eq k]; exact hs) (by rw [← hR.in_eq i k]; exact hr))⟩,
      hR.recvDec i k b⟩
  · cases l with
    | tau =>
      -- Interleaved `τ`: one process's own `echo` or `byzDecided`.
      rw [sync_tau_iff] at hsync
      obtain ⟨m, ν, hstepm, rfl⟩ := hsync
      rcases coreProcStep_tau_inv hstepm with ⟨b, hcnt, hs, rfl⟩ | ⟨b, hF, rfl⟩
      · rw [piPMF_update_eq_pure, PMF.mem_support_pure_iff] at hq'
        subst hq'
        exact ⟨s.sendDecided m b,
          Or.inl ⟨rfl, System.weakLSilent_of_step (CoreStep.echo s m b
            (by rw [← hR.decidedCount_eq m b]; exact hcnt)
            (by rw [← hR.out_eq m]; exact hs))⟩, hR.sendDec m b⟩
      · rw [piPMF_update_eq_pure, PMF.mem_support_pure_iff] at hq'
        subst hq'
        exact ⟨s.sendDecided m b,
          Or.inl ⟨rfl, System.weakLSilent_of_step (CoreStep.byzDecided s m b
            (by rw [← hR.F_eq m]; exact hF))⟩, hR.sendDec m b⟩
    | callABA id b =>
      rw [sync_inl_iff P q (Lab.callABA id b) (by simp)] at hsync
      obtain ⟨μ_, hall, rfl⟩ := hsync
      have hoth : ∀ m, m ≠ id → μ_ m = PMF.pure (q m) :=
        fun m hm => coreProcStep_callABA_foreign (Ne.symm hm) (hall m)
      rcases coreProcStep_callABA_own (hall id) with ⟨hin, hμ⟩ | hμ
      · rw [piPMF_eq_pure_update q id _ hμ hoth, PMF.mem_support_pure_iff] at hq'
        subst hq'
        refine ⟨s.setProc id { s.procs id with
            input := some b, est := some b, round := 0, phase := .toCallG },
          Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
            (CoreStep.input s id b (by rw [← hR.proc_eq id]; exact hin))⟩, ?_⟩
        rw [← hR.proc_eq id]; exact hR.setProc id _
      · have hall' : ∀ m, μ_ m = PMF.pure (q m) := fun m => by
          by_cases hm : m = id
          · subst hm; exact hμ
          · exact hoth m hm
        rw [piPMF_eq_pure hall', PMF.mem_support_pure_iff] at hq'
        subst hq'
        exact ⟨s, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (CoreStep.inputLoop s id b)⟩, hR⟩
    | retABA id b =>
      rw [sync_inl_iff P q (Lab.retABA id b) (by simp)] at hsync
      obtain ⟨μ_, hall, rfl⟩ := hsync
      have hoth : ∀ m, m ≠ id → μ_ m = PMF.pure (q m) :=
        fun m hm => coreProcStep_retABA_foreign (Ne.symm hm) (hall m)
      obtain ⟨hcnt, hs, hret, hμ⟩ := coreProcStep_retABA_own (hall id)
      rw [piPMF_eq_pure_update q id _ hμ hoth, PMF.mem_support_pure_iff] at hq'
      subst hq'
      refine ⟨s.setProc id { s.procs id with returned := true },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (CoreStep.ret s id b (by rw [← hR.decidedCount_eq id b]; exact hcnt)
            (by rw [← hR.out_eq id]; exact hs)
            (by rw [← hR.proc_eq id]; exact hret))⟩, ?_⟩
      rw [← hR.proc_eq id]; exact hR.setProc id _
    | callG r id b =>
      rw [sync_inl_iff P q (Lab.callG r id b) (by simp)] at hsync
      obtain ⟨μ_, hall, rfl⟩ := hsync
      have hoth : ∀ m, m ≠ id → μ_ m = PMF.pure (q m) :=
        fun m hm => coreProcStep_callG_foreign (Ne.symm hm) (hall m)
      rcases coreProcStep_callG_own (hall id) with ⟨hph, hr, hest, hμ⟩ | ⟨hF, hμ⟩
      · rw [piPMF_eq_pure_update q id _ hμ hoth, PMF.mem_support_pure_iff] at hq'
        subst hq'
        refine ⟨s.setProc id { s.procs id with phase := .awaitG },
          Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
            (CoreStep.callG s r id b (by rw [← hR.proc_eq id]; exact hph)
              (by rw [← hR.proc_eq id]; exact hr)
              (by rw [← hR.proc_eq id]; exact hest))⟩, ?_⟩
        rw [← hR.proc_eq id]; exact hR.setProc id _
      · have hall' : ∀ m, μ_ m = PMF.pure (q m) := fun m => by
          by_cases hm : m = id
          · subst hm; exact hμ
          · exact hoth m hm
        rw [piPMF_eq_pure hall', PMF.mem_support_pure_iff] at hq'
        subst hq'
        exact ⟨s, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (CoreStep.callGByz s r id b (by rw [← hR.F_eq id]; exact hF))⟩, hR⟩
    | retG r id out =>
      rw [sync_inl_iff P q (Lab.retG r id out) (by simp)] at hsync
      obtain ⟨μ_, hall, rfl⟩ := hsync
      have hoth : ∀ m, m ≠ id → μ_ m = PMF.pure (q m) :=
        fun m hm => coreProcStep_retG_foreign (Ne.symm hm) (hall m)
      rcases coreProcStep_retG_own (hall id) with ⟨hph, hr, hμ⟩ | ⟨hF, hμ⟩
      · rw [piPMF_eq_pure_update q id _ hμ hoth, PMF.mem_support_pure_iff] at hq'
        subst hq'
        refine ⟨s.setProc id { s.procs id with
            est := out.est, lastGrade := some out, phase := .toCallW },
          Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
            (CoreStep.retG s r id out (by rw [← hR.proc_eq id]; exact hph)
              (by rw [← hR.proc_eq id]; exact hr))⟩, ?_⟩
        rw [← hR.proc_eq id]; exact hR.setProc id _
      · have hall' : ∀ m, μ_ m = PMF.pure (q m) := fun m => by
          by_cases hm : m = id
          · subst hm; exact hμ
          · exact hoth m hm
        rw [piPMF_eq_pure hall', PMF.mem_support_pure_iff] at hq'
        subst hq'
        exact ⟨s, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (CoreStep.retGByz s r id out (by rw [← hR.F_eq id]; exact hF))⟩, hR⟩
    | callW r id =>
      rw [sync_inl_iff P q (Lab.callW r id) (by simp)] at hsync
      obtain ⟨μ_, hall, rfl⟩ := hsync
      have hoth : ∀ m, m ≠ id → μ_ m = PMF.pure (q m) :=
        fun m hm => coreProcStep_callW_foreign (Ne.symm hm) (hall m)
      rcases coreProcStep_callW_own (hall id) with ⟨hph, hr, hμ⟩ | ⟨hF, hμ⟩
      · rw [piPMF_eq_pure_update q id _ hμ hoth, PMF.mem_support_pure_iff] at hq'
        subst hq'
        refine ⟨s.setProc id { s.procs id with phase := .awaitW },
          Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
            (CoreStep.callW s r id (by rw [← hR.proc_eq id]; exact hph)
              (by rw [← hR.proc_eq id]; exact hr))⟩, ?_⟩
        rw [← hR.proc_eq id]; exact hR.setProc id _
      · have hall' : ∀ m, μ_ m = PMF.pure (q m) := fun m => by
          by_cases hm : m = id
          · subst hm; exact hμ
          · exact hoth m hm
        rw [piPMF_eq_pure hall', PMF.mem_support_pure_iff] at hq'
        subst hq'
        exact ⟨s, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (CoreStep.callWByz s r id (by rw [← hR.F_eq id]; exact hF))⟩, hR⟩
    | retW r id c =>
      rw [sync_inl_iff P q (Lab.retW r id c) (by simp)] at hsync
      obtain ⟨μ_, hall, rfl⟩ := hsync
      have hoth : ∀ m, m ≠ id → μ_ m = PMF.pure (q m) :=
        fun m hm => coreProcStep_retW_foreign (Ne.symm hm) (hall m)
      rcases coreProcStep_retW_own (hall id) with ⟨hph, hr, hμ⟩ | ⟨hF, hμ⟩
      · rw [piPMF_eq_pure_update q id _ hμ hoth, PMF.mem_support_pure_iff] at hq'
        subst hq'
        exact ⟨s.stepRound id c,
          Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
            (CoreStep.retW s r id c (by rw [← hR.proc_eq id]; exact hph)
              (by rw [← hR.proc_eq id]; exact hr))⟩, hR.stepRound id c⟩
      · have hall' : ∀ m, μ_ m = PMF.pure (q m) := fun m => by
          by_cases hm : m = id
          · subst hm; exact hμ
          · exact hoth m hm
        rw [piPMF_eq_pure hall', PMF.mem_support_pure_iff] at hq'
        subst hq'
        exact ⟨s, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (CoreStep.retWByz s r id c (by rw [← hR.F_eq id]; exact hF))⟩, hR⟩
    | fail id =>
      rw [sync_inl_iff P q (Lab.fail id) (by simp)] at hsync
      obtain ⟨μ_, hall, rfl⟩ := hsync
      rw [piPMF_eq_pure (fun m => coreProcStep_fail_inv (hall m)),
        PMF.mem_support_pure_iff] at hq'
      subst hq'
      exact ⟨s.corrupt P id, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (CoreStep.fail s id)⟩, hR.corrupt id⟩

/-- **The core refines the composite.** Every monolithic rule is reassembled
from the owner's local rule and the idle answers of the other processes;
`CoreStep.deliver` is reassembled from the sender and receiver halves of a
gossip rendezvous. -/
theorem core_sim (P : Params) :
    ForwardSimulation (core P) (perProcCore P) (fun s q => CoreRel P q s) := by
  constructor
  intro s q hR l μ hstep s' hs'
  cases l with
  | tau =>
    rw [core_step, coreStep_tau_iff] at hstep
    rcases hstep with ⟨i, k, b, hs, hr, rfl⟩ | ⟨id, b, hcnt, hsent, rfl⟩ |
      ⟨id, b, hF, rfl⟩
    · -- `deliver` ↔ the sender and receiver halves of a gossip rendezvous.
      rw [PMF.mem_support_pure_iff] at hs'
      subst hs'
      refine ⟨Function.update q i ((q i).recvDec k b), Or.inl ⟨rfl, ?_⟩, hR.recvDec i k b⟩
      refine System.weakLSilent_of_step ?_
      refine perProcCore_gossip_step P q i k b _ (fun m => ?_)
      by_cases hmi : m = i
      · subst hmi
        rw [Function.update_self]
        by_cases hmk : m = k
        · subst hmk
          exact CoreProcStep.netSelf _ b (by rw [hR.out_eq]; exact hs)
            (by rw [hR.in_eq]; exact hr)
        · exact CoreProcStep.netRecv _ _ b (Ne.symm hmk) (by rw [hR.in_eq]; exact hr)
      · rw [Function.update_of_ne hmi]
        by_cases hmk : m = k
        · subst hmk
          exact CoreProcStep.netSend _ _ b (Ne.symm hmi) (by rw [hR.out_eq]; exact hs)
        · exact CoreProcStep.netIdle _ _ _ b (Ne.symm hmi) (Ne.symm hmk)
    · -- `echo`: one process's own silent rule, interleaved.
      rw [PMF.mem_support_pure_iff] at hs'
      subst hs'
      exact ⟨Function.update q id ((q id).sendDec b),
        Or.inl ⟨rfl, System.weakLSilent_of_step (perProcCore_tau_step P q id _
          (CoreProcStep.echo _ b (by rw [hR.decidedCount_eq]; exact hcnt)
            (by rw [hR.out_eq]; exact hsent)))⟩, hR.sendDec id b⟩
    · -- `byzDecided`: likewise.
      rw [PMF.mem_support_pure_iff] at hs'
      subst hs'
      exact ⟨Function.update q id ((q id).sendDec b),
        Or.inl ⟨rfl, System.weakLSilent_of_step (perProcCore_tau_step P q id _
          (CoreProcStep.byzDecided _ b (by rw [hR.F_eq]; exact hF)))⟩, hR.sendDec id b⟩
  | callABA id b =>
    rw [core_step, coreStep_callABA_iff] at hstep
    rcases hstep with ⟨hin, rfl⟩ | rfl
    · rw [PMF.mem_support_pure_iff] at hs'
      subst hs'
      refine ⟨Function.update q id ((q id).setProc { (q id).proc with
          input := some b, est := some b, round := 0, phase := .toCallG }), ?_, ?_⟩
      · refine Or.inr ⟨by simp, System.weakLStep_of_step (by simp) ?_⟩
        refine perProcCore_visible_step P q (Lab.callABA id b) (by simp) _ (fun m => ?_)
        by_cases hm : m = id
        · subst hm
          rw [Function.update_self]
          exact CoreProcStep.input _ b (by rw [hR.proc_eq]; exact hin)
        · rw [Function.update_of_ne hm]
          exact CoreProcStep.callABAIdle _ _ b (Ne.symm hm)
      · rw [← hR.proc_eq id]; exact hR.setProc id _
    · rw [PMF.mem_support_pure_iff] at hs'
      subst hs'
      refine ⟨q, Or.inr ⟨by simp, System.weakLStep_of_step (by simp) ?_⟩, hR⟩
      refine perProcCore_visible_step P q (Lab.callABA id b) (by simp) _ (fun m => ?_)
      by_cases hm : m = id
      · subst hm; exact CoreProcStep.inputLoop _ b
      · exact CoreProcStep.callABAIdle _ _ b (Ne.symm hm)
  | retABA id b =>
    rw [core_step, coreStep_retABA_iff] at hstep
    obtain ⟨hcnt, hsent, hret, rfl⟩ := hstep
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨Function.update q id ((q id).setProc { (q id).proc with returned := true }),
      ?_, ?_⟩
    · refine Or.inr ⟨by simp, System.weakLStep_of_step (by simp) ?_⟩
      refine perProcCore_visible_step P q (Lab.retABA id b) (by simp) _ (fun m => ?_)
      by_cases hm : m = id
      · subst hm
        rw [Function.update_self]
        exact CoreProcStep.ret _ b (by rw [hR.decidedCount_eq]; exact hcnt)
          (by rw [hR.out_eq]; exact hsent) (by rw [hR.proc_eq]; exact hret)
      · rw [Function.update_of_ne hm]
        exact CoreProcStep.retABAIdle _ _ b (Ne.symm hm)
    · rw [← hR.proc_eq id]; exact hR.setProc id _
  | callG r id b =>
    rw [core_step, coreStep_callG_iff] at hstep
    rcases hstep with ⟨hph, hrd, hest, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hs'
      subst hs'
      refine ⟨Function.update q id ((q id).setProc { (q id).proc with phase := .awaitG }),
        ?_, ?_⟩
      · refine Or.inr ⟨by simp, System.weakLStep_of_step (by simp) ?_⟩
        refine perProcCore_visible_step P q (Lab.callG r id b) (by simp) _ (fun m => ?_)
        by_cases hm : m = id
        · subst hm
          rw [Function.update_self]
          exact CoreProcStep.callG _ r b (by rw [hR.proc_eq]; exact hph)
            (by rw [hR.proc_eq]; exact hrd) (by rw [hR.proc_eq]; exact hest)
        · rw [Function.update_of_ne hm]
          exact CoreProcStep.callGIdle _ r _ b (Ne.symm hm)
      · rw [← hR.proc_eq id]; exact hR.setProc id _
    · rw [PMF.mem_support_pure_iff] at hs'
      subst hs'
      refine ⟨q, Or.inr ⟨by simp, System.weakLStep_of_step (by simp) ?_⟩, hR⟩
      refine perProcCore_visible_step P q (Lab.callG r id b) (by simp) _ (fun m => ?_)
      by_cases hm : m = id
      · subst hm; exact CoreProcStep.callGByz _ r b (by rw [hR.F_eq]; exact hF)
      · exact CoreProcStep.callGIdle _ r _ b (Ne.symm hm)
  | retG r id out =>
    rw [core_step, coreStep_retG_iff] at hstep
    rcases hstep with ⟨hph, hrd, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hs'
      subst hs'
      refine ⟨Function.update q id ((q id).setProc { (q id).proc with
          est := out.est, lastGrade := some out, phase := .toCallW }), ?_, ?_⟩
      · refine Or.inr ⟨by simp, System.weakLStep_of_step (by simp) ?_⟩
        refine perProcCore_visible_step P q (Lab.retG r id out) (by simp) _ (fun m => ?_)
        by_cases hm : m = id
        · subst hm
          rw [Function.update_self]
          exact CoreProcStep.retG _ r out (by rw [hR.proc_eq]; exact hph)
            (by rw [hR.proc_eq]; exact hrd)
        · rw [Function.update_of_ne hm]
          exact CoreProcStep.retGIdle _ r _ out (Ne.symm hm)
      · rw [← hR.proc_eq id]; exact hR.setProc id _
    · rw [PMF.mem_support_pure_iff] at hs'
      subst hs'
      refine ⟨q, Or.inr ⟨by simp, System.weakLStep_of_step (by simp) ?_⟩, hR⟩
      refine perProcCore_visible_step P q (Lab.retG r id out) (by simp) _ (fun m => ?_)
      by_cases hm : m = id
      · subst hm; exact CoreProcStep.retGByz _ r out (by rw [hR.F_eq]; exact hF)
      · exact CoreProcStep.retGIdle _ r _ out (Ne.symm hm)
  | callW r id =>
    rw [core_step, coreStep_callW_iff] at hstep
    rcases hstep with ⟨hph, hrd, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hs'
      subst hs'
      refine ⟨Function.update q id ((q id).setProc { (q id).proc with phase := .awaitW }),
        ?_, ?_⟩
      · refine Or.inr ⟨by simp, System.weakLStep_of_step (by simp) ?_⟩
        refine perProcCore_visible_step P q (Lab.callW r id) (by simp) _ (fun m => ?_)
        by_cases hm : m = id
        · subst hm
          rw [Function.update_self]
          exact CoreProcStep.callW _ r (by rw [hR.proc_eq]; exact hph)
            (by rw [hR.proc_eq]; exact hrd)
        · rw [Function.update_of_ne hm]
          exact CoreProcStep.callWIdle _ r _ (Ne.symm hm)
      · rw [← hR.proc_eq id]; exact hR.setProc id _
    · rw [PMF.mem_support_pure_iff] at hs'
      subst hs'
      refine ⟨q, Or.inr ⟨by simp, System.weakLStep_of_step (by simp) ?_⟩, hR⟩
      refine perProcCore_visible_step P q (Lab.callW r id) (by simp) _ (fun m => ?_)
      by_cases hm : m = id
      · subst hm; exact CoreProcStep.callWByz _ r (by rw [hR.F_eq]; exact hF)
      · exact CoreProcStep.callWIdle _ r _ (Ne.symm hm)
  | retW r id c =>
    rw [core_step, coreStep_retW_iff] at hstep
    rcases hstep with ⟨hph, hrd, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hs'
      subst hs'
      refine ⟨Function.update q id ((q id).stepRound c), ?_, hR.stepRound id c⟩
      refine Or.inr ⟨by simp, System.weakLStep_of_step (by simp) ?_⟩
      refine perProcCore_visible_step P q (Lab.retW r id c) (by simp) _ (fun m => ?_)
      by_cases hm : m = id
      · subst hm
        rw [Function.update_self]
        exact CoreProcStep.retW _ r c (by rw [hR.proc_eq]; exact hph)
          (by rw [hR.proc_eq]; exact hrd)
      · rw [Function.update_of_ne hm]
        exact CoreProcStep.retWIdle _ r _ c (Ne.symm hm)
    · rw [PMF.mem_support_pure_iff] at hs'
      subst hs'
      refine ⟨q, Or.inr ⟨by simp, System.weakLStep_of_step (by simp) ?_⟩, hR⟩
      refine perProcCore_visible_step P q (Lab.retW r id c) (by simp) _ (fun m => ?_)
      by_cases hm : m = id
      · subst hm; exact CoreProcStep.retWByz _ r c (by rw [hR.F_eq]; exact hF)
      · exact CoreProcStep.retWIdle _ r _ c (Ne.symm hm)
  | fail id =>
    rw [core_step, coreStep_fail_iff] at hstep
    subst hstep
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨fun m => (q m).corrupt P id,
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (perProcCore_visible_step P q (Lab.fail id) (by simp) _
          (fun m => CoreProcStep.fail _ id))⟩, hR.corrupt id⟩

/-- **The per-process presentation is the core.** The composition of the
per-process automata, with gossip hidden, achieves exactly the trace
distributions of the monolithic `ABA.core`. -/
theorem perProcCore_atd (P : Params) :
    achievableTraceDists (perProcCore P) = achievableTraceDists (core P) :=
  Set.Subset.antisymm
    (ForwardSimulation.toProbabilistic (perProcCore_isLTS P) (core_isLTS P)
      (coreRel_init P) (perProcCore_sim P)).achievableTraceDists_subset
    (ForwardSimulation.toProbabilistic (core_isLTS P) (perProcCore_isLTS P)
      (coreRel_init P) (core_sim P)).achievableTraceDists_subset

end ABA
end PLTS
