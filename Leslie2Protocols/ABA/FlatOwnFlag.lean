/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.FlatABA
import Leslie2Protocols.Framework.TraceSupport
import Leslie2.Simulation.TraceMap

/-!
# ABA with own corruption flags and a trace-level budget

The deployed reading of the flat presentation: each process carries a single
Boolean corruption flag of its own and no copy of the corrupted set, and the
adversary flips flags freely — the `fail k` broadcast raises `k`'s flag
unconditionally, with no budget guard in the state. The corruption budget
`≤ f` is instead a hypothesis on traces (`BudgetTrace`): the processes named
by the `fail` labels of the trace form a set of at most `f` ids.

`OwnFlag.ABAProcStepU P j` is `Flat.ABAProcStep P j` with exactly three
deltas: the state record carries one flag in place of the per-copy corrupted
sets, every Byzantine guard `j ∈ F` becomes `corrupted = true`, and the
`fail k` row sets `k`'s own flag (idempotently) instead of applying the
budget-guarded insert to every copy. Honest rules never read the corrupted
set, so they port verbatim modulo the record change. The assembly
`OwnFlag.ownFlagFlat` mirrors `Flat.flatHybrid` shape for shape; the coin
oracle `WCC.specFamily` is untouched and keeps its budget-guarded `corrupt`.

## The conservativity bridge

`inflate` reads an own-flag state as a guarded flat state: every protocol
field is copied, and every copy of the corrupted set — at the round loop and
at every stage of every node — becomes the one global set `flagSet u` of
currently flagged processes. A step of the own-flag system whose `fail`
labels stay within budget is matched by the guarded system along `inflate`
(`ownFlagFlatB_bridge`): honest and Byzantine rows match guard for guard, and
on a `fail k` that is either a repeat or fired with budget headroom the
guarded insert agrees with the unguarded flag write. The budgeted system
`ownFlagFlatB` packages that side condition as a step constraint, and
`achievableTraceDists_map` turns the bridge into a trace-distribution
inclusion into `Flat.flatHybrid`.

A positive-probability trace of the *unrestricted* own-flag system satisfying
`BudgetTrace P.f` is a trace of the budgeted system with the same positive
probability: every `fail` label of a witness execution appears in its trace,
so along such an execution the flag set stays inside the trace's fail set and
every `fail` step is a repeat or has budget headroom (`exec_okLabel`);
pruning the scheduler's out-of-budget emissions (`pruneSched`) then leaves
the probability of that execution unchanged.

## Headlines

* `ownFlagFlat_safe` — every positive-probability trace of `ownFlagFlat P`
  satisfying `BudgetTrace P.f` satisfies Validity and Agreement, by
  composition with `Flat.flatABA_safe`.
* `ownFlagFlat_traces` — every such trace has positive probability under an
  achievable trace distribution of `ABA.hybridImpl P`, by composition with
  `Flat.flatABA_atd`.
-/

open Stream'

namespace PLTS
namespace ABA

/-! ### The unguarded records -/

namespace GBCA

/-- The fields of `ProcNode` minus the copy of the corrupted set. -/
structure ProcNodeU (n : ℕ) : Type where
  /-- The process's local record — the monolithic `proc j`. -/
  proc : ProcState
  /-- The messages the process has multicast. -/
  out : Finset Msg
  /-- `inbox k` — the messages from sender `k` delivered here. -/
  inbox : Fin n → Finset Msg
  deriving DecidableEq

namespace ProcNodeU

variable {n : ℕ}

/-- The initial node: nothing received, nothing sent. -/
def initial (n : ℕ) : ProcNodeU n where
  proc := ProcState.initial
  out := ∅
  inbox := fun _ => ∅

/-- The number of distinct senders from which this process has received `m`. -/
def recvCount (p : ProcNodeU n) (m : Msg) : ℕ :=
  (Finset.univ.filter (fun k => m ∈ p.inbox k)).card

/-- The number of distinct senders of some received `ECHO`. -/
def echoCount (p : ProcNodeU n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ b, Msg.echo b ∈ p.inbox k)).card

/-- The number of distinct senders of some received `VOTE`. -/
def voteCount (p : ProcNodeU n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ v, Msg.vote v ∈ p.inbox k)).card

/-- The number of distinct senders of some received `BIND`. -/
def bindCount (p : ProcNodeU n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ v, Msg.bind v ∈ p.inbox k)).card

/-- The number of distinct senders of some received `SEAL`. -/
def sealCount (p : ProcNodeU n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ v, Msg.seal v ∈ p.inbox k)).card

/-- Both bits are backed by an `n − f` `INPUT` quorum among the delivered
messages. -/
def bothValid (P : Params) (p : ProcNodeU P.n) : Prop :=
  P.n - P.f ≤ p.recvCount (.input true) ∧ P.n - P.f ≤ p.recvCount (.input false)

/-- Overwrite the local record. -/
def setP (p : ProcNodeU n) (pr : ProcState) : ProcNodeU n := { p with proc := pr }

/-- Multicast `m`: add it to the outbox. -/
def send (p : ProcNodeU n) (m : Msg) : ProcNodeU n := { p with out := insert m p.out }

/-- File `m` under the inbox row of sender `k`. -/
def deliverTo (p : ProcNodeU n) (k : Fin n) (m : Msg) : ProcNodeU n :=
  { p with inbox := Function.update p.inbox k (insert m (p.inbox k)) }

end ProcNodeU

end GBCA

/-- The fields of `CoreNode` minus the copy of the corrupted set. -/
structure CoreNodeU (n : ℕ) : Type where
  /-- The process's own control record. -/
  proc : ProcCore n
  /-- The process's own DECIDED pool. -/
  decOut : Finset Bool
  /-- The DECIDED payloads delivered to this process, indexed by sender. -/
  decIn : Fin n → Finset Bool

namespace CoreNodeU

variable {n : ℕ}

/-- The initial state of one process: idle control record, empty pools. -/
def initial (n : ℕ) : CoreNodeU n where
  proc := ProcCore.initial n
  decOut := ∅
  decIn := fun _ => ∅

/-- The number of distinct senders whose `⟨DECIDED, b⟩` this process holds. -/
def decidedCount (q : CoreNodeU n) (b : Bool) : ℕ :=
  (Finset.univ.filter (fun k => b ∈ q.decIn k)).card

/-- Update the control record. -/
def setProc (q : CoreNodeU n) (p : ProcCore n) : CoreNodeU n := { q with proc := p }

/-- Multicast `⟨DECIDED, b⟩`: insert `b` into the own pool. -/
def sendDec (q : CoreNodeU n) (b : Bool) : CoreNodeU n :=
  { q with decOut := insert b q.decOut }

/-- Record a delivered `⟨DECIDED, b⟩` from sender `k`. -/
def recvDec (q : CoreNodeU n) (k : Fin n) (b : Bool) : CoreNodeU n :=
  { q with decIn := Function.update q.decIn k (insert b (q.decIn k)) }

/-- The round advance on receiving the coin `c`, exactly as
`CoreNode.stepRound`. -/
def stepRound (q : CoreNodeU n) (c : Bool) : CoreNodeU n :=
  (match q.proc.lastGrade with
    | some (.A b) => q.sendDec b
    | _ => q).setProc
    { q.proc with
      est := some (q.proc.est.getD c),
      lastGrade := none,
      round := q.proc.round + 1,
      phase := .toCallG }

end CoreNodeU

namespace OwnFlag

open Flat

/-- The state of one own-flag flat process: the coordinator record and one
stage per round, both without corrupted-set copies, and one corruption flag
for the whole node. -/
abbrev ABANodeU (n : ℕ) : Type := CoreNodeU n × (ℕ → GBCA.ProcNodeU n) × Bool

/-! ### The rule table

`Flat.ABAProcStep`, rule for rule. Honest rules are verbatim modulo the
record change; the Byzantine guards `j ∈ F` (round loop) and `j ∈ (g r).F`
(stage) both become `fl = true`; the `fail k` row raises `k`'s own flag
unconditionally and idempotently, and every other node takes the broadcast
label without moving. -/

/-- The step relation of the own-flag flat automaton of process `j`. -/
inductive ABAProcStepU (P : Params) (j : Fin P.n) :
    ABANodeU P.n → FLab P.n → PMF (ABANodeU P.n) → Prop
  /-- `upon ABA(b)`: record input and estimate, open round `0`. -/
  | input (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool) (b : Bool)
      (h : c.proc.input = none) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.callABA j b))
        (PMF.pure (c.setProc { c.proc with
          input := some b, est := some b, round := 0, phase := .toCallG }, g, fl))
  /-- Input-enabledness loop on `j`'s own `callABA`. -/
  | inputLoop (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool) (b : Bool) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.callABA j b)) (PMF.pure (c, g, fl))
  /-- An input addressed elsewhere: not `j`'s business. -/
  | callABAIdle (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.callABA id b)) (PMF.pure (c, g, fl))
  /-- Return `b` on an `n − f` DECIDED quorum, having multicast. -/
  | ret (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool) (b : Bool)
      (hcnt : P.n - P.f ≤ c.decidedCount b) (hs : b ∈ c.decOut)
      (hret : c.proc.returned = false) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.retABA j b))
        (PMF.pure (c.setProc { c.proc with returned := true }, g, fl))
  /-- A return by another process: not `j`'s business. -/
  | retABAIdle (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.retABA id b)) (PMF.pure (c, g, fl))
  /-- The genuine graded-agreement handshake. -/
  | callG_call (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (b : Bool)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r) (hest : c.proc.est = some b)
      (hin : (g r).proc.input = none) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.callG r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG },
          Function.update g r (((g r).setP { (g r).proc with
              input := some b,
              sentInput := Function.update (g r).proc.sentInput b true }).send
            (.input b)), fl))
  /-- The handshake against an already-called stage. -/
  | callG_loop (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (b : Bool)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r) (hest : c.proc.est = some b) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.callG r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG }, g, fl))
  /-- A corrupted round-loop drives the call with an arbitrary bit. -/
  | callGByz_call (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (b : Bool)
      (hF : fl = true) (hin : (g r).proc.input = none) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.callG r j b))
        (PMF.pure (c,
          Function.update g r (((g r).setP { (g r).proc with
              input := some b,
              sentInput := Function.update (g r).proc.sentInput b true }).send
            (.input b)), fl))
  /-- A corrupted round-loop drives the call against an already-called stage. -/
  | callGByz_loop (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (b : Bool) (hF : fl = true) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.callG r j b)) (PMF.pure (c, g, fl))
  /-- A graded-agreement call by another process: not `j`'s business. -/
  | callGIdle (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.callG r id b)) (PMF.pure (c, g, fl))
  /-- Return with grade `A v`. -/
  | retG_A (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (v : Bool)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r)
      (hcnt : P.n - P.f ≤ (g r).recvCount (.seal (some v)))
      (hret : (g r).proc.returned = false) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.retG r j (.A v)))
        (PMF.pure (c.setProc { c.proc with
            est := (GbcaOut.A v).est, lastGrade := some (.A v), phase := .toCallW },
          Function.update g r ((g r).setP { (g r).proc with returned := true }), fl))
  /-- Return with grade `B v`. -/
  | retG_B (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (v : Bool)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r)
      (hcnt : P.n - P.f ≤ (g r).sealCount)
      (honce : ∃ k, GBCA.Msg.seal (some v) ∈ (g r).inbox k)
      (hbind : P.f + 1 ≤ (g r).recvCount (.bind (some v)))
      (hval : (g r).bothValid P)
      (hret : (g r).proc.returned = false) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.retG r j (.B v)))
        (PMF.pure (c.setProc { c.proc with
            est := (GbcaOut.B v).est, lastGrade := some (.B v), phase := .toCallW },
          Function.update g r ((g r).setP { (g r).proc with returned := true }), fl))
  /-- Return with grade `C`. -/
  | retG_C (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool) (r : ℕ)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r)
      (hcnt : P.n - P.f ≤ (g r).recvCount (.seal none))
      (hval : (g r).bothValid P)
      (hret : (g r).proc.returned = false) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.retG r j .C))
        (PMF.pure (c.setProc { c.proc with
            est := GbcaOut.C.est, lastGrade := some .C, phase := .toCallW },
          Function.update g r ((g r).setP { (g r).proc with returned := true }), fl))
  /-- Grade-`A` return to a corrupted round-loop. -/
  | retGByz_A (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (v : Bool) (hF : fl = true)
      (hcnt : P.n - P.f ≤ (g r).recvCount (.seal (some v)))
      (hret : (g r).proc.returned = false) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.retG r j (.A v)))
        (PMF.pure (c,
          Function.update g r ((g r).setP { (g r).proc with returned := true }), fl))
  /-- Grade-`B` return to a corrupted round-loop. -/
  | retGByz_B (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (v : Bool) (hF : fl = true)
      (hcnt : P.n - P.f ≤ (g r).sealCount)
      (honce : ∃ k, GBCA.Msg.seal (some v) ∈ (g r).inbox k)
      (hbind : P.f + 1 ≤ (g r).recvCount (.bind (some v)))
      (hval : (g r).bothValid P)
      (hret : (g r).proc.returned = false) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.retG r j (.B v)))
        (PMF.pure (c,
          Function.update g r ((g r).setP { (g r).proc with returned := true }), fl))
  /-- Grade-`C` return to a corrupted round-loop. -/
  | retGByz_C (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (hF : fl = true)
      (hcnt : P.n - P.f ≤ (g r).recvCount (.seal none))
      (hval : (g r).bothValid P)
      (hret : (g r).proc.returned = false) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.retG r j .C))
        (PMF.pure (c,
          Function.update g r ((g r).setP { (g r).proc with returned := true }), fl))
  /-- A graded-agreement return to another process: not `j`'s business. -/
  | retGIdle (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (id : Fin P.n) (out : GbcaOut) (hid : id ≠ j) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.retG r id out)) (PMF.pure (c, g, fl))
  /-- `c ← WCC_r()`, the call half at the round-loop. -/
  | callW (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool) (r : ℕ)
      (hph : c.proc.phase = .toCallW) (hr : c.proc.round = r) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.callW r j))
        (PMF.pure (c.setProc { c.proc with phase := .awaitW }, g, fl))
  /-- A corrupted round-loop drives the coin call. -/
  | callWByz (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool) (r : ℕ)
      (hF : fl = true) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.callW r j)) (PMF.pure (c, g, fl))
  /-- A coin call by another process: not `j`'s business. -/
  | callWIdle (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (id : Fin P.n) (hid : id ≠ j) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.callW r id)) (PMF.pure (c, g, fl))
  /-- The coin return, fused with the round advance. -/
  | retW (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (co : Bool)
      (hph : c.proc.phase = .awaitW) (hr : c.proc.round = r) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.retW r j co))
        (PMF.pure (c.stepRound co, g, fl))
  /-- A corrupted round-loop drives the coin return. -/
  | retWByz (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (co : Bool) (hF : fl = true) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.retW r j co)) (PMF.pure (c, g, fl))
  /-- A coin return to another process: not `j`'s business. -/
  | retWIdle (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (id : Fin P.n) (co : Bool) (hid : id ≠ j) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.retW r id co)) (PMF.pure (c, g, fl))
  /-- Corruption: `j` raises its own flag iff it is the corrupted process;
  the write is unguarded and idempotent, and every node takes the label. -/
  | fail (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool) (k : Fin P.n) :
      ABAProcStepU P j (c, g, fl) (Sum.inl (.fail k))
        (PMF.pure (c, g, if k = j then true else fl))
  /-- The DECIDED echo on an `f + 1` quorum. -/
  | echo (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool) (b : Bool)
      (hcnt : P.f + 1 ≤ c.decidedCount b) (hs : b ∉ c.decOut) :
      ABAProcStepU P j (c, g, fl) (Sum.inl .tau) (PMF.pure (c.sendDec b, g, fl))
  /-- A corrupted process injects an arbitrary DECIDED payload. -/
  | byzDecided (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool) (b : Bool)
      (hF : fl = true) :
      ABAProcStepU P j (c, g, fl) (Sum.inl .tau) (PMF.pure (c.sendDec b, g, fl))
  /-- Stage `r`'s `INPUT` relay. -/
  | stageRelay (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (b : Bool)
      (hin : (g r).proc.input ≠ none) (hcnt : P.f + 1 ≤ (g r).recvCount (.input b))
      (hsend : (g r).proc.sentInput b = false) :
      ABAProcStepU P j (c, g, fl) (Sum.inl .tau)
        (PMF.pure (c, Function.update g r (((g r).setP { (g r).proc with
          sentInput := Function.update (g r).proc.sentInput b true }).send (.input b)), fl))
  /-- Stage `r`'s `ECHO`. -/
  | stageEcho (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (b : Bool)
      (hin : (g r).proc.input ≠ none) (hcnt : P.n - P.f ≤ (g r).recvCount (.input b))
      (hsend : (g r).proc.sentEcho = none) :
      ABAProcStepU P j (c, g, fl) (Sum.inl .tau)
        (PMF.pure (c, Function.update g r
          (((g r).setP { (g r).proc with sentEcho := some b }).send (.echo b)), fl))
  /-- Stage `r`'s `VOTE b`. -/
  | stageVoteBit (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (b : Bool)
      (hin : (g r).proc.input ≠ none) (hcnt : P.n - P.f ≤ (g r).recvCount (.echo b))
      (hsend : (g r).proc.sentVote = none) :
      ABAProcStepU P j (c, g, fl) (Sum.inl .tau)
        (PMF.pure (c, Function.update g r
          (((g r).setP { (g r).proc with sentVote := some (some b) }).send
            (.vote (some b))), fl))
  /-- Stage `r`'s `VOTE ⊥`. -/
  | stageVoteBot (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool) (r : ℕ)
      (hin : (g r).proc.input ≠ none) (hcnt : P.n - P.f ≤ (g r).echoCount)
      (hval : (g r).bothValid P) (hsend : (g r).proc.sentVote = none) :
      ABAProcStepU P j (c, g, fl) (Sum.inl .tau)
        (PMF.pure (c, Function.update g r
          (((g r).setP { (g r).proc with sentVote := some none }).send (.vote none)), fl))
  /-- Stage `r`'s `BIND b`. -/
  | stageBindBit (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (b : Bool)
      (hin : (g r).proc.input ≠ none) (hcnt : P.n - P.f ≤ (g r).recvCount (.vote (some b)))
      (hsend : (g r).proc.sentBind = none) :
      ABAProcStepU P j (c, g, fl) (Sum.inl .tau)
        (PMF.pure (c, Function.update g r
          (((g r).setP { (g r).proc with sentBind := some (some b) }).send
            (.bind (some b))), fl))
  /-- Stage `r`'s `BIND ⊥`. -/
  | stageBindBot (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool) (r : ℕ)
      (hin : (g r).proc.input ≠ none) (hcnt : P.n - P.f ≤ (g r).voteCount)
      (hval : (g r).bothValid P) (hsend : (g r).proc.sentBind = none) :
      ABAProcStepU P j (c, g, fl) (Sum.inl .tau)
        (PMF.pure (c, Function.update g r
          (((g r).setP { (g r).proc with sentBind := some none }).send (.bind none)), fl))
  /-- Stage `r`'s `SEAL b`. -/
  | stageSealBit (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (b : Bool)
      (hin : (g r).proc.input ≠ none) (hcnt : P.n - P.f ≤ (g r).recvCount (.bind (some b)))
      (hsend : (g r).proc.sentSeal = none) :
      ABAProcStepU P j (c, g, fl) (Sum.inl .tau)
        (PMF.pure (c, Function.update g r
          (((g r).setP { (g r).proc with sentSeal := some (some b) }).send
            (.seal (some b))), fl))
  /-- Stage `r`'s `SEAL ⊥`. -/
  | stageSealBot (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool) (r : ℕ)
      (hin : (g r).proc.input ≠ none) (hcnt : P.n - P.f ≤ (g r).bindCount)
      (hval : (g r).bothValid P) (hsend : (g r).proc.sentSeal = none) :
      ABAProcStepU P j (c, g, fl) (Sum.inl .tau)
        (PMF.pure (c, Function.update g r
          (((g r).setP { (g r).proc with sentSeal := some none }).send (.seal none)), fl))
  /-- Byzantine injection into stage `r`'s outbox: the guard is the node's one
  flag. -/
  | stageByz (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (m : GBCA.Msg) (hF : fl = true) :
      ABAProcStepU P j (c, g, fl) (Sum.inl .tau)
        (PMF.pure (c, Function.update g r ((g r).send m), fl))
  /-- DECIDED gossip, sender and receiver in one process. -/
  | dnetSelf (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool) (b : Bool)
      (hs : b ∈ c.decOut) (hr : b ∉ c.decIn j) :
      ABAProcStepU P j (c, g, fl) (Sum.inr (.dnet j j b)) (PMF.pure (c.recvDec j b, g, fl))
  /-- DECIDED gossip, sender half. -/
  | dnetSend (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (i : Fin P.n) (b : Bool) (hi : i ≠ j) (hs : b ∈ c.decOut) :
      ABAProcStepU P j (c, g, fl) (Sum.inr (.dnet i j b)) (PMF.pure (c, g, fl))
  /-- DECIDED gossip, receiver half. -/
  | dnetRecv (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (k : Fin P.n) (b : Bool) (hk : k ≠ j) (hr : b ∉ c.decIn k) :
      ABAProcStepU P j (c, g, fl) (Sum.inr (.dnet j k b)) (PMF.pure (c.recvDec k b, g, fl))
  /-- DECIDED gossip between two other processes: not `j`'s business. -/
  | dnetIdle (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (i k : Fin P.n) (b : Bool) (hi : i ≠ j) (hk : k ≠ j) :
      ABAProcStepU P j (c, g, fl) (Sum.inr (.dnet i k b)) (PMF.pure (c, g, fl))
  /-- Stage-`r` self-delivery. -/
  | gnetSelf (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (m : GBCA.Msg) (h : m ∈ (g r).out) :
      ABAProcStepU P j (c, g, fl) (Sum.inr (.gnet r j j m))
        (PMF.pure (c, Function.update g r ((g r).deliverTo j m), fl))
  /-- Stage-`r` sender half. -/
  | gnetSend (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (i : Fin P.n) (m : GBCA.Msg) (hi : i ≠ j) (h : m ∈ (g r).out) :
      ABAProcStepU P j (c, g, fl) (Sum.inr (.gnet r i j m)) (PMF.pure (c, g, fl))
  /-- Stage-`r` receiver half. -/
  | gnetRecv (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (k : Fin P.n) (m : GBCA.Msg) (hk : k ≠ j) :
      ABAProcStepU P j (c, g, fl) (Sum.inr (.gnet r j k m))
        (PMF.pure (c, Function.update g r ((g r).deliverTo k m), fl))
  /-- A stage-`r` delivery between two other processes: not `j`'s business. -/
  | gnetIdle (c : CoreNodeU P.n) (g : ℕ → GBCA.ProcNodeU P.n) (fl : Bool)
      (r : ℕ) (i k : Fin P.n) (m : GBCA.Msg) (hi : i ≠ j) (hk : k ≠ j) :
      ABAProcStepU P j (c, g, fl) (Sum.inr (.gnet r i k m)) (PMF.pure (c, g, fl))

/-! ### The automaton and the composition pipeline -/

/-- The own-flag flat automaton of process `j`. -/
noncomputable def ABAProcU (P : Params) (j : Fin P.n) :
    System (ABANodeU P.n) (FLab P.n) where
  init := (CoreNodeU.initial P.n, fun _ => GBCA.ProcNodeU.initial P.n, false)
  step := ABAProcStepU P j

/-- Every own-flag flat transition is Dirac. -/
theorem ABAProcU_isLTS (P : Params) (j : Fin P.n) : (ABAProcU P j).IsLTS := by
  rintro q l μ hstep
  cases hstep <;> exact ⟨_, rfl⟩

/-- **The own-flag process group**: full synchronisation, the two networks
hidden, the result read back over `Lab n`. -/
noncomputable def ownFlagGroup (P : Params) :
    System (∀ _ : Fin P.n, ABANodeU P.n) (Lab P.n) :=
  ((System.syncProduct (ABAProcU P)).abstract (flatNetLabels P.n)).relabel

theorem ownFlagGroup_isLTS (P : Params) : (ownFlagGroup P).IsLTS :=
  System.relabel_isLTS
    (System.abstract_isLTS (System.syncProduct_isLTS (ABAProcU_isLTS P)) _)

/-- The own-flag process group beside the coin oracle, which keeps its
budget-guarded `corrupt`. -/
noncomputable def ownFlagPre (P : Params) :
    System ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)) (Lab P.n) :=
  (ownFlagGroup P).parallel (WCC.specFamily P)

/-- **The own-flag flat hybrid**: the own-flag counterpart of
`Flat.flatHybrid`, with the sub-protocol API hidden. -/
noncomputable def ownFlagFlat (P : Params) :
    System ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)) (Lab P.n) :=
  (ownFlagPre P).abstract (Lab.hiddenAPI P.n)

/-! ### Inflation

`inflate` reads an own-flag state as a guarded flat state: every protocol
field is copied and every copy of the corrupted set becomes the one global
set of flagged processes. -/

/-- Refit a `CoreNodeU` with the corrupted set `S`. -/
def inflCore {n : ℕ} (S : Finset (Fin n)) (c : CoreNodeU n) : CoreNode n :=
  ⟨c.proc, c.decOut, c.decIn, S⟩

/-- Refit a `ProcNodeU` with the corrupted set `S`. -/
def inflStage {n : ℕ} (S : Finset (Fin n)) (p : GBCA.ProcNodeU n) : GBCA.ProcNode n :=
  ⟨p.proc, p.out, p.inbox, S⟩

/-- Refit one flat node with the corrupted set `S` (the flag is dropped). -/
def inflNode {n : ℕ} (S : Finset (Fin n)) (q : ABANodeU n) : ABANode n :=
  (inflCore S q.1, fun r => inflStage S (q.2.1 r))

/-- The set of processes whose flag is raised. -/
def flagSet {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) : Finset (Fin n) :=
  Finset.univ.filter (fun k => (u k).2.2 = true)

@[simp] theorem mem_flagSet {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) (k : Fin n) :
    k ∈ flagSet u ↔ (u k).2.2 = true := by
  simp [flagSet]

/-- **The packing map**: every node gets its protocol fields back and the one
global flag set in every copy of the corrupted set. -/
def inflate {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) : ∀ _ : Fin n, ABANode n :=
  fun m => inflNode (flagSet u) (u m)

/-- The packing map on a whole state: the coin oracle is untouched. -/
def inflateFull {P : Params}
    (s : (∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)) :
    (∀ _ : Fin P.n, ABANode P.n) × (ℕ → WCC.SpecState P.n) :=
  (inflate s.1, s.2)

/-- The corrupted set after a label: `fail k` inserts `k`, everything else is
fixed. -/
def failAfter {n : ℕ} : FLab n → Finset (Fin n) → Finset (Fin n)
  | Sum.inl (.fail k), S => insert k S
  | _, S => S

/-! #### Commutation of inflation with the state updates -/

theorem inflStage_update {n : ℕ} (S : Finset (Fin n)) (g : ℕ → GBCA.ProcNodeU n)
    (r : ℕ) (x : GBCA.ProcNodeU n) :
    (fun r' => inflStage S (Function.update g r x r'))
      = Function.update (fun r' => inflStage S (g r')) r (inflStage S x) := by
  funext r'
  by_cases h : r' = r
  · subst h; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne h]

/-- A stage update inside a node, read through inflation. -/
theorem inflNode_update_eq {n : ℕ} (S : Finset (Fin n)) (c : CoreNodeU n)
    (g : ℕ → GBCA.ProcNodeU n) (fl : Bool) (r : ℕ) (x : GBCA.ProcNodeU n) :
    inflNode S (c, Function.update g r x, fl)
      = (inflCore S c, Function.update (fun r' => inflStage S (g r')) r (inflStage S x)) :=
  Prod.ext rfl (inflStage_update S g r x)

@[simp] theorem inflCore_proc {n : ℕ} (S : Finset (Fin n)) (c : CoreNodeU n) :
    (inflCore S c).proc = c.proc := rfl

theorem inflCore_stepRound {n : ℕ} (S : Finset (Fin n)) (c : CoreNodeU n) (co : Bool) :
    inflCore S (c.stepRound co) = (inflCore S c).stepRound co := by
  unfold CoreNodeU.stepRound CoreNode.stepRound
  rw [inflCore_proc]
  cases c.proc.lastGrade with
  | none => rfl
  | some out => cases out <;> rfl

/-- The guarded insert agrees with the unguarded flag write on a repeat or
with budget headroom. -/
theorem inflCore_corrupt {P : Params} {S : Finset (Fin P.n)} {k : Fin P.n}
    (h : k ∈ S ∨ S.card < P.f) (c : CoreNodeU P.n) :
    (inflCore S c).corrupt P k = inflCore (insert k S) c := by
  unfold CoreNode.corrupt
  by_cases hk : k ∈ S
  · rw [if_neg (by simp [inflCore, hk]), Finset.insert_eq_self.mpr hk]
  · rw [if_pos ⟨by simpa [inflCore] using hk, by simpa [inflCore] using h.resolve_left hk⟩]
    rfl

theorem inflStage_corrupt {P : Params} {S : Finset (Fin P.n)} {k : Fin P.n}
    (h : k ∈ S ∨ S.card < P.f) (p : GBCA.ProcNodeU P.n) :
    (inflStage S p).corrupt P k = inflStage (insert k S) p := by
  unfold GBCA.ProcNode.corrupt
  by_cases hk : k ∈ S
  · rw [if_neg (by simp [inflStage, hk]), Finset.insert_eq_self.mpr hk]
  · rw [if_pos ⟨by simpa [inflStage] using hk, by simpa [inflStage] using h.resolve_left hk⟩]
    rfl

/-! ### The per-step matching lemma

One rule table read into the other: an own-flag transition of process `j`
whose `fail` labels are repeats or fired with budget headroom is the guarded
transition on the same label, targets pushed along `inflNode`. -/

theorem bridge_procStep {P : Params} {j : Fin P.n} {S : Finset (Fin P.n)}
    {q : ABANodeU P.n} {l : FLab P.n} {ν : PMF (ABANodeU P.n)}
    (hS : q.2.2 = true ↔ j ∈ S)
    (hOK : ∀ k, l = Sum.inl (.fail k) → k ∈ S ∨ S.card < P.f)
    (h : ABAProcStepU P j q l ν) :
    ABAProcStep P j (inflNode S q) l (ν.map (inflNode (failAfter l S))) := by
  cases h with
  | input c g fl b hin =>
    rw [PMF.pure_map]
    exact .input _ _ b hin
  | inputLoop c g fl b =>
    rw [PMF.pure_map]
    exact .inputLoop _ _ b
  | callABAIdle c g fl id b hid =>
    rw [PMF.pure_map]
    exact .callABAIdle _ _ id b hid
  | ret c g fl b hcnt hs hret =>
    rw [PMF.pure_map]
    exact .ret _ _ b hcnt hs hret
  | retABAIdle c g fl id b hid =>
    rw [PMF.pure_map]
    exact .retABAIdle _ _ id b hid
  | callG_call c g fl r b hph hr hest hin =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .callG_call _ _ r b hph hr hest hin
  | callG_loop c g fl r b hph hr hest =>
    rw [PMF.pure_map]
    exact .callG_loop _ _ r b hph hr hest
  | callGByz_call c g fl r b hF hin =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .callGByz_call _ _ r b (hS.mp hF) hin
  | callGByz_loop c g fl r b hF =>
    rw [PMF.pure_map]
    exact .callGByz_loop _ _ r b (hS.mp hF)
  | callGIdle c g fl r id b hid =>
    rw [PMF.pure_map]
    exact .callGIdle _ _ r id b hid
  | retG_A c g fl r v hph hr hcnt hret =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .retG_A _ _ r v hph hr hcnt hret
  | retG_B c g fl r v hph hr hcnt honce hbind hval hret =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .retG_B _ _ r v hph hr hcnt honce hbind hval hret
  | retG_C c g fl r hph hr hcnt hval hret =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .retG_C _ _ r hph hr hcnt hval hret
  | retGByz_A c g fl r v hF hcnt hret =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .retGByz_A _ _ r v (hS.mp hF) hcnt hret
  | retGByz_B c g fl r v hF hcnt honce hbind hval hret =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .retGByz_B _ _ r v (hS.mp hF) hcnt honce hbind hval hret
  | retGByz_C c g fl r hF hcnt hval hret =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .retGByz_C _ _ r (hS.mp hF) hcnt hval hret
  | retGIdle c g fl r id out hid =>
    rw [PMF.pure_map]
    exact .retGIdle _ _ r id out hid
  | callW c g fl r hph hr =>
    rw [PMF.pure_map]
    exact .callW _ _ r hph hr
  | callWByz c g fl r hF =>
    rw [PMF.pure_map]
    exact .callWByz _ _ r (hS.mp hF)
  | callWIdle c g fl r id hid =>
    rw [PMF.pure_map]
    exact .callWIdle _ _ r id hid
  | retW c g fl r co hph hr =>
    have heq : inflNode (failAfter (Sum.inl (Lab.retW r j co) : FLab P.n) S)
          (c.stepRound co, g, fl)
        = ((inflCore S c).stepRound co, fun r' => inflStage S (g r')) :=
      Prod.ext (inflCore_stepRound S c co) rfl
    rw [PMF.pure_map, heq]
    exact .retW _ _ r co hph hr
  | retWByz c g fl r co hF =>
    rw [PMF.pure_map]
    exact .retWByz _ _ r co (hS.mp hF)
  | retWIdle c g fl r id co hid =>
    rw [PMF.pure_map]
    exact .retWIdle _ _ r id co hid
  | fail c g fl k =>
    rw [PMF.pure_map,
      show inflNode (failAfter (Sum.inl (.fail k)) S) (c, g, if k = j then true else fl)
          = ((inflCore S c).corrupt P k, fun r => (inflStage S (g r)).corrupt P k) from by
        refine Prod.ext ?_ (funext fun r => ?_)
        · exact (inflCore_corrupt (hOK k rfl) c).symm
        · exact (inflStage_corrupt (hOK k rfl) (g r)).symm]
    exact .fail _ _ k
  | echo c g fl b hcnt hs =>
    rw [PMF.pure_map]
    exact .echo _ _ b hcnt hs
  | byzDecided c g fl b hF =>
    rw [PMF.pure_map]
    exact .byzDecided _ _ b (hS.mp hF)
  | stageRelay c g fl r b hin hcnt hsend =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .stageRelay _ _ r b hin hcnt hsend
  | stageEcho c g fl r b hin hcnt hsend =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .stageEcho _ _ r b hin hcnt hsend
  | stageVoteBit c g fl r b hin hcnt hsend =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .stageVoteBit _ _ r b hin hcnt hsend
  | stageVoteBot c g fl r hin hcnt hval hsend =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .stageVoteBot _ _ r hin hcnt hval hsend
  | stageBindBit c g fl r b hin hcnt hsend =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .stageBindBit _ _ r b hin hcnt hsend
  | stageBindBot c g fl r hin hcnt hval hsend =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .stageBindBot _ _ r hin hcnt hval hsend
  | stageSealBit c g fl r b hin hcnt hsend =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .stageSealBit _ _ r b hin hcnt hsend
  | stageSealBot c g fl r hin hcnt hval hsend =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .stageSealBot _ _ r hin hcnt hval hsend
  | stageByz c g fl r m hF =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .stageByz _ _ r m (hS.mp hF)
  | dnetSelf c g fl b hs hr =>
    rw [PMF.pure_map]
    exact .dnetSelf _ _ b hs hr
  | dnetSend c g fl i b hi hs =>
    rw [PMF.pure_map]
    exact .dnetSend _ _ i b hi hs
  | dnetRecv c g fl k b hk hr =>
    rw [PMF.pure_map]
    exact .dnetRecv _ _ k b hk hr
  | dnetIdle c g fl i k b hi hk =>
    rw [PMF.pure_map]
    exact .dnetIdle _ _ i k b hi hk
  | gnetSelf c g fl r m hm =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .gnetSelf _ _ r m hm
  | gnetSend c g fl r i m hi hm =>
    rw [PMF.pure_map]
    exact .gnetSend _ _ r i m hi hm
  | gnetRecv c g fl r k m hk =>
    rw [PMF.pure_map, inflNode_update_eq]
    exact .gnetRecv _ _ r k m hk
  | gnetIdle c g fl r i k m hi hk =>
    rw [PMF.pure_map]
    exact .gnetIdle _ _ r i k m hi hk

/-! ### The flag after a step -/

/-- A raised flag was already raised, unless the step is the node's own
corruption. -/
theorem stepU_flag_support {P : Params} {j : Fin P.n} {q y : ABANodeU P.n}
    {l : FLab P.n} {ν : PMF (ABANodeU P.n)}
    (h : ABAProcStepU P j q l ν) (hy : y ∈ ν.support) (hf : y.2.2 = true) :
    q.2.2 = true ∨ l = Sum.inl (Lab.fail j) := by
  cases h with
  | fail c g fl k =>
    rw [PMF.mem_support_pure_iff] at hy
    subst hy
    by_cases hk : k = j
    · subst hk; exact Or.inr rfl
    · rw [if_neg hk] at hf; exact Or.inl hf
  | _ =>
    rw [PMF.mem_support_pure_iff] at hy
    subst hy
    exact Or.inl hf

/-- Non-fail rules leave the flag alone. -/
theorem stepU_flag_eq {P : Params} {j : Fin P.n} {q y : ABANodeU P.n}
    {l : FLab P.n} {ν : PMF (ABANodeU P.n)}
    (h : ABAProcStepU P j q l ν) (hy : y ∈ ν.support)
    (hl : ∀ k, l ≠ Sum.inl (Lab.fail k)) : y.2.2 = q.2.2 := by
  cases h with
  | fail c g fl k => exact absurd rfl (hl k)
  | _ =>
    rw [PMF.mem_support_pure_iff] at hy
    subst hy
    rfl

/-- Inversion of the fail row. -/
theorem stepU_fail_inv {P : Params} {j : Fin P.n} {q : ABANodeU P.n}
    {k : Fin P.n} {ν : PMF (ABANodeU P.n)}
    (h : ABAProcStepU P j q (Sum.inl (.fail k)) ν) :
    ν = PMF.pure (q.1, q.2.1, if k = j then true else q.2.2) := by
  cases h
  rfl

theorem flagSet_congr {n : ℕ} {u x : ∀ _ : Fin n, ABANodeU n}
    (h : ∀ m, (x m).2.2 = (u m).2.2) : flagSet x = flagSet u := by
  unfold flagSet
  exact Finset.filter_congr fun m _ => by rw [h m]

theorem flagSet_insert {n : ℕ} {u x : ∀ _ : Fin n, ABANodeU n} {k : Fin n}
    (h : ∀ m, (x m).2.2 = (if k = m then true else (u m).2.2)) :
    flagSet x = insert k (flagSet u) := by
  ext m
  rw [Finset.mem_insert, mem_flagSet, mem_flagSet, h m]
  by_cases hk : k = m
  · subst hk; simp
  · rw [if_neg hk]
    exact ⟨Or.inr, fun hc => hc.elim (fun he => absurd he.symm hk) id⟩

/-! ### Reading the own-flag group's step relation -/

private theorem pure_inj {α : Type} {a b : α}
    (h : (PMF.pure a : PMF α) = PMF.pure b) : a = b := by
  have hm : a ∈ (PMF.pure b).support := by rw [← h]; simp
  simpa using hm

/-- The composite step relation of the own-flag group, mirroring
`Flat.flatGroup_step_iff`. -/
theorem ownGroup_step_iff (P : Params) (q : ∀ _ : Fin P.n, ABANodeU P.n)
    (l : Lab P.n) (μ : PMF (∀ _ : Fin P.n, ABANodeU P.n)) :
    (ownFlagGroup P).step q l μ ↔
      (l = .tau ∧ ∃ e : FlatNet P.n,
        (System.syncProduct (ABAProcU P)).step q (Sum.inr e) μ) ∨
      (System.syncProduct (ABAProcU P)).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_flatNetLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_flatNetLabels l, hstep⟩

/-- A synchronised transition on a visible label: every process steps. -/
theorem syncU_visible_iff (P : Params) (q : ∀ _ : Fin P.n, ABANodeU P.n)
    (l : FLab P.n) (hl : l ≠ Sum.inl .tau) (μ : PMF (∀ _ : Fin P.n, ABANodeU P.n)) :
    (System.syncProduct (ABAProcU P)).step q l μ ↔
      ∃ μ_ : Fin P.n → PMF (ABANodeU P.n),
        (∀ m, ABAProcStepU P m (q m) l (μ_ m)) ∧ μ = piPMF μ_ := by
  constructor
  · rintro (⟨-, μ_, hall, rfl⟩ | ⟨hτ, -⟩)
    · exact ⟨μ_, hall, rfl⟩
    · exact absurd hτ hl
  · rintro ⟨μ_, hall, rfl⟩
    exact Or.inl ⟨hl, μ_, hall, rfl⟩

/-- A synchronised transition on the silent label: exactly one process steps. -/
theorem syncU_tau_iff (P : Params) (q : ∀ _ : Fin P.n, ABANodeU P.n)
    (μ : PMF (∀ _ : Fin P.n, ABANodeU P.n)) :
    (System.syncProduct (ABAProcU P)).step q (Sum.inl .tau) μ ↔
      ∃ (m : Fin P.n) (ν : PMF (ABANodeU P.n)),
        ABAProcStepU P m (q m) (Sum.inl .tau) ν ∧
        μ = piPMF (Function.update (fun k => PMF.pure (q k)) m ν) := by
  constructor
  · rintro (⟨hτ, -⟩ | ⟨-, m, ν, hstep, rfl⟩)
    · exact absurd rfl hτ
    · exact ⟨m, ν, hstep, rfl⟩
  · rintro ⟨m, ν, hstep, rfl⟩
    exact Or.inr ⟨rfl, m, ν, hstep, rfl⟩

private theorem piPMFU_eq_pure {P : Params} {μ_ : Fin P.n → PMF (ABANodeU P.n)}
    {x : ∀ _ : Fin P.n, ABANodeU P.n} (h : ∀ m, μ_ m = PMF.pure (x m)) :
    piPMF μ_ = PMF.pure x := by
  rw [funext h]
  exact piPMF_pure x

private theorem piPMFU_update_eq_pure {P : Params} (q : ∀ _ : Fin P.n, ABANodeU P.n)
    (i : Fin P.n) (y : ABANodeU P.n) :
    piPMF (Function.update (fun k => PMF.pure (q k)) i (PMF.pure y))
      = PMF.pure (Function.update q i y) := by
  rw [piPMF_update_pure, PMF.pure_map]

/-! ### The group-level bridge -/

/-- **The group bridge.** A transition of the own-flag group whose `fail`
label, if any, is a repeat or fired with budget headroom is the matching
guarded-group transition along `inflate`. -/
theorem bridge_group (P : Params) {u : ∀ _ : Fin P.n, ABANodeU P.n}
    {l : Lab P.n} {μ : PMF (∀ _ : Fin P.n, ABANodeU P.n)}
    (h : (ownFlagGroup P).step u l μ)
    (hOK : ∀ k, l = .fail k → k ∈ flagSet u ∨ (flagSet u).card < P.f) :
    (flatGroup P).step (inflate u) l (μ.map inflate) := by
  rw [ownGroup_step_iff] at h
  rcases h with ⟨rfl, e, hsync⟩ | hsync
  · -- Hidden network rendezvous: every process steps, no flag moves.
    obtain ⟨μ_, hall, rfl⟩ := (syncU_visible_iff P u (Sum.inr e) (by simp) _).mp hsync
    choose x hx using fun m => ABAProcU_isLTS P m (u m) _ _ (hall m)
    have hSx : flagSet x = flagSet u :=
      flagSet_congr fun m => stepU_flag_eq (hall m)
        (by rw [hx m]; simp) (fun k => by simp)
    rw [piPMFU_eq_pure hx, PMF.pure_map,
      show inflate x = fun m => inflNode (flagSet u) (x m) from
        funext fun m => by unfold inflate; rw [hSx]]
    refine flatGroup_net_step P (inflate u) e _ fun m => ?_
    have hb := bridge_procStep (mem_flagSet u m).symm (fun k hk => by cases hk)
      ((hx m) ▸ hall m)
    rwa [PMF.pure_map] at hb
  · by_cases hτ : l = .tau
    · -- One process's own silent rule: no flag moves.
      subst hτ
      obtain ⟨m, ν, hstep, rfl⟩ := (syncU_tau_iff P u _).mp hsync
      obtain ⟨y, rfl⟩ := ABAProcU_isLTS P m (u m) _ _ hstep
      have hSy : flagSet (Function.update u m y) = flagSet u := by
        refine flagSet_congr fun m' => ?_
        by_cases hm : m' = m
        · subst hm
          rw [Function.update_self]
          exact stepU_flag_eq hstep (by simp) (fun k => by simp)
        · rw [Function.update_of_ne hm]
      rw [piPMFU_update_eq_pure, PMF.pure_map,
        show inflate (Function.update u m y)
            = Function.update (inflate u) m (inflNode (flagSet u) y) from by
          funext m'
          unfold inflate
          rw [hSy]
          by_cases hm : m' = m
          · subst hm; rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hm, Function.update_of_ne hm]]
      refine flatGroup_tau_step P (inflate u) m _ ?_
      have hb := bridge_procStep (mem_flagSet u m).symm (fun k hk => by cases hk) hstep
      rwa [PMF.pure_map] at hb
    · -- A visible synchronised label: every process steps.
      obtain ⟨μ_, hall, rfl⟩ :=
        (syncU_visible_iff P u (Sum.inl l) (by simpa using hτ) _).mp hsync
      choose x hx using fun m => ABAProcU_isLTS P m (u m) _ _ (hall m)
      have hOK' : ∀ k, Sum.inl l = (Sum.inl (.fail k) : FLab P.n) →
          k ∈ flagSet u ∨ (flagSet u).card < P.f :=
        fun k hk => hOK k (Sum.inl_injective hk)
      have hSx : flagSet x = failAfter (Sum.inl l) (flagSet u) := by
        by_cases hf : ∃ k, l = .fail k
        · obtain ⟨k, rfl⟩ := hf
          refine flagSet_insert fun m => ?_
          have hinv := stepU_fail_inv (hall m)
          rw [hx m] at hinv
          rw [pure_inj hinv]
        · have hfa : failAfter (Sum.inl l) (flagSet u) = flagSet u := by
            cases l <;> first | rfl | exact absurd ⟨_, rfl⟩ hf
          rw [hfa]
          refine flagSet_congr fun m => stepU_flag_eq (hall m)
            (by rw [hx m]; simp)
            (fun k hk => hf ⟨k, Sum.inl_injective hk⟩)
      rw [piPMFU_eq_pure hx, PMF.pure_map,
        show inflate x = fun m => inflNode (failAfter (Sum.inl l) (flagSet u)) (x m) from
          funext fun m => by unfold inflate; rw [hSx]]
      refine flatGroup_visible_step P (inflate u) l hτ _ fun m => ?_
      have hb := bridge_procStep (mem_flagSet u m).symm hOK' ((hx m) ▸ hall m)
      rwa [PMF.pure_map] at hb

/-! ### The outer bridge -/

private theorem map_inflateFull_prod {P : Params}
    (μ₁ : PMF (∀ _ : Fin P.n, ABANodeU P.n)) (μ₂ : PMF (ℕ → WCC.SpecState P.n)) :
    (prodPMF μ₁ μ₂).map inflateFull = prodPMF (μ₁.map inflate) μ₂ := by
  rw [show (inflateFull (P := P))
      = (fun p : (∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n) =>
          (inflate p.1, id p.2)) from rfl,
    prodPMF_map, PMF.map_id]

/-- **The pre-abstraction bridge**: the group is bridged, the oracle carried
through untouched (it is the same component in the same state on both
sides). -/
theorem bridge_pre (P : Params)
    {s : (∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)}
    {l : Lab P.n}
    {μ : PMF ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n))}
    (h : (ownFlagPre P).step s l μ)
    (hOK : ∀ k, l = .fail k → k ∈ flagSet s.1 ∨ (flagSet s.1).card < P.f) :
    (flatPre P).step (inflateFull s) l (μ.map inflateFull) := by
  obtain ⟨u, w⟩ := s
  rcases h with ⟨hl, μ₁, μ₂, h1, h2, rfl⟩ | ⟨hτ, μ₁, h1, rfl⟩ | ⟨hτ, μ₂, h2, rfl⟩
  · exact Or.inl ⟨hl, μ₁.map inflate, μ₂, bridge_group P h1 hOK, h2,
      map_inflateFull_prod μ₁ μ₂⟩
  · refine Or.inr (Or.inl ⟨hτ, μ₁.map inflate,
      bridge_group P h1 (fun k hk => absurd (hτ.symm.trans hk) (by simp)), ?_⟩)
    exact map_inflateFull_prod μ₁ (PMF.pure w)
  · refine Or.inr (Or.inr ⟨hτ, μ₂, h2, ?_⟩)
    rw [map_inflateFull_prod (PMF.pure u) μ₂, PMF.pure_map]
    rfl

/-! ### The budgeted own-flag system and the full bridge -/

/-- The step-level budget condition: a `fail k` label is a repeat or is fired
with budget headroom. Every non-fail label is unconditionally OK. -/
def okLabel {P : Params}
    (s : (∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n))
    (l : Lab P.n) : Prop :=
  ∀ k, l = .fail k → (s.1 k).2.2 = true ∨ (flagSet s.1).card < P.f

/-- **The budgeted own-flag hybrid**: `ownFlagFlat` restricted to the steps
whose `fail` labels stay within budget. Its executions are exactly the
budget-respecting executions of `ownFlagFlat`. -/
noncomputable def ownFlagFlatB (P : Params) :
    System ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)) (Lab P.n) where
  init := (ownFlagFlat P).init
  step s l μ := (ownFlagFlat P).step s l μ ∧ okLabel s l

/-- **The bridge.** Every step of the budgeted own-flag hybrid is the guarded
flat hybrid's step along `inflateFull`, successor distributions pushed
forward. -/
theorem ownFlagFlatB_bridge (P : Params) :
    ∀ s l μ, (ownFlagFlatB P).step s l μ →
      (flatHybrid P).step (inflateFull s) l (μ.map inflateFull) := by
  rintro s l μ ⟨h, hOK⟩
  rcases h with ⟨rfl, l', hl', hpre⟩ | ⟨hn, hpre⟩
  · exact Or.inl ⟨rfl, l', hl',
      bridge_pre P hpre (fun k hk => absurd (hk ▸ hl') (Lab.fail_not_mem_hiddenAPI k))⟩
  · exact Or.inr ⟨hn,
      bridge_pre P hpre (fun k hk => (hOK k hk).imp (mem_flagSet _ _).mpr id)⟩

/-- Inflation carries the own-flag initial state to the guarded one. -/
theorem inflateFull_init (P : Params) :
    inflateFull ((ownFlagFlatB P).init) = (flatHybrid P).init := by
  have hfs : flagSet ((ownFlagFlatB P).init).1 = ∅ := by
    simp [flagSet, ownFlagFlatB, ownFlagFlat, ownFlagPre, ownFlagGroup, ABAProcU]
  refine Prod.ext ?_ rfl
  funext m
  show inflNode (flagSet ((ownFlagFlatB P).init).1) _ = _
  rw [hfs]
  rfl

/-! ### Flag growth along composite steps

Only its own `fail` label raises a process's flag: silent moves — local
sends, network rendezvous, hidden API labels, the coin flip — and foreign
visible labels leave every flag alone. -/

theorem group_flag_sub (P : Params) {u : ∀ _ : Fin P.n, ABANodeU P.n}
    {l : Lab P.n} {μ₁ : PMF (∀ _ : Fin P.n, ABANodeU P.n)}
    {u' : ∀ _ : Fin P.n, ABANodeU P.n}
    (h : (ownFlagGroup P).step u l μ₁) (hu' : u' ∈ μ₁.support)
    (m : Fin P.n) (hm : (u' m).2.2 = true) :
    (u m).2.2 = true ∨ l = .fail m := by
  rw [ownGroup_step_iff] at h
  rcases h with ⟨rfl, e, hsync⟩ | hsync
  · obtain ⟨μ_, hall, rfl⟩ := (syncU_visible_iff P u (Sum.inr e) (by simp) _).mp hsync
    rcases stepU_flag_support (hall m) (mem_support_piPMF.mp hu' m) hm with hold | habs
    · exact Or.inl hold
    · exact absurd habs (by simp)
  · by_cases hτ : l = .tau
    · subst hτ
      obtain ⟨i, ν, hstep, rfl⟩ := (syncU_tau_iff P u _).mp hsync
      have hmem := mem_support_piPMF.mp hu' m
      by_cases hmi : m = i
      · subst hmi
        rw [Function.update_self] at hmem
        rcases stepU_flag_support hstep hmem hm with hold | habs
        · exact Or.inl hold
        · exact absurd (Sum.inl_injective habs) (by simp)
      · rw [Function.update_of_ne hmi, PMF.mem_support_pure_iff] at hmem
        exact Or.inl (hmem ▸ hm)
    · obtain ⟨μ_, hall, rfl⟩ :=
        (syncU_visible_iff P u (Sum.inl l) (by simpa using hτ) _).mp hsync
      rcases stepU_flag_support (hall m) (mem_support_piPMF.mp hu' m) hm with hold | habs
      · exact Or.inl hold
      · exact Or.inr (Sum.inl_injective habs)

theorem pre_flag_sub (P : Params)
    {s s' : (∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)}
    {l : Lab P.n}
    {μ : PMF ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n))}
    (h : (ownFlagPre P).step s l μ) (hs' : s' ∈ μ.support)
    (m : Fin P.n) (hm : (s'.1 m).2.2 = true) :
    (s.1 m).2.2 = true ∨ l = .fail m := by
  obtain ⟨u, w⟩ := s
  rcases h with ⟨hl, μ₁, μ₂, h1, h2, rfl⟩ | ⟨hτ, μ₁, h1, rfl⟩ | ⟨hτ, μ₂, h2, rfl⟩
  · exact group_flag_sub P h1 (mem_support_prodPMF.mp hs').1 m hm
  · exact group_flag_sub P h1 (mem_support_prodPMF.mp hs').1 m hm
  · have h1' := (mem_support_prodPMF.mp hs').1
    rw [PMF.mem_support_pure_iff] at h1'
    exact Or.inl (h1' ▸ hm)

theorem step_flag_sub (P : Params)
    {s s' : (∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)}
    {l : Lab P.n}
    {μ : PMF ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n))}
    (h : (ownFlagFlat P).step s l μ) (hs' : s' ∈ μ.support)
    (m : Fin P.n) (hm : (s'.1 m).2.2 = true) :
    (s.1 m).2.2 = true ∨ l = .fail m := by
  rcases h with ⟨rfl, l', hl', hpre⟩ | ⟨-, hpre⟩
  · rcases pre_flag_sub P hpre hs' m hm with hold | hfail
    · exact Or.inl hold
    · exact absurd (hfail ▸ hl') (Lab.fail_not_mem_hiddenAPI m)
  · exact pre_flag_sub P hpre hs' m hm

/-! ### The budget invariant along a genuine execution -/

/-- Along a genuine own-flag execution, the flag set stays inside any set
containing the ids of all `fail` labels of the execution. -/
theorem exec_flag_sub (P : Params)
    {u₀ : (∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)}
    {L : List (Lab P.n × ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)))}
    (he : is_exec ⟨u₀, Seq.ofList L⟩ (ownFlagFlat P)) {A : Finset (Fin P.n)}
    (hA : ∀ p ∈ L, ∀ k : Fin P.n, p.1 = Lab.fail k → k ∈ A) :
    ∀ n s, (⟨u₀, Seq.ofList L⟩ :
        AlterSeq ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n))
          (Lab P.n)).stateAt n = some s →
      flagSet s.1 ⊆ A := by
  intro n
  induction n with
  | zero =>
    intro s hs
    obtain rfl : u₀ = s := Option.some.inj hs
    have hinit : (ownFlagFlat P).init = u₀ := he.2
    rw [← hinit]
    have hempty : flagSet ((ownFlagFlat P).init).1 = ∅ := by
      simp [flagSet, ownFlagFlat, ownFlagPre, ownFlagGroup, ABAProcU]
    rw [hempty]
    exact Finset.empty_subset A
  | succ k ih =>
    intro s hs
    obtain ⟨⟨l, s''⟩, h_get, h_snd⟩ : ∃ p, (Seq.ofList L).get? k = some p ∧ p.2 = s := by
      cases hg : (Seq.ofList L).get? k with
      | none =>
        rw [show (⟨u₀, Seq.ofList L⟩ : AlterSeq _ _).stateAt (k + 1)
            = ((Seq.ofList L).get? k).map Prod.snd from rfl, hg] at hs
        exact absurd hs (by simp)
      | some p =>
        rw [show (⟨u₀, Seq.ofList L⟩ : AlterSeq _ _).stateAt (k + 1)
            = ((Seq.ofList L).get? k).map Prod.snd from rfl, hg] at hs
        exact ⟨p, rfl, Option.some.inj hs⟩
    obtain ⟨s₀, μ, h_state, h_step, h_supp⟩ := he.1 k l s'' h_get
    subst h_snd
    intro m hmem
    rw [mem_flagSet] at hmem
    rcases step_flag_sub P h_step h_supp m hmem with hold | hfail
    · exact ih s₀ h_state ((mem_flagSet _ _).mpr hold)
    · refine hA (l, s'') (List.mem_iff_getElem?.mpr ⟨k, ?_⟩) m hfail
      rw [← Seq.ofList_get?]
      exact h_get

/-- At any terminated position of an `ofList` execution the reached state is
the end state of the list. -/
theorem stateAt_ofList_terminated {S L : Type} {s₀ : S} {M : List (L × S)}
    {n : ℕ} {s : S}
    (hterm : (⟨s₀, Seq.ofList M⟩ : AlterSeq S L).trans.TerminatedAt n)
    (hstate : (⟨s₀, Seq.ofList M⟩ : AlterSeq S L).stateAt n = some s) :
    s = AlterSeq.endStList s₀ M := by
  have hlen : M.length ≤ n := by
    by_contra hlt
    push Not at hlt
    have hnone : (Seq.ofList M).get? n = none := hterm
    rw [Seq.ofList_get?, List.getElem?_eq_getElem hlt] at hnone
    exact absurd hnone (by simp)
  cases n with
  | zero =>
    obtain rfl : M = [] := by
      cases M with
      | nil => rfl
      | cons x xs => simp at hlen
    rw [AlterSeq.endStList_nil]
    exact (Option.some.inj hstate).symm
  | succ m =>
    change ((Seq.ofList M).get? m).map Prod.snd = some s at hstate
    rw [Seq.ofList_get?] at hstate
    cases hMm : M[m]? with
    | none => rw [hMm] at hstate; exact absurd hstate (by simp)
    | some p =>
      rw [hMm] at hstate
      obtain ⟨hmlt, -⟩ := List.getElem?_eq_some_iff.mp hMm
      have hlen' : M.length = m + 1 := by omega
      have hlast : M.getLast? = some p := by
        rw [List.getLast?_eq_getElem?, hlen']
        simpa using hMm
      simp only [Option.map_some, Option.some.injEq] at hstate
      rw [← hstate]
      unfold AlterSeq.endStList
      rw [hlast]
      rfl

/-! ### Pruning a scheduler to the budgeted system -/

/-- The step-level budget condition, read off a history: it holds at every
terminated position of the history (there is at most one). -/
def histOK (P : Params)
    (e : AlterSeq ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n))
      (Lab P.n)) (l : Lab P.n) : Prop :=
  ∀ n s, e.trans.TerminatedAt n → e.stateAt n = some s → okLabel s l

open Classical in
/-- Replace an emission whose label breaks the budget at the current state by
a stop. -/
noncomputable def pruneEmit (P : Params)
    (e : AlterSeq ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n))
      (Lab P.n)) :
    Option (Lab P.n × PMF ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n))) →
      Option (Lab P.n × PMF ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)))
  | some (l, μ) => if histOK P e l then some (l, μ) else none
  | none => none

/-- An `ownFlagFlat` scheduler with the out-of-budget emissions pruned is an
`ownFlagFlatB` scheduler. -/
noncomputable def pruneSched (P : Params)
    (pe : ProbabilisticExecution (ownFlagFlat P)) : Scheduler (ownFlagFlatB P) where
  next e := (pe.scheduler.next e).map (pruneEmit P e)
  valid := by
    intro e n s hterm hstate l μ hsupp
    rw [PMF.mem_support_map_iff] at hsupp
    obtain ⟨o, ho, heq⟩ := hsupp
    cases o with
    | none => exact absurd heq (by simp [pruneEmit])
    | some lμ =>
      obtain ⟨l', μ'⟩ := lμ
      by_cases hok : histOK P e l'
      · rw [show pruneEmit P e (some (l', μ')) = some (l', μ') from by
          simp [pruneEmit, hok]] at heq
        rw [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact ⟨pe.scheduler.valid e n s hterm hstate _ _ ho, hok n s hterm hstate⟩
      · rw [show pruneEmit P e (some (l', μ')) = none from by
          simp [pruneEmit, hok]] at heq
        exact absurd heq (by simp)

/-- Pruning does not move the mass of an in-budget emission. -/
theorem prune_next_apply (P : Params)
    (pe : ProbabilisticExecution (ownFlagFlat P))
    (e : AlterSeq ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n))
      (Lab P.n))
    (l : Lab P.n)
    (μ : PMF ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)))
    (hok : histOK P e l) :
    ((pe.scheduler.next e).map (pruneEmit P e)) (some (l, μ))
      = pe.scheduler.next e (some (l, μ)) := by
  classical
  rw [PMF.map_apply, tsum_eq_single (some (l, μ)) ?_]
  · rw [show pruneEmit P e (some (l, μ)) = some (l, μ) from by simp [pruneEmit, hok],
      if_pos rfl]
  · intro o ho
    rcases o with _ | ⟨l', μ'⟩
    · simp [pruneEmit]
    · by_cases hok' : histOK P e l'
      · rw [show pruneEmit P e (some (l', μ')) = some (l', μ') from by
          simp [pruneEmit, hok']]
        rw [if_neg (fun hc => ho hc.symm)]
      · rw [show pruneEmit P e (some (l', μ')) = none from by simp [pruneEmit, hok']]
        simp

/-- Pruning preserves the one-step kernel at an in-budget label. -/
theorem prune_kernel_eq (P : Params)
    (pe : ProbabilisticExecution (ownFlagFlat P))
    (e : AlterSeq ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n))
      (Lab P.n))
    (a : Lab P.n × ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)))
    (hok : histOK P e a.1) :
    (⟨pe.initState, pruneSched P pe⟩ :
        ProbabilisticExecution (ownFlagFlatB P)).kernel e a = pe.kernel e a := by
  unfold ProbabilisticExecution.kernel
  refine tsum_congr fun μ => ?_
  change ((pe.scheduler.next e).map (pruneEmit P e)) (some (a.1, μ)) * μ a.2 = _
  rw [prune_next_apply P pe e a.1 μ hok]

/-- Pruning preserves the probability of every execution all of whose steps
are in budget. -/
theorem prune_probOf_eq (P : Params)
    (pe : ProbabilisticExecution (ownFlagFlat P)) :
    ∀ (L : List (Lab P.n × ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n))))
      (u₀ : (∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)),
      (∀ (M : List (Lab P.n × ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n))))
        (a : Lab P.n × ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)))
        (K : List (Lab P.n × ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)))),
        L = M ++ a :: K → okLabel (AlterSeq.endStList u₀ M) a.1) →
      (⟨pe.initState, pruneSched P pe⟩ :
          ProbabilisticExecution (ownFlagFlatB P)).probOf ⟨u₀, Seq.ofList L⟩
          (Seq.terminates_ofList L)
        = pe.probOf ⟨u₀, Seq.ofList L⟩ (Seq.terminates_ofList L) := by
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    intro u₀ _
    rw [(⟨pe.initState, pruneSched P pe⟩ :
        ProbabilisticExecution (ownFlagFlatB P)).probOf_congr
        ⟨u₀, Seq.ofList []⟩ ⟨u₀, Seq.nil⟩ (by rw [Seq.ofList_nil])
        (Seq.terminates_ofList []) Seq.terminates_nil,
      ProbabilisticExecution.probOf_nil,
      pe.probOf_congr ⟨u₀, Seq.ofList []⟩ ⟨u₀, Seq.nil⟩ (by rw [Seq.ofList_nil])
        (Seq.terminates_ofList []) Seq.terminates_nil,
      ProbabilisticExecution.probOf_nil]
    rfl
  | append_singleton M a ih =>
    intro u₀ hok
    have h_split : (Seq.ofList (M ++ [a]) :
          Seq (Lab P.n × ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n))))
        = (Seq.ofList M).append (Seq.cons a Seq.nil) := by
      rw [Seq.ofList_append, Seq.ofList_cons, Seq.ofList_nil]
    have hfinApp : ((Seq.ofList M).append (Seq.cons a Seq.nil) :
        Seq (Lab P.n × ((∀ _ : Fin P.n, ABANodeU P.n) ×
          (ℕ → WCC.SpecState P.n)))).Terminates :=
      h_split ▸ Seq.terminates_ofList (M ++ [a])
    have hokM : histOK P ⟨u₀, Seq.ofList M⟩ a.1 := by
      intro n s hterm hstate
      rw [stateAt_ofList_terminated hterm hstate]
      exact hok M a [] rfl
    rw [(⟨pe.initState, pruneSched P pe⟩ :
        ProbabilisticExecution (ownFlagFlatB P)).probOf_congr
        ⟨u₀, Seq.ofList (M ++ [a])⟩ ⟨u₀, (Seq.ofList M).append (Seq.cons a Seq.nil)⟩
        (by rw [h_split]) (Seq.terminates_ofList _) hfinApp,
      (⟨pe.initState, pruneSched P pe⟩ :
        ProbabilisticExecution (ownFlagFlatB P)).probOf_append_singleton u₀
        (Seq.ofList M) (Seq.terminates_ofList M) a hfinApp,
      pe.probOf_congr ⟨u₀, Seq.ofList (M ++ [a])⟩
        ⟨u₀, (Seq.ofList M).append (Seq.cons a Seq.nil)⟩
        (by rw [h_split]) (Seq.terminates_ofList _) hfinApp,
      pe.probOf_append_singleton u₀ (Seq.ofList M) (Seq.terminates_ofList M) a hfinApp,
      ih u₀ (fun M' a' K' hM' => hok M' a' (K' ++ [a])
        (by rw [hM', List.append_assoc, List.cons_append])),
      prune_kernel_eq P pe ⟨u₀, Seq.ofList M⟩ a hokM]

/-! ### The trace-level budget and the transfer -/

/-- **The trace-level corruption budget**: the processes named by the `fail`
labels of `t` form a set of at most `f` ids. -/
def BudgetTrace {n : ℕ} (f : ℕ) (t : Seq (Lab n)) : Prop :=
  ∃ A : Finset (Fin n), A.card ≤ f ∧ ∀ id : Fin n, Lab.fail id ∈ t → id ∈ A

/-- **Budgeted traces cost nothing.** A positive-probability trace of the
unrestricted own-flag hybrid that satisfies the budget keeps positive
probability under the pruned scheduler of the budgeted system: every `fail`
label of a witness execution appears in the trace, so the whole execution is
in budget and its probability is untouched by the pruning. -/
theorem traceProb_ne_zero_of_budget (P : Params)
    (pe : ProbabilisticExecution (ownFlagFlat P))
    (hinit : pe.initState = PMF.pure (ownFlagFlat P).init)
    (t : Seq (Lab P.n)) (hB : BudgetTrace P.f t)
    (hne : (ownFlagFlat P).traceProb pe t ≠ 0) :
    (ownFlagFlatB P).traceProb ⟨pe.initState, pruneSched P pe⟩ t ≠ 0 := by
  classical
  obtain ⟨A, hAcard, hAmem⟩ := hB
  unfold System.traceProb at hne
  obtain ⟨⟨e, hFin, htr, htight⟩, hprob⟩ :
      ∃ e : {e // e.trans.Terminates ∧ (ownFlagFlat P).trace e = t ∧
        (ownFlagFlat P).IsTight e}, pe.probOf e.1 e.2.1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (ENNReal.tsum_eq_zero.mpr hc)
  set L := e.trans.toList hFin with hL
  have hofl : Seq.ofList L = e.trans := Seq.ofList_toList e.trans hFin
  have heE : (⟨e.init, Seq.ofList L⟩ : AlterSeq _ _) = e := by
    cases e
    simp only [hofl]
  have hprob' : pe.probOf ⟨e.init, Seq.ofList L⟩ (Seq.terminates_ofList L) ≠ 0 := by
    rw [pe.probOf_congr ⟨e.init, Seq.ofList L⟩ e heE (Seq.terminates_ofList L) hFin]
    exact hprob
  have hexec : is_exec ⟨e.init, Seq.ofList L⟩ (ownFlagFlat P) :=
    is_exec_of_probOf_ne_zero pe hinit _ _ hprob'
  -- Every fail label of the execution is a fail label of the trace, hence in A.
  have hAL : ∀ p ∈ L, ∀ k : Fin P.n, p.1 = Lab.fail k → k ∈ A := by
    intro p hp k hk
    refine hAmem k ?_
    have htr' : (ownFlagFlat P).trace ⟨e.init, Seq.ofList L⟩ = t := by
      rw [heE]; exact htr
    rw [← htr']
    change Lab.fail k ∈
      (((Seq.ofList L).filter (fun q => ¬ (q.1 = Silent.τ))).map Prod.fst)
    rw [Seq.ofList_filter, Seq.map_ofList_pub, Seq_mem_ofList]
    refine List.mem_map.mpr
      ⟨p, List.mem_filter.mpr ⟨hp, @decide_eq_true _ (Classical.propDecidable _) ?_⟩, hk⟩
    rw [hk]
    simp
  -- Every step of the execution is in budget.
  have hokall :
      ∀ (M : List (Lab P.n × ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n))))
        (a : Lab P.n × ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)))
        (K : List (Lab P.n × ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)))),
        L = M ++ a :: K → okLabel (AlterSeq.endStList e.init M) a.1 := by
    intro M a K hsplit
    have hstate : (⟨e.init, Seq.ofList L⟩ : AlterSeq _ _).stateAt M.length
        = some (AlterSeq.endStList e.init M) := by
      rw [hsplit, AlterSeq.stateAt_ofList_append_le e.init M (a :: K) (le_refl _)]
      exact AlterSeq.stateAt_ofList_length e.init M
    have hsub : flagSet (AlterSeq.endStList e.init M).1 ⊆ A :=
      exec_flag_sub P hexec hAL M.length _ hstate
    intro k hk
    by_cases hf : ((AlterSeq.endStList e.init M).1 k).2.2 = true
    · exact Or.inl hf
    · refine Or.inr ?_
      have hkA : k ∈ A :=
        hAL a (by rw [hsplit]; exact List.mem_append_right M (List.mem_cons_self ..)) k hk
      have hknS : k ∉ flagSet (AlterSeq.endStList e.init M).1 :=
        fun hc => hf ((mem_flagSet _ _).mp hc)
      exact lt_of_lt_of_le
        (Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨k, hkA, hknS⟩))
        hAcard
  have hpB := prune_probOf_eq P pe L e.init hokall
  intro h0
  unfold System.traceProb at h0
  have hzero := ENNReal.tsum_eq_zero.mp h0 ⟨e, hFin, htr, htight⟩
  rw [(⟨pe.initState, pruneSched P pe⟩ :
      ProbabilisticExecution (ownFlagFlatB P)).probOf_congr e ⟨e.init, Seq.ofList L⟩
      heE.symm hFin (Seq.terminates_ofList L), hpB] at hzero
  exact hprob' hzero

/-! ### Headlines -/

/-- **Safety of the own-flag presentation**: every positive-probability trace
of the own-flag hybrid that respects the corruption budget satisfies Validity
and Agreement — the safety predicate of `Flat.flatABA_safe`, obtained by
composing the conservativity bridge with that theorem. -/
theorem ownFlagFlat_safe (P : Params) :
    ∀ D ∈ achievableTraceDists (ownFlagFlat P), ∀ t, D t ≠ 0 → BudgetTrace P.f t →
      ValidityTrace P t ∧ AgreementTrace t := by
  rintro D ⟨pe, hinit, hD⟩ t hne hB
  rw [← hD t] at hne
  have hBne := traceProb_ne_zero_of_budget P pe hinit t hB hne
  have hY := mapBeliefExec_traceProb inflateFull (ownFlagFlatB_bridge P)
    ⟨pe.initState, pruneSched P pe⟩ (inflateFull_init P) (by rw [hinit]; rfl) t
  refine Flat.flatABA_safe P
    ((flatHybrid P).traceProb
      (mapBeliefExec inflateFull (ownFlagFlatB_bridge P) ⟨pe.initState, pruneSched P pe⟩))
    ⟨_, mapBeliefExec_initState _ _ _, fun τ => rfl⟩ t ?_
  rw [hY]
  exact hBne

/-- **Trace conservativity of the own-flag presentation**: every
positive-probability trace of the own-flag hybrid that respects the
corruption budget has positive probability under an achievable trace
distribution of `ABA.hybridImpl` — the bridge composed with
`Flat.flatABA_atd`. -/
theorem ownFlagFlat_traces (P : Params) :
    ∀ D ∈ achievableTraceDists (ownFlagFlat P), ∀ t, D t ≠ 0 → BudgetTrace P.f t →
      ∃ D' ∈ achievableTraceDists (hybridImpl P), D' t ≠ 0 := by
  rintro D ⟨pe, hinit, hD⟩ t hne hB
  rw [← hD t] at hne
  have hBne := traceProb_ne_zero_of_budget P pe hinit t hB hne
  have hY := mapBeliefExec_traceProb inflateFull (ownFlagFlatB_bridge P)
    ⟨pe.initState, pruneSched P pe⟩ (inflateFull_init P) (by rw [hinit]; rfl) t
  refine ⟨(flatHybrid P).traceProb
      (mapBeliefExec inflateFull (ownFlagFlatB_bridge P) ⟨pe.initState, pruneSched P pe⟩),
    ?_, by rw [hY]; exact hBne⟩
  rw [← Flat.flatABA_atd P]
  exact ⟨_, mapBeliefExec_initState _ _ _, fun τ => rfl⟩

/-! ### Mechanical axiom firewall

Neither headline may acquire a `sorryAx` dependence. -/

/-- info: 'PLTS.ABA.OwnFlag.ownFlagFlat_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ownFlagFlat_safe

/-- info: 'PLTS.ABA.OwnFlag.ownFlagFlat_traces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ownFlagFlat_traces

end OwnFlag
end ABA
end PLTS
