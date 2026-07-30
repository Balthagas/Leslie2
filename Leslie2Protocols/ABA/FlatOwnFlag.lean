/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Main
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SyncProduct
import Leslie2Protocols.Framework.TraceSupport
import Leslie2.Simulation.TraceMap

/-!
# ABA with own corruption flags and a trace-level budget

The deployed reading of the protocol: one automaton per process, running that
process's code and nothing else, beside a single centralized box for the coin.
Each process carries a single Boolean corruption flag of its own and no copy
of the corrupted set, and the adversary flips flags freely — the `fail k`
broadcast raises `k`'s flag unconditionally, with no budget guard in the
state. The corruption budget `≤ f` is instead a hypothesis on traces
(`BudgetTrace`): the processes named by the `fail` labels of the trace form a
set of at most `f` ids.

`OwnFlag.ABAProcStepU P j` is the program of process `j`. Its state is one
`ABANodeU` — the round-loop record of the coordinator together with one
graded-agreement stage per round, and the process's one flag — and every
guard in its rule table reads that node and nothing else. The processes are
composed under full synchronisation (`System.syncProduct`); the two networks
the shared alphabet `Lab n` cannot name are carried by the auxiliary alphabet
`FlatNet n` and hidden by the composition, so the composite
`OwnFlag.ownFlagGroup` speaks exactly `Lab n`. The coin oracle
`WCC.specFamily` is the one component that is not a process: it stays a
separate factor beside the process group — the one box whose transitions are
not Dirac — and keeps its budget-guarded `corrupt`.

## The correspondence with the monolithic hybrid

`deflate`-style maps read the own-flag product as one monolithic state: the
round-`r` stage `deflStage u r` is assembled from the U-nodes' round-`r`
slices (receiver rows transposed into the monolithic `recv`), the core
`deflCore u` from the coordinator slices, and every copy of the corrupted set
becomes the one set `flagSet u` of currently flagged processes.

The budget is what makes the two `fail` rows correspond: the monolithic
`corrupt` is guarded by `k ∉ F ∧ |F| < f`, while the flag write is unguarded.
Both systems are therefore restricted to the steps whose `fail` labels are a
repeat or fired with budget headroom — `okLabel` on the own-flag side reads
the budget off the flags, `okLabelM` on the monolithic side reads the same
condition off the core's copy of `F`, and along `deflateFull` the core's `F`
*is* `flagSet u`, so the two restrictions name the same steps. Within the
restriction the guarded insert and the unguarded flag write agree (budget
headroom on a fresh corruption, idempotence on a repeat), and every other
rule matches guard for guard: `ownFlagFlatB` and `hybridImplB` are related by
a strong functional matching along `deflateFull` and its converse
(`ownFlagSim`, `ownFlagSimConverse`).

## Headlines

* `ownFlag_atd` — the budget-restricted own-flag hybrid and the
  budget-restricted monolithic hybrid achieve exactly the same trace
  distributions.
* `ownFlagFlat_safe` — every positive-probability trace of `ownFlagFlat P`
  satisfying `BudgetTrace P.f` satisfies Validity and Agreement: pruning the
  scheduler's out-of-budget emissions lands in `ownFlagFlatB`, the matching
  carries the execution into `hybridImplB`, forgetting the restriction lands
  in `hybridImpl`, and `ABA.main` applies.
* `ownFlagFlat_traces` — every such trace has positive probability under an
  achievable trace distribution of `ABA.hybridImpl P`, by the same route.

A positive-probability trace of the *unrestricted* own-flag system satisfying
`BudgetTrace P.f` is a trace of the budgeted system with the same positive
probability: every `fail` label of a witness execution appears in its trace,
so along such an execution the flag set stays inside the trace's fail set and
every `fail` step is a repeat or has budget headroom (`exec_flag_sub`);
pruning the scheduler's out-of-budget emissions (`pruneSched`) then leaves
the probability of that execution unchanged.
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

/-! ### The auxiliary alphabet -/

/-- The auxiliary (rendezvous) alphabet of the own-flag presentation: the
stage network round-tagged by the stage it belongs to, plus the DECIDED
network of the coordinator, which has no round. -/
inductive FlatNet (n : ℕ) : Type
  /-- Round-`r` stage delivery: sender `j` hands `m` to receiver `i`. -/
  | gnet (r : ℕ) (i j : Fin n) (m : GBCA.Msg)
  /-- DECIDED delivery: sender `j`'s `⟨DECIDED, b⟩` reaches receiver `i`. -/
  | dnet (i j : Fin n) (b : Bool)
  deriving DecidableEq

/-- The extended alphabet of the own-flag presentation. Its silent label is
`Sum.inl τ`, so every `Sum.inr` label is observable and hence hideable. -/
abbrev FLab (n : ℕ) : Type := Lab n ⊕ FlatNet n

/-- The rendezvous labels, hidden by the composition. -/
def flatNetLabels (n : ℕ) : Set (FLab n) := {l | ∃ e : FlatNet n, l = Sum.inr e}

@[simp] theorem inl_notMem_flatNetLabels {n : ℕ} (l : Lab n) :
    Sum.inl l ∉ flatNetLabels n := by
  simp [flatNetLabels]

@[simp] theorem inr_mem_flatNetLabels {n : ℕ} (e : FlatNet n) :
    Sum.inr e ∈ flatNetLabels n := ⟨e, rfl⟩

/-- The state of one own-flag flat process: the coordinator record and one
stage per round, both without corrupted-set copies, and one corruption flag
for the whole node. -/
abbrev ABANodeU (n : ℕ) : Type := CoreNodeU n × (ℕ → GBCA.ProcNodeU n) × Bool


/-! ### The rule table

Process `j`'s rules, splitting the alphabet by role exactly as the
monolithic composition's handshakes and stage rules do. Honest rules read
only the node's protocol fields; the Byzantine guards (round loop and
stage alike) read `fl = true`; the `fail k` row raises `k`'s own flag
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

/-- **The deployed system**: the `n` own-flag programs beside the coin
oracle, with the sub-protocol API hidden. -/
noncomputable def ownFlagFlat (P : Params) :
    System ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)) (Lab P.n) :=
  (ownFlagPre P).abstract (Lab.hiddenAPI P.n)
/-- The set of processes whose flag is raised. -/
def flagSet {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) : Finset (Fin n) :=
  Finset.univ.filter (fun k => (u k).2.2 = true)

@[simp] theorem mem_flagSet {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) (k : Fin n) :
    k ∈ flagSet u ↔ (u k).2.2 = true := by
  simp [flagSet]
/-! ### Reading the own-flag group's step relation -/

private theorem pure_inj {α : Type} {a b : α}
    (h : (PMF.pure a : PMF α) = PMF.pure b) : a = b := by
  have hm : a ∈ (PMF.pure b).support := by rw [← h]; simp
  simpa using hm

/-- The composite step relation of the own-flag group, unfolded to the
one-mover/broadcast case analysis of the synchronised product. -/
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
/-! ### The forward map

A product of own-flag nodes is read as one monolithic state by assembling
the record layers slice by slice: the round-`r` stage from the nodes'
round-`r` slices (receiver rows transposed into the monolithic `recv`), the
core from the coordinator slices, and every copy of the corrupted set is the
one set of currently flagged processes. -/

private theorem coreState_ext {n : ℕ} {a b : CoreState n}
    (h1 : a.procs = b.procs) (h2 : a.decidedSent = b.decidedSent)
    (h3 : a.decidedRecv = b.decidedRecv) (h4 : a.F = b.F) : a = b := by
  cases a; cases b
  cases h1; cases h2; cases h3; cases h4
  rfl

private theorem implState_ext {n : ℕ} {a b : GBCA.ImplState n}
    (h1 : a.proc = b.proc) (h2 : a.sent = b.sent)
    (h3 : a.recv = b.recv) (h4 : a.F = b.F) : a = b := by
  cases a; cases b
  cases h1; cases h2; cases h3; cases h4
  rfl

/-- The core half of the forward map. -/
def deflCore {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) : CoreState n where
  procs := fun j => (u j).1.proc
  decidedSent := fun j => (u j).1.decOut
  decidedRecv := fun i => (u i).1.decIn
  F := flagSet u

@[simp] theorem deflCore_procs {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) :
    (deflCore u).procs = fun j => (u j).1.proc := rfl
@[simp] theorem deflCore_decidedSent {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) :
    (deflCore u).decidedSent = fun j => (u j).1.decOut := rfl
@[simp] theorem deflCore_decidedRecv {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) :
    (deflCore u).decidedRecv = fun i => (u i).1.decIn := rfl
@[simp] theorem deflCore_F {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) :
    (deflCore u).F = flagSet u := rfl

/-- The round-`r` stage of the forward map. -/
def deflStage {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) (r : ℕ) : GBCA.ImplState n where
  proc := fun j => ((u j).2.1 r).proc
  sent := fun j => ((u j).2.1 r).out
  recv := fun i => ((u i).2.1 r).inbox
  F := flagSet u

@[simp] theorem deflStage_proc {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) (r : ℕ) :
    (deflStage u r).proc = fun j => ((u j).2.1 r).proc := rfl
@[simp] theorem deflStage_sent {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) (r : ℕ) :
    (deflStage u r).sent = fun j => ((u j).2.1 r).out := rfl
@[simp] theorem deflStage_recv {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) (r : ℕ) :
    (deflStage u r).recv = fun i => ((u i).2.1 r).inbox := rfl
@[simp] theorem deflStage_F {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) (r : ℕ) :
    (deflStage u r).F = flagSet u := rfl

/-- **The forward map** on a whole state: the deflated stages and core beside
the untouched coin oracle. -/
def deflateFull {P : Params}
    (s : (∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)) :
    (ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)) :=
  (fun r => deflStage s.1 r, deflCore s.1, s.2)

/-! #### Deltas of the forward map

Each rule's state update, read through the forward map: a one-node update
becomes the matching one-row monolithic update. All receipt counts transfer
definitionally, so only the update shapes need commutation lemmas. -/

theorem flagSet_update_of_flag_eq {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n)
    (j : Fin n) {nd : ABANodeU n} (h : nd.2.2 = (u j).2.2) :
    flagSet (Function.update u j nd) = flagSet u := by
  refine flagSet_congr fun m => ?_
  by_cases hm : m = j
  · subst hm; rw [Function.update_self, h]
  · rw [Function.update_of_ne hm]

/-- A node update at `j` that keeps the stage slices and the flag leaves
every deflated stage alone. -/
theorem deflStage_update_core {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n)
    (j : Fin n) (c' : CoreNodeU n) (r : ℕ) :
    deflStage (Function.update u j (c', (u j).2.1, (u j).2.2)) r = deflStage u r := by
  refine implState_ext ?_ ?_ ?_ (flagSet_update_of_flag_eq u j rfl)
  all_goals
    simp only [deflStage_proc, deflStage_sent, deflStage_recv]
    funext i
    by_cases hi : i = j
    · subst hi; rw [Function.update_self]
    · rw [Function.update_of_ne hi]

/-- The stage tuple of a core-only node update, as one function equality. -/
theorem deflStages_core {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n)
    (j : Fin n) (c' : CoreNodeU n) :
    (fun r => deflStage (Function.update u j (c', (u j).2.1, (u j).2.2)) r)
      = fun r => deflStage u r :=
  funext fun r => deflStage_update_core u j c' r

/-- A node update at `j` (arbitrary core replacement, flag kept) deflates the
core to the field-wise one-row update. -/
theorem deflCore_update {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n)
    (j : Fin n) (c' : CoreNodeU n) (g' : ℕ → GBCA.ProcNodeU n) :
    deflCore (Function.update u j (c', g', (u j).2.2))
      = { procs := Function.update (deflCore u).procs j c'.proc
          decidedSent := Function.update (deflCore u).decidedSent j c'.decOut
          decidedRecv := Function.update (deflCore u).decidedRecv j c'.decIn
          F := flagSet u } := by
  refine coreState_ext ?_ ?_ ?_ (flagSet_update_of_flag_eq u j rfl)
  all_goals
    simp only [deflCore_procs, deflCore_decidedSent, deflCore_decidedRecv]
    funext i
    by_cases hi : i = j
    · subst hi; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]

/-- A stage-only node update leaves the deflated core alone. -/
theorem deflCore_id {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n)
    (j : Fin n) (g' : ℕ → GBCA.ProcNodeU n) :
    deflCore (Function.update u j ((u j).1, g', (u j).2.2)) = deflCore u := by
  rw [deflCore_update]
  refine coreState_ext ?_ ?_ ?_ rfl
  all_goals
    simp only [deflCore_procs, deflCore_decidedSent, deflCore_decidedRecv]
    exact Function.update_eq_self j _

/-- A node update at `j` whose stage-`r` slice becomes `p'` (flag kept)
deflates stage `r` to the field-wise one-row update. -/
theorem deflStage_update_self {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n)
    (j : Fin n) (c' : CoreNodeU n) (r : ℕ) (p' : GBCA.ProcNodeU n) :
    deflStage (Function.update u j (c', Function.update (u j).2.1 r p', (u j).2.2)) r
      = { proc := Function.update (deflStage u r).proc j p'.proc
          sent := Function.update (deflStage u r).sent j p'.out
          recv := Function.update (deflStage u r).recv j p'.inbox
          F := flagSet u } := by
  refine implState_ext ?_ ?_ ?_ (flagSet_update_of_flag_eq u j rfl)
  all_goals
    simp only [deflStage_proc, deflStage_sent, deflStage_recv]
    funext i
    by_cases hi : i = j
    · subst hi
      rw [Function.update_self, Function.update_self]
      show _ = _
      rw [show ((c', Function.update (u i).2.1 r p', (u i).2.2) :
          ABANodeU n).2.1 = Function.update (u i).2.1 r p' from rfl,
        Function.update_self]
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]

/-- The same update leaves every other stage alone. -/
theorem deflStage_update_ne {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n)
    (j : Fin n) (c' : CoreNodeU n) (r : ℕ) (p' : GBCA.ProcNodeU n)
    {r' : ℕ} (h : r' ≠ r) :
    deflStage (Function.update u j (c', Function.update (u j).2.1 r p', (u j).2.2)) r'
      = deflStage u r' := by
  refine implState_ext ?_ ?_ ?_ (flagSet_update_of_flag_eq u j rfl)
  all_goals
    simp only [deflStage_proc, deflStage_sent, deflStage_recv]
    funext i
    by_cases hi : i = j
    · subst hi
      rw [Function.update_self]
      show _ = _
      rw [show ((c', Function.update (u i).2.1 r p', (u i).2.2) :
          ABANodeU n).2.1 = Function.update (u i).2.1 r p' from rfl,
        Function.update_of_ne h]
    · rw [Function.update_of_ne hi]

/-- The stage tuple of a stage-`r` node update, as the one-coordinate update
of the stage tuple. -/
theorem deflStages_update {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n)
    (j : Fin n) (c' : CoreNodeU n) (r : ℕ) (p' : GBCA.ProcNodeU n) :
    (fun r' => deflStage
        (Function.update u j (c', Function.update (u j).2.1 r p', (u j).2.2)) r')
      = Function.update (fun r' => deflStage u r') r
          (deflStage
            (Function.update u j (c', Function.update (u j).2.1 r p', (u j).2.2)) r) := by
  funext r'
  by_cases h : r' = r
  · subst h; rw [Function.update_self]
  · rw [Function.update_of_ne h, deflStage_update_ne u j c' r p' h]

/-! #### The deltas, operation by operation -/

theorem deflCore_setProc {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) (j : Fin n)
    (p : ProcCore n) (g' : ℕ → GBCA.ProcNodeU n) :
    deflCore (Function.update u j ((u j).1.setProc p, g', (u j).2.2))
      = (deflCore u).setProc j p := by
  rw [deflCore_update]
  refine coreState_ext rfl ?_ ?_ rfl
  · exact Function.update_eq_self j _
  · exact Function.update_eq_self j _

theorem deflCore_sendDec {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) (j : Fin n)
    (b : Bool) (g' : ℕ → GBCA.ProcNodeU n) :
    deflCore (Function.update u j ((u j).1.sendDec b, g', (u j).2.2))
      = (deflCore u).sendDecided j b := by
  rw [deflCore_update]
  refine coreState_ext ?_ rfl ?_ rfl
  · exact Function.update_eq_self j _
  · exact Function.update_eq_self j _

theorem deflCore_recvDec {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) (i k : Fin n)
    (b : Bool) (g' : ℕ → GBCA.ProcNodeU n) :
    deflCore (Function.update u i ((u i).1.recvDec k b, g', (u i).2.2))
      = (deflCore u).deliverDecided i k b := by
  rw [deflCore_update]
  refine coreState_ext ?_ ?_ rfl rfl
  · exact Function.update_eq_self i _
  · exact Function.update_eq_self i _

theorem deflCore_stepRound {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) (j : Fin n)
    (co : Bool) (g' : ℕ → GBCA.ProcNodeU n) :
    deflCore (Function.update u j ((u j).1.stepRound co, g', (u j).2.2))
      = (deflCore u).stepRound j co := by
  cases hlg : (u j).1.proc.lastGrade with
  | none =>
    have h1 : (u j).1.stepRound co = (u j).1.setProc { (u j).1.proc with
        est := some ((u j).1.proc.est.getD co), lastGrade := none,
        round := (u j).1.proc.round + 1, phase := .toCallG } := by
      unfold CoreNodeU.stepRound
      rw [hlg]
    have h2 : (deflCore u).stepRound j co = (deflCore u).setProc j { (u j).1.proc with
        est := some ((u j).1.proc.est.getD co), lastGrade := none,
        round := (u j).1.proc.round + 1, phase := .toCallG } := by
      unfold CoreState.stepRound
      rw [show ((deflCore u).procs j).lastGrade = none from hlg]
      rfl
    rw [h1, h2]
    exact deflCore_setProc u j _ g'
  | some out =>
    cases out with
    | A b =>
      have h1 : (u j).1.stepRound co = ((u j).1.sendDec b).setProc { (u j).1.proc with
          est := some ((u j).1.proc.est.getD co), lastGrade := none,
          round := (u j).1.proc.round + 1, phase := .toCallG } := by
        unfold CoreNodeU.stepRound
        rw [hlg]
      have h2 : (deflCore u).stepRound j co
          = ((deflCore u).sendDecided j b).setProc j { (u j).1.proc with
              est := some ((u j).1.proc.est.getD co), lastGrade := none,
              round := (u j).1.proc.round + 1, phase := .toCallG } := by
        unfold CoreState.stepRound
        rw [show ((deflCore u).procs j).lastGrade = some (.A b) from hlg]
        rfl
      rw [h1, h2, deflCore_update]
      refine coreState_ext rfl rfl ?_ rfl
      exact Function.update_eq_self j _
    | B b =>
      have h1 : (u j).1.stepRound co = (u j).1.setProc { (u j).1.proc with
          est := some ((u j).1.proc.est.getD co), lastGrade := none,
          round := (u j).1.proc.round + 1, phase := .toCallG } := by
        unfold CoreNodeU.stepRound
        rw [hlg]
      have h2 : (deflCore u).stepRound j co = (deflCore u).setProc j { (u j).1.proc with
          est := some ((u j).1.proc.est.getD co), lastGrade := none,
          round := (u j).1.proc.round + 1, phase := .toCallG } := by
        unfold CoreState.stepRound
        rw [show ((deflCore u).procs j).lastGrade = some (.B b) from hlg]
        rfl
      rw [h1, h2]
      exact deflCore_setProc u j _ g'
    | C =>
      have h1 : (u j).1.stepRound co = (u j).1.setProc { (u j).1.proc with
          est := some ((u j).1.proc.est.getD co), lastGrade := none,
          round := (u j).1.proc.round + 1, phase := .toCallG } := by
        unfold CoreNodeU.stepRound
        rw [hlg]
      have h2 : (deflCore u).stepRound j co = (deflCore u).setProc j { (u j).1.proc with
          est := some ((u j).1.proc.est.getD co), lastGrade := none,
          round := (u j).1.proc.round + 1, phase := .toCallG } := by
        unfold CoreState.stepRound
        rw [show ((deflCore u).procs j).lastGrade = some .C from hlg]
        rfl
      rw [h1, h2]
      exact deflCore_setProc u j _ g'

theorem deflStage_setP_send {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) (j : Fin n)
    (c' : CoreNodeU n) (r : ℕ) (pr : GBCA.ProcState) (m : GBCA.Msg) :
    deflStage (Function.update u j (c', Function.update (u j).2.1 r
        ((((u j).2.1 r).setP pr).send m), (u j).2.2)) r
      = ((deflStage u r).setProc j pr).mcast j m := by
  rw [deflStage_update_self]
  exact implState_ext rfl rfl (Function.update_eq_self j _) rfl

theorem deflStage_setP {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) (j : Fin n)
    (c' : CoreNodeU n) (r : ℕ) (pr : GBCA.ProcState) :
    deflStage (Function.update u j (c', Function.update (u j).2.1 r
        (((u j).2.1 r).setP pr), (u j).2.2)) r
      = (deflStage u r).setProc j pr := by
  rw [deflStage_update_self]
  exact implState_ext rfl (Function.update_eq_self j _) (Function.update_eq_self j _) rfl

theorem deflStage_send {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) (j : Fin n)
    (c' : CoreNodeU n) (r : ℕ) (m : GBCA.Msg) :
    deflStage (Function.update u j (c', Function.update (u j).2.1 r
        (((u j).2.1 r).send m), (u j).2.2)) r
      = (deflStage u r).mcast j m := by
  rw [deflStage_update_self]
  exact implState_ext (Function.update_eq_self j _) rfl (Function.update_eq_self j _) rfl

theorem deflStage_deliverTo {n : ℕ} (u : ∀ _ : Fin n, ABANodeU n) (i : Fin n)
    (c' : CoreNodeU n) (r : ℕ) (k : Fin n) (m : GBCA.Msg) :
    deflStage (Function.update u i (c', Function.update (u i).2.1 r
        (((u i).2.1 r).deliverTo k m), (u i).2.2)) r
      = (deflStage u r).recvMsg i k m := by
  rw [deflStage_update_self]
  exact implState_ext (Function.update_eq_self i _) (Function.update_eq_self i _) rfl rfl

/-! #### The fail row: guarded insert against unguarded flag write

Within budget — a repeat, or a fresh corruption with headroom — the
monolithic budget-guarded `corrupt` on a deflated state equals the deflation
of the unguarded flag write. -/

theorem deflCore_corrupt {P : Params} (u : ∀ _ : Fin P.n, ABANodeU P.n)
    (k : Fin P.n) (hOK : k ∈ flagSet u ∨ (flagSet u).card < P.f) :
    (deflCore u).corrupt P k
      = deflCore (fun m => ((u m).1, (u m).2.1, if k = m then true else (u m).2.2)) := by
  have hfs : flagSet (fun m => ((u m).1, (u m).2.1, if k = m then true else (u m).2.2))
      = insert k (flagSet u) :=
    flagSet_insert (fun m => rfl)
  refine coreState_ext ?_ ?_ ?_ ?_
  · rw [CoreState.corrupt_procs]; rfl
  · rw [CoreState.corrupt_decidedSent]; rfl
  · rw [CoreState.corrupt_decidedRecv]; rfl
  · show (CoreState.corrupt P k (deflCore u)).F = _
    unfold CoreState.corrupt
    by_cases hk : k ∈ flagSet u
    · rw [if_neg (by simp [hk])]
      exact (hfs.trans (Finset.insert_eq_self.mpr hk)).symm
    · rw [if_pos ⟨by simpa using hk, by simpa using hOK.resolve_left hk⟩]
      exact hfs.symm

theorem deflStage_corrupt {P : Params} (u : ∀ _ : Fin P.n, ABANodeU P.n)
    (r : ℕ) (k : Fin P.n) (hOK : k ∈ flagSet u ∨ (flagSet u).card < P.f) :
    (deflStage u r).corrupt P k
      = deflStage (fun m => ((u m).1, (u m).2.1, if k = m then true else (u m).2.2)) r := by
  have hfs : flagSet (fun m => ((u m).1, (u m).2.1, if k = m then true else (u m).2.2))
      = insert k (flagSet u) :=
    flagSet_insert (fun m => rfl)
  refine implState_ext ?_ ?_ ?_ ?_
  · rw [GBCA.ImplState.corrupt_proc]; rfl
  · rw [GBCA.ImplState.corrupt_sent]; rfl
  · rw [GBCA.ImplState.corrupt_recv]; rfl
  · show (GBCA.ImplState.corrupt P k (deflStage u r)).F = _
    unfold GBCA.ImplState.corrupt
    by_cases hk : k ∈ flagSet u
    · rw [if_neg (by simp [hk])]
      exact (hfs.trans (Finset.insert_eq_self.mpr hk)).symm
    · rw [if_pos ⟨by simpa using hk, by simpa using hOK.resolve_left hk⟩]
      exact hfs.symm

/-! ### One process's rules, by label class -/

section Inversion

variable {P : Params} {j : Fin P.n} {q : ABANodeU P.n} {ν : PMF (ABANodeU P.n)}

theorem stepU_callABA_own {b : Bool}
    (h : ABAProcStepU P j q (Sum.inl (.callABA j b)) ν) :
    (q.1.proc.input = none ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with
        input := some b, est := some b, round := 0, phase := .toCallG },
        q.2.1, q.2.2)) ∨
    ν = PMF.pure q := by
  cases h
  case input => exact Or.inl ⟨by assumption, rfl⟩
  case inputLoop => exact Or.inr rfl
  case callABAIdle => exact absurd rfl ‹_ ≠ j›

theorem stepU_callABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ABAProcStepU P j q (Sum.inl (.callABA id b)) ν) : ν = PMF.pure q := by
  cases h
  case input => exact absurd rfl hid
  case inputLoop => exact absurd rfl hid
  case callABAIdle => rfl

theorem stepU_retABA_own {b : Bool}
    (h : ABAProcStepU P j q (Sum.inl (.retABA j b)) ν) :
    P.n - P.f ≤ q.1.decidedCount b ∧ b ∈ q.1.decOut ∧ q.1.proc.returned = false ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with returned := true }, q.2.1, q.2.2) := by
  cases h
  case ret => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case retABAIdle => exact absurd rfl ‹_ ≠ j›

theorem stepU_retABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ABAProcStepU P j q (Sum.inl (.retABA id b)) ν) : ν = PMF.pure q := by
  cases h
  case ret => exact absurd rfl hid
  case retABAIdle => rfl

theorem stepU_callG_own {r : ℕ} {b : Bool}
    (h : ABAProcStepU P j q (Sum.inl (.callG r j b)) ν) :
    (q.1.proc.phase = .toCallG ∧ q.1.proc.round = r ∧ q.1.proc.est = some b ∧
      (((q.2.1 r).proc.input = none ∧
        ν = PMF.pure (q.1.setProc { q.1.proc with phase := .awaitG },
          Function.update q.2.1 r (((q.2.1 r).setP { (q.2.1 r).proc with
            input := some b,
            sentInput := Function.update (q.2.1 r).proc.sentInput b true }).send
              (.input b)),
          q.2.2))
       ∨ ν = PMF.pure (q.1.setProc { q.1.proc with phase := .awaitG },
          q.2.1, q.2.2))) ∨
    (q.2.2 = true ∧
      (((q.2.1 r).proc.input = none ∧
        ν = PMF.pure (q.1,
          Function.update q.2.1 r (((q.2.1 r).setP { (q.2.1 r).proc with
            input := some b,
            sentInput := Function.update (q.2.1 r).proc.sentInput b true }).send
              (.input b)),
          q.2.2))
       ∨ ν = PMF.pure q)) := by
  cases h
  case callG_call =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, Or.inl ⟨by assumption, rfl⟩⟩
  case callG_loop =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, Or.inr rfl⟩
  case callGByz_call => exact Or.inr ⟨by assumption, Or.inl ⟨by assumption, rfl⟩⟩
  case callGByz_loop => exact Or.inr ⟨by assumption, Or.inr rfl⟩
  case callGIdle => exact absurd rfl ‹_ ≠ j›

theorem stepU_callG_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ABAProcStepU P j q (Sum.inl (.callG r id b)) ν) : ν = PMF.pure q := by
  cases h
  case callG_call => exact absurd rfl hid
  case callG_loop => exact absurd rfl hid
  case callGByz_call => exact absurd rfl hid
  case callGByz_loop => exact absurd rfl hid
  case callGIdle => rfl

theorem stepU_retG_A_own {r : ℕ} {v : Bool}
    (h : ABAProcStepU P j q (Sum.inl (.retG r j (.A v))) ν) :
    P.n - P.f ≤ (q.2.1 r).recvCount (.seal (some v)) ∧ (q.2.1 r).proc.returned = false ∧
    ((q.1.proc.phase = .awaitG ∧ q.1.proc.round = r ∧
        ν = PMF.pure (q.1.setProc { q.1.proc with
            est := (GbcaOut.A v).est, lastGrade := some (.A v), phase := .toCallW },
          Function.update q.2.1 r ((q.2.1 r).setP { (q.2.1 r).proc with returned := true }),
          q.2.2)) ∨
      (q.2.2 = true ∧
        ν = PMF.pure (q.1,
          Function.update q.2.1 r ((q.2.1 r).setP { (q.2.1 r).proc with returned := true }),
          q.2.2))) := by
  cases h
  case retG_A =>
    exact ⟨by assumption, by assumption, Or.inl ⟨by assumption, by assumption, rfl⟩⟩
  case retGByz_A => exact ⟨by assumption, by assumption, Or.inr ⟨by assumption, rfl⟩⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›

theorem stepU_retG_B_own {r : ℕ} {v : Bool}
    (h : ABAProcStepU P j q (Sum.inl (.retG r j (.B v))) ν) :
    P.n - P.f ≤ (q.2.1 r).sealCount ∧
    (∃ k, GBCA.Msg.seal (some v) ∈ (q.2.1 r).inbox k) ∧
    P.f + 1 ≤ (q.2.1 r).recvCount (.bind (some v)) ∧ (q.2.1 r).bothValid P ∧
    (q.2.1 r).proc.returned = false ∧
    ((q.1.proc.phase = .awaitG ∧ q.1.proc.round = r ∧
        ν = PMF.pure (q.1.setProc { q.1.proc with
            est := (GbcaOut.B v).est, lastGrade := some (.B v), phase := .toCallW },
          Function.update q.2.1 r ((q.2.1 r).setP { (q.2.1 r).proc with returned := true }),
          q.2.2)) ∨
      (q.2.2 = true ∧
        ν = PMF.pure (q.1,
          Function.update q.2.1 r ((q.2.1 r).setP { (q.2.1 r).proc with returned := true }),
          q.2.2))) := by
  cases h
  case retG_B =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
      Or.inl ⟨by assumption, by assumption, rfl⟩⟩
  case retGByz_B =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
      Or.inr ⟨by assumption, rfl⟩⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›

theorem stepU_retG_C_own {r : ℕ}
    (h : ABAProcStepU P j q (Sum.inl (.retG r j .C)) ν) :
    P.n - P.f ≤ (q.2.1 r).recvCount (.seal none) ∧ (q.2.1 r).bothValid P ∧
    (q.2.1 r).proc.returned = false ∧
    ((q.1.proc.phase = .awaitG ∧ q.1.proc.round = r ∧
        ν = PMF.pure (q.1.setProc { q.1.proc with
            est := GbcaOut.C.est, lastGrade := some .C, phase := .toCallW },
          Function.update q.2.1 r ((q.2.1 r).setP { (q.2.1 r).proc with returned := true }),
          q.2.2)) ∨
      (q.2.2 = true ∧
        ν = PMF.pure (q.1,
          Function.update q.2.1 r ((q.2.1 r).setP { (q.2.1 r).proc with returned := true }),
          q.2.2))) := by
  cases h
  case retG_C =>
    exact ⟨by assumption, by assumption, by assumption,
      Or.inl ⟨by assumption, by assumption, rfl⟩⟩
  case retGByz_C =>
    exact ⟨by assumption, by assumption, by assumption, Or.inr ⟨by assumption, rfl⟩⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›

theorem stepU_retG_foreign {r : ℕ} {id : Fin P.n} {out : GbcaOut} (hid : id ≠ j)
    (h : ABAProcStepU P j q (Sum.inl (.retG r id out)) ν) : ν = PMF.pure q := by
  cases h
  case retG_A => exact absurd rfl hid
  case retG_B => exact absurd rfl hid
  case retG_C => exact absurd rfl hid
  case retGByz_A => exact absurd rfl hid
  case retGByz_B => exact absurd rfl hid
  case retGByz_C => exact absurd rfl hid
  case retGIdle => rfl

theorem stepU_callW_own {r : ℕ}
    (h : ABAProcStepU P j q (Sum.inl (.callW r j)) ν) :
    (q.1.proc.phase = .toCallW ∧ q.1.proc.round = r ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with phase := .awaitW }, q.2.1, q.2.2)) ∨
    (q.2.2 = true ∧ ν = PMF.pure q) := by
  cases h
  case callW => exact Or.inl ⟨by assumption, by assumption, rfl⟩
  case callWByz => exact Or.inr ⟨by assumption, rfl⟩
  case callWIdle => exact absurd rfl ‹_ ≠ j›

theorem stepU_callW_foreign {r : ℕ} {id : Fin P.n} (hid : id ≠ j)
    (h : ABAProcStepU P j q (Sum.inl (.callW r id)) ν) : ν = PMF.pure q := by
  cases h
  case callW => exact absurd rfl hid
  case callWByz => exact absurd rfl hid
  case callWIdle => rfl

theorem stepU_retW_own {r : ℕ} {co : Bool}
    (h : ABAProcStepU P j q (Sum.inl (.retW r j co)) ν) :
    (q.1.proc.phase = .awaitW ∧ q.1.proc.round = r ∧
      ν = PMF.pure (q.1.stepRound co, q.2.1, q.2.2)) ∨
    (q.2.2 = true ∧ ν = PMF.pure q) := by
  cases h
  case retW => exact Or.inl ⟨by assumption, by assumption, rfl⟩
  case retWByz => exact Or.inr ⟨by assumption, rfl⟩
  case retWIdle => exact absurd rfl ‹_ ≠ j›

theorem stepU_retW_foreign {r : ℕ} {id : Fin P.n} {co : Bool} (hid : id ≠ j)
    (h : ABAProcStepU P j q (Sum.inl (.retW r id co)) ν) : ν = PMF.pure q := by
  cases h
  case retW => exact absurd rfl hid
  case retWByz => exact absurd rfl hid
  case retWIdle => rfl

theorem stepU_dnet_inv {i k : Fin P.n} {b : Bool}
    (h : ABAProcStepU P j q (Sum.inr (.dnet i k b)) ν) :
    ν = PMF.pure (if j = i then (q.1.recvDec k b, q.2.1, q.2.2) else q) ∧
      (j = k → b ∈ q.1.decOut) ∧ (j = i → b ∉ q.1.decIn k) := by
  cases h
  case dnetSelf =>
    exact ⟨by rw [if_pos rfl], fun _ => by assumption, fun _ => by assumption⟩
  case dnetSend =>
    exact ⟨by rw [if_neg fun hc => ‹i ≠ j› hc.symm], fun _ => by assumption,
      fun hc => absurd hc.symm ‹i ≠ j›⟩
  case dnetRecv =>
    exact ⟨by rw [if_pos rfl], fun hc => absurd hc.symm ‹k ≠ j›, fun _ => by assumption⟩
  case dnetIdle =>
    exact ⟨by rw [if_neg fun hc => ‹i ≠ j› hc.symm], fun hc => absurd hc.symm ‹k ≠ j›,
      fun hc => absurd hc.symm ‹i ≠ j›⟩

theorem stepU_gnet_inv {r : ℕ} {i k : Fin P.n} {m : GBCA.Msg}
    (h : ABAProcStepU P j q (Sum.inr (.gnet r i k m)) ν) :
    ν = PMF.pure (if j = i then
        (q.1, Function.update q.2.1 r ((q.2.1 r).deliverTo k m), q.2.2) else q) ∧
      (j = k → m ∈ (q.2.1 r).out) := by
  cases h
  case gnetSelf => exact ⟨by rw [if_pos rfl], fun _ => by assumption⟩
  case gnetSend =>
    exact ⟨by rw [if_neg fun hc => ‹i ≠ j› hc.symm], fun _ => by assumption⟩
  case gnetRecv => exact ⟨by rw [if_pos rfl], fun hc => absurd hc.symm ‹k ≠ j›⟩
  case gnetIdle =>
    exact ⟨by rw [if_neg fun hc => ‹i ≠ j› hc.symm], fun hc => absurd hc.symm ‹k ≠ j›⟩

theorem stepU_tau_inv (h : ABAProcStepU P j q (Sum.inl .tau) ν) :
    (∃ b, P.f + 1 ≤ q.1.decidedCount b ∧ b ∉ q.1.decOut ∧
      ν = PMF.pure (q.1.sendDec b, q.2.1, q.2.2)) ∨
    (∃ b, q.2.2 = true ∧ ν = PMF.pure (q.1.sendDec b, q.2.1, q.2.2)) ∨
    (∃ r b, (q.2.1 r).proc.input ≠ none ∧ P.f + 1 ≤ (q.2.1 r).recvCount (.input b) ∧
      (q.2.1 r).proc.sentInput b = false ∧
      ν = PMF.pure (q.1, Function.update q.2.1 r (((q.2.1 r).setP { (q.2.1 r).proc with
        sentInput := Function.update (q.2.1 r).proc.sentInput b true }).send (.input b)),
        q.2.2)) ∨
    (∃ r b, (q.2.1 r).proc.input ≠ none ∧ P.n - P.f ≤ (q.2.1 r).recvCount (.input b) ∧
      (q.2.1 r).proc.sentEcho = none ∧
      ν = PMF.pure (q.1, Function.update q.2.1 r
        (((q.2.1 r).setP { (q.2.1 r).proc with sentEcho := some b }).send (.echo b)),
        q.2.2)) ∨
    (∃ r b, (q.2.1 r).proc.input ≠ none ∧ P.n - P.f ≤ (q.2.1 r).recvCount (.echo b) ∧
      (q.2.1 r).proc.sentVote = none ∧
      ν = PMF.pure (q.1, Function.update q.2.1 r
        (((q.2.1 r).setP { (q.2.1 r).proc with sentVote := some (some b) }).send
          (.vote (some b))),
        q.2.2)) ∨
    (∃ r, (q.2.1 r).proc.input ≠ none ∧ P.n - P.f ≤ (q.2.1 r).echoCount ∧
      (q.2.1 r).bothValid P ∧ (q.2.1 r).proc.sentVote = none ∧
      ν = PMF.pure (q.1, Function.update q.2.1 r
        (((q.2.1 r).setP { (q.2.1 r).proc with sentVote := some none }).send (.vote none)),
        q.2.2)) ∨
    (∃ r b, (q.2.1 r).proc.input ≠ none ∧
      P.n - P.f ≤ (q.2.1 r).recvCount (.vote (some b)) ∧
      (q.2.1 r).proc.sentBind = none ∧
      ν = PMF.pure (q.1, Function.update q.2.1 r
        (((q.2.1 r).setP { (q.2.1 r).proc with sentBind := some (some b) }).send
          (.bind (some b))),
        q.2.2)) ∨
    (∃ r, (q.2.1 r).proc.input ≠ none ∧ P.n - P.f ≤ (q.2.1 r).voteCount ∧
      (q.2.1 r).bothValid P ∧ (q.2.1 r).proc.sentBind = none ∧
      ν = PMF.pure (q.1, Function.update q.2.1 r
        (((q.2.1 r).setP { (q.2.1 r).proc with sentBind := some none }).send (.bind none)),
        q.2.2)) ∨
    (∃ r b, (q.2.1 r).proc.input ≠ none ∧
      P.n - P.f ≤ (q.2.1 r).recvCount (.bind (some b)) ∧
      (q.2.1 r).proc.sentSeal = none ∧
      ν = PMF.pure (q.1, Function.update q.2.1 r
        (((q.2.1 r).setP { (q.2.1 r).proc with sentSeal := some (some b) }).send
          (.seal (some b))),
        q.2.2)) ∨
    (∃ r, (q.2.1 r).proc.input ≠ none ∧ P.n - P.f ≤ (q.2.1 r).bindCount ∧
      (q.2.1 r).bothValid P ∧ (q.2.1 r).proc.sentSeal = none ∧
      ν = PMF.pure (q.1, Function.update q.2.1 r
        (((q.2.1 r).setP { (q.2.1 r).proc with sentSeal := some none }).send (.seal none)),
        q.2.2)) ∨
    (∃ r m, q.2.2 = true ∧
      ν = PMF.pure (q.1, Function.update q.2.1 r ((q.2.1 r).send m), q.2.2)) := by
  cases h
  case echo => exact Or.inl ⟨_, by assumption, by assumption, rfl⟩
  case byzDecided => exact Or.inr (Or.inl ⟨_, by assumption, rfl⟩)
  case stageRelay =>
    exact Or.inr (Or.inr (Or.inl
      ⟨_, _, by assumption, by assumption, by assumption, rfl⟩))
  case stageEcho =>
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨_, _, by assumption, by assumption, by assumption, rfl⟩)))
  case stageVoteBit =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨_, _, by assumption, by assumption, by assumption, rfl⟩))))
  case stageVoteBot =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨_, by assumption, by assumption, by assumption, by assumption, rfl⟩)))))
  case stageBindBit =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨_, _, by assumption, by assumption, by assumption, rfl⟩))))))
  case stageBindBot =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨_, by assumption, by assumption, by assumption, by assumption, rfl⟩)))))))
  case stageSealBit =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨_, _, by assumption, by assumption, by assumption, rfl⟩))))))))
  case stageSealBot =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨_, by assumption, by assumption, by assumption, by assumption, rfl⟩)))))))))
  case stageByz =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨_, _, by assumption, rfl⟩)))))))))

end Inversion

/-! ### Reading the stage family's step relation

The coin oracle is never unfolded: it occupies the same slot in both systems
and its transitions are passed through unchanged. Only the stage family needs
inversion. -/

section StageFamily

variable {P : Params} {g : ℕ → GBCA.ImplState P.n}

/-- A label no stage owns, other than corruption and `τ`, leaves the stage
family where it is. -/
theorem implFamily_idle_inv {l : Lab P.n} {μ : PMF (ℕ → GBCA.ImplState P.n)}
    (hown : l.gbcaRound = none) (hglob : ¬ Lab.isFail l) (hτ : l ≠ .tau)
    (h : (GBCA.implFamily P).step g l μ) : μ = PMF.pure g := by
  rcases h with ⟨hτ', -⟩ | ⟨r, hr, -⟩ | ⟨-, -, hg, -⟩ | ⟨-, -, -, rfl⟩
  · exact absurd hτ' hτ
  · rw [hown] at hr; exact absurd hr (by simp)
  · exact absurd hg hglob
  · rfl

theorem implFamily_idle_step {l : Lab P.n}
    (hown : l.gbcaRound = none) (hglob : ¬ Lab.isFail l) (hτ : l ≠ .tau) :
    (GBCA.implFamily P).step g l (PMF.pure g) :=
  Or.inr (Or.inr (Or.inr ⟨hτ, hown, hglob, rfl⟩))

/-- Corruption is a broadcast: every stage applies the same transform. -/
theorem implFamily_fail_inv {k : Fin P.n} {μ : PMF (ℕ → GBCA.ImplState P.n)}
    (h : (GBCA.implFamily P).step g (.fail k) μ) :
    μ = PMF.pure (fun r => (g r).corrupt P k) := by
  rcases h with ⟨hτ', -⟩ | ⟨r, hr, -⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, hg, -⟩
  · exact absurd hτ' (by simp)
  · exact absurd hr (by simp [Lab.gbcaRound])
  · rfl
  · exact absurd trivial hg

theorem implFamily_fail_step (k : Fin P.n) :
    (GBCA.implFamily P).step g (.fail k) (PMF.pure (fun r => (g r).corrupt P k)) :=
  Or.inr (Or.inr (Or.inl ⟨by simp, by simp [Lab.gbcaRound], trivial, rfl⟩))

/-- A label owned by round `r` moves that stage alone. -/
theorem implFamily_owned_inv {l : Lab P.n} {r : ℕ} {μ : PMF (ℕ → GBCA.ImplState P.n)}
    (hown : l.gbcaRound = some r) (hτ : l ≠ .tau)
    (h : (GBCA.implFamily P).step g l μ) :
    ∃ μr, GBCA.ImplStep P r (g r) l μr ∧ μ = μr.map (Function.update g r) := by
  rcases h with ⟨hτ', -⟩ | ⟨r', hr', μr, hstep, rfl⟩ | ⟨-, hn, -, -⟩ | ⟨-, hn, -, -⟩
  · exact absurd hτ' hτ
  · rw [hown] at hr'
    obtain rfl : r = r' := Option.some.inj hr'
    exact ⟨μr, hstep, rfl⟩
  · rw [hown] at hn; exact absurd hn (by simp)
  · rw [hown] at hn; exact absurd hn (by simp)

theorem implFamily_owned_step {l : Lab P.n} {r : ℕ} {x : GBCA.ImplState P.n}
    (hown : l.gbcaRound = some r) (h : GBCA.ImplStep P r (g r) l (PMF.pure x)) :
    (GBCA.implFamily P).step g l (PMF.pure (Function.update g r x)) :=
  Or.inr (Or.inl ⟨r, hown, PMF.pure x, h, by rw [PMF.pure_map]⟩)

/-- The self-loop instance of `implFamily_owned_step`. -/
theorem implFamily_owned_step_self {l : Lab P.n} {r : ℕ}
    (hown : l.gbcaRound = some r) (h : GBCA.ImplStep P r (g r) l (PMF.pure (g r))) :
    (GBCA.implFamily P).step g l (PMF.pure g) := by
  have hstep := implFamily_owned_step (g := g) hown h
  rwa [Function.update_eq_self] at hstep

/-- A silent transition of the stage family is one stage's own local send or
delivery. -/
theorem implFamily_tau_inv {μ : PMF (ℕ → GBCA.ImplState P.n)}
    (h : (GBCA.implFamily P).step g .tau μ) :
    ∃ r μr, GBCA.ImplStep P r (g r) .tau μr ∧ μ = μr.map (Function.update g r) := by
  rcases h with ⟨-, r, μr, hstep, rfl⟩ | ⟨r, hr, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · exact ⟨r, μr, hstep, rfl⟩
  · exact absurd hr (by simp [Lab.gbcaRound])
  · exact absurd rfl hn
  · exact absurd rfl hn

theorem implFamily_tau_step {r : ℕ} {x : GBCA.ImplState P.n}
    (h : GBCA.ImplStep P r (g r) .tau (PMF.pure x)) :
    (GBCA.implFamily P).step g .tau (PMF.pure (Function.update g r x)) :=
  Or.inl ⟨rfl, r, PMF.pure x, h, by rw [PMF.pure_map]⟩

end StageFamily

/-! ### Building and reading composite transitions -/

/-- A visible transition of the group: every process steps on `Sum.inl l`. -/
theorem ownGroup_visible_step (P : Params) (u : ∀ _ : Fin P.n, ABANodeU P.n)
    (l : Lab P.n) (hl : l ≠ .tau) (x : ∀ _ : Fin P.n, ABANodeU P.n)
    (hall : ∀ m, ABAProcStepU P m (u m) (Sum.inl l) (PMF.pure (x m))) :
    (ownFlagGroup P).step u l (PMF.pure x) :=
  (ownGroup_step_iff P u l _).mpr (Or.inr
    ((syncU_visible_iff P u (Sum.inl l) (by simpa using hl) _).mpr
      ⟨fun m => PMF.pure (x m), hall, (piPMFU_eq_pure fun _ => rfl).symm⟩))

/-- A silent transition of the group by one process's own `τ`-rule. -/
theorem ownGroup_tau_step (P : Params) (u : ∀ _ : Fin P.n, ABANodeU P.n)
    (i : Fin P.n) (y : ABANodeU P.n)
    (h : ABAProcStepU P i (u i) (Sum.inl .tau) (PMF.pure y)) :
    (ownFlagGroup P).step u .tau (PMF.pure (Function.update u i y)) :=
  (ownGroup_step_iff P u .tau _).mpr (Or.inr
    ((syncU_tau_iff P u _).mpr ⟨i, PMF.pure y, h, (piPMFU_update_eq_pure u i y).symm⟩))

/-- A hidden network rendezvous, which the shared alphabet sees as a `τ`. -/
theorem ownGroup_net_step (P : Params) (u : ∀ _ : Fin P.n, ABANodeU P.n)
    (e : FlatNet P.n) (x : ∀ _ : Fin P.n, ABANodeU P.n)
    (hall : ∀ m, ABAProcStepU P m (u m) (Sum.inr e) (PMF.pure (x m))) :
    (ownFlagGroup P).step u .tau (PMF.pure x) :=
  (ownGroup_step_iff P u .tau _).mpr (Or.inl ⟨rfl, e,
    (syncU_visible_iff P u (Sum.inr e) (by simp) _).mpr
      ⟨fun m => PMF.pure (x m), hall, (piPMFU_eq_pure fun _ => rfl).symm⟩⟩)

/-- The target of a synchronised move, read off componentwise. -/
private theorem sync_targetU {P : Params} {μ_ : Fin P.n → PMF (ABANodeU P.n)}
    {p' x : ∀ _ : Fin P.n, ABANodeU P.n}
    (hμ : (PMF.pure p' : PMF (∀ _ : Fin P.n, ABANodeU P.n)) = piPMF μ_)
    (h : ∀ m, μ_ m = PMF.pure (x m)) : p' = x := by
  rw [funext h, piPMF_pure] at hμ
  exact pure_inj hμ

/-- The target of an interleaved silent move. -/
private theorem interleave_targetU {P : Params} {p' x : ∀ _ : Fin P.n, ABANodeU P.n}
    {m : Fin P.n} {y : ABANodeU P.n}
    (hμ : (PMF.pure p' : PMF (∀ _ : Fin P.n, ABANodeU P.n))
      = piPMF (Function.update (fun k => PMF.pure (x k)) m (PMF.pure y))) :
    p' = Function.update x m y := by
  rw [piPMFU_update_eq_pure] at hμ
  exact pure_inj hμ

/-! ### The group layer, read forward

Every transition of the own-flag group deflates to the transition of the two
monolithic components it assembles. On a `fail` label the side condition is
the step-level budget: within it, the guarded insert and the flag write
agree. -/

/-- **Visible labels, read forward.** A synchronised transition of the
own-flag group on a label other than `τ` deflates to a stage-family
transition beside a core transition on the same label. -/
theorem group_of_ownGroup_visible (P : Params) {u p' : ∀ _ : Fin P.n, ABANodeU P.n}
    {l : Lab P.n} (hl : l ≠ .tau)
    (hOK : ∀ k, l = .fail k → k ∈ flagSet u ∨ (flagSet u).card < P.f)
    (h : (ownFlagGroup P).step u l (PMF.pure p')) :
    (GBCA.implFamily P).step (fun r => deflStage u r) l
        (PMF.pure (fun r => deflStage p' r)) ∧
      CoreStep P (deflCore u) l (PMF.pure (deflCore p')) := by
  rw [ownGroup_step_iff] at h
  rcases h with ⟨rfl, -, -⟩ | hs
  · exact absurd rfl hl
  rw [syncU_visible_iff P u (Sum.inl l) (by simpa using hl)] at hs
  obtain ⟨μ_, hall, hμ⟩ := hs
  cases l with
  | tau => exact absurd rfl hl
  | callABA id b =>
    rcases stepU_callABA_own (hall id) with ⟨hin, hd⟩ | hd
    · have hp' : p' = Function.update u id ((u id).1.setProc { (u id).1.proc with
          input := some b, est := some b, round := 0, phase := .toCallG },
          (u id).2.1, (u id).2.2) := by
        refine sync_targetU hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]; exact hd
        · rw [Function.update_of_ne hm]
          exact stepU_callABA_foreign (Ne.symm hm) (hall m)
      subst hp'
      refine ⟨?_, ?_⟩
      · rw [deflStages_core]
        exact implFamily_idle_step rfl (by simp [Lab.isFail]) hl
      · rw [deflCore_setProc]
        exact CoreStep.input _ id b hin
    · have hp' : p' = u := by
        refine sync_targetU hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; exact hd
        · exact stepU_callABA_foreign (Ne.symm hm) (hall m)
      subst hp'
      exact ⟨implFamily_idle_step rfl (by simp [Lab.isFail]) hl,
        CoreStep.inputLoop _ id b⟩
  | retABA id b =>
    obtain ⟨hcnt, hs', hret, hd⟩ := stepU_retABA_own (hall id)
    have hp' : p' = Function.update u id
        ((u id).1.setProc { (u id).1.proc with returned := true },
          (u id).2.1, (u id).2.2) := by
      refine sync_targetU hμ fun m => ?_
      by_cases hm : m = id
      · subst hm; rw [Function.update_self]; exact hd
      · rw [Function.update_of_ne hm]
        exact stepU_retABA_foreign (Ne.symm hm) (hall m)
    subst hp'
    refine ⟨?_, ?_⟩
    · rw [deflStages_core]
      exact implFamily_idle_step rfl (by simp [Lab.isFail]) hl
    · rw [deflCore_setProc]
      exact CoreStep.ret _ id b hcnt hs' hret
  | callG r id b =>
    rcases stepU_callG_own (hall id) with ⟨hph, hrd, hest, ⟨hin, hd⟩ | hd⟩
      | ⟨hF, ⟨hin, hd⟩ | hd⟩
    · have hp' : p' = Function.update u id
          ((u id).1.setProc { (u id).1.proc with phase := .awaitG },
            Function.update (u id).2.1 r ((((u id).2.1 r).setP { ((u id).2.1 r).proc with
              input := some b,
              sentInput := Function.update ((u id).2.1 r).proc.sentInput b true }).send
                (.input b)),
            (u id).2.2) := by
        refine sync_targetU hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]; exact hd
        · rw [Function.update_of_ne hm]
          exact stepU_callG_foreign (Ne.symm hm) (hall m)
      subst hp'
      refine ⟨?_, ?_⟩
      · rw [deflStages_update, deflStage_setP_send]
        exact implFamily_owned_step rfl (GBCA.ImplStep.call (deflStage u r) id b hin)
      · rw [deflCore_setProc]
        exact CoreStep.callG _ r id b hph hrd hest
    · have hp' : p' = Function.update u id
          ((u id).1.setProc { (u id).1.proc with phase := .awaitG },
            (u id).2.1, (u id).2.2) := by
        refine sync_targetU hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]; exact hd
        · rw [Function.update_of_ne hm]
          exact stepU_callG_foreign (Ne.symm hm) (hall m)
      subst hp'
      refine ⟨?_, ?_⟩
      · rw [deflStages_core]
        exact implFamily_owned_step_self (g := fun r' => deflStage u r') rfl
          (GBCA.ImplStep.callLoop (deflStage u r) id b)
      · rw [deflCore_setProc]
        exact CoreStep.callG _ r id b hph hrd hest
    · have hp' : p' = Function.update u id ((u id).1,
          Function.update (u id).2.1 r ((((u id).2.1 r).setP { ((u id).2.1 r).proc with
            input := some b,
            sentInput := Function.update ((u id).2.1 r).proc.sentInput b true }).send
              (.input b)),
          (u id).2.2) := by
        refine sync_targetU hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]; exact hd
        · rw [Function.update_of_ne hm]
          exact stepU_callG_foreign (Ne.symm hm) (hall m)
      subst hp'
      refine ⟨?_, ?_⟩
      · rw [deflStages_update, deflStage_setP_send]
        exact implFamily_owned_step rfl (GBCA.ImplStep.call (deflStage u r) id b hin)
      · rw [deflCore_id]
        exact CoreStep.callGByz _ r id b ((mem_flagSet u id).mpr hF)
    · have hp' : p' = u := by
        refine sync_targetU hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; exact hd
        · exact stepU_callG_foreign (Ne.symm hm) (hall m)
      rw [hp']
      exact ⟨implFamily_owned_step_self (g := fun r' => deflStage u r') rfl
          (GBCA.ImplStep.callLoop (deflStage u r) id b),
        CoreStep.callGByz _ r id b ((mem_flagSet u id).mpr hF)⟩
  | retG r id out =>
    cases out with
    | A v =>
      obtain ⟨hcnt, hret, hd⟩ := stepU_retG_A_own (hall id)
      rcases hd with ⟨hph, hrd, hd⟩ | ⟨hF, hd⟩
      · have hp' : p' = Function.update u id ((u id).1.setProc { (u id).1.proc with
            est := (GbcaOut.A v).est, lastGrade := some (.A v), phase := .toCallW },
            Function.update (u id).2.1 r (((u id).2.1 r).setP { ((u id).2.1 r).proc with
              returned := true }),
            (u id).2.2) := by
          refine sync_targetU hμ fun m => ?_
          by_cases hm : m = id
          · subst hm; rw [Function.update_self]; exact hd
          · rw [Function.update_of_ne hm]
            exact stepU_retG_foreign (Ne.symm hm) (hall m)
        subst hp'
        refine ⟨?_, ?_⟩
        · rw [deflStages_update, deflStage_setP]
          exact implFamily_owned_step rfl (GBCA.ImplStep.retA (deflStage u r) id v hcnt hret)
        · rw [deflCore_setProc]
          exact CoreStep.retG _ r id (.A v) hph hrd
      · have hp' : p' = Function.update u id ((u id).1,
            Function.update (u id).2.1 r (((u id).2.1 r).setP { ((u id).2.1 r).proc with
              returned := true }),
            (u id).2.2) := by
          refine sync_targetU hμ fun m => ?_
          by_cases hm : m = id
          · subst hm; rw [Function.update_self]; exact hd
          · rw [Function.update_of_ne hm]
            exact stepU_retG_foreign (Ne.symm hm) (hall m)
        subst hp'
        refine ⟨?_, ?_⟩
        · rw [deflStages_update, deflStage_setP]
          exact implFamily_owned_step rfl (GBCA.ImplStep.retA (deflStage u r) id v hcnt hret)
        · rw [deflCore_id]
          exact CoreStep.retGByz _ r id (.A v) ((mem_flagSet u id).mpr hF)
    | B v =>
      obtain ⟨hcnt, honce, hbind, hval, hret, hd⟩ := stepU_retG_B_own (hall id)
      rcases hd with ⟨hph, hrd, hd⟩ | ⟨hF, hd⟩
      · have hp' : p' = Function.update u id ((u id).1.setProc { (u id).1.proc with
            est := (GbcaOut.B v).est, lastGrade := some (.B v), phase := .toCallW },
            Function.update (u id).2.1 r (((u id).2.1 r).setP { ((u id).2.1 r).proc with
              returned := true }),
            (u id).2.2) := by
          refine sync_targetU hμ fun m => ?_
          by_cases hm : m = id
          · subst hm; rw [Function.update_self]; exact hd
          · rw [Function.update_of_ne hm]
            exact stepU_retG_foreign (Ne.symm hm) (hall m)
        subst hp'
        refine ⟨?_, ?_⟩
        · rw [deflStages_update, deflStage_setP]
          exact implFamily_owned_step rfl
            (GBCA.ImplStep.retB (deflStage u r) id v hcnt honce hbind hval hret)
        · rw [deflCore_setProc]
          exact CoreStep.retG _ r id (.B v) hph hrd
      · have hp' : p' = Function.update u id ((u id).1,
            Function.update (u id).2.1 r (((u id).2.1 r).setP { ((u id).2.1 r).proc with
              returned := true }),
            (u id).2.2) := by
          refine sync_targetU hμ fun m => ?_
          by_cases hm : m = id
          · subst hm; rw [Function.update_self]; exact hd
          · rw [Function.update_of_ne hm]
            exact stepU_retG_foreign (Ne.symm hm) (hall m)
        subst hp'
        refine ⟨?_, ?_⟩
        · rw [deflStages_update, deflStage_setP]
          exact implFamily_owned_step rfl
            (GBCA.ImplStep.retB (deflStage u r) id v hcnt honce hbind hval hret)
        · rw [deflCore_id]
          exact CoreStep.retGByz _ r id (.B v) ((mem_flagSet u id).mpr hF)
    | C =>
      obtain ⟨hcnt, hval, hret, hd⟩ := stepU_retG_C_own (hall id)
      rcases hd with ⟨hph, hrd, hd⟩ | ⟨hF, hd⟩
      · have hp' : p' = Function.update u id ((u id).1.setProc { (u id).1.proc with
            est := GbcaOut.C.est, lastGrade := some .C, phase := .toCallW },
            Function.update (u id).2.1 r (((u id).2.1 r).setP { ((u id).2.1 r).proc with
              returned := true }),
            (u id).2.2) := by
          refine sync_targetU hμ fun m => ?_
          by_cases hm : m = id
          · subst hm; rw [Function.update_self]; exact hd
          · rw [Function.update_of_ne hm]
            exact stepU_retG_foreign (Ne.symm hm) (hall m)
        subst hp'
        refine ⟨?_, ?_⟩
        · rw [deflStages_update, deflStage_setP]
          exact implFamily_owned_step rfl (GBCA.ImplStep.retC (deflStage u r) id hcnt hval hret)
        · rw [deflCore_setProc]
          exact CoreStep.retG _ r id .C hph hrd
      · have hp' : p' = Function.update u id ((u id).1,
            Function.update (u id).2.1 r (((u id).2.1 r).setP { ((u id).2.1 r).proc with
              returned := true }),
            (u id).2.2) := by
          refine sync_targetU hμ fun m => ?_
          by_cases hm : m = id
          · subst hm; rw [Function.update_self]; exact hd
          · rw [Function.update_of_ne hm]
            exact stepU_retG_foreign (Ne.symm hm) (hall m)
        subst hp'
        refine ⟨?_, ?_⟩
        · rw [deflStages_update, deflStage_setP]
          exact implFamily_owned_step rfl (GBCA.ImplStep.retC (deflStage u r) id hcnt hval hret)
        · rw [deflCore_id]
          exact CoreStep.retGByz _ r id .C ((mem_flagSet u id).mpr hF)
  | callW r id =>
    rcases stepU_callW_own (hall id) with ⟨hph, hrd, hd⟩ | ⟨hF, hd⟩
    · have hp' : p' = Function.update u id
          ((u id).1.setProc { (u id).1.proc with phase := .awaitW },
            (u id).2.1, (u id).2.2) := by
        refine sync_targetU hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]; exact hd
        · rw [Function.update_of_ne hm]
          exact stepU_callW_foreign (Ne.symm hm) (hall m)
      subst hp'
      refine ⟨?_, ?_⟩
      · rw [deflStages_core]
        exact implFamily_idle_step rfl (by simp [Lab.isFail]) hl
      · rw [deflCore_setProc]
        exact CoreStep.callW _ r id hph hrd
    · have hp' : p' = u := by
        refine sync_targetU hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; exact hd
        · exact stepU_callW_foreign (Ne.symm hm) (hall m)
      rw [hp']
      exact ⟨implFamily_idle_step rfl (by simp [Lab.isFail]) hl,
        CoreStep.callWByz _ r id ((mem_flagSet u id).mpr hF)⟩
  | retW r id co =>
    rcases stepU_retW_own (hall id) with ⟨hph, hrd, hd⟩ | ⟨hF, hd⟩
    · have hp' : p' = Function.update u id
          ((u id).1.stepRound co, (u id).2.1, (u id).2.2) := by
        refine sync_targetU hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]; exact hd
        · rw [Function.update_of_ne hm]
          exact stepU_retW_foreign (Ne.symm hm) (hall m)
      subst hp'
      refine ⟨?_, ?_⟩
      · rw [deflStages_core]
        exact implFamily_idle_step rfl (by simp [Lab.isFail]) hl
      · rw [deflCore_stepRound]
        exact CoreStep.retW _ r id co hph hrd
    · have hp' : p' = u := by
        refine sync_targetU hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; exact hd
        · exact stepU_retW_foreign (Ne.symm hm) (hall m)
      rw [hp']
      exact ⟨implFamily_idle_step rfl (by simp [Lab.isFail]) hl,
        CoreStep.retWByz _ r id co ((mem_flagSet u id).mpr hF)⟩
  | fail k =>
    have hp' : p' = fun m => ((u m).1, (u m).2.1, if k = m then true else (u m).2.2) :=
      sync_targetU hμ fun m => stepU_fail_inv (hall m)
    subst hp'
    refine ⟨?_, ?_⟩
    · rw [show (fun r => deflStage
          (fun m => ((u m).1, (u m).2.1, if k = m then true else (u m).2.2)) r)
          = fun r => (deflStage u r).corrupt P k from
        funext fun r => (deflStage_corrupt u r k (hOK k rfl)).symm]
      exact implFamily_fail_step k
    · rw [show deflCore (fun m => ((u m).1, (u m).2.1, if k = m then true else (u m).2.2))
          = (deflCore u).corrupt P k from (deflCore_corrupt u k (hOK k rfl)).symm]
      exact CoreStep.fail _ k

/-- **Silent labels, read forward.** A silent transition of the own-flag
group deflates to either a core silent rule — an interleaved send or a
hidden DECIDED rendezvous — or a stage-family silent rule. -/
theorem group_of_ownGroup_tau (P : Params) {u p' : ∀ _ : Fin P.n, ABANodeU P.n}
    (h : (ownFlagGroup P).step u .tau (PMF.pure p')) :
    ((fun r => deflStage p' r) = (fun r => deflStage u r) ∧
      CoreStep P (deflCore u) .tau (PMF.pure (deflCore p'))) ∨
    (deflCore p' = deflCore u ∧
      (GBCA.implFamily P).step (fun r => deflStage u r) .tau
        (PMF.pure (fun r => deflStage p' r))) := by
  rw [ownGroup_step_iff] at h
  rcases h with ⟨-, e, hs⟩ | hs
  · rw [syncU_visible_iff P u (Sum.inr e) (by simp)] at hs
    obtain ⟨μ_, hall, hμ⟩ := hs
    cases e with
    | gnet r i k m =>
      have hsent : m ∈ ((u k).2.1 r).out := (stepU_gnet_inv (hall k)).2 rfl
      have hp' : p' = Function.update u i ((u i).1,
          Function.update (u i).2.1 r (((u i).2.1 r).deliverTo k m), (u i).2.2) := by
        refine sync_targetU hμ fun m' => ?_
        rw [(stepU_gnet_inv (hall m')).1]
        by_cases hm : m' = i
        · subst hm; rw [if_pos rfl, Function.update_self]
        · rw [if_neg hm, Function.update_of_ne hm]
      subst hp'
      refine Or.inr ⟨deflCore_id u i _, ?_⟩
      rw [deflStages_update, deflStage_deliverTo]
      exact implFamily_tau_step (GBCA.ImplStep.deliver (deflStage u r) i k m hsent)
    | dnet i k b =>
      have hsent : b ∈ (u k).1.decOut := (stepU_dnet_inv (hall k)).2.1 rfl
      have hfresh : b ∉ (u i).1.decIn k := (stepU_dnet_inv (hall i)).2.2 rfl
      have hp' : p' = Function.update u i
          ((u i).1.recvDec k b, (u i).2.1, (u i).2.2) := by
        refine sync_targetU hμ fun m' => ?_
        rw [(stepU_dnet_inv (hall m')).1]
        by_cases hm : m' = i
        · subst hm; rw [if_pos rfl, Function.update_self]
        · rw [if_neg hm, Function.update_of_ne hm]
      subst hp'
      refine Or.inl ⟨deflStages_core u i _, ?_⟩
      rw [deflCore_recvDec]
      exact CoreStep.deliver (deflCore u) i k b hsent hfresh
  · rw [syncU_tau_iff] at hs
    obtain ⟨m, ν, hstep, hμ⟩ := hs
    rcases stepU_tau_inv hstep with
      ⟨b, hcnt, hsend, rfl⟩ | ⟨b, hF, rfl⟩ |
      ⟨r, b, hin, hcnt, hsend, rfl⟩ | ⟨r, b, hin, hcnt, hsend, rfl⟩ |
      ⟨r, b, hin, hcnt, hsend, rfl⟩ | ⟨r, hin, hcnt, hval, hsend, rfl⟩ |
      ⟨r, b, hin, hcnt, hsend, rfl⟩ | ⟨r, hin, hcnt, hval, hsend, rfl⟩ |
      ⟨r, b, hin, hcnt, hsend, rfl⟩ | ⟨r, hin, hcnt, hval, hsend, rfl⟩ |
      ⟨r, msg, hF, rfl⟩
    · obtain rfl := interleave_targetU (x := u) hμ
      refine Or.inl ⟨deflStages_core u m _, ?_⟩
      rw [deflCore_sendDec]
      exact CoreStep.echo (deflCore u) m b hcnt hsend
    · obtain rfl := interleave_targetU (x := u) hμ
      refine Or.inl ⟨deflStages_core u m _, ?_⟩
      rw [deflCore_sendDec]
      exact CoreStep.byzDecided (deflCore u) m b ((mem_flagSet u m).mpr hF)
    · obtain rfl := interleave_targetU (x := u) hμ
      refine Or.inr ⟨deflCore_id u m _, ?_⟩
      rw [deflStages_update, deflStage_setP_send]
      exact implFamily_tau_step (GBCA.ImplStep.relay (deflStage u r) m b hin hcnt hsend)
    · obtain rfl := interleave_targetU (x := u) hμ
      refine Or.inr ⟨deflCore_id u m _, ?_⟩
      rw [deflStages_update, deflStage_setP_send]
      exact implFamily_tau_step (GBCA.ImplStep.echo (deflStage u r) m b hin hcnt hsend)
    · obtain rfl := interleave_targetU (x := u) hμ
      refine Or.inr ⟨deflCore_id u m _, ?_⟩
      rw [deflStages_update, deflStage_setP_send]
      exact implFamily_tau_step (GBCA.ImplStep.voteBit (deflStage u r) m b hin hcnt hsend)
    · obtain rfl := interleave_targetU (x := u) hμ
      refine Or.inr ⟨deflCore_id u m _, ?_⟩
      rw [deflStages_update, deflStage_setP_send]
      exact implFamily_tau_step (GBCA.ImplStep.voteBot (deflStage u r) m hin hcnt hval hsend)
    · obtain rfl := interleave_targetU (x := u) hμ
      refine Or.inr ⟨deflCore_id u m _, ?_⟩
      rw [deflStages_update, deflStage_setP_send]
      exact implFamily_tau_step (GBCA.ImplStep.bindBit (deflStage u r) m b hin hcnt hsend)
    · obtain rfl := interleave_targetU (x := u) hμ
      refine Or.inr ⟨deflCore_id u m _, ?_⟩
      rw [deflStages_update, deflStage_setP_send]
      exact implFamily_tau_step (GBCA.ImplStep.bindBot (deflStage u r) m hin hcnt hval hsend)
    · obtain rfl := interleave_targetU (x := u) hμ
      refine Or.inr ⟨deflCore_id u m _, ?_⟩
      rw [deflStages_update, deflStage_setP_send]
      exact implFamily_tau_step (GBCA.ImplStep.sealBit (deflStage u r) m b hin hcnt hsend)
    · obtain rfl := interleave_targetU (x := u) hμ
      refine Or.inr ⟨deflCore_id u m _, ?_⟩
      rw [deflStages_update, deflStage_setP_send]
      exact implFamily_tau_step (GBCA.ImplStep.sealBot (deflStage u r) m hin hcnt hval hsend)
    · obtain rfl := interleave_targetU (x := u) hμ
      refine Or.inr ⟨deflCore_id u m _, ?_⟩
      rw [deflStages_update, deflStage_send]
      exact implFamily_tau_step
        (GBCA.ImplStep.byz (deflStage u r) m msg ((mem_flagSet u m).mpr hF))

/-! ### The group layer, read back

Every transition of the two monolithic components out of a deflated state is
reflected by an own-flag group transition whose target deflates to the
monolithic target. States whose copies of the corrupted set disagree are
outside the image of the forward map and never arise here. -/

/-- **Visible labels, read back.** -/
theorem ownGroup_visible_of_group (P : Params) {u : ∀ _ : Fin P.n, ABANodeU P.n}
    {g' : ℕ → GBCA.ImplState P.n} {c' : CoreState P.n} {l : Lab P.n} (hl : l ≠ .tau)
    (hOK : ∀ k, l = .fail k → k ∈ flagSet u ∨ (flagSet u).card < P.f)
    (hG : (GBCA.implFamily P).step (fun r => deflStage u r) l (PMF.pure g'))
    (hC : CoreStep P (deflCore u) l (PMF.pure c')) :
    ∃ u', (fun r => deflStage u' r) = g' ∧ deflCore u' = c' ∧
      (ownFlagGroup P).step u l (PMF.pure u') := by
  cases l with
  | tau => exact absurd rfl hl
  | callABA id b =>
    have hg' := pure_inj (implFamily_idle_inv rfl (by simp [Lab.isFail]) hl hG)
    rw [coreStep_callABA_iff] at hC
    rcases hC with ⟨hin, hc⟩ | hc
    · refine ⟨Function.update u id ((u id).1.setProc { (u id).1.proc with
          input := some b, est := some b, round := 0, phase := .toCallG },
          (u id).2.1, (u id).2.2), ?_, ?_, ?_⟩
      · rw [deflStages_core]
        exact hg'.symm
      · rw [deflCore_setProc]
        exact (pure_inj hc).symm
      · refine ownGroup_visible_step P u _ hl _ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]
          exact ABAProcStepU.input _ _ _ b hin
        · rw [Function.update_of_ne hm]
          exact ABAProcStepU.callABAIdle _ _ _ id b (Ne.symm hm)
    · refine ⟨u, hg'.symm, (pure_inj hc).symm, ?_⟩
      refine ownGroup_visible_step P u _ hl u fun m => ?_
      by_cases hm : m = id
      · subst hm; exact ABAProcStepU.inputLoop _ _ _ b
      · exact ABAProcStepU.callABAIdle _ _ _ id b (Ne.symm hm)
  | retABA id b =>
    have hg' := pure_inj (implFamily_idle_inv rfl (by simp [Lab.isFail]) hl hG)
    rw [coreStep_retABA_iff] at hC
    obtain ⟨hcnt, hs, hret, hc⟩ := hC
    refine ⟨Function.update u id ((u id).1.setProc { (u id).1.proc with returned := true },
        (u id).2.1, (u id).2.2), ?_, ?_, ?_⟩
    · rw [deflStages_core]
      exact hg'.symm
    · rw [deflCore_setProc]
      exact (pure_inj hc).symm
    · refine ownGroup_visible_step P u _ hl _ fun m => ?_
      by_cases hm : m = id
      · subst hm; rw [Function.update_self]
        exact ABAProcStepU.ret _ _ _ b hcnt hs hret
      · rw [Function.update_of_ne hm]
        exact ABAProcStepU.retABAIdle _ _ _ id b (Ne.symm hm)
  | callG r id b =>
    obtain ⟨μr, hx, heq⟩ := implFamily_owned_inv rfl hl hG
    rw [coreStep_callG_iff] at hC
    cases hx with
    | call =>
      rename_i hin
      rw [PMF.pure_map] at heq
      have hg' := pure_inj heq
      rcases hC with ⟨hph, hrd, hest, hc⟩ | ⟨hF, hc⟩
      · refine ⟨Function.update u id
            ((u id).1.setProc { (u id).1.proc with phase := .awaitG },
              Function.update (u id).2.1 r ((((u id).2.1 r).setP { ((u id).2.1 r).proc with
                input := some b,
                sentInput := Function.update ((u id).2.1 r).proc.sentInput b true }).send
                  (.input b)),
              (u id).2.2), ?_, ?_, ?_⟩
        · rw [deflStages_update, deflStage_setP_send]
          exact hg'.symm
        · rw [deflCore_setProc]
          exact (pure_inj hc).symm
        · refine ownGroup_visible_step P u _ hl _ fun m => ?_
          by_cases hm : m = id
          · subst hm; rw [Function.update_self]
            exact ABAProcStepU.callG_call _ _ _ r b hph hrd hest hin
          · rw [Function.update_of_ne hm]
            exact ABAProcStepU.callGIdle _ _ _ r id b (Ne.symm hm)
      · refine ⟨Function.update u id ((u id).1,
            Function.update (u id).2.1 r ((((u id).2.1 r).setP { ((u id).2.1 r).proc with
              input := some b,
              sentInput := Function.update ((u id).2.1 r).proc.sentInput b true }).send
                (.input b)),
            (u id).2.2), ?_, ?_, ?_⟩
        · rw [deflStages_update, deflStage_setP_send]
          exact hg'.symm
        · rw [deflCore_id]
          exact (pure_inj hc).symm
        · refine ownGroup_visible_step P u _ hl _ fun m => ?_
          by_cases hm : m = id
          · subst hm; rw [Function.update_self]
            exact ABAProcStepU.callGByz_call _ _ _ r b ((mem_flagSet u m).mp hF) hin
          · rw [Function.update_of_ne hm]
            exact ABAProcStepU.callGIdle _ _ _ r id b (Ne.symm hm)
    | callLoop =>
      rw [PMF.pure_map] at heq
      have hg' := pure_inj heq
      have hg2 : g' = fun r' => deflStage u r' := by
        rw [hg']
        exact Function.update_eq_self r (fun r' => deflStage u r')
      rcases hC with ⟨hph, hrd, hest, hc⟩ | ⟨hF, hc⟩
      · refine ⟨Function.update u id
            ((u id).1.setProc { (u id).1.proc with phase := .awaitG },
              (u id).2.1, (u id).2.2), ?_, ?_, ?_⟩
        · rw [deflStages_core]
          exact hg2.symm
        · rw [deflCore_setProc]
          exact (pure_inj hc).symm
        · refine ownGroup_visible_step P u _ hl _ fun m => ?_
          by_cases hm : m = id
          · subst hm; rw [Function.update_self]
            exact ABAProcStepU.callG_loop _ _ _ r b hph hrd hest
          · rw [Function.update_of_ne hm]
            exact ABAProcStepU.callGIdle _ _ _ r id b (Ne.symm hm)
      · refine ⟨u, hg2.symm, (pure_inj hc).symm, ?_⟩
        refine ownGroup_visible_step P u _ hl u fun m => ?_
        by_cases hm : m = id
        · subst hm
          exact ABAProcStepU.callGByz_loop _ _ _ r b ((mem_flagSet u m).mp hF)
        · exact ABAProcStepU.callGIdle _ _ _ r id b (Ne.symm hm)
  | retG r id out =>
    obtain ⟨μr, hx, heq⟩ := implFamily_owned_inv rfl hl hG
    rw [coreStep_retG_iff] at hC
    cases hx with
    | retA =>
      rename_i v hcnt hret
      rw [PMF.pure_map] at heq
      have hg' := pure_inj heq
      rcases hC with ⟨hph, hrd, hc⟩ | ⟨hF, hc⟩
      · refine ⟨Function.update u id ((u id).1.setProc { (u id).1.proc with
            est := (GbcaOut.A v).est, lastGrade := some (.A v), phase := .toCallW },
            Function.update (u id).2.1 r (((u id).2.1 r).setP { ((u id).2.1 r).proc with
              returned := true }),
            (u id).2.2), ?_, ?_, ?_⟩
        · rw [deflStages_update, deflStage_setP]
          exact hg'.symm
        · rw [deflCore_setProc]
          exact (pure_inj hc).symm
        · refine ownGroup_visible_step P u _ hl _ fun m => ?_
          by_cases hm : m = id
          · subst hm; rw [Function.update_self]
            exact ABAProcStepU.retG_A _ _ _ r v hph hrd hcnt hret
          · rw [Function.update_of_ne hm]
            exact ABAProcStepU.retGIdle _ _ _ r id _ (Ne.symm hm)
      · refine ⟨Function.update u id ((u id).1,
            Function.update (u id).2.1 r (((u id).2.1 r).setP { ((u id).2.1 r).proc with
              returned := true }),
            (u id).2.2), ?_, ?_, ?_⟩
        · rw [deflStages_update, deflStage_setP]
          exact hg'.symm
        · rw [deflCore_id]
          exact (pure_inj hc).symm
        · refine ownGroup_visible_step P u _ hl _ fun m => ?_
          by_cases hm : m = id
          · subst hm; rw [Function.update_self]
            exact ABAProcStepU.retGByz_A _ _ _ r v ((mem_flagSet u m).mp hF) hcnt hret
          · rw [Function.update_of_ne hm]
            exact ABAProcStepU.retGIdle _ _ _ r id _ (Ne.symm hm)
    | retB =>
      rename_i v hcnt honce hbind hval hret
      rw [PMF.pure_map] at heq
      have hg' := pure_inj heq
      rcases hC with ⟨hph, hrd, hc⟩ | ⟨hF, hc⟩
      · refine ⟨Function.update u id ((u id).1.setProc { (u id).1.proc with
            est := (GbcaOut.B v).est, lastGrade := some (.B v), phase := .toCallW },
            Function.update (u id).2.1 r (((u id).2.1 r).setP { ((u id).2.1 r).proc with
              returned := true }),
            (u id).2.2), ?_, ?_, ?_⟩
        · rw [deflStages_update, deflStage_setP]
          exact hg'.symm
        · rw [deflCore_setProc]
          exact (pure_inj hc).symm
        · refine ownGroup_visible_step P u _ hl _ fun m => ?_
          by_cases hm : m = id
          · subst hm; rw [Function.update_self]
            exact ABAProcStepU.retG_B _ _ _ r v hph hrd hcnt honce hbind hval hret
          · rw [Function.update_of_ne hm]
            exact ABAProcStepU.retGIdle _ _ _ r id _ (Ne.symm hm)
      · refine ⟨Function.update u id ((u id).1,
            Function.update (u id).2.1 r (((u id).2.1 r).setP { ((u id).2.1 r).proc with
              returned := true }),
            (u id).2.2), ?_, ?_, ?_⟩
        · rw [deflStages_update, deflStage_setP]
          exact hg'.symm
        · rw [deflCore_id]
          exact (pure_inj hc).symm
        · refine ownGroup_visible_step P u _ hl _ fun m => ?_
          by_cases hm : m = id
          · subst hm; rw [Function.update_self]
            exact ABAProcStepU.retGByz_B _ _ _ r v ((mem_flagSet u m).mp hF)
              hcnt honce hbind hval hret
          · rw [Function.update_of_ne hm]
            exact ABAProcStepU.retGIdle _ _ _ r id _ (Ne.symm hm)
    | retC =>
      rename_i hcnt hval hret
      rw [PMF.pure_map] at heq
      have hg' := pure_inj heq
      rcases hC with ⟨hph, hrd, hc⟩ | ⟨hF, hc⟩
      · refine ⟨Function.update u id ((u id).1.setProc { (u id).1.proc with
            est := GbcaOut.C.est, lastGrade := some .C, phase := .toCallW },
            Function.update (u id).2.1 r (((u id).2.1 r).setP { ((u id).2.1 r).proc with
              returned := true }),
            (u id).2.2), ?_, ?_, ?_⟩
        · rw [deflStages_update, deflStage_setP]
          exact hg'.symm
        · rw [deflCore_setProc]
          exact (pure_inj hc).symm
        · refine ownGroup_visible_step P u _ hl _ fun m => ?_
          by_cases hm : m = id
          · subst hm; rw [Function.update_self]
            exact ABAProcStepU.retG_C _ _ _ r hph hrd hcnt hval hret
          · rw [Function.update_of_ne hm]
            exact ABAProcStepU.retGIdle _ _ _ r id _ (Ne.symm hm)
      · refine ⟨Function.update u id ((u id).1,
            Function.update (u id).2.1 r (((u id).2.1 r).setP { ((u id).2.1 r).proc with
              returned := true }),
            (u id).2.2), ?_, ?_, ?_⟩
        · rw [deflStages_update, deflStage_setP]
          exact hg'.symm
        · rw [deflCore_id]
          exact (pure_inj hc).symm
        · refine ownGroup_visible_step P u _ hl _ fun m => ?_
          by_cases hm : m = id
          · subst hm; rw [Function.update_self]
            exact ABAProcStepU.retGByz_C _ _ _ r ((mem_flagSet u m).mp hF) hcnt hval hret
          · rw [Function.update_of_ne hm]
            exact ABAProcStepU.retGIdle _ _ _ r id _ (Ne.symm hm)
  | callW r id =>
    have hg' := pure_inj (implFamily_idle_inv rfl (by simp [Lab.isFail]) hl hG)
    rw [coreStep_callW_iff] at hC
    rcases hC with ⟨hph, hrd, hc⟩ | ⟨hF, hc⟩
    · refine ⟨Function.update u id
          ((u id).1.setProc { (u id).1.proc with phase := .awaitW },
            (u id).2.1, (u id).2.2), ?_, ?_, ?_⟩
      · rw [deflStages_core]
        exact hg'.symm
      · rw [deflCore_setProc]
        exact (pure_inj hc).symm
      · refine ownGroup_visible_step P u _ hl _ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]
          exact ABAProcStepU.callW _ _ _ r hph hrd
        · rw [Function.update_of_ne hm]
          exact ABAProcStepU.callWIdle _ _ _ r id (Ne.symm hm)
    · refine ⟨u, hg'.symm, (pure_inj hc).symm, ?_⟩
      refine ownGroup_visible_step P u _ hl u fun m => ?_
      by_cases hm : m = id
      · subst hm
        exact ABAProcStepU.callWByz _ _ _ r ((mem_flagSet u m).mp hF)
      · exact ABAProcStepU.callWIdle _ _ _ r id (Ne.symm hm)
  | retW r id co =>
    have hg' := pure_inj (implFamily_idle_inv rfl (by simp [Lab.isFail]) hl hG)
    rw [coreStep_retW_iff] at hC
    rcases hC with ⟨hph, hrd, hc⟩ | ⟨hF, hc⟩
    · refine ⟨Function.update u id ((u id).1.stepRound co, (u id).2.1, (u id).2.2),
        ?_, ?_, ?_⟩
      · rw [deflStages_core]
        exact hg'.symm
      · rw [deflCore_stepRound]
        exact (pure_inj hc).symm
      · refine ownGroup_visible_step P u _ hl _ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]
          exact ABAProcStepU.retW _ _ _ r co hph hrd
        · rw [Function.update_of_ne hm]
          exact ABAProcStepU.retWIdle _ _ _ r id co (Ne.symm hm)
    · refine ⟨u, hg'.symm, (pure_inj hc).symm, ?_⟩
      refine ownGroup_visible_step P u _ hl u fun m => ?_
      by_cases hm : m = id
      · subst hm
        exact ABAProcStepU.retWByz _ _ _ r co ((mem_flagSet u m).mp hF)
      · exact ABAProcStepU.retWIdle _ _ _ r id co (Ne.symm hm)
  | fail k =>
    have hOKk := hOK k rfl
    have hg' := pure_inj (implFamily_fail_inv hG)
    have hc' := pure_inj ((coreStep_fail_iff P _ k _).mp hC)
    refine ⟨fun m => ((u m).1, (u m).2.1, if k = m then true else (u m).2.2), ?_, ?_, ?_⟩
    · rw [hg']
      exact funext fun r => (deflStage_corrupt u r k hOKk).symm
    · rw [hc']
      exact (deflCore_corrupt u k hOKk).symm
    · refine ownGroup_visible_step P u _ hl _ fun m => ?_
      exact ABAProcStepU.fail _ _ _ k

/-- **The round loop's silent rules, read back.** -/
theorem ownGroup_tau_of_core (P : Params) {u : ∀ _ : Fin P.n, ABANodeU P.n}
    {c' : CoreState P.n} (hC : CoreStep P (deflCore u) .tau (PMF.pure c')) :
    ∃ u', (fun r => deflStage u' r) = (fun r => deflStage u r) ∧ deflCore u' = c' ∧
      (ownFlagGroup P).step u .tau (PMF.pure u') := by
  rw [coreStep_tau_iff] at hC
  rcases hC with ⟨i, k, b, hs, hr, hc⟩ | ⟨id, b, hcnt, hsent, hc⟩ | ⟨id, b, hF, hc⟩
  · refine ⟨Function.update u i ((u i).1.recvDec k b, (u i).2.1, (u i).2.2),
      deflStages_core u i _, ?_, ?_⟩
    · rw [deflCore_recvDec]
      exact (pure_inj hc).symm
    · refine ownGroup_net_step P u (.dnet i k b) _ fun m => ?_
      by_cases hmi : m = i
      · subst hmi
        rw [Function.update_self]
        by_cases hmk : m = k
        · subst hmk
          exact ABAProcStepU.dnetSelf _ _ _ b hs hr
        · exact ABAProcStepU.dnetRecv _ _ _ k b (Ne.symm hmk) hr
      · rw [Function.update_of_ne hmi]
        by_cases hmk : m = k
        · subst hmk
          exact ABAProcStepU.dnetSend _ _ _ i b (Ne.symm hmi) hs
        · exact ABAProcStepU.dnetIdle _ _ _ i k b (Ne.symm hmi) (Ne.symm hmk)
  · refine ⟨Function.update u id ((u id).1.sendDec b, (u id).2.1, (u id).2.2),
      deflStages_core u id _, ?_, ?_⟩
    · rw [deflCore_sendDec]
      exact (pure_inj hc).symm
    · exact ownGroup_tau_step P u id _ (ABAProcStepU.echo _ _ _ b hcnt hsent)
  · refine ⟨Function.update u id ((u id).1.sendDec b, (u id).2.1, (u id).2.2),
      deflStages_core u id _, ?_, ?_⟩
    · rw [deflCore_sendDec]
      exact (pure_inj hc).symm
    · exact ownGroup_tau_step P u id _
        (ABAProcStepU.byzDecided _ _ _ b ((mem_flagSet u id).mp hF))

/-- **A stage's silent rules, read back.** -/
theorem ownGroup_tau_of_impl (P : Params) {u : ∀ _ : Fin P.n, ABANodeU P.n}
    {g' : ℕ → GBCA.ImplState P.n}
    (hG : (GBCA.implFamily P).step (fun r => deflStage u r) .tau (PMF.pure g')) :
    ∃ u', (fun r => deflStage u' r) = g' ∧ deflCore u' = deflCore u ∧
      (ownFlagGroup P).step u .tau (PMF.pure u') := by
  obtain ⟨r, μr, hx, heq⟩ := implFamily_tau_inv hG
  cases hx with
  | deliver =>
    rename_i i k msg hmsg
    rw [PMF.pure_map] at heq
    have hg' := pure_inj heq
    refine ⟨Function.update u i ((u i).1,
        Function.update (u i).2.1 r (((u i).2.1 r).deliverTo k msg), (u i).2.2),
      ?_, deflCore_id u i _, ?_⟩
    · rw [deflStages_update, deflStage_deliverTo]
      exact hg'.symm
    · refine ownGroup_net_step P u (.gnet r i k msg) _ fun m => ?_
      by_cases hmi : m = i
      · subst hmi
        rw [Function.update_self]
        by_cases hmk : m = k
        · subst hmk
          exact ABAProcStepU.gnetSelf _ _ _ r msg hmsg
        · exact ABAProcStepU.gnetRecv _ _ _ r k msg (Ne.symm hmk)
      · rw [Function.update_of_ne hmi]
        by_cases hmk : m = k
        · subst hmk
          exact ABAProcStepU.gnetSend _ _ _ r i msg (Ne.symm hmi) hmsg
        · exact ABAProcStepU.gnetIdle _ _ _ r i k msg (Ne.symm hmi) (Ne.symm hmk)
  | relay =>
    rename_i x b hin hcnt hsend
    rw [PMF.pure_map] at heq
    have hg' := pure_inj heq
    refine ⟨Function.update u x ((u x).1, Function.update (u x).2.1 r
        ((((u x).2.1 r).setP { ((u x).2.1 r).proc with
          sentInput := Function.update ((u x).2.1 r).proc.sentInput b true }).send
            (.input b)),
        (u x).2.2), ?_, deflCore_id u x _, ?_⟩
    · rw [deflStages_update, deflStage_setP_send]
      exact hg'.symm
    · exact ownGroup_tau_step P u x _ (ABAProcStepU.stageRelay _ _ _ r b hin hcnt hsend)
  | echo =>
    rename_i x b hin hcnt hsend
    rw [PMF.pure_map] at heq
    have hg' := pure_inj heq
    refine ⟨Function.update u x ((u x).1, Function.update (u x).2.1 r
        ((((u x).2.1 r).setP { ((u x).2.1 r).proc with sentEcho := some b }).send
          (.echo b)),
        (u x).2.2), ?_, deflCore_id u x _, ?_⟩
    · rw [deflStages_update, deflStage_setP_send]
      exact hg'.symm
    · exact ownGroup_tau_step P u x _ (ABAProcStepU.stageEcho _ _ _ r b hin hcnt hsend)
  | voteBit =>
    rename_i x b hin hcnt hsend
    rw [PMF.pure_map] at heq
    have hg' := pure_inj heq
    refine ⟨Function.update u x ((u x).1, Function.update (u x).2.1 r
        ((((u x).2.1 r).setP { ((u x).2.1 r).proc with sentVote := some (some b) }).send
          (.vote (some b))),
        (u x).2.2), ?_, deflCore_id u x _, ?_⟩
    · rw [deflStages_update, deflStage_setP_send]
      exact hg'.symm
    · exact ownGroup_tau_step P u x _ (ABAProcStepU.stageVoteBit _ _ _ r b hin hcnt hsend)
  | voteBot =>
    rename_i x hin hcnt hval hsend
    rw [PMF.pure_map] at heq
    have hg' := pure_inj heq
    refine ⟨Function.update u x ((u x).1, Function.update (u x).2.1 r
        ((((u x).2.1 r).setP { ((u x).2.1 r).proc with sentVote := some none }).send
          (.vote none)),
        (u x).2.2), ?_, deflCore_id u x _, ?_⟩
    · rw [deflStages_update, deflStage_setP_send]
      exact hg'.symm
    · exact ownGroup_tau_step P u x _
        (ABAProcStepU.stageVoteBot _ _ _ r hin hcnt hval hsend)
  | bindBit =>
    rename_i x b hin hcnt hsend
    rw [PMF.pure_map] at heq
    have hg' := pure_inj heq
    refine ⟨Function.update u x ((u x).1, Function.update (u x).2.1 r
        ((((u x).2.1 r).setP { ((u x).2.1 r).proc with sentBind := some (some b) }).send
          (.bind (some b))),
        (u x).2.2), ?_, deflCore_id u x _, ?_⟩
    · rw [deflStages_update, deflStage_setP_send]
      exact hg'.symm
    · exact ownGroup_tau_step P u x _ (ABAProcStepU.stageBindBit _ _ _ r b hin hcnt hsend)
  | bindBot =>
    rename_i x hin hcnt hval hsend
    rw [PMF.pure_map] at heq
    have hg' := pure_inj heq
    refine ⟨Function.update u x ((u x).1, Function.update (u x).2.1 r
        ((((u x).2.1 r).setP { ((u x).2.1 r).proc with sentBind := some none }).send
          (.bind none)),
        (u x).2.2), ?_, deflCore_id u x _, ?_⟩
    · rw [deflStages_update, deflStage_setP_send]
      exact hg'.symm
    · exact ownGroup_tau_step P u x _
        (ABAProcStepU.stageBindBot _ _ _ r hin hcnt hval hsend)
  | sealBit =>
    rename_i x b hin hcnt hsend
    rw [PMF.pure_map] at heq
    have hg' := pure_inj heq
    refine ⟨Function.update u x ((u x).1, Function.update (u x).2.1 r
        ((((u x).2.1 r).setP { ((u x).2.1 r).proc with sentSeal := some (some b) }).send
          (.seal (some b))),
        (u x).2.2), ?_, deflCore_id u x _, ?_⟩
    · rw [deflStages_update, deflStage_setP_send]
      exact hg'.symm
    · exact ownGroup_tau_step P u x _ (ABAProcStepU.stageSealBit _ _ _ r b hin hcnt hsend)
  | sealBot =>
    rename_i x hin hcnt hval hsend
    rw [PMF.pure_map] at heq
    have hg' := pure_inj heq
    refine ⟨Function.update u x ((u x).1, Function.update (u x).2.1 r
        ((((u x).2.1 r).setP { ((u x).2.1 r).proc with sentSeal := some none }).send
          (.seal none)),
        (u x).2.2), ?_, deflCore_id u x _, ?_⟩
    · rw [deflStages_update, deflStage_setP_send]
      exact hg'.symm
    · exact ownGroup_tau_step P u x _
        (ABAProcStepU.stageSealBot _ _ _ r hin hcnt hval hsend)
  | byz =>
    rename_i x msg hF
    rw [PMF.pure_map] at heq
    have hg' := pure_inj heq
    refine ⟨Function.update u x ((u x).1, Function.update (u x).2.1 r
        (((u x).2.1 r).send msg), (u x).2.2), ?_, deflCore_id u x _, ?_⟩
    · rw [deflStages_update, deflStage_send]
      exact hg'.symm
    · exact ownGroup_tau_step P u x _
        (ABAProcStepU.stageByz _ _ _ r msg ((mem_flagSet u x).mp hF))

/-! ### The outer layer: the coin oracle beside the group

The coin box occupies the same slot in both systems and is never unfolded:
on a visible label it is carried through the synchronisation untouched, and
its own resolution appears on both sides as the same pushforward of
`Params.wccPMF`. -/

/-- The system whose sub-protocol API `hybridImpl` hides: the stage family
beside the round loop and the coin oracle. -/
noncomputable def hybridPre (P : Params) :
    System ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))
      (Lab P.n) :=
  (GBCA.implFamily P).parallel (context P)

theorem hybridImpl_eq (P : Params) :
    hybridImpl P = (hybridPre P).abstract (Lab.hiddenAPI P.n) := rfl

private theorem prodPMF_pure_pure {α β : Type} (a : α) (b : β) :
    prodPMF (PMF.pure a) (PMF.pure b) = PMF.pure (a, b) := by
  rw [prodPMF_pure_left, PMF.pure_map]

private theorem map_deflateFull_prod {P : Params} (u : ∀ _ : Fin P.n, ABANodeU P.n)
    (μ_w : PMF (ℕ → WCC.SpecState P.n)) :
    (prodPMF (PMF.pure u) μ_w).map deflateFull
      = prodPMF (PMF.pure (fun r => deflStage u r))
          (prodPMF (PMF.pure (deflCore u)) μ_w) := by
  rw [prodPMF_pure_left, prodPMF_pure_left, prodPMF_pure_left, PMF.map_comp, PMF.map_comp]
  rfl

/-- **Every pre-abstraction own-flag transition is the matching monolithic
transition** along the forward map, given the step-level budget on `fail`
labels. -/
theorem hybridPre_step_of_ownPre (P : Params)
    {s : (∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)} {l : Lab P.n}
    {μ : PMF ((∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n))}
    (h : (ownFlagPre P).step s l μ)
    (hOK : ∀ k, l = .fail k → k ∈ flagSet s.1 ∨ (flagSet s.1).card < P.f) :
    (hybridPre P).step (deflateFull s) l (μ.map deflateFull) := by
  obtain ⟨u, w⟩ := s
  rcases h with ⟨hl, μ₁, μ₂, h1, h2, rfl⟩ | ⟨rfl, μ₁, h1, rfl⟩ | ⟨rfl, μ₂, h2, rfl⟩
  · -- A visible label: the group and the coin box move together.
    obtain ⟨p', rfl⟩ := ownFlagGroup_isLTS P _ _ _ h1
    obtain ⟨hG, hC⟩ := group_of_ownGroup_visible P hl hOK h1
    exact Or.inl ⟨hl, PMF.pure (fun r => deflStage p' r),
      prodPMF (PMF.pure (deflCore p')) μ₂, hG,
      Or.inl ⟨hl, PMF.pure (deflCore p'), μ₂, hC, h2, rfl⟩,
      map_deflateFull_prod p' μ₂⟩
  · -- The group's own silent rule: a core rule or a stage rule.
    obtain ⟨p', rfl⟩ := ownFlagGroup_isLTS P _ _ _ h1
    rcases group_of_ownGroup_tau P h1 with ⟨hgs, hC⟩ | ⟨hcs, hG⟩
    · have heq : (prodPMF (PMF.pure p') (PMF.pure w)).map deflateFull
          = prodPMF (PMF.pure (fun r => deflStage u r))
              (prodPMF (PMF.pure (deflCore p')) (PMF.pure w)) := by
        rw [prodPMF_pure_pure, PMF.pure_map, prodPMF_pure_pure, prodPMF_pure_pure, ← hgs]
        rfl
      exact Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure (deflCore p')) (PMF.pure w),
        Or.inr (Or.inl ⟨rfl, PMF.pure (deflCore p'), hC, rfl⟩), heq⟩)
    · have heq : (prodPMF (PMF.pure p') (PMF.pure w)).map deflateFull
          = prodPMF (PMF.pure (fun r => deflStage p' r))
              (PMF.pure ((deflCore u, w) :
                CoreState P.n × (ℕ → WCC.SpecState P.n))) := by
        rw [prodPMF_pure_pure, PMF.pure_map, prodPMF_pure_pure, ← hcs]
        rfl
      exact Or.inr (Or.inl ⟨rfl, PMF.pure (fun r => deflStage p' r), hG, heq⟩)
  · -- The coin resolution: the same pushforward on both sides.
    exact Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure (deflCore u)) μ₂,
      Or.inr (Or.inr ⟨rfl, μ₂, h2, rfl⟩), map_deflateFull_prod u μ₂⟩)

/-- **Every monolithic transition from a deflated state is the matching
own-flag transition**, distributions pushed forward. -/
theorem ownPre_step_of_hybridPre (P : Params)
    {s : (∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)} {l : Lab P.n}
    {μ : PMF ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))}
    (h : (hybridPre P).step (deflateFull s) l μ)
    (hOK : ∀ k, l = .fail k → k ∈ flagSet s.1 ∨ (flagSet s.1).card < P.f) :
    ∃ ν, (ownFlagPre P).step s l ν ∧ μ = ν.map deflateFull := by
  obtain ⟨u, w⟩ := s
  rcases h with ⟨hl, μ₁, μ₂₃, hG, hCW, rfl⟩ | ⟨rfl, μ₁, hG, rfl⟩ | ⟨rfl, μ₂₃, hCW, rfl⟩
  · -- A visible label.
    obtain ⟨g', rfl⟩ := GBCA.implFamily_isLTS P _ _ _ hG
    rcases hCW with ⟨-, μ₂, μ_w, hC, hW, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
    · obtain ⟨c', rfl⟩ := core_isLTS P _ _ _ hC
      obtain ⟨u', hgs, hcs, hstep⟩ := ownGroup_visible_of_group P hl hOK hG hC
      have heq : prodPMF (PMF.pure g') (prodPMF (PMF.pure c') μ_w)
          = (prodPMF (PMF.pure u') μ_w).map deflateFull := by
        rw [map_deflateFull_prod, hgs, hcs]
      exact ⟨prodPMF (PMF.pure u') μ_w,
        Or.inl ⟨hl, PMF.pure u', μ_w, hstep, hW, rfl⟩, heq⟩
    · exact absurd hτ hl
    · exact absurd hτ hl
  · -- A stage's own silent rule.
    obtain ⟨g', rfl⟩ := GBCA.implFamily_isLTS P _ _ _ hG
    obtain ⟨u', hgs, hcs, hstep⟩ := ownGroup_tau_of_impl P hG
    have heq : prodPMF (PMF.pure g')
          (PMF.pure ((deflCore u, w) : CoreState P.n × (ℕ → WCC.SpecState P.n)))
        = (prodPMF (PMF.pure u') (PMF.pure w)).map deflateFull := by
      rw [prodPMF_pure_pure, prodPMF_pure_pure, PMF.pure_map, ← hgs, ← hcs]
      rfl
    exact ⟨prodPMF (PMF.pure u') (PMF.pure w),
      Or.inr (Or.inl ⟨rfl, PMF.pure u', hstep, rfl⟩), heq⟩
  · rcases hCW with ⟨hτ, -⟩ | ⟨-, μ₂, hC, rfl⟩ | ⟨-, μ_w, hW, rfl⟩
    · exact absurd rfl hτ
    · -- The round loop's own silent rule.
      obtain ⟨c', rfl⟩ := core_isLTS P _ _ _ hC
      obtain ⟨u', hgs, hcs, hstep⟩ := ownGroup_tau_of_core P hC
      have heq : prodPMF (PMF.pure (fun r => deflStage u r))
            (prodPMF (PMF.pure c') (PMF.pure w))
          = (prodPMF (PMF.pure u') (PMF.pure w)).map deflateFull := by
        rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure, PMF.pure_map,
          ← hgs, ← hcs]
        rfl
      exact ⟨prodPMF (PMF.pure u') (PMF.pure w),
        Or.inr (Or.inl ⟨rfl, PMF.pure u', hstep, rfl⟩), heq⟩
    · -- The coin resolution.
      exact ⟨prodPMF (PMF.pure u) μ_w, Or.inr (Or.inr ⟨rfl, μ_w, hW, rfl⟩),
        (map_deflateFull_prod u μ_w).symm⟩

/-! ### The budgeted own-flag system -/

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
/-- The step-level budget condition on the monolithic side, read off the
core's copy of the corrupted set: a `fail k` label is a repeat or is fired
with budget headroom. Along the forward map the core's `F` *is* the flag set,
so this is `okLabel` verbatim (`okLabelM_deflate`). -/
def okLabelM {P : Params}
    (s : (ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))
    (l : Lab P.n) : Prop :=
  ∀ k, l = .fail k → k ∈ s.2.1.F ∨ s.2.1.F.card < P.f

/-- **The budgeted monolithic hybrid**: `hybridImpl` restricted to the steps
whose `fail` labels stay within budget, with the same restriction shape as
`ownFlagFlatB`. -/
noncomputable def hybridImplB (P : Params) :
    System ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))
      (Lab P.n) where
  init := (hybridImpl P).init
  step s l μ := (hybridImpl P).step s l μ ∧ okLabelM s l

/-- The two step-level budget conditions correspond along the forward map. -/
theorem okLabelM_deflate {P : Params}
    (s : (∀ _ : Fin P.n, ABANodeU P.n) × (ℕ → WCC.SpecState P.n)) (l : Lab P.n) :
    okLabelM (deflateFull s) l ↔ okLabel s l := by
  unfold okLabelM okLabel
  constructor
  · intro h k hk
    rcases h k hk with hmem | hcard
    · exact Or.inl ((mem_flagSet s.1 k).mp hmem)
    · exact Or.inr hcard
  · intro h k hk
    rcases h k hk with hfl | hcard
    · exact Or.inl ((mem_flagSet s.1 k).mpr hfl)
    · exact Or.inr hcard

/-- **The forward matching.** Every step of the budgeted own-flag hybrid is
the budgeted monolithic hybrid's step along the forward map, successor
distributions pushed forward. -/
theorem hybridB_step_of_ownB (P : Params) :
    ∀ s l μ, (ownFlagFlatB P).step s l μ →
      (hybridImplB P).step (deflateFull s) l (μ.map deflateFull) := by
  rintro s l μ ⟨h, hOK⟩
  refine ⟨?_, (okLabelM_deflate s l).mpr hOK⟩
  rcases h with ⟨rfl, l', hl', hpre⟩ | ⟨hn, hpre⟩
  · exact Or.inl ⟨rfl, l', hl', hybridPre_step_of_ownPre P hpre
      (fun k hk => absurd (hk ▸ hl') (Lab.fail_not_mem_hiddenAPI k))⟩
  · exact Or.inr ⟨hn, hybridPre_step_of_ownPre P hpre
      (fun k hk => (hOK k hk).imp (mem_flagSet _ _).mpr id)⟩

/-- **The converse matching.** Every step of the budgeted monolithic hybrid
out of a deflated state is reflected by a budgeted own-flag step. -/
theorem ownB_step_of_hybridB (P : Params) :
    ∀ s l μ, (hybridImplB P).step (deflateFull s) l μ →
      ∃ ν, (ownFlagFlatB P).step s l ν ∧ μ = ν.map deflateFull := by
  rintro s l μ ⟨h, hOKM⟩
  have hOK : okLabel s l := (okLabelM_deflate s l).mp hOKM
  rcases h with ⟨rfl, l', hl', hpre⟩ | ⟨hn, hpre⟩
  · obtain ⟨ν, hν, rfl⟩ := ownPre_step_of_hybridPre P hpre
      (fun k hk => absurd (hk ▸ hl') (Lab.fail_not_mem_hiddenAPI k))
    exact ⟨ν, ⟨Or.inl ⟨rfl, l', hl', hν⟩, hOK⟩, rfl⟩
  · obtain ⟨ν, hν, rfl⟩ := ownPre_step_of_hybridPre P hpre
      (fun k hk => (hOK k hk).imp (mem_flagSet _ _).mpr id)
    exact ⟨ν, ⟨Or.inr ⟨hn, hν⟩, hOK⟩, rfl⟩

/-- The forward map carries the own-flag initial state to the monolithic
one: no process is flagged, no set is corrupted. -/
theorem deflateFull_init (P : Params) :
    deflateFull ((ownFlagFlatB P).init) = (hybridImplB P).init := by
  have hfs : flagSet (((ownFlagFlatB P).init).1) = ∅ := by
    simp [flagSet, ownFlagFlatB, ownFlagFlat, ownFlagPre, ownFlagGroup, ABAProcU]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext r
    exact implState_ext rfl rfl rfl hfs
  · exact coreState_ext rfl rfl rfl hfs

/-! ### The two simulations and the headline -/

/-- The budgeted own-flag hybrid simulates into the budgeted monolithic
hybrid, along the graph of the forward map. -/
theorem ownFlagSim (P : Params) :
    ProbabilisticForwardSimulation (ownFlagFlatB P) (hybridImplB P)
      (fun s ν => ν = PMF.pure (deflateFull s)) :=
  ProbabilisticForwardSimulation.ofStrongFunctional deflateFull (deflateFull_init P)
    (hybridB_step_of_ownB P)

/-- The budgeted monolithic hybrid simulates back, along the same graph read
backwards: the forward map is not surjective — monolithic states whose copies
of the corrupted set disagree have no preimage — but it reflects steps. -/
theorem ownFlagSimConverse (P : Params) :
    ProbabilisticForwardSimulation (hybridImplB P) (ownFlagFlatB P)
      (fun p ν => ∃ q, ν = PMF.pure q ∧ p = deflateFull q) :=
  ProbabilisticForwardSimulation.ofStrongFunctional_converse deflateFull
    (deflateFull_init P) (fun q l μ h => ownB_step_of_hybridB P q l μ h)

/-- **The own-flag presentation is the hybrid, budget for budget.** The
budget-restricted own-flag hybrid and the budget-restricted monolithic hybrid
achieve exactly the same trace distributions. -/
theorem ownFlag_atd (P : Params) :
    achievableTraceDists (ownFlagFlatB P) = achievableTraceDists (hybridImplB P) :=
  Set.Subset.antisymm
    (ownFlagSim P).achievableTraceDists_subset
    (ownFlagSimConverse P).achievableTraceDists_subset

/-- Forgetting the budget restriction: the identity map carries every
`hybridImplB` step to the `hybridImpl` step it restricts. -/
theorem hybridImplB_refines (P : Params) :
    achievableTraceDists (hybridImplB P) ⊆ achievableTraceDists (hybridImpl P) := by
  have hsim : ProbabilisticForwardSimulation (hybridImplB P) (hybridImpl P)
      (fun s ν => ν = PMF.pure (id s)) :=
    ProbabilisticForwardSimulation.ofStrongFunctional id rfl
      (fun s l μ h => by rw [PMF.map_id]; exact h.1)
  exact hsim.achievableTraceDists_subset

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
and Agreement. Pruning lands in `ownFlagFlatB`, the forward matching carries
the execution into `hybridImplB`, forgetting the restriction lands in
`hybridImpl`, and `ABA.main` applies. -/
theorem ownFlagFlat_safe (P : Params) :
    ∀ D ∈ achievableTraceDists (ownFlagFlat P), ∀ t, D t ≠ 0 → BudgetTrace P.f t →
      ValidityTrace P t ∧ AgreementTrace t := by
  rintro D ⟨pe, hinit, hD⟩ t hne hB
  rw [← hD t] at hne
  have hBne := traceProb_ne_zero_of_budget P pe hinit t hB hne
  have hY := mapBeliefExec_traceProb deflateFull (hybridB_step_of_ownB P)
    ⟨pe.initState, pruneSched P pe⟩ (deflateFull_init P) (by rw [hinit]; rfl) t
  refine main P
    ((hybridImplB P).traceProb
      (mapBeliefExec deflateFull (hybridB_step_of_ownB P) ⟨pe.initState, pruneSched P pe⟩))
    (hybridImplB_refines P ⟨_, mapBeliefExec_initState _ _ _, fun τ => rfl⟩) t ?_
  rw [hY]
  exact hBne

/-- **Trace conservativity of the own-flag presentation**: every
positive-probability trace of the own-flag hybrid that respects the
corruption budget has positive probability under an achievable trace
distribution of `ABA.hybridImpl`. -/
theorem ownFlagFlat_traces (P : Params) :
    ∀ D ∈ achievableTraceDists (ownFlagFlat P), ∀ t, D t ≠ 0 → BudgetTrace P.f t →
      ∃ D' ∈ achievableTraceDists (hybridImpl P), D' t ≠ 0 := by
  rintro D ⟨pe, hinit, hD⟩ t hne hB
  rw [← hD t] at hne
  have hBne := traceProb_ne_zero_of_budget P pe hinit t hB hne
  have hY := mapBeliefExec_traceProb deflateFull (hybridB_step_of_ownB P)
    ⟨pe.initState, pruneSched P pe⟩ (deflateFull_init P) (by rw [hinit]; rfl) t
  exact ⟨(hybridImplB P).traceProb
      (mapBeliefExec deflateFull (hybridB_step_of_ownB P) ⟨pe.initState, pruneSched P pe⟩),
    hybridImplB_refines P ⟨_, mapBeliefExec_initState _ _ _, fun τ => rfl⟩,
    by rw [hY]; exact hBne⟩

/-! ### Mechanical axiom firewall

No headline may acquire a `sorryAx` dependence. -/

/-- info: 'PLTS.ABA.OwnFlag.ownFlag_atd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ownFlag_atd

/-- info: 'PLTS.ABA.OwnFlag.ownFlagFlat_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ownFlagFlat_safe

/-- info: 'PLTS.ABA.OwnFlag.ownFlagFlat_traces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ownFlagFlat_traces

end OwnFlag
end ABA
end PLTS
