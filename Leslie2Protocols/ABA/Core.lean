/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Labels

/-!
# The ABA core (the source blueprint's Algorithm 1 = ABDY22's Algorithm 2)

The per-process algorithm of the round loop of ABDY22's Asynchronous Byzantine
Agreement protocol. The pseudocode is the source blueprint's Algorithm 1,
which realises **ABDY22's Algorithm 2** —
the weak-coin framework `AA_ε`: rounds of GBCA followed by a weak-coin flip,
the coin adopted only on a `⊥` decision — with the DECIDED gossip below in
place of the paper's bare grade-2 commit. (The paper's Algorithm 1 is the
*strong*-coin framework over ungraded BCA and is not encoded anywhere in this
development; algorithm numbers below refer to the source blueprint unless the
paper is named.) Per process, on external input `b`:

    r ← 0
    loop:
      (b, g) ← GBCA_r(b)          -- b ∈ {0,1,⊥}, g ∈ {A,B,C}
      c ← WCC_r()
      if b = ⊥ then b ← c
      else if g = A then multicast ⟨DECIDED, b⟩
      r ← r + 1

    upon ⟨DECIDED, b⟩ from f + 1 senders, not having multicast:
      multicast ⟨DECIDED, b⟩
    upon ⟨DECIDED, b⟩ from n − f senders, having multicast ⟨DECIDED, b⟩:
      return b

The file holds the algorithm alone: the handshake phase `Phase`, the estimate
a graded outcome dictates (`GbcaOut.est`), and the per-process control record
`ProcCore`. The record carries no sub-protocol state — the
`callG`/`retG`/`callW`/`retW` interactions are pure handshakes over the API
labels, advancing the process's `phase` and recording the returned data, while
the sub-protocol state itself lives in the round specifications and the coin
oracle — and no network state: the DECIDED pools and the corrupted set belong
to the network. The transitions themselves are `CoreProcStepN`
(`ABA/Components.lean`), the rows of a round-loop record `CoreRec` over the
extended alphabet, and `Net.ABAProcStepN` (`ABA/Protocol.lean`), the rows of
the protocol program that carries a round loop beside its stage-side record. This file realises the Core-side
assumptions of `DESIGN-CoreSim.md`: the phase machine (invariant conjunct 4), the DECIDED
diffusion state (conjunct 6), and input coherence (conjunct 5 — the honest
`callG` guard ties the emitted bit to the current estimate).

## Model and deviations (continuing the project's D1–D8)

* **D9 (0-based rounds).** `round : ℕ` starts at `0` where Algorithm 1 starts
  at `r = 1`; the `GBCA_r`/`WCC_r` instance indices shift accordingly.
* **D10 (fused DECIDED-send).** Algorithm 1's `elif g = A: send ⟨DECIDED, b⟩`
  is performed inside the round advance `CoreRec.stepRound`, joined with the
  network's publication of the bit: receiving the round's coin adopts it when
  `est = ⊥`, multicasts `⟨DECIDED, b⟩` when the round's grade was `A b`,
  clears `lastGrade` and advances to the next round, all in one Dirac
  transition. The joint step is the `retWPub` rendezvous, whose round-loop
  half is the advance and whose network half is the pool insert.
* **D11 (byzantine handshake drivers).** Corrupted processes may drive their
  sub-protocol handshakes arbitrarily: each of `callG`/`retG`/`callW`/`retW`
  has a Byzantine drive, authorised by `k ∈ F` at the network and constrained
  by no phase or estimate. The round loop contributes an idle row to every
  such drive, so the family-side call/return rules for corrupted ids are never
  blocked by it.
* **D12′ (per-process DECIDED pools, equivocation-capable).** The DECIDED
  multicast state is the network's per-process pool
  `dpool : Fin n → Finset Bool`, read on the ABA side as `decidedSent`
  (`ABA/ABAState.lean`) and mirroring graded agreement's D5 sent-pool pattern.
  Honest sends insert into the pool (the fused `retWPub` publication and the
  `f + 1` relay `dsnd`; in reachable states DECIDED coherence keeps every
  honest pool at card ≤ 1, so the insert is a first write or a no-op re-send
  of the same bit). Byzantine injection (`byzD`, guarded only by `k ∈ F`) may
  insert either or both bits at any time — a corrupted process may send
  `DECIDED 0` to one receiver and `DECIDED 1` to another (delivery is
  selective). The delivery rendezvous `ddlv` moves one pooled bit into the
  receiver's own row `decidedRecv i j` at most once per (receiver, sender,
  bit) triple, with soundness `b ∈ decidedSent j` on the network's half; the
  `retABA` quorum guard counts distinct *senders* per bit (`decidedCount`).
  The per-process pools (D12′) let a corrupted process equivocate in the
  DECIDED pools; a single-slot model would bar that — an under-approximation
  inconsistent with graded agreement.

Two further notes: the return rule has **no** honesty check — corrupted
returns must pass the same `n − f` DECIDED count as honest ones, and the
specification's return rule is likewise blind to honesty — and
`lastGrade` always refers to the *current* round's GBCA
return (it is cleared by the round advance).
-/

namespace PLTS
namespace ABA

/-- The handshake phase of one core process. The five phases make each
sub-protocol handshake guard crisp:
`idle → toCallG → awaitG → toCallW → awaitW → (next round) toCallG → …`.
The blueprint's per-round bookkeeping between the WCC return and the next
GBCA call is fused into the `retW` step (deviation D10), so no separate
"stepping" phase is needed. -/
inductive Phase : Type
  /-- No external input received yet. -/
  | idle
  /-- Ready to call the current round's GBCA. -/
  | toCallG
  /-- Waiting for the current round's GBCA return. -/
  | awaitG
  /-- Ready to call the current round's WCC. -/
  | toCallW
  /-- Waiting for the current round's WCC return. -/
  | awaitW
  deriving DecidableEq, Repr

/-- The estimate a graded outcome dictates: `A b`/`B b` set the estimate to
`b`, `C` clears it to `⊥` (awaiting the coin). -/
def GbcaOut.est : GbcaOut → Option Bool
  | .A b => some b
  | .B b => some b
  | .C => none

@[simp] theorem GbcaOut.est_A (b : Bool) : (GbcaOut.A b).est = some b := rfl

@[simp] theorem GbcaOut.est_B (b : Bool) : (GbcaOut.B b).est = some b := rfl

@[simp] theorem GbcaOut.est_C : (GbcaOut.C).est = none := rfl

/-- The per-process state of the ABA core. (No field mentions `n`; the
parameter is kept so the record is addressed uniformly as `ProcCore n`
alongside the other per-process records of the development.) -/
structure ProcCore (n : ℕ) : Type where
  /-- The original external input (`callABA` payload), `none` before the call. -/
  input : Option Bool
  /-- The current estimate; `none` encodes the algorithm's `⊥` (awaiting the
  coin). -/
  est : Option Bool
  /-- The current round (0-based, deviation D9). -/
  round : ℕ
  /-- The handshake phase. -/
  phase : Phase
  /-- The graded outcome returned by the *current* round's GBCA (`none` before
  the return; cleared by the round advance). -/
  lastGrade : Option GbcaOut
  /-- Whether this process has returned (fired `retABA`). -/
  returned : Bool
  deriving DecidableEq

namespace ProcCore

/-- The initial per-process state: no input, estimate `⊥`, round `0`, idle. -/
def initial (n : ℕ) : ProcCore n where
  input := none
  est := none
  round := 0
  phase := .idle
  lastGrade := none
  returned := false

@[simp] theorem initial_input (n : ℕ) : (initial n).input = none := rfl

@[simp] theorem initial_est (n : ℕ) : (initial n).est = none := rfl

@[simp] theorem initial_round (n : ℕ) : (initial n).round = 0 := rfl

@[simp] theorem initial_phase (n : ℕ) : (initial n).phase = .idle := rfl

@[simp] theorem initial_lastGrade (n : ℕ) : (initial n).lastGrade = none := rfl

@[simp] theorem initial_returned (n : ℕ) : (initial n).returned = false := rfl

end ProcCore

/-! ### The round-loop record

A process's control record is not by itself what the composition moves: a
round loop also holds the DECIDED payloads delivered to it. The record below
pairs the two, and is one component of the ABA-side state the core simulation
reads (`ABA/ABAState.lean`). -/

/-- The round-loop record of one process: its own control record and the
DECIDED payloads delivered to it, indexed by sender. There is no record of
what it has multicast — the DECIDED pools live in the network. -/
structure CoreRec (n : ℕ) : Type where
  /-- The process's own control record. -/
  proc : ProcCore n
  /-- The DECIDED payloads delivered to this process, indexed by sender. -/
  decIn : Fin n → Finset Bool
  deriving DecidableEq

namespace CoreRec

variable {n : ℕ}

/-- The initial round-loop record: idle control record, no receipts. -/
def initial (n : ℕ) : CoreRec n where
  proc := ProcCore.initial n
  decIn := fun _ => ∅

/-- The number of distinct senders whose `⟨DECIDED, b⟩` this process holds. -/
def decidedCount (q : CoreRec n) (b : Bool) : ℕ :=
  (Finset.univ.filter (fun k => b ∈ q.decIn k)).card

/-- Update the control record. -/
def setProc (q : CoreRec n) (p : ProcCore n) : CoreRec n := { q with proc := p }

/-- Record a delivered `⟨DECIDED, b⟩` from sender `k`. -/
def recvDec (q : CoreRec n) (k : Fin n) (b : Bool) : CoreRec n :=
  { q with decIn := Function.update q.decIn k (insert b (q.decIn k)) }

/-- The round advance on receiving the coin `c`: adopt the coin if the
estimate is `⊥`, clear the grade, open the next round. The `⟨DECIDED, b⟩`
publication the advance carries on an `A` grade (D10) is the network's half of
the joint step, so no row of it appears here. -/
def stepRound (q : CoreRec n) (c : Bool) : CoreRec n :=
  q.setProc
    { q.proc with
      est := some (q.proc.est.getD c),
      lastGrade := none,
      round := q.proc.round + 1,
      phase := .toCallG }

end CoreRec

end ABA
end PLTS
