/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.CoreProc
import Leslie2Protocols.ABA.GBCAProc
import Leslie2Protocols.ABA.Main

/-!
# ABA as the program of one process

The whole protocol read the way it is written: one automaton per process,
running that process's code and nothing else, beside a single centralized box
for the coin.

`ABA.Flat.ABAProc P j` is the program of process `j`. Its state is one
`ABANode` — the round-loop record of the coordinator together with one
graded-agreement stage per round — and every guard in its rule table reads that
node and nothing else. The processes are composed under full synchronisation
(`System.syncProduct`); the two networks the shared alphabet `Lab n` cannot
name are carried by the auxiliary alphabet `FlatNet n` and hidden by the
composition, so the composite `ABA.Flat.flatGroup` speaks exactly `Lab n`.

The coin oracle `WCC.specFamily` is the one component that is not a process. It
stays a separate factor beside the process group, and it keeps its own half of
the `callW` / `retW` handshake: `ABAProc` carries only the coordinator's half of
those two labels, and the two halves rendezvous at the outer parallel
composition. That is also what makes the presentation possible at all — the
coin is the one box whose transitions are not Dirac, so it is never unfolded
into per-process code.

## The rule table

The label classes of `Lab n` partition the table.

* `callABA` / `retABA` — the ABA API. Only the coordinator half of the addressed
  process moves; every stage of every process idles.
* `callG r id b` / `retG r id out` — the graded-agreement API of round `r`.
  These are the labels on which the coordinator record and the round-`r` stage
  of the *same* process move together, so each of them is a fused rule: a
  `callG` fuses one of the two coordinator behaviours (honest, corrupted) with
  one of the two stage behaviours (the genuine call, the input-enabledness
  loop), giving four constructors; a `retG` fuses the two coordinator
  behaviours with the stage evidence that fixes the graded outcome, giving six.
  The `retG` rules are the only place where stage evidence guards a visible
  label, and the stage has no return loop.
* `callW r id` / `retW r id c` — the coin API. Only the coordinator half is
  here; the oracle answers at the outer composition.
* `fail k` — corruption. The node's coordinator copy of the corrupted set and
  *every* stage copy are written at once, matching the simultaneous broadcast
  every component of the composition answers.
* `τ` — the local sends. Two of them belong to the coordinator (the DECIDED echo
  and the corrupted injection), seven to a stage, at any round.
* `FlatNet` — the two networks. `dnet i j b` carries the coordinator's
  `⟨DECIDED, b⟩` from `j` to `i`; `gnet r i j m` carries the round-`r` stage
  message `m` from `j` to `i`. Both are two-party rendezvous, split into the
  self, sender, receiver and bystander roles. The guards of the two differ by
  design: a DECIDED delivery is refused when the receiver already holds the
  payload from that sender, whereas a stage delivery is not — the stage network
  is idempotent, so re-delivery is a no-op there and needs no guard.

Byzantine guards are read off the copy of the corrupted set that belongs to the
half being driven: the coordinator rules read the coordinator's copy, the stage
rule `stageByz` reads that stage's own copy.

## What is proved

`ABA.Flat.flatABA_atd` states that the flat presentation and `ABA.hybridImpl`
achieve exactly the same trace distributions, and `ABA.Flat.flatABA_safe` reads
the safety theorem `ABA.main` along that equality. The proof is a double
simulation between the pre-abstraction systems

    flatPre  = flatGroup ∥ WCC.specFamily
    preImpl  = GBCA.implFamily ∥ (ABA.core ∥ WCC.specFamily)

along the packing map `ABA.Flat.unflat`, which reads a `preImpl` state as one
flat node per process. Every transition of either system other than the coin
flip is Dirac and the two shapes have the same Dirac successor, so the two
directions are a strong functional matching and its converse; the coin flip
appears on both sides as the same pushforward of `Params.coinPMF` and is
matched by itself. Abstraction of the sub-protocol API and soundness of
probabilistic forward simulation then give the two inclusions.
-/

namespace PLTS
namespace ABA
namespace Flat

/-! ### The flat auxiliary alphabet -/

/-- The auxiliary (rendezvous) alphabet of the flat presentation: the stage
network round-tagged by the stage it belongs to, plus the DECIDED network of the
coordinator, which has no round. -/
inductive FlatNet (n : ℕ) : Type
  /-- Round-`r` stage delivery: sender `j` hands `m` to receiver `i`. -/
  | gnet (r : ℕ) (i j : Fin n) (m : GBCA.Msg)
  /-- DECIDED delivery: sender `j`'s `⟨DECIDED, b⟩` reaches receiver `i`. -/
  | dnet (i j : Fin n) (b : Bool)
  deriving DecidableEq

/-- The extended alphabet of the flat presentation. Its silent label is
`Sum.inl τ`, so every `Sum.inr` label is observable and hence hideable. -/
abbrev FLab (n : ℕ) : Type := Lab n ⊕ FlatNet n

/-- The state of one flat process: its coordinator round-loop node together with
one graded-agreement stage node per round. -/
abbrev ABANode (n : ℕ) : Type := CoreNode n × (ℕ → GBCA.ProcNode n)

/-! ### The rule table -/

/-- The step relation of the flat automaton of process `j`: the program `j`
runs. Every guard reads `j`'s own node. Labels `j` does not own carry idle
self-loops, so that full synchronisation lets their owner move. All transitions
are Dirac. -/
inductive ABAProcStep (P : Params) (j : Fin P.n) :
    ABANode P.n → FLab P.n → PMF (ABANode P.n) → Prop
  /-- `upon ABA(b)`: the external input arrives, is recorded as input and
  estimate, and round `0` opens. No stage moves. -/
  | input (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (b : Bool)
      (h : c.proc.input = none) :
      ABAProcStep P j (c, g) (Sum.inl (.callABA j b))
        (PMF.pure (c.setProc { c.proc with
          input := some b, est := some b, round := 0, phase := .toCallG }, g))
  /-- Input-enabledness loop on `j`'s own `callABA`. -/
  | inputLoop (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (b : Bool) :
      ABAProcStep P j (c, g) (Sum.inl (.callABA j b)) (PMF.pure (c, g))
  /-- An input addressed elsewhere: not `j`'s business. -/
  | callABAIdle (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (id : Fin P.n) (b : Bool)
      (hid : id ≠ j) :
      ABAProcStep P j (c, g) (Sum.inl (.callABA id b)) (PMF.pure (c, g))
  /-- `upon ⟨DECIDED, b⟩ from n − f senders, having multicast ⟨DECIDED, b⟩:
  return b`. The quorum counts distinct senders in `j`'s own receipt rows and
  there is no honesty check. -/
  | ret (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (b : Bool)
      (hcnt : P.n - P.f ≤ c.decidedCount b) (hs : b ∈ c.decOut)
      (hret : c.proc.returned = false) :
      ABAProcStep P j (c, g) (Sum.inl (.retABA j b))
        (PMF.pure (c.setProc { c.proc with returned := true }, g))
  /-- A return by another process: not `j`'s business. -/
  | retABAIdle (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (id : Fin P.n) (b : Bool)
      (hid : id ≠ j) :
      ABAProcStep P j (c, g) (Sum.inl (.retABA id b)) (PMF.pure (c, g))
  /-- The genuine graded-agreement handshake: the round-loop emits its current
  estimate and stage `r` records it and multicasts `⟨INPUT, b⟩`. -/
  | callG_call (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (b : Bool)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r) (hest : c.proc.est = some b)
      (hin : (g r).proc.input = none) :
      ABAProcStep P j (c, g) (Sum.inl (.callG r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG },
          Function.update g r (((g r).setP { (g r).proc with
              input := some b,
              sentInput := Function.update (g r).proc.sentInput b true }).send
            (.input b))))
  /-- The same handshake against an already-called stage: the round-loop
  advances and the stage answers by its input-enabledness loop. -/
  | callG_loop (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (b : Bool)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r) (hest : c.proc.est = some b) :
      ABAProcStep P j (c, g) (Sum.inl (.callG r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG }, g))
  /-- A corrupted round-loop drives the call with an arbitrary bit; the stage
  takes it as a genuine call. -/
  | callGByz_call (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (b : Bool)
      (hF : j ∈ c.F) (hin : (g r).proc.input = none) :
      ABAProcStep P j (c, g) (Sum.inl (.callG r j b))
        (PMF.pure (c,
          Function.update g r (((g r).setP { (g r).proc with
              input := some b,
              sentInput := Function.update (g r).proc.sentInput b true }).send
            (.input b))))
  /-- A corrupted round-loop drives the call against an already-called stage:
  neither half moves. -/
  | callGByz_loop (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (b : Bool)
      (hF : j ∈ c.F) :
      ABAProcStep P j (c, g) (Sum.inl (.callG r j b)) (PMF.pure (c, g))
  /-- A graded-agreement call by another process: not `j`'s business. -/
  | callGIdle (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (id : Fin P.n)
      (b : Bool) (hid : id ≠ j) :
      ABAProcStep P j (c, g) (Sum.inl (.callG r id b)) (PMF.pure (c, g))
  /-- Return with grade `A v`: an `n − f` `BIND v` quorum in stage `r` closes the
  stage and hands `v` to the round-loop, which adopts it and heads for the
  coin. -/
  | retG_A (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (v : Bool)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r)
      (hcnt : P.n - P.f ≤ (g r).recvCount (.bind (some v)))
      (hret : (g r).proc.returned = false) :
      ABAProcStep P j (c, g) (Sum.inl (.retG r j (.A v)))
        (PMF.pure (c.setProc { c.proc with
            est := (GbcaOut.A v).est, lastGrade := some (.A v), phase := .toCallW },
          Function.update g r ((g r).setP { (g r).proc with returned := true })))
  /-- Return with grade `B v`: an `n − f` any-`BIND` quorum containing `BIND v`,
  `f + 1` `VOTE v`s and both bits valid. -/
  | retG_B (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (v : Bool)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r)
      (hcnt : P.n - P.f ≤ (g r).bindCount)
      (honce : ∃ k, GBCA.Msg.bind (some v) ∈ (g r).inbox k)
      (hvote : P.f + 1 ≤ (g r).recvCount (.vote (some v)))
      (hval : (g r).bothValid P)
      (hret : (g r).proc.returned = false) :
      ABAProcStep P j (c, g) (Sum.inl (.retG r j (.B v)))
        (PMF.pure (c.setProc { c.proc with
            est := (GbcaOut.B v).est, lastGrade := some (.B v), phase := .toCallW },
          Function.update g r ((g r).setP { (g r).proc with returned := true })))
  /-- Return with grade `C`: an `n − f` `BIND ⊥` quorum with both bits valid
  clears the estimate, so the round-loop will adopt the coin. -/
  | retG_C (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r)
      (hcnt : P.n - P.f ≤ (g r).recvCount (.bind none))
      (hval : (g r).bothValid P)
      (hret : (g r).proc.returned = false) :
      ABAProcStep P j (c, g) (Sum.inl (.retG r j .C))
        (PMF.pure (c.setProc { c.proc with
            est := GbcaOut.C.est, lastGrade := some .C, phase := .toCallW },
          Function.update g r ((g r).setP { (g r).proc with returned := true })))
  /-- Grade-`A` return to a corrupted round-loop: the stage closes on its own
  evidence and the round-loop records nothing. -/
  | retGByz_A (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (v : Bool)
      (hF : j ∈ c.F)
      (hcnt : P.n - P.f ≤ (g r).recvCount (.bind (some v)))
      (hret : (g r).proc.returned = false) :
      ABAProcStep P j (c, g) (Sum.inl (.retG r j (.A v)))
        (PMF.pure (c, Function.update g r ((g r).setP { (g r).proc with returned := true })))
  /-- Grade-`B` return to a corrupted round-loop. -/
  | retGByz_B (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (v : Bool)
      (hF : j ∈ c.F)
      (hcnt : P.n - P.f ≤ (g r).bindCount)
      (honce : ∃ k, GBCA.Msg.bind (some v) ∈ (g r).inbox k)
      (hvote : P.f + 1 ≤ (g r).recvCount (.vote (some v)))
      (hval : (g r).bothValid P)
      (hret : (g r).proc.returned = false) :
      ABAProcStep P j (c, g) (Sum.inl (.retG r j (.B v)))
        (PMF.pure (c, Function.update g r ((g r).setP { (g r).proc with returned := true })))
  /-- Grade-`C` return to a corrupted round-loop. -/
  | retGByz_C (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ)
      (hF : j ∈ c.F)
      (hcnt : P.n - P.f ≤ (g r).recvCount (.bind none))
      (hval : (g r).bothValid P)
      (hret : (g r).proc.returned = false) :
      ABAProcStep P j (c, g) (Sum.inl (.retG r j .C))
        (PMF.pure (c, Function.update g r ((g r).setP { (g r).proc with returned := true })))
  /-- A graded-agreement return to another process: not `j`'s business. -/
  | retGIdle (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (id : Fin P.n)
      (out : GbcaOut) (hid : id ≠ j) :
      ABAProcStep P j (c, g) (Sum.inl (.retG r id out)) (PMF.pure (c, g))
  /-- `c ← WCC_r()`, the call half at the round-loop. The oracle's half of this
  handshake is supplied by the coin box at the outer composition. -/
  | callW (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ)
      (hph : c.proc.phase = .toCallW) (hr : c.proc.round = r) :
      ABAProcStep P j (c, g) (Sum.inl (.callW r j))
        (PMF.pure (c.setProc { c.proc with phase := .awaitW }, g))
  /-- A corrupted round-loop drives the coin call. -/
  | callWByz (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (hF : j ∈ c.F) :
      ABAProcStep P j (c, g) (Sum.inl (.callW r j)) (PMF.pure (c, g))
  /-- A coin call by another process: not `j`'s business. -/
  | callWIdle (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (id : Fin P.n)
      (hid : id ≠ j) :
      ABAProcStep P j (c, g) (Sum.inl (.callW r id)) (PMF.pure (c, g))
  /-- `c ← WCC_r()`, the return half at the round-loop, together with
  `if b = ⊥ then b ← c`, `elif g = A then multicast ⟨DECIDED, b⟩` and
  `r ← r + 1` — one fused round advance. -/
  | retW (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (co : Bool)
      (hph : c.proc.phase = .awaitW) (hr : c.proc.round = r) :
      ABAProcStep P j (c, g) (Sum.inl (.retW r j co)) (PMF.pure (c.stepRound co, g))
  /-- A corrupted round-loop drives the coin return. -/
  | retWByz (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (co : Bool)
      (hF : j ∈ c.F) :
      ABAProcStep P j (c, g) (Sum.inl (.retW r j co)) (PMF.pure (c, g))
  /-- A coin return to another process: not `j`'s business. -/
  | retWIdle (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (id : Fin P.n)
      (co : Bool) (hid : id ≠ j) :
      ABAProcStep P j (c, g) (Sum.inl (.retW r id co)) (PMF.pure (c, g))
  /-- Corruption: the round-loop's copy of the corrupted set and every stage's
  copy are written at once, one write per copy every component of the
  composition performs simultaneously. -/
  | fail (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (k : Fin P.n) :
      ABAProcStep P j (c, g) (Sum.inl (.fail k))
        (PMF.pure (c.corrupt P k, fun r => (g r).corrupt P k))
  /-- `upon ⟨DECIDED, b⟩ from f + 1 senders, not having multicast: multicast
  ⟨DECIDED, b⟩`. -/
  | echo (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (b : Bool)
      (hcnt : P.f + 1 ≤ c.decidedCount b) (hs : b ∉ c.decOut) :
      ABAProcStep P j (c, g) (Sum.inl .tau) (PMF.pure (c.sendDec b, g))
  /-- A corrupted process injects an arbitrary DECIDED payload into its own
  pool, and so may equivocate. -/
  | byzDecided (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (b : Bool) (hF : j ∈ c.F) :
      ABAProcStep P j (c, g) (Sum.inl .tau) (PMF.pure (c.sendDec b, g))
  /-- Stage `r`'s `INPUT` relay. -/
  | stageRelay (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (b : Bool)
      (hin : (g r).proc.input ≠ none) (hcnt : P.f + 1 ≤ (g r).recvCount (.input b))
      (hsend : (g r).proc.sentInput b = false) :
      ABAProcStep P j (c, g) (Sum.inl .tau)
        (PMF.pure (c, Function.update g r (((g r).setP { (g r).proc with
          sentInput := Function.update (g r).proc.sentInput b true }).send (.input b))))
  /-- Stage `r`'s `ECHO`. -/
  | stageEcho (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (b : Bool)
      (hin : (g r).proc.input ≠ none) (hcnt : P.n - P.f ≤ (g r).recvCount (.input b))
      (hsend : (g r).proc.sentEcho = none) :
      ABAProcStep P j (c, g) (Sum.inl .tau)
        (PMF.pure (c, Function.update g r
          (((g r).setP { (g r).proc with sentEcho := some b }).send (.echo b))))
  /-- Stage `r`'s `VOTE b`. -/
  | stageVoteBit (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (b : Bool)
      (hin : (g r).proc.input ≠ none) (hcnt : P.n - P.f ≤ (g r).recvCount (.echo b))
      (hsend : (g r).proc.sentVote = none) :
      ABAProcStep P j (c, g) (Sum.inl .tau)
        (PMF.pure (c, Function.update g r
          (((g r).setP { (g r).proc with sentVote := some (some b) }).send (.vote (some b)))))
  /-- Stage `r`'s `VOTE ⊥`. -/
  | stageVoteBot (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ)
      (hin : (g r).proc.input ≠ none) (hcnt : P.n - P.f ≤ (g r).echoCount)
      (hval : (g r).bothValid P) (hsend : (g r).proc.sentVote = none) :
      ABAProcStep P j (c, g) (Sum.inl .tau)
        (PMF.pure (c, Function.update g r
          (((g r).setP { (g r).proc with sentVote := some none }).send (.vote none))))
  /-- Stage `r`'s `BIND b`. -/
  | stageBindBit (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (b : Bool)
      (hin : (g r).proc.input ≠ none) (hcnt : P.n - P.f ≤ (g r).recvCount (.vote (some b)))
      (hsend : (g r).proc.sentBind = none) :
      ABAProcStep P j (c, g) (Sum.inl .tau)
        (PMF.pure (c, Function.update g r
          (((g r).setP { (g r).proc with sentBind := some (some b) }).send (.bind (some b)))))
  /-- Stage `r`'s `BIND ⊥`. -/
  | stageBindBot (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ)
      (hin : (g r).proc.input ≠ none) (hcnt : P.n - P.f ≤ (g r).voteCount)
      (hval : (g r).bothValid P) (hsend : (g r).proc.sentBind = none) :
      ABAProcStep P j (c, g) (Sum.inl .tau)
        (PMF.pure (c, Function.update g r
          (((g r).setP { (g r).proc with sentBind := some none }).send (.bind none))))
  /-- Byzantine injection into stage `r`'s outbox. The guard is stage `r`'s own
  copy of the corrupted set. -/
  | stageByz (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (m : GBCA.Msg)
      (hF : j ∈ (g r).F) :
      ABAProcStep P j (c, g) (Sum.inl .tau)
        (PMF.pure (c, Function.update g r ((g r).send m)))
  /-- DECIDED gossip, sender and receiver in one process: `j` delivers its own
  `⟨DECIDED, b⟩` to itself, supplying both halves of the guard. -/
  | dnetSelf (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (b : Bool)
      (hs : b ∈ c.decOut) (hr : b ∉ c.decIn j) :
      ABAProcStep P j (c, g) (Sum.inr (.dnet j j b)) (PMF.pure (c.recvDec j b, g))
  /-- DECIDED gossip, sender half: `j` contributes the soundness guard and does
  not move. -/
  | dnetSend (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (i : Fin P.n) (b : Bool)
      (hi : i ≠ j) (hs : b ∈ c.decOut) :
      ABAProcStep P j (c, g) (Sum.inr (.dnet i j b)) (PMF.pure (c, g))
  /-- DECIDED gossip, receiver half: `j` contributes the freshness guard and
  performs the write. -/
  | dnetRecv (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (k : Fin P.n) (b : Bool)
      (hk : k ≠ j) (hr : b ∉ c.decIn k) :
      ABAProcStep P j (c, g) (Sum.inr (.dnet j k b)) (PMF.pure (c.recvDec k b, g))
  /-- DECIDED gossip between two other processes: not `j`'s business. -/
  | dnetIdle (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (i k : Fin P.n) (b : Bool)
      (hi : i ≠ j) (hk : k ≠ j) :
      ABAProcStep P j (c, g) (Sum.inr (.dnet i k b)) (PMF.pure (c, g))
  /-- Stage-`r` self-delivery: `j` is both sender and receiver. -/
  | gnetSelf (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (m : GBCA.Msg)
      (h : m ∈ (g r).out) :
      ABAProcStep P j (c, g) (Sum.inr (.gnet r j j m))
        (PMF.pure (c, Function.update g r ((g r).deliverTo j m)))
  /-- Stage-`r` sender half: `j` contributes the outbox guard and does not
  move. -/
  | gnetSend (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (i : Fin P.n)
      (m : GBCA.Msg) (hi : i ≠ j) (h : m ∈ (g r).out) :
      ABAProcStep P j (c, g) (Sum.inr (.gnet r i j m)) (PMF.pure (c, g))
  /-- Stage-`r` receiver half: `j` files the message under the sender's row. The
  outbox guard is the sender's business, so there is none here. -/
  | gnetRecv (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (k : Fin P.n)
      (m : GBCA.Msg) (hk : k ≠ j) :
      ABAProcStep P j (c, g) (Sum.inr (.gnet r j k m))
        (PMF.pure (c, Function.update g r ((g r).deliverTo k m)))
  /-- A stage-`r` delivery between two other processes: not `j`'s business. -/
  | gnetIdle (c : CoreNode P.n) (g : ℕ → GBCA.ProcNode P.n) (r : ℕ) (i k : Fin P.n)
      (m : GBCA.Msg) (hi : i ≠ j) (hk : k ≠ j) :
      ABAProcStep P j (c, g) (Sum.inr (.gnet r i k m)) (PMF.pure (c, g))

/-! ### The automaton and the composition pipeline -/

/-- The flat automaton of process `j`. -/
noncomputable def ABAProc (P : Params) (j : Fin P.n) : System (ABANode P.n) (FLab P.n) where
  init := (CoreNode.initial P.n, fun _ => GBCA.ProcNode.initial P.n)
  step := ABAProcStep P j

@[simp] theorem ABAProc_init (P : Params) (j : Fin P.n) :
    (ABAProc P j).init = (CoreNode.initial P.n, fun _ => GBCA.ProcNode.initial P.n) := rfl

@[simp] theorem ABAProc_step (P : Params) (j : Fin P.n) (q : ABANode P.n)
    (l : FLab P.n) (μ : PMF (ABANode P.n)) :
    (ABAProc P j).step q l μ ↔ ABAProcStep P j q l μ := Iff.rfl

/-- Every flat transition is Dirac. -/
theorem ABAProc_isLTS (P : Params) (j : Fin P.n) : (ABAProc P j).IsLTS := by
  rintro q l μ hstep
  cases hstep <;> exact ⟨_, rfl⟩

/-- The rendezvous labels, hidden by the composition. -/
def flatNetLabels (n : ℕ) : Set (FLab n) := {l | ∃ e : FlatNet n, l = Sum.inr e}

@[simp] theorem inl_notMem_flatNetLabels {n : ℕ} (l : Lab n) :
    Sum.inl l ∉ flatNetLabels n := by
  simp [flatNetLabels]

@[simp] theorem inr_mem_flatNetLabels {n : ℕ} (e : FlatNet n) :
    Sum.inr e ∈ flatNetLabels n := ⟨e, rfl⟩

/-- **The process group**: the flat automata under full synchronisation, the two
networks hidden, the result read back over the shared alphabet `Lab n`. -/
noncomputable def flatGroup (P : Params) :
    System (∀ _ : Fin P.n, ABANode P.n) (Lab P.n) :=
  ((System.syncProduct (ABAProc P)).abstract (flatNetLabels P.n)).relabel

@[simp] theorem flatGroup_init (P : Params) :
    (flatGroup P).init = fun _ => (CoreNode.initial P.n, fun _ => GBCA.ProcNode.initial P.n) :=
  rfl

theorem flatGroup_isLTS (P : Params) : (flatGroup P).IsLTS :=
  System.relabel_isLTS
    (System.abstract_isLTS (System.syncProduct_isLTS (ABAProc_isLTS P)) _)

/-- The process group beside the coin oracle: the flat counterpart of the
pre-abstraction hybrid. -/
noncomputable def flatPre (P : Params) :
    System ((∀ _ : Fin P.n, ABANode P.n) × (ℕ → WCC.SpecState P.n)) (Lab P.n) :=
  (flatGroup P).parallel (WCC.specFamily P)

/-- **The flat hybrid**: the process group beside the coin oracle, the
sub-protocol API hidden. The flat counterpart of `ABA.hybridImpl`. -/
noncomputable def flatHybrid (P : Params) :
    System ((∀ _ : Fin P.n, ABANode P.n) × (ℕ → WCC.SpecState P.n)) (Lab P.n) :=
  (flatPre P).abstract (Lab.hiddenAPI P.n)

/-- The system whose sub-protocol API `ABA.hybridImpl` hides: the stage family
beside the round loop and the coin oracle. -/
noncomputable def preImpl (P : Params) :
    System ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))
      (Lab P.n) :=
  (GBCA.implFamily P).parallel ((core P).parallel (WCC.specFamily P))

theorem hybridImpl_eq (P : Params) :
    hybridImpl P = (preImpl P).abstract (Lab.hiddenAPI P.n) := rfl

/-! ### The packing map

A monolithic state is read as one flat node per process by splitting each of its
arrays along the process index. The round-loop half is `cpack`; the stage half
is `GBCA.unpack` applied round by round. -/

/-- The round-loop half of the packing map: the coordinator state read as one
node per process. -/
def cpack {P : Params} (c : CoreState P.n) : ∀ _ : Fin P.n, CoreNode P.n :=
  fun x => { proc := c.procs x, decOut := c.decidedSent x, decIn := c.decidedRecv x, F := c.F }

/-- **The packing map.** A monolithic state read as one flat node per process:
each node gets that process's round-loop record, DECIDED pool and receipt rows,
and, for every round, that process's row of the round's stage. -/
def pack {P : Params} (g : ℕ → GBCA.ImplState P.n) (c : CoreState P.n) :
    ∀ _ : Fin P.n, ABANode P.n :=
  fun x => (cpack c x, fun r => GBCA.unpack (g r) x)

@[simp] theorem pack_fst {P : Params} (g : ℕ → GBCA.ImplState P.n) (c : CoreState P.n)
    (x : Fin P.n) : (pack g c x).1 = cpack c x := rfl

@[simp] theorem pack_snd {P : Params} (g : ℕ → GBCA.ImplState P.n) (c : CoreState P.n)
    (x : Fin P.n) : (pack g c x).2 = fun r => GBCA.unpack (g r) x := rfl

/-- The packing map on a whole pre-abstraction state: the coin oracle is
untouched. -/
def unflat {P : Params}
    (q : (ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n))) :
    (∀ _ : Fin P.n, ABANode P.n) × (ℕ → WCC.SpecState P.n) :=
  (pack q.1 q.2.1, q.2.2)

/-! #### The round-loop half, delta by delta

`CoreRel` (`ABA/CoreProc.lean`) is the graph of `cpack`, so the state-delta
lemmas proved there transfer verbatim. -/

/-- `CoreRel` is the graph of `cpack`. -/
theorem coreRel_iff {P : Params} (q : ∀ _ : Fin P.n, CoreNode P.n) (s : CoreState P.n) :
    CoreRel P q s ↔ q = cpack s := by
  constructor
  · intro h
    funext x
    unfold cpack
    rw [← h.proc_eq x, ← h.out_eq x, ← h.F_eq x, ← funext (h.in_eq x)]
  · rintro rfl
    exact ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem coreRel_cpack {P : Params} (s : CoreState P.n) : CoreRel P (cpack s) s :=
  (coreRel_iff _ s).mpr rfl

theorem cpack_setProc {P : Params} (c : CoreState P.n) (id : Fin P.n) (p : ProcCore P.n) :
    cpack (c.setProc id p) = Function.update (cpack c) id ((cpack c id).setProc p) :=
  ((coreRel_iff _ _).mp ((coreRel_cpack c).setProc id p)).symm

theorem cpack_sendDec {P : Params} (c : CoreState P.n) (id : Fin P.n) (b : Bool) :
    cpack (c.sendDecided id b) = Function.update (cpack c) id ((cpack c id).sendDec b) :=
  ((coreRel_iff _ _).mp ((coreRel_cpack c).sendDec id b)).symm

theorem cpack_recvDec {P : Params} (c : CoreState P.n) (i k : Fin P.n) (b : Bool) :
    cpack (c.deliverDecided i k b) = Function.update (cpack c) i ((cpack c i).recvDec k b) :=
  ((coreRel_iff _ _).mp ((coreRel_cpack c).recvDec i k b)).symm

theorem cpack_stepRound {P : Params} (c : CoreState P.n) (id : Fin P.n) (co : Bool) :
    cpack (c.stepRound id co) = Function.update (cpack c) id ((cpack c id).stepRound co) :=
  ((coreRel_iff _ _).mp ((coreRel_cpack c).stepRound id co)).symm

theorem cpack_corrupt {P : Params} (c : CoreState P.n) (k : Fin P.n) :
    cpack (c.corrupt P k) = fun x => (cpack c x).corrupt P k :=
  ((coreRel_iff _ _).mp ((coreRel_cpack c).corrupt k)).symm

/-- The receipt counts of a packed node are the monolithic counts at that
process: the two shapes hold the same rows. -/
@[simp] theorem cpack_decidedCount {P : Params} (c : CoreState P.n) (x : Fin P.n) (b : Bool) :
    (cpack c x).decidedCount b = c.decidedCount x b := rfl

/-! #### Lifting a half-update to the whole packing -/

/-- A round-loop update touches one node's round-loop half and nothing else. -/
theorem pack_core_update {P : Params} (g : ℕ → GBCA.ImplState P.n)
    {c c' : CoreState P.n} {x : Fin P.n} {nd : CoreNode P.n}
    (h : cpack c' = Function.update (cpack c) x nd) :
    pack g c' = Function.update (pack g c) x (nd, (pack g c x).2) := by
  funext y
  by_cases hy : y = x
  · subst hy
    rw [Function.update_self]
    refine Prod.ext ?_ rfl
    change cpack c' y = nd
    rw [h, Function.update_self]
  · rw [Function.update_of_ne hy]
    refine Prod.ext ?_ rfl
    change cpack c' y = cpack c y
    rw [h, Function.update_of_ne hy]

/-- A stage update at round `r` touches one node's round-`r` stage and nothing
else. -/
theorem pack_stage_update {P : Params} {g : ℕ → GBCA.ImplState P.n} (c : CoreState P.n)
    {r : ℕ} {x : Fin P.n} {s' : GBCA.ImplState P.n} {nd : GBCA.ProcNode P.n}
    (h : GBCA.unpack s' = Function.update (GBCA.unpack (g r)) x nd) :
    pack (Function.update g r s') c
      = Function.update (pack g c) x ((pack g c x).1, Function.update (pack g c x).2 r nd) := by
  funext y
  by_cases hy : y = x
  · subst hy
    rw [Function.update_self]
    refine Prod.ext rfl (funext fun r' => ?_)
    change GBCA.unpack (Function.update g r s' r') y
      = Function.update (fun rr => GBCA.unpack (g rr) y) r nd r'
    by_cases hr : r' = r
    · subst hr
      rw [Function.update_self, Function.update_self, h, Function.update_self]
    · rw [Function.update_of_ne hr, Function.update_of_ne hr]
  · rw [Function.update_of_ne hy]
    refine Prod.ext rfl (funext fun r' => ?_)
    change GBCA.unpack (Function.update g r s' r') y = GBCA.unpack (g r') y
    by_cases hr : r' = r
    · subst hr
      rw [Function.update_self, h, Function.update_of_ne hy]
    · rw [Function.update_of_ne hr]

/-- The corruption broadcast writes every copy of the corrupted set at once. -/
theorem pack_corrupt {P : Params} (g : ℕ → GBCA.ImplState P.n) (c : CoreState P.n)
    (k : Fin P.n) :
    pack (fun r => (g r).corrupt P k) (c.corrupt P k)
      = fun x => ((pack g c x).1.corrupt P k, fun r => ((pack g c x).2 r).corrupt P k) := by
  funext x
  refine Prod.ext ?_ (funext fun r => ?_)
  · change cpack (c.corrupt P k) x = (cpack c x).corrupt P k
    rw [cpack_corrupt]
  · change GBCA.unpack ((g r).corrupt P k) x = (GBCA.unpack (g r) x).corrupt P k
    rw [GBCA.unpack_corrupt]

/-! ### Reading the process group's step relation -/

@[simp] theorem silent_flab_eq (n : ℕ) : (Silent.τ : FLab n) = Sum.inl Lab.tau := rfl

/-- **The composite step relation.** A transition of the process group on `l` is
either a hidden network rendezvous — only at `l = τ` — or a synchronised
transition on `Sum.inl l`. -/
theorem flatGroup_step_iff (P : Params) (q : ∀ _ : Fin P.n, ABANode P.n)
    (l : Lab P.n) (μ : PMF (∀ _ : Fin P.n, ABANode P.n)) :
    (flatGroup P).step q l μ ↔
      (l = .tau ∧ ∃ e : FlatNet P.n,
        (System.syncProduct (ABAProc P)).step q (Sum.inr e) μ) ∨
      (System.syncProduct (ABAProc P)).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_flatNetLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_flatNetLabels l, hstep⟩

/-- A synchronised transition on a visible label: every process steps on it. -/
theorem sync_visible_iff (P : Params) (q : ∀ _ : Fin P.n, ABANode P.n)
    (l : FLab P.n) (hl : l ≠ Sum.inl .tau) (μ : PMF (∀ _ : Fin P.n, ABANode P.n)) :
    (System.syncProduct (ABAProc P)).step q l μ ↔
      ∃ μ_ : Fin P.n → PMF (ABANode P.n),
        (∀ m, ABAProcStep P m (q m) l (μ_ m)) ∧ μ = piPMF μ_ := by
  constructor
  · rintro (⟨-, μ_, hall, rfl⟩ | ⟨hτ, -⟩)
    · exact ⟨μ_, hall, rfl⟩
    · exact absurd hτ hl
  · rintro ⟨μ_, hall, rfl⟩
    exact Or.inl ⟨hl, μ_, hall, rfl⟩

/-- A synchronised transition on a shared label other than `τ`. -/
theorem sync_inl_iff (P : Params) (q : ∀ _ : Fin P.n, ABANode P.n) (l : Lab P.n)
    (hl : l ≠ .tau) (μ : PMF (∀ _ : Fin P.n, ABANode P.n)) :
    (System.syncProduct (ABAProc P)).step q (Sum.inl l) μ ↔
      ∃ μ_ : Fin P.n → PMF (ABANode P.n),
        (∀ m, ABAProcStep P m (q m) (Sum.inl l) (μ_ m)) ∧ μ = piPMF μ_ :=
  sync_visible_iff P q (Sum.inl l) (by simpa using hl) μ

/-- A synchronised transition on the silent label: exactly one process steps and
the others hold their state. -/
theorem sync_tau_iff (P : Params) (q : ∀ _ : Fin P.n, ABANode P.n)
    (μ : PMF (∀ _ : Fin P.n, ABANode P.n)) :
    (System.syncProduct (ABAProc P)).step q (Sum.inl .tau) μ ↔
      ∃ (m : Fin P.n) (ν : PMF (ABANode P.n)),
        ABAProcStep P m (q m) (Sum.inl .tau) ν ∧
        μ = piPMF (Function.update (fun k => PMF.pure (q k)) m ν) := by
  constructor
  · rintro (⟨hτ, -⟩ | ⟨-, m, ν, hstep, rfl⟩)
    · exact absurd rfl hτ
    · exact ⟨m, ν, hstep, rfl⟩
  · rintro ⟨m, ν, hstep, rfl⟩
    exact Or.inr ⟨rfl, m, ν, hstep, rfl⟩

/-! #### Products of Diracs -/

/-- A family of Diracs multiplies to the Dirac on the tuple of their points. -/
private theorem piPMF_eq_pure {P : Params} {μ_ : Fin P.n → PMF (ABANode P.n)}
    {x : ∀ _ : Fin P.n, ABANode P.n} (h : ∀ m, μ_ m = PMF.pure (x m)) :
    piPMF μ_ = PMF.pure x := by
  rw [funext h]
  exact piPMF_pure x

/-- The one-mover case: process `i` lands on `y`, every other process holds its
state. -/
private theorem piPMF_eq_pure_update {P : Params} {μ_ : Fin P.n → PMF (ABANode P.n)}
    (q : ∀ _ : Fin P.n, ABANode P.n) (i : Fin P.n) (y : ABANode P.n)
    (hi : μ_ i = PMF.pure y) (hoth : ∀ m, m ≠ i → μ_ m = PMF.pure (q m)) :
    piPMF μ_ = PMF.pure (Function.update q i y) := by
  refine piPMF_eq_pure (fun m => ?_)
  by_cases hm : m = i
  · subst hm; rw [hi, Function.update_self]
  · rw [hoth m hm, Function.update_of_ne hm]

/-- The silent-interleaving distribution of a Dirac mover. -/
private theorem piPMF_update_eq_pure {P : Params} (q : ∀ _ : Fin P.n, ABANode P.n)
    (i : Fin P.n) (y : ABANode P.n) :
    piPMF (Function.update (fun k => PMF.pure (q k)) i (PMF.pure y))
      = PMF.pure (Function.update q i y) := by
  rw [piPMF_update_pure, PMF.pure_map]

/-! #### Building composite transitions -/

/-- A visible transition of the group: every process steps on `Sum.inl l`. -/
theorem flatGroup_visible_step (P : Params) (q : ∀ _ : Fin P.n, ABANode P.n)
    (l : Lab P.n) (hl : l ≠ .tau) (x : ∀ _ : Fin P.n, ABANode P.n)
    (hall : ∀ m, ABAProcStep P m (q m) (Sum.inl l) (PMF.pure (x m))) :
    (flatGroup P).step q l (PMF.pure x) :=
  (flatGroup_step_iff P q l _).mpr (Or.inr ((sync_inl_iff P q l hl _).mpr
    ⟨fun m => PMF.pure (x m), hall, (piPMF_eq_pure fun _ => rfl).symm⟩))

/-- A silent transition of the group by one process's own `τ`-rule. -/
theorem flatGroup_tau_step (P : Params) (q : ∀ _ : Fin P.n, ABANode P.n)
    (i : Fin P.n) (y : ABANode P.n)
    (h : ABAProcStep P i (q i) (Sum.inl .tau) (PMF.pure y)) :
    (flatGroup P).step q .tau (PMF.pure (Function.update q i y)) :=
  (flatGroup_step_iff P q .tau _).mpr (Or.inr
    ((sync_tau_iff P q _).mpr ⟨i, PMF.pure y, h, (piPMF_update_eq_pure q i y).symm⟩))

/-- A hidden network rendezvous, which the shared alphabet sees as a `τ`. -/
theorem flatGroup_net_step (P : Params) (q : ∀ _ : Fin P.n, ABANode P.n)
    (e : FlatNet P.n) (x : ∀ _ : Fin P.n, ABANode P.n)
    (hall : ∀ m, ABAProcStep P m (q m) (Sum.inr e) (PMF.pure (x m))) :
    (flatGroup P).step q .tau (PMF.pure x) :=
  (flatGroup_step_iff P q .tau _).mpr (Or.inl ⟨rfl, e,
    (sync_visible_iff P q (Sum.inr e) (by simp) _).mpr
      ⟨fun m => PMF.pure (x m), hall, (piPMF_eq_pure fun _ => rfl).symm⟩⟩)

/-! ### Reading the two families' step relations

The coin oracle is never unfolded: it occupies the same slot in both systems and
its transitions are passed through unchanged. Only the stage family needs
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

/-! ### The group layer: assembling flat transitions

Every rule of the two monolithic components is reassembled from the flat rules
of its participants and the idling of everybody else. -/

private theorem pure_inj {α : Type} {a b : α} (h : (PMF.pure a : PMF α) = PMF.pure b) : a = b := by
  have hm : a ∈ (PMF.pure b).support := by rw [← h]; simp
  simpa using hm

/-- Both halves of one process move: its round loop and one of its stages. -/
theorem pack_both_update {P : Params} {g : ℕ → GBCA.ImplState P.n} {c c' : CoreState P.n}
    {r : ℕ} {x : Fin P.n} {s' : GBCA.ImplState P.n} {nd : GBCA.ProcNode P.n}
    {cn : CoreNode P.n}
    (hs : GBCA.unpack s' = Function.update (GBCA.unpack (g r)) x nd)
    (hc : cpack c' = Function.update (cpack c) x cn) :
    pack (Function.update g r s') c'
      = Function.update (pack g c) x (cn, Function.update (pack g c x).2 r nd) := by
  funext y
  by_cases hy : y = x
  · subst hy
    rw [Function.update_self]
    refine Prod.ext ?_ (funext fun r' => ?_)
    · change cpack c' y = cn
      rw [hc, Function.update_self]
    · change GBCA.unpack (Function.update g r s' r') y
        = Function.update (fun rr => GBCA.unpack (g rr) y) r nd r'
      by_cases hr : r' = r
      · subst hr
        rw [Function.update_self, Function.update_self, hs, Function.update_self]
      · rw [Function.update_of_ne hr, Function.update_of_ne hr]
  · rw [Function.update_of_ne hy]
    refine Prod.ext ?_ (funext fun r' => ?_)
    · change cpack c' y = cpack c y
      rw [hc, Function.update_of_ne hy]
    · change GBCA.unpack (Function.update g r s' r') y = GBCA.unpack (g r') y
      by_cases hr : r' = r
      · subst hr
        rw [Function.update_self, hs, Function.update_of_ne hy]
      · rw [Function.update_of_ne hr]

/-- **Visible labels.** On every label of the shared alphabet other than `τ`, a
stage-family transition and a round-loop transition assemble into one
synchronised transition of the process group. -/
theorem flatGroup_visible_of_group (P : Params) {g g' : ℕ → GBCA.ImplState P.n}
    {c c' : CoreState P.n} {l : Lab P.n} (hl : l ≠ .tau)
    (hG : (GBCA.implFamily P).step g l (PMF.pure g'))
    (hC : CoreStep P c l (PMF.pure c')) :
    (flatGroup P).step (pack g c) l (PMF.pure (pack g' c')) := by
  cases l with
  | tau => exact absurd rfl hl
  | callABA id b =>
    -- The stage family idles; the round loop takes its input or loops.
    rw [pure_inj (implFamily_idle_inv rfl (by simp [Lab.isFail]) hl hG)]
    rw [coreStep_callABA_iff] at hC
    rcases hC with ⟨hin, hc⟩ | hc
    · rw [pure_inj hc, pack_core_update g (cpack_setProc c id _)]
      refine flatGroup_visible_step P _ _ hl _ fun m => ?_
      by_cases hm : m = id
      · subst hm; rw [Function.update_self]; exact ABAProcStep.input _ _ b hin
      · rw [Function.update_of_ne hm]; exact ABAProcStep.callABAIdle _ _ id b (Ne.symm hm)
    · rw [pure_inj hc]
      refine flatGroup_visible_step P _ _ hl _ fun m => ?_
      by_cases hm : m = id
      · subst hm; exact ABAProcStep.inputLoop _ _ b
      · exact ABAProcStep.callABAIdle _ _ id b (Ne.symm hm)
  | retABA id b =>
    -- The stage family idles; the round loop returns on its own quorum.
    rw [pure_inj (implFamily_idle_inv rfl (by simp [Lab.isFail]) hl hG)]
    rw [coreStep_retABA_iff] at hC
    obtain ⟨hcnt, hs, hret, hc⟩ := hC
    rw [pure_inj hc, pack_core_update g (cpack_setProc c id _)]
    refine flatGroup_visible_step P _ _ hl _ fun m => ?_
    by_cases hm : m = id
    · subst hm; rw [Function.update_self]; exact ABAProcStep.ret _ _ b hcnt hs hret
    · rw [Function.update_of_ne hm]; exact ABAProcStep.retABAIdle _ _ id b (Ne.symm hm)
  | callG r id b =>
    -- The four fused behaviours: {round loop honest, corrupted} × {stage call, loop}.
    obtain ⟨μr, hx, heq⟩ := implFamily_owned_inv rfl hl hG
    rw [coreStep_callG_iff] at hC
    cases hx with
    | call =>
      rename_i hin
      rw [PMF.pure_map] at heq
      rw [pure_inj heq]
      rcases hC with ⟨hph, hrd, hest, hc⟩ | ⟨hF, hc⟩
      · rw [pure_inj hc, pack_both_update (GBCA.unpack_send (g r) id _ _)
          (cpack_setProc c id _)]
        refine flatGroup_visible_step P _ _ hl _ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]
          exact ABAProcStep.callG_call _ _ r b hph hrd hest hin
        · rw [Function.update_of_ne hm]; exact ABAProcStep.callGIdle _ _ r id b (Ne.symm hm)
      · rw [pure_inj hc, pack_stage_update c (GBCA.unpack_send (g r) id _ _)]
        refine flatGroup_visible_step P _ _ hl _ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]
          exact ABAProcStep.callGByz_call _ _ r b hF hin
        · rw [Function.update_of_ne hm]; exact ABAProcStep.callGIdle _ _ r id b (Ne.symm hm)
    | callLoop =>
      rw [PMF.pure_map] at heq
      rw [pure_inj heq, Function.update_eq_self]
      rcases hC with ⟨hph, hrd, hest, hc⟩ | ⟨hF, hc⟩
      · rw [pure_inj hc, pack_core_update g (cpack_setProc c id _)]
        refine flatGroup_visible_step P _ _ hl _ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]
          refine ABAProcStep.callG_loop _ _ r b ?_ ?_ ?_
          · exact hph
          · exact hrd
          · exact hest
        · rw [Function.update_of_ne hm]; exact ABAProcStep.callGIdle _ _ r id b (Ne.symm hm)
      · rw [pure_inj hc]
        refine flatGroup_visible_step P _ _ hl _ fun m => ?_
        by_cases hm : m = id
        · subst hm; exact ABAProcStep.callGByz_loop _ _ r b hF
        · exact ABAProcStep.callGIdle _ _ r id b (Ne.symm hm)
  | retG r id out =>
    -- The stage evidence fixes the grade; the round loop is honest or corrupted.
    obtain ⟨μr, hx, heq⟩ := implFamily_owned_inv rfl hl hG
    rw [coreStep_retG_iff] at hC
    cases hx with
    | retA =>
      rename_i v hcnt hret
      rw [PMF.pure_map] at heq
      rw [pure_inj heq]
      rcases hC with ⟨hph, hrd, hc⟩ | ⟨hF, hc⟩
      · rw [pure_inj hc, pack_both_update (GBCA.unpack_setProc (g r) id _)
          (cpack_setProc c id _)]
        refine flatGroup_visible_step P _ _ hl _ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]
          exact ABAProcStep.retG_A _ _ r v hph hrd hcnt hret
        · rw [Function.update_of_ne hm]; exact ABAProcStep.retGIdle _ _ r id _ (Ne.symm hm)
      · rw [pure_inj hc, pack_stage_update c (GBCA.unpack_setProc (g r) id _)]
        refine flatGroup_visible_step P _ _ hl _ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]
          exact ABAProcStep.retGByz_A _ _ r v hF hcnt hret
        · rw [Function.update_of_ne hm]; exact ABAProcStep.retGIdle _ _ r id _ (Ne.symm hm)
    | retB =>
      rename_i v hcnt honce hvote hval hret
      rw [PMF.pure_map] at heq
      rw [pure_inj heq]
      rcases hC with ⟨hph, hrd, hc⟩ | ⟨hF, hc⟩
      · rw [pure_inj hc, pack_both_update (GBCA.unpack_setProc (g r) id _)
          (cpack_setProc c id _)]
        refine flatGroup_visible_step P _ _ hl _ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]
          exact ABAProcStep.retG_B _ _ r v hph hrd hcnt honce hvote hval hret
        · rw [Function.update_of_ne hm]; exact ABAProcStep.retGIdle _ _ r id _ (Ne.symm hm)
      · rw [pure_inj hc, pack_stage_update c (GBCA.unpack_setProc (g r) id _)]
        refine flatGroup_visible_step P _ _ hl _ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]
          exact ABAProcStep.retGByz_B _ _ r v hF hcnt honce hvote hval hret
        · rw [Function.update_of_ne hm]; exact ABAProcStep.retGIdle _ _ r id _ (Ne.symm hm)
    | retC =>
      rename_i hcnt hval hret
      rw [PMF.pure_map] at heq
      rw [pure_inj heq]
      rcases hC with ⟨hph, hrd, hc⟩ | ⟨hF, hc⟩
      · rw [pure_inj hc, pack_both_update (GBCA.unpack_setProc (g r) id _)
          (cpack_setProc c id _)]
        refine flatGroup_visible_step P _ _ hl _ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]
          exact ABAProcStep.retG_C _ _ r hph hrd hcnt hval hret
        · rw [Function.update_of_ne hm]; exact ABAProcStep.retGIdle _ _ r id _ (Ne.symm hm)
      · rw [pure_inj hc, pack_stage_update c (GBCA.unpack_setProc (g r) id _)]
        refine flatGroup_visible_step P _ _ hl _ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]
          exact ABAProcStep.retGByz_C _ _ r hF hcnt hval hret
        · rw [Function.update_of_ne hm]; exact ABAProcStep.retGIdle _ _ r id _ (Ne.symm hm)
  | callW r id =>
    -- Only the round loop is here; the coin box answers outside the group.
    rw [pure_inj (implFamily_idle_inv rfl (by simp [Lab.isFail]) hl hG)]
    rw [coreStep_callW_iff] at hC
    rcases hC with ⟨hph, hrd, hc⟩ | ⟨hF, hc⟩
    · rw [pure_inj hc, pack_core_update g (cpack_setProc c id _)]
      refine flatGroup_visible_step P _ _ hl _ fun m => ?_
      by_cases hm : m = id
      · subst hm; rw [Function.update_self]; exact ABAProcStep.callW _ _ r hph hrd
      · rw [Function.update_of_ne hm]; exact ABAProcStep.callWIdle _ _ r id (Ne.symm hm)
    · rw [pure_inj hc]
      refine flatGroup_visible_step P _ _ hl _ fun m => ?_
      by_cases hm : m = id
      · subst hm; exact ABAProcStep.callWByz _ _ r hF
      · exact ABAProcStep.callWIdle _ _ r id (Ne.symm hm)
  | retW r id co =>
    rw [pure_inj (implFamily_idle_inv rfl (by simp [Lab.isFail]) hl hG)]
    rw [coreStep_retW_iff] at hC
    rcases hC with ⟨hph, hrd, hc⟩ | ⟨hF, hc⟩
    · rw [pure_inj hc, pack_core_update g (cpack_stepRound c id co)]
      refine flatGroup_visible_step P _ _ hl _ fun m => ?_
      by_cases hm : m = id
      · subst hm; rw [Function.update_self]; exact ABAProcStep.retW _ _ r co hph hrd
      · rw [Function.update_of_ne hm]; exact ABAProcStep.retWIdle _ _ r id co (Ne.symm hm)
    · rw [pure_inj hc]
      refine flatGroup_visible_step P _ _ hl _ fun m => ?_
      by_cases hm : m = id
      · subst hm; exact ABAProcStep.retWByz _ _ r co hF
      · exact ABAProcStep.retWIdle _ _ r id co (Ne.symm hm)
  | fail k =>
    -- Corruption: every copy of the corrupted set is written at once.
    rw [coreStep_fail_iff] at hC
    rw [pure_inj (implFamily_fail_inv hG), pure_inj hC, pack_corrupt]
    exact flatGroup_visible_step P _ _ hl _ fun m => ABAProcStep.fail _ _ k

/-- **The round loop's silent rules.** The DECIDED echo and the corrupted
injection are one process's own `τ`; a DECIDED delivery is the hidden `dnet`
rendezvous of its sender and its receiver. -/
theorem flatGroup_tau_of_core (P : Params) (g : ℕ → GBCA.ImplState P.n)
    {c c' : CoreState P.n} (hC : CoreStep P c .tau (PMF.pure c')) :
    (flatGroup P).step (pack g c) .tau (PMF.pure (pack g c')) := by
  rw [coreStep_tau_iff] at hC
  rcases hC with ⟨i, k, b, hs, hr, hc⟩ | ⟨id, b, hcnt, hsent, hc⟩ | ⟨id, b, hF, hc⟩
  · obtain rfl := pure_inj hc
    rw [pack_core_update g (cpack_recvDec c i k b)]
    refine flatGroup_net_step P _ (.dnet i k b) _ fun m => ?_
    by_cases hmi : m = i
    · subst hmi
      rw [Function.update_self]
      by_cases hmk : m = k
      · subst hmk; exact ABAProcStep.dnetSelf _ _ b hs hr
      · exact ABAProcStep.dnetRecv _ _ k b (Ne.symm hmk) hr
    · rw [Function.update_of_ne hmi]
      by_cases hmk : m = k
      · subst hmk; exact ABAProcStep.dnetSend _ _ i b (Ne.symm hmi) hs
      · exact ABAProcStep.dnetIdle _ _ i k b (Ne.symm hmi) (Ne.symm hmk)
  · obtain rfl := pure_inj hc
    rw [pack_core_update g (cpack_sendDec c id b)]
    exact flatGroup_tau_step P _ id _ (ABAProcStep.echo _ _ b hcnt hsent)
  · obtain rfl := pure_inj hc
    rw [pack_core_update g (cpack_sendDec c id b)]
    exact flatGroup_tau_step P _ id _ (ABAProcStep.byzDecided _ _ b hF)

/-- **A stage's silent rules.** Each local send of stage `r` is one process's own
`τ`; a stage delivery is the hidden `gnet` rendezvous of its two ends. -/
theorem flatGroup_tau_of_impl (P : Params) {g g' : ℕ → GBCA.ImplState P.n}
    (c : CoreState P.n) (hG : (GBCA.implFamily P).step g .tau (PMF.pure g')) :
    (flatGroup P).step (pack g c) .tau (PMF.pure (pack g' c)) := by
  obtain ⟨r, μr, hx, heq⟩ := implFamily_tau_inv hG
  cases hx with
  | deliver =>
    rename_i i k msg hmsg
    rw [PMF.pure_map] at heq
    obtain rfl := pure_inj heq
    rw [pack_stage_update c (GBCA.unpack_recvMsg (g r) i k msg)]
    refine flatGroup_net_step P _ (.gnet r i k msg) _ fun m => ?_
    by_cases hmi : m = i
    · subst hmi
      rw [Function.update_self]
      by_cases hmk : m = k
      · subst hmk; exact ABAProcStep.gnetSelf _ _ r msg hmsg
      · exact ABAProcStep.gnetRecv _ _ r k msg (Ne.symm hmk)
    · rw [Function.update_of_ne hmi]
      by_cases hmk : m = k
      · subst hmk; exact ABAProcStep.gnetSend _ _ r i msg (Ne.symm hmi) hmsg
      · exact ABAProcStep.gnetIdle _ _ r i k msg (Ne.symm hmi) (Ne.symm hmk)
  | relay =>
    rename_i x b hin hcnt hsend
    rw [PMF.pure_map] at heq
    obtain rfl := pure_inj heq
    rw [pack_stage_update c (GBCA.unpack_send (g r) x _ _)]
    exact flatGroup_tau_step P _ x _ (ABAProcStep.stageRelay _ _ r b hin hcnt hsend)
  | echo =>
    rename_i x b hin hcnt hsend
    rw [PMF.pure_map] at heq
    obtain rfl := pure_inj heq
    rw [pack_stage_update c (GBCA.unpack_send (g r) x _ _)]
    exact flatGroup_tau_step P _ x _ (ABAProcStep.stageEcho _ _ r b hin hcnt hsend)
  | voteBit =>
    rename_i x b hin hcnt hsend
    rw [PMF.pure_map] at heq
    obtain rfl := pure_inj heq
    rw [pack_stage_update c (GBCA.unpack_send (g r) x _ _)]
    exact flatGroup_tau_step P _ x _ (ABAProcStep.stageVoteBit _ _ r b hin hcnt hsend)
  | voteBot =>
    rename_i x hin hcnt hval hsend
    rw [PMF.pure_map] at heq
    obtain rfl := pure_inj heq
    rw [pack_stage_update c (GBCA.unpack_send (g r) x _ _)]
    exact flatGroup_tau_step P _ x _ (ABAProcStep.stageVoteBot _ _ r hin hcnt hval hsend)
  | bindBit =>
    rename_i x b hin hcnt hsend
    rw [PMF.pure_map] at heq
    obtain rfl := pure_inj heq
    rw [pack_stage_update c (GBCA.unpack_send (g r) x _ _)]
    exact flatGroup_tau_step P _ x _ (ABAProcStep.stageBindBit _ _ r b hin hcnt hsend)
  | bindBot =>
    rename_i x hin hcnt hval hsend
    rw [PMF.pure_map] at heq
    obtain rfl := pure_inj heq
    rw [pack_stage_update c (GBCA.unpack_send (g r) x _ _)]
    exact flatGroup_tau_step P _ x _ (ABAProcStep.stageBindBot _ _ r hin hcnt hval hsend)
  | byz =>
    rename_i x msg hF
    rw [PMF.pure_map] at heq
    obtain rfl := pure_inj heq
    rw [pack_stage_update c (GBCA.unpack_mcast (g r) x msg)]
    exact flatGroup_tau_step P _ x _ (ABAProcStep.stageByz _ _ r msg hF)

/-! ### The group layer: reading flat transitions back

Each flat rule is read back as the rule of the round loop it drives, together
with the rule of the stage it drives, if any. The stage half is read through the
per-process presentation of one graded-agreement instance
(`GBCA.impl_step_of_perProc`), which is what turns a rendezvous into
`GBCA.ImplStep.deliver` and an interleaved send into the monolithic send. -/

/-- The target of a synchronised move, read off componentwise. -/
private theorem sync_target {P : Params} {μ_ : Fin P.n → PMF (ABANode P.n)}
    {p' x : ∀ _ : Fin P.n, ABANode P.n}
    (hμ : (PMF.pure p' : PMF (∀ _ : Fin P.n, ABANode P.n)) = piPMF μ_)
    (h : ∀ m, μ_ m = PMF.pure (x m)) : p' = x := by
  rw [funext h, piPMF_pure] at hμ
  exact pure_inj hμ

/-- A stage update at round `r` that moves every process's row. -/
theorem pack_stage_all {P : Params} {g : ℕ → GBCA.ImplState P.n} (c : CoreState P.n)
    {r : ℕ} {s' : GBCA.ImplState P.n} :
    pack (Function.update g r s') c
      = fun m => ((pack g c m).1, Function.update (pack g c m).2 r (GBCA.unpack s' m)) := by
  funext m
  refine Prod.ext rfl (funext fun r' => ?_)
  change GBCA.unpack (Function.update g r s' r') m
    = Function.update (fun rr => GBCA.unpack (g rr) m) r (GBCA.unpack s' m) r'
  by_cases hr : r' = r
  · subst hr; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hr, Function.update_of_ne hr]

/-- One process's interleaved stage send, read as a monolithic stage send. -/
private theorem implStep_of_stage_tau {P : Params} {r : ℕ} {q : GBCA.ImplState P.n}
    {m : Fin P.n} {y : GBCA.ProcNode P.n}
    (h : GBCA.ProcStep P r m (GBCA.unpack q m) (Sum.inl Lab.tau) (PMF.pure y)) :
    ∃ q', Function.update (GBCA.unpack q) m y = GBCA.unpack q' ∧
      GBCA.ImplStep P r q .tau (PMF.pure q') :=
  GBCA.impl_step_of_perProc ((GBCA.perProcInst_step_iff P r _ _ _).mpr
    (Or.inr (Or.inr ⟨rfl, m, PMF.pure y, h, by rw [piPMF_update_pure, PMF.pure_map]⟩)))

/-- A stage rendezvous, read as a monolithic stage delivery. -/
private theorem implStep_of_stage_net {P : Params} {r : ℕ} {q : GBCA.ImplState P.n}
    {i k : Fin P.n} {msg : GBCA.Msg} {x : ∀ _ : Fin P.n, GBCA.ProcNode P.n}
    (h : ∀ m, GBCA.ProcStep P r m (GBCA.unpack q m) (Sum.inr (GBCA.GNet.net i k msg))
      (PMF.pure (x m))) :
    ∃ q', x = GBCA.unpack q' ∧ GBCA.ImplStep P r q .tau (PMF.pure q') :=
  GBCA.impl_step_of_perProc ((GBCA.perProcInst_step_iff P r _ _ _).mpr
    (Or.inl ⟨rfl, i, k, msg,
      Or.inl ⟨by simp, fun m => PMF.pure (x m), h, (piPMF_pure x).symm⟩⟩))

/-! #### One process's rules, by label class -/

section Inversion

variable {P : Params} {j : Fin P.n} {q : ABANode P.n} {μ : PMF (ABANode P.n)}

theorem flat_callABA_own {b : Bool}
    (h : ABAProcStep P j q (Sum.inl (.callABA j b)) μ) :
    (q.1.proc.input = none ∧
      μ = PMF.pure (q.1.setProc { q.1.proc with
        input := some b, est := some b, round := 0, phase := .toCallG }, q.2)) ∨
    μ = PMF.pure q := by
  cases h
  case input => exact Or.inl ⟨by assumption, rfl⟩
  case inputLoop => exact Or.inr rfl
  case callABAIdle => exact absurd rfl ‹_ ≠ j›

theorem flat_callABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ABAProcStep P j q (Sum.inl (.callABA id b)) μ) : μ = PMF.pure q := by
  cases h
  case input => exact absurd rfl hid
  case inputLoop => exact absurd rfl hid
  case callABAIdle => rfl

theorem flat_retABA_own {b : Bool}
    (h : ABAProcStep P j q (Sum.inl (.retABA j b)) μ) :
    P.n - P.f ≤ q.1.decidedCount b ∧ b ∈ q.1.decOut ∧ q.1.proc.returned = false ∧
      μ = PMF.pure (q.1.setProc { q.1.proc with returned := true }, q.2) := by
  cases h
  case ret => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case retABAIdle => exact absurd rfl ‹_ ≠ j›

theorem flat_retABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ABAProcStep P j q (Sum.inl (.retABA id b)) μ) : μ = PMF.pure q := by
  cases h
  case ret => exact absurd rfl hid
  case retABAIdle => rfl

theorem flat_callG_own {r : ℕ} {b : Bool}
    (h : ABAProcStep P j q (Sum.inl (.callG r j b)) μ) :
    (q.1.proc.phase = .toCallG ∧ q.1.proc.round = r ∧ q.1.proc.est = some b ∧
      ((q.2 r).proc.input = none ∧
        μ = PMF.pure (q.1.setProc { q.1.proc with phase := .awaitG },
          Function.update q.2 r (((q.2 r).setP { (q.2 r).proc with
            input := some b,
            sentInput := Function.update (q.2 r).proc.sentInput b true }).send (.input b)))
       ∨ μ = PMF.pure (q.1.setProc { q.1.proc with phase := .awaitG }, q.2))) ∨
    (j ∈ q.1.F ∧
      ((q.2 r).proc.input = none ∧
        μ = PMF.pure (q.1,
          Function.update q.2 r (((q.2 r).setP { (q.2 r).proc with
            input := some b,
            sentInput := Function.update (q.2 r).proc.sentInput b true }).send (.input b)))
       ∨ μ = PMF.pure q)) := by
  cases h
  case callG_call =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, Or.inl ⟨by assumption, rfl⟩⟩
  case callG_loop =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, Or.inr rfl⟩
  case callGByz_call => exact Or.inr ⟨by assumption, Or.inl ⟨by assumption, rfl⟩⟩
  case callGByz_loop => exact Or.inr ⟨by assumption, Or.inr rfl⟩
  case callGIdle => exact absurd rfl ‹_ ≠ j›

theorem flat_callG_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ABAProcStep P j q (Sum.inl (.callG r id b)) μ) : μ = PMF.pure q := by
  cases h
  case callG_call => exact absurd rfl hid
  case callG_loop => exact absurd rfl hid
  case callGByz_call => exact absurd rfl hid
  case callGByz_loop => exact absurd rfl hid
  case callGIdle => rfl

theorem flat_retG_A_own {r : ℕ} {v : Bool}
    (h : ABAProcStep P j q (Sum.inl (.retG r j (.A v))) μ) :
    P.n - P.f ≤ (q.2 r).recvCount (.bind (some v)) ∧ (q.2 r).proc.returned = false ∧
    ((q.1.proc.phase = .awaitG ∧ q.1.proc.round = r ∧
        μ = PMF.pure (q.1.setProc { q.1.proc with
            est := (GbcaOut.A v).est, lastGrade := some (.A v), phase := .toCallW },
          Function.update q.2 r ((q.2 r).setP { (q.2 r).proc with returned := true }))) ∨
      (j ∈ q.1.F ∧
        μ = PMF.pure (q.1,
          Function.update q.2 r ((q.2 r).setP { (q.2 r).proc with returned := true })))) := by
  cases h
  case retG_A =>
    exact ⟨by assumption, by assumption, Or.inl ⟨by assumption, by assumption, rfl⟩⟩
  case retGByz_A => exact ⟨by assumption, by assumption, Or.inr ⟨by assumption, rfl⟩⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›

theorem flat_retG_B_own {r : ℕ} {v : Bool}
    (h : ABAProcStep P j q (Sum.inl (.retG r j (.B v))) μ) :
    P.n - P.f ≤ (q.2 r).bindCount ∧ (∃ k, GBCA.Msg.bind (some v) ∈ (q.2 r).inbox k) ∧
    P.f + 1 ≤ (q.2 r).recvCount (.vote (some v)) ∧ (q.2 r).bothValid P ∧
    (q.2 r).proc.returned = false ∧
    ((q.1.proc.phase = .awaitG ∧ q.1.proc.round = r ∧
        μ = PMF.pure (q.1.setProc { q.1.proc with
            est := (GbcaOut.B v).est, lastGrade := some (.B v), phase := .toCallW },
          Function.update q.2 r ((q.2 r).setP { (q.2 r).proc with returned := true }))) ∨
      (j ∈ q.1.F ∧
        μ = PMF.pure (q.1,
          Function.update q.2 r ((q.2 r).setP { (q.2 r).proc with returned := true })))) := by
  cases h
  case retG_B =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
      Or.inl ⟨by assumption, by assumption, rfl⟩⟩
  case retGByz_B =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
      Or.inr ⟨by assumption, rfl⟩⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›

theorem flat_retG_C_own {r : ℕ}
    (h : ABAProcStep P j q (Sum.inl (.retG r j .C)) μ) :
    P.n - P.f ≤ (q.2 r).recvCount (.bind none) ∧ (q.2 r).bothValid P ∧
    (q.2 r).proc.returned = false ∧
    ((q.1.proc.phase = .awaitG ∧ q.1.proc.round = r ∧
        μ = PMF.pure (q.1.setProc { q.1.proc with
            est := GbcaOut.C.est, lastGrade := some .C, phase := .toCallW },
          Function.update q.2 r ((q.2 r).setP { (q.2 r).proc with returned := true }))) ∨
      (j ∈ q.1.F ∧
        μ = PMF.pure (q.1,
          Function.update q.2 r ((q.2 r).setP { (q.2 r).proc with returned := true })))) := by
  cases h
  case retG_C =>
    exact ⟨by assumption, by assumption, by assumption,
      Or.inl ⟨by assumption, by assumption, rfl⟩⟩
  case retGByz_C =>
    exact ⟨by assumption, by assumption, by assumption, Or.inr ⟨by assumption, rfl⟩⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›

theorem flat_retG_foreign {r : ℕ} {id : Fin P.n} {out : GbcaOut} (hid : id ≠ j)
    (h : ABAProcStep P j q (Sum.inl (.retG r id out)) μ) : μ = PMF.pure q := by
  cases h
  case retG_A => exact absurd rfl hid
  case retG_B => exact absurd rfl hid
  case retG_C => exact absurd rfl hid
  case retGByz_A => exact absurd rfl hid
  case retGByz_B => exact absurd rfl hid
  case retGByz_C => exact absurd rfl hid
  case retGIdle => rfl

theorem flat_callW_own {r : ℕ}
    (h : ABAProcStep P j q (Sum.inl (.callW r j)) μ) :
    (q.1.proc.phase = .toCallW ∧ q.1.proc.round = r ∧
      μ = PMF.pure (q.1.setProc { q.1.proc with phase := .awaitW }, q.2)) ∨
    (j ∈ q.1.F ∧ μ = PMF.pure q) := by
  cases h
  case callW => exact Or.inl ⟨by assumption, by assumption, rfl⟩
  case callWByz => exact Or.inr ⟨by assumption, rfl⟩
  case callWIdle => exact absurd rfl ‹_ ≠ j›

theorem flat_callW_foreign {r : ℕ} {id : Fin P.n} (hid : id ≠ j)
    (h : ABAProcStep P j q (Sum.inl (.callW r id)) μ) : μ = PMF.pure q := by
  cases h
  case callW => exact absurd rfl hid
  case callWByz => exact absurd rfl hid
  case callWIdle => rfl

theorem flat_retW_own {r : ℕ} {co : Bool}
    (h : ABAProcStep P j q (Sum.inl (.retW r j co)) μ) :
    (q.1.proc.phase = .awaitW ∧ q.1.proc.round = r ∧
      μ = PMF.pure (q.1.stepRound co, q.2)) ∨
    (j ∈ q.1.F ∧ μ = PMF.pure q) := by
  cases h
  case retW => exact Or.inl ⟨by assumption, by assumption, rfl⟩
  case retWByz => exact Or.inr ⟨by assumption, rfl⟩
  case retWIdle => exact absurd rfl ‹_ ≠ j›

theorem flat_retW_foreign {r : ℕ} {id : Fin P.n} {co : Bool} (hid : id ≠ j)
    (h : ABAProcStep P j q (Sum.inl (.retW r id co)) μ) : μ = PMF.pure q := by
  cases h
  case retW => exact absurd rfl hid
  case retWByz => exact absurd rfl hid
  case retWIdle => rfl

theorem flat_fail_inv {k : Fin P.n}
    (h : ABAProcStep P j q (Sum.inl (.fail k)) μ) :
    μ = PMF.pure (q.1.corrupt P k, fun r => (q.2 r).corrupt P k) := by
  cases h
  rfl

theorem flat_tau_inv (h : ABAProcStep P j q (Sum.inl .tau) μ) :
    (∃ b, P.f + 1 ≤ q.1.decidedCount b ∧ b ∉ q.1.decOut ∧
      μ = PMF.pure (q.1.sendDec b, q.2)) ∨
    (∃ b, j ∈ q.1.F ∧ μ = PMF.pure (q.1.sendDec b, q.2)) ∨
    (∃ r y, GBCA.ProcStep P r j (q.2 r) (Sum.inl Lab.tau) (PMF.pure y) ∧
      μ = PMF.pure (q.1, Function.update q.2 r y)) := by
  cases h
  case echo => refine Or.inl ⟨_, ?_, ?_, rfl⟩ <;> assumption
  case byzDecided => exact Or.inr (Or.inl ⟨_, by assumption, rfl⟩)
  case stageRelay =>
    refine Or.inr (Or.inr ⟨_, _, ?_, rfl⟩)
    exact GBCA.ProcStep.relay _ _ (by assumption) (by assumption) (by assumption)
  case stageEcho =>
    refine Or.inr (Or.inr ⟨_, _, ?_, rfl⟩)
    exact GBCA.ProcStep.echo _ _ (by assumption) (by assumption) (by assumption)
  case stageVoteBit =>
    refine Or.inr (Or.inr ⟨_, _, ?_, rfl⟩)
    exact GBCA.ProcStep.voteBit _ _ (by assumption) (by assumption) (by assumption)
  case stageVoteBot =>
    refine Or.inr (Or.inr ⟨_, _, ?_, rfl⟩)
    exact GBCA.ProcStep.voteBot _ (by assumption) (by assumption) (by assumption)
      (by assumption)
  case stageBindBit =>
    refine Or.inr (Or.inr ⟨_, _, ?_, rfl⟩)
    exact GBCA.ProcStep.bindBit _ _ (by assumption) (by assumption) (by assumption)
  case stageBindBot =>
    refine Or.inr (Or.inr ⟨_, _, ?_, rfl⟩)
    exact GBCA.ProcStep.bindBot _ (by assumption) (by assumption) (by assumption)
      (by assumption)
  case stageByz =>
    refine Or.inr (Or.inr ⟨_, _, ?_, rfl⟩)
    exact GBCA.ProcStep.byz _ _ (by assumption)

theorem flat_dnet_inv {i k : Fin P.n} {b : Bool}
    (h : ABAProcStep P j q (Sum.inr (.dnet i k b)) μ) :
    μ = PMF.pure (if j = i then (q.1.recvDec k b, q.2) else q) ∧
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

theorem flat_gnet_inv {r : ℕ} {i k : Fin P.n} {msg : GBCA.Msg}
    (h : ABAProcStep P j q (Sum.inr (.gnet r i k msg)) μ) :
    ∃ y, GBCA.ProcStep P r j (q.2 r) (Sum.inr (GBCA.GNet.net i k msg)) (PMF.pure y) ∧
      μ = PMF.pure (q.1, Function.update q.2 r y) := by
  cases h
  case gnetSelf => exact ⟨_, GBCA.ProcStep.netSelf _ msg (by assumption), rfl⟩
  case gnetSend =>
    exact ⟨_, GBCA.ProcStep.netSend _ i msg (by assumption) (by assumption),
      by rw [Function.update_eq_self]⟩
  case gnetRecv => exact ⟨_, GBCA.ProcStep.netRecv _ k msg (by assumption), rfl⟩
  case gnetIdle =>
    exact ⟨_, GBCA.ProcStep.netIdle _ i k msg (by assumption) (by assumption),
      by rw [Function.update_eq_self]⟩

end Inversion

/-! #### The two monolithic components, recovered -/

/-- The target of an interleaved silent move. -/
private theorem interleave_target {P : Params} {p' x : ∀ _ : Fin P.n, ABANode P.n}
    {m : Fin P.n} {y : ABANode P.n}
    (h : (PMF.pure p' : PMF (∀ _ : Fin P.n, ABANode P.n))
      = piPMF (Function.update (fun k => PMF.pure (x k)) m (PMF.pure y))) :
    p' = Function.update x m y := by
  rw [piPMF_update_eq_pure] at h
  exact pure_inj h

/-- **Visible labels, read back.** A synchronised transition of the process group
on a label other than `τ` is a stage-family transition beside a round-loop
transition on the same label. -/
theorem group_of_flatGroup_visible (P : Params) {g : ℕ → GBCA.ImplState P.n}
    {c : CoreState P.n} {l : Lab P.n} (hl : l ≠ .tau)
    {p' : ∀ _ : Fin P.n, ABANode P.n}
    (h : (flatGroup P).step (pack g c) l (PMF.pure p')) :
    ∃ g' c', p' = pack g' c' ∧ (GBCA.implFamily P).step g l (PMF.pure g') ∧
      CoreStep P c l (PMF.pure c') := by
  rw [flatGroup_step_iff] at h
  rcases h with ⟨rfl, -, -⟩ | hs
  · exact absurd rfl hl
  rw [sync_inl_iff P _ l hl] at hs
  obtain ⟨μ_, hall, hμ⟩ := hs
  cases l with
  | tau => exact absurd rfl hl
  | callABA id b =>
    rcases flat_callABA_own (hall id) with ⟨hin, hd⟩ | hd
    · refine ⟨g, c.setProc id { c.procs id with
          input := some b, est := some b, round := 0, phase := .toCallG }, ?_,
        implFamily_idle_step rfl (by simp [Lab.isFail]) hl,
        (coreStep_callABA_iff P c id b _).mpr (Or.inl ⟨hin, rfl⟩)⟩
      rw [pack_core_update g (cpack_setProc c id _)]
      refine sync_target hμ fun m => ?_
      by_cases hm : m = id
      · subst hm; rw [Function.update_self]; exact hd
      · rw [Function.update_of_ne hm]; exact flat_callABA_foreign (Ne.symm hm) (hall m)
    · refine ⟨g, c, ?_, implFamily_idle_step rfl (by simp [Lab.isFail]) hl,
        (coreStep_callABA_iff P c id b _).mpr (Or.inr rfl)⟩
      refine sync_target hμ fun m => ?_
      by_cases hm : m = id
      · subst hm; exact hd
      · exact flat_callABA_foreign (Ne.symm hm) (hall m)
  | retABA id b =>
    obtain ⟨hcnt, hsent, hret, hd⟩ := flat_retABA_own (hall id)
    refine ⟨g, c.setProc id { c.procs id with returned := true }, ?_,
      implFamily_idle_step rfl (by simp [Lab.isFail]) hl,
      (coreStep_retABA_iff P c id b _).mpr ⟨hcnt, hsent, hret, rfl⟩⟩
    rw [pack_core_update g (cpack_setProc c id _)]
    refine sync_target hμ fun m => ?_
    by_cases hm : m = id
    · subst hm; rw [Function.update_self]; exact hd
    · rw [Function.update_of_ne hm]; exact flat_retABA_foreign (Ne.symm hm) (hall m)
  | callG r id b =>
    rcases flat_callG_own (hall id) with ⟨hph, hrd, hest, hst⟩ | ⟨hF, hst⟩
    · rcases hst with ⟨hin, hd⟩ | hd
      · refine ⟨_, c.setProc id { c.procs id with phase := .awaitG }, ?_,
          implFamily_owned_step rfl (GBCA.ImplStep.call (g r) id b hin),
          (coreStep_callG_iff P c r id b _).mpr (Or.inl ⟨hph, hrd, hest, rfl⟩)⟩
        rw [pack_both_update (GBCA.unpack_send (g r) id _ _) (cpack_setProc c id _)]
        refine sync_target hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]; exact hd
        · rw [Function.update_of_ne hm]; exact flat_callG_foreign (Ne.symm hm) (hall m)
      · refine ⟨g, c.setProc id { c.procs id with phase := .awaitG }, ?_, ?_,
          (coreStep_callG_iff P c r id b _).mpr (Or.inl ⟨hph, hrd, hest, rfl⟩)⟩
        · rw [pack_core_update g (cpack_setProc c id _)]
          refine sync_target hμ fun m => ?_
          by_cases hm : m = id
          · subst hm; rw [Function.update_self]; exact hd
          · rw [Function.update_of_ne hm]; exact flat_callG_foreign (Ne.symm hm) (hall m)
        · have hstep := implFamily_owned_step (g := g) (l := Lab.callG r id b) (r := r)
            (x := g r) rfl (GBCA.ImplStep.callLoop (g r) id b)
          rwa [Function.update_eq_self] at hstep
    · rcases hst with ⟨hin, hd⟩ | hd
      · refine ⟨_, c, ?_, implFamily_owned_step rfl (GBCA.ImplStep.call (g r) id b hin),
          (coreStep_callG_iff P c r id b _).mpr (Or.inr ⟨hF, rfl⟩)⟩
        rw [pack_stage_update c (GBCA.unpack_send (g r) id _ _)]
        refine sync_target hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]; exact hd
        · rw [Function.update_of_ne hm]; exact flat_callG_foreign (Ne.symm hm) (hall m)
      · refine ⟨g, c, ?_, ?_, (coreStep_callG_iff P c r id b _).mpr (Or.inr ⟨hF, rfl⟩)⟩
        · refine sync_target hμ fun m => ?_
          by_cases hm : m = id
          · subst hm; exact hd
          · exact flat_callG_foreign (Ne.symm hm) (hall m)
        · have hstep := implFamily_owned_step (g := g) (l := Lab.callG r id b) (r := r)
            (x := g r) rfl (GBCA.ImplStep.callLoop (g r) id b)
          rwa [Function.update_eq_self] at hstep
  | retG r id out =>
    cases out with
    | A v =>
      obtain ⟨hcnt, hret, hd⟩ := flat_retG_A_own (hall id)
      rcases hd with ⟨hph, hrd, hd⟩ | ⟨hF, hd⟩
      · refine ⟨_, c.setProc id { c.procs id with
            est := (GbcaOut.A v).est, lastGrade := some (.A v), phase := .toCallW }, ?_,
          implFamily_owned_step rfl (GBCA.ImplStep.retA (g r) id v hcnt hret),
          (coreStep_retG_iff P c r id (.A v) _).mpr (Or.inl ⟨hph, hrd, rfl⟩)⟩
        rw [pack_both_update (GBCA.unpack_setProc (g r) id _) (cpack_setProc c id _)]
        refine sync_target hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]; exact hd
        · rw [Function.update_of_ne hm]; exact flat_retG_foreign (Ne.symm hm) (hall m)
      · refine ⟨_, c, ?_,
          implFamily_owned_step rfl (GBCA.ImplStep.retA (g r) id v hcnt hret),
          (coreStep_retG_iff P c r id (.A v) _).mpr (Or.inr ⟨hF, rfl⟩)⟩
        rw [pack_stage_update c (GBCA.unpack_setProc (g r) id _)]
        refine sync_target hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]; exact hd
        · rw [Function.update_of_ne hm]; exact flat_retG_foreign (Ne.symm hm) (hall m)
    | B v =>
      obtain ⟨hcnt, honce, hvote, hval, hret, hd⟩ := flat_retG_B_own (hall id)
      rcases hd with ⟨hph, hrd, hd⟩ | ⟨hF, hd⟩
      · refine ⟨_, c.setProc id { c.procs id with
            est := (GbcaOut.B v).est, lastGrade := some (.B v), phase := .toCallW }, ?_,
          implFamily_owned_step rfl
            (GBCA.ImplStep.retB (g r) id v hcnt honce hvote hval hret),
          (coreStep_retG_iff P c r id (.B v) _).mpr (Or.inl ⟨hph, hrd, rfl⟩)⟩
        rw [pack_both_update (GBCA.unpack_setProc (g r) id _) (cpack_setProc c id _)]
        refine sync_target hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]; exact hd
        · rw [Function.update_of_ne hm]; exact flat_retG_foreign (Ne.symm hm) (hall m)
      · refine ⟨_, c, ?_,
          implFamily_owned_step rfl
            (GBCA.ImplStep.retB (g r) id v hcnt honce hvote hval hret),
          (coreStep_retG_iff P c r id (.B v) _).mpr (Or.inr ⟨hF, rfl⟩)⟩
        rw [pack_stage_update c (GBCA.unpack_setProc (g r) id _)]
        refine sync_target hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]; exact hd
        · rw [Function.update_of_ne hm]; exact flat_retG_foreign (Ne.symm hm) (hall m)
    | C =>
      obtain ⟨hcnt, hval, hret, hd⟩ := flat_retG_C_own (hall id)
      rcases hd with ⟨hph, hrd, hd⟩ | ⟨hF, hd⟩
      · refine ⟨_, c.setProc id { c.procs id with
            est := GbcaOut.C.est, lastGrade := some .C, phase := .toCallW }, ?_,
          implFamily_owned_step rfl (GBCA.ImplStep.retC (g r) id hcnt hval hret),
          (coreStep_retG_iff P c r id .C _).mpr (Or.inl ⟨hph, hrd, rfl⟩)⟩
        rw [pack_both_update (GBCA.unpack_setProc (g r) id _) (cpack_setProc c id _)]
        refine sync_target hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]; exact hd
        · rw [Function.update_of_ne hm]; exact flat_retG_foreign (Ne.symm hm) (hall m)
      · refine ⟨_, c, ?_,
          implFamily_owned_step rfl (GBCA.ImplStep.retC (g r) id hcnt hval hret),
          (coreStep_retG_iff P c r id .C _).mpr (Or.inr ⟨hF, rfl⟩)⟩
        rw [pack_stage_update c (GBCA.unpack_setProc (g r) id _)]
        refine sync_target hμ fun m => ?_
        by_cases hm : m = id
        · subst hm; rw [Function.update_self]; exact hd
        · rw [Function.update_of_ne hm]; exact flat_retG_foreign (Ne.symm hm) (hall m)
  | callW r id =>
    rcases flat_callW_own (hall id) with ⟨hph, hrd, hd⟩ | ⟨hF, hd⟩
    · refine ⟨g, c.setProc id { c.procs id with phase := .awaitW }, ?_,
        implFamily_idle_step rfl (by simp [Lab.isFail]) hl,
        (coreStep_callW_iff P c r id _).mpr (Or.inl ⟨hph, hrd, rfl⟩)⟩
      rw [pack_core_update g (cpack_setProc c id _)]
      refine sync_target hμ fun m => ?_
      by_cases hm : m = id
      · subst hm; rw [Function.update_self]; exact hd
      · rw [Function.update_of_ne hm]; exact flat_callW_foreign (Ne.symm hm) (hall m)
    · refine ⟨g, c, ?_, implFamily_idle_step rfl (by simp [Lab.isFail]) hl,
        (coreStep_callW_iff P c r id _).mpr (Or.inr ⟨hF, rfl⟩)⟩
      refine sync_target hμ fun m => ?_
      by_cases hm : m = id
      · subst hm; exact hd
      · exact flat_callW_foreign (Ne.symm hm) (hall m)
  | retW r id co =>
    rcases flat_retW_own (hall id) with ⟨hph, hrd, hd⟩ | ⟨hF, hd⟩
    · refine ⟨g, c.stepRound id co, ?_,
        implFamily_idle_step rfl (by simp [Lab.isFail]) hl,
        (coreStep_retW_iff P c r id co _).mpr (Or.inl ⟨hph, hrd, rfl⟩)⟩
      rw [pack_core_update g (cpack_stepRound c id co)]
      refine sync_target hμ fun m => ?_
      by_cases hm : m = id
      · subst hm; rw [Function.update_self]; exact hd
      · rw [Function.update_of_ne hm]; exact flat_retW_foreign (Ne.symm hm) (hall m)
    · refine ⟨g, c, ?_, implFamily_idle_step rfl (by simp [Lab.isFail]) hl,
        (coreStep_retW_iff P c r id co _).mpr (Or.inr ⟨hF, rfl⟩)⟩
      refine sync_target hμ fun m => ?_
      by_cases hm : m = id
      · subst hm; exact hd
      · exact flat_retW_foreign (Ne.symm hm) (hall m)
  | fail k =>
    refine ⟨fun r => (g r).corrupt P k, c.corrupt P k, ?_, implFamily_fail_step k,
      (coreStep_fail_iff P c k _).mpr rfl⟩
    rw [pack_corrupt]
    exact sync_target hμ fun m => flat_fail_inv (hall m)

/-- **Silent labels, read back.** A silent transition of the process group is
either a round-loop silent rule — an interleaved send or a hidden DECIDED
rendezvous — or a stage-family silent rule. -/
theorem group_of_flatGroup_tau (P : Params) {g : ℕ → GBCA.ImplState P.n}
    {c : CoreState P.n} {p' : ∀ _ : Fin P.n, ABANode P.n}
    (h : (flatGroup P).step (pack g c) .tau (PMF.pure p')) :
    (∃ c', p' = pack g c' ∧ CoreStep P c .tau (PMF.pure c')) ∨
    (∃ g', p' = pack g' c ∧ (GBCA.implFamily P).step g .tau (PMF.pure g')) := by
  rw [flatGroup_step_iff] at h
  rcases h with ⟨-, e, hs⟩ | hs
  · rw [sync_visible_iff P _ (Sum.inr e) (by simp)] at hs
    obtain ⟨μ_, hall, hμ⟩ := hs
    cases e with
    | gnet r i k msg =>
      choose y hy hμy using fun m => flat_gnet_inv (hall m)
      obtain ⟨q', hq', himpl⟩ := implStep_of_stage_net (q := g r) hy
      refine Or.inr ⟨Function.update g r q', ?_, implFamily_tau_step himpl⟩
      rw [pack_stage_all c, ← hq']
      exact sync_target hμ hμy
    | dnet i k b =>
      have hsent := (flat_dnet_inv (hall k)).2.1 rfl
      have hfresh := (flat_dnet_inv (hall i)).2.2 rfl
      refine Or.inl ⟨c.deliverDecided i k b, ?_, CoreStep.deliver c i k b hsent hfresh⟩
      rw [pack_core_update g (cpack_recvDec c i k b)]
      refine sync_target hμ fun m => ?_
      rw [(flat_dnet_inv (hall m)).1]
      by_cases hm : m = i
      · subst hm; rw [if_pos rfl, Function.update_self]; rfl
      · rw [if_neg hm, Function.update_of_ne hm]
  · rw [sync_tau_iff] at hs
    obtain ⟨m, ν, hstep, hμ⟩ := hs
    rcases flat_tau_inv hstep with ⟨b, hcnt, hsent, rfl⟩ | ⟨b, hF, rfl⟩ | ⟨r, y, hps, rfl⟩
    · refine Or.inl ⟨c.sendDecided m b, ?_, CoreStep.echo c m b hcnt hsent⟩
      rw [pack_core_update g (cpack_sendDec c m b)]
      exact interleave_target hμ
    · refine Or.inl ⟨c.sendDecided m b, ?_, CoreStep.byzDecided c m b hF⟩
      rw [pack_core_update g (cpack_sendDec c m b)]
      exact interleave_target hμ
    · obtain ⟨q', hq', himpl⟩ := implStep_of_stage_tau (q := g r) hps
      refine Or.inr ⟨Function.update g r q', ?_, implFamily_tau_step himpl⟩
      rw [pack_stage_update c hq'.symm]
      exact interleave_target hμ

/-! ### The outer layer: the coin oracle beside the group

The coin box occupies the same slot in both systems and is never unfolded: on a
visible label it is carried through the synchronisation untouched, and its own
resolution appears on both sides as the same pushforward of `Params.coinPMF`. -/

private theorem prodPMF_pure_pure {α β : Type} (a : α) (b : β) :
    prodPMF (PMF.pure a) (PMF.pure b) = PMF.pure (a, b) := by
  rw [prodPMF_pure_left, PMF.pure_map]

private theorem map_unflat_prod {P : Params} (g : ℕ → GBCA.ImplState P.n)
    (c : CoreState P.n) (μ_w : PMF (ℕ → WCC.SpecState P.n)) :
    (prodPMF (PMF.pure g) (prodPMF (PMF.pure c) μ_w)).map unflat
      = prodPMF (PMF.pure (pack g c)) μ_w := by
  rw [prodPMF_pure_left, prodPMF_pure_left, prodPMF_pure_left, PMF.map_comp, PMF.map_comp]
  rfl

/-- **Every transition of the hybrid is the matching flat transition.** -/
theorem flatPre_step_of_preImpl (P : Params)
    (s : (ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))
    (l : Lab P.n)
    (μ : PMF ((ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n))))
    (h : (preImpl P).step s l μ) :
    (flatPre P).step (unflat s) l (μ.map unflat) := by
  obtain ⟨g, c, w⟩ := s
  rcases h with ⟨hl, μ₁, μ₂₃, hG, hCW, rfl⟩ | ⟨rfl, μ₁, hG, rfl⟩ | ⟨rfl, μ₂₃, hCW, rfl⟩
  · -- A visible label: both families and the coin box move together.
    obtain ⟨g', rfl⟩ := GBCA.implFamily_isLTS P _ _ _ hG
    rcases hCW with ⟨-, μ₂, μ_w, hC, hW, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
    · obtain ⟨c', rfl⟩ := core_isLTS P _ _ _ hC
      rw [map_unflat_prod]
      exact Or.inl ⟨hl, _, μ_w, flatGroup_visible_of_group P hl hG hC, hW, rfl⟩
    · exact absurd hτ hl
    · exact absurd hτ hl
  · -- A stage's own silent rule.
    obtain ⟨g', rfl⟩ := GBCA.implFamily_isLTS P _ _ _ hG
    refine Or.inr (Or.inl ⟨rfl, PMF.pure (pack g' c), flatGroup_tau_of_impl P c hG, ?_⟩)
    rw [prodPMF_pure_pure, PMF.pure_map, prodPMF_pure_pure]
    rfl
  · rcases hCW with ⟨hτ, -⟩ | ⟨-, μ₂, hC, rfl⟩ | ⟨-, μ_w, hW, rfl⟩
    · exact absurd rfl hτ
    · -- The round loop's own silent rule.
      obtain ⟨c', rfl⟩ := core_isLTS P _ _ _ hC
      refine Or.inr (Or.inl ⟨rfl, PMF.pure (pack g c'), flatGroup_tau_of_core P g hC, ?_⟩)
      rw [prodPMF_pure_pure, prodPMF_pure_pure, PMF.pure_map, prodPMF_pure_pure]
      rfl
    · -- The coin resolution: the same pushforward on both sides.
      rw [map_unflat_prod]
      exact Or.inr (Or.inr ⟨rfl, μ_w, hW, rfl⟩)

/-- **Every flat transition from a packed state is the matching hybrid
transition.** -/
theorem preImpl_step_of_flatPre (P : Params)
    (s : (ℕ → GBCA.ImplState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n)))
    (l : Lab P.n)
    (μ : PMF ((∀ _ : Fin P.n, ABANode P.n) × (ℕ → WCC.SpecState P.n)))
    (h : (flatPre P).step (unflat s) l μ) :
    ∃ ν, (preImpl P).step s l ν ∧ μ = ν.map unflat := by
  obtain ⟨g, c, w⟩ := s
  rcases h with ⟨hl, μ₁, μ_w, hF, hW, rfl⟩ | ⟨rfl, μ₁, hF, rfl⟩ | ⟨rfl, μ_w, hW, rfl⟩
  · obtain ⟨p', rfl⟩ := flatGroup_isLTS P _ _ _ hF
    obtain ⟨g', c', rfl, hG, hC⟩ := group_of_flatGroup_visible P hl hF
    exact ⟨prodPMF (PMF.pure g') (prodPMF (PMF.pure c') μ_w),
      Or.inl ⟨hl, _, _, hG, Or.inl ⟨hl, _, μ_w, hC, hW, rfl⟩, rfl⟩,
      (map_unflat_prod g' c' μ_w).symm⟩
  · obtain ⟨p', rfl⟩ := flatGroup_isLTS P _ _ _ hF
    rcases group_of_flatGroup_tau P hF with ⟨c', rfl, hC⟩ | ⟨g', rfl, hG⟩
    · refine ⟨prodPMF (PMF.pure g) (prodPMF (PMF.pure c') (PMF.pure w)),
        Or.inr (Or.inr ⟨rfl, _, Or.inr (Or.inl ⟨rfl, _, hC, rfl⟩), rfl⟩), ?_⟩
      rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure, PMF.pure_map]
      rfl
    · refine ⟨prodPMF (PMF.pure g') (PMF.pure (c, w)),
        Or.inr (Or.inl ⟨rfl, _, hG, rfl⟩), ?_⟩
      rw [prodPMF_pure_pure, prodPMF_pure_pure, PMF.pure_map]
      rfl
  · exact ⟨prodPMF (PMF.pure g) (prodPMF (PMF.pure c) μ_w),
      Or.inr (Or.inr ⟨rfl, _, Or.inr (Or.inr ⟨rfl, μ_w, hW, rfl⟩), rfl⟩),
      (map_unflat_prod g c μ_w).symm⟩

/-! ### The two simulations

The forward direction is a strong functional matching along `unflat`. The
backward direction is its converse: `unflat` is not injective — flat states whose
copies of the corrupted set disagree have no preimage — but it reflects steps,
which is enough to run the same coupling backwards along its graph. -/

/-- The flat presentation simulates the hybrid, along the graph of the packing
map. -/
theorem flatSim (P : Params) :
    ProbabilisticForwardSimulation (preImpl P) (flatPre P)
      (fun s ν => ν = PMF.pure (unflat s)) :=
  ProbabilisticForwardSimulation.ofStrongFunctional unflat rfl (flatPre_step_of_preImpl P)

/-- The hybrid simulates the flat presentation, along the same graph read
backwards. -/
theorem flatSimConverse (P : Params) :
    ProbabilisticForwardSimulation (flatPre P) (preImpl P)
      (fun p ν => ∃ q, ν = PMF.pure q ∧ p = unflat q) :=
  ProbabilisticForwardSimulation.ofStrongFunctional_converse unflat rfl
    (fun q l μ h => preImpl_step_of_flatPre P q l μ h)

/-! ### The equivalence -/

/-- **The flat presentation is the hybrid.** Reading the protocol as one program
per process, with the two networks hidden and the coin oracle the one component
that is not a process, neither adds nor removes observable behaviour. -/
theorem flatABA_atd (P : Params) :
    achievableTraceDists (flatHybrid P) = achievableTraceDists (hybridImpl P) :=
  Set.Subset.antisymm
    (((flatSimConverse P).abstract (Lab.hiddenAPI P.n)).achievableTraceDists_subset)
    (((flatSim P).abstract (Lab.hiddenAPI P.n)).achievableTraceDists_subset)

/-- **Safety of the flat presentation**: every positive-probability trace of the
flat hybrid satisfies Validity and Agreement. The scope is that of `ABA.main` —
safety only, with the coin held at specification level. -/
theorem flatABA_safe (P : Params) :
    ∀ D ∈ achievableTraceDists (flatHybrid P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace t := by
  rw [flatABA_atd]
  exact main P

/-! ### Mechanical axiom firewall

Neither headline may acquire a `sorryAx` dependence. -/

/-- info: 'PLTS.ABA.Flat.flatABA_atd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flatABA_atd

/-- info: 'PLTS.ABA.Flat.flatABA_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flatABA_safe

end Flat
end ABA
end PLTS
