/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2.Systems.LTS
import Leslie2Protocols.ABA.Labels

/-!
# The ABA core (blueprint Algorithm 1)

The round-loop control component of ABDY22's Asynchronous Byzantine Agreement
protocol (blueprint Algorithm 1), as an LTS over the shared alphabet
`ABA.Lab n`. Per process, on external input `b`:

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

The sub-protocol interactions are pure handshakes over the API labels: the
`callG`/`retG`/`callW`/`retW` steps only advance the process's `phase` and
record the returned data, while the sub-protocol state itself lives in the
composed `GBCA.specFamily` / `WCC.specFamily`. This file realises the
Core-side assumptions of `DESIGN-CoreSim.md`: the phase machine (invariant
conjunct 4), the DECIDED diffusion state (conjunct 6), and input coherence
(conjunct 5 — the honest `callG` guard ties the emitted bit to the current
estimate).

Every transition is Dirac (`core_isLTS`). No `withIdle` padding is applied:
the core participates genuinely in every label class of `Lab n`, and `τ`
interleaves in `System.parallel` by itself. The only self-loops are the
`callABA` input-enabledness loop (mirroring the spec's rule 2) and the
byzantine handshake drivers (D11).

## Model and deviations (continuing the project's D1–D8)

* **D9 (0-based rounds).** `round : ℕ` starts at `0` where Algorithm 1 starts
  at `r = 1`; the `GBCA_r`/`WCC_r` instance indices shift accordingly.
* **D10 (fused DECIDED-send).** Algorithm 1's `elif g = A: send ⟨DECIDED, b⟩`
  is performed inside the `retW` step (`CoreState.stepRound`): receiving the
  round's coin adopts it when `est = ⊥`, multicasts `⟨DECIDED, b⟩` when the
  round's grade was `A b`, clears `lastGrade` and advances to the next round,
  all in one Dirac transition. The `decidedSent` write is last-write-wins; in
  reachable states DECIDED coherence makes any overwrite a no-op.
* **D11 (byzantine handshake drivers).** Corrupted processes may drive their
  sub-protocol handshakes arbitrarily: each of `callG`/`retG`/`callW`/`retW`
  has a `…Byz` constructor guarded only by `id ∈ F`, with no phase/estimate
  constraint and no state change. Under full synchronisation the family-side
  call/return rules for corrupted ids are therefore never blocked by the core.
* **D12′ (per-process DECIDED pools, equivocation-capable).** The DECIDED
  multicast state is the per-process pool `CoreState.decidedSent : Finset Bool`
  (chosen as the one representation — no mirror field inside `ProcCore`),
  mirroring the GBCA layer's D5 sent-pool pattern. Honest sends insert into
  the pool (the `retW`/`stepRound` fused send and the `echo` rule; in
  reachable states DECIDED coherence keeps every honest pool at card ≤ 1, so
  the insert is a first write or a no-op re-send of the same bit). Byzantine
  injection (`byzDecided`, guarded only by `id ∈ F`) may insert either or
  both bits at any time — a corrupted process may send `DECIDED 0` to one
  receiver and `DECIDED 1` to another (delivery is selective). `deliver`
  moves one pooled bit into the receiver-side pool `decidedRecv i j` at most
  once per (receiver, sender, bit) triple, with soundness
  `b ∈ decidedSent j`; the `retABA` quorum guard counts distinct *senders*
  per bit (`decidedCount`). The per-process pools (D12′) let a corrupted
  process equivocate at the DECIDED layer; a single-slot model would bar
  that — an under-approximation inconsistent with the GBCA layer.

Two further notes: the return rule `ret` has **no** honesty check — corrupted
returns must pass the same `n − f` quorum guard, exactly like the spec's
return rule — and `lastGrade` always refers to the *current* round's GBCA
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

/-- The state of the ABA core: the per-process control states, the DECIDED
gossip layer (deviation D12) and the corrupted set. -/
structure CoreState (n : ℕ) : Type where
  /-- Per-process control states. -/
  procs : Fin n → ProcCore n
  /-- `b ∈ decidedSent id` — process `id` has multicast `⟨DECIDED, b⟩`
  (a pool: a corrupted process may hold both bits, deviation D12′). -/
  decidedSent : Fin n → Finset Bool
  /-- `b ∈ decidedRecv i j` — the adversary has delivered `j`'s
  `⟨DECIDED, b⟩` multicast to receiver `i`. -/
  decidedRecv : Fin n → Fin n → Finset Bool
  /-- The corrupted set (local copy, kept in lockstep by `fail` broadcast). -/
  F : Finset (Fin n)
  deriving DecidableEq

namespace CoreState

variable {n : ℕ}

/-- The initial core state: all processes idle, no DECIDED traffic, nobody
corrupted. -/
def initial (n : ℕ) : CoreState n where
  procs := fun _ => ProcCore.initial n
  decidedSent := fun _ => ∅
  decidedRecv := fun _ _ => ∅
  F := ∅

@[simp] theorem initial_procs (n : ℕ) (id : Fin n) :
    (initial n).procs id = ProcCore.initial n := rfl

@[simp] theorem initial_decidedSent (n : ℕ) (id : Fin n) :
    (initial n).decidedSent id = ∅ := rfl

@[simp] theorem initial_decidedRecv (n : ℕ) (i j : Fin n) :
    (initial n).decidedRecv i j = ∅ := rfl

@[simp] theorem initial_F (n : ℕ) : (initial n).F = ∅ := rfl

/-- The number of distinct senders whose `⟨DECIDED, b⟩` has been delivered to
receiver `id`. -/
def decidedCount (s : CoreState n) (id : Fin n) (b : Bool) : ℕ :=
  (Finset.univ.filter (fun j => b ∈ s.decidedRecv id j)).card

@[simp] theorem initial_decidedCount (n : ℕ) (id : Fin n) (b : Bool) :
    (initial n).decidedCount id b = 0 := by
  simp [decidedCount]

/-! ### State update helpers -/

/-- Update the control state of process `id`. -/
def setProc (s : CoreState n) (id : Fin n) (p : ProcCore n) : CoreState n :=
  { s with procs := Function.update s.procs id p }

@[simp] theorem setProc_decidedSent (s : CoreState n) (id : Fin n) (p : ProcCore n) :
    (s.setProc id p).decidedSent = s.decidedSent := rfl
@[simp] theorem setProc_decidedRecv (s : CoreState n) (id : Fin n) (p : ProcCore n) :
    (s.setProc id p).decidedRecv = s.decidedRecv := rfl
@[simp] theorem setProc_F (s : CoreState n) (id : Fin n) (p : ProcCore n) :
    (s.setProc id p).F = s.F := rfl
@[simp] theorem setProc_decidedCount (s : CoreState n) (id : Fin n) (p : ProcCore n)
    (i : Fin n) (b : Bool) :
    (s.setProc id p).decidedCount i b = s.decidedCount i b := rfl

@[simp] theorem setProc_procs_self (s : CoreState n) (id : Fin n) (p : ProcCore n) :
    (s.setProc id p).procs id = p := by
  simp [setProc]

theorem setProc_procs_ne (s : CoreState n) (id : Fin n) (p : ProcCore n)
    {k : Fin n} (h : k ≠ id) : (s.setProc id p).procs k = s.procs k := by
  simp [setProc, Function.update_of_ne h]

/-- Process `id` multicasts `⟨DECIDED, b⟩`: insert `b` into `id`'s sent pool
(deviation D12′ — the pool only ever grows). -/
def sendDecided (s : CoreState n) (id : Fin n) (b : Bool) : CoreState n :=
  { s with decidedSent := Function.update s.decidedSent id (insert b (s.decidedSent id)) }

@[simp] theorem sendDecided_procs (s : CoreState n) (id : Fin n) (b : Bool) :
    (s.sendDecided id b).procs = s.procs := rfl
@[simp] theorem sendDecided_decidedRecv (s : CoreState n) (id : Fin n) (b : Bool) :
    (s.sendDecided id b).decidedRecv = s.decidedRecv := rfl
@[simp] theorem sendDecided_F (s : CoreState n) (id : Fin n) (b : Bool) :
    (s.sendDecided id b).F = s.F := rfl
@[simp] theorem sendDecided_decidedSent (s : CoreState n) (id : Fin n) (b : Bool) :
    (s.sendDecided id b).decidedSent =
      Function.update s.decidedSent id (insert b (s.decidedSent id)) := rfl

/-- Sent pools only grow under `sendDecided`. -/
theorem sendDecided_decidedSent_mono (s : CoreState n) (id : Fin n) (b : Bool)
    {k : Fin n} {b' : Bool} (h : b' ∈ s.decidedSent k) :
    b' ∈ (s.sendDecided id b).decidedSent k := by
  by_cases hk : k = id
  · subst hk
    simp only [sendDecided_decidedSent, Function.update_self]
    exact Finset.mem_insert_of_mem h
  · simp only [sendDecided_decidedSent, Function.update_of_ne hk]
    exact h

/-- Membership in a post-`sendDecided` sent pool: the fresh bit at `id`, or an
old pool member. -/
theorem mem_sendDecided_decidedSent_iff (s : CoreState n) (id : Fin n) (b : Bool)
    (k : Fin n) (b' : Bool) :
    b' ∈ (s.sendDecided id b).decidedSent k ↔
      (k = id ∧ b' = b) ∨ b' ∈ s.decidedSent k := by
  by_cases hk : k = id
  · subst hk
    simp [sendDecided_decidedSent, Function.update_self, Finset.mem_insert]
  · simp [sendDecided_decidedSent, hk]
@[simp] theorem sendDecided_decidedCount (s : CoreState n) (id : Fin n) (b : Bool)
    (i : Fin n) (b' : Bool) :
    (s.sendDecided id b).decidedCount i b' = s.decidedCount i b' := rfl

/-- The adversary delivers `⟨DECIDED, b⟩` from sender `j` to receiver `i`:
insert `b` into the `(i, j)` receipt pool (per-(receiver, sender, bit),
deviation D12′). -/
def deliverDecided (s : CoreState n) (i j : Fin n) (b : Bool) : CoreState n :=
  { s with decidedRecv := Function.update s.decidedRecv i
              (Function.update (s.decidedRecv i) j (insert b (s.decidedRecv i j))) }

@[simp] theorem deliverDecided_procs (s : CoreState n) (i j : Fin n) (b : Bool) :
    (s.deliverDecided i j b).procs = s.procs := rfl
@[simp] theorem deliverDecided_decidedSent (s : CoreState n) (i j : Fin n) (b : Bool) :
    (s.deliverDecided i j b).decidedSent = s.decidedSent := rfl
@[simp] theorem deliverDecided_F (s : CoreState n) (i j : Fin n) (b : Bool) :
    (s.deliverDecided i j b).F = s.F := rfl

@[simp] theorem deliverDecided_decidedRecv_self (s : CoreState n) (i j : Fin n) (b : Bool) :
    (s.deliverDecided i j b).decidedRecv i j = insert b (s.decidedRecv i j) := by
  simp [deliverDecided]

/-- Deliveries to other (receiver, sender) edges are untouched. -/
theorem deliverDecided_decidedRecv_of_ne (s : CoreState n) (i j : Fin n) (b : Bool)
    {i' j' : Fin n} (h : i' ≠ i ∨ j' ≠ j) :
    (s.deliverDecided i j b).decidedRecv i' j' = s.decidedRecv i' j' := by
  rcases h with h | h
  · simp [deliverDecided, Function.update_of_ne h]
  · by_cases hi : i' = i
    · subst hi
      simp [deliverDecided, Function.update_of_ne h]
    · simp [deliverDecided, Function.update_of_ne hi]

/-- The round advance of process `id` on receiving the coin `c` (fused
DECIDED-send, deviation D10): adopt the coin when the estimate is `⊥`,
multicast `⟨DECIDED, b⟩` when the round's grade was `A b`, clear the grade and
move to `toCallG` of the next round. -/
def stepRound (s : CoreState n) (id : Fin n) (c : Bool) : CoreState n :=
  (match (s.procs id).lastGrade with
    | some (.A b) => s.sendDecided id b
    | _ => s).setProc id
    { s.procs id with
      est := some ((s.procs id).est.getD c),
      lastGrade := none,
      round := (s.procs id).round + 1,
      phase := .toCallG }

@[simp] theorem stepRound_procs_self (s : CoreState n) (id : Fin n) (c : Bool) :
    (s.stepRound id c).procs id =
      { s.procs id with
        est := some ((s.procs id).est.getD c),
        lastGrade := none,
        round := (s.procs id).round + 1,
        phase := .toCallG } := by
  unfold stepRound
  exact setProc_procs_self _ _ _

theorem stepRound_procs_ne (s : CoreState n) (id : Fin n) (c : Bool)
    {k : Fin n} (h : k ≠ id) : (s.stepRound id c).procs k = s.procs k := by
  unfold stepRound
  cases (s.procs id).lastGrade with
  | none => exact setProc_procs_ne _ _ _ h
  | some out => cases out <;> exact setProc_procs_ne _ _ _ h

@[simp] theorem stepRound_decidedRecv (s : CoreState n) (id : Fin n) (c : Bool) :
    (s.stepRound id c).decidedRecv = s.decidedRecv := by
  unfold stepRound
  cases (s.procs id).lastGrade with
  | none => rfl
  | some out => cases out <;> rfl

@[simp] theorem stepRound_F (s : CoreState n) (id : Fin n) (c : Bool) :
    (s.stepRound id c).F = s.F := by
  unfold stepRound
  cases (s.procs id).lastGrade with
  | none => rfl
  | some out => cases out <;> rfl

@[simp] theorem stepRound_decidedCount (s : CoreState n) (id : Fin n) (c : Bool)
    (i : Fin n) (b : Bool) :
    (s.stepRound id c).decidedCount i b = s.decidedCount i b := by
  unfold decidedCount
  rw [stepRound_decidedRecv]

/-- On an `A b` grade the round advance multicasts `⟨DECIDED, b⟩`. -/
theorem stepRound_decidedSent_of_A (s : CoreState n) (id : Fin n) (c b : Bool)
    (h : (s.procs id).lastGrade = some (.A b)) :
    (s.stepRound id c).decidedSent =
      Function.update s.decidedSent id (insert b (s.decidedSent id)) := by
  unfold stepRound
  rw [h]
  rfl

/-- Without an `A` grade the round advance leaves the DECIDED slots alone. -/
theorem stepRound_decidedSent_of_not_A (s : CoreState n) (id : Fin n) (c : Bool)
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

/-- Corruption (deviation D1): total, Dirac, monotone in `F`. -/
def corrupt (P : Params) (id : Fin P.n) (s : CoreState P.n) : CoreState P.n :=
  if id ∉ s.F ∧ s.F.card < P.f then { s with F := insert id s.F } else s

@[simp] theorem corrupt_procs {P : Params} (s : CoreState P.n) (id : Fin P.n) :
    (s.corrupt P id).procs = s.procs := by
  unfold corrupt; split <;> rfl
@[simp] theorem corrupt_decidedSent {P : Params} (s : CoreState P.n) (id : Fin P.n) :
    (s.corrupt P id).decidedSent = s.decidedSent := by
  unfold corrupt; split <;> rfl
@[simp] theorem corrupt_decidedRecv {P : Params} (s : CoreState P.n) (id : Fin P.n) :
    (s.corrupt P id).decidedRecv = s.decidedRecv := by
  unfold corrupt; split <;> rfl
@[simp] theorem corrupt_decidedCount {P : Params} (s : CoreState P.n) (id : Fin P.n)
    (i : Fin P.n) (b : Bool) :
    (s.corrupt P id).decidedCount i b = s.decidedCount i b := by
  unfold corrupt; split <;> rfl

end CoreState

/-- The step relation of the ABA core (blueprint Algorithm 1). All transitions
are Dirac. -/
inductive CoreStep (P : Params) :
    CoreState P.n → Lab P.n → PMF (CoreState P.n) → Prop
  /-- The external input arrives: record it as input and initial estimate and
  enter round `0` (deviation D9). -/
  | input (s : CoreState P.n) (id : Fin P.n) (b : Bool)
      (h : (s.procs id).input = none) :
      CoreStep P s (.callABA id b)
        (PMF.pure (s.setProc id { s.procs id with
          input := some b, est := some b, round := 0, phase := .toCallG }))
  /-- Input-enabledness loop for `callABA` (mirrors the spec's rule 2). -/
  | inputLoop (s : CoreState P.n) (id : Fin P.n) (b : Bool) :
      CoreStep P s (.callABA id b) (PMF.pure s)
  /-- Honest GBCA call: emit the current estimate to the current round's GBCA
  (input coherence: the emitted bit *is* the estimate). -/
  | callG (s : CoreState P.n) (r : ℕ) (id : Fin P.n) (b : Bool)
      (hph : (s.procs id).phase = .toCallG) (hr : (s.procs id).round = r)
      (hest : (s.procs id).est = some b) :
      CoreStep P s (.callG r id b)
        (PMF.pure (s.setProc id { s.procs id with phase := .awaitG }))
  /-- Byzantine GBCA-call driver (deviation D11): a corrupted process may emit
  any `callG`, with no state change. -/
  | callGByz (s : CoreState P.n) (r : ℕ) (id : Fin P.n) (b : Bool)
      (hF : id ∈ s.F) :
      CoreStep P s (.callG r id b) (PMF.pure s)
  /-- Honest GBCA return: record the graded outcome — `A b`/`B b` set the
  estimate to `b`, `C` clears it to `⊥` — and head for the coin. -/
  | retG (s : CoreState P.n) (r : ℕ) (id : Fin P.n) (out : GbcaOut)
      (hph : (s.procs id).phase = .awaitG) (hr : (s.procs id).round = r) :
      CoreStep P s (.retG r id out)
        (PMF.pure (s.setProc id { s.procs id with
          est := out.est, lastGrade := some out, phase := .toCallW }))
  /-- Byzantine GBCA-return driver (deviation D11). -/
  | retGByz (s : CoreState P.n) (r : ℕ) (id : Fin P.n) (out : GbcaOut)
      (hF : id ∈ s.F) :
      CoreStep P s (.retG r id out) (PMF.pure s)
  /-- Honest WCC call. -/
  | callW (s : CoreState P.n) (r : ℕ) (id : Fin P.n)
      (hph : (s.procs id).phase = .toCallW) (hr : (s.procs id).round = r) :
      CoreStep P s (.callW r id)
        (PMF.pure (s.setProc id { s.procs id with phase := .awaitW }))
  /-- Byzantine WCC-call driver (deviation D11). -/
  | callWByz (s : CoreState P.n) (r : ℕ) (id : Fin P.n) (hF : id ∈ s.F) :
      CoreStep P s (.callW r id) (PMF.pure s)
  /-- Honest WCC return: adopt the coin if the estimate is `⊥`, multicast
  `⟨DECIDED, b⟩` if the round's grade was `A b` (deviation D10), advance the
  round. -/
  | retW (s : CoreState P.n) (r : ℕ) (id : Fin P.n) (c : Bool)
      (hph : (s.procs id).phase = .awaitW) (hr : (s.procs id).round = r) :
      CoreStep P s (.retW r id c) (PMF.pure (s.stepRound id c))
  /-- Byzantine WCC-return driver (deviation D11). -/
  | retWByz (s : CoreState P.n) (r : ℕ) (id : Fin P.n) (c : Bool) (hF : id ∈ s.F) :
      CoreStep P s (.retW r id c) (PMF.pure s)
  /-- DECIDED delivery: the adversary moves a pooled `⟨DECIDED, b⟩` from
  sender `j` into receiver `i`'s receipt pool (at most once per
  (receiver, sender, bit); soundness `b ∈ decidedSent j`, deviation D12′). -/
  | deliver (s : CoreState P.n) (i j : Fin P.n) (b : Bool)
      (hs : b ∈ s.decidedSent j) (hr : b ∉ s.decidedRecv i j) :
      CoreStep P s .tau (PMF.pure (s.deliverDecided i j b))
  /-- DECIDED echo: `f + 1` delivered `⟨DECIDED, b⟩` (distinct senders) and not
  having multicast `⟨DECIDED, b⟩` oneself trigger the multicast (the process
  keeps running its round loop). The guard is payload-specific: a pool holding
  the other bit does not block the echo of `b`. -/
  | echo (s : CoreState P.n) (id : Fin P.n) (b : Bool)
      (hcnt : P.f + 1 ≤ s.decidedCount id b) (hs : b ∉ s.decidedSent id) :
      CoreStep P s .tau (PMF.pure (s.sendDecided id b))
  /-- Byzantine DECIDED injection (deviation D12′): a corrupted process may
  insert an arbitrary payload into its sent pool at any time — either or both
  bits, so a corrupted process can equivocate at the DECIDED layer. -/
  | byzDecided (s : CoreState P.n) (id : Fin P.n) (b : Bool)
      (hF : id ∈ s.F) :
      CoreStep P s .tau (PMF.pure (s.sendDecided id b))
  /-- Return: `n − f` delivered `⟨DECIDED, b⟩` (distinct senders) and having
  multicast `⟨DECIDED, b⟩` oneself. **No honesty check** — corrupted returns
  must pass the same quorum guard (as in the spec's return rule). -/
  | ret (s : CoreState P.n) (id : Fin P.n) (b : Bool)
      (hcnt : P.n - P.f ≤ s.decidedCount id b) (hs : b ∈ s.decidedSent id)
      (hret : (s.procs id).returned = false) :
      CoreStep P s (.retABA id b)
        (PMF.pure (s.setProc id { s.procs id with returned := true }))
  /-- Corruption (deviation D1): total and Dirac. -/
  | fail (s : CoreState P.n) (id : Fin P.n) :
      CoreStep P s (.fail id) (PMF.pure (s.corrupt P id))

/-- The ABA core system (blueprint Algorithm 1). -/
noncomputable def core (P : Params) : System (CoreState P.n) (Lab P.n) where
  init := CoreState.initial P.n
  step := CoreStep P

@[simp] theorem core_init (P : Params) : (core P).init = CoreState.initial P.n := rfl

@[simp] theorem core_step (P : Params) (s : CoreState P.n) (l : Lab P.n)
    (μ : PMF (CoreState P.n)) : (core P).step s l μ ↔ CoreStep P s l μ := Iff.rfl

/-- Every core transition is Dirac: the core is an LTS. -/
theorem core_isLTS (P : Params) : (core P).IsLTS := by
  rintro s l μ hstep
  cases hstep <;> exact ⟨_, rfl⟩

/-! ### Step inversion, by label class -/

@[simp] theorem coreStep_callABA_iff (P : Params) (s : CoreState P.n) (id : Fin P.n)
    (b : Bool) (μ : PMF (CoreState P.n)) :
    CoreStep P s (.callABA id b) μ ↔
      ((s.procs id).input = none ∧
        μ = PMF.pure (s.setProc id { s.procs id with
          input := some b, est := some b, round := 0, phase := .toCallG })) ∨
      μ = PMF.pure s := by
  constructor
  · rintro h
    cases h
    case input hin => exact Or.inl ⟨hin, rfl⟩
    case inputLoop => exact Or.inr rfl
  · rintro (⟨h, rfl⟩ | rfl)
    · exact .input s id b h
    · exact .inputLoop s id b

@[simp] theorem coreStep_callG_iff (P : Params) (s : CoreState P.n) (r : ℕ)
    (id : Fin P.n) (b : Bool) (μ : PMF (CoreState P.n)) :
    CoreStep P s (.callG r id b) μ ↔
      ((s.procs id).phase = .toCallG ∧ (s.procs id).round = r ∧
        (s.procs id).est = some b ∧
        μ = PMF.pure (s.setProc id { s.procs id with phase := .awaitG })) ∨
      (id ∈ s.F ∧ μ = PMF.pure s) := by
  constructor
  · rintro h
    cases h
    case callG hph hr hest => exact Or.inl ⟨hph, hr, hest, rfl⟩
    case callGByz hF => exact Or.inr ⟨hF, rfl⟩
  · rintro (⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩)
    · exact .callG s r id b hph hr hest
    · exact .callGByz s r id b hF

@[simp] theorem coreStep_retG_iff (P : Params) (s : CoreState P.n) (r : ℕ)
    (id : Fin P.n) (out : GbcaOut) (μ : PMF (CoreState P.n)) :
    CoreStep P s (.retG r id out) μ ↔
      ((s.procs id).phase = .awaitG ∧ (s.procs id).round = r ∧
        μ = PMF.pure (s.setProc id { s.procs id with
          est := out.est, lastGrade := some out, phase := .toCallW })) ∨
      (id ∈ s.F ∧ μ = PMF.pure s) := by
  constructor
  · rintro h
    cases h
    case retG hph hr => exact Or.inl ⟨hph, hr, rfl⟩
    case retGByz hF => exact Or.inr ⟨hF, rfl⟩
  · rintro (⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩)
    · exact .retG s r id out hph hr
    · exact .retGByz s r id out hF

@[simp] theorem coreStep_callW_iff (P : Params) (s : CoreState P.n) (r : ℕ)
    (id : Fin P.n) (μ : PMF (CoreState P.n)) :
    CoreStep P s (.callW r id) μ ↔
      ((s.procs id).phase = .toCallW ∧ (s.procs id).round = r ∧
        μ = PMF.pure (s.setProc id { s.procs id with phase := .awaitW })) ∨
      (id ∈ s.F ∧ μ = PMF.pure s) := by
  constructor
  · rintro h
    cases h
    case callW hph hr => exact Or.inl ⟨hph, hr, rfl⟩
    case callWByz hF => exact Or.inr ⟨hF, rfl⟩
  · rintro (⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩)
    · exact .callW s r id hph hr
    · exact .callWByz s r id hF

@[simp] theorem coreStep_retW_iff (P : Params) (s : CoreState P.n) (r : ℕ)
    (id : Fin P.n) (c : Bool) (μ : PMF (CoreState P.n)) :
    CoreStep P s (.retW r id c) μ ↔
      ((s.procs id).phase = .awaitW ∧ (s.procs id).round = r ∧
        μ = PMF.pure (s.stepRound id c)) ∨
      (id ∈ s.F ∧ μ = PMF.pure s) := by
  constructor
  · rintro h
    cases h
    case retW hph hr => exact Or.inl ⟨hph, hr, rfl⟩
    case retWByz hF => exact Or.inr ⟨hF, rfl⟩
  · rintro (⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩)
    · exact .retW s r id c hph hr
    · exact .retWByz s r id c hF

@[simp] theorem coreStep_tau_iff (P : Params) (s : CoreState P.n)
    (μ : PMF (CoreState P.n)) :
    CoreStep P s .tau μ ↔
      (∃ i j b, b ∈ s.decidedSent j ∧ b ∉ s.decidedRecv i j ∧
        μ = PMF.pure (s.deliverDecided i j b)) ∨
      (∃ id b, P.f + 1 ≤ s.decidedCount id b ∧ b ∉ s.decidedSent id ∧
        μ = PMF.pure (s.sendDecided id b)) ∨
      (∃ id b, id ∈ s.F ∧ μ = PMF.pure (s.sendDecided id b)) := by
  constructor
  · rintro h
    cases h
    case deliver i j b hs hr => exact Or.inl ⟨i, j, b, hs, hr, rfl⟩
    case echo id b hcnt hs => exact Or.inr (Or.inl ⟨id, b, hcnt, hs, rfl⟩)
    case byzDecided id b hF => exact Or.inr (Or.inr ⟨id, b, hF, rfl⟩)
  · rintro (⟨i, j, b, hs, hr, rfl⟩ | ⟨id, b, hcnt, hs, rfl⟩ | ⟨id, b, hF, rfl⟩)
    · exact .deliver s i j b hs hr
    · exact .echo s id b hcnt hs
    · exact .byzDecided s id b hF

@[simp] theorem coreStep_retABA_iff (P : Params) (s : CoreState P.n) (id : Fin P.n)
    (b : Bool) (μ : PMF (CoreState P.n)) :
    CoreStep P s (.retABA id b) μ ↔
      P.n - P.f ≤ s.decidedCount id b ∧ b ∈ s.decidedSent id ∧
        (s.procs id).returned = false ∧
        μ = PMF.pure (s.setProc id { s.procs id with returned := true }) := by
  constructor
  · rintro h
    cases h
    case ret => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  · rintro ⟨hcnt, hs, hret, rfl⟩
    exact .ret s id b hcnt hs hret

@[simp] theorem coreStep_fail_iff (P : Params) (s : CoreState P.n) (id : Fin P.n)
    (μ : PMF (CoreState P.n)) :
    CoreStep P s (.fail id) μ ↔ μ = PMF.pure (s.corrupt P id) := by
  constructor
  · rintro h
    cases h
    rfl
  · rintro rfl
    exact .fail s id

end ABA
end PLTS
