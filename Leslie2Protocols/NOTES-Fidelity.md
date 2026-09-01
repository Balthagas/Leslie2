# Fidelity — the encoding against its sources

A registry of the places where the ABA encoding and the artifacts it answers to do not
coincide, restricted to divergences carrying no D-number — together with §1, the one
place where the two sources disagree with each other and the encoding must pick a side —
for a reader holding the sources open beside the Lean.

**Two sources, in a chain.** The *source blueprint* — "Verifying ABA with Leslie",
`Papers/Leslie_blueprint.pdf` — supplies the transition systems (TS 1 = ABA, TS 2 =
GBCA, TS 3 = WCC, pp. 18–19) and the pseudocode (Algorithm 1 = the ABA core, p. 14;
Algorithm 2 = GBCA, p. 15). It in turn adapts *ABDY22* (Abraham, Ben-David and
Yandamuri, PODC 2022), which numbers independently: ABDY22's Algorithm 2 is the
weak-coin agreement framework `AA_ε` that the source blueprint's Algorithm 1
realises (ABDY22's Algorithm 1 is the strong-coin framework, not encoded here),
and ABDY22's Algorithm 6 is the GBCA of record. Bare algorithm numbers in this
file are the source blueprint's. The encoding follows the
source blueprint; where the source blueprint departs from ABDY22 the encoding inherits
the departure, with the single exception of §1.

**The D-registry is elsewhere.** The catalogued deviations — D1, D4, D5, D8–D19, D21
and D22, with D12 refined to D12′ — are cited at the point of use in the ABA module
docstrings and glossed one by one in the blueprint chapter (the Deviations paragraph of
`blueprint/src/content.tex`), which is the registry of record.

## 1. Where the encoding follows ABDY22 against the source blueprint

The one substantive item, and the one place the encoding parts from the source blueprint
rather than inheriting its parting from ABDY22.

The verified GBCA implementation (`GBCA.ImplStep`) transcribes **ABDY22's Algorithm 6 in
full** — six rounds, the message levels INPUT, ECHO, VOTE, BIND, SEAL (the paper's `echo`
through `echo5`), and that algorithm's three decide conditions, `retA` an `n − f`
`SEAL v` receipt quorum, `retB` an `n − f` any-`SEAL` quorum containing `SEAL v` with
`f + 1` `BIND v` receipts and `|Valid| > 1`, `retC` an `n − f` `SEAL ⊥` quorum with
`|Valid| > 1`. That is deviation **D18**, and what it departs from is the source
blueprint's Algorithm 2, a **four-round compression** of Algorithm 6: the `echo5` level
elided, the decide conditions read one message level down, and `f + 1` `VOTE v` receipts
as the grade-1 witness where Algorithm 6 reads `f + 1` `BIND v`.

The compression is not merely shallower; it violates the paper's Graded Binding. One
process held at the echo stage through a grade-0 decision can afterwards direct its
write-once echo at either bit, and one corruption completes the `f + 1` `VOTE v` count
for the bit of the adversary's choice, so two extensions of a single `C`-return hand out
two different bits and no binding-faithful specification simulates the compression. The
concrete violation at `n = 4, f = 1` is written out in `DESIGN-GBCASim.md`. At the D18
evidence level the same attack dies: `f + 1 > |F|` `BIND v` receipts put an honest
`BIND v` sender behind every grade-≥1 output, hence an `n − f` `VOTE v` receipt quorum
over the write-once `VOTE` level — and that quorum is the object the paper's binding
argument counts (Lemmas 4.8/4.9 through E.9).

Annotation lives in `GBCAImpl.lean`'s module docstring, in the blueprint chapter's caption
for the algorithm and its D18 registry entry, and in the source blueprint's own TeX
(`Leslie/blueprint/src/sections/Algorithm.tex`, a red note at Algorithm 2's decide
conditions); the source's PDF caption reads "Implementation of GBCA from [ABDY22]" with no
such note.

On the specification side the matching item is **D19**. TS 2's bound value
`bind ∈ {0,1,⊥}` is replaced by the exclusion set `dead : Finset Bool`, the bits the
instance can no longer hand out (`GBCASpec.lean`). The kill fires under the guard
`dead = ∅`, so reachable states are exactly `dead ∈ {∅, {b}}`
(`GBCASafety.dead_card_le_one`) and the bound value embeds onto them — `bind = ⊥` as
`dead = ∅`, `bind = b` as `dead = {!b}`. The two state shapes therefore differ in the
guards rather than in the cardinality. `dead` is monotone and written once, so Graded
Agreement is the return guard pair `v ∉ dead ∧ !v ∈ dead` and Binding is the `C`-return
guard `1 ≤ dead.card`, both proved from monotonicity alone in `GBCASafety.lean`
(`retG_value_agree`, `specInst_binding`, `retC_dead_nonempty`) with no auxiliary
invariant; the same file carries Validity's safety half (`specInst_validity`,
`specInst_no_retC`).

A transcription question of ABDY22's own: the prose preceding Algorithm 6 says "upon
receiving `echo4` messages from `2t + 1` parties" where the pseudocode's lines 19–20 say
`n − t`. The two coincide only at `n = 3t + 1`; the encoding follows the pseudocode
(`n − f`).

## 2. Interpretation-level readings

**"Received once."** The wait case (b) of Algorithm 6 requires that "⟨echo5, b⟩ has been
received once". `ImplStep.retB` reads this as *from at least one sender*: `honce : ∃ k,
Msg.seal (some v) ∈ s.recv id k`, not as a cardinality constraint of exactly one
receipt. The hypothesis is a genuine part of the rule, carried through the protocol's
rendering by `ABAProcStepN.retG_B` and through the round instance's Byzantine-drive
twin `GProcStep.byzRetB`, but no proof
consumes it: the refinement's `retB` rows bind it and leave it unused, discharging the
`B`-return's specification-side guards from the `f + 1` `BIND v` receipts and `hval`
instead. Either reading supports the same theorems.

**Terminating `return` as state.** The pseudocode's `return` ends the process; the
encoding renders that as a fire-once flag — `ProcState.returned`, guarded by the `hr`
hypothesis of all three GBCA returns `ImplStep.retA`, `retB` and `retC`, and
`ProcCore.returned`, guarded at `CoreProcStepN.ret`. The
guard has no surface counterpart in Algorithm 1 or Algorithm 2, which name no such
variable; the control-flow fact it expresses does. (At specification level it is no
interpretation: TS 1 and TS 2 carry `ret[id] = ⊥` guards of their own.) At the protocol,
returning and terminating are two fields and two rules: `ProcCore.returned` records that
`ABAProcStepN.ret` has fired, and `Net.StageSideRec.terminated`, whose sole writer is
`ABAProcStepN.terminate`, records that the process has stopped participating (D22, §6).

## 3. A network-model artifact

The source pseudocode has no explicit network: sends and receipts are primitive. The
encoding's set-based authenticated model is D5 and the DECIDED pools are D12′; what
belongs here is the asymmetry *between* the two networks. `CoreProcStepN.ddlvRecv`
carries a freshness guard `hr : b ∉ c.decIn k`; `ImplStep.deliver` carries no
counterpart, its only hypothesis being soundness `h : m ∈ s.sent j`. Both are sound for the same reason — receipt sets are `Finset`s
and re-delivery is `insert` into a set, so the guard removes redundant transitions
rather than reachable states — and the asymmetry reappears exactly in the protocol's
rendering, where each delivery is a rendezvous whose two halves are held by different
components. Soundness is the network adversary's conjunct in both pools: `NetStep.gdlv`
requires `h : m ∈ s.pool r j` and `NetStep.ddlv` requires `h : b ∈ s.dpool j`, neither
consuming the pooled message. Freshness is the receiver's, and only in the DECIDED
pools: `ABAProcStepN.ddlvRecv` carries `hr : b ∉ c.decIn k` while
`ABAProcStepN.gdlvRecv` carries no freshness guard, filing the message under the sender's
inbox row whatever is already there. Its one hypothesis is the termination guard
`hterm : p.terminated = false` carried by every stage-side row (D22, §6), which is not a
freshness condition.

## 4. Guards the specifications do not carry

Algorithm 6's control flow sits in the implementation tables and not in the systems they
refine. A refinement asks only that the implementation move no more freely than its
specification, so the gap is harmless; what is worth having in one place is which side of
it each guard falls on, and whether that placement was chosen or forced.

**Carried by the implementation tables** — `GBCA.ImplStep` (`ABA/GBCAImpl.lean`), mirrored
row for row at `GBCA.GProcStep` (`ABA/GBCAInstances.lean`), Byzantine drives included, and
at `Net.ABAProcStepN` (`ABA/Protocol.lean`) with the reads taken through `p.stage r`.

- **The wait-until order.** The order is carried from the `BIND` level down: each of
  those sends requires the sender's own send at the level below — `hlv : sentVote ≠ none`
  on the two `BIND` rules, `sentBind ≠ none` on the two `SEAL` rules, and
  `sentSeal ≠ none` on all three returns. Algorithm 6 reaches those **wait until** blocks
  only after executing the send the block above them ends with, and `hlv` is that
  reachability written as a guard. The two `VOTE` rules carry no own-send guard, and here
  the encoding follows the paper's own reading rather than tightening it: what precedes
  the first **wait until** block is not a block a process runs to its end but the
  **upon** handler of Algorithm 6's lines 5–7, which multicasts `ECHO`, so a process may
  reach that block and send its `VOTE` with its own `ECHO` still pending.
- **The denials of the higher cases.** Each rule carries the denials of the cases above
  it in its own block. In a ladder block the `⊥` rule denies its block's case (a) at
  either bit
  (`hnot : ∀ b, recvCount (level below, b) < n − f` at `voteBot`, `bindBot`, `sealBot`).
  In the decide block `retB` and `retC` carry `hnotA`, the denial of case (1) at either
  bit, and `retC` carries `hnotB`, the denial of case (2) in reduced form:
  `∀ v, (∃ k, seal (some v) ∈ recv id k) → recvCount (.bind (some v)) < f + 1`. Case (2)
  asks at a bit `v` for four things — an `n − f` any-`SEAL` quorum, a received `SEAL v`,
  `f + 1` `BIND v` receipts and `|Valid| > 1` — of which the first and the last are
  `retC`'s own `hcnt` and `hval`, an `n − f` `SEAL ⊥` quorum being in particular an
  `n − f` any-`SEAL` quorum; the reduced `hnotB` denies the remaining pair. The
  docstring of `ImplStep.retC` states the reduction.
- **The return call-gates.** All three returns require `input ≠ none`, the D8 gate
  carried from the sends over to the returns: a process that was never called does not
  return from the round.
- **The protocol's participation gates.** `ABAProcStepN.ret` and `ABAProcStepN.dsndRelay`
  require `c.proc.input ≠ none`, and `ABAProcStepN.gcallLoop` requires
  `(p.stage r).proc.input ≠ none`. `gcallLoop` deliberately carries no termination guard,
  so a process that has terminated at phase `toCallG` over an uncalled stage record has a
  row on neither call label and takes no further round-loop step. That dead region is
  accepted rather than repaired: a terminated process is one whose own return has already
  fired, and no statement of the development is about what it does afterwards.

**Absent from the specifications.** Three of the placements below are chosen and two are
forced by where the authorisation of a Byzantine drive sits (D11), which cannot be
repaired at the rule; the sixth entry is a cross-reference.

- **`GBCASpec.Step`, every rule (chosen).** No rule of the graded-agreement specification
  requires a send at the level below, denies a higher case, or gates a return on a call.
  The specification abstracts the receipt patterns into `dead` and `grade` (D19), and its
  return guards are that pair; supplying them from the receipts is exactly the work of
  `GBCASim.implRefines`.
- **`WCC.Step.ret` without `called` (forced).** `WCC.SpecState` carries a `called` field
  and the return rule does not read it. The Byzantine coin drive `byzRetW` has no row at
  the process it names — `CoreProcStepN.byzRetWIdle` stands idle at every process — and
  `wccPull` maps that drive onto `retW`, so the coin instance answers it alone. A `called`
  guard there would leave the drive unanswerable. This is a consequence of the
  authorisation placement, not a preference.
- **`ImplStep.callLoop` and `GProcStep.callLoop` (forced).** Both are unguarded
  self-loops. `gPull` maps `byzCallGLoop` onto `callG`, `GNetStep.byzCallGLoop` carries no
  `k ∈ F`, and the driven process's row is idle, so the call loop must accept every call
  label whatever the record holds.
- **`CoreProcStepN`'s DECIDED rows (chosen).** `CoreProcStepN.ret` and
  `CoreProcStepN.dsndRelay` read the receipt counts alone, without the `input ≠ none`
  gate their `ABAProcStepN` counterparts carry. The composed reading is the abstraction
  the protocol is carried into, and gating there would ripple through `ProtocolRel` and
  the core simulation.
- **`SpecStep.ret` (chosen).** The top-level return guards are `val = some b` and
  `ret id = false`, and nothing about the returner. `ValidityTrace` is
  returner-unconditional (§6), so the specification is deliberately the weaker of the two
  on that axis.
- **The `2f + 1` commit read as a relay threshold (cross-reference).**
  `ABAProcStepN.terminate` reads `2f + 1` DECIDED receipts where the paper's condition is
  that the process may stop without holding another back. That delta is the third D22
  residue of §6, and is not restated here.

## 5. Source defects the encoding does not reproduce

- **TS 1 violates Agreement and the papers' Validity.** The source's re-proposal rule
  fires with `val` already written, so the unanimity rule can overwrite it and one run
  returns `v` and then `1 − v`; and the free bind choice together with that same
  re-proposal carries a bit input only by a later-corrupted process through to a return.
  `Spec.lean` reproduces neither rule. `PLTS.ABA.SpecStep.decide` is the sole writer of
  `val` and fires only from `val = ⊥`, so the decision value is written once and
  Agreement is structural (`PLTS.ABA.SpecInv.val_stable`); and it carries the D13 support
  guard `PLTS.ABA.SuppOK`, which is where the Validity trace dies —
  the counterexample check in `Spec.lean` records it, with inputs `1,0,0,0` at
  `n = 4, f = 1` and the sole `1`-inputter corrupted leaving one supporter of `1` against
  the `f + 1 = 2` the guard demands. The six-rule shape this leaves, with the control mode
  carrying the flip, is deviation **D21**.
- **TS 2's singular binding witness** (`∃ id ∉ F, call[id] = b`, source p. 19) loses
  provenance one level down, and `hybrid` over it violates Validity; the
  deterministic trace is in `GBCASpec.lean`'s module docstring, under D14.
  Both TS 1 defects and this one are annotated in the source blueprint's TeX
  (`Leslie/blueprint/src/sections/Specification.tex`, red notes at the affected
  rules). D14 and D15
  replace every such witness with an `F`-blind count.
- **Algorithm 2 violates Binding**, being a four-round compression of ABDY22's
  Algorithm 6; the encoding follows Algorithm 6 instead (D18) — §1.
- **The Graded Agreement clause is ill-typed** as stated: "if two correct processes
  return `(b, X)` and `(b′, X′)` then `b = 0 ⟹ b′ ≠ 1` and `X = A ⟹ X′ ≠ ⊥`" (p. 6),
  with `⊥` in a grade slot ranging over `{A, B, C}`. It reads as grade `C`, and is
  realized as the `grade` latch's `A`/`C` exclusivity, the `hg` guards of
  `PLTS.ABA.GBCA.Step.retA` and `PLTS.ABA.GBCA.Step.retC`.
- **TS 1's `Initial` clause names an undeclared field** `out` (source p. 18), absent
  from the same system's `State` line. It is omitted: `PLTS.ABA.SpecState` declares
  `input`, `ret`, `F`, `val` and `mode`, and nothing else.

## 6. Scope boundaries

Beyond D4 — the WCC `guess` label and state field, whose omission `Labels.lean` and
`WCCSpec.lean` both record in their module docstrings — they exist solely for
Unpredictability, inexpressible once the guess is dropped.

- **Per-transition fairness markings.** Every transition system in the source carries
  the line "all transitions are fair except those labelled by fail and the call loops"
  (pp. 18–19). The encoding has none; they bear on liveness only.
- **Partial-information adversaries.** The source equips a system with a pair of
  observation functions (Definition 9, p. 4) and a belief construction turning such an
  adversary into an omniscient one (Definition 10, p. 5). Every adversary in the ABA
  chain is declared omniscient there (Definitions 11–15, Specifications 1–3, pp. 6–7),
  which the encoding's unrestricted schedulers match; belief has no counterpart.
- **The Byzantine `⟨ECHO, ⊥⟩`.** `GBCA.Msg.echo` carries a `Bool` where `Msg.vote`,
  `Msg.bind` and `Msg.seal` carry an `Option Bool`, so `ImplStep.byz` cannot inject an
  `ECHO` of non-bit payload, which ABDY22 permits a corrupted sender. The restriction
  falls on the adversary and costs nothing. Two guards read `ECHO`: at a named bit,
  `recvCount j (.echo b)`, in `voteBit`'s quorum and in `voteBot`'s denial `hnot`; and
  payload-blind, `echoCount j`, in `voteBot`'s quorum. A non-bit `ECHO` raises
  `echoCount j` alone, so its one use to the adversary is to reach `voteBot`'s quorum
  without carrying either bit to `n − f` and breaking `hnot`. An injection of a bit does
  the same whenever some bit has `recvCount j (.echo b) < n − f − 1`. When neither has,
  both stand at `n − f − 1`; an honest sender's `sentEcho` is write-once, so only the `f`
  corrupted senders are counted at both bits and `echoCount j ≥ 2(n − f − 1) − f`, which
  `3f < n` puts at `n − f` or above (`f ≥ 1`, which an injection presupposes). `voteBot`
  is then enabled already and no injection is wanted. So the bit-valued injection reaches
  every guard the non-bit one would, and no safety- or termination-relevant behaviour is
  lost.
- **Byzantine drives at the ABA interface.** The stage and coin interfaces carry drives
  for a corrupted process — `NetStep.byzCallG`, `byzCallGLoop`, `byzRetG`, `byzCallW` and
  `byzRetW`, each under a `k ∈ F` guard (D11) — and the ABA interface carries none.
  `ABAProcStepN.input` and `ABAProcStepN.ret` are the only rows at the process a
  `callABA` or `retABA` names, and a corrupted process takes them under the guards an
  honest one takes: `ret` asks for the call record, `n − f` DECIDED receipts and an
  unfired return, and reads `F` nowhere, while `NetStep.retABA` adds the pool conjunct
  `b ∈ s.dpool id`. The arbitrary outputs ABDY22 permits a faulty party are therefore
  absent from the trace set. Nothing claimed turns on it: the paper's properties quantify
  over non-faulty parties, and the encoding proves `AgreementTrace` and `ValidityTrace`
  of every return, corrupted returners included — the divergence this section closes on.
- **Termination.** ABA's ε-sure Termination, GBCA's Termination and WCC's ε′-sure
  Termination (pp. 6–7) are unclaimed — `ABA.main` is Validity ∧
  Agreement. See `NOTES-Liveness-Roadmap.md`.
- **Participation past the round advance.** ABDY22 separates deciding from terminating: a
  process decides and then eventually terminates (Definitions 3.1 and 3.2), and the
  amplification argument counts the echoes a decided process keeps sending (Lemmas 4.6 and
  E.5, stated under the hypothesis that no non-faulty party terminates). The encoding
  carries that shape, as deviation **D22**; what belongs here is what the shape leaves
  uncovered. A process record holds the stage record of
  every round the process has touched, in a `Finmap` read through
  `Net.StageSideRec.stage`; each stage-side rule reads and writes the stage record of the
  round its own label tags, under an instance-local guard and no round gate; and the round
  advance, `ABAProcStepN.retW` and `ABAProcStepN.retWPub`, resets nothing. A process
  therefore answers prior-round traffic and files deliveries of any round.
  `ABAProcStepN.terminate` is the terminating step. It fires when the process's own return
  has fired and DECIDED receipts from `2f + 1` distinct senders are on record, and it
  writes `terminated` alone, so the stage records freeze where they stand. Three
  residues remain.
    - The amplification rule `ABAProcStepN.gsndRelay` is gated on the process holding an
      input in that round's stage record (`hin : (p.stage r).proc.input ≠ none`, D8, and
      `ImplStep.relay` carries the same gate one level down), where lines 3–4 of ABDY22's
      Algorithm 6 gate the relay on the receipt count alone.
    - A stage delivery at a process that has terminated is disabled rather than ignored.
      `ABAProcStepN.gdlvRecv` carries `hterm : p.terminated = false` and
      `ABAProcStepN.gdlvIdle` demands a different receiver, so the adversary has no
      composite step delivering a stage message there at all.
    - The `2f + 1` receipt count of `ABAProcStepN.terminate` is the encoding's commit
      point. At most `f` senders are corrupted, so `2f + 1` receipts stand behind `f + 1`
      honest senders of the payload, which is the threshold `ABAProcStepN.dsndRelay` reads;
      the paper's own condition is that the process may stop without holding back any other.
- **The scope of `terminate`.** The flag is read by the stage-side rows and by nothing
  else: `callG_call`, the three `retG_*`, `gsndRelay`, `gsndEcho`, the six ladder rows
  `gsndVoteBit` through `gsndSealBot`, `gdlvRecv`, and `terminate` itself; `gcallLoop` is
  the stage-side row that does not read it (§4). A process that has terminated still
  finishes a pending coin handshake (`callW`, `retW`), publishes `⟨DECIDED, b⟩` through
  `retWPub`, and both relays and receives DECIDED (`dsndRelay`, `ddlvRecv`). That placement is the
  design and not an oversight: what the flag records is that the process has stopped
  participating in graded agreement, and the D12′ broadcast it keeps carrying is what
  lets the processes still running cross the relay threshold without it.

One divergence runs in the safe direction. The source's Validity restricts to correct
processes ("if a correct process returns `b` then a correct process had `b` as input",
p. 6), where `ValidityTrace` is returner-unconditional — every return, corrupted
returners included, is witnessed by a preceding `callABA` from a `NeverCorrupted`
caller — and `AgreementTrace` is stronger on the same axis. `ABA.spec`'s return rule
does not inspect `F`, so the stronger statement is what `spec_safe` proves.

## 7. Adjacent open items

Neither is a fidelity gap; both sit under Future work in `ABA/README.md`.
**Achievability** — `NonVacuity.lean` carries the non-vacuity run on `hybrid`, the system
the core simulation takes as its subject, and a machine-checked positive-mass trace for
`protocol`, the system `main` is about, is outstanding.
**`ValidityTrace` witness strengthening** — the witness clause accepts any preceding
`callABA id' b`, where the proof yields a stronger ghost-backed one.
