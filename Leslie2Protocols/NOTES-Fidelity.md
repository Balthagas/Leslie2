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

**The D-registry is elsewhere.** The catalogued deviations — D1, D3–D5, D8–D19, D12
refined to D12′ — are cited at the point of use in the ABA module docstrings, summarised
in `ABA/README.md`, and listed in the blueprint chapter (the Deviations paragraph of `blueprint/src/content.tex`).

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
Msg.seal (some v) ∈ s.recv id k` (`GBCAImpl.lean:467`), not as a cardinality constraint
of exactly one receipt. The hypothesis is a genuine part of the rule, carried through the
deployed rendering (`FlatOwnFlag.lean:313`, the fused `retG_B` row), but no proof
consumes it: the refinement's `retB` rows bind it and leave it unused, discharging the
`B`-return's specification-side guards from the `f + 1` `BIND v` receipts and `hval`
instead. Either reading supports the same theorems.

**Terminating `return` as state.** The pseudocode's `return` ends the process; the
encoding renders that as a fire-once flag — `ProcState.returned` (`GBCAImpl.lean:127`),
guarded at all three GBCA returns (`GBCAImpl.lean:458`, `:470`, `:478`), and
`ProcCore.returned` (`Core.lean:135`), guarded at `CoreStep.ret` (`Core.lean:474`). The
guard has no surface counterpart in Algorithm 1 or Algorithm 2, which name no such
variable; the control-flow fact it expresses does. (At specification level it is no
interpretation: TS 1 and TS 2 carry `ret[id] = ⊥` guards of their own.)

## 3. A network-model artifact

The source pseudocode has no explicit network: sends and receipts are primitive. The
encoding's set-based authenticated model is D5 and the DECIDED pools are D12′; what
belongs here is the asymmetry *between* the two networks. `CoreStep.deliver` carries a
freshness guard `hr : b ∉ s.decidedRecv i j` (`Core.lean:454`); `ImplStep.deliver`
carries no counterpart, its only hypothesis being soundness `h : m ∈ s.sent j`
(`GBCAImpl.lean:378`). Both are sound for the same reason — receipt sets are `Finset`s
and re-delivery is `insert` into a set, so the guard removes redundant transitions
rather than reachable states — and the asymmetry reappears exactly in the deployed
automaton, each guard splitting across the two ends of a rendezvous: the DECIDED halves
carry it (`ABAProcStepU.dnetSelf`/`dnetRecv`, `FlatOwnFlag.lean:474`, `:482`), the stage
halves do not (`ABAProcStepU.gnetSelf`/`gnetRecv`, `FlatOwnFlag.lean:490`, `:499`).

## 4. Source defects the encoding does not reproduce

- **TS 1 violates Agreement** without the rule-7 re-propose guard and the papers'
  Validity without the rule-4 support guard; both counterexample traces are in
  `Spec.lean`'s module docstring (D3 at lines 36–43, D13 at 15–35), the second with the
  `decide` witness at `Spec.lean:247–250` — the support guard failing on inputs
  `1,0,0,0` at `n = 4, f = 1`.
- **TS 2's singular binding witness** (`∃ id ∉ F, call[id] = b`, source p. 19) loses
  provenance one level down, and `hybridSpec` over it violates Validity; the
  deterministic trace is in `GBCASpec.lean`'s docstring (the D14 entry, lines 65–75).
  Both TS 1 defects and this one are annotated in the source blueprint's TeX
  (`Leslie/blueprint/src/sections/Specification.tex`, red notes at the affected
  rules). D14 and D15
  replace every such witness with an `F`-blind count.
- **Algorithm 2 violates Binding**, being a four-round compression of ABDY22's
  Algorithm 6; the encoding follows Algorithm 6 instead (D18) — §1.
- **The Graded Agreement clause is ill-typed** as stated: "if two correct processes
  return `(b, X)` and `(b′, X′)` then `b = 0 ⟹ b′ ≠ 1` and `X = A ⟹ X′ ≠ ⊥`" (p. 6),
  with `⊥` in a grade slot ranging over `{A, B, C}`. It reads as grade `C`, and is
  realized as the `grade` latch's `A`/`C` exclusivity (`GBCASpec.lean:181`, `:195`).
- **TS 1's `Initial` clause names an undeclared field** `out` (source p. 18), absent
  from the same system's `State` line. It is omitted (`Spec.lean:58`).

## 5. Scope boundaries

Beyond D4 — the WCC `guess` label and state field (`Labels.lean:33`, `WCCSpec.lean:21`),
which exist solely for Unpredictability, inexpressible once the guess is dropped.

- **Per-transition fairness markings.** Every transition system in the source carries
  the line "all transitions are fair except those labelled by fail and the call loops"
  (pp. 18–19). The encoding has none; they bear on liveness only.
- **Partial-information adversaries.** The source equips a system with a pair of
  observation functions (Definition 9, p. 4) and a belief construction turning such an
  adversary into an omniscient one (Definition 10, p. 5). Every adversary in the ABA
  chain is declared omniscient there (Definitions 11–15, Specifications 1–3, pp. 6–7),
  which the encoding's unrestricted schedulers match; belief has no counterpart.
- **Termination.** ABA's ε-sure Termination, GBCA's Termination and WCC's ε′-sure
  Termination (pp. 6–7) are unclaimed — `ABA.main` (`Main.lean:56`) is Validity ∧
  Agreement. See `NOTES-Liveness-Roadmap.md`.

One divergence runs in the safe direction. The source's Validity restricts to correct
processes ("if a correct process returns `b` then a correct process had `b` as input",
p. 6), where `ValidityTrace` (`SpecSafety.lean:95`) is returner-unconditional — every
return, corrupted returners included, is witnessed by a preceding `callABA` from a
`NeverCorrupted` caller — and `AgreementTrace` (`SpecSafety.lean:101`) is stronger on
the same axis. `ABA.spec`'s return rule does not inspect `F`, so the stronger statement
is what `spec_safe` (`SpecSafety.lean:855`) proves.

## 6. Adjacent open items

Neither is a fidelity gap; both sit under Future work in `ABA/README.md`.
**Achievability** — `Examples.lean` carries the non-vacuity run on `hybridSpec`, and a
machine-checked positive-mass trace for `hybridImpl`, the system `main` is about, is
outstanding. **`ValidityTrace` witness strengthening** — the witness clause accepts any
preceding `callABA id' b`, where the proof yields a stronger ghost-backed one.
