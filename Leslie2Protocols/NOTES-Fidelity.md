# Fidelity — the encoding against its sources

A registry of the places where the ABA encoding and the artifacts it answers to do not
coincide, restricted to divergences carrying no D-number, for a reader holding the
sources open beside the Lean.

**Two sources, in a chain.** The *source blueprint* — "Verifying ABA with Leslie",
`Papers/Leslie_blueprint.pdf` — supplies the transition systems (TS 1 = ABA, TS 2 =
GBCA, TS 3 = WCC, pp. 18–19) and the pseudocode (Algorithm 1 = the ABA core, p. 14;
Algorithm 2 = GBCA, p. 15). It in turn adapts *ABDY22* (Abraham, Ben-David and
Yandamuri, PODC 2022), whose Algorithm 6 is the GBCA of record. The encoding follows the
source blueprint; where the source blueprint departs from ABDY22 the encoding inherits
the departure.

**The D-registry is elsewhere.** The catalogued deviations — D1, D3–D5, D8–D16, D12
refined to D12′ — are cited at the point of use in the ABA module docstrings, summarised
in `ABA/README.md`, and listed in the blueprint chapter (`blueprint/src/content.tex:762`).

## 1. The inherited algorithmic gap

The one substantive item. The verified GBCA implementation (`GBCA.ImplStep`) is the
source blueprint's **four-round** form of ABDY22's five-round Algorithm 6: the fifth
echo round is elided and the decide conditions read one message level down —
`ImplStep.retB`'s `hvote : f + 1 ≤ recvCount id (VOTE v)` (`GBCAImpl.lean:413`) sits
where ABDY22 reads `t + 1` fourth-round echoes at the fifth. Graded agreement and
validity go through for the four-round form under `n > 3f`, and `implRefines`
(`GBCASim.lean:1306`) machine-checks it against TS 2, so no theorem here is false; the
gap is one of attribution, the source blueprint presenting Algorithm 2 as ABDY22's.
Annotation lives in `GBCAImpl.lean`'s module docstring (lines 15–23), in the
blueprint chapter's caption for Algorithm 2 (`blueprint/src/content.tex:1243`), and in
the source blueprint's own TeX (`Leslie/blueprint/src/sections/Algorithm.tex:35`, a red
note on Algorithm 2); the source's PDF caption reads "Implementation of GBCA from
[ABDY22]" with no such note.

Closing the gap is an available option, not a plan: re-encode the stage automaton per
Algorithm 6 — a fifth message kind, a fifth send rule, return guards one level up — and
re-prove `implRefines`. The lazy-bind *shape* survives, being indifferent to how many
stages precede a return: the specification's `bind`/`grade` carried as receipt
certificates (`bind_cert`, `gradeA_ev`, `gradeC_ev`, `GBCASim.lean:1100–1108`) with
`bindSet` fired inside the weak step at the first `A`/`B`-return
(`firstRetA_burst`/`firstRetB_burst`, `GBCASim.lean:1237`, `:1256`). The per-stage
skeleton does not: `Inv`'s rows come one pair per message kind (`echo_conf`/`echo_once`,
`vote_conf`/`vote_input`, `bind_once`/`bind_conf`, `GBCASim.lean:218–236`), and the
harvest lemmas walking them down to `INPUT` receipts (`echoQuorum_of_vote_receipts`
through `bindSet_guards`, `GBCASim.lean:1040`–`:1182`) name the stage they refine at
each hop. Both would be re-indexed rather than reused.

## 2. Interpretation-level readings

**"Received once."** Algorithm 2's wait case (b) requires that "⟨BIND, b⟩ has been
received once". `ImplStep.retB` reads this as *from at least one sender*: `honce : ∃ k,
Msg.bind (some v) ∈ s.recv id k` (`GBCAImpl.lean:412`), not as a cardinality constraint
of exactly one receipt. The hypothesis is a genuine part of the rule, reproduced
verbatim per-process (`GBCAProc.lean:189`, `FlatABA.lean:197`, `:228`), but no proof
consumes it: the refinement's `retB` rows bind it and leave it unused
(`GBCASim.lean:912`, `:1521`), discharging the `B`-return's specification-side guards
from `hvote` and `hval` instead. Either reading supports the same theorems.

**Terminating `return` as state.** The pseudocode's `return` ends the process; the
encoding renders that as a fire-once flag — `ProcState.returned` (`GBCAImpl.lean:97`),
guarded at all three GBCA returns (`GBCAImpl.lean:405`, `:415`, `:423`), and
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
(`GBCAImpl.lean:343`). Both are sound for the same reason — receipt sets are `Finset`s
and re-delivery is `insert` into a set, so the guard removes redundant transitions
rather than reachable states — and the asymmetry reappears exactly in the per-process
automata, each guard splitting across the two ends of a rendezvous: the DECIDED halves
carry it (`CoreProcStep.netSelf`/`netRecv`, `CoreProc.lean:362`, `:371`;
`ABAProcStep.dnetSelf`/`dnetRecv`, `FlatABA.lean:338`, `:348`), the stage halves do not
(`GBCA.ProcStep.netSelf`/`netRecv`, `GBCAProc.lean:269`, `:277`;
`ABAProcStep.gnetSelf`/`gnetRecv`, `FlatABA.lean:356`, `:367`).

## 4. Source defects the encoding does not reproduce

- **TS 1 violates Agreement** without the rule-7 re-propose guard and the papers'
  Validity without the rule-4 support guard; both counterexample traces are in
  `Spec.lean`'s module docstring (D3 at lines 36–43, D13 at 15–35), the second with the
  `decide` witness at `Spec.lean:209–212` — the support guard failing on inputs
  `1,0,0,0` at `n = 4, f = 1`.
- **TS 2's singular binding witness** (`∃ id ∉ F, call[id] = b`, source p. 19) loses
  provenance one level down, and `hybridSpec` over it violates Validity; the
  deterministic trace is in `GBCASpec.lean`'s docstring (lines 29–49). Both TS 1
  defects and this one are annotated in the source blueprint's TeX
  (`Leslie/blueprint/src/sections/Specification.tex`, red notes at the affected
  rules). D14 and D15
  replace every such witness with an `F`-blind count.
- **The Graded Agreement clause is ill-typed** as stated: "if two correct processes
  return `(b, X)` and `(b′, X′)` then `b = 0 ⟹ b′ ≠ 1` and `X = A ⟹ X′ ≠ ⊥`" (p. 6),
  with `⊥` in a grade slot ranging over `{A, B, C}`. It reads as grade `C`, and is
  realized as the `grade` latch's `A`/`C` exclusivity (`GBCASpec.lean:128`, `:140`).
- **TS 1's `Initial` clause names an undeclared field** `out` (source p. 18), absent
  from the same system's `State` line. It is omitted (`Spec.lean:48`).

## 5. Scope boundaries

Beyond D4 — the WCC `guess` label and state field (`Labels.lean:33`, `WCCSpec.lean:20`),
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
