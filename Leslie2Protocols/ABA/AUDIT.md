# Encoding-Fidelity Audit — `Leslie2Protocols/ABA` vs. Leslie blueprint + ABDY22

*Date: 2026-07-24. Scope: definitions and theorem statements only — Lean has checked the
proofs; this audit judges whether the encodings mean what the source papers mean.*

*Ground truth, in priority order: the blueprint TeX (`leslie/blueprint/src/sections/`,
= compiled `Papers/Leslie_blueprint.pdf`) first, `Papers/GBCA-paper.pdf` (ABDY22) second.
All repo prose (docstrings, deviation notes D1–D12, READMEs, TeX annotations) was treated
as untrusted claims and adjudicated independently.*

---

## 1. Per-artifact verdicts

| Artifact | Verdict | Correspondence (paper ↔ Lean, checked guard-by-guard in both directions) |
|---|---|---|
| `Params.lean` | **FAITHFUL** | `3f<n` ↔ ABDY22 Thm 5.3 `n≥3t+1` (the blueprint TeX never states a resilience bound — Lean correctly supplies the paper's); `2ε≤1` ↔ coin mass; `coinPMF`: ε/ε/1−2ε ↔ Specification.tex:41. No `ε>0` assumption (liveness-only, and liveness is unclaimed). |
| `Labels.lean` | **FAITHFUL** | `hiddenAPI` = exactly {callG, retG, callW, retW}; `callABA/retABA/fail/τ` stay visible — matches `ABA:Impl/Hybrid` "API of GBCA and WCC abstracted". `retG` carries the bound value (the blueprint's own Binding linearisation). `guess` omitted (D4). |
| `Spec.lean` | **FAITHFUL-WITH-DEVIATIONS** | 9 constructors ↔ TS 1's 10 rules (fail + fail-loop merged, D1). Rules 1–8 exact, incl. quorum `n−f` with F counted as wildcards, unanimity `∀ honest call ≠ b`, the free-`b` mixed rule, and the D3 repair guard on rule 7. `coin=⊥` silently added to Initial (the paper's Initial omits `coin` and instead contains a stray `out`; Lean's completion is the obvious reading). |
| `WCCSpec.lean` | **FAITHFUL-WITH-DEVIATIONS** | Resolution threshold `>f` (F-wildcard) exact ↔ Specification.tex:157; a single global ε/ε/⊤ draw; on `⊤` the adversary chooses **per-process, per-return** — exactly the paper's `val ∈ {b,⊤}` return rule. D1, D4. |
| `GBCASpec.lean` | **FAITHFUL** (mod D1) | Exact transcription of TS 2: bind needs quorum + honest witness; A/C exclusion via the grade latch; B/C returns need an honest dissent `call = 1−bind`; every return carries the bound value. |
| `GBCAImpl.lean` | **FAITHFUL to blueprint / DIVERGENT from ABDY22** | Every threshold matches `alg:GBCA` (relay f+1; echo/vote/bind/retA n−f; retB n−f any-BIND + BIND-v-once + f+1 VOTE v + \|Valid\|>1; retC n−f BIND-⊥ + \|Valid\|>1). But see finding **#3**. D5–D8. |
| `Core.lean` | **FAITHFUL-WITH-DEVIATIONS** | Phase machine ↔ `alg:ABA` round loop; D10 fusion preserves the `if/elif` order (an A-grade forces `est = some b`); DECIDED echo f+1 / return n−f "having sent it" exact. D9–D12; see finding **#4**. |
| `Hybrid.lean` | **FAITHFUL shape** | `hybridSpec` = blueprint `ABA:Hybrid` (full-sync `parallel` + idle families emulating sync-set ∥_S, then `abstract hiddenAPI` — verified `abstract` bars hidden labels from firing under their own name). `hybridImpl` ≠ blueprint `ABA:Impl`: see finding **#2**. |
| `SpecSafety.lean` | Agreement **ADEQUATE** / Validity **DIVERGENT** | See finding **#1**. |
| `Main.lean` | **ADEQUATE with caveats** | Quantifier structure correct: ∀ scheduler (randomized, history-dependent, optionally-stopping, validity-constrained), init pinned to the Dirac `PMF.pure ls.init` (`Systems/Trace.lean:124-127`), ∀ positive-mass trace. `traceProb` is the finite-cone probability (infinite traces get mass 0) — the right notion for safety, since any violation shows in a positive-mass finite prefix. Axiom guards present and pinned; the repo is built, so `#guard_msgs` passed. **Not claimed**: termination/liveness, unpredictability, fairness, anything about WCC/Gather/SRSD implementations. |
| `Examples.lean` | **GENUINE but WEAK** | Refutes instant-deadlock vacuity (3 inputs, 3 hidden callG, bindSet, one A-return, a fail sync). No coin flip, no completed round, **no `retABA`** is ever witnessed; the impl-side witness is a single input step. Agreement's non-vacuity (a two-return trace) is unwitnessed. Label-type vacuity is excluded: disagreeing traces are representable in `Lab n`, so `AgreementTrace` is not true by unrepresentability. |

---

## 2. Discrepancies, severity-ordered

1. **CRITICAL — `ValidityTrace` does not mean the papers' Validity.**
   Papers: "if a **correct** process returns b then a **correct** process had b as input"
   (Protocols.tex:24; ABDY22 Def 2.2). Lean (`SpecSafety.lean:46-47`): every return's bit is
   witnessed by *some* `callABA` event — possibly directed at a process **corrupted later in
   the same trace**. This is not merely a statement choice: the following spec trace is
   achievable (n=4, f=1):

   ```
   callABA 0 1; callABA 1 0; callABA 2 0; callABA 3 0     (all recorded, bind=⊥)
   → mixed (b:=1)      quorum 4≥3, both bits honestly present; bind=1, val stays ⊥
   → fail 0            corrupt the sole 1-holder (|F|=1 ≤ f)
   → coinFlip → ⊤      (mass 1−2ε; or bit 0 with mass ε) — either disagrees with bind=1
   → repropose 1,2,3 with b:=1        legal: val=⊥ ⇒ arbitrary re-proposal (rule 7)
   → unanim (b:=0)     ∀ honest call ≠ 0 ✓ → val := 1
   → retABA 1 1
   ```

   This positive-probability trace **satisfies `ValidityTrace`** (`callABA 0 1` is present)
   yet **violates paper-Validity** (correct = {1,2,3}, all inputs 0). The real ABDY22
   protocol excludes it (value 1 never enters `Valid`: one sender < f+1 blocks relay, so no
   n−f INPUT-1 quorum exists) — but the spec's rule 7 (`Spec.lean:144-148`, transcribed from
   Specification.tex:47-50) is arbitrary while `val=⊥`, and that over-approximation loses the
   validity-preserving structure. Consequences: (a) the paper's Validity is **unprovable for
   this spec** — the weakening is forced, not stylistic; (b) the blueprint's *own* TS 1 fails
   its own stated Validity property, and no annotation flags it (the D3 discussion repairs
   Agreement only); (c) the SpecSafety docstring's claim that both predicates are "slightly
   stronger than the blueprint's correct-process phrasing" (lines 29-31) is **wrong for
   Validity** — stronger on the returns quantifier, strictly weaker on the witness clause.

2. **MAJOR — `main` is not about the blueprint's `ABA.Impl`.**
   `hybridImpl` keeps **WCC at spec level** (`Hybrid.lean:42-45`); blueprint `ABA:Impl`
   composes `WCC.Impl` (Protocols.tex:66-69). Documented in the docstring ("up to WCC being
   held at spec level"), but the headline "Correctness of ABA" reads stronger than what is
   proven: GBCA is refined to implementation level; WCC is assumed at its specification.

3. **MAJOR — the GBCA implementation is a 4-round compression of ABDY22's 5-round
   Algorithm 6, while claiming to encode it.**
   ABDY22 adds *two* rounds to BCA ("we then add an additional echo4 **and echo5** round to
   get the graded agreement property", p.14) and decides on echo5 evidence with
   "⟨echo4,id,v⟩ from at least t+1" (Alg 6, line 25). The blueprint's `alg:GBCA` (and
   `GBCAImpl.lean`, whose docstring says "ABDY22's Graded Binding Crusader Agreement
   protocol") has INPUT/ECHO/VOTE/BIND only — Algorithm 6 minus the echo5 round, with the
   decide conditions read one level down ("f+1 VOTE b" where the paper has "t+1 echo4 v").
   I re-derived graded agreement and validity for the 4-round variant (the quorum-intersection
   arguments go through with n>3f; the machine-checked `GBCA.Impl ⊑ GBCA.Spec` corroborates),
   so no theorem is false — but the encoding is **not the cited algorithm**, and the
   divergence is documented nowhere (neither blueprint nor Lean).

4. **MAJOR — D12 removes Byzantine DECIDED equivocation.**
   `byzDecided` fills only an *empty* single slot; delivery is at most once per
   (receiver, sender) edge (`Core.lean:413-427`). The papers' Byzantine process can send
   DECIDED 0 to X and DECIDED 1 to Y; the model's cannot — and this is *inconsistent* with
   the GBCA layer, where D5's `sent`-pool plus `byz` injection does support equivocation
   (insert both payloads, deliver selectively). Quorum intersection (two n−f quorums share
   ≥ n−2f > f senders, hence an honest one) suggests Agreement survives the stronger
   adversary, but the formal theorem does not cover it. The deviation is documented
   descriptively ("even a corrupted process gossips one consistent DECIDED payload") but
   never justified.

5. **MINOR — D2 does not exist.**
   Deviations are D1, D3–D12 (11 total), scattered across module docstrings with no central
   list; `GBCAImpl.lean:29` says "continuing the project's D1–D4", implying a D2 should
   exist. Either a silently renumbered/deleted deviation or a documentation gap. No
   corresponding undocumented encoding change surfaced in the rule tables; the unnumbered
   candidates are the `coin=⊥` Initial completion and the shared round-tagged label alphabet,
   both benign.

6. **MINOR — corrupt processes cannot act arbitrarily on the ABA interface.**
   There are no Byz drivers for `callABA`/`retABA` (D11 covers only the sub-protocol
   handshakes); corrupt returns must pass the same n−f DECIDED quorum guard (noted at
   `Core.lean:67-69`, matching the spec's F-blind return rule). Inherited from the blueprint.
   The papers' properties ignore corrupt outputs, so nothing is misstated — but the modeled
   adversary is weaker than "may act arbitrarily" on the visible interface, and this is
   precisely what lets `AgreementTrace` quantify over *all* returns (legitimately stronger
   than the paper on that axis).

7. **MINOR — `ValidityTrace` is unordered.**
   The witnessing call is not required to precede the return in the trace. The proof in fact
   produces a preceding witness (via `labelsUpTo k`); the statement understates what is
   proven. Acknowledged in the docstring.

8. **MINOR — blueprint↔ABDY22 return threshold.**
   `alg:ABA` returns at n−f DECIDED receipts where ABDY22's termination note uses 2t+1
   (equal only at n = 3f+1). Lean follows the blueprint. Safety-neutral.

9. **MINOR — D1 determinization** removes fail-labels-without-effect traces (the paper's
   input-enabledness loop can also fire when the corruption guard holds). Immaterial to the
   ⊆-shaped theorems; both sides use the same total `corrupt`, the cap `|F| ≤ f` is enforced,
   and corruption is irrevocable — matching the papers' adversary budget.

---

## 3. Deviation & TS-repair adjudication

**TS-repair (Specification.tex:51-64) — annotation VERIFIED.** The unguarded rule 7 admits
exactly the claimed 6-step Agreement violation (replayed independently before reading the
Lean: unanimity sets `val=v`; coin ≠ bind; unguarded re-proposal floods `1−v`; unanimity
re-fires overwriting `val := 1−v`; returns of both `v` and `1−v` appear). The repair
`val=⊥ ∨ b=val` blocks it, matches the protocol's real invariant (post-unanimous rounds
re-input only v), and *restricts* the spec — making `refines`/`main` stronger, not weaker.
It is one of two minimal single-rule fixes (the alternative: guarding the unanimity rule);
the chosen one mirrors the protocol mechanism. The stray-`out` note is also correct (a
genuine leftover; note the paper's Initial *also* omits `coin`, which Lean silently
completes to `⊥` — the obvious reading).

| Dev | Adjudication |
|---|---|
| D1 | Sound; justification (lockstep `F` under the fail broadcast) correct. See discrepancy #9. |
| D2 | **Missing** — see discrepancy #5. |
| D3 | Correct and load-bearing: Agreement is false for the unrepaired TS (counterexample real). |
| D4 | Harmless; Unpredictability explicitly out of scope; no impact on Validity/Agreement. |
| D5 | Faithful IT-model network: authenticated (no forging honest senders — `deliver` requires `m ∈ sent j`), duplication absorbed by sets, distinct-sender counting, corrupt equivocation preserved at this layer. |
| D6 | Gate justification **verified**: n−f BIND(v) receipts ⇒ ≥ n−2f honest-at-send senders; at most f ever corrupted ⇒ ≥ n−3f ≥ 1 permanently honest ghost witness, so `bindGhost` stays enabled — a scheduling/liveness-only restriction. The docstring's C-return caveat is honest. |
| D7 | Write-only ghost mirroring the spec's grade latch; harmless. |
| D8 | Defensible per ABDY22's "to participate…" framing; removes uncalled-process amplification from the modeled impl (shrinks the refinement LHS; safety-neutral in practice). Documented. |
| D9 | 0-basing consistent everywhere (core `round` init 0, `callG r` requires `round = r`, ℕ-indexed families); cosmetic. |
| D10 | Fusion preserves the algorithm's branch order (A-grade forces `est = some b`, so the `elif` is honored). The last-write-wins `decidedSent` overwrite rests on a proof-level coherence claim not re-verified here. Representation choice. |
| D11 | Adequate: corrupt ids retain the **full honest repertoire** (no honesty guards on honest-path constructors) plus free handshake drivers, and the family side still constrains their sub-protocol returns — Byz ⊇ honest, as a Byzantine model requires. |
| D12 | See discrepancy #4 (equivocation gap). |

---

## 4. Not validated

- **All proof bodies** (per the audit mandate): SpecSafety internals, CoreSim / CoreSimRel /
  CoreSimBurst, GBCASim / GBCAFamily, the framework Results 1–5, `safety_transfer` beyond
  its (trivial, checked) statement.
- **WCC.Impl / Gather / SRSD / BRB / AVSS** — absent from the development; `main`'s
  "implementation" is partially abstract (discrepancy #2).
- **Liveness, fairness, unpredictability** — the TS Fairness clauses have no Lean
  counterpart; nothing liveness-shaped is claimed (correctly so).
- **PDF↔TeX identity** — the TeX was trusted as the compiled blueprint's source
  (titles/page count spot-checked only).
- **`#guard_msgs` execution** — verified textually, and built `.olean` artifacts exist
  (implying the guards passed at build time); `lake build` was not re-run.
- **Reachability of a full decision** in the hybrid: no machine-checked trace reaches
  `retABA` (Examples stop at the first A-return handshake), so "the encoded hybrid can
  actually decide" rests on inspection of the rule chain, not on a witness.

---

## Bottom line

The encodings are unusually careful transcriptions of the *blueprint* — every threshold and
guard checked matches — and `AgreementTrace` / `main`'s quantifier structure faithfully
(indeed more strongly than the paper) capture Agreement under all schedulers from the Dirac
init. The genuine gaps are: **Validity as proven is a strictly weaker property than the
papers'** (and cannot be strengthened without changing the spec — see the concrete
counterexample in §2.1); the GBCA implementation is a **4-round variant misattributed to
ABDY22**; **WCC stays at spec level** in the headline theorem; and the DECIDED gossip layer
**under-approximates the Byzantine adversary** (no equivocation).
