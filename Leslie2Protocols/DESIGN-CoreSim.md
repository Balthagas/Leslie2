# M1.5 design spike — the core simulation `HybridSpec.abstract H ⊑ ABA.spec`

Status: design document (M1.5). Will migrate into `blueprint/src/content.tex` as the
proof sketch of `coreSim` when M6 lands. Written against the M1 Lean encodings
(`ABA/Spec.lean`, `ABA/WCCSpec.lean`); GBCA.Spec / Core per plan.

## Systems

```
context    := ABA.core ∥ WCC.specFamily                (∥ = full-sync System.parallel)
hybridSpec := (GBCA.specFamily ∥ context).abstract hiddenAPI
target     : ProbabilisticForwardSimulation hybridSpec (ABA.spec P) coreRel
```

M5a update: `ABA.core` needs **no** `withIdle` padding — it participates genuinely in
every label class (τ interleaves inside `parallel` by itself); corrupted-process
handshakes are covered by the dedicated `…Byz` constructors (D11). See Core.lean's
module docstring for the 15-constructor table and deviations D9–D12 (0-based rounds,
fused DECIDED-send in `retW`/`stepRound`, single-slot DECIDED gossip).

Concrete state: `(g, (c, w))` with `g : ℕ → GBCA.SpecState`, `c : ABA.CoreState`,
`w : ℕ → WCC.SpecState`. Abstract state: `a : ABA.SpecState`.

## The relation

`coreRel := diracRel R₀` — all randomness couples outcome-to-outcome at flip time,
so the abstract side stays Dirac:

```
R₀ (g, c, w) a  :=  Inv (g, c, w)   ∧   a = absMap (g, c, w)
```

where `absMap` reconstructs the abstract state field-by-field:

| abstract field | reconstruction |
|---|---|
| `a.F` | the common corrupted set (all `F`-copies equal, by Inv) |
| `a.ret id` | `c.procs id` has fired `retABA` (Core's `retired`/returned flag) |
| `a.val` | `some v` iff some round `r₀` had a unanimous-`v` GBCA outcome: `g r₀`'s bind = `some v` with an A-grade-enabling configuration; `none` before any such round. Equivalently: Core-level, the first `r` at which every honest input to `GBCA_r` was `v`. Inv keeps this well-defined (all later bound values equal `v`). |
| `a.bind` | bound value of `GBCA_R` where `R := curRound (g,c,w)` (the largest `r` with `g r` bound), `none` if no round bound yet |
| `a.coin` | `w R .val` translated (`TVal`), for the current round `R`; `.bot` if `GBCA_R` not yet bound or `WCC_R` unresolved |
| `a.call id` | reconstruction of the abstract pending-input slot: `some b` if `c.procs id` is mid-round with input `b` for round `R+1`-relevant activity (phase-dependent; see matching table), `none` otherwise |

`curRound`, `absMap` are total functions of the concrete state (no choice), which is
what keeps `coreRel` diracRel-shaped.

## The invariant `Inv` (conjuncts)

1. **F-lockstep**: `g r .F = c.F = w r .F` for all `r`, and `card ≤ f` (D1 gives this
   for free — `corrupt` is the same total function everywhere and `fail` is a
   broadcast handshake).
2. **Cofinite quiescence**: all but finitely many rounds are at instance-init
   (`∀ r > curRound, g r = init ∧ w r = init`). Preserved: only round-tagged labels
   move an instance, Core only emits tags ≤ curRound + 1.
3. **Round monotonicity**: rounds `< curRound` are complete (every honest caller of
   `GBCA_r` got its return; `w r` resolved if called); round `curRound` is active.
4. **Per-process phase coherence**: `c.procs id .phase` agrees with the instance
   states (e.g. `calledG r` ⇒ `g r .call id ≠ ⊥` and no return yet; `calledW r` ⇒
   `w r .called id` and not returned; etc.).
5. **Input coherence**: honest `GBCA_r` inputs come from Core estimates
   (`g r .call id = some b` ⇒ `c.procs id .est = some b` at call time), and after a
   decided round (`a.val = some v`) every honest estimate is `v` (this is the concrete
   shadow of spec-invariant `SpecInv.call_val` and is what makes the abstract
   `repropose` guard (D3) satisfiable when we must match Core's re-proposals).
6. **DECIDED coherence**: `c.decidedSent id = some b` ⇒ `absMap.val = some b` — a
   process only gossips DECIDED after an A-grade, and A-grades imply the deciding
   round was unanimous. `retABA`-enabling (n−f DECIDED received + sent) ⇒
   `a.val = some b ∧ a.ret id = false`, matching spec rule 8's guard.
7. **Bound-value coherence**: `g r .bind` for the current round equals `a.bind`, and
   when `WCC_r` resolves with bit `b` = bound value, honest adopters' next-round
   inputs equal `bind` (spec rule 6); on `⊤` or mismatch, re-proposals obey the
   D3 guard via conjunct 5.

## Matching table (concrete step class → abstract move)

Concrete steps are read through the step-inversion lemma for
`((A ∥ (B ∥ C)).abstract H).step` (infrastructure item #11): each case is one row.

| # | concrete step (after inversion) | label seen | abstract match |
|---|---|---|---|
| 1 | Core: env call `callABA id b` (real or idle handshake with families idle) | `callABA id b` | spec rule 1 if `absMap.call id = ⊥ ∧ a.bind = ⊥` else rule 2 loop; `weakStep` strong (one visible step, no τ padding) |
| 2 | Core emits `callG r id b` handshake with `GBCA_r` (hidden → τ) | τ | if this call completes no quorum: abstract stutter (`weakTau_refl` — `absMap` unchanged). If `absMap.call` changes: abstract τ-chain of rule 6/7 fillings (`weakTau_of_step` chained) |
| 3 | `GBCA_r` internal τ-bind (quorum reached) | τ | abstract rule 3 (unanimity) or rule 4 (mixed), one `weakTau_of_step`; `absMap.bind/val` move exactly then. This is where Inv 5 discharges rule 3's guard and where D3-repair compatibility is used |
| 4 | `retG r id out bound` handshake (hidden) | τ | abstract stutter (returns don't move `absMap`; Core phase advances — conjunct 4 re-established) |
| 5 | Core emits `callW r id` (hidden) | τ | abstract stutter |
| 6 | `WCC_r` coin flip (`coinPMF.map`) — the ONLY probabilistic step | τ | **the coupling**: if `r = curRound` and abstract coin pending: abstract `weakTau` = (pre-enabling rule-6/7 τ-chain to reach `call = ⊥ⁿ ∧ bind ≠ ⊥` if needed) `;` spec rule 5, coupled by `ω := coinPMF.map (fun o => PMF.pure (absUpd o))` — same `coinPMF` on both sides (both are `P.coinPMF.map`), identical ε. If `r ≠ curRound` (stale/early flip — only reachable for called-but-superseded rounds): abstract `weakTau_refl` with `ω := coinPMF.map (fun _ => PMF.pure a)`; Inv keeps `absMap` insensitive to non-current instances |
| 7 | `retW r id b` handshake (hidden) | τ | abstract rule 6 (`bind = coin`: adopt) or rule 7 (D3-guarded re-propose) as a τ-step, or stutter, per conjunct 7 |
| 8 | Core DECIDED gossip τ (send/echo) | τ | abstract stutter (conjunct 6 maintained) |
| 9 | Core `retABA id b` (families idle) | `retABA id b` | spec rule 8; guard from conjunct 6; `weakStep` strong |
| 10 | `fail id` broadcast (all three components) | `fail id` | spec rule 9 (D1 total `corrupt`), `weakStep` strong; F-lockstep re-established |

All abstract `weakTau` witnesses are explicit finite chains (`weakTau_of_step`,
`weakTau_trans`, `weakTau_mix` for the per-outcome continuation after the coin) — no
halting subtleties (ABA.spec's τ-rules never force loops; its input-enabledness loops
are visible labels).

## Timing analysis (the risk item)

The delicate row is #6 when the concrete coin fires **before** the abstract
pre-enabling conditions (`call = ⊥ⁿ ∧ bind ≠ ⊥`, rule 5's guard) can be produced by
abstract τ-steps alone:

- `bind ≠ ⊥` abstract requires abstract rule 3/4 to have fired = concrete `GBCA_R`
  bound. Concrete `WCC_R` flip needs > f calls to `WCC_R`; Core only calls `WCC_R`
  after its `GBCA_R` **return**, which requires `GBCA_R` bound. ⇒ at flip time
  `GBCA_R` is bound, and the abstract bind-rule is *enabled or already fired*
  (its quorum guard: n−f abstract calls; abstract `call` slots are filled by τ rules
  6/7 — enabled since `bind_{R−1} ≠ coin_{R−1}` handling and D3 guard are satisfied
  by conjunct 5). ⇒ pre-enabling chain exists. ✓
- `call = ⊥ⁿ` after the bind rule: rules 3/4 reset `call := ⊥ⁿ` themselves. ✓

So the single-constructor `diracRel R₀` should suffice; the **fallback** (second,
pending-coin constructor in `coreRel`) remains available without core changes if a
corner case (e.g. abstract quorum needs F-padding mid-chain) surfaces in Lean.

Potential wrinkle flagged for M6: abstract rule-3/4 quorum counts
`{honest, call ≠ ⊥} ∪ F` — concrete GBCA quorum counts its own callers; F-lockstep
(conjunct 1) aligns the `F` parts, and honest-caller sets align by conjunct 4.

## Non-vacuity witnesses (with M6)

`example`s: a 1-round happy path (n = 4, f = 1): four `callABA` inputs, GBCA_0
unanimous bind, coin flip agreeing, DECIDED diffusion, four `retABA` — exercised on
`hybridSpec` to show the composite is not deadlocked by the padding discipline.

---

# DESIGN v2 (M6, after three agent attempts): the lazy abstract twin

The functional `absMap` design above over-constrains the abstract state and forces
abstract moves at nearly every row. ABA.spec's τ-rules are so permissive
(rule 7 with `val = ⊥` fills calls arbitrarily; rules 3/4 rebind at will from
filled calls) that the abstract twin can instead stay **lazy** and catch up in
τ-bursts exactly when forced. Result: most rows are `weakTau_refl` stutters.

## Relation

`coreRel := diracRel R₀`, `R₀ (g,(c,w)) a := Inv (g,c,w) ∧ Abs (g,c,w) a` with
`Abs` the conjunction (writing `nextUnbound := Nat.find (∃ r, (g r).bind = none)`,
`lastBound := nextUnbound - 1`, meaningful only when `0 < nextUnbound`):

- **C1** `a.F = c.F`
- **C2** `a.ret id = (c.procs id).returned`
- **C3** `a.bind = none → ∀ id, a.call id = (c.procs id).input`
  (pre-first-bind, calls track the visible `callABA` history — `input` is
  write-once, filled by rule 1 answers)
- **C5** `0 < nextUnbound ↔ a.bind ≠ none`, and then `a.bind = (g lastBound).bind`
- **C6** `0 < nextUnbound → a.coin = (w lastBound).val` (as TVal; `⊥` when
  unresolved — coupling keeps outcomes literally equal)
- **C7** `a.val = none ∨ (∃ v, a.val = some v ∧ SafeVal v)` where `SafeVal v`
  (an Inv-side predicate): every bound `g`-round has bind `v`, every honest
  `decidedSent ∈ {none, some v}`, every honest est that can seed a future bind
  is `v` (est-propagation closure)
- **C8** `a.bind ≠ none → a.call = fun _ => none` (bursts always end in a
  rule-3/4 call-reset or a coinFlip, so between rows calls are empty)

## Row dispositions (new)

| row | concrete | abstract answer |
|---|---|---|
| 1 | `callABA id b` real/loop | rule 1 if `a.bind = ⊥` (restores C3), else rule 2 loop; loop answered by loop |
| 2,4,5,7,8 | callG emit, retG receive, callW emit, retW advance, DECIDED τs | **stutter** (`weakTau_refl`) — only Inv moves |
| 3 | `GBCA_r` bindSet (r = nextUnbound) | **burst**: fills (rule 7 mixed-fill when `¬agrees(bind,coin)`, rule 6 otherwise; first-ever burst uses the C3 input-fills as-is) then rule 4 (preferred: keeps `val` untouched — fill both bits when allowed) or rule 3 (only when unanimity is forced, in which case `SafeVal` holds); restores C5, C8 |
| 6 | `WCC_r` flip | if `r = lastBound`: abstract rule 5 (guards: C8 `call = ⊥ⁿ`, C5 `bind ≠ ⊥`; pre-state coin `⊥` by C6+w-unflipped), coupled `ω := coinPMF.map (pure ∘ absUpd)`; stale `r ≠ lastBound`: stutter-couple `ω := coinPMF.map (fun _ => pure a)` (C6 reads `w lastBound`, untouched) |
| 9 | `retABA id b` | **burst then rule 8** (`weakStep` = τ\*-burst ; ret): Inv gives `a.bind = b` for free (A-grade at r_A forces all binds ≥ r_A to be b, and lastBound ≥ r_A); fill all-b (rule 6 if `b = bind = coin`-agrees else rule 7 — D3 fine since `val ∈ {⊥, b}` by C7), rule 3 sets `val := b` if still `⊥`, then rule 8 |
| 10 | `fail id` | rule 9, strong (same corrupt guard both sides via C1) |

## Key Inv conjuncts (concrete-only)

- **I1** F-lockstep: `∀ r, (g r).F = c.F ∧ (w r).F = c.F`, `c.F.card ≤ f`
- **I2** first-round input coherence: `(g 0).call id = some b ∧ id ∉ F → (c.procs id).input = some b`; and generally honest `g`-callers have `input ≠ none` (quorum transfer for the first burst)
- **I3** est-propagation: (a) if `agrees((g lastBound).bind, (w lastBound).val)` then honest ests entering later rounds equal the bind value (so the concrete cannot rebind differently exactly when the abstract's only filler is rule 6); (b) A-grade commitment: an A-locked round `r` with bind `b` forces every bound round `r' ≥ r` to bind `b`, honest ests to `b`, honest DECIDEDs to `b` (⊆ SafeVal b)
- **I4** DECIDED coherence: honest `decidedSent id = some b → ∃ r, (g r).grade = A-side ∧ (g r).bind = some b`; and `n−f ≤ decidedCount id b → ∃ honest sender with decidedSent = some b` (via delivery-soundness `recv ⊆ sent` and `n−f > f`)
- **I5** phase/round coherence: retG r received ⇒ `g r` bound; `w r` called ⇒ caller finished `GBCA_r` ⇒ `g r` bound (hence flips only at bound rounds, `r ≤ lastBound`)
- **I6** bound rounds are downward-closed (`g r` bound → `g (r-1)` bound), so `nextUnbound` characterizes them
- **I7** cofinite quiescence: `∃ R, ∀ r ≥ R, (g r).bind = none` (so `Nat.find` in `nextUnbound` is well-posed; e.g. all rounds > every proc's round are at init)

## Burst lemmas (CoreSim-side, reusable)

- **B1 (fill)**: from `Abs`-state with `a.bind ≠ none` and target function
  `t : Fin n → Bool` s.t. D3-compat (`a.val = some v → t = const v`) and
  `¬agrees(a.bind, a.coin)` (else `t = const a.bind`): τ-chain filling
  `a.call := some ∘ t` (iterate rule 7/6 over `Finset.univ`; induction over a
  list enumeration of `Fin n`)
- **B2 (rebind)**: filled calls with witness `t id₀ = b_r`, quorum ⇒ rule 4
  (if both bits in `t`) or rule 3 (unanimous) reaching `bind = b_r`,
  `call = ⊥ⁿ`, `val` untouched-or-`SafeVal`
- **B3 (val-force)**: `a.bind = some b`, `val ∈ {⊥, b}` ⇒ τ-chain to `val = some b`
  (B1 all-b + rule 3)

All assembled with `weakTau_of_step`/`weakTau_trans`; coupling per
`toProbabilistic`'s pattern.

## Execution plan for M6 (post-crash)

1. CoreSimRel.lean: definitions (`nextUnbound`, `SafeVal`, `Abs`, `Inv`),
   `Inv.initial`+`Abs.initial`, hybrid step-inversion, Inv-preservation
   (per-row lemmas). Skeleton first with `sorry`-stubs, closed one by one.
2. CoreSim.lean: burst lemmas B1–B3, then the 10 rows.
3. Narrow single-lemma subagent delegation where convenient (chunked writes,
   ≤200-line tool calls — three agents died emitting monoliths).

---

# DESIGN v2.1 (Abs-layer correction; Inv layer of v2 unchanged and fully proven)

**Flaw in v2 found by a late-joiner trace:** tying C5 (`a.bind`) to the concrete
bindSet row forces abstract rule 3 (hence `val := v`) while `a.call` shows only the
inputs committed *so far*; a later `callABA(id, !v)` can then concretely enable a
C-grade at the bound round (dissent arrives before any return), C-adopters take a
`!v` coin, round 1 binds `!v`, A-locks, and DECIDEDs `!v` — unmatchable against the
already-set abstract `val = v`.

**Fix — be lazier still:**
1. **bindSet rows are stutters.** The abstract bind-burst moves to the **coin-flip
   row** of each round. There the WCC threshold (`> f` callers) guarantees at least
   one honest process finished `GBCA_r` *before* the flip; if no honest dissent
   existed at `r`, B/C-returns were impossible (their `hw`), so that return was an
   **A-return** — `grade_r = some true` already holds when rule 3 would be forced,
   and `val := v` is then certified by an A-lock. If dissent existed, rule 4
   rebinds without touching `val`.
2. **C5'/C6' are flip-based:** `a.bind ≠ none ↔ ∃ r, (w r).val ≠ ⊥`; on the flipped
   frontier `fr` (largest flipped round; flips are downward-closed by an `w_order`
   conjunct — rounds pass through flips in order), `a.bind = (g fr).bind` …
   with the pre-flip burst at row `fr` establishing it just before rule 5 fires.
   First flip is necessarily round 0 (rounds are passed in order), where fills come
   from C3-inputs (`input_g0` aligns witnesses).
3. **Delete `SafeVal`.** Replace `Abs.val_safe` by the permanent certificate
   `val_cert : ∀ v, a.val = some v → ∃ r, (g r).grade = some true ∧ (g r).bind = some v`.
   Preservation is trivial (both facts permanent); every consumer (D3-guard fills,
   retABA `val`-forcing, uniqueness at DECIDED overwrites) goes through
   `Inv.commit_up` — exactly the machinery already proven in the Inv layer.
4. Supporting Inv additions: `w_order : (w (r+1)).val ≠ ⊥ → (w r).val ≠ ⊥`
   (pass-in-order), and a flip-threshold consequence
   `flip_alock : (w r).val ≠ ⊥ → (g r).grade ≠ none ∨ (∃ honest-dissent call at r)`
   — formulated state-level at tranche time (used to decide rule 3 vs rule 4 in
   the flip-burst and to certify `val` when rule 3 is forced).

Row summary (v2.1): visible rows unchanged; bindSet τ → stutter; flip row =
pre-burst (fills + 3/4) ; coupled rule 5; retABA = burst (B3 via A-lock) ; rule 8;
all other τ rows stutter.

---

# DESIGN v2.2 (final): the never-flipping twin

Two further adversarial-timing corners break v2.1's flip-based constraints:
(a) the concrete frontier-bind's honest witness can be corrupted before the flip
row, stranding the abstract rebind; (b) when the abstract coin agrees with its
bind, rule 6 is the only filler and can force a wrong-value `val`. Resolving both
yields a strictly simpler design:

**The abstract twin NEVER fires rule 5.** Rules 3/4 reset `coin := ⊥`, and
`TVal.agrees (some u) ⊥ = False`, so **rule 7 is available at every post-bind
moment** (D3 permitting). All coin-flip rows are constant-coupled stutters
(`ω := coinPMF.map (fun _ => pure a)`).

**Abs v2.2 fields:** `F_eq`, `ret_eq`, `call_pre` (unbound ⇒ calls = inputs,
banked by answering rule 1 at every `callABA` while unbound), `call_post`
(bound ⇒ calls = ⊥ⁿ), `coin_bot : a.coin = .bot` (always), `val_cert`
(A-lock certificate, unchanged), and the just-in-time readiness invariant:

`bind_ready : a.bind = none → (∀ r, (g r).grade ≠ some false) ∧ (honest inputs pairwise agree) ∧ (∀ r v, (g r).bind = some v → honest inputs ⊆ {v} ∧ f + 1 ≤ #{all ids with input = some v})`

Rationale: while the abstract is unbound, no honest dissent input has ever been
made (the binding policy below fires at the first one), hence every dissent
`g`-call entry was emitted by an already-corrupted process (F-at-emit, permanent),
hence no C-lock can ever fire while unbound (retC's `hw` needs a currently-honest
witness, and honest-emitted dissent would have triggered the policy); by
`bind_succ`, all bound rounds then carry the unanimous honest value `v`, whose
input pool (≥ n−2f ≥ f+1 total inputters, F-insensitive count) always retains a
currently-honest member.

**Binding policy (encoded in which rows burst):**
- `callABA id b` row, abstract unbound, `b` disagrees with an honest input and a
  bound round exists (quorum transfers): answer rule 1 (bank) then rule 4 in the
  τ-tail of the same weakStep (`bind := v₀`, no val). Otherwise plain rule 1/2.
- `bindSet` row (round 0, unbound, mixed honest inputs): rule-4 burst; unanimous
  case: stutter (pool fact established: n−2f ≥ f+1 unanimous inputters).
- `retABA id b` row: if unbound: bind via rule 4 (mixed) or rule 3 (unanimous-b —
  the pool forces the consensus to be `b`; A-lock cert from the DECIDED source);
  then, bound with `coin = ⊥`: rule-7 fill-all-`b` (D3 fine: `val ∈ {⊥, b}` via
  `val_cert` + `commit_up`), rule 3 (`b₀ := !b`) sets `val := b` certified; rule 8.
  All via `fill_chain`/`rebind_*`/`val_force`/`weakStep_of_burst_then_step`.
- `fail id` row: plain rule 9 (no pre-burst needed — `bind_ready` is F-robust).
- Everything else (all hidden handshakes, all τs, ALL coin flips): stutter.

Tranche-D's `IsLastFlipped`/`bind_iff'`/`bind_flip`/`coin_flip` fields are
deleted; its stutter lemmas survive minus those fields. E1's burst kit applies
verbatim (its `havail` agrees-hypothesis is vacuous under `coin_bot`).

## v2.2 amendment (bind_ready weakening; closes the early-mixed gap)

The pairwise-agreement conjunct of `bind_ready` was too strong: two opposite
fresh inputs with nothing bound force a bind the quorum cannot support (real
counterexample, found in the final closure tranche). Corrected field:

`bind_ready : a.bind = none → (∀ r, (g r).grade ≠ some false) ∧ (∀ r v, (g r).bind = some v → (∀ id b, id ∉ c.F → (c.procs id).input = some b → b = v) ∧ f + 1 ≤ #{all ids with input = some v})`

i.e. honest-input unanimity is asserted only once a round is bound. Consequences:
- Early mixed inputs (no bound round): the abstract simply banks (rule 1) and
  stays unbound — no burst, no quorum needed.
- `callABA` dissent WITH a bound round: rule-4 burst as before (quorum via
  `abstract_quorum_of_call`; witnesses: the fresh honest dissent + the f+1 pool).
- The FIRST `bindSet` row now has two real cases: honest-banked unanimous →
  stutter (unanimity + pool established: v₀ = the consensus via `input_g0`,
  pool ≥ n−2f ≥ f+1); mixed → rule-4 burst at that row (quorum transfers from
  the fire-time guard; both witnesses honest-now from the mixed banked inputs).
  E2's "mixed bindSet vacuous" simplification is retracted.
- `bindSet` at r ≥ 1 while unbound: witness est-provenance + no-C-locks +
  `bind_succ` force the new value to equal the standing consensus (unchanged).
- retC-impossibility while unbound: retC requires a bound round, so the
  conditioned unanimity applies — same refutation as before.

