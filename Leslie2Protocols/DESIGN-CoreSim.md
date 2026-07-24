# Design — the core simulation `hybridSpec ⊑ ABA.spec` (`coreSim`)

Companion design document to the Lean proof in `ABA/CoreSimRel.lean` (relation +
invariant), `ABA/CoreSimBurst.lean` (abstract τ-burst kit), and `ABA/CoreSim.lean`
(the per-row simulation proof). A condensed version is a candidate proof sketch of
`coreSim` for `blueprint/src/content.tex`. The spec-level repairs the simulation
depends on are labelled D13/D14/D15 (Validity provenance) and D12′ (DECIDED
equivocation).

## Systems

```
context    := ABA.core ∥ WCC.specFamily                (∥ = full-sync System.parallel)
hybridSpec := (GBCA.specFamily ∥ context).abstract hiddenAPI
target     : ProbabilisticForwardSimulation hybridSpec (ABA.spec P) coreRel
```

`ABA.core` needs no `withIdle` padding — it participates genuinely in every label
class (τ interleaves inside `parallel` by itself); corrupted-process handshakes are
covered by the dedicated `…Byz` constructors (D11). See `Core.lean`'s module
docstring for the 15-constructor table and deviations D9–D12′ (0-based rounds, fused
DECIDED-send in `retW`/`stepRound`, per-process DECIDED pools — see § D12′ below).

Concrete state: `(g, (c, w))` with `g : ℕ → GBCA.SpecState`, `c : ABA.CoreState`,
`w : ℕ → WCC.SpecState`. Abstract state: `a : ABA.SpecState`.

## The relation: the ultra-lazy two-phase twin

`coreRel := diracRel R₀` with `R₀ (g,(c,w)) a := Inv (g,c,w) ∧ Abs (g,c,w) a` — all
randomness couples outcome-to-outcome, so the abstract side stays Dirac.

The twin is **ultra-lazy** and **never-flipping**. It never fires rule 5, so its coin
is permanently `⊥` (field `coin_bot`); with `TVal.agrees (some u) ⊥` false the rule-7
filler stays available at every post-bind moment and every concrete coin-flip row
couples to a stutter. And it never binds *between* rows: it occupies one of two phases,
keyed on `a.val`, and moves only at the visible `retABA` that opens phase 2.

### `Abs` fields (`CoreSimRel.lean`)

- `F_eq : a.F = c.F`
- `ret_eq : ∀ id, a.ret id = (c.procs id).returned`
- `coin_bot : a.coin = ⊥` (the twin never fires rule 5)
- `phase` — the two-phase disjunction on `a.val`:
  - **Phase 1** (pre-first-return): `a.bind = none ∧ a.val = none`, the abstract call
    row mirrors the concrete write-once external inputs
    (`∀ id, a.call id = (c.procs id).input`), and the ghost is synced on every committed
    input (`∀ id b, (c.procs id).input = some b → a.input id = some b`).
  - **Phase 2** (post-first-return): `∃ v, a.bind = some v ∧ a.val = some v`, the board
    is clear (`∀ id, a.call id = none`), and `v` is permanently certified by a concrete
    `A`-lock (`∃ r, (g r).grade = some true ∧ (g r).bind = some v`).

Phase 1 banks each genuine `callABA` with rule 1, whose unconditional ghost overwrite
keeps `a.input` in step with the concrete inputs; the twin stays fully unbound and
answers every hidden row with a stutter. The single `retABA` answer runs the phase-1
decide burst (§ Row dispositions), which binds, fills, decides, and clears the board in
one τ-tail, landing the twin in phase 2. From there `a.val` pins the decided value for
good, so every later row is a stutter or a direct rule-8 return.

### The frame lemma

`Abs` reads only three projections of the concrete state: `F`, the per-process
`input`/`returned` fields, and the `g`-side `A`-lock certificate. `Abs.frame` packages
exactly this — `Abs` transfers along any frame preserving `F`, `input`, `returned`, and
(weakly, up to the certificate existential) the `A`-locks — and `Abs.w_swap` is the
`w`-only corollary, since the twin never reads the coin state. Together they replace the
per-row stutter arguments: every hidden row preserves the three projections, so its
`Abs`-match is one `Abs.frame`/`Abs.w_swap` invocation rather than a bespoke
re-derivation (the six Stage-C stutter lemmas of `CoreSimRel.lean` are all instances).

## Row dispositions

Concrete steps are read through the step-inversion lemma for
`((A ∥ (B ∥ C)).abstract H).step`; each class is one row of `CoreSim.lean`.

| concrete row | label | abstract answer |
|---|---|---|
| every hidden handshake (`callG`/`retG`/`callW`/`retW`), `bindSet`, DECIDED gossip τ | τ | stutter (`Abs.frame`; only `Inv` moves) |
| **every** `WCC_r` coin flip | τ | constant-coupled stutter `ω := coinPMF.map (fun _ => pure a)` (`Abs.w_swap`; the twin never flips) |
| `callABA id b`, phase 1, genuine (idle-exit input) | `callABA id b` | rule 1 (banks the concrete input into `a.call` and the ghost) |
| `callABA id b`, otherwise (phase 2, or a self-loop re-call) | `callABA id b` | rule 2 (first-write-wins; no `Abs`-field change) |
| `retABA id b`, phase 1 | `retABA id b` | `decide_burst` then rule 8 (`weakStep_of_burst_then_step`) — see below |
| `retABA id b`, phase 2 | `retABA id b` | rule 8 directly (`commit_up` pins `b = v`) |
| `fail id` | `fail id` | rule 9 (same corrupt guard via `F_eq`; robust in both phases) |

The single burst is `decide_burst` (`CoreSim.lean`), fired at the phase-1 `retABA`. From
an unbound, undecided twin with `coin = ⊥`, a quorum on the standing calls, and `f + 1`
call-and-ghost-or-`F` material for the returned bit `b` (supplied by the concrete pool
`Inv.bind_supp` at the `A`-locked round, transferred through phase 1's call/ghost sync),
it reaches `bind = val = some b` with the board clear:

- (i) if no honest call dissents from `b`, one rule-3 step decides outright;
- (ii) otherwise byz-fill the empty `F`-slots with the majority bit `v'` (the quorum
  pigeonholes its `n − f ≥ 2f + 1` callers-or-`F` onto two bits) and rule-4 rebind to
  `v'`, *clearing the board* — which is what makes every `F`-slot fillable afterwards
  (the fill-only wall of § Why this shape does not bite TS 1: rules 3/4 reset `call`);
- (iii) fill the `f + 1` material for `b` (ghost/byz branches) and the rest with `v'`
  (bind branch), then rule-4 rebind to `b` (rule 3 if everything is material);
- (iv) `val_force'` (all-`b` bind-branch fill + rule 3), rule 8.

The trailing rule 8 is glued on by `weakStep_of_burst_then_step`: the burst is the
leading τ-closure and the visible `retABA` the middle hyper-step.

## The spec repairs as design

Four spec-level repairs make the simulation possible; each is a permanent, `F`-blind
provenance discipline. D13/D14 repair the abstract specs (TS 1 = `ABA.spec`,
TS 2 = the `GBCA` layer) against the papers' Validity; D15 is the implementation-side
harvest that re-closes `GBCASim` under D14; D12′ closes a DECIDED-equivocation gap.

### D13 — TS 1 Validity (ghost provenance)

The blueprint's TS 1 fails the papers' Validity: rule 7's free re-propose (while
`val = ⊥`) and rule 4's free mixed-bind lose input provenance, so a bit input only by a
later-corrupted process can win. The repair principle: a value may circulate only with
`f + 1` distinct supporters — at most `f` processes are *ever* corrupted, so `f + 1`
supporters always include a never-corrupted one, and provenance survives dynamic
corruption with no future-peeking guard (`3f < n` supplies `n − 2f ≥ f + 1`).

Deltas to `Spec.lean`:

- **Ghost** `input : Fin n → Option Bool` in `SpecState`. Rule 1 records
  unconditionally; rule 2 records first-write-wins
  (`input := if s.input id = none then update … else s.input`) — sound (rule-2 events
  are genuine `callABA` trace events) and load-bearing: it is what lets the twin mirror
  inputs banked after it binds. No honesty guards anywhere; every support count is
  `F`-blind, hence immune to later `fail`s.
- **Rule 4** gains `hs : f + 1 ≤ #{id | s.call id = some b}` (support among all
  callers). This genuinely shrinks enabledness — `n − 2f` honest callers can split as
  low as `⌈(f+1)/2⌉` per bit — by design; spec liveness is unclaimed.
- **Rule 7**: `h₃` becomes
  `(s.val = none ∧ (s.input id = some b ∨ s.bind = some b)) ∨ s.val = some b`. Coin
  values are deliberately not licensed (`b = coin-bit` would re-admit a
  Validity-breaking decision via a probability-ε coin flip).
- **New rule** `callByzFill` (τ):
  `id ∈ s.F → s.call id = none → call := update s.call id (some b)`, no ghost record.
  Necessity: the concrete adversary fills GBCA call slots via hidden byz `callG` drivers
  with no `callABA` event, so without an abstract counterpart the rule-4 `hs` is
  undischargeable on exactly the validity-*satisfying* traces where byz phantoms complete
  the `f + 1` pool around one never-corrupted inputter. Byz entries are paid for by the
  `F` budget through the `id ∈ F` disjunct, not the ghost; `decide_burst`'s
  `byz_fill_chain` is the twin's use of this rule.
- Rules 3, 5, 6, 8, 9 unchanged (rule 3's quorum already leaves `≥ n − 2f ≥ f + 1`
  honest callers of the decided bit).

Provenance invariant (extending `SpecSafety.SpecInv`), with
`SuppOK s v := f + 1 ≤ #{id | s.input id = some v ∨ id ∈ s.F}` (monotone in `F` and
`input`): **V-P0** `bind = none →` every call is an input-holder or in `F`; **V-P1**
`bind = some v → SuppOK s v`; **V-P2** `val = some v → SuppOK s v`; **V-P3** the
post-`val` collapse of rule 7's `val`-branch writes into `b = v`. Preservation is by
monotonicity: rule 4 harvests its `f + 1` callers through V-P0/V-P3, rule 3 through its
`n − 2f` honest callers, `callByzFill` lands in the `id ∈ F` disjunct. Validity endgame
(the budget pigeonhole): at any `retABA _ v`, V-P2 gives `f + 1` supporters; they cannot
all lie in the final `F` (`|F| ≤ f`), so some supporter is never corrupted and its
recorded input is a genuine prior `callABA`.

### D14 — TS 2 Validity (SuppOK guards)

TS 2 (the `GBCA` layer, `GBCASpec.lean`) certifies `bindSet` by a *single* honest
witness (`∃ id ∉ F, call id = b`), and `B`/`C` dissent by a single honest dissenter —
the same singular-witness provenance loss one level down, and `hybridSpec` built on it
provably violates Validity (§ Why this shape). ABDY22's implementation carries the
`f + 1` via Valid-set relay thresholds; TS 2 abstracted it to one witness. The repair is
exactly TS 1's `SuppOK` shape: `bindSet`'s guard becomes
`f + 1 ≤ #{id | call id = some b ∨ id ∈ F}`, and the `retB`/`retC` dissent guards the
same for `!v`. Directly `F`-blind — the count is monotone in `F` and `call`, so it is
immune to later `fail`s — and the budget pigeonhole transfers verbatim: among `f + 1`
supporters some member is outside the final `F`, hence a never-corrupted genuine caller.
Corrupt supporters are paid for by the `F` budget itself, with no phantom-call
bookkeeping and no spec-side fills.

### D15 — the implementation harvest (`GBCASim`)

D14's superset counts must be discharged from `GBCA.Impl`. The bridge is one new `Inv`
conjunct, `input_supp`:

```
∀ b j, j ∉ F → Msg.input b ∈ sent j →
  (proc j).input = some b ∨ f + 1 ≤ #{id | (proc id).input = some b ∨ id ∈ F}
```

Preservation: `callABA` adds a holder; a `relay`'s `f + 1` receipt senders are each in
`F`, a holder, or a prior honest non-holder sender (the pre-state conjunct closes); `byz`
senders are in `F`; `fail` grows the count and shrinks the triggers; the count is
monotone throughout. The harvest answering all three D14 sites is `suppI_of_bind`: an
honest `BIND b` multicast chases `BIND → VOTE → ECHO` to an honest `ECHO b` sender, whose
`n − f ≥ f + 1` `INPUT b` receipts feed `Inv.supp_of_input_receipts`; the `retB`/`retC`
dissent bit is covered by `bothValid`'s own `n − f` `INPUT (!v)` receipt quorum at the
returner, so no separate dissent-relay argument is needed. `call_eq` stays exact and
`instRel_corrupt` is untouched — the superset guards need nothing from the concrete
relation but the honest slots it already mirrors.

### D12′ — the DECIDED equivocation gap

D12 modeled DECIDED gossip as a single per-process slot, which cannot send `DECIDED 0`
to X and `DECIDED 1` to Y — an under-approximation inconsistent with the GBCA layer's
equivocating D5 sent-pool. D12′ mirrors D5 at the DECIDED layer (`Core.lean`):
`decidedSent : Fin n → Finset Bool` and `decidedRecv : Fin n → Fin n → Finset Bool`
(pools that only grow); `sendDecided` inserts, `deliver` is per (receiver, sender, bit)
with soundness `b ∈ decidedSent j` and an at-most-once `b ∉ decidedRecv i j` guard;
`byzDecided` is guarded *only* by `id ∈ F`. Honest pools stay at card ≤ 1 in reachable
states (A-grade certificates pin one bit), but no card invariant is needed. The invariant
rewiring (`CoreSimRel.lean`): `recv_sound` becomes per-bit and *honesty-free*
(`b ∈ decidedRecv i j → b ∈ decidedSent j`, preserved by pure monotonicity, since sent
pools never shrink); `decided_src` becomes per pooled bit
(`id ∉ F → b ∈ decidedSent id → ∃ r` A-lock cert for `b`) — the equivocation-robust
form: corrupted equivocators may pad any bit's tally, but the `retABA`-row pigeonhole
(`n − f` distinct senders of `b`, `|F| ≤ f`, `n − f > f`) recovers a never-corrupted
sender of `b`, whose pooled `b` carries the A-lock certificate feeding `decide_burst`
exactly as before.

## `Inv`: the concrete invariant (`CoreSimRel.lean`)

Roughly thirty conjuncts (names as in the code), grouped:

- **F-lockstep**: `F_g`, `F_w` (every instance's `F` equals `c.F`), `F_card`.
- **Round structure**: `down_closed` (bound rounds downward-closed), `quiescent`
  (cofinitely many rounds unbound), `round_bound`, `call_round`, `w_call_round`,
  `w_bound`/`w_called` (flips/W-calls only at bound rounds), `w_order`, `round_flip`.
- **Input/est provenance**: `input_g0`, `input_g0_perm`, `input_called`, `phase_input`,
  `est0`, `est_ret`, `est_prev`, `est_prev_ne`, `call_prov`, `bind_succ` (a later bind's
  value has provenance in the previous round's bind/`C`-lock or dissent), `c_chain`.
- **Locks and DECIDED**: `a_commit` (an `A`-lock at bind `b` forces every later bound
  round to bind `b`, honest ests to `b`, honest DECIDEDs to `b`), `agree_locked`,
  `grade_needs_bind`, `grade_A_src`, `decided_src` and `recv_sound` (both in their D12′
  per-bit, honesty-free forms — see above), `bound_quorum`.
- **Support pools**: `bind_supp` (I26) — every bound round's value carries a permanent
  `f + 1` input-or-`F` pool (`InputSupp`, the concrete mirror of TS 1's V-P1), established
  at `bindSet` from the D14 count guard (round 0 wholesale via `input_g0_perm`, `r ≥ 1`
  through `call_prov` into the previous round's pools) — and `clock_supp` (I27), its
  `C`-lock dissent twin, established at `retC`. Both are permanent and monotone; they are
  what supplies `decide_burst`'s `f + 1` material through phase 1's call/ghost sync.
- **Dissent bookkeeping**: `flip_alock`, `retg_residue`, `wcalled_residue`,
  `idle_no_wcall`, each keyed on the permanent `F`-free `DissentResidue` (with its
  `transport` lemma for frame-agnostic preservation). The support pools `bind_supp`/
  `clock_supp` latently subsume much of this residue machinery — both are permanent
  `F`-free provenance facts — so folding the residue conjuncts into the pools is a
  recorded future refactor.

Each row of `CoreSim.lean` proves `Inv`-preservation for its step class and then the
`Abs`-level match above.

## The burst kit (`CoreSimBurst.lean`)

Pure `ABA.spec`-side weak-τ chains, no `Inv`/`Abs` reasoning:

- `fill_chain` — from a bound `Abs`-state, a rule-7 τ-chain reaching any `val`-compatible
  target call vector (induction over the process list).
- `byz_fill_chain` — the `callByzFill` analogue: fills empty `F`-slots to any target,
  paying through the `F` budget rather than the ghost.
- `rebind_mixed` / `rebind_unanim` — filled calls with a quorum reach a rule-4 (resp.
  rule-3) rebind: `bind := b`, `call := ⊥ⁿ`, `val` untouched (resp. set, certified).
- `weakStep_of_burst_then_step` — packaging: a τ-burst then a visible step is a
  `weakStep`.

All assembled with `weakTau_of_step`/`weakTau_trans`; `val_force'` — the
`bind`-value-decoupled fill-and-decide that closes `decide_burst` — lives in
`CoreSim.lean` (its `coin = ⊥` hypothesis makes `TVal.agrees` false, so the all-`b` fill
is licensed only from `a.bind = some b`, exactly how the burst invokes it).

## Why this shape

Each of the following adversarial-timing traces kills a natural simpler alternative;
recording them is what pins the design.

1. **Eager functional abstraction fails.** If the abstract state is a total function of
   the concrete (`a = absMap (g,c,w)`) with `a.bind`/`a.val` tied to the concrete
   `bindSet` row, abstract rule 3 is forced the moment a round binds unanimously — but a
   late joiner can then submit a dissenting `callABA`, enable a `C`-grade at that round,
   steer the next round to bind the opposite value, `A`-lock it, and DECIDE against the
   already-committed abstract `val`. Hence laziness: the twin commits as late as possible.
2. **Flip-anchored abstraction fails.** Anchoring `a.bind` to the concrete flip frontier
   is broken twice over: the honest witness backing the frontier round's rebind can be
   corrupted *before* the flip row (stranding the abstract quorum), and when the abstract
   coin agrees with its bind, rule 6 is the only filler and can force a wrong-value `val`.
   Hence the never-flipping twin: with `coin = ⊥`, rule 7 is always available and the
   rule-5/rule-6 timing issues vanish.
3. **Unconditional honest-unanimity fails.** Requiring pairwise agreement of honest
   inputs whenever the twin is unbound is too strong: two opposite fresh inputs with
   nothing bound yet are reachable and would force a bind no quorum supports. The
   ultra-lazy twin sidesteps the question entirely — it carries no unanimity constraint,
   because phase 1 never binds.
4. **Free re-propose loses provenance (TS 1).** In the blueprint's TS 1, rule 7's free
   re-propose and rule 4's free mixed-bind let a bit input only by a later-corrupted
   process win a return: input `1` from a lone process that is then `fail`ed is
   re-proposed and bound while every never-corrupted process input `0`. This forces the
   D13 `f + 1` `F`-blind support discipline.
5. **The singular witness loses provenance (TS 2).** Deterministically at `n = 4, f = 1`,
   inputs `1,0,0,0`: TS 2's `bindSet 1` fires off the sole `1`-holder, `retB`-adopt
   propagates `est := 1`, round-1 unanimity decides `1`, `fail 0`, `retABA 1 1` — yet
   every never-corrupted process input `0`. A single certifying witness is exactly the
   D13 loss one level down; hence the D14 SuppOK guards.
6. **Fill-only designs cannot be value-pinned (the wall).** One might try to discharge
   the D14 counts spec-side, filling empty `F`-slots at the *implementation* relation
   instead of counting them. This dies on a pre-corruption genuine call: at `n = 4,
   f = 1`, a genuine `callG 3 0` forces the honest slot 3 to mirror `0`; after `fail 3`
   the adversary amplifies `INPUT 1` to a `BIND 1` and a visible `retA 0 1`, but the spec
   state has `#callers(1) = 1 < 2` and slot 3 is *genuinely full* — no τ fills it, since a
   fill needs an *empty* `F`-slot. The spec does emit the trace, via a different run that
   answers `callG 3 0` with a loop and byz-fills slot 3 with `1` after `fail 3`; but that
   choice needs knowledge of the later `fail`, a prophecy out of reach of any forward
   simulation. So provenance must be carried by `F`-blind *counts* (D14/`input_supp`), not
   by spec-side fills — the pool guards beat the fills.
7. **Eager binding junks the ghost (the ultra-lazy wall).** Even the lazy twin must not
   bind *between* rows. Rule 2's ghost is first-write-wins and rule 1's unconditional
   overwrite is dead once the twin binds; so if the twin binds early, a concrete
   `inputLoop` that answers `callABA id b̂` as a no-op while `id`'s input is uncommitted
   forces the bound twin onto rule 2, banking ghost `b̂`, and a later genuine
   `callABA id b` (`b ≠ b̂`) can never overwrite it — leaving `a.input id` permanently
   wrong. At `n = 4, f = 1`, mixed round-0 inputs force an eager bind, pre-emptive
   self-loops junk every future `b`-inputter, and a round-0 `retC` plus a `⊤`-coin flip
   develop an `A`-lock for `b` whose `f + 1` support is carried entirely by junked
   inputters — leaving rule 4's `hs` for `b` undischargeable. Hence the ultra-lazy
   two-phase twin: it never binds until the first return, so genuine banks always answer
   rule 1 and the ghost never diverges.
