# Design — the core simulation `hybridSpec ⊑ ABA.spec` (`coreSim`)

Companion design document to the Lean proof in `ABA/CoreSimRel.lean` (relation +
invariant), `ABA/CoreSimBurst.lean` (abstract τ-burst kit), and `ABA/CoreSim.lean`
(the per-row simulation proof). A condensed version is a candidate proof sketch of
`coreSim` for `blueprint/src/content.tex`.

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

## The relation: a lazy, never-flipping abstract twin

`coreRel := diracRel R₀` with `R₀ (g,(c,w)) a := Inv (g,c,w) ∧ Abs (g,c,w) a` — all
randomness couples outcome-to-outcome, so the abstract side stays Dirac.

Two ideas shape `Abs`:

1. **Laziness.** `ABA.spec`'s τ-rules are permissive (rule 7 fills calls at will
   when compatible with `val`; rules 3/4 rebind from filled calls), so the abstract
   twin does not mirror concrete progress step-by-step: it stays put on almost
   every concrete τ-row and catches up in explicit τ-**bursts** exactly at the few
   rows where a visible label or a forced `Abs`-field change requires it.
2. **The twin never flips its coin** (never fires rule 5). Rules 3/4 reset
   `coin := ⊥`, and `TVal.agrees (some u) ⊥` is false, so rule 7 is available at
   every post-bind moment (`val`-guard permitting). Consequently every concrete
   coin-flip row is a constant-coupled stutter
   (`ω := coinPMF.map (fun _ => pure a)`), and the abstract coin is *identically*
   `⊥` — recorded as the field `coin_bot`.

### `Abs` fields (`CoreSimRel.lean`)

- `F_eq : a.F = c.F`
- `ret_eq : a.ret id = (c.procs id).returned`
- `call_pre` — while unbound (`a.bind = none`), abstract calls equal the concrete
  write-once inputs: `a.call id = (c.procs id).input` (banked by answering rule 1
  at every `callABA` while unbound)
- `call_post` — once bound, `a.call = ⊥ⁿ` (bursts end in a rule-3/4 call reset)
- `coin_bot : a.coin = ⊥` (see above)
- `val_cert` — a permanent certificate: `a.val = some v` implies some round has an
  `A`-lock with bind `v` (`(g r).grade = some true ∧ (g r).bind = some v`)
- `bind_ready` — just-in-time readiness: while unbound, (1) no round is `C`-locked,
  and (2) every bound round's value `v` is the unanimous honest input, backed by an
  `f + 1`-strong input pool (`F`-insensitive count). Honest-input unanimity is
  asserted *only conditionally on a round being bound* — early mixed inputs simply
  bank via rule 1 and the abstract stays unbound.

Rationale for `bind_ready`: while the abstract is unbound, no honest dissent input
has ever been made (the binding policy below fires at the first one), so every
dissenting `g`-call entry was emitted by an already-corrupted process; hence no
`C`-lock can fire while unbound, all bound rounds carry the unanimous honest value
`v`, and `v`'s input pool (≥ n − 2f ≥ f + 1 inputters, counted `F`-insensitively)
always retains a currently-honest member to witness later quorums.

## Binding policy and row dispositions

Concrete steps are read through the step-inversion lemma for
`((A ∥ (B ∥ C)).abstract H).step`; each class is one row of `CoreSim.lean`:

| concrete row | label | abstract answer |
|---|---|---|
| `callABA id b`, unbound, `b` agrees with all honest inputs or nothing bound | `callABA id b` | rule 1 (bank; keeps `call_pre`), else rule 2 loop |
| `callABA id b`, unbound, `b` dissents from an honest input and a bound round exists | `callABA id b` | rule 1 then rule-4 burst in the τ-tail of the same `weakStep` (`bind := v₀`, `val` untouched; quorum from the fresh honest dissent + the `f + 1` pool) |
| `bindSet` (round 0, unbound, honest inputs unanimous) | τ | stutter (pool fact `n − 2f ≥ f + 1` banked) |
| `bindSet` (round 0, unbound, honest inputs mixed) | τ | rule-4 burst (quorum transfers from the fire-time guard; witnesses honest-now from the banked inputs) |
| `bindSet` (round ≥ 1 while unbound) | τ | stutter — est-provenance + no-`C`-locks + `bind_succ` force the new bind to equal the standing consensus |
| all hidden handshakes (`callG`/`retG`/`callW`/`retW`), DECIDED gossip τs | τ | stutter (`weakTau_refl`; only `Inv` moves) |
| **every** `WCC_r` coin flip | τ | constant-coupled stutter `ω := coinPMF.map (fun _ => pure a)` — the twin never flips |
| `retABA id b` | `retABA id b` | burst-then-rule-8 (`weakStep_of_burst_then_step`): if unbound, bind via rule 4 (mixed) or rule 3 (unanimous-`b`; `A`-lock certificate from the DECIDED source); then `fill_chain` all-`b` via rule 7 (`val ∈ {⊥, b}` by `val_cert` + `a_commit`), `val_force` sets `val := b`, rule 8 |
| `fail id` | `fail id` | rule 9, strong (same corrupt guard via `F_eq`; `bind_ready` is `F`-robust) |

## `Inv`: the concrete invariant (`CoreSimRel.lean`)

Grouped conjuncts (names as in the code):

- **F-lockstep**: `F_g`, `F_w` (every instance's `F` equals `c.F`), `F_card`.
- **Round structure**: `down_closed` (bound rounds are downward-closed),
  `quiescent` (cofinitely many rounds unbound), `round_bound`, `call_round`,
  `w_call_round`, `w_bound`/`w_called` (flips/W-calls only at bound rounds),
  `w_order` (rounds pass through flips in order), `round_flip`.
- **Input/est provenance**: `input_called`, `phase_input`, `est_ret`, `est_prev`,
  `est_prev_ne`, `call_prov`, `bind_succ` (a later bind's value has provenance in
  the previous round's bind/`C`-lock or dissent), `c_chain`.
- **Locks and DECIDED**: `a_commit` (an `A`-lock at bind `b` forces every later
  bound round to bind `b`, honest ests to `b`, honest DECIDEDs to `b`),
  `agree_locked`, `grade_needs_bind`, `grade_A_src`, `decided_src` (per pooled
  bit since D12′: an honest sender's pooled `b` carries an `A`-lock
  certificate), `recv_sound` (per-(receiver, sender, bit) delivery soundness,
  honesty-free since D12′ — sent pools only grow; with `n − f > f` the
  `retABA`-row pigeonhole still yields a never-corrupted DECIDED source of the
  returned bit even when corrupted equivocators pad the tally),
  `bound_quorum`.
- **Dissent bookkeeping**: `flip_alock` — a flipped round is graded or carries a
  `DissentResidue`, the permanent `F`-free residue of an honest-at-the-time
  dissent (with its `transport` lemma for frame-agnostic preservation),
  `retg_residue`, `wcalled_residue`, `idle_no_wcall`.

Each row of `CoreSim.lean` proves `Inv`-preservation for its step class and then
the `Abs`-level match above.

## The burst kit (`CoreSimBurst.lean`)

- `fill_chain` — from a bound `Abs`-state, a τ-chain of rule-7 fills reaching any
  target call vector compatible with `val` (iteration over `Fin n`).
- `rebind_mixed` / `rebind_unanim` — filled calls with a quorum reach a rule-4
  (resp. rule-3) rebind: `bind := b`, `call := ⊥ⁿ`, `val` untouched (resp. set,
  certified).
- `val_force` — `bind = some b`, `val ∈ {⊥, b}` ⇒ τ-chain to `val = some b`.
- `coin_reset_flip` — the coin-reset bookkeeping for post-rebind states.
- `weakStep_of_burst_then_step` — packaging: τ-burst then a visible step is a
  `weakStep`.

All assembled with `weakTau_of_step`/`weakTau_trans`; the probabilistic coupling
follows `toProbabilistic`'s pattern.

## Why this shape

Three adversarial-timing counterexamples force the design; they are worth
recording because each kills a natural simpler alternative.

1. **Eager functional abstraction fails.** If the abstract state is a total
   function of the concrete state (`a = absMap (g,c,w)`) with `a.bind`/`a.val`
   tied to the concrete bindSet row, abstract rule 3 (which also sets `val`) is
   forced the moment a round binds unanimously — but a *late joiner* can then
   submit a dissenting `callABA`, concretely enable a `C`-grade at that same round
   (dissent arrives before any return), steer the next round to bind the opposite
   value, `A`-lock it, and DECIDE against the already-committed abstract `val`.
   Hence the lazy twin: the abstract commits as late as possible and catches up in
   bursts.
2. **Flip-anchored abstraction fails.** Anchoring `a.bind` to the concrete flip
   frontier (largest flipped round) instead is also broken twice over: the honest
   witness backing the frontier round's rebind can be corrupted *before* the flip
   row (stranding the abstract quorum), and when the abstract coin happens to
   agree with its bind, rule 6 is the only available filler and can force a
   wrong-value `val`. Hence the never-flipping twin: with `coin_bot`, rule 7 is
   always available and rule-6/rule-5 timing issues vanish.
3. **Unconditional honest-unanimity fails.** Requiring pairwise agreement of
   honest inputs whenever the abstract is unbound is too strong: two opposite
   fresh inputs with nothing bound yet are perfectly reachable and would force a
   bind the quorum cannot support. Hence `bind_ready` conditions unanimity on a
   round actually being bound; early mixed inputs are just banked.

## D13: the Validity repair

The audit (`ABA/AUDIT.md` §2.1) shows TS 1 fails the papers' Validity: rule 7's
free re-propose (while `val = ⊥`) and rule 4's free mixed-bind lose input
provenance, so a bit input only by a later-corrupted process can win. The repair
principle: a value may circulate only with `f + 1` distinct supporters — at most
`f` processes are *ever* corrupted, so `f + 1` distinct supporters always include
a never-corrupted one, and provenance survives dynamic corruption with no
future-peeking guard (`3f < n` supplies `n − 2f ≥ f + 1`).

### The repaired TS 1 (exact deltas to `Spec.lean`)

- **Ghost** `input : Fin n → Option Bool` in `SpecState` (initial `fun _ => none`).
  Rule 1 records unconditionally: `input := Function.update s.input id (some b)`
  (write-once for free: pre-bind `call` is written only by rule 1 — rule 6 writes
  `none`, rule 7 is disabled since `coin = ⊥` and `TVal.agrees none ⊥` — and
  `call` is never cleared while `bind = none`, so rule 1 fires at most once per
  id). Rule 2 records first-write-wins:
  `input := if s.input id = none then Function.update s.input id (some b) else s.input`
  — sound (rule-2 events are genuine `callABA` trace events) and load-bearing:
  it is what lets an abstract twin mirror concrete inputs banked after the
  abstract binds (the rows it answers with rule 2). No honesty guards anywhere;
  all support counts are `F`-blind, which is exactly what makes them immune to
  later `fail`s.
- **Rule 4** gains
  `hs : P.f + 1 ≤ (Finset.univ.filter (fun id => s.call id = some b)).card`
  (support among ALL callers). Refuted en route: the quorum + `h1`/`h0` do *not*
  imply some bit has `f + 1` total callers (`n − 2f` honest callers can split as
  low as `⌈(f+1)/2⌉` per bit), so the guard genuinely shrinks enabledness — by
  design; spec liveness is unclaimed.
- **Rule 7**: `h₃` becomes
  `(s.val = none ∧ (s.input id = some b ∨ s.bind = some b)) ∨ s.val = some b`.
  Coin values are deliberately *not* licensed: `b = coin-bit` would resurrect the
  audit trace through a probability-ε flip.
- **New rule** `callByzFill` (τ):
  `(hF : id ∈ s.F) (h : s.call id = none) : call := Function.update s.call id (some b)`,
  no ghost record. Necessity: in TS 1 the only writers of `call` are rules 1/6/7
  (rules 3/4 clear; `corrupt` touches only `F`), so counting corrupt callers in
  `hs` is *sound* — but the concrete adversary fills GBCA call slots via hidden
  byz `callG` drivers with **no** `callABA` event, and without an abstract
  counterpart `hs` is undischargeable precisely on the validity-*satisfying*
  traces where byz phantoms complete the `f + 1` pool around one never-corrupted
  inputter. Byz entries are accounted by the `id ∈ F` disjunct below: the `F`
  budget, not the ghost, pays for them.
- Rules 3, 5, 6, 8, 9 unchanged. Rule 3 needs nothing: its quorum leaves
  `≥ n − f − f = n − 2f ≥ f + 1` *honest* callers, all of the decided bit.
  Rule 6 writes `bind`, which V-P1 already supports.

### The provenance invariant (extending `SpecSafety.SpecInv`)

`SuppOK s v := P.f + 1 ≤ #{id | s.input id = some v ∨ id ∈ s.F}` (monotone in
`F` and `input`, hence stable under `fail` and banking). New conjuncts:

- **V-P0** `s.bind = none → ∀ id b, s.call id = some b → s.input id = some b ∨ id ∈ s.F`
- **V-P1** `∀ v, s.bind = some v → SuppOK s v`
- **V-P2** `∀ v, s.val = some v → SuppOK s v`
- **V-P3** `∀ v, s.bind = some v → ∀ id b, s.call id = some b → s.input id = some b ∨ b = v ∨ id ∈ s.F`
  (post-`val`, `bind_val` collapses rule 7's `val`-branch writes into `b = v`).

Preservation: rules 1/2 grow `input` (all conjuncts monotone); rule 4 harvests
its `f + 1` callers through V-P0/V-P3 — each is an `input`-supporter, an
`F`-member, or carries `b = old bind` (then old V-P1 closes); rule 3 harvests its
`n − 2f ≥ f + 1` honest callers the same way (the `F` disjunct is vacuous for
them); rules 5/6/8 touch nothing relevant; `callByzFill` lands in the `id ∈ F`
disjuncts; rule 9 grows `F` (monotone). The audit trace now fails exactly at
`mixed (b := 1)`: `hs` demands 2 callers of `1` and only id 0 qualifies; the
rule-7 detour is also dead (only id 0 may re-propose `1`, and a `val := 1`
unanimity can never reach quorum from `|{0} ∪ F| ≤ 1 + f < n − f`).

Validity endgame (the budget pigeonhole): at any `retABA _ v`, V-P2 gives `f + 1`
supporters; if every `input`-supporter of `v` were ever-corrupted, all `f + 1`
supporters would lie in the final `F`, contradicting `|F| ≤ f`. So some supporter
is never corrupted and its recorded input is a genuine prior `callABA`.

Paper-form target (`fail` is total under D1, so *fail-event presence* is the
wrong notion — no-op fails can name more than `f` ids; refuted by: supporters
`{0,1}`, `fail 0` effective, `fail 1` a no-op at budget): define
`failSet t k : Finset (Fin n)` as the fold of D1-`corrupt` over the first `k`
labels (it provably equals the reachable state's `F`), and
`NeverCorrupted t id := ∀ k, id ∉ failSet t k`. Then

```
ValidityTraceP t := ∀ m id b, t m = retABA id b →
  ∃ k < m, ∃ id', t k = callABA id' b ∧ NeverCorrupted t id'
```

— returner-unconditional (stronger than the paper, like `AgreementTrace`), and
the "no `fail id` event" phrasing survives only as a hypothesis-side corollary.
`ValInv`'s call-attribution must except `F`-members (byz fills have no event).

### The gate: CoreSim feasibility — NO-GO as scoped

Adjudication of every abstract rule-4/7 use by the lazy twin:

| twin use | new obligation | verdict / supplier |
|---|---|---|
| `bindSet`-mixed burst (`SpecStep.mixed`, `b` = concrete bind) | `hs`: `f+1` abstract callers of `b`; abstract `call` = banked inputs (`call_pre`) | **not dischargeable**: TS 2's `bindSet` certifies a *single* honest witness (`hw`) for `b` |
| `callABA`-dissent burst (`SpecStep.mixed`, `b` = fresh dissent bit) | `hs` for `b` | not dischargeable for `b`; **dischargeable after a delta**: bind the standing pool value `v` instead — `bind_ready`'s `f+1` input pool + `call_pre` supply `hs`, and `h1`/`h0` survive (fresh honest dissent + a currently-honest pool member by `|F| ≤ f`) |
| `retABA`-unbound (rule 3 + rule 8) | none new | dischargeable (guards unchanged) |
| `retABA`-bound (`val_force'`: rule-7 fill of `b` with `a.bind = some vb`, `vb` unpinned) | per-id `input id = some b ∨ bind = some b ∨ val = some b` | `val = some b` branch fine (`val_cert` + `commit_up`); `val = ⊥ ∧ vb ≠ b` **not dischargeable** — nothing pins `a.bind`'s value and a fill needs all `n` ids licensed |
| ghost mirror at rules 1/2 | `a.input = concrete banked inputs` | free, *given* rule-2 recording and a new `Abs` conjunct `input_eq : ∀ id, a.input id = (c.procs id).input` (`call_pre` alone dies at `a.bind ≠ none`) |

No local (`Inv`/`Abs`) strengthening fixes the two failing rows, because
`hybridSpec` itself violates paper-Validity — refinement into any Validity-sound
spec is impossible. Witness (deterministic; both WCC flips are outcome-
irrelevant), `n = 4`, `f = 1`: inputs `1,0,0,0`; GBCA₀ calls mirror them;
`bindSet b := 1` off the single honest witness id 0; ids 1–3 `retB` (singular
dissent witness id 1) and adopt `est := 1` (B keeps `est` through `retW`);
round 1: ids 1–3 call `1`, bind `1`, `retA`, DECIDED `1`, `n − f` receipts;
`fail 0`; `retABA 1 1`. Never-corrupted = `{1,2,3}`, all inputs `0`. The repaired
spec can never emit these visible labels (bit `1` has one supporter), and forward
simulation preserves visible traces. Root cause: TS 2's `bindSet` witness and
`retB`/`retC` dissent are *singular* — the same provenance loss one level down
(ABDY22's implementation has the `f + 1` via Valid-set relay thresholds; TS 2
abstracted it to one witness). A second, probabilistic channel does the same
through `retC` + WCC `⊤` free adoption.

Scope of the actual repair (recorded for V-next, not softened): (1) TS 1 as
above; (2) TS 2: `bindSet`'s `hw` → `f + 1 ≤ #{id | call id = some b}`,
`retB`/`retC`'s `hw` → the same for `!v` (F-blind; GBCA.Impl's relay threshold
should re-close `GBCASim`, to be re-proven); (3) new `Inv` conjuncts
`bind_supp : (g r).bind = some v → f + 1 ≤ #{id | (g r).call id = some v}` and
its C-lock dissent twin — both permanent and `F`-free, likely subsuming much of
the `DissentResidue` transport machinery — bottoming at `input_g0`; (4) new
`Abs` conjuncts `input_eq`, byz-call banking (abstract `callByzFill` mirrors
hidden byz `callG`), and `ret_support` (an A-lock at bind `b` yields `f + 1`
abstract call/byz-fill material for `b`); (5) `CoreSim` deltas: the dissent
burst binds the pool value, and the `retABA`-bound row rebinds to `b` via
byz-fill/input-branch fills + rule 4 instead of `val_force'`. With (1)–(5) every
row of the table has a named supplier; without (2), no design does.

## D15: V2a′ finding — fill-only byz fills cannot be value-pinned (GBCASim wall)

Attempting the recorded item-4/5 repair (D14 guards + `byzFill` + disjunctive
`call_eq` + eager fills) hits a genuine wall at the `bindGhost` row: the
obligation `bindSet.hw : f + 1 ≤ #{id | t.call id = some b}` is
**undischargeable** by any forward simulation whose relation makes honest
(`∉ F`) spec slots mirror the genuine inputs — and the quorum and dissent
harvests (`quorum_of_vote_quorum`, `retB`/`retC`) force exactly that (at
`f = 0` any honest slot left empty breaks the spec quorum outright).

**Witness W1 (pre-corruption call; kills every fill-only design).**
`n = 4, f = 1`: `callG 3 0` (genuine mirror forced: slot 3 := `0`),
`fail 3`, `byz 3 (INPUT 1)`, `callG 0 1`, `callG 1 0`, `callG 2 0`;
deliver `INPUT 1` from `{0,3}` to 1, 2 → both `relay 1` (`f+1 = 2`
receipts); now 4 `INPUT 1` senders → echoes/votes/`BIND 1` at 0 →
`bindGhost 1`, and later visible `retA 0 1`. Related spec state:
`call = [1,0,0,0]`, `F = {3}` (budget full), `#callers(1) = 1 < 2`; no τ
helps — `byzFill` needs an *empty* `F` slot and slot 3 is genuinely full.

**Witness W2 (byz double-send; kills value-pinned eager fills).** `3 ∈ F`
from the start sends `INPUT 0` then `INPUT 1`: the single-write slot is
eagerly filled `0`, and the same amplification of bit `1` follows. (W2 alone
is dodged by lazy fills + `callLoop`-answering calls to already-corrupted
ids; W1 is not dodged by anything fill-only.) The gap in the item-5 site
decomposition is twofold: honest *relayers* of `b` are not genuine holders
of `b`, and filled `F` slots are not necessarily filled *with* `b`.

**Not a soundness gap.** The spec emits W1's visible trace via a different
run: answer `callG 3 0` with `callLoop`, insert `byzFill 3 1` after
`fail 3`, then `bindSet 1` (`callers(1) = {0,3}`). The choice needs
knowledge of the later `fail` — a prophecy/backward-simulation situation,
out of reach of any forward simulation.

### Repair candidates (recorded, not implemented — designer's call)

- **R1 (recommended): guards in SuppOK form.** `bindSet.hw` (and the
  `retB`/`retC` twins for `!v`) become
  `f + 1 ≤ #{id | call id = some b ∨ id ∈ F}` — exactly TS 1's `SuppOK`
  shape (D13). Validity pigeonhole survives verbatim: `F` is monotone and
  `|F_final| ≤ f`, so some member of the `f + 1` is outside `F_final`,
  hence outside `F_now`, hence a never-corrupted genuine caller. Then
  `call_eq` stays **exact**, no fills, no byz mirror rows, `instRel_corrupt`
  untouched; `byzFill` becomes unused (harmless). Impl side: one new `Inv`
  conjunct, the relayer-inductivized first-relayer argument
  `input_supp : ∀ b j, j ∉ F → Msg.input b ∈ sent j →
  (proc j).input = some b ∨ f + 1 ≤ #{id | (proc id).input = some b ∨ id ∈ F}`
  (preservation checked: `call` adds a holder; `relay`'s `f + 1` receipt
  senders are each in `F`, a holder, or a prior honest non-holder sender —
  the pre-state conjunct closes; `byz` senders are in `F`; `fail` grows the
  count and shrinks the triggers; the count is monotone throughout). Harvest
  lemma: an `n − f` `INPUT b` sent-quorum yields the count (some honest
  non-holder sender → conjunct; else all senders are `F`-or-holders and
  `n − f ≥ f + 1`). All three sites discharge through `call_eq`/`F_eq`.
- **R2: `byzFill` → `byzSet` overwrite** (`id ∈ F → call id := some b`,
  slot full or not). Keeps the D14 guard form; each site is answered by a
  `byzSet` burst re-pointing `F` slots to the harvest bit; needs a
  `t`-dependent `InstRel` count conjunct and burst machinery. Post-burst
  the count *equals* R1's `∨ id ∈ F` count — R2 is R1 with state surgery;
  strictly heavier, and corrupted slots lose single-write meaning.

Both change the spec (R1 weakens the guard predicate, R2 adds adversary
power), which V2a′ was told not to do unilaterally: stopped at the green
Stage-1 commit (`byzFill` landed, sound, currently unused). `GBCASim`,
`GBCAFamily`, `Hybrid` remained red pending the decision; `SpecSafety` green.

**Resolution (V2a″): R1 implemented.** `GBCASpec`'s three guards are the
SuppOK counts and `byzFill` is removed; `GBCASim` carries `Inv.input_supp`
exactly as recorded (preservation as checked above — the relay case closes
through `Inv.supp_of_input_receipts`, the same harvest that answers all
three sites: `suppI_of_bind` chases `BIND → VOTE → ECHO` to an honest
`ECHO b` sender's `n − f` `INPUT b` receipts, and `retB`/`retC`'s dissent
bit is covered by `bothValid`'s own `n − f` `INPUT (!v)` receipt quorum at
the returner — no separate dissent-relay argument needed). `call_eq` exact,
`instRel_corrupt` untouched. Green: `GBCASpec`, `SpecSafety`, `GBCAImpl`,
`GBCASim`, `GBCAFamily`, `Hybrid`, `Examples` (the D14 witness satisfies
the superset count). Red for V2b as scoped: `CoreSimRel`, `CoreSimBurst`,
`CoreSim`, `Main`.

## D16: V2b — the eager twin is unhealable; the ultra-lazy twin

Healing V0's CoreSim against the D13/D15-R1 specs surfaced a wall *behind* the
D13 gate table: the eager-binding twin (bursts at `bindSet`-mixed and
`callABA`-dissent, `bind_ready` discipline) cannot discharge the repaired
`retABA` row at all — its row-5 "ghost mirror is free" verdict is wrong.

**The junk witness.** Rule 2's ghost record is first-write-wins, and rule 1
(unconditional overwrite) is dead once the twin binds. The concrete `inputLoop`
answers `callABA id b̂` as a no-op even while `id`'s input is uncommitted, and
the twin — bound, so forced onto rule 2 — must bank ghost `b̂`. A later genuine
`callABA id b` (`b ≠ b̂`, still bound → rule 2 keeps `b̂`) leaves
`a.input id = b̂` against concrete input `b` *permanently*. Adversary schedule
(n = 4, f = 1): mixed round-0 inputs force the eager twin to bind at `bindSet₀`;
pre-emptive self-loops junk every future `b`-inputter; a round-0 `retC` plus a
`⊤`-coin flip develop an A-lock for `b` whose f+1 support is carried entirely by
post-bind (junked) inputters — the twin has at most `|F| ≤ f` fillable slots for
`b` and rule 4's `hs` for `b` is undischargeable. (The spec emits the trace by
answering the *first* self-loop event with rule 2 and the genuine one with
rule 1 — a prophecy choice, the W1 shape one level up.)

**Resolution: the ultra-lazy twin (implemented).** The twin never binds between
rows. `Abs` is a two-phase invariant keyed on `a.val`: phase 1 (pre-first-
return) — `bind = val = ⊥`, `a.call` = the concrete write-once inputs, and
ghost synced on every *committed* input (genuine banks always answer rule 1
while unbound, whose unconditional overwrite erases junk-pending ghosts);
phase 2 (post-first-return) — `bind = val = some v` with a permanent concrete
A-lock certificate, board clear. Consequences: every hidden row stutters
(`Abs.frame` subsumes all six Stage-C lemmas), `bind_ready` and the
`bindSet`/`callABA` bursts are gone, and the whole burst load concentrates in
the phase-1 `retABA` answer (`decide_burst`): (i) no honest dissent from the
returned bit `b` → rule 3 outright; (ii) else byz-fill empty `F`-slots with the
majority bit `v'` (the quorum pigeonholes `n − f ≥ 2f + 1` callers-or-`F` onto
two bits) and rule-4 rebind to `v'` — **clearing the board**, which is what
makes every `F`-slot fillable afterwards (the D15-W1 objection to fill-only
designs does not apply to TS 1: rules 3/4 reset `call`); (iii) fill the
`f + 1` material for `b` (ghost/byz branches; supplied by the new concrete pool
`Inv.bind_supp` at the A-locked round, transferred through phase 1's call/ghost
sync) plus bind-branch `v'`s, rule-4 rebind to `b` (rule 3 if all-material);
(iv) `val_force` (all-`b` bind-branch fill + rule 3), rule 8. Phase-2 `retABA`
is rule 8 directly (`commit_up` pins `b`); `callABA` is rule 1 (phase 1,
genuine) or rule 2 (everything else).

**New `Inv` conjuncts** (established at `bindSet`/`retC` from the D15-R1 count
guards; permanent, monotone): `bind_supp` (I26) — every bound round's value has
`f + 1` input-or-`F` support (`InputSupp`, TS 1's V-P1 shape one level down) —
and `clock_supp` (I27), its C-lock dissent twin; round 0 transfers wholesale via
`input_g0_perm`, `r ≥ 1` recurses through `call_prov` into the previous round's
pools (`Inv.supp_of_call_count`). The D15-R1 guard inversions elsewhere harvest
an in-state honest witness via `GBCA.exists_honest_caller` (count + `|F| ≤ f`).

Supersedes: the `Abs` field list, the binding-policy row table, and the burst
inventory in the sections above (historical record of V0); `Inv` is unchanged
except for I26/I27. Green: full `Leslie2Protocols`, `Main` guards unchanged
(`[propext, Classical.choice, Quot.sound]`).

## D12′: closing the DECIDED equivocation gap (AUDIT finding #4)

The original D12 modeled DECIDED gossip as a single per-process slot
(`decidedSent : Option Bool`, `byzDecided` filling only an *empty* slot,
delivery at most once per (receiver, sender) edge). That adversary cannot send
`DECIDED 0` to X and `DECIDED 1` to Y — an under-approximation, and
inconsistent with the GBCA layer's D5 sent-pool (which does equivocate).

**Model (Core.lean).** Mirror D5 at the DECIDED layer:
`decidedSent : Fin n → Finset Bool` and
`decidedRecv : Fin n → Fin n → Finset Bool` (pools). `sendDecided` inserts
(pools only grow); `deliver` is per (receiver, sender, bit) with soundness
`b ∈ decidedSent j` and at-most-once guard `b ∉ decidedRecv i j`;
`byzDecided` is guarded *only* by `id ∈ F` — a corrupted process may pool
either or both bits at any time, delivered selectively. `echo` keeps the
paper's "not having multicast" as `decidedSent id = ∅`; `ret` keeps "having
multicast ⟨DECIDED, b⟩" as `b ∈ decidedSent id`; `decidedCount` counts
distinct senders per bit, unchanged in spirit. Honest pools stay at card ≤ 1
in reachable states (all A-grade certificates pin one bit via
`grade_A_src` + `a_commit`), but no card invariant is needed anywhere.

**Invariant rewiring (CoreSimRel.lean).** `recv_sound` becomes per-bit and
*honesty-free* (`b ∈ decidedRecv i j → b ∈ decidedSent j` — preserved by pure
monotonicity since sent pools never shrink; the old form needed `j ∉ F`
against slot overwrites). `decided_src` becomes per pooled bit
(`id ∉ F → b ∈ decidedSent id → ∃ r` A-lock cert for `b`): this is the
equivocation-robust form — corrupted equivocators may pad any bit's tally,
but the `retABA`-row pigeonhole (`n − f` distinct senders of `b`, `|F| ≤ f`,
`n − f > f`) recovers a never-corrupted sender of `b`, whose pooled `b`
carries the A-lock certificate feeding `decide_burst` exactly as before.
Preservation: `byzDecided` rows are vacuous at the corrupted sender and
monotone elsewhere; the `echo`/`retW`-A-send rows extend the pool by a
certified bit (pigeonhole resp. `grade_A_src`). The `retW` `recv_sound` row
*simplified* (the old overwrite argument via `a_commit` dropped to
`mem_insert_of_mem`). DECIDED gossip rows stay τ-stutters; the unguarded
`byzDecided` is the same stutter case with one fewer hypothesis. `Abs`, the
burst kit, `Examples`, and `Main` needed no repair beyond the two inversion
destructurings. Green: full `Leslie2Protocols`, `Main` guards unchanged
(`[propext, Classical.choice, Quot.sound]`).
