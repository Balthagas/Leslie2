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
docstring for the 15-constructor table and deviations D9–D12 (0-based rounds, fused
DECIDED-send in `retW`/`stepRound`, single-slot DECIDED gossip).

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
  `agree_locked`, `grade_needs_bind`, `grade_A_src`, `decided_src`, `recv_sound`
  (delivery soundness; with `n − f > f` this yields an honest DECIDED source),
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
