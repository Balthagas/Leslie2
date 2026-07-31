# Design — the per-instance GBCA refinement `GBCA.implInst ⊑ GBCA.specInst` (`implRefines`)

Companion design document to the Lean proof in `ABA/GBCASim.lean` (relation,
invariant, burst lemmas, per-row simulation), against the implementation shape
in `ABA/GBCAImpl.lean` (deviation D18: the full six-level message ladder of
ABDY22's Algorithm 6) and the specification shape in `ABA/GBCASpec.lean`
(deviation D19: the exclusion set `dead : Finset Bool` in place of a bound
value). The refinement paragraphs of `blueprint/src/content.tex` — the kill
certificate, the `VOTE` wall, and the two-step kill-then-return burst — are a
condensation of this document.

## Systems

```
implInst P r : System (ImplState P.n) (Lab P.n)     -- ABDY22 Algorithm 6, D1/D5/D8/D18
specInst P r : System (SpecState P.n) (Lab P.n)     -- graded-binding spec, D1/D14/D15/D19
target       : ForwardSimulation (implInst P r) (specInst P r) (instRel P r)
```

Both systems are Dirac-transition LTSs. The instance refinement reaches the
ℕ-indexed families through the round subsystem (`ABA/GBCASub.lean`), whose
family lifting takes its broadcast ingredient from
`GBCAFamily.instRel_corrupt`.

### The implementation (D18): the six-level ladder

The implementation transcribes ABDY22's Algorithm 6. The message type is

```lean
inductive Msg : Type
  | input (b : Bool)         -- ⟨echo,  b⟩ of Algorithm 6
  | echo  (b : Bool)         -- ⟨echo2, b⟩
  | vote  (v : Option Bool)  -- ⟨echo3, v⟩,  v ∈ {0, 1, ⊥}
  | bind  (v : Option Bool)  -- ⟨echo4, v⟩
  | seal  (v : Option Bool)  -- ⟨echo5, v⟩
```

and `ProcState` carries one write-once slot per level above `INPUT`:
`sentEcho : Option Bool`, `sentVote sentBind sentSeal : Option (Option Bool)`,
next to `input`, `sentInput : Bool → Bool` and `returned`. `ImplState` is the
per-process states, the D5 set-based network (`sent`, `recv`) and the
corrupted set `F`. Derived counts: `recvCount i m` (distinct senders of the
exact message `m` delivered to `i`), `echoCount`/`voteCount`/`bindCount`/
`sealCount i` (distinct senders of *any* payload at that level), and
`bothValid P s i` (an `n − f` `INPUT b` receipt quorum at `i` for **each**
bit — Algorithm 6's `|approvedVals| > 1`).

The rules, all τ except the labelled API rows (D8 participation gating
`input ≠ none` on every protocol send, including the seal level):

* `call` / `callLoop` — record the input, multicast `INPUT b` / input-enabled
  self-loop;
* `deliver` — adversarial move of a sent message into a `recv` cell;
* `relay` — `f + 1` `INPUT b` receipts, re-multicast `INPUT b` (amplification);
* `echo` — `n − f` `INPUT b` receipts, multicast `ECHO b` (write-once);
* `voteBit` — `n − f` `ECHO b` receipts, multicast `VOTE b` (write-once);
* `voteBot` — `n − f` any-`ECHO` receipts and `bothValid`, multicast `VOTE ⊥`;
* `bindBit` — `n − f` `VOTE b` receipts, multicast `BIND b` (write-once);
* `bindBot` — `n − f` any-`VOTE` receipts and `bothValid`, multicast `BIND ⊥`;
* `sealBit` — `n − f` `BIND b` receipts, multicast `SEAL b` (write-once);
* `sealBot` — `n − f` any-`BIND` receipts and `bothValid`, multicast `SEAL ⊥`;
* `byz` — a corrupted sender multicasts anything;
* `retA id v` — an `n − f` `SEAL v` receipt quorum (grade 2);
* `retB id v` — `n − f` any-`SEAL` receipts, at least one `SEAL v` receipt,
  **`f + 1` `BIND v` receipts**, and `bothValid` (grade 1 — Algorithm 6's
  line-25 condition: the `t + 1` `echo4` check is what puts an honest `BIND v`
  behind every grade-1 output);
* `retC id` — an `n − f` `SEAL ⊥` receipt quorum and `bothValid` (grade 0);
* `fail` — D1 determinised corruption.

The load-bearing depth of the return evidence: **every grade-≥1 output names a
bit with an honest `BIND` behind it** — `retA` via `n − f` `SEAL v` →
honest sealer → `n − f` `BIND v` receipts → honest binder; `retB` via
`f + 1 > |F|` `BIND v` receipts directly — and an honest `BIND v` sits on an
`n − f` `VOTE v` receipt quorum. The `VOTE` level is write-once, so that
quorum is the object the binding argument counts (paper Lemmas 4.8/4.9 through
E.9).

### The specification (D19): the exclusion set

`SpecState` is `call : Fin n → Option Bool`, `ret : Fin n → Bool`,
`dead : Finset Bool`, `grade : Option Bool`, `F : Finset (Fin n)`; initially
`dead = ∅`. Binding is *negative* information: `dead` is the set of bits the
instance can no longer hand out. The rules:

* `call` / `callLoop` — as in every instance spec (D15 file conventions);
* `bindUnset b` (τ) — guards `s.quorum P`,
  `f + 1 ≤ #{id | s.call id = some (!b) ∨ id ∈ s.F}` (the D15 SuppOK count,
  at the *surviving* bit `!b`), and `hd0 : s.dead = ∅`; effect
  `dead := insert b s.dead`;
* `retA id v` — guards `v ∉ s.dead`, `(!v) ∈ s.dead`,
  `s.grade = none ∨ s.grade = some true`, `s.ret id = false`; effect
  `grade := some true`, mark returned;
* `retB id v` — guards `v ∉ s.dead`, `(!v) ∈ s.dead`, the D15 dissent count
  `f + 1 ≤ #{id' | s.call id' = some (!v) ∨ id' ∈ s.F}`, `s.ret id = false`;
  effect: mark returned;
* `retC id` — guards `1 ≤ s.dead.card`, the two D15 counts (one per bit),
  `s.grade = none ∨ s.grade = some false`, `s.ret id = false`; effect
  `grade := some false`, mark returned;
* `fail` — D1 corruption, `dead` untouched.

The `hd0` guard admits `bindUnset` from the empty set only, so an instance kills
at most once and every reachable state has `dead ∈ {∅, {b}}`
(`GBCASafety.dead_card_le_one`). The once-only kill is also what keeps a round
completable: after an `A`-return a second kill would leave no live bit for the
value-bearing returns while the A-latch blocks `retC`, stranding the processes
yet to return.

`dead` is monotone (only `bindUnset` writes it, by `insert`), so the graded
binding property is structural: a killed bit is never handed out (`v ∉ dead`
guards both value-bearing returns), every `A`/`B`-return pins `(!v) ∈ dead`
whence any two value-bearing returns agree on the surviving bit, and a
`C`-return forces `dead ≠ ∅` permanently — from that moment at most one bit is
ever alive, which is the paper's Binding. Provenance (D14/D15) is carried by
`bindUnset`'s SuppOK count for the surviving bit: a bit `v` handed out at
grade ≥ 1 requires `(!v) ∈ dead`, whose `bindUnset (!v)` certified `f + 1`
F-blind callers of `v`; the budget pigeonhole (`|F| ≤ f` forever) recovers a
never-corrupted genuine caller of `v`.

## The relation

```lean
structure InstRel (P : Params) (s : ImplState P.n) (t : SpecState P.n) : Prop where
  inv       : Inv P s
  call_eq   : ∀ id, t.call id = (s.proc id).input
  ret_eq    : ∀ id, t.ret id = (s.proc id).returned
  F_eq      : t.F = s.F
  dead_cert : ∀ b, b ∈ t.dead → DeadCert P s b
  gradeA_ev : t.grade = some true  → ∃ v i, P.n - P.f ≤ s.recvCount i (.seal (some v))
  gradeC_ev : t.grade = some false → ∃ i,   P.n - P.f ≤ s.recvCount i (.seal none)
```

`call_eq`/`ret_eq`/`F_eq` are the exact abstraction rows, identical in shape
to every other instance relation of the development. `gradeA_ev`/`gradeC_ev`
are the A/C-exclusivity certificates, read at the `SEAL` level (the level the
returns read): two opposing `n − f` `SEAL` quorums intersect in an honest
process with two different `SEAL` payloads, contradicting the write-once
`seal_once` — which is what discharges the spec's grade latches.

`dead_cert` is the load-bearing novelty: the spec's `dead` is bookkeeping the
protocol never stores, so the relation carries a receipt-pattern *kill
certificate* for every dead bit. Note the direction — the relation bounds
`dead` from above (`dead ⊆ {b | DeadCert P s b}`) and never from below; which
bits are actually in `dead` is recovered by case analysis at the return rows,
not stored.

## The kill certificates

```lean
/-- Case A: the opposite bit owns the (unique) `n − f` `ECHO` receipt
quorum. -/
def EchoQuorum (P : Params) (s : ImplState P.n) (v : Bool) : Prop :=
  ∃ i, P.n - P.f ≤ s.recvCount i (.echo v)

/-- Case B: an `n − f` wall of processes each of which is corrupted or has
committed its write-once `VOTE` slot to a payload other than `some b`. -/
def VoteWall (P : Params) (s : ImplState P.n) (b : Bool) : Prop :=
  P.n - P.f ≤ (Finset.univ.filter
    (fun j => j ∈ s.F ∨ ∃ w, (s.proc j).sentVote = some w ∧ w ≠ some b)).card

/-- The kill certificate licensing `b ∈ dead` on the specification side. -/
def DeadCert (P : Params) (s : ImplState P.n) (b : Bool) : Prop :=
  EchoQuorum P s (!b) ∨ VoteWall P s b
```

Both disjuncts kill `b` by making an `n − f` `VOTE b` receipt quorum — the
sole gateway to any grade-≥1 evidence for `b` — impossible forever:

* **Case A** (`EchoQuorum P s (!b)`). Any `VOTE b` quorum contains an honest
  `VOTE b` sender (`n − f > f ≥ |F|`), whose `vote_conf` receipt quorum is an
  `n − f` `ECHO b` quorum; two same-level `n − f` quorums for different bits
  share an honest sender (`exists_honest_recv₂`, `(n−f)+(n−f)−n > f`) that
  multicast two `ECHO` payloads, contradicting the write-once `echo_once`.
  This is `echoQuorum_unique`.
* **Case B** (`VoteWall P s b`). Any later `n − f` `VOTE b` quorum `Q` has all
  its non-`F` members committed to `sentVote = some (some b)` (`recv_sub` +
  `vote_once`), so `Q` meets the wall `D` only inside `F`:
  `|Q| + |D| ≤ n + |Q ∩ D| ≤ n + f`, i.e. `2(n − f) ≤ n + f`, i.e. `n ≤ 3f` —
  against `P.hf`. The wall is the state-predicate form of the paper's
  Lemma 4.9 pinning count ("`n − f` receipts pin `≥ n − f − |F|` honest
  committed voters, leaving `≤ f < n − 2f` free honest votes").

The three certificate obligations:

**(i) Monotonicity.** Receipts only grow (`deliver`), `sentVote` is
write-once and never unset (guard `sentVote = none` on `voteBit`/`voteBot`,
no rule clears it), and `F` only grows (`fail`); every other rule touches
neither `recv`, `sentVote` nor `F`. Packaged as

```lean
theorem DeadCert.mono {s s' : ImplState P.n} {b : Bool}
    (hrecv : ∀ i j m, m ∈ s.recv i j → m ∈ s'.recv i j)
    (hvote : ∀ j w, (s.proc j).sentVote = some w → (s'.proc j).sentVote = some w)
    (hF : s.F ⊆ s'.F) : DeadCert P s b → DeadCert P s' b
```

applied per row exactly like `ImplSupp.mono`. This is
what keeps `dead_cert` a stutter-stable field: `dead` never shrinks and the
certificates never expire.

**(ii) Availability at the kill moments.** The simulation fires `bindUnset`
only inside return bursts, and each return's own evidence yields the needed
certificate:

```lean
/-- Any `n − f` `VOTE v` receipt quorum kills the opposite bit … -/
theorem deadCert_of_voteQuorum (hI : Inv P s) {i v}
    (h : P.n - P.f ≤ s.recvCount i (.vote (some v))) : DeadCert P s (!v)

/-- … and certifies that `v` itself is alive. -/
theorem not_deadCert_of_voteQuorum (hI : Inv P s) {i v}
    (h : P.n - P.f ≤ s.recvCount i (.vote (some v))) : ¬ DeadCert P s v
```

`deadCert_of_voteQuorum` lands in `VoteWall (!v)` — the quorum's members are
each in `F` or committed to `some v ≠ some (!v)`, so the quorum itself is the
wall. `not_deadCert_of_voteQuorum` is the two Case A/B refutations above.
Both value-bearing returns route into a `VOTE` quorum by the harvest chain

```lean
theorem voteQuorum_of_bind_receipts (hI : Inv P s) {i v}
    (h : P.f + 1 ≤ s.recvCount i (.bind (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.recvCount k (.vote (some v))

theorem bind_receipts_of_seal_quorum (hI : Inv P s) {i v}
    (h : P.n - P.f ≤ s.recvCount i (.seal (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.recvCount k (.bind (some v))
```

(`retA`: seal quorum → honest sealer → `seal_conf`; then `n − f ≥ f + 1` and
the first chain: bind receipts → honest binder (`f + 1 > |F|`) → `bind_conf`.
`retB`: its `f + 1` `BIND v` receipts enter the first chain directly.) The
`C`-return has no distinguished bit; its evidence yields a certificate for
*some* bit:

```lean
theorem deadCert_of_sealBot_quorum (hI : Inv P s) {i}
    (h : P.n - P.f ≤ s.recvCount i (.seal none)) : ∃ b, DeadCert P s b
```

Proof shape (this is the sketch's Case A/Case B dichotomy, formalised): the
quorum contains an honest `SEAL ⊥` sender `p` (`n − f > f`); `sealBot_conf`
gives `n − f ≤ s.bindCount p`, so `p` holds an honest any-payload `BIND`
sender `k`. Classical case split on `∃ m b', m ∉ s.F ∧ Msg.vote (some b') ∈
s.sent m` (an honest bit-voter exists somewhere):

* **yes** — `vote_conf` at `m` is an `n − f` `ECHO b'` quorum, so
  `EchoQuorum P s b'` and `DeadCert P s (!b')` by Case A;
* **no** — then `k` cannot have sent `BIND (some v')` (its `bind_conf`
  `VOTE v'` quorum would contain an honest bit-voter), so `k` sent `BIND ⊥`
  and `bindBot_conf` gives `n − f ≤ s.voteCount k`: every non-`F` sender in
  that quorum committed a vote (`vote_once`) that is not a bit (no honest
  bit-voter exists), i.e. `sentVote = some none ≠ some (some b)` for **both**
  bits — `VoteWall` holds for both bits, `DeadCert` for either.

**(iii) The `bindUnset` guards are discharged.** `bindUnset b` needs the
quorum guard and `f + 1` F-blind caller support for `!b`. At a value-bearing
return of `v` (killing `b = !v`, support bit `!(!v) = v`), both come from one
`ECHO` certificate:

```lean
theorem bindUnset_guards (hR : InstRel P s t) {v} (hq : EchoQuorum P s v) :
    t.quorum P ∧ P.f + 1 ≤ (Finset.univ.filter
      (fun id => t.call id = some v ∨ id ∈ t.F)).card
```

— refine the `ECHO v` quorum to an `n − f` `INPUT v` receipt quorum
(`inputQuorum_of_echoQuorum`), whose honest senders hold an input
(`input_called`, D8): that is the quorum guard (`quorum_of_msg_quorum`), and
its count feeds `Inv.supp_of_input_receipts` → `InstRel.spec_supp` for the
SuppOK count. The `EchoQuorum v` input is supplied by
`echoQuorum_of_vote_receipts` off the harvested `VOTE v` quorum
(`n − f ≥ f + 1`). At the `C`-return (killing an arbitrary certified `b*`,
support bit `!b*`), both guards come instead from the returner's own
`bothValid`: the per-bit `n − f` `INPUT` receipt quorum gives the quorum guard
through `quorum_of_msg_quorum`/`input_called`, and `suppI_of_valid` gives the
`f + 1` count for **either** bit — so the guard is available no matter which
bit the certificate names.

### Case A / Case B as named invariants

The soundness fact "the surviving bit at any C-return is determined by prefix
receipts" is not a lemma of the simulation file; it is the conjunction of the
certificate properties above, and it is what makes a *plain forward*
simulation sufficient (no prophecy): at every moment the simulation must
commit a kill, the impl state already contains a monotone certificate naming
the killed bit, and no extension ever produces return evidence for a certified
bit (`not_deadCert_of_voteQuorum` against `DeadCert.mono`). The two named
carriers:

* **Case A** — `deadCert_of_voteQuorum` (an honest `VOTE v`, equivalently an
  `ECHO v` quorum, kills `!v` forever): quorum intersection on the write-once
  `ECHO` level.
* **Case B** — the **no**-branch of `deadCert_of_sealBot_quorum` (a
  `C`-return over an all-⊥ honest vote prefix kills both bits): the
  `VoteWall` counting on the write-once `VOTE` level.

## Kill scheduling and burst shapes

The specification kills by an internal τ-transition, so an implementation
return that needs a not-yet-dead bit killed is answered by a two-step weak
burst through `weakLStep_tauThen`. Unlike a bound-value
design there is no "first return" phase distinction: **every** return row does
the same decidable case split on the spec's `dead`, and the burst is enabled
whenever the kill is missing, regardless of how many returns happened before.
Every burst carries `hd0 : t.dead = ∅`, the `bindUnset` guard:

```lean
/-- `bindUnset (!v) ; retA v` from an all-alive state (`dead = ∅`). -/
theorem killThenRetA_burst {r t id v}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some v ∨ k ∈ t.F)).card)
    (hlive : v ∉ t.dead) (hd0 : t.dead = ∅)
    (hg : t.grade = none ∨ t.grade = some true) (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id (.A v))
      { t with dead := insert (!v) t.dead, grade := some true,
               ret := Function.update t.ret id true }
```

(the `bindUnset (!v)` support guard reads `some (!(!v))`; `Bool.not_not`
rewrites it to `hw`'s `some v`, and `retA`'s `v ∉ insert (!v) t.dead` follows
from `hlive` and `v ≠ !v`). `killThenRetB_burst` is the same with the dissent
count `f + 1 ≤ #{k | t.call k = some (!v) ∨ k ∈ t.F}` in place of the grade
latch, landing in `{ t with dead := insert (!v) t.dead, ret := … }`. The
`C`-side burst kills one arbitrary bit:

```lean
/-- `bindUnset b ; retC` from an all-alive state (`dead = ∅`). -/
theorem killThenRetC_burst {r t id b}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some (!b) ∨ k ∈ t.F)).card)
    (hd0 : t.dead = ∅)
    (hwT : P.f + 1 ≤ #{k | t.call k = some true  ∨ k ∈ t.F})
    (hwF : P.f + 1 ≤ #{k | t.call k = some false ∨ k ∈ t.F})
    (hg : t.grade = none ∨ t.grade = some false) (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id .C)
      { t with dead := insert b t.dead, grade := some false,
               ret := Function.update t.ret id true }
```

(`retC`'s `1 ≤ dead.card` holds because `insert` is nonempty).

### Where `hd0` comes from at the call sites

The two value-return rows derive it from the branch they are in rather than
carrying it in the relation. At `retA`/`retB` the row already holds
`hlive : v ∉ t.dead` (the certificate refutation) and enters the burst branch
under `hdead : (!v) ∉ t.dead`, and a `Finset Bool` missing both `v` and `!v` is
empty:

```lean
theorem dead_empty_of_both {d : Finset Bool} {v : Bool}
    (h1 : v ∉ d) (h2 : (!v) ∉ d) : d = ∅
```

so the call sites read `killThenRetA_burst hq hw hlive (dead_empty_of_both
hlive hdead) hgr hret`, and likewise for `retB`. The `retC` row splits on
`Finset.eq_empty_or_nonempty t.dead` outright, so its empty branch *is* `hd0`
and its nonempty branch answers with a single `Step.retC`.

### Which bit the `C`-return kills

`retC` fires the burst only from `t.dead = ∅` (otherwise `1 ≤ t.dead.card`
already holds and a single `Step.retC` answers). The killed bit is
`b* := Classical.choose (deadCert_of_sealBot_quorum …)` — the certified bit
its evidence names: the opposite of the unique honestly-voted bit when one
exists (Case A branch), and canonically `false` in the neither-bit-decidable
case (Case B branch, where both bits are certified and the choice is
arbitrary). Soundness never depends on the choice: both spec-side guards of
`bindUnset b*` hold for either bit (they read `bothValid`), and a certified
bit can never carry later return evidence, so no future row is obstructed by
the pick — if some later `retB v` were to need `v` alive, its evidence proves
`¬ DeadCert P s' v`, and `DeadCert.mono` shows `v` was never certified, hence
never picked.

### The matching table

| impl rule | label | spec answer | relation obligations beyond `Inv.step` |
|---|---|---|---|
| `call` | `callG r id b` | `Step.call` (guard via `call_eq`) | `call_eq`/`ret_eq` re-pointwise; `dead_cert` by `DeadCert.mono` (input write only); grade evs untouched |
| `callLoop` | `callG r id b` | `Step.callLoop` | all fields unchanged |
| `deliver` | τ | stutter (`weakLSilent_refl`) | `dead_cert` via `DeadCert.mono` (recv grows); grade evs via `recvCount_le_recvMsg` |
| `relay` | τ | stutter | frame: sender's `sentInput` only |
| `echo` | τ | stutter | frame: sender's `sentEcho` only |
| `voteBit` / `voteBot` | τ | stutter | `sentVote` goes `none → some _`: `DeadCert.mono`'s persistence hypothesis holds vacuously-forward (wall members already committed) |
| `bindBit` / `bindBot` | τ | stutter | frame: sender's `sentBind` only |
| `sealBit` / `sealBot` | τ | stutter | frame: sender's `sentSeal` only (nothing in the relation reads `sentSeal` outside `Inv`) |
| `byz` | τ | stutter | frame: `sent` pool of a corrupted sender only |
| `retA id v` | `retG r id (A v)` | `(!v) ∈ dead`: single `Step.retA`; else: `killThenRetA_burst` | see below |
| `retB id v` | `retG r id (B v)` | `(!v) ∈ dead`: single `Step.retB`; else: `killThenRetB_burst` | see below |
| `retC id` | `retG r id C` | `dead ≠ ∅`: single `Step.retC`; else: `killThenRetC_burst` on `b*` | see below |
| `fail id` | `fail id` | `Step.fail` (lockstep `corrupt`) | `corrupt_F_eq`; `dead` untouched by spec `corrupt`; `dead_cert` via `DeadCert.mono` (`corrupt_recv`/`corrupt_proc`/`corrupt_F_subset`); grade evs via `corrupt_recvCount` |

The three return rows in detail. Common first move: harvest the honest
`VOTE`-level quorum —

* `retA`: `hcnt : n − f ≤ recvCount id (.seal (some v))` →
  `bind_receipts_of_seal_quorum` → `voteQuorum_of_bind_receipts` (via
  `n − f ≥ f + 1`) → `hvq : n − f ≤ recvCount k (.vote (some v))`;
* `retB`: `hbind : f + 1 ≤ recvCount id (.bind (some v))` →
  `voteQuorum_of_bind_receipts` → `hvq`;

then

1. `hlive : v ∉ t.dead` — from `dead_cert` contraposed by
   `not_deadCert_of_voteQuorum hvq`;
2. grade latch (`retA` only) — `grade_ne_false_of_seal_quorum`: the `SEAL v`
   quorum against `gradeC_ev`'s `SEAL ⊥` quorum meets in an honest
   double-sealer, contradicting `seal_once`;
3. dissent count (`retB` only) — `spec_supp (suppI_of_valid hval (!v))`;
4. case `(!v) ∈ t.dead`: single labelled step. Case `(!v) ∉ t.dead`: burst, with
   `bindUnset_guards` fed by `echoQuorum_of_vote_receipts hvq` and `hd0` by
   `dead_empty_of_both hlive hdead`;
5. restore: `dead_cert` — old bits by `DeadCert.mono` (the step only sets
   `returned`), the new bit `!v` by `deadCert_of_voteQuorum hvq`;
   `gradeA_ev := ⟨v, id, hcnt⟩` (`retA`), other grade evidence by
   monotonicity or vacuity.

`retC`: `hwT`/`hwF` from `suppI_of_valid hval`, the C-latch from
`grade_ne_true_of_sealBot_quorum` (`SEAL ⊥` quorum against `gradeA_ev`'s
`SEAL v` quorum, honest double-sealer, `seal_once`), the burst's `b*` and its
certificate from `deadCert_of_sealBot_quorum`, the `bindUnset` quorum guard
from `quorum_of_msg_quorum` on `bothValid`'s `INPUT` quorum; restore
`gradeC_ev := ⟨id, hcnt⟩` and `dead_cert` as above with `DeadCert b*` for the
new member.

Value agreement needs no dedicated lemmas: with `dead` in place of a bound
value, agreement between successive returns is the guard pair
`v ∉ dead ∧ (!v) ∈ dead` itself, discharged per row by
`not_deadCert_of_voteQuorum` (for `∉`) and the case analysis (for `∈`).

## Invariant inventory

### Shared machinery

The kit the proof draws on, most of it common to the instance refinements of
the development; the `SEAL`-level τ-rows (`sealBit`/`sealBot`) are frame cases
identical in shape to `bindBit`/`bindBot` and need nothing beyond it:

* the weak-transition kit: `weakLStep_single`, `weakLSilent_single`,
  `weakLStep_tauThen`;
* network plumbing: `recv_sub`, `recvCount_le_recvMsg`, `mem_mcast_sent`,
  `mem_recvMsg_recv`, `exists_sender_notMem`, `exists_honest_recv₂`,
  `corrupt_*` frame lemmas, `corrupt_F_eq`;
* the corruption budget `F_card` and the D15 input machinery: `ImplSupp`,
  `ImplSupp.mono`, `input_orig`, `input_supp`, `input_called`,
  `Inv.supp_of_input_receipts`, `suppI_of_valid`, `InstRel.spec_supp`,
  `quorum_of_msg_quorum`, `inputQuorum_of_echoQuorum`;
* the `ECHO`-level certificate: `EchoQuorum`, `echoQuorum_unique`,
  `echoQuorum_of_vote_receipts`, and `bindUnset_guards` (quorum + SuppOK count
  out of one `EchoQuorum`);
* conformance and write-once clauses `echo_conf`, `echo_once`, `vote_input`,
  `vote_conf`, `bind_once`, `bind_conf` (`bind_once` serves here as a
  conformance fact only — grade exclusivity is read at the `SEAL` level).

### `Inv` clauses at the `VOTE` and `SEAL` levels

```lean
/-- Honest `VOTE` multicasts are recorded in the write-once `sentVote`. -/
vote_once : ∀ j w, j ∉ s.F → Msg.vote w ∈ s.sent j → (s.proc j).sentVote = some w
/-- Honest `BIND ⊥` is backed by `n − f` any-`VOTE` receipts. -/
bindBot_conf : ∀ j, j ∉ s.F → Msg.bind none ∈ s.sent j → P.n - P.f ≤ s.voteCount j
/-- Honest `SEAL` multicasts are recorded in the write-once `sentSeal`. -/
seal_once : ∀ j w, j ∉ s.F → Msg.seal w ∈ s.sent j → (s.proc j).sentSeal = some w
/-- Honest `SEAL b` is backed by an `n − f` `BIND b` receipt quorum. -/
seal_conf : ∀ j b, j ∉ s.F → Msg.seal (some b) ∈ s.sent j →
  P.n - P.f ≤ s.recvCount j (.bind (some b))
/-- Honest `SEAL ⊥` is backed by `n − f` any-`BIND` receipts. -/
sealBot_conf : ∀ j, j ∉ s.F → Msg.seal none ∈ s.sent j → P.n - P.f ≤ s.bindCount j
/-- Honest sealers hold an input (D8, one level up). -/
seal_input : ∀ j w, j ∉ s.F → Msg.seal w ∈ s.sent j → (s.proc j).input ≠ none
```

`vote_once` and `bindBot_conf` are forced by the kill certificates (`VoteWall`
counting and the Case B branch of `deadCert_of_sealBot_quorum`); the seal
clauses mirror the per-level pattern one level up, with
`seal_once`/`seal_conf`/`sealBot_conf` load-bearing (grade exclusivity and the
two harvest chains) and `seal_input` kept for pattern uniformity only.
Preservation is by the same three schemas as every other clause: the
`_once` clauses by the `sentSeal = none`/`sentVote = none` send guards, the
`_conf` clauses by the sending rule's own receipt guard plus count
monotonicity, everything by frame elsewhere. Count monotonicity needs the
any-payload analogues of `recvCount_le_recvMsg`:

```lean
theorem voteCount_le_recvMsg (s : ImplState n) (i j : Fin n) (m : Msg) (i' : Fin n) :
    s.voteCount i' ≤ (s.recvMsg i j m).voteCount i'
-- likewise bindCount_le_recvMsg, sealCount_le_recvMsg, echoCount_le_recvMsg
```

(same one-line `Finset.card_le_card` proof; the four together cover every
level of the ladder).

### Certificate and harvest lemmas

Collected statements (all defined in `GBCASim.lean` unless noted):

```lean
def VoteWall (P : Params) (s : ImplState P.n) (b : Bool) : Prop := …   -- § kill certificates
def DeadCert (P : Params) (s : ImplState P.n) (b : Bool) : Prop :=
  EchoQuorum P s (!b) ∨ VoteWall P s b

theorem DeadCert.mono {s s' : ImplState P.n} {b : Bool}
    (hrecv : ∀ i j m, m ∈ s.recv i j → m ∈ s'.recv i j)
    (hvote : ∀ j w, (s.proc j).sentVote = some w → (s'.proc j).sentVote = some w)
    (hF : s.F ⊆ s'.F) : DeadCert P s b → DeadCert P s' b

theorem voteQuorum_of_bind_receipts {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.f + 1 ≤ s.recvCount i (.bind (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.recvCount k (.vote (some v))

theorem bind_receipts_of_seal_quorum {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.recvCount i (.seal (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.recvCount k (.bind (some v))

theorem deadCert_of_voteQuorum {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.recvCount i (.vote (some v))) :
    DeadCert P s (!v)

theorem not_deadCert_of_voteQuorum {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.recvCount i (.vote (some v))) :
    ¬ DeadCert P s v

theorem deadCert_of_sealBot_quorum {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} (h : P.n - P.f ≤ s.recvCount i (.seal none)) :
    ∃ b, DeadCert P s b

theorem grade_ne_false_of_seal_quorum {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {id : Fin P.n} {v : Bool}
    (hcnt : P.n - P.f ≤ s.recvCount id (.seal (some v))) : t.grade ≠ some false

theorem grade_ne_true_of_sealBot_quorum {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {id : Fin P.n}
    (hcnt : P.n - P.f ≤ s.recvCount id (.seal none)) : t.grade ≠ some true
```

The counting core shared by `not_deadCert_of_voteQuorum` (Case B refutation)
and worth stating once:

```lean
/-- Two `n − f`-sized subsets of `Fin n` meeting only inside `F` contradict
`|F| ≤ f < n − 2f`. -/
theorem no_disjoint_quorums {P : Params} {Q D F : Finset (Fin P.n)}
    (hQ : P.n - P.f ≤ Q.card) (hD : P.n - P.f ≤ D.card)
    (hQD : Q ∩ D ⊆ F) (hF : F.card ≤ P.f) : False
```

(`|Q| + |D| = |Q ∪ D| + |Q ∩ D| ≤ n + f`, against `2(n − f) > n + f` from
`P.hf` — the same arithmetic as `exists_honest_recv₂`, exposed as a set
statement because `VoteWall` is a set of *processes*, not a receipt row).

## Why this shape: the compression attack dies at `n = 4, f = 1`

A one-level-shallower reading of the grade-1 evidence — `f + 1` `VOTE v`
receipts in place of `f + 1` `BIND v` receipts, with the `SEAL` level elided
and the returns reading `BIND` quorums — admits the following binding
violation, which pins both D18 and the certificate design. Prefix: `p1`, `p2`,
`p3` are called and echo `0`, `1`, `0` respectively; with both bits `Valid`
everywhere, all three vote ⊥, bind ⊥ (and seal ⊥), and `p1` C-returns off the
three ⊥-receipts while `p4` is held unscheduled at the echo stage. Extension
A: `p4` echoes `0` and votes `0` off the `ECHO 0` senders `{p1, p3, p4}`;
`p2` is corrupted and injects `VOTE 0` and `BIND 0`; `p3` collects `f + 1 = 2`
`VOTE 0` receipts from `{p4, p2}` and B-returns `0`. Extension B is the
mirror image (corrupt `p1`, hand out `1`) — one C-return, two extensions,
two different surviving bits: binding fails, and no forward simulation into
any binding-faithful spec exists.

Against the D18 evidence level the attack dies: in extension A, `p3`'s
`retB 0` needs `f + 1 = 2` `BIND 0` receipts, hence an honest `BIND 0` sender
(`2 > |F| = 1`), hence an `n − f = 3`-strong `VOTE 0` receipt quorum at that
sender. But the prefix pinned the write-once votes of `p1`, `p2`, `p3` at ⊥,
and `p2` is the corrupted slot, so the `VOTE 0` senders available in any
extension are at most `{p4} ∪ F = {p4, p2}` — `2 < 3`, no quorum, no honest
`BIND 0`, no `retB 0` (and a fortiori no `retA 0`: an honest `SEAL 0` needs
three `BIND 0` senders). Symmetrically for bit `1` in extension B. In
certificate terms: at `p1`'s C-return the honest `BIND ⊥` senders' vote
quorums pin `{p1, p2, p3}` as committed-⊥-or-`F`, which is `VoteWall` at
`n − f = 3` for **both** bits — exactly the `∃ b, DeadCert` the `retC` burst
consumes, and exactly why no later receipt pattern can contradict the kill.

## Where the shapes surface downstream

The exclusion set and the kill certificate are read directly by the layers
above this file. `CoreSimRel.lean`/`CoreSim.lean` phrase the round skeleton
over `dead`: `IsLastBound g r` is `(g r).dead ≠ ∅ ∧ (g (r + 1)).dead = ∅`,
`Closed g r` is `(g r).dead ≠ ∅ ∨ (g r).grade = some false`, and `a_commit`,
`gradeA_needs_bind`, `bind_supp` and the A-lock certificates are keyed on the
guard pair `(!b) ∈ dead ∧ b ∉ dead` — the D19 rendering of `bind = some b`,
with `bind ≠ none` rendered as `dead ≠ ∅`. `GBCAFamily.instRel_corrupt`
carries the `dead_cert` row through `DeadCert.mono`, whose three hypotheses it
discharges by `corrupt_recv`, `corrupt_proc` and `corrupt_F_subset`.
`FlatNetwork.lean`'s deployed rendering carries the same ladder inside one
process: the stage node `GBCA.ProcNodeN` keeps the write-once `sentSeal` slot in
its `proc` record and carries its own `sealCount` over its inbox rows, the
rendezvous rows `gsndSealBit`/`gsndSealBot` are the seal multicasts read off
that node, and the three `retG` rows (and their `byzRetG` twins) read the seal
level off it. The bridge to the global view is `GSub.subDefl`
(`ABA/GBCASub.lean`), which assembles the round-`r` `ImplState` from the round
subsystem's pieces — the stage programs' records and inbox rows, and the round's
own message fabric, which holds the per-sender pools and the corrupted set; the
seal-level counts agree across it (`subDefl_sealCount`) because a deflated
`recv` row is the sender's row of the program that receives it. That bridge is
what lets `GSub.subSim` consume `implRefines` as it stands: the projection
`sub_projects` matches every subsystem transition with the monolithic
instance's, one step for one step, and this file's refinement answers it, its
weak answer read back at the subsystem's interface — which is what licenses
replacing a round's subsystem by the graded agreement specification.

## Risks and open points

1. **`Bool` negation syntax.** Two elaboration traps. (a) `bindUnset b`'s
   support guard mentions `some (!b)`; instantiating `b := !v` produces
   `some (!(!v))`, which is not
   definitionally `some v` — the burst lemmas carry one
   `simpa only [Bool.not_not]` at the `bindUnset` application. (b) `!` binds
   looser than `∈`/`∉`, so `!v ∈ s.dead` silently elaborates as the coerced
   `!(decide (v ∈ s.dead))`; every membership guard on the negated bit must be
   written `(!v) ∈ s.dead` / `(!v) ∉ t.dead`.
2. **`retB`'s `honce` receipt.** The implementation's `retB` keeps the
   algorithm's "at least one `SEAL v` receipt" guard. The simulation never
   reads it (the `f + 1` `BIND v` receipts carry all evidence), so it rides
   along as pure conformance; it must not be dropped from the rule — the rule
   is the algorithm.
3. **Canonical `C`-kill via `Classical.choose`.** The `retC` row consumes
   `∃ b, DeadCert P s b` nonconstructively. If a later development (e.g. a
   quantitative or decidability layer) needs the choice computable, replace it
   with the explicit case split (`if EchoQuorum … true then false else …`);
   nothing in the simulation depends on which certified bit is chosen.
4. **`dead.card ≤ 1` is an invariant, and the relation still does not carry
   it.** It holds at every state of every execution of the specification
   instance (`GBCASafety.dead_card_le_one`), by the `hd0 : dead = ∅` guard on
   the single writer. The relation neither states nor needs it: each burst gets
   its `hd0` from the branch analysis of its own row (`dead_empty_of_both` at
   the value returns, `Finset.eq_empty_or_nonempty` at `retC`), so adding the
   conjunct would create restoration obligations on every row for no benefit.
   Recorded so nobody "strengthens" the relation into extra work.
5. **`VoteWall` reads process-local slots.** Unlike `EchoQuorum` it counts
   `sentVote` slots, not receipts — still monotone in `F` (a corrupted slot
   stays in the wall via the `j ∈ F` disjunct) and in `sentVote` (write-once),
   which is all the simulation needs. Any per-process decomposition must
   therefore transport it along the state map like the other `proc`-field
   predicates — in `ABA/GBCASub.lean` that is `subDefl_proc` for the slot and
   `subDefl_F` for the corrupted set, the latter reading the copy of the
   corrupted set held by the round's own message fabric.
6. **Vacuous-fill hazard in `deadCert_of_sealBot_quorum`.** The Case B branch
   needs the global classical split "some honest bit-voter exists"; its
   **no**-branch uses `bindBot_conf` on a *specific* honest `BIND` sender
   harvested from `sealBot_conf`'s any-`BIND` count. That harvest wants
   `exists_sender_notMem` on an any-payload count, i.e. the payload-returning
   variant `ImplState.exists_bind_sender_notMem`:
   `∃ k w, k ∉ F ∧ Msg.bind w ∈ s.recv p k`, same proof as the exact-message
   version.
