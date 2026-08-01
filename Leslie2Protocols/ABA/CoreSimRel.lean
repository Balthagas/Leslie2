/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.CoreView
import Leslie2Protocols.ABA.LayeredSpec
import Leslie2Protocols.ABA.GBCASafety

/-!
# The core-simulation relation: the lazy abstract twin

The relation and invariant for `coreSim : layeredSpec ⊑ ABA.spec`, following
`DESIGN-CoreSim.md`. The abstract twin is *ultra-lazy* (D16): it answers
every hidden (τ) row and the probabilistic coin row by stuttering under a
constant coupling; the single τ-burst fires at the first `retABA` row, where
the twin binds, fills the board, decides, and returns within one weak step.

* `Abs` — the abstract-state constraints (C1 `F_eq`, C2 `ret_eq`, `coin_bot`,
  and C3/C7 `phase`).
* `Inv` — the concrete invariant (thirty-nine fields, docstring-numbered
  I1–I30, a few numbers covering a small group of fields: F-lockstep, input
  coherence, the `Closed`-keyed round skeleton with quiescence, DECIDED
  coherence, A-grade commitment, delivery soundness, round/phase coherence,
  support pools, and the burn-proof certificate conjuncts I28–I30).
* `coreR` — the simulation relation `Inv ∧ Abs`, wrapped in `diracRel` by
  `CoreSim.lean`.

This file holds the two predicates, their frame and reader lemmas, and the
initial states. The proof that `coreR` is a simulation relation runs in the two
files above it: step inversion for `layeredSpec` and preservation of `Inv` in
`CoreSimInv.lean`, `Abs` preservation for the stutter rows and the assembly in
`CoreSimAbs.lean`.
-/

open Stream'

namespace PLTS
namespace ABA

open Net Layer

variable {P : Params}

/-- The ABA-side factors of a deployment-shaped state, read as one state: the
round loops beside the network they share. -/
abbrev LayeredSpecState.aba (s : LayeredSpecState P) : ABAState P := (s.2.1, s.2.2.1)

/-- The coin oracle's factor. -/
abbrev LayeredSpecState.wcc (s : LayeredSpecState P) : ℕ → WCC.SpecState P.n := s.2.2.2

/-- The last-bound-round reading of a family: round `r`'s exclusion set is non-empty
and round `r + 1`'s is still empty.
Concrete-only; used by `Inv.agree_locked` (I3a). -/
def IsLastBound (g : ℕ → GBCA.SpecState P.n) (r : ℕ) : Prop :=
  (g r).dead ≠ ∅ ∧ (g (r + 1)).dead = ∅

/-- An honest-side holder of round `r`'s outcome bit `v`: a round-`(r + 1)`
GBCA call, or a committed estimate between round `r`'s `retG` and round
`(r + 1)`'s. Honesty is *not* part of the predicate; the clauses that consume
it (`Inv.carrier_agree`, `ACommit`) add it. -/
def Carrier (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : ABAState P)
    (r : ℕ) (id : Fin P.n) (v : Bool) : Prop :=
  (g (r + 1)).call id = some v ∨
    ((c.procs id).est = some v ∧
      (((c.procs id).round = r ∧
          ((c.procs id).phase = .toCallW ∨ (c.procs id).phase = .awaitW)) ∨
        ((c.procs id).round = r + 1 ∧
          ((c.procs id).phase = .idle ∨ (c.procs id).phase = .toCallG ∨
            (c.procs id).phase = .awaitG))))

/-- The permanent commitments of an `A`-locked round (the old `a_commit`
conclusions, plus the round's own honest carriers). Carried *inside* every
`A`-certificate: a later `bindUnset` may *burn* the round — kill its surviving
bit as well, reaching `dead = {0, 1}` — after which the exclusion set alone no
longer names the decided value. Every component is monotone-stable: the pair
hypothesis of the first component only ever loses instances when `dead` grows,
and the others read only `call` (write-once) and honest `procs` fields. -/
def ACommit (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : ABAState P)
    (r : ℕ) (b : Bool) : Prop :=
  (∀ r' b', r ≤ r' → (!b') ∈ (g r').dead ∧ b' ∉ (g r').dead → b' = b) ∧
  (∀ r' id b', r < r' → id ∉ c.F → (g r').call id = some b' → b' = b) ∧
  (∀ id, id ∉ c.F → r < (c.procs id).round → (c.procs id).est = some b) ∧
  (∀ id v, id ∉ c.F → Carrier P g c r id v → v = b)

/-- The full `A`-certificate: an `A`-locked round whose surviving bit at lock
time was `b` (the permanent residue `!b ∈ dead`), together with the round's
permanent commitments. -/
def ACert (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : ABAState P)
    (r : ℕ) (b : Bool) : Prop :=
  (g r).grade = some true ∧ (!b) ∈ (g r).dead ∧ ACommit P g c r b

/-- A process-side holder of an `A`-decision for `b`: a live `A`-grade or a
pooled DECIDED multicast. -/
def AHolder (P : Params) (c : ABAState P) (id : Fin P.n) (b : Bool) : Prop :=
  (c.procs id).lastGrade = some (.A b) ∨ b ∈ c.decidedSent id

/-! ### Abs: the abstract-twin constraints -/

/-- Constraints tying the abstract twin `a` to the concrete state — the
**ultra-lazy, never-flipping twin** (D16). The twin never fires rule 5
(`coin` permanently `⊥`), and it never binds *between* rows: it lives in one
of two phases keyed on `a.val`. In **phase 1** (before the first visible
return) it is fully unbound, its `call` row mirrors the concrete write-once
external inputs (banked by rule 1 at every genuine `callABA` — whose
unconditional ghost overwrite also keeps `a.input` synced on every committed
input), and it answers *every* hidden row with a stutter. In **phase 2**
(after the first `retABA`, whose answering burst binds, fills, and decides in
one τ-tail) the board is clear, `bind = val = some v`, and `v` is permanently
certified by a concrete `A`-lock. Laziness is load-bearing (D16): any twin
that binds before the last genuine input bank is killed by ghost junk — a
`callABA` answered by the concrete self-loop force-banks rule 2's
first-write-wins ghost, and once bound the twin can never overwrite it. -/
structure Abs (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : ABAState P)
    (w : ℕ → WCC.SpecState P.n) (a : SpecState P.n) : Prop where
  /-- C1: corrupted sets agree. -/
  F_eq : a.F = c.F
  /-- C2: returns agree. -/
  ret_eq : ∀ id, a.ret id = (c.procs id).returned
  /-- The abstract twin never fires the coin-flip rule: its coin is always `⊥`. -/
  coin_bot : a.coin = .bot
  /-- C3/C7: the two-phase discipline. Phase 1 (pre-return): unbound,
  undecided, `call` = concrete inputs, ghost synced on committed inputs.
  Phase 2 (post-return): `bind = val = some v`, board clear, `v` certified by
  a full `A`-certificate, and every honest `A`-decision holder — live grade or
  pooled DECIDED — names `v` (the F-free universal that survives corruption of
  the original witnesses). -/
  phase :
    (a.bind = none ∧ a.val = none ∧
      (∀ id, a.call id = (c.procs id).input) ∧
      (∀ id b, (c.procs id).input = some b → a.input id = some b)) ∨
    (∃ v, a.bind = some v ∧ a.val = some v ∧ (∀ id, a.call id = none) ∧
      (∃ r, ACert P g c r v) ∧
      (∀ j b', j ∉ c.F → AHolder P c j b' → b' = v))

/-- A permanent, `F`-free residue of "an honest-at-the-time dissent existed at round `r` when
some process exited `GBCA_r` via a `B`/`C`-return": round `r`'s surviving bit `v` has
provenance either from round `0`'s external input (`input_g0`-style, if `r = 0`) or from round
`r - 1`'s surviving bit/`C`-lock (`call_prov`-style, if `r ≥ 1`) being the opposite bit — both
permanent facts, so this survives every later `fail`/step once established. -/
def DissentResidue (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : ABAState P)
    (r : ℕ) : Prop :=
  ∃ v, (!v) ∈ (g r).dead ∧
    (if r = 0 then ∃ id', (c.procs id').input = some (!v)
     else v ∈ (g (r - 1)).dead ∨ (g (r - 1)).grade = some false)

/-- `DissentResidue` transports along any frame that agrees on `g`'s exclusion set at
`r`/`r - 1`, `g`'s grade at `r - 1`, and every honest input (the shape every `Inv.step_*`
row's frame facts already provide for their own row; the `r = 0` branch only needs the input
equality, the `r ≥ 1` branch only the exclusion-set/grade ones). -/
theorem DissentResidue.transport {P : Params} {g₀ g : ℕ → GBCA.SpecState P.n}
    {c₀ c : ABAState P} {r : ℕ}
    (hdead : (g r).dead = (g₀ r).dead)
    (hdead1 : (g (r - 1)).dead = (g₀ (r - 1)).dead)
    (hgrade1 : (g₀ (r - 1)).grade = some false → (g (r - 1)).grade = some false)
    (hinput : ∀ id, (c.procs id).input = (c₀.procs id).input) :
    DissentResidue P g₀ c₀ r → DissentResidue P g c r := by
  rintro ⟨v, hb, hif⟩
  refine ⟨v, by rw [hdead]; exact hb, ?_⟩
  by_cases h0 : r = 0
  · rw [if_pos h0] at hif ⊢
    obtain ⟨id', hid'⟩ := hif
    exact ⟨id', by rw [hinput]; exact hid'⟩
  · rw [if_neg h0] at hif ⊢
    rcases hif with h | h
    · left; rw [hdead1]; exact h
    · right; exact hgrade1 h

/-- The permanent input-or-`F` support pool for a bit `v` (D13/D15 SuppOK shape,
one level down): `f + 1` processes that either committed `v` as their genuine external
input (write-once) or are corrupted (`F` only grows). Both disjuncts are permanent, so
the count is monotone along every step. -/
def InputSupp (P : Params) (c : ABAState P) (v : Bool) : Prop :=
  P.f + 1 ≤ (Finset.univ.filter
    (fun id => (c.procs id).input = some v ∨ id ∈ c.F)).card

/-- `InputSupp` is monotone under input growth and `F` growth. -/
theorem InputSupp.mono {P : Params} {c c' : ABAState P} {v : Bool}
    (h : InputSupp P c v)
    (hin : ∀ id b, (c.procs id).input = some b → (c'.procs id).input = some b)
    (hF : c.F ⊆ c'.F) : InputSupp P c' v := by
  refine le_trans h (Finset.card_le_card ?_)
  intro id hid
  rw [Finset.mem_filter] at hid ⊢
  exact ⟨Finset.mem_univ id, hid.2.elim (fun h' => Or.inl (hin id v h'))
    (fun h' => Or.inr (hF h'))⟩

/-- Round `r` is **closed**: some bit is dead, or a `C`-return has locked its grade to the
C-side. Either way it hands out no fresh bit from here on. This is the predicate the round
skeleton of `Inv` (`down_closed`, `quiescent`, `w_bound`, `round_bound`, `w_called`) is keyed
on: a `C`-return kills no bit itself, so "round `r` is finished" is `Closed`, which is
strictly weaker than `dead ≠ ∅`. -/
def Closed (g : ℕ → GBCA.SpecState P.n) (r : ℕ) : Prop :=
  (g r).dead ≠ ∅ ∨ (g r).grade = some false

/-- `Closed` reads only round `r`'s `dead` and `grade`. -/
theorem Closed.congr {g g' : ℕ → GBCA.SpecState P.n} {r : ℕ}
    (hdead : (g' r).dead = (g r).dead) (hgrade : (g' r).grade = (g r).grade) :
    Closed g' r ↔ Closed g r := by
  unfold Closed; rw [hdead, hgrade]

/-- `Closed` transports along any frame that keeps round `r`'s `dead` and only ever adds the
`C`-side grade lock. -/
theorem Closed.of_frame {g g' : ℕ → GBCA.SpecState P.n} {r : ℕ}
    (hdead : (g' r).dead = (g r).dead)
    (hgrade : (g r).grade = some false → (g' r).grade = some false)
    (h : Closed g r) : Closed g' r :=
  h.imp (fun hb hc => hb (by rw [← hdead]; exact hc)) hgrade

/-- `ACommit` transports along any frame that keeps `dead` and `call`
pointwise, keeps honest `round`/`est` projections, reflects carriers, and only
ever grows `F`. -/
theorem ACommit.of_frame {P : Params} {g g' : ℕ → GBCA.SpecState P.n}
    {c c' : ABAState P} {r : ℕ} {b : Bool}
    (hdead : ∀ r', (g' r').dead = (g r').dead)
    (hcall : ∀ r' id, (g' r').call id = (g r').call id)
    (hF : c.F ⊆ c'.F)
    (hround : ∀ id, (c'.procs id).round = (c.procs id).round)
    (hest : ∀ id, (c'.procs id).est = (c.procs id).est)
    (hcarr : ∀ id v, Carrier P g' c' r id v → Carrier P g c r id v)
    (h : ACommit P g c r b) : ACommit P g' c' r b := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun r' b' hrr' hb' => h1 r' b' hrr' (by rw [← hdead r']; exact hb'),
    fun r' id b' hrr' hmem hcall' =>
      h2 r' id b' hrr' (fun hh => hmem (hF hh)) (by rw [← hcall r']; exact hcall'),
    fun id hmem hround' => ?_,
    fun id v hmem hcar => h4 id v (fun hh => hmem (hF hh)) (hcarr id v hcar)⟩
  rw [hest id]
  exact h3 id (fun hh => hmem (hF hh)) (by rw [← hround id]; exact hround')

/-- `ACert` transports along the same frames as `ACommit`, given the round's
grade is kept. -/
theorem ACert.of_frame {P : Params} {g g' : ℕ → GBCA.SpecState P.n}
    {c c' : ABAState P} {r : ℕ} {b : Bool}
    (hgrade : (g' r).grade = (g r).grade)
    (hdead : ∀ r', (g' r').dead = (g r').dead)
    (hcall : ∀ r' id, (g' r').call id = (g r').call id)
    (hF : c.F ⊆ c'.F)
    (hround : ∀ id, (c'.procs id).round = (c.procs id).round)
    (hest : ∀ id, (c'.procs id).est = (c.procs id).est)
    (hcarr : ∀ id v, Carrier P g' c' r id v → Carrier P g c r id v)
    (h : ACert P g c r b) : ACert P g' c' r b :=
  ⟨hgrade.trans h.1, by rw [hdead r]; exact h.2.1,
    ACommit.of_frame hdead hcall hF hround hest hcarr h.2.2⟩

/-- The `Abs`-side transport a step row hands to `Abs.frame`: `A`-certificates survive the
step, and any holder-pinning universal survives given its certificate (the certificate is
what pins a *fresh* `A`-holder when every old holder has been corrupted away). -/
def AbsFrame (P : Params) (g g' : ℕ → GBCA.SpecState P.n) (c c' : ABAState P) : Prop :=
  (∀ r0 b0, ACert P g c r0 b0 → ∃ r1, ACert P g' c' r1 b0) ∧
  (∀ v, (∃ r1, ACert P g c r1 v) →
    (∀ j0 b0', j0 ∉ c.F → AHolder P c j0 b0' → b0' = v) →
    ∀ j b', j ∉ c'.F → AHolder P c' j b' → b' = v)

/-- The identity `AbsFrame`, for rows that touch neither `g`-certificates nor holders. -/
theorem AbsFrame.refl (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : ABAState P) :
    AbsFrame P g g c c :=
  ⟨fun r0 _ hc => ⟨r0, hc⟩, fun _ _ hpin => hpin⟩

/-! ### Inv: the concrete invariant (I1–I7) -/

/-- The concrete invariant of `layeredSpec`-reachable states. All conjuncts are
about the concrete `(g, c, w)` only. -/
structure Inv (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : ABAState P)
    (w : ℕ → WCC.SpecState P.n) : Prop where
  /-- I1: F-lockstep across every component copy. -/
  F_g : ∀ r, (g r).F = c.F
  F_w : ∀ r, (w r).F = c.F
  F_card : c.F.card ≤ P.f
  /-- I2: round-0 honest GBCA inputs are the external inputs. -/
  input_g0 : ∀ id b, id ∉ c.F → (g 0).call id = some b →
    (c.procs id).input = some b
  /-- I2': honest GBCA callers (any round) have committed an external input. -/
  input_called : ∀ r id, id ∉ c.F → (g r).call id ≠ none →
    (c.procs id).input ≠ none
  /-- I2'' : once a proc has left `idle` its input is committed (write-once, never
  cleared; the sole idle-exit is `callABA`'s honest `input` ctor, which sets it). -/
  phase_input : ∀ id, id ∉ c.F → (c.procs id).phase ≠ .idle → (c.procs id).input ≠ none
  /-- I6: closed rounds are downward closed. -/
  down_closed : ∀ r, Closed g (r + 1) → Closed g r
  /-- I7: cofinitely many rounds are open. -/
  quiescent : ∃ R, ∀ r, R ≤ r → ¬ Closed g r
  /-- I5: coins flip only at closed rounds. -/
  w_bound : ∀ r, (w r).val ≠ .bot → Closed g r
  /-- I4: delivery soundness for DECIDED, per (receiver, sender, bit) (D12′).
  Honesty-free: sent pools only ever grow, so every receipt stays covered even
  after the sender is corrupted or equivocates. -/
  recv_sound : ∀ i j b, b ∈ c.decidedRecv i j → b ∈ c.decidedSent j
  /-- I4: honest DECIDEDs come from an A-locked bound round — per pooled bit
  (D12′). Equivocation-robust form: a corrupted sender may pool both bits (and
  its receipts count toward either tally), but any `n − f`-sender tally for `b`
  contains a never-corrupted sender of `b` (pigeonhole, at the `retABA` row),
  and *that* sender's pooled `b` carries the `A`-lock certificate. -/
  decided_src : ∀ id b, id ∉ c.F → b ∈ c.decidedSent id → ∃ r, ACert P g c r b
  /-- I3b: an A-locked round whose surviving bit is still alive commits
  everything at and above it. Keyed on the live pair — the pair can only be
  *destroyed* by later kills (never created at an A-locked round, whose
  exclusion set is already non-empty), so the clause weakens vacuously; the
  certificates (`ACert`) carry the payload past a burn. -/
  a_commit : ∀ r b, (g r).grade = some true → (!b) ∈ (g r).dead ∧ b ∉ (g r).dead →
    ACommit P g c r b
  /-- I5': honest procs' round progress implies closed rounds below. -/
  round_bound : ∀ id, id ∉ c.F → ∀ r, r < (c.procs id).round →
    Closed g r
  /-- I3a: when the frontier coin agrees with the frontier surviving bit, honest
  estimates of procs beyond the frontier are that bit (the
  rule-6-only-filler corner: the concrete cannot rebind differently). -/
  agree_locked : ∀ r v, IsLastBound g r → (!v) ∈ (g r).dead ∧ v ∉ (g r).dead →
    (w r).val = .bit v →
    ∀ id, id ∉ c.F → r < (c.procs id).round → (c.procs id).est = some v
  /-- I8' : an A-side graded `GBCA_r` round has a non-empty exclusion set (`retA`
  requires `(!v) ∈ dead` as precondition, and `dead` is monotone). -/
  gradeA_needs_bind : ∀ r, (g r).grade = some true → (g r).dead ≠ ∅
  /-- I8 : honest `GBCA_r` callers have reached round `r` (rounds only grow). -/
  call_round : ∀ r id, id ∉ c.F → (g r).call id ≠ none → r ≤ (c.procs id).round
  /-- I9 : an honest `WCC_r` caller has already gotten `retG r`, so round `r` is closed. -/
  w_called : ∀ r id, id ∉ c.F → (w r).called id = true → Closed g r
  /-- I10 : an honest proc past round `r` has already resolved round `r`'s coin
  (flips are permanent). -/
  round_flip : ∀ r id, id ∉ c.F → r < (c.procs id).round → (w r).val ≠ .bot
  /-- I11 : round-0 pre-`retG` honest ests are the external input. -/
  est0 : ∀ id, id ∉ c.F → (c.procs id).round = 0 →
    ((c.procs id).phase = .idle ∨ (c.procs id).phase = .toCallG ∨
      (c.procs id).phase = .awaitG) →
    (c.procs id).est = (c.procs id).input
  /-- I12 : an `A`-grade traces back to a genuine `GBCA` `A`-return. Honesty-free:
  the round loop's `CoreProcStepN.retG` records the outcome carried on the shared `retG`
  label, so it is the outcome the round specification's return guards
  (`retA`/`retB`/`retC`) licensed, regardless of `id`'s corruption; this is needed
  corruption-free in `step_retW`'s `recv_sound`/`decided_src` rows, which have no honesty
  hypothesis. -/
  grade_A_src : ∀ id b, (c.procs id).lastGrade = some (.A b) →
    ∃ r, ACert P g c r b
  /-- I13 : post-`retG` est provenance — honest procs between `retG r` and
  `retW r` have `est` equal to round `r`'s surviving bit (the `A`/`B` case) or `none` with a
  `C`-return certificate. The `C`-certificate is phrased as "no round `≤ r` is `A`-locked"
  (not as an honest-dissent witness: the witness process could itself get corrupted by a
  later `fail`, so an existential witness isn't preserved — this `F`-free universal is). -/
  est_ret : ∀ r id, id ∉ c.F → (c.procs id).round = r →
    ((c.procs id).phase = .toCallW ∨ (c.procs id).phase = .awaitW) →
    ((c.procs id).est = none →
      (g r).grade = some false ∧
      ∀ r₀, r₀ ≤ r → (g r₀).grade ≠ some true) ∧
    (∀ b, (c.procs id).est = some b → (!b) ∈ (g r).dead)
  /-- I14 : `dead` is monotone and write-once per bit, so a freshly-bound round
  `r + 1`'s surviving value was already carried at round `r`: either round `r` had already
  bound to it, or round `r` just closed with a `C`-lock and the coin pins the adopted value
  (the `⊤` disjunct: an unresolved-to-a-bit coin lets the adopting return pick an arbitrary
  matching bit, so the coin fact alone doesn't pin `v`, only the `C`-lock does — every
  downstream use only needs the `grade = some false` half). -/
  bind_succ : ∀ r v, (!v) ∈ (g (r + 1)).dead →
    (!v) ∈ (g r).dead ∨
      ((g r).grade = some false ∧ ((w r).val = .bit v ∨ (w r).val = .top))
  /-- I15 : an honest call to round `r + 1` carries est-provenance from finishing
  round `r`. -/
  call_prov : ∀ r id v, id ∉ c.F → (g (r + 1)).call id = some v →
    (!v) ∈ (g r).dead ∨
      ((g r).grade = some false ∧ ((w r).val = .bit v ∨ (w r).val = .top))
  /-- I16 : honest procs at the start of round `r + 1` carry est-provenance from
  finishing round `r`. -/
  est_prev : ∀ r id, id ∉ c.F → (c.procs id).round = r + 1 →
    ((c.procs id).phase = .idle ∨ (c.procs id).phase = .toCallG ∨
      (c.procs id).phase = .awaitG) →
    ∀ v, (c.procs id).est = some v →
      (!v) ∈ (g r).dead ∨
        ((g r).grade = some false ∧ ((w r).val = .bit v ∨ (w r).val = .top))
  /-- I17 : `C`-locks propagate downward. -/
  c_chain : ∀ r, (g (r + 1)).grade = some false → (g r).grade = some false
  /-- I18 : an honest proc that hasn't yet `retG`'d this round has a committed
  (non-`⊥`) estimate — `retW`'s `est := some (est.getD b)` is always non-`none` by
  construction, and neither `callG` nor bookkeeping steps ever clear it; only a later
  `retG`'s `C`-output (which also flips the phase away from `toCallG`/`awaitG`) can. -/
  est_prev_ne : ∀ id, id ∉ c.F → (c.procs id).round ≠ 0 →
    ((c.procs id).phase = .idle ∨ (c.procs id).phase = .toCallG ∨
      (c.procs id).phase = .awaitG) →
    (c.procs id).est ≠ none
  /-- I19 : flips happen in round order. Established at the flip
  row: the threshold on `w (r + 1)` yields an honest caller (`Finset` pigeonhole, as in
  `w_bound`), which by `round_flip` has already resolved round `r`'s coin. -/
  w_order : ∀ r, (w (r + 1)).val ≠ .bot → (w r).val ≠ .bot
  /-- I20 : `F`-free residue of round-`0` `GBCA` call provenance — either the input
  is genuinely committed (write-once, permanent) or the caller was already corrupted (`F` only
  grows, so this disjunct is permanent too). Established at the `callG` round-`0` row (honest:
  `est0`; byz: the corruption ctor). -/
  input_g0_perm : ∀ id b, (g 0).call id = some b → (c.procs id).input = some b ∨ id ∈ c.F
  /-- I21' : the `WCC`-side analogue of `call_round` (I8) — an honest `WCC_r`
  caller has reached round `r`. Established at the `callW` row exactly like `call_round` is at
  `callG`; feeds `w_order`/`flip_alock`'s flip-row establishment (an honest caller of the
  newly-flipped round has already resolved every earlier round's coin via `round_flip`). -/
  w_call_round : ∀ r id, id ∉ c.F → (w r).called id = true → r ≤ (c.procs id).round
  /-- I21 : a flip-threshold consequence — once round `r`'s coin has
  resolved, round `r` is either already `A`/`C`-graded or a `DissentResidue` certifies why a
  `B`/`C`-return could have fired there. Used to decide rule 3 vs.\ rule 4 at
  the flip burst. -/
  flip_alock : ∀ r, (w r).val ≠ .bot → (g r).grade ≠ none ∨ DissentResidue P g c r
  /-- I22 : an honest process that has never received its external input has never
  called any `WCC` instance (the sole idle-exit, `callABA`'s honest `input` ctor, is what first
  makes a `callW` handshake reachable; `input` is write-once, so this is preserved trivially
  once `input ≠ none`). Feeds `w_call_round`'s self-corner at the fresh `callABA` row. -/
  idle_no_wcall : ∀ id, id ∉ c.F → (c.procs id).input = none → ∀ r, (w r).called id = false
  /-- I23 : a `GBCA_r`-side residue analogous to `flip_alock` (I21), but keyed on an
  honest process's own round-`r` progress rather than round `r`'s coin: once an honest process
  has reached (or passed) the "done with `GBCA_r`" point, round `r` is either already graded or
  a `DissentResidue` certifies why not. Established at the `retG` row (the genuine GBCA return
  guards `retA`/`retB`/`retC`); preserved elsewhere because the conclusion is permanent and the
  hypothesis's round/phase progression only ever moves forward into the `r < round` disjunct. -/
  retg_residue : ∀ r id, id ∉ c.F →
    (((c.procs id).round = r ∧
        ((c.procs id).phase = .toCallW ∨ (c.procs id).phase = .awaitW)) ∨
      r < (c.procs id).round) →
    (g r).grade ≠ none ∨ DissentResidue P g c r
  /-- I24 : an honest `WCC_r` caller inherits `retg_residue`'s conclusion outright
  (it called `GBCA_r` and reached `toCallW`/`awaitW` in the same handshake). Established at the
  `callW` row from `retg_residue`; preserved trivially (conclusion permanent, `fail` shrinks the
  quantifier). Feeds `flip_alock`'s flip-row establishment via the threshold's honest caller. -/
  wcalled_residue : ∀ r id, id ∉ c.F → (w r).called id = true →
    (g r).grade ≠ none ∨ DissentResidue P g c r
  /-- I25 : every bound round permanently retains its firing quorum (`bindUnset`'s
  guard, monotone under later call-growth and `F`-growth). Transfers to the abstract's
  rule-3/4 quorum guard via `abstract_quorum`. -/
  bound_quorum : ∀ r, (g r).dead ≠ ∅ → (g r).quorum P
  /-- I26 (D13) : every bound round's surviving value carries a permanent `f + 1`
  input-or-`F` support pool — the concrete mirror of TS 1's V-P1 `SuppOK`.
  Established at the `bindUnset` row from the D15 count guard (round 0
  wholesale via `input_g0_perm`; `r ≥ 1` through `call_prov` and the previous
  round's pools); preserved everywhere by monotonicity. -/
  bind_supp : ∀ r v, (!v) ∈ (g r).dead → InputSupp P c v
  /-- I27 (D13) : a `C`-locked round retains the `retC` guards themselves — `f + 1`
  F-blind support for *each* bit, in `SuppOK` shape. Both `call` and `F` only grow, so
  the counts are permanent. Established at the `retC` row; preserved everywhere by
  monotonicity. `supp_of_call_count` reads them back as input pools, and they are what
  keeps a `C`-lock incompatible with an `A`-lock below it or with an agreeing coin
  underneath it. -/
  clock_supp : ∀ r b, (g r).grade = some false →
    P.f + 1 ≤ (Finset.univ.filter
      (fun id => (g r).call id = some b ∨ id ∈ (g r).F)).card
  /-- I28 : every kill's D15 guard is permanent — a dead bit's spared rival
  keeps `f + 1` F-blind call support at that round (`call` and `F` only grow).
  Established at the `bindUnset` row verbatim from its guard; harvesting it
  (`GBCA.exists_honest_caller`) recovers an honest caller of the spared bit
  from any residue, which is what pins values past a burn. -/
  dead_supp : ∀ r b, b ∈ (g r).dead →
    P.f + 1 ≤ (Finset.univ.filter
      (fun id => (g r).call id = some (!b) ∨ id ∈ (g r).F)).card
  /-- I29 : honest holders of round `r`'s outcome agree, unless the round is
  C-locked. This is the state residue of the order argument "two opposite
  value-bearing returns cannot both fire" — the first pins the rival bit dead,
  the second's liveness guard then fails — which the exclusion set alone
  forgets once the round burns. -/
  carrier_agree : ∀ r id id' v v', id ∉ c.F → id' ∉ c.F →
    Carrier P g c r id v → Carrier P g c r id' v' →
    v = v' ∨ (g r).grade = some false
  /-- I30 : honest `A`-decision holders agree globally, across rounds. The
  pairwise residue of Graded Agreement plus A-lock commitment; each new holder
  is compared at its `retG` row, where the fresh return's live pair meets the
  existing holder's certificate. -/
  alock_agree : ∀ i j b b', i ∉ c.F → j ∉ c.F →
    AHolder P c i b → AHolder P c j b' → b = b'

/-- The core simulation relation (pre-`diracRel`): the concrete invariant
plus the abstract-twin constraints. -/
def coreR (P : Params) (s : LayeredSpecState P) (a : SpecState P.n) : Prop :=
  Inv P s.1 s.aba s.wcc ∧ Abs P s.1 s.aba s.wcc a

/-- The GBCA quorum guard is monotone: enlarging `F` and preserving non-`⊥` calls only
enlarges the counted union `{honest callers} ∪ F`. -/
theorem GBCA.SpecState.quorum_mono {P : Params} {s s' : GBCA.SpecState P.n}
    (hF : s.F ⊆ s'.F) (hcall : ∀ id, s.call id ≠ none → s'.call id ≠ none)
    (h : s.quorum P) : s'.quorum P := by
  refine le_trans h (Finset.card_le_card ?_)
  intro x hx
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  rcases hx with ⟨hxF, hxc⟩ | hxF
  · by_cases h' : x ∈ s'.F
    · exact Or.inr h'
    · exact Or.inl ⟨h', hcall x hxc⟩
  · exact Or.inr (hF hxF)

/-- The GBCA quorum guard depends only on `F` and `call`. -/
theorem GBCA.SpecState.quorum_of_eq {P : Params} {s s' : GBCA.SpecState P.n}
    (hF : s'.F = s.F) (hcall : s'.call = s.call) (h : s.quorum P) : s'.quorum P := by
  unfold GBCA.SpecState.quorum at h ⊢; rw [hF, hcall]; exact h

/-- **Witness harvest (D15)**: the SuppOK-form support count (`f + 1` callers-or-`F`)
plus the `F` budget recover an honest caller *at fire time* — the in-state honest witness
the pre-repair guards carried directly (at most `f` of the `f + 1` are `F`-members). -/
theorem GBCA.exists_honest_caller {P : Params} {s : GBCA.SpecState P.n} {b : Bool}
    (hw : P.f + 1 ≤ (Finset.univ.filter (fun id => s.call id = some b ∨ id ∈ s.F)).card)
    (hF : s.F.card ≤ P.f) :
    ∃ id, id ∉ s.F ∧ s.call id = some b := by
  by_contra hc
  push Not at hc
  have hsub : (Finset.univ.filter (fun id => s.call id = some b ∨ id ∈ s.F)) ⊆ s.F := by
    intro id hid
    rw [Finset.mem_filter] at hid
    rcases hid.2 with h | h
    · by_contra hne; exact hc id hne h
    · exact h
  have := Finset.card_le_card hsub
  omega

/-- The `SuppOK`-shape count is monotone in `call` and in `F`: both only ever grow along a
run, so every established support count is permanent. -/
theorem GBCA.callSupp_mono {P : Params} {s s' : GBCA.SpecState P.n} {b : Bool}
    (hcall : ∀ id, s.call id = some b → s'.call id = some b) (hF : s.F ⊆ s'.F)
    (h : P.f + 1 ≤ (Finset.univ.filter (fun id => s.call id = some b ∨ id ∈ s.F)).card) :
    P.f + 1 ≤ (Finset.univ.filter (fun id => s'.call id = some b ∨ id ∈ s'.F)).card := by
  refine le_trans h (Finset.card_le_card ?_)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact hx.imp (hcall x) (fun h' => hF h')

/-- **Quorum transfer** : a bound concrete round's firing quorum (`Inv.bound_quorum`)
transfers to the abstract's quorum guard, for any abstract `F`/`call` that agrees with `c.F`
and is non-`⊥` on every honest process holding a committed external input. Stated on raw
`aF`/`aCall` so it also serves the banked abstract at the `callABA` burst. -/
theorem abstract_quorum_of_call {P : Params} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P} {w : ℕ → WCC.SpecState P.n} {aF : Finset (Fin P.n)}
    {aCall : Fin P.n → Option Bool} (hI : Inv P g c w) (haF : aF = c.F)
    (hcall : ∀ id, id ∉ c.F → (c.procs id).input ≠ none → aCall id ≠ none)
    {r : ℕ} (hr : (g r).dead ≠ ∅) :
    P.n - P.f ≤ ((Finset.univ.filter (fun id => id ∉ aF ∧ aCall id ≠ none)) ∪ aF).card := by
  refine le_trans (hI.bound_quorum r hr) (Finset.card_le_card ?_)
  intro x hx
  have hFgr : (g r).F = c.F := hI.F_g r
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  rcases hx with ⟨hxF, hxc⟩ | hxF
  · have hxc' : x ∉ c.F := hFgr ▸ hxF
    exact Or.inl ⟨by rw [haF]; exact hxc', hcall x hxc' (hI.input_called r x hxc' hxc)⟩
  · exact Or.inr (by rw [haF, ← hFgr]; exact hxF)

/-- **Pool establishment (D13).** A D15 count over round-`r` calls (`f + 1`
callers-or-`F` of `b`) yields the permanent input-or-`F` pool for `b`: wholesale via
`input_g0_perm` at round `0`; at `r ≥ 1` by harvesting one honest caller, whose
`call_prov` provenance routes either through the previous round's `bind_supp` (the bit is
that round's surviving bit) or through its `clock_supp` count, which is a smaller instance
of the very same statement. Serves both the `bindUnset` (`b` = the surviving bit) and `retC`
(`b` = either bit) establishment sites. -/
theorem Inv.supp_of_call_count {P : Params} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P} {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) :
    ∀ r (b : Bool), P.f + 1 ≤ (Finset.univ.filter
      (fun id => (g r).call id = some b ∨ id ∈ (g r).F)).card → InputSupp P c b := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro b hw
    rcases Nat.eq_zero_or_eq_succ_pred r with hr0 | hrs
    · subst hr0
      refine le_trans hw (Finset.card_le_card ?_)
      intro id hid
      rw [Finset.mem_filter] at hid ⊢
      refine ⟨Finset.mem_univ id, ?_⟩
      rcases hid.2 with hcall | hF
      · exact hI.input_g0_perm id b hcall
      · exact Or.inr (by rw [← hI.F_g 0]; exact hF)
    · obtain ⟨id0, hid0F, hcall0⟩ :=
        GBCA.exists_honest_caller hw (by rw [hI.F_g r]; exact hI.F_card)
      have hid0F' : id0 ∉ c.F := (hI.F_g r) ▸ hid0F
      rw [hrs] at hcall0
      rcases hI.call_prov (r - 1) id0 b hid0F' hcall0 with hbind | ⟨hgf, -⟩
      · exact hI.bind_supp (r - 1) b hbind
      · exact ih (r - 1) (by omega) b (hI.clock_supp (r - 1) b hgf)

/-- **Both-bit support forces a `C`-lock below.** `f + 1` F-blind supporters of *each* bit at
round `r + 1` yield honest callers of both bits there (`exists_honest_caller`); they are
opposite-valued holders of round `r`'s outcome, which `carrier_agree` only admits at a
`C`-locked round. -/
theorem Inv.c_chain_of_both_supports {P : Params} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P} {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ)
    (hwT : P.f + 1 ≤ (Finset.univ.filter
      (fun id' => (g (r + 1)).call id' = some true ∨ id' ∈ (g (r + 1)).F)).card)
    (hwF : P.f + 1 ≤ (Finset.univ.filter
      (fun id' => (g (r + 1)).call id' = some false ∨ id' ∈ (g (r + 1)).F)).card) :
    (g r).grade = some false := by
  obtain ⟨idT, hidTF, hcallT⟩ :=
    GBCA.exists_honest_caller hwT (by rw [hI.F_g (r + 1)]; exact hI.F_card)
  obtain ⟨idF, hidFF, hcallF⟩ :=
    GBCA.exists_honest_caller hwF (by rw [hI.F_g (r + 1)]; exact hI.F_card)
  rcases hI.carrier_agree r idT idF true false ((hI.F_g (r + 1)) ▸ hidTF)
      ((hI.F_g (r + 1)) ▸ hidFF) (Or.inl hcallT) (Or.inl hcallF) with h | h
  · exact absurd h (by simp)
  · exact h

/-- **No `A`-lock below both-bit support.** An `A`-lock at `r₀ < r` commits every honest
round-`r` caller to `b₀` (`a_commit`), so `f + 1` F-blind support for *each* bit at round `r`
— which produces honest callers of both bits — is impossible. -/
theorem Inv.no_alock_below_both_supports {P : Params} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P} {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ)
    (hwT : P.f + 1 ≤ (Finset.univ.filter
      (fun id' => (g r).call id' = some true ∨ id' ∈ (g r).F)).card)
    (hwF : P.f + 1 ≤ (Finset.univ.filter
      (fun id' => (g r).call id' = some false ∨ id' ∈ (g r).F)).card)
    (r₀ : ℕ) (b₀ : Bool) (hlt : r₀ < r)
    (hg₀ : (g r₀).grade = some true)
    (hb₀ : (!b₀) ∈ (g r₀).dead ∧ b₀ ∉ (g r₀).dead) : False := by
  obtain ⟨-, h2, -⟩ := hI.a_commit r₀ b₀ hg₀ hb₀
  obtain ⟨idT, hidTF, hcallT⟩ :=
    GBCA.exists_honest_caller hwT (by rw [hI.F_g r]; exact hI.F_card)
  obtain ⟨idF, hidFF, hcallF⟩ :=
    GBCA.exists_honest_caller hwF (by rw [hI.F_g r]; exact hI.F_card)
  have eT := h2 r idT true hlt ((hI.F_g r) ▸ hidTF) hcallT
  have eF := h2 r idF false hlt ((hI.F_g r) ▸ hidFF) hcallF
  rw [← eT] at eF; simp at eF

/-- **An agreeing coin blocks the next round's `C`-lock.** Once round `r`'s coin has resolved
to `.bit v` and `!v` is not round `r`'s surviving bit, `call_prov` pins every honest
round-`(r + 1)` caller to `v`: both provenance disjuncts name `v`. So `f + 1` F-blind support
for `!v` at round `r + 1` — which a `C`-return there requires — cannot exist. -/
theorem Inv.no_cgrade_succ_of_supp {P : Params} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P} {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ) (v : Bool)
    (hcoin : (w r).val = .bit v)
    (hbnd : v ∉ (g r).dead)
    (hwNv : P.f + 1 ≤ (Finset.univ.filter
      (fun id' => (g (r + 1)).call id' = some (!v) ∨ id' ∈ (g (r + 1)).F)).card) :
    False := by
  obtain ⟨id0, hid0F, hcall0⟩ :=
    GBCA.exists_honest_caller hwNv (by rw [hI.F_g (r + 1)]; exact hI.F_card)
  rcases hI.call_prov r id0 (!v) ((hI.F_g (r + 1)) ▸ hid0F) hcall0 with hb | ⟨-, hw0⟩
  · simp only [Bool.not_not] at hb; exact hbnd hb
  · rcases hw0 with hh | hh <;> rw [hcoin] at hh <;> simp at hh

/-- The `Inv`-level reading of `no_cgrade_succ_of_supp`, through the `retC` guards a
`C`-locked round retains (`clock_supp`). -/
theorem Inv.no_cgrade_succ {P : Params} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P} {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ) (v : Bool)
    (hcoin : (w r).val = .bit v)
    (hbnd : v ∉ (g r).dead)
    (hgf : (g (r + 1)).grade = some false) : False :=
  hI.no_cgrade_succ_of_supp r v hcoin hbnd (hI.clock_supp (r + 1) (!v) hgf)

/-! ### Initial states -/

/-- The initial hybrid state satisfies the invariant. -/
theorem Inv.initial (P : Params) :
    Inv P (fun _ => GBCA.SpecState.initial P.n) (ABAState.initial P)
      (fun _ => WCC.SpecState.initial P.n) where
  F_g := fun _ => rfl
  F_w := fun _ => rfl
  F_card := by simp [ABAState.initial]
  input_g0 := fun id b _ h => absurd h (by simp [GBCA.SpecState.initial])
  input_called := fun _ _ _ h => absurd rfl h
  phase_input := fun id _ h => absurd (by simp [ABAState.initial] :
    ((ABAState.initial P).procs id).phase = .idle) h
  down_closed := fun _ h => h.elim (fun h' => absurd rfl h')
    (fun h' => absurd h' (by simp [GBCA.SpecState.initial]))
  quiescent := ⟨0, fun _ _ h => h.elim (fun h' => h' rfl)
    (fun h' => absurd h' (by simp [GBCA.SpecState.initial]))⟩
  w_bound := fun _ h => absurd rfl h
  recv_sound := fun i j b h => absurd h (by simp [ABAState.initial])
  decided_src := fun id b _ h => absurd h (by simp [ABAState.initial])
  a_commit := fun r b hg => absurd hg (by simp [GBCA.SpecState.initial])
  round_bound := fun id _ r h => absurd h (by simp [ABAState.initial])
  agree_locked := fun r v _ hb => absurd hb (by simp [GBCA.SpecState.initial])
  gradeA_needs_bind := fun r h => absurd h (by simp [GBCA.SpecState.initial])
  call_round := fun r id _ h => absurd h (by simp [GBCA.SpecState.initial])
  w_called := fun r id _ h => absurd h (by simp [WCC.SpecState.initial])
  round_flip := fun r id _ h => absurd h (by simp [ABAState.initial])
  est0 := fun id _ _ _ => by simp [ABAState.initial]
  grade_A_src := fun id b h => absurd h (by simp [ABAState.initial])
  est_ret := fun r id _ _ hphase => absurd hphase (by simp [ABAState.initial])
  bind_succ := fun r v h => absurd h (by simp [GBCA.SpecState.initial])
  call_prov := fun r id v _ h => absurd h (by simp [GBCA.SpecState.initial])
  est_prev := fun r id _ hround _ _ _ => by simp [ABAState.initial] at hround
  c_chain := fun r h => absurd h (by simp [GBCA.SpecState.initial])
  est_prev_ne := fun id _ hround _ => absurd (by simp [ABAState.initial] :
    ((ABAState.initial P).procs id).round = 0) hround
  w_order := fun r h => absurd h (by simp [WCC.SpecState.initial])
  input_g0_perm := fun id b h => absurd h (by simp [GBCA.SpecState.initial])
  w_call_round := fun r id _ h => absurd h (by simp [WCC.SpecState.initial])
  flip_alock := fun r h => absurd h (by simp [WCC.SpecState.initial])
  idle_no_wcall := fun id _ _ r => by simp [WCC.SpecState.initial]
  retg_residue := fun r id _ h => absurd h (by
    simp [ABAState.initial])
  wcalled_residue := fun r id _ h => absurd h (by simp [WCC.SpecState.initial])
  bound_quorum := fun r h => (h (by simp [GBCA.SpecState.initial])).elim
  bind_supp := fun r v h => absurd h (by simp [GBCA.SpecState.initial])
  clock_supp := fun r b hg => absurd hg (by simp [GBCA.SpecState.initial])
  dead_supp := fun r b h => absurd h (by simp [GBCA.SpecState.initial])
  carrier_agree := fun r id id' v v' _ _ hcar _ => by
    rcases hcar with hcall | ⟨hest, -⟩
    · exact absurd hcall (by simp [GBCA.SpecState.initial])
    · exact absurd hest (by simp [ABAState.initial])
  alock_agree := fun i j b b' _ _ h _ => by
    rcases h with h | h
    · exact absurd h (by simp [ABAState.initial])
    · exact absurd h (by simp [ABAState.initial])

/-- The initial abstract state is a lazy twin of the initial hybrid state. -/
theorem Abs.initial (P : Params) :
    Abs P (fun _ => GBCA.SpecState.initial P.n) (ABAState.initial P)
      (fun _ => WCC.SpecState.initial P.n) (SpecState.initial P.n) where
  F_eq := rfl
  ret_eq := fun _ => rfl
  coin_bot := rfl
  phase := Or.inl ⟨rfl, rfl, fun _ => rfl,
    fun id b h => absurd h (by simp [ABAState.initial])⟩

end ABA
end PLTS
