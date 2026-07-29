/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Hybrid
import Leslie2Protocols.ABA.GBCASafety

/-!
# The core-simulation relation: the lazy abstract twin

The relation and invariant for `coreSim : hybridSpec ⊑ ABA.spec`, following
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
-/

open Stream'

namespace PLTS
namespace ABA

variable {P : Params}

/-- Concrete hybrid state components: the GBCA spec family, the coordinator,
the WCC spec family. -/
abbrev HState (P : Params) : Type :=
  (ℕ → GBCA.SpecState P.n) × (CoreState P.n × (ℕ → WCC.SpecState P.n))

/-- The last-bound-round reading of a family: round `r`'s exclusion set is non-empty
and round `r + 1`'s is still empty.
Concrete-only; used by `Inv.agree_locked` (I3a). -/
def IsLastBound (g : ℕ → GBCA.SpecState P.n) (r : ℕ) : Prop :=
  (g r).dead ≠ ∅ ∧ (g (r + 1)).dead = ∅

/-- An honest-side holder of round `r`'s outcome bit `v`: a round-`(r + 1)`
GBCA call, or a committed estimate between round `r`'s `retG` and round
`(r + 1)`'s. Honesty is *not* part of the predicate; the clauses that consume
it (`Inv.carrier_agree`, `ACommit`) add it. -/
def Carrier (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : CoreState P.n)
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
def ACommit (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : CoreState P.n)
    (r : ℕ) (b : Bool) : Prop :=
  (∀ r' b', r ≤ r' → (!b') ∈ (g r').dead ∧ b' ∉ (g r').dead → b' = b) ∧
  (∀ r' id b', r < r' → id ∉ c.F → (g r').call id = some b' → b' = b) ∧
  (∀ id, id ∉ c.F → r < (c.procs id).round → (c.procs id).est = some b) ∧
  (∀ id v, id ∉ c.F → Carrier P g c r id v → v = b)

/-- The full `A`-certificate: an `A`-locked round whose surviving bit at lock
time was `b` (the permanent residue `!b ∈ dead`), together with the round's
permanent commitments. -/
def ACert (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : CoreState P.n)
    (r : ℕ) (b : Bool) : Prop :=
  (g r).grade = some true ∧ (!b) ∈ (g r).dead ∧ ACommit P g c r b

/-- A process-side holder of an `A`-decision for `b`: a live `A`-grade or a
pooled DECIDED multicast. -/
def AHolder (P : Params) (c : CoreState P.n) (id : Fin P.n) (b : Bool) : Prop :=
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
structure Abs (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : CoreState P.n)
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
def DissentResidue (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : CoreState P.n)
    (r : ℕ) : Prop :=
  ∃ v, (!v) ∈ (g r).dead ∧
    (if r = 0 then ∃ id', (c.procs id').input = some (!v)
     else v ∈ (g (r - 1)).dead ∨ (g (r - 1)).grade = some false)

/-- `DissentResidue` transports along any frame that agrees on `g`'s exclusion set at
`r`/`r - 1`, `g`'s grade at `r - 1`, and every honest input (the shape every `Inv.step_*`
row's frame facts already provide for their own row; the `r = 0` branch only needs the input
equality, the `r ≥ 1` branch only the exclusion-set/grade ones). -/
theorem DissentResidue.transport {P : Params} {g₀ g : ℕ → GBCA.SpecState P.n}
    {c₀ c : CoreState P.n} {r : ℕ}
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
def InputSupp (P : Params) (c : CoreState P.n) (v : Bool) : Prop :=
  P.f + 1 ≤ (Finset.univ.filter
    (fun id => (c.procs id).input = some v ∨ id ∈ c.F)).card

/-- `InputSupp` is monotone under input growth and `F` growth. -/
theorem InputSupp.mono {P : Params} {c c' : CoreState P.n} {v : Bool}
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
    {c c' : CoreState P.n} {r : ℕ} {b : Bool}
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
    {c c' : CoreState P.n} {r : ℕ} {b : Bool}
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
def AbsFrame (P : Params) (g g' : ℕ → GBCA.SpecState P.n) (c c' : CoreState P.n) : Prop :=
  (∀ r0 b0, ACert P g c r0 b0 → ∃ r1, ACert P g' c' r1 b0) ∧
  (∀ v, (∃ r1, ACert P g c r1 v) →
    (∀ j0 b0', j0 ∉ c.F → AHolder P c j0 b0' → b0' = v) →
    ∀ j b', j ∉ c'.F → AHolder P c' j b' → b' = v)

/-- The identity `AbsFrame`, for rows that touch neither `g`-certificates nor holders. -/
theorem AbsFrame.refl (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : CoreState P.n) :
    AbsFrame P g g c c :=
  ⟨fun r0 _ hc => ⟨r0, hc⟩, fun _ _ hpin => hpin⟩

/-! ### Inv: the concrete invariant (I1–I7) -/

/-- The concrete invariant of `hybridSpec`-reachable states. All conjuncts are
about the concrete `(g, c, w)` only. -/
structure Inv (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : CoreState P.n)
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
  `CoreStep.retG`'s `out`/`bound` are synchronised with the genuine `GBCA` return guards
  (`retA`/`retB`/`retC`) regardless of `id`'s corruption, and this is needed corruption-free
  in `step_retW`'s `recv_sound`/`decided_src` rows, which have no honesty hypothesis. -/
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
def coreR (P : Params) (s : HState P) (a : SpecState P.n) : Prop :=
  Inv P s.1 s.2.1 s.2.2 ∧ Abs P s.1 s.2.1 s.2.2 a

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
    {c : CoreState P.n} {w : ℕ → WCC.SpecState P.n} {aF : Finset (Fin P.n)}
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
    {c : CoreState P.n} {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) :
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
    {c : CoreState P.n} {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ)
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
    {c : CoreState P.n} {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ)
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
    {c : CoreState P.n} {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ) (v : Bool)
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
    {c : CoreState P.n} {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ) (v : Bool)
    (hcoin : (w r).val = .bit v)
    (hbnd : v ∉ (g r).dead)
    (hgf : (g (r + 1)).grade = some false) : False :=
  hI.no_cgrade_succ_of_supp r v hcoin hbnd (hI.clock_supp (r + 1) (!v) hgf)

/-! ### Initial states -/

/-- The initial hybrid state satisfies the invariant. -/
theorem Inv.initial (P : Params) :
    Inv P (fun _ => GBCA.SpecState.initial P.n) (CoreState.initial P.n)
      (fun _ => WCC.SpecState.initial P.n) where
  F_g := fun _ => rfl
  F_w := fun _ => rfl
  F_card := by simp [CoreState.initial]
  input_g0 := fun id b _ h => absurd h (by simp [GBCA.SpecState.initial])
  input_called := fun _ _ _ h => absurd rfl h
  phase_input := fun id _ h => absurd (by simp [CoreState.initial] :
    ((CoreState.initial P.n).procs id).phase = .idle) h
  down_closed := fun _ h => h.elim (fun h' => absurd rfl h')
    (fun h' => absurd h' (by simp [GBCA.SpecState.initial]))
  quiescent := ⟨0, fun _ _ h => h.elim (fun h' => h' rfl)
    (fun h' => absurd h' (by simp [GBCA.SpecState.initial]))⟩
  w_bound := fun _ h => absurd rfl h
  recv_sound := fun i j b h => absurd h (by simp [CoreState.initial])
  decided_src := fun id b _ h => absurd h (by simp [CoreState.initial])
  a_commit := fun r b hg => absurd hg (by simp [GBCA.SpecState.initial])
  round_bound := fun id _ r h => absurd h (by simp [CoreState.initial])
  agree_locked := fun r v _ hb => absurd hb (by simp [GBCA.SpecState.initial])
  gradeA_needs_bind := fun r h => absurd h (by simp [GBCA.SpecState.initial])
  call_round := fun r id _ h => absurd h (by simp [GBCA.SpecState.initial])
  w_called := fun r id _ h => absurd h (by simp [WCC.SpecState.initial])
  round_flip := fun r id _ h => absurd h (by simp [CoreState.initial])
  est0 := fun id _ _ _ => by simp [CoreState.initial]
  grade_A_src := fun id b h => absurd h (by simp [CoreState.initial])
  est_ret := fun r id _ _ hphase => absurd hphase (by simp [CoreState.initial])
  bind_succ := fun r v h => absurd h (by simp [GBCA.SpecState.initial])
  call_prov := fun r id v _ h => absurd h (by simp [GBCA.SpecState.initial])
  est_prev := fun r id _ hround _ _ _ => by simp [CoreState.initial] at hround
  c_chain := fun r h => absurd h (by simp [GBCA.SpecState.initial])
  est_prev_ne := fun id _ hround _ => absurd (by simp [CoreState.initial] :
    ((CoreState.initial P.n).procs id).round = 0) hround
  w_order := fun r h => absurd h (by simp [WCC.SpecState.initial])
  input_g0_perm := fun id b h => absurd h (by simp [GBCA.SpecState.initial])
  w_call_round := fun r id _ h => absurd h (by simp [WCC.SpecState.initial])
  flip_alock := fun r h => absurd h (by simp [WCC.SpecState.initial])
  idle_no_wcall := fun id _ _ r => by simp [WCC.SpecState.initial]
  retg_residue := fun r id _ h => absurd h (by
    simp [CoreState.initial])
  wcalled_residue := fun r id _ h => absurd h (by simp [WCC.SpecState.initial])
  bound_quorum := fun r h => (h (by simp [GBCA.SpecState.initial])).elim
  bind_supp := fun r v h => absurd h (by simp [GBCA.SpecState.initial])
  clock_supp := fun r b hg => absurd hg (by simp [GBCA.SpecState.initial])
  dead_supp := fun r b h => absurd h (by simp [GBCA.SpecState.initial])
  carrier_agree := fun r id id' v v' _ _ hcar _ => by
    rcases hcar with hcall | ⟨hest, -⟩
    · exact absurd hcall (by simp [GBCA.SpecState.initial])
    · exact absurd hest (by simp [CoreState.initial])
  alock_agree := fun i j b b' _ _ h _ => by
    rcases h with h | h
    · exact absurd h (by simp [CoreState.initial])
    · exact absurd h (by simp [CoreState.initial])

/-- The initial abstract state is a lazy twin of the initial hybrid state. -/
theorem Abs.initial (P : Params) :
    Abs P (fun _ => GBCA.SpecState.initial P.n) (CoreState.initial P.n)
      (fun _ => WCC.SpecState.initial P.n) (SpecState.initial P.n) where
  F_eq := rfl
  ret_eq := fun _ => rfl
  coin_bot := rfl
  phase := Or.inl ⟨rfl, rfl, fun _ => rfl,
    fun id b h => absurd h (by simp [CoreState.initial])⟩

/-! ### Stage A: step inversion for `hybridSpec` -/

/-- `hybridSpec` inversion, `callABA`: both spec families idle (Dirac self-loop on a
label outside their round-owned API), the core genuinely steps. -/
theorem hybrid_step_callABA (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : CoreState P.n)
    (w : ℕ → WCC.SpecState P.n) (id : Fin P.n) (b : Bool) (μ : PMF (HState P)) :
    (hybridSpec P).step (g, (c, w)) (.callABA id b) μ ↔
      ∃ μc, CoreStep P c (.callABA id b) μc ∧
        μ = prodPMF (PMF.pure g) (prodPMF μc (PMF.pure w)) := by
  have hnotmem : Lab.callABA id b ∉ Lab.hiddenAPI P.n := Lab.callABA_not_mem_hiddenAPI id b
  have hnottau : Lab.callABA id b ≠ Silent.τ := by simp
  unfold hybridSpec context GBCA.specFamily WCC.specFamily
  rw [System.abstract_step]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, hstep⟩)
    · exact absurd h hnottau
    · rw [System.parallel_step] at hstep
      rcases hstep with ⟨-, μ1, μ2, h1, h2, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
      · rw [System.family_step_iff] at h1
        simp only [Lab.gbcaRound, Lab.isFail] at h1
        rcases h1 with ⟨hτ, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
        · exact absurd hτ hnottau
        · exact absurd hr (by simp)
        · exact hglob.elim
        · rw [System.parallel_step] at h2
          rcases h2 with ⟨-, μc, μw, hc, hw, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
          · rw [System.family_step_iff] at hw
            simp only [Lab.wccRound, Lab.isFail] at hw
            rcases hw with ⟨hτ, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
            · exact absurd hτ hnottau
            · exact absurd hr (by simp)
            · exact hglob.elim
            · exact ⟨μc, hc, rfl⟩
          · exact absurd hτ hnottau
          · exact absurd hτ hnottau
      · exact absurd hτ hnottau
      · exact absurd hτ hnottau
  · rintro ⟨μc, hc, rfl⟩
    refine Or.inr ⟨hnotmem, ?_⟩
    rw [System.parallel_step]
    refine Or.inl ⟨hnottau, PMF.pure g, prodPMF μc (PMF.pure w), ?_, ?_, rfl⟩
    · rw [System.family_step_iff]
      exact Or.inr (Or.inr (Or.inr ⟨hnottau, rfl, by simp [Lab.isFail], rfl⟩))
    · rw [System.parallel_step]
      refine Or.inl ⟨hnottau, μc, PMF.pure w, hc, ?_, rfl⟩
      rw [System.family_step_iff]
      exact Or.inr (Or.inr (Or.inr ⟨hnottau, rfl, by simp [Lab.isFail], rfl⟩))

/-- `hybridSpec` inversion, `retABA`: both spec families idle, the core genuinely steps. -/
theorem hybrid_step_retABA (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : CoreState P.n)
    (w : ℕ → WCC.SpecState P.n) (id : Fin P.n) (b : Bool) (μ : PMF (HState P)) :
    (hybridSpec P).step (g, (c, w)) (.retABA id b) μ ↔
      ∃ μc, CoreStep P c (.retABA id b) μc ∧
        μ = prodPMF (PMF.pure g) (prodPMF μc (PMF.pure w)) := by
  have hnotmem : Lab.retABA id b ∉ Lab.hiddenAPI P.n := Lab.retABA_not_mem_hiddenAPI id b
  have hnottau : Lab.retABA id b ≠ Silent.τ := by simp
  unfold hybridSpec context GBCA.specFamily WCC.specFamily
  rw [System.abstract_step]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, hstep⟩)
    · exact absurd h hnottau
    · rw [System.parallel_step] at hstep
      rcases hstep with ⟨-, μ1, μ2, h1, h2, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
      · rw [System.family_step_iff] at h1
        simp only [Lab.gbcaRound, Lab.isFail] at h1
        rcases h1 with ⟨hτ, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
        · exact absurd hτ hnottau
        · exact absurd hr (by simp)
        · exact hglob.elim
        · rw [System.parallel_step] at h2
          rcases h2 with ⟨-, μc, μw, hc, hw, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
          · rw [System.family_step_iff] at hw
            simp only [Lab.wccRound, Lab.isFail] at hw
            rcases hw with ⟨hτ, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
            · exact absurd hτ hnottau
            · exact absurd hr (by simp)
            · exact hglob.elim
            · exact ⟨μc, hc, rfl⟩
          · exact absurd hτ hnottau
          · exact absurd hτ hnottau
      · exact absurd hτ hnottau
      · exact absurd hτ hnottau
  · rintro ⟨μc, hc, rfl⟩
    refine Or.inr ⟨hnotmem, ?_⟩
    rw [System.parallel_step]
    refine Or.inl ⟨hnottau, PMF.pure g, prodPMF μc (PMF.pure w), ?_, ?_, rfl⟩
    · rw [System.family_step_iff]
      exact Or.inr (Or.inr (Or.inr ⟨hnottau, rfl, by simp [Lab.isFail], rfl⟩))
    · rw [System.parallel_step]
      refine Or.inl ⟨hnottau, μc, PMF.pure w, hc, ?_, rfl⟩
      rw [System.family_step_iff]
      exact Or.inr (Or.inr (Or.inr ⟨hnottau, rfl, by simp [Lab.isFail], rfl⟩))

/-- `hybridSpec` inversion, `fail`: a genuine synchronisation of all three components,
each applying its own corruption transform. -/
theorem hybrid_step_fail (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : CoreState P.n)
    (w : ℕ → WCC.SpecState P.n) (id : Fin P.n) (μ : PMF (HState P)) :
    (hybridSpec P).step (g, (c, w)) (.fail id) μ ↔
      μ = prodPMF (PMF.pure (fun r => (g r).corrupt P id))
        (prodPMF (PMF.pure (c.corrupt P id)) (PMF.pure (fun r => (w r).corrupt P id))) := by
  have hnotmem : Lab.fail id ∉ Lab.hiddenAPI P.n := Lab.fail_not_mem_hiddenAPI id
  have hnottau : Lab.fail (n := P.n) id ≠ Silent.τ := by simp
  unfold hybridSpec context GBCA.specFamily WCC.specFamily
  rw [System.abstract_step]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, hstep⟩)
    · exact absurd h hnottau
    · rw [System.parallel_step] at hstep
      rcases hstep with ⟨-, μ1, μ2, h1, h2, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
      · rw [System.family_step_iff] at h1
        simp only [Lab.gbcaRound, Lab.isFail, GBCA.failAct] at h1
        rcases h1 with ⟨hτ, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, hglob, -⟩
        · exact absurd hτ hnottau
        · exact absurd hr (by simp)
        · rw [System.parallel_step] at h2
          rcases h2 with ⟨-, μc, μw, hc, hw, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
          · rw [core_step, coreStep_fail_iff] at hc
            rw [System.family_step_iff] at hw
            simp only [Lab.wccRound, Lab.isFail, WCC.failAct] at hw
            rcases hw with ⟨hτ, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, hglob, -⟩
            · exact absurd hτ hnottau
            · exact absurd hr (by simp)
            · rw [hc]
            · exact absurd trivial hglob
          · exact absurd hτ hnottau
          · exact absurd hτ hnottau
        · exact absurd trivial hglob
      · exact absurd hτ hnottau
      · exact absurd hτ hnottau
  · rintro rfl
    refine Or.inr ⟨hnotmem, ?_⟩
    rw [System.parallel_step]
    refine Or.inl ⟨hnottau, _, _, ?_, ?_, rfl⟩
    · rw [System.family_step_iff]
      exact Or.inr (Or.inr (Or.inl ⟨hnottau, rfl, by simp [Lab.isFail], rfl⟩))
    · rw [System.parallel_step]
      refine Or.inl ⟨hnottau, _, _, ?_, ?_, rfl⟩
      · rw [core_step, coreStep_fail_iff]
      · rw [System.family_step_iff]
        exact Or.inr (Or.inr (Or.inl ⟨hnottau, rfl, by simp [Lab.isFail], rfl⟩))

/-- `hybridSpec` inversion, `τ` (`mp`-only: preservation only needs the forward direction).
Seven sources: a genuine internal step of the GBCA family (`bindUnset`), the core, or the WCC
family; or a hidden handshake (`callG`/`retG`/`callW`/`retW`) where the owning family steps
and the core steps genuinely in sync, the other family idling. -/
theorem hybrid_step_tau (P : Params) (g : ℕ → GBCA.SpecState P.n) (c : CoreState P.n)
    (w : ℕ → WCC.SpecState P.n) (μ : PMF (HState P))
    (hstep : (hybridSpec P).step (g, (c, w)) .tau μ) :
    (∃ r μr, GBCA.Step P r (g r) .tau μr ∧
        μ = prodPMF (μr.map (Function.update g r)) (PMF.pure (c, w))) ∨
      (∃ μc, CoreStep P c .tau μc ∧
        μ = prodPMF (PMF.pure g) (prodPMF μc (PMF.pure w))) ∨
      (∃ r μw', WCC.Step P r (w r) .tau μw' ∧
        μ = prodPMF (PMF.pure g) (prodPMF (PMF.pure c) (μw'.map (Function.update w r)))) ∨
      (∃ r id b μr μc, GBCA.Step P r (g r) (.callG r id b) μr ∧
        CoreStep P c (.callG r id b) μc ∧
        μ = prodPMF (μr.map (Function.update g r)) (prodPMF μc (PMF.pure w))) ∨
      (∃ r id out μr μc, GBCA.Step P r (g r) (.retG r id out) μr ∧
        CoreStep P c (.retG r id out) μc ∧
        μ = prodPMF (μr.map (Function.update g r)) (prodPMF μc (PMF.pure w))) ∨
      (∃ r id μw' μc, WCC.Step P r (w r) (.callW r id) μw' ∧ CoreStep P c (.callW r id) μc ∧
        μ = prodPMF (PMF.pure g) (prodPMF μc (μw'.map (Function.update w r)))) ∨
      (∃ r id b μw' μc, WCC.Step P r (w r) (.retW r id b) μw' ∧
        CoreStep P c (.retW r id b) μc ∧
        μ = prodPMF (PMF.pure g) (prodPMF μc (μw'.map (Function.update w r)))) := by
  have hnottau : (Silent.τ : Lab P.n) = Lab.tau := rfl
  unfold hybridSpec context GBCA.specFamily WCC.specFamily at hstep
  rw [System.abstract_step] at hstep
  rcases hstep with ⟨-, l, hl, hstep⟩ | ⟨-, hstep⟩
  · -- hidden handshake: relabeled from a `callG`/`retG`/`callW`/`retW` step
    cases l with
    | tau => exact absurd hl (by simp)
    | callABA id b => exact absurd hl (by simp)
    | retABA id b => exact absurd hl (by simp)
    | fail id => exact absurd hl (by simp)
    | callG r id b =>
      have hlτ : Lab.callG r id b ≠ Silent.τ := by simp
      rw [System.parallel_step] at hstep
      rcases hstep with ⟨-, μ1, μ2, h1, h2, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
      · rw [System.family_step_iff] at h1
        simp only [Lab.gbcaRound, Lab.isFail] at h1
        rcases h1 with ⟨hτ, -⟩ | ⟨r', hr', μr, hr1, rfl⟩ | ⟨-, hr, -, -⟩ | ⟨-, hr, -, -⟩
        · exact absurd hτ hlτ
        · rw [Option.some.injEq] at hr'
          subst hr'
          rw [System.parallel_step] at h2
          rcases h2 with ⟨-, μc, μw, hc, hw, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
          · rw [System.family_step_iff] at hw
            simp only [Lab.wccRound, Lab.isFail] at hw
            rcases hw with ⟨hτ, -⟩ | ⟨r', hr', -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
            · exact absurd hτ hlτ
            · exact absurd hr' (by simp)
            · exact hglob.elim
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, id, b, μr, μc, hr1, hc, rfl⟩)))
          · exact absurd hτ hlτ
          · exact absurd hτ hlτ
        · exact absurd hr (by simp)
        · exact absurd hr (by simp)
      · exact absurd hτ hlτ
      · exact absurd hτ hlτ
    | retG r id out =>
      have hlτ : Lab.retG r id out ≠ Silent.τ := by simp
      rw [System.parallel_step] at hstep
      rcases hstep with ⟨-, μ1, μ2, h1, h2, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
      · rw [System.family_step_iff] at h1
        simp only [Lab.gbcaRound, Lab.isFail] at h1
        rcases h1 with ⟨hτ, -⟩ | ⟨r', hr', μr, hr1, rfl⟩ | ⟨-, hr, -, -⟩ | ⟨-, hr, -, -⟩
        · exact absurd hτ hlτ
        · rw [Option.some.injEq] at hr'
          subst hr'
          rw [System.parallel_step] at h2
          rcases h2 with ⟨-, μc, μw, hc, hw, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
          · rw [System.family_step_iff] at hw
            simp only [Lab.wccRound, Lab.isFail] at hw
            rcases hw with ⟨hτ, -⟩ | ⟨r', hr', -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
            · exact absurd hτ hlτ
            · exact absurd hr' (by simp)
            · exact hglob.elim
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨r, id, out, μr, μc, hr1, hc, rfl⟩))))
          · exact absurd hτ hlτ
          · exact absurd hτ hlτ
        · exact absurd hr (by simp)
        · exact absurd hr (by simp)
      · exact absurd hτ hlτ
      · exact absurd hτ hlτ
    | callW r id =>
      have hlτ : Lab.callW r id ≠ Silent.τ := by simp
      rw [System.parallel_step] at hstep
      rcases hstep with ⟨-, μ1, μ2, h1, h2, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
      · rw [System.family_step_iff] at h1
        simp only [Lab.gbcaRound, Lab.isFail] at h1
        rcases h1 with ⟨hτ, -⟩ | ⟨r', hr', -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
        · exact absurd hτ hlτ
        · exact absurd hr' (by simp)
        · exact hglob.elim
        · rw [System.parallel_step] at h2
          rcases h2 with ⟨-, μc, μw, hc, hw, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
          · rw [System.family_step_iff] at hw
            simp only [Lab.wccRound, Lab.isFail] at hw
            rcases hw with ⟨hτ, -⟩ | ⟨r', hr', μw', hw1, rfl⟩ | ⟨-, hr, -, -⟩ | ⟨-, hr, -, -⟩
            · exact absurd hτ hlτ
            · rw [Option.some.injEq] at hr'
              subst hr'
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨r, id, μw', μc, hw1, hc, rfl⟩)))))
            · exact absurd hr (by simp)
            · exact absurd hr (by simp)
          · exact absurd hτ hlτ
          · exact absurd hτ hlτ
      · exact absurd hτ hlτ
      · exact absurd hτ hlτ
    | retW r id b =>
      have hlτ : Lab.retW r id b ≠ Silent.τ := by simp
      rw [System.parallel_step] at hstep
      rcases hstep with ⟨-, μ1, μ2, h1, h2, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
      · rw [System.family_step_iff] at h1
        simp only [Lab.gbcaRound, Lab.isFail] at h1
        rcases h1 with ⟨hτ, -⟩ | ⟨r', hr', -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
        · exact absurd hτ hlτ
        · exact absurd hr' (by simp)
        · exact hglob.elim
        · rw [System.parallel_step] at h2
          rcases h2 with ⟨-, μc, μw, hc, hw, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
          · rw [System.family_step_iff] at hw
            simp only [Lab.wccRound, Lab.isFail] at hw
            rcases hw with ⟨hτ, -⟩ | ⟨r', hr', μw', hw1, rfl⟩ | ⟨-, hr, -, -⟩ | ⟨-, hr, -, -⟩
            · exact absurd hτ hlτ
            · rw [Option.some.injEq] at hr'
              subst hr'
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                ⟨r, id, b, μw', μc, hw1, hc, rfl⟩)))))
            · exact absurd hr (by simp)
            · exact absurd hr (by simp)
          · exact absurd hτ hlτ
          · exact absurd hτ hlτ
      · exact absurd hτ hlτ
      · exact absurd hτ hlτ
  · -- genuine `τ`: exactly one of the three components moves
    rw [System.parallel_step] at hstep
    rcases hstep with ⟨hne, -⟩ | ⟨-, μ1, h1, rfl⟩ | ⟨-, μ2, h2, rfl⟩
    · exact absurd rfl hne
    · rw [System.family_step_iff] at h1
      simp only [Lab.gbcaRound, Lab.isFail] at h1
      rcases h1 with ⟨-, r, μr, hr1, rfl⟩ | ⟨r, hr, -⟩ | ⟨hτ, -, -, -⟩ | ⟨hτ, -, -, -⟩
      · exact Or.inl ⟨r, μr, hr1, rfl⟩
      · exact absurd hr (by simp)
      · exact absurd hnottau.symm hτ
      · exact absurd hnottau.symm hτ
    · rw [System.parallel_step] at h2
      rcases h2 with ⟨hne, -⟩ | ⟨-, μc, hc, rfl⟩ | ⟨-, μw, hw, rfl⟩
      · exact absurd rfl hne
      · exact Or.inr (Or.inl ⟨μc, hc, rfl⟩)
      · rw [System.family_step_iff] at hw
        simp only [Lab.wccRound, Lab.isFail] at hw
        rcases hw with ⟨-, r, μw', hw1, rfl⟩ | ⟨r, hr, -⟩ | ⟨hτ, -, -, -⟩ | ⟨hτ, -, -, -⟩
        · exact Or.inr (Or.inr (Or.inl ⟨r, μw', hw1, rfl⟩))
        · exact absurd hr (by simp)
        · exact absurd hnottau.symm hτ
        · exact absurd hnottau.symm hτ

/-! ### Stage B: preservation of `Inv` -/

/-- WCC corruption changes only `F`. -/
theorem WCC.corrupt_val {P : Params} (id : Fin P.n) (s : WCC.SpecState P.n) :
    (s.corrupt P id).val = s.val := by unfold WCC.SpecState.corrupt; split <;> rfl

theorem WCC.corrupt_called {P : Params} (id : Fin P.n) (s : WCC.SpecState P.n) :
    (s.corrupt P id).called = s.called := by unfold WCC.SpecState.corrupt; split <;> rfl

/-- The GBCA corruption of a state agreeing with the core on `F` agrees with the core's
corruption on `F` (keeps `F_g` in lockstep across a `fail` broadcast). -/
theorem GBCA.corrupt_F_eq {P : Params} (id : Fin P.n) (s : GBCA.SpecState P.n)
    (c : CoreState P.n) (h : s.F = c.F) :
    (s.corrupt P id).F = (c.corrupt P id).F := by
  unfold GBCA.SpecState.corrupt CoreState.corrupt
  rw [h]; split_ifs <;> simp [h]

/-- The WCC corruption of a state agreeing with the core on `F` agrees with the core's
corruption on `F` (keeps `F_w` in lockstep across a `fail` broadcast). -/
theorem WCC.corrupt_F_eq {P : Params} (id : Fin P.n) (s : WCC.SpecState P.n)
    (c : CoreState P.n) (h : s.F = c.F) :
    (s.corrupt P id).F = (c.corrupt P id).F := by
  unfold WCC.SpecState.corrupt CoreState.corrupt
  rw [h]; split_ifs <;> simp [h]

/-- `retABA` only sets `returned`, a field `Inv` never inspects: `Inv` transfers verbatim
modulo the pointwise-unchanged projections of `procs`. -/
theorem Inv.step_retABA {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (id : Fin P.n) (b : Bool)
    {μc : PMF (CoreState P.n)} (hstep : CoreStep P c (.retABA id b) μc)
    {c' : CoreState P.n} (hc' : c' ∈ μc.support) :
    Inv P g c' w ∧ AbsFrame P g g c c' := by
  rw [coreStep_retABA_iff] at hstep
  obtain ⟨-, -, -, rfl⟩ := hstep
  rw [PMF.mem_support_pure_iff] at hc'
  subst hc'
  set c' := c.setProc id { c.procs id with returned := true } with hc'def
  have hF : c'.F = c.F := CoreState.setProc_F _ _ _
  have hDS : c'.decidedSent = c.decidedSent := CoreState.setProc_decidedSent _ _ _
  have hDR : c'.decidedRecv = c.decidedRecv := CoreState.setProc_decidedRecv _ _ _
  have hDC : ∀ i b', c'.decidedCount i b' = c.decidedCount i b' :=
    fun i b' => CoreState.setProc_decidedCount _ _ _ _ _
  have hInput : ∀ id', (c'.procs id').input = (c.procs id').input := by
    intro id'; by_cases h : id' = id
    · subst h; rw [hc'def, CoreState.setProc_procs_self]
    · rw [hc'def, CoreState.setProc_procs_ne _ _ _ h]
  have hEst : ∀ id', (c'.procs id').est = (c.procs id').est := by
    intro id'; by_cases h : id' = id
    · subst h; rw [hc'def, CoreState.setProc_procs_self]
    · rw [hc'def, CoreState.setProc_procs_ne _ _ _ h]
  have hRound : ∀ id', (c'.procs id').round = (c.procs id').round := by
    intro id'; by_cases h : id' = id
    · subst h; rw [hc'def, CoreState.setProc_procs_self]
    · rw [hc'def, CoreState.setProc_procs_ne _ _ _ h]
  have hPhase : ∀ id', (c'.procs id').phase = (c.procs id').phase := by
    intro id'; by_cases h : id' = id
    · subst h; rw [hc'def, CoreState.setProc_procs_self]
    · rw [hc'def, CoreState.setProc_procs_ne _ _ _ h]
  have hLastGrade : ∀ id', (c'.procs id').lastGrade = (c.procs id').lastGrade := by
    intro id'; by_cases h : id' = id
    · subst h; rw [hc'def, CoreState.setProc_procs_self]
    · rw [hc'def, CoreState.setProc_procs_ne _ _ _ h]
  have hCarr : ∀ r' id' v, Carrier P g c' r' id' v → Carrier P g c r' id' v := by
    intro r' id' v hc
    unfold Carrier at hc ⊢
    rwa [hEst, hRound, hPhase] at hc
  have hCert : ∀ r' b', ACert P g c r' b' → ACert P g c' r' b' := fun r' b' =>
    ACert.of_frame rfl (fun _ => rfl) (fun _ _ => rfl)
      (by rw [hF] : c.F ⊆ c'.F) hRound hEst (fun id0 v => hCarr r' id0 v)
  have hHold : ∀ id' b', AHolder P c' id' b' → AHolder P c id' b' := by
    intro id' b' h
    unfold AHolder at h ⊢
    rwa [hLastGrade, hDS] at h
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
    fun v _ hpin j b' hj hh => hpin j b' (hF ▸ hj) (hHold j b' hh)⟩
  refine ⟨fun r => (hI.F_g r).trans hF.symm, fun r => ?_, ?_, ?_, ?_, ?_,
    hI.down_closed, hI.quiescent, hI.w_bound, ?_, ?_, ?_, ?_, ?_,
    hI.gradeA_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.c_chain, ?_,
    hI.w_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
    fun r v hb => (hI.bind_supp r v hb).mono
      (fun id' b' h => by rw [hInput]; exact h) (fun x hx => by rw [hF]; exact hx),
    hI.clock_supp, hI.dead_supp,
    fun r' i j v v' hm hm' h h' => hI.carrier_agree r' i j v v' (hF ▸ hm) (hF ▸ hm')
      (hCarr _ _ _ h) (hCarr _ _ _ h'),
    fun i j b₀ b₀' hm hm' h h' => hI.alock_agree i j b₀ b₀' (hF ▸ hm) (hF ▸ hm')
      (hHold _ _ h) (hHold _ _ h')⟩
  · rw [hF]; exact hI.F_w r
  · rw [hF]; exact hI.F_card
  · intro id' b' hmem hcall; rw [hInput]; exact hI.input_g0 id' b' (hF ▸ hmem) hcall
  · intro r id' hmem hcall; rw [hInput]; exact hI.input_called r id' (hF ▸ hmem) hcall
  · intro id' hmem hne; rw [hPhase] at hne; rw [hInput]; exact hI.phase_input id' (hF ▸ hmem) hne
  · intro i j b' h; rw [hDR] at h; rw [hDS]; exact hI.recv_sound i j b' h
  · intro id' b' hmem h; rw [hDS] at h
    exact (hI.decided_src id' b' (hF ▸ hmem) h).imp (fun r => hCert r b')
  · intro r b' hg hb
    exact ACommit.of_frame (fun _ => rfl) (fun _ _ => rfl)
      (by rw [hF]) hRound hEst (fun id0 v => hCarr r id0 v) (hI.a_commit r b' hg hb)
  · intro id' hmem r hr; exact hI.round_bound id' (hF ▸ hmem) r (hRound id' ▸ hr)
  · intro r v hlast hb hcoin id' hmem hr
    rw [hEst]; exact hI.agree_locked r v hlast hb hcoin id' (hF ▸ hmem) (hRound id' ▸ hr)
  · intro r id' hmem hcall; rw [hRound]; exact hI.call_round r id' (hF ▸ hmem) hcall
  · intro r id' hmem hcalled; exact hI.w_called r id' (hF ▸ hmem) hcalled
  · intro r id' hmem hr; rw [hRound] at hr; exact hI.round_flip r id' (hF ▸ hmem) hr
  · intro id' hmem hround hphase
    rw [hRound] at hround; rw [hPhase] at hphase
    rw [hEst, hInput]; exact hI.est0 id' (hF ▸ hmem) hround hphase
  · intro id' b' hlg; rw [hLastGrade] at hlg
    exact (hI.grade_A_src id' b' hlg).imp (fun r => hCert r b')
  · intro r id' hmem hround hphase
    rw [hRound] at hround; rw [hPhase] at hphase
    rw [hEst]; exact hI.est_ret r id' (hF ▸ hmem) hround hphase
  · intro r id' v hmem hcall; exact hI.call_prov r id' v (hF ▸ hmem) hcall
  · intro r id' hmem hround hphase v hest
    rw [hRound] at hround; rw [hPhase] at hphase; rw [hEst] at hest
    exact hI.est_prev r id' (hF ▸ hmem) hround hphase v hest
  · intro id' hmem hround hphase
    rw [hRound] at hround; rw [hPhase] at hphase; rw [hEst]
    exact hI.est_prev_ne id' (hF ▸ hmem) hround hphase
  · intro id' b' h
    rcases hI.input_g0_perm id' b' h with hin | hf
    · left; rw [hInput]; exact hin
    · right; rw [hF]; exact hf
  · intro r id' hmem hcalled; rw [hRound]; exact hI.w_call_round r id' (hF ▸ hmem) hcalled
  · intro r h
    rcases hI.flip_alock r h with hg | hd
    · left; exact hg
    · right; exact DissentResidue.transport rfl rfl (fun hh => hh) (fun id' => hInput id') hd
  · intro id' hmem hin r'; rw [hInput] at hin; exact hI.idle_no_wcall id' (hF ▸ hmem) hin r'
  · intro r id' hmem h
    rw [hRound] at h; rw [hPhase] at h
    rcases hI.retg_residue r id' (hF ▸ hmem) h with hg | hd
    · left; exact hg
    · right; exact DissentResidue.transport rfl rfl (fun hh => hh) (fun id'' => hInput id'') hd
  · intro r id' hmem hcalled
    rcases hI.wcalled_residue r id' (hF ▸ hmem) hcalled with hg | hd
    · left; exact hg
    · right; exact DissentResidue.transport rfl rfl (fun hh => hh) (fun id'' => hInput id'') hd

/-- `callABA`: either a genuine external input (guarded by `input = none`, so `input_called`
rules out the "already called GBCA" corner) or the idle self-loop. -/
theorem Inv.step_callABA {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (id : Fin P.n) (b : Bool)
    {μc : PMF (CoreState P.n)} (hstep : CoreStep P c (.callABA id b) μc)
    {c' : CoreState P.n} (hc' : c' ∈ μc.support) :
    Inv P g c' w ∧ AbsFrame P g g c c' := by
  rw [coreStep_callABA_iff] at hstep
  rcases hstep with ⟨hin, rfl⟩ | rfl
  · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    set c' := c.setProc id { c.procs id with
      input := some b, est := some b, round := 0, phase := .toCallG } with hc'def
    have hF : c'.F = c.F := CoreState.setProc_F _ _ _
    have hDS : c'.decidedSent = c.decidedSent := CoreState.setProc_decidedSent _ _ _
    have hDR : c'.decidedRecv = c.decidedRecv := CoreState.setProc_decidedRecv _ _ _
    have hSelf : c'.procs id = { c.procs id with
        input := some b, est := some b, round := 0, phase := .toCallG } := by
      rw [hc'def]; exact CoreState.setProc_procs_self _ _ _
    have hNe : ∀ id', id' ≠ id → c'.procs id' = c.procs id' := by
      intro id' h; rw [hc'def]; exact CoreState.setProc_procs_ne _ _ _ h
    have hDissTrans : ∀ r, DissentResidue P g c r → DissentResidue P g c' r := by
      intro r hd
      obtain ⟨v, hbv, hif⟩ := hd
      refine ⟨v, hbv, ?_⟩
      by_cases h0 : r = 0
      · rw [if_pos h0] at hif ⊢
        obtain ⟨id', hid'⟩ := hif
        by_cases hidmatch : id' = id
        · exfalso; rw [hidmatch, hin] at hid'; exact absurd hid' (by simp)
        · exact ⟨id', by rw [hNe id' hidmatch]; exact hid'⟩
      · rw [if_neg h0] at hif ⊢; exact hif
    have hInMono : ∀ id' b', (c.procs id').input = some b' → (c'.procs id').input = some b' := by
      intro id' b' h
      by_cases hid : id' = id
      · exact absurd (hid ▸ h) (by rw [hin]; simp)
      · rw [hNe id' hid]; exact h
    have hCarrTrans : ∀ r' id₀ v, Carrier P g c' r' id₀ v → Carrier P g c r' id₀ v := by
      intro r' id₀ v hc
      rcases hc with h | ⟨he, hk⟩
      · exact Or.inl h
      · by_cases hid : id₀ = id
        · subst hid; exfalso; simp [hSelf] at hk
        · rw [hNe id₀ hid] at he hk
          exact Or.inr ⟨he, hk⟩
    have hCertTrans : ∀ r' b', ACert P g c r' b' → ACert P g c' r' b' := by
      rintro r' b' ⟨hg1, hd1, h1, h2, h3, h4⟩
      refine ⟨hg1, hd1, h1,
        fun r'' id'' b'' hrr hmem hcall => h2 r'' id'' b'' hrr (hF ▸ hmem) hcall,
        fun id'' hmem hr => ?_,
        fun id'' v hmem hcar => h4 id'' v (hF ▸ hmem) (hCarrTrans r' id'' v hcar)⟩
      by_cases h : id'' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id'' h] at hr ⊢; exact h3 id'' (hF ▸ hmem) hr
    have hLG : ∀ id₀, (c'.procs id₀).lastGrade = (c.procs id₀).lastGrade := by
      intro id₀; by_cases h : id₀ = id
      · subst h; simp [hSelf]
      · rw [hNe id₀ h]
    have hHold : ∀ id₀ b₀, AHolder P c' id₀ b₀ → AHolder P c id₀ b₀ := by
      intro id₀ b₀ h
      unfold AHolder at h ⊢
      rwa [hLG, hDS] at h
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hF ▸ hj) (hHold j b' hh)⟩
    refine ⟨fun r => (hI.F_g r).trans hF.symm, fun r => hF ▸ hI.F_w r, hF ▸ hI.F_card,
      ?_, ?_, ?_, hI.down_closed, hI.quiescent, hI.w_bound, ?_, ?_, ?_, ?_, ?_,
      hI.gradeA_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.c_chain, ?_,
      hI.w_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_supp r v hb).mono hInMono (fun x hx => by rw [hF]; exact hx),
      hI.clock_supp, hI.dead_supp,
      fun r' i j v v' hm hm' h h' => hI.carrier_agree r' i j v v' (hF ▸ hm) (hF ▸ hm')
        (hCarrTrans _ _ _ h) (hCarrTrans _ _ _ h'),
      fun i j b₀ b₀' hm hm' h h' => hI.alock_agree i j b₀ b₀' (hF ▸ hm) (hF ▸ hm')
        (hHold _ _ h) (hHold _ _ h')⟩
    · intro id' b' hmem hcall
      by_cases h : id' = id
      · rw [h] at hcall hmem
        have hne : (g 0).call id ≠ none := by rw [hcall]; simp
        exact absurd hin (hI.input_called 0 id (hF ▸ hmem) hne)
      · rw [hNe id' h]; exact hI.input_g0 id' b' (hF ▸ hmem) hcall
    · intro r id' hmem hcall
      by_cases h : id' = id
      · rw [h]; simp [hSelf]
      · rw [hNe id' h]; exact hI.input_called r id' (hF ▸ hmem) hcall
    · intro id' hmem hne
      by_cases h : id' = id
      · rw [h]; simp [hSelf]
      · rw [hNe id' h] at hne ⊢; exact hI.phase_input id' (hF ▸ hmem) hne
    · intro i j b' h; rw [hDR] at h; rw [hDS]; exact hI.recv_sound i j b' h
    · intro id' b' hmem h; rw [hDS] at h
      exact (hI.decided_src id' b' (hF ▸ hmem) h).imp (fun r => hCertTrans r b')
    · intro r b' hg hb
      obtain ⟨h1, h2, h3, h4⟩ := hI.a_commit r b' hg hb
      refine ⟨h1, h2, fun id' hmem hr => ?_,
        fun id0 v hmem hcar => h4 id0 v (hF ▸ hmem) (hCarrTrans r id0 v hcar)⟩
      by_cases h : id' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id' h] at hr ⊢; exact h3 id' (hF ▸ hmem) hr
    · intro id' hmem r hr
      by_cases h : id' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id' h] at hr; exact hI.round_bound id' (hF ▸ hmem) r hr
    · intro r v hlast hb hcoin id' hmem hr
      by_cases h : id' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id' h] at hr ⊢; exact hI.agree_locked r v hlast hb hcoin id' (hF ▸ hmem) hr
    · intro r id' hmem hcall
      by_cases h : id' = id
      · rw [h] at hcall hmem; exact absurd hin (hI.input_called r id (hF ▸ hmem) hcall)
      · rw [hNe id' h]; exact hI.call_round r id' (hF ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.w_called r id' (hF ▸ hmem) hcalled
    · intro r id' hmem hr
      by_cases h : id' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id' h] at hr; exact hI.round_flip r id' (hF ▸ hmem) hr
    · intro id' hmem hround hphase
      by_cases h : id' = id
      · subst h; simp [hSelf]
      · rw [hNe id' h] at hround hphase ⊢; exact hI.est0 id' (hF ▸ hmem) hround hphase
    · intro id' b' hlg
      by_cases h : id' = id
      · rw [h] at hlg; rw [hSelf] at hlg
        exact (hI.grade_A_src id b' hlg).imp (fun r => hCertTrans r b')
      · rw [hNe id' h] at hlg
        exact (hI.grade_A_src id' b' hlg).imp (fun r => hCertTrans r b')
    · intro r id' hmem hround hphase
      by_cases h : id' = id
      · subst h; simp [hSelf] at hphase
      · rw [hNe id' h] at hround hphase ⊢; exact hI.est_ret r id' (hF ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_prov r id' v (hF ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      by_cases h : id' = id
      · subst h; simp [hSelf] at hround
      · rw [hNe id' h] at hround hphase hest
        exact hI.est_prev r id' (hF ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      by_cases h : id' = id
      · subst h; simp [hSelf] at hround
      · rw [hNe id' h] at hround hphase ⊢
        exact hI.est_prev_ne id' (hF ▸ hmem) hround hphase
    · intro id' b' h
      rcases hI.input_g0_perm id' b' h with hpre | hf
      · by_cases hid : id' = id
        · rw [hid, hin] at hpre; exact absurd hpre (by simp)
        · left; rw [hNe id' hid]; exact hpre
      · right; rw [hF]; exact hf
    · -- `w_call_round`'s `id' = id` corner: `id` was just idle (`hin`), so `idle_no_wcall`
      -- rules out `id` having ever called any `WCC` instance.
      intro r id' hmem hcalled
      by_cases hid : id' = id
      · rw [hid] at hmem hcalled
        have := hI.idle_no_wcall id (hF ▸ hmem) hin r
        rw [this] at hcalled
        exact absurd hcalled (by simp)
      · rw [hNe id' hid]; exact hI.w_call_round r id' (hF ▸ hmem) hcalled
    · -- `flip_alock`: `g` is untouched entirely; the only wrinkle is the `r = 0` dissent
      -- witness possibly naming `id` itself, ruled out by `hin : input = none` (the fresh
      -- honest input can't have been the opposing dissenter).
      intro r h
      rcases hI.flip_alock r h with hg | hd
      · left; exact hg
      · right
        obtain ⟨v, hbv, hif⟩ := hd
        refine ⟨v, hbv, ?_⟩
        by_cases h0 : r = 0
        · rw [if_pos h0] at hif ⊢
          obtain ⟨id', hid'⟩ := hif
          by_cases hidmatch : id' = id
          · exfalso; rw [hidmatch, hin] at hid'; exact absurd hid' (by simp)
          · exact ⟨id', by rw [hNe id' hidmatch]; exact hid'⟩
        · rw [if_neg h0] at hif ⊢; exact hif
    · intro id' hmem hin' r'
      by_cases h : id' = id
      · subst h; simp [hSelf] at hin'
      · rw [hNe id' h] at hin'; exact hI.idle_no_wcall id' (hF ▸ hmem) hin' r'
    · intro r id' hmem hp
      by_cases h : id' = id
      · subst h; simp [hSelf] at hp
      · rw [hNe id' h] at hp
        rcases hI.retg_residue r id' (hF ▸ hmem) hp with hg | hd
        · left; exact hg
        · right; exact hDissTrans r hd
    · intro r id' hmem hcalled
      rcases hI.wcalled_residue r id' (hF ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact hDissTrans r hd
  · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    exact ⟨hI, AbsFrame.refl P g _⟩

/-- `fail`: a genuine synchronised corruption of all three components; `F` only grows, and
every other projection is untouched, so honesty hypotheses transfer via `F`-monotonicity. -/
theorem Inv.step_fail {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (id : Fin P.n) :
    Inv P (fun r => (g r).corrupt P id) (c.corrupt P id) (fun r => (w r).corrupt P id) ∧
      AbsFrame P g (fun r => (g r).corrupt P id) c (c.corrupt P id) := by
  set g' := fun r => (g r).corrupt P id with hg'def
  set c' := c.corrupt P id with hc'def
  set w' := fun r => (w r).corrupt P id with hw'def
  have hcall : ∀ r, (g' r).call = (g r).call := fun r => GBCA.corrupt_call P (g r) id
  have hbind : ∀ r, (g' r).dead = (g r).dead := fun r => GBCA.corrupt_dead P (g r) id
  have hgrade : ∀ r, (g' r).grade = (g r).grade := fun r => GBCA.corrupt_grade P (g r) id
  have hval : ∀ r, (w' r).val = (w r).val := fun r => WCC.corrupt_val id (w r)
  have hcalled : ∀ r, (w' r).called = (w r).called := fun r => WCC.corrupt_called id (w r)
  have hprocs : c'.procs = c.procs := CoreState.corrupt_procs c id
  have hDS : c'.decidedSent = c.decidedSent := CoreState.corrupt_decidedSent c id
  have hDR : c'.decidedRecv = c.decidedRecv := CoreState.corrupt_decidedRecv c id
  have hFg : ∀ r, (g' r).F = c'.F := fun r => GBCA.corrupt_F_eq id (g r) c (hI.F_g r)
  have hFw : ∀ r, (w' r).F = c'.F := fun r => WCC.corrupt_F_eq id (w r) c (hI.F_w r)
  have hFsub : c.F ⊆ c'.F := by
    rw [hc'def]; unfold CoreState.corrupt; split_ifs with hcond
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _
  have hFcard : c'.F.card ≤ P.f := by
    rw [hc'def]; unfold CoreState.corrupt; split_ifs with hcond
    · obtain ⟨-, hlt⟩ := hcond
      show (insert id c.F).card ≤ P.f
      have hcard := Finset.card_insert_le id c.F
      omega
    · exact hI.F_card
  have hLastBound : ∀ r, IsLastBound g' r ↔ IsLastBound g r := by
    intro r; unfold IsLastBound; rw [hbind r, hbind (r + 1)]
  have hCarrTrans : ∀ r' id₀ v, Carrier P g' c' r' id₀ v → Carrier P g c r' id₀ v := by
    intro r' id₀ v hc
    unfold Carrier at hc ⊢
    rwa [hprocs, hcall (r' + 1)] at hc
  have hCertTrans : ∀ r' b', ACert P g c r' b' → ACert P g' c' r' b' := fun r' b' =>
    ACert.of_frame (hgrade r') hbind (fun r'' id' => congrFun (hcall r'') id') hFsub
      (fun id' => by rw [hprocs]) (fun id' => by rw [hprocs])
      (fun id0 v => hCarrTrans r' id0 v)
  have hHold : ∀ id₀ b₀, AHolder P c' id₀ b₀ → AHolder P c id₀ b₀ := by
    intro id₀ b₀ h
    unfold AHolder at h ⊢
    rwa [hprocs, hDS] at h
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
    fun v _ hpin j b' hj hh => hpin j b' (fun h0 => hj (hFsub h0)) (hHold j b' hh)⟩
  refine ⟨fun r => hFg r, fun r => hFw r, hFcard, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r v hb => (hI.bind_supp r v (by rw [← hbind r]; exact hb)).mono
      (fun id' b' h => by rw [hprocs]; exact h) hFsub,
    fun r b hgf => GBCA.callSupp_mono (fun id' h => by rw [hcall r]; exact h)
      (by rw [hFg r, hI.F_g r]; exact hFsub)
      (hI.clock_supp r b (by rw [← hgrade r]; exact hgf)),
    fun r b h => GBCA.callSupp_mono (fun id' h' => by rw [hcall r]; exact h')
      (by rw [hFg r, hI.F_g r]; exact hFsub)
      (hI.dead_supp r b (by rw [← hbind r]; exact h)),
    fun r' i j v v' hm hm' h h' => hI.carrier_agree r' i j v v'
      (fun hh => hm (hFsub hh)) (fun hh => hm' (hFsub hh))
      (hCarrTrans _ _ _ h) (hCarrTrans _ _ _ h') |>.imp (fun hh => hh) (fun hh => by
        rw [hgrade r']; exact hh),
    fun i j b₀ b₀' hm hm' h h' => hI.alock_agree i j b₀ b₀'
      (fun hh => hm (hFsub hh)) (fun hh => hm' (hFsub hh))
      (hHold _ _ h) (hHold _ _ h')⟩
  · intro id' b' hmem hcall0
    rw [hprocs]; rw [hcall 0] at hcall0
    exact hI.input_g0 id' b' (fun h => hmem (hFsub h)) hcall0
  · intro r id' hmem hcall0
    rw [hprocs]; rw [hcall r] at hcall0
    exact hI.input_called r id' (fun h => hmem (hFsub h)) hcall0
  · intro id' hmem hne
    rw [hprocs] at hne ⊢; exact hI.phase_input id' (fun h => hmem (hFsub h)) hne
  · intro r h
    rw [Closed.congr (hbind r) (hgrade r)]
    exact hI.down_closed r ((Closed.congr (hbind (r + 1)) (hgrade (r + 1))).mp h)
  · obtain ⟨R, hR⟩ := hI.quiescent
    exact ⟨R, fun r hr h => hR r hr ((Closed.congr (hbind r) (hgrade r)).mp h)⟩
  · intro r h
    rw [hval r] at h; rw [Closed.congr (hbind r) (hgrade r)]
    exact hI.w_bound r h
  · intro i j b' h
    rw [hDR] at h; rw [hDS]
    exact hI.recv_sound i j b' h
  · intro id' b' hmem h
    rw [hDS] at h
    exact (hI.decided_src id' b' (fun h' => hmem (hFsub h')) h).imp (fun r => hCertTrans r b')
  · intro r b' hgr hbr
    rw [hgrade r] at hgr; rw [hbind r] at hbr
    obtain ⟨h1, h2, h3, h4⟩ := hI.a_commit r b' hgr hbr
    refine ⟨fun r' b'' hrr' hb' => ?_, fun r' id' b'' hrr' hmem hcall0 => ?_,
      fun id' hmem hround => ?_,
      fun id0 v hmem hcar => h4 id0 v (fun h => hmem (hFsub h)) (hCarrTrans r id0 v hcar)⟩
    · rw [hbind r'] at hb'; exact h1 r' b'' hrr' hb'
    · rw [hcall r'] at hcall0; exact h2 r' id' b'' hrr' (fun h => hmem (hFsub h)) hcall0
    · rw [hprocs] at hround ⊢; exact h3 id' (fun h => hmem (hFsub h)) hround
  · intro id' hmem r hround
    rw [hprocs] at hround; rw [Closed.congr (hbind r) (hgrade r)]
    exact hI.round_bound id' (fun h => hmem (hFsub h)) r hround
  · intro r v hlast hbr hcoin id' hmem hround
    rw [hLastBound r] at hlast; rw [hbind r] at hbr; rw [hval r] at hcoin
    rw [hprocs] at hround ⊢
    exact hI.agree_locked r v hlast hbr hcoin id' (fun h => hmem (hFsub h)) hround
  · intro r h; rw [hgrade r] at h; rw [hbind r]; exact hI.gradeA_needs_bind r h
  · intro r id' hmem hcall0
    rw [hprocs]; rw [hcall r] at hcall0
    exact hI.call_round r id' (fun h => hmem (hFsub h)) hcall0
  · intro r id' hmem hcalled0
    rw [hcalled r] at hcalled0; rw [Closed.congr (hbind r) (hgrade r)]
    exact hI.w_called r id' (fun h => hmem (hFsub h)) hcalled0
  · intro r id' hmem hround
    rw [hprocs] at hround; rw [hval r]
    exact hI.round_flip r id' (fun h => hmem (hFsub h)) hround
  · intro id' hmem hround hphase
    rw [hprocs] at hround hphase ⊢
    exact hI.est0 id' (fun h => hmem (hFsub h)) hround hphase
  · intro id' b' hlg
    rw [hprocs] at hlg
    exact (hI.grade_A_src id' b' hlg).imp (fun r => hCertTrans r b')
  · intro r id' hmem hround hphase
    rw [hprocs] at hround hphase
    obtain ⟨hnone, hsome⟩ := hI.est_ret r id' (fun h => hmem (hFsub h)) hround hphase
    rw [hprocs]
    refine ⟨fun he => ?_, fun b' hb' => ?_⟩
    · obtain ⟨hg0, hno⟩ := hnone he
      refine ⟨by rw [hgrade]; exact hg0, fun r₀ hr0 hgr0 => ?_⟩
      rw [hgrade] at hgr0
      exact hno r₀ hr0 hgr0
    · rw [hbind]; exact hsome b' hb'
  · intro r v h
    rw [hbind (r + 1)] at h; rw [hbind r, hgrade r, hval r]
    exact hI.bind_succ r v h
  · intro r id' v hmem hcall0
    rw [hcall (r + 1)] at hcall0; rw [hbind r, hgrade r, hval r]
    exact hI.call_prov r id' v (fun h => hmem (hFsub h)) hcall0
  · intro r id' hmem hround hphase v hest
    rw [hprocs] at hround hphase hest; rw [hbind r, hgrade r, hval r]
    exact hI.est_prev r id' (fun h => hmem (hFsub h)) hround hphase v hest
  · intro r h; rw [hgrade (r + 1)] at h; rw [hgrade r]; exact hI.c_chain r h
  · intro id' hmem hround hphase
    rw [hprocs] at hround hphase ⊢
    exact hI.est_prev_ne id' (fun h => hmem (hFsub h)) hround hphase
  · intro r h; rw [hval] at h ⊢; exact hI.w_order r h
  · intro id' b' h
    rw [hcall 0] at h; rw [hprocs]
    rcases hI.input_g0_perm id' b' h with hin | hf
    · left; exact hin
    · right; exact hFsub hf
  · intro r id' hmem hcalled0
    rw [hcalled r] at hcalled0; rw [hprocs]
    exact hI.w_call_round r id' (fun h => hmem (hFsub h)) hcalled0
  · intro r h
    rw [hval] at h
    rcases hI.flip_alock r h with hg | hd
    · left; rw [hgrade]; exact hg
    · right
      exact DissentResidue.transport (hbind r) (hbind (r - 1)) (fun hh => (hgrade (r - 1)) ▸ hh)
        (fun id' => by rw [hprocs]) hd
  · intro id' hmem hin r
    rw [hprocs] at hin; rw [hcalled r]
    exact hI.idle_no_wcall id' (fun h => hmem (hFsub h)) hin r
  · intro r id' hmem hp
    rw [hprocs] at hp
    rcases hI.retg_residue r id' (fun h => hmem (hFsub h)) hp with hg | hd
    · left; rw [hgrade]; exact hg
    · right
      exact DissentResidue.transport (hbind r) (hbind (r - 1)) (fun hh => (hgrade (r - 1)) ▸ hh)
        (fun id' => by rw [hprocs]) hd
  · intro r id' hmem hcalled0
    rw [hcalled r] at hcalled0
    rcases hI.wcalled_residue r id' (fun h => hmem (hFsub h)) hcalled0 with hg | hd
    · left; rw [hgrade]; exact hg
    · right
      exact DissentResidue.transport (hbind r) (hbind (r - 1)) (fun hh => (hgrade (r - 1)) ▸ hh)
        (fun id' => by rw [hprocs]) hd
  · intro r h
    rw [hbind r] at h
    exact GBCA.SpecState.quorum_mono (by rw [hFg r, hI.F_g r]; exact hFsub)
      (fun id' hne => by rw [hcall r]; exact hne) (hI.bound_quorum r h)

/-- `bindUnset` (the GBCA family's only genuine `τ`-step): kills one bit of round `r`'s
exclusion set. `down_closed`'s round-`r` corner needs "a call at round `r` implies current
round `≥ r`", a fact `Inv` doesn't carry explicitly — handed off. The value-transport
corners lean on the kill's own D15 guard: the spared bit `!b` keeps `f + 1` F-blind call
support at round `r`, whose harvested honest caller pins `!b` against every standing
commitment. -/
theorem Inv.step_gbcaTau {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ)
    {μr : PMF (GBCA.SpecState P.n)} (hstep : GBCA.Step P r (g r) .tau μr)
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support) :
    Inv P (Function.update g r gr') c w ∧
      AbsFrame P g (Function.update g r gr') c c := by
  cases hstep
  case bindUnset b _hq _hw hd0 =>
    rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'
    have hb : b ∉ (g r).dead := by rw [hd0]; simp
    set g' := Function.update g r { g r with dead := insert b (g r).dead } with hg'def
    have hFeq : ∀ r', (g' r').F = (g r').F := by
      intro r'; by_cases h : r' = r
      · subst h; rw [hg'def, Function.update_self]
      · rw [hg'def, Function.update_of_ne h]
    have hCalleq : ∀ r', (g' r').call = (g r').call := by
      intro r'; by_cases h : r' = r
      · subst h; rw [hg'def, Function.update_self]
      · rw [hg'def, Function.update_of_ne h]
    have hGradeeq : ∀ r', (g' r').grade = (g r').grade := by
      intro r'; by_cases h : r' = r
      · subst h; rw [hg'def, Function.update_self]
      · rw [hg'def, Function.update_of_ne h]
    have hDeadSelf : (g' r).dead = insert b (g r).dead := by
      rw [hg'def, Function.update_self]
    have hDeadNe : ∀ r', r' ≠ r → (g' r').dead = (g r').dead := by
      intro r' h; rw [hg'def, Function.update_of_ne h]
    have hDeadMono : ∀ r' x, x ∈ (g r').dead → x ∈ (g' r').dead := by
      intro r' x hx
      by_cases h : r' = r
      · subst h; rw [hDeadSelf]; exact Finset.mem_insert_of_mem hx
      · rw [hDeadNe r' h]; exact hx
    obtain ⟨id0, hid0F, hcall0⟩ :=
      GBCA.exists_honest_caller _hw (by rw [hI.F_g r]; exact hI.F_card)
    have hFid0 : id0 ∉ c.F := by rw [← hI.F_g r]; exact hid0F
    have hClosedNe : ∀ r', r' ≠ r → (Closed g' r' ↔ Closed g r') :=
      fun r' h => Closed.congr (hDeadNe r' h) (hGradeeq r')
    have hClosedSelf : Closed g' r := Or.inl (by rw [hDeadSelf]; simp)
    have hDissTrans : ∀ r₀, DissentResidue P g c r₀ → DissentResidue P g' c r₀ := by
      intro r₀ hd
      obtain ⟨v, hbv, hif⟩ := hd
      refine ⟨v, hDeadMono r₀ _ hbv, ?_⟩
      by_cases h0 : r₀ = 0
      · rw [if_pos h0] at hif ⊢; exact hif
      · rw [if_neg h0] at hif ⊢
        rcases hif with hh | hh
        · exact Or.inl (hDeadMono (r₀ - 1) _ hh)
        · exact Or.inr ((hGradeeq (r₀ - 1)).trans hh)
    have hCarrTrans : ∀ r₀ id₀ v, Carrier P g' c r₀ id₀ v → Carrier P g c r₀ id₀ v := by
      intro r₀ id₀ v hc
      unfold Carrier at hc ⊢
      rwa [hCalleq (r₀ + 1)] at hc
    have hCommitTrans : ∀ r'' b'', (!b'') ∈ (g r'').dead → ACommit P g c r'' b'' →
        ACommit P g' c r'' b'' := by
      rintro r'' b'' hres ⟨h1, h2, h3, h4⟩
      refine ⟨fun r₀ b₀ hrr hb' => ?_,
        fun r₀ id₀ b₀ hrr hmem hcall =>
          h2 r₀ id₀ b₀ hrr hmem (by rw [← hCalleq r₀]; exact hcall), h3,
        fun id₀ v hmem hcar => h4 id₀ v hmem (hCarrTrans r'' id₀ v hcar)⟩
      by_cases h3' : r₀ = r
      · subst h3'
        rw [hDeadSelf] at hb'
        have hb₀nd : b₀ ∉ (g r₀).dead := fun hh => hb'.2 (Finset.mem_insert_of_mem hh)
        rcases Finset.mem_insert.mp hb'.1 with hnew | hold
        · rcases eq_or_lt_of_le hrr with heq | hlt
          · have hne : b₀ ≠ !b'' := fun hh => hb₀nd (hh ▸ (heq ▸ hres))
            revert hne; cases b₀ <;> cases b'' <;> simp
          · have hb₀ : b₀ = !b := by revert hnew; cases b₀ <;> cases b <;> simp
            rw [hb₀]; exact h2 r₀ id0 (!b) hlt hFid0 hcall0
        · exact h1 r₀ b₀ hrr ⟨hold, hb₀nd⟩
      · rw [hDeadNe r₀ h3'] at hb'; exact h1 r₀ b₀ hrr hb'
    have hCertTrans : ∀ r'' b'', ACert P g c r'' b'' → ACert P g' c r'' b'' := by
      rintro r'' b'' ⟨hg1, hd1, hcm⟩
      exact ⟨(hGradeeq r'').trans hg1, hDeadMono r'' _ hd1, hCommitTrans r'' b'' hd1 hcm⟩
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
      fun v _ hpin => hpin⟩
    refine ⟨fun r' => (hFeq r').trans (hI.F_g r'), hI.F_w, hI.F_card, ?_, ?_, hI.phase_input,
      ?_, ?_, ?_,
      hI.recv_sound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.round_flip, hI.est0, ?_, ?_,
      ?_, ?_, ?_, ?_, hI.est_prev_ne, hI.w_order, ?_, hI.w_call_round, ?_,
      hI.idle_no_wcall, ?_, ?_, ?_, ?_, ?_, ?_,
      fun r₀ i j v v' hm hm' h h' => (hI.carrier_agree r₀ i j v v' hm hm'
        (hCarrTrans _ _ _ h) (hCarrTrans _ _ _ h')).imp (fun x => x)
        (fun hh => (hGradeeq r₀).trans hh),
      hI.alock_agree⟩
    · intro id b' hmem hcall; rw [hCalleq] at hcall; exact hI.input_g0 id b' hmem hcall
    · intro r' id hmem hcall; rw [hCalleq] at hcall; exact hI.input_called r' id hmem hcall
    · intro r' h
      by_cases h2 : r' = r
      · subst h2; exact hClosedSelf
      · by_cases h1 : r' + 1 = r
        · -- the fresh kill at `r' + 1` had an honest caller of the spared bit, whose
          -- round progress closes `r'`
          obtain ⟨id0, hid0F, hcall0⟩ :=
            GBCA.exists_honest_caller _hw (by rw [hI.F_g r]; exact hI.F_card)
          have hFid0 : id0 ∉ c.F := by rw [← hI.F_g r]; exact hid0F
          have hcr : r ≤ (c.procs id0).round :=
            hI.call_round r id0 hFid0 (by rw [hcall0]; simp)
          rw [hClosedNe r' h2]
          exact hI.round_bound id0 hFid0 r' (by omega)
        · rw [hClosedNe r' h2]
          exact hI.down_closed r' ((hClosedNe (r' + 1) h1).mp h)
    · obtain ⟨R, hR⟩ := hI.quiescent
      exact ⟨max R (r + 1), fun r' hr' h =>
        hR r' (by omega) ((hClosedNe r' (by omega)).mp h)⟩
    · intro r' h
      by_cases h2 : r' = r
      · subst h2; exact hClosedSelf
      · rw [hClosedNe r' h2]; exact hI.w_bound r' h
    · intro id b' hmem h
      exact (hI.decided_src id b' hmem h).imp (fun r'' => hCertTrans r'' b')
    · intro r' b' hgr hbr
      rw [hGradeeq] at hgr
      have hpair : (!b') ∈ (g r').dead ∧ b' ∉ (g r').dead := by
        by_cases h2 : r' = r
        · subst h2
          rw [hDeadSelf] at hbr
          refine ⟨?_, fun hh => hbr.2 (Finset.mem_insert_of_mem hh)⟩
          rcases Finset.mem_insert.mp hbr.1 with hnew | hold
          · -- the fresh kill is `!b'`: the A-locked round already had a dead bit,
            -- which can be neither `b` (`hb`) nor `b'` (still alive), so it is `!b'`
            obtain ⟨wd, hwd⟩ :=
              Finset.nonempty_iff_ne_empty.mpr (hI.gradeA_needs_bind r' hgr)
            have hwb : wd ≠ b := fun hh => hb (hh ▸ hwd)
            have hwb' : wd ≠ b' := fun hh => hbr.2 (Finset.mem_insert_of_mem (hh ▸ hwd))
            have hwd' : wd = !b' := by
              revert hwb hwb' hnew; cases wd <;> cases b' <;> cases b <;> simp
            exact hwd' ▸ hwd
          · exact hold
        · rw [hDeadNe r' h2] at hbr; exact hbr
      exact hCommitTrans r' b' hpair.1 (hI.a_commit r' b' hgr hpair)
    · intro id hmem r' hround
      by_cases h2 : r' = r
      · subst h2; exact hClosedSelf
      · rw [hClosedNe r' h2]; exact hI.round_bound id hmem r' hround
    · intro r' v hlast hbr hcoin id hmem hround
      by_cases h1 : r' + 1 = r
      · exfalso
        have hemp : (g' (r' + 1)).dead = ∅ := hlast.2
        rw [h1, hDeadSelf] at hemp; exact absurd hemp (by simp)
      · by_cases h2 : r' = r
        · have hDeadSelf' : (g' r').dead = insert b (g r').dead := by
            rw [h2]; exact hDeadSelf
          have hbAt : b ∉ (g r').dead := by rw [h2]; exact hb
          have hemp1 : (g (r' + 1)).dead = ∅ := by
            rw [← hDeadNe (r' + 1) h1]; exact hlast.2
          by_cases hdead0 : (g r').dead = ∅
          · -- round `r'` was fresh before this kill, hence already `C`-blocked upward;
            -- `est_prev` pins `id`'s estimate to the agreeing coin's bit.
            have hnoC : (g (r' + 1)).grade ≠ some false :=
              fun hh => hI.no_cgrade_succ r' v hcoin (by rw [hdead0]; simp) hh
            have hround1 : (c.procs id).round = r' + 1 := by
              by_contra hne
              rcases hI.round_bound id hmem (r' + 1) (by omega) with hh | hh
              · exact hh hemp1
              · exact hnoC hh
            by_cases hgroup : (c.procs id).phase = .toCallW ∨ (c.procs id).phase = .awaitW
            · exfalso
              obtain ⟨hnone, hsome⟩ := hI.est_ret (r' + 1) id hmem hround1 hgroup
              rcases Option.eq_none_or_eq_some ((c.procs id).est) with he | ⟨u, he⟩
              · exact hnoC (hnone he).1
              · have hu := hsome u he
                rw [hemp1] at hu; exact absurd hu (by simp)
            · have hphase3 : (c.procs id).phase = .idle ∨ (c.procs id).phase = .toCallG ∨
                  (c.procs id).phase = .awaitG := by
                rcases hph2 : (c.procs id).phase with _ | _ | _ | _ | _
                · exact Or.inl rfl
                · exact Or.inr (Or.inl rfl)
                · exact Or.inr (Or.inr rfl)
                · exact absurd (Or.inl hph2) hgroup
                · exact absurd (Or.inr hph2) hgroup
              obtain ⟨u, he⟩ :=
                Option.ne_none_iff_exists'.mp (hI.est_prev_ne id hmem (by omega) hphase3)
              rw [he]
              rcases hI.est_prev r' id hmem hround1 hphase3 u he with hbu | ⟨-, hw0⟩
              · rw [hdead0] at hbu; simp at hbu
              · rcases hw0 with hh | hh
                · rw [hcoin] at hh; simp only [TVal.bit.injEq] at hh; rw [hh]
                · rw [hcoin] at hh; simp at hh
          · -- round `r'` already had a dead bit, which the live pair pins to `!v`:
            -- the pre-kill pair holds and the old `agree_locked` applies
            have hpairold : (!v) ∈ (g r').dead ∧ v ∉ (g r').dead := by
              rw [hDeadSelf'] at hbr
              refine ⟨?_, fun hh => hbr.2 (Finset.mem_insert_of_mem hh)⟩
              rcases Finset.mem_insert.mp hbr.1 with hnew | hold
              · obtain ⟨wd, hwd⟩ := Finset.nonempty_iff_ne_empty.mpr hdead0
                have hwb : wd ≠ b := fun hh => hbAt (hh ▸ hwd)
                have hwv : wd ≠ v := fun hh => hbr.2 (Finset.mem_insert_of_mem (hh ▸ hwd))
                have hwd' : wd = !v := by
                  revert hwb hwv hnew; cases wd <;> cases v <;> cases b <;> simp
                exact hwd' ▸ hwd
              · exact hold
            have hlast' : IsLastBound g r' :=
              ⟨Finset.nonempty_iff_ne_empty.mp ⟨_, hpairold.1⟩, hemp1⟩
            exact hI.agree_locked r' v hlast' hpairold hcoin id hmem hround
        · have hlast' : IsLastBound g r' := ⟨by rw [← hDeadNe r' h2]; exact hlast.1,
            by rw [← hDeadNe (r' + 1) h1]; exact hlast.2⟩
          rw [hDeadNe r' h2] at hbr
          exact hI.agree_locked r' v hlast' hbr hcoin id hmem hround
    · intro r' h
      by_cases h2 : r' = r
      · subst h2; rw [hDeadSelf]; simp
      · rw [hGradeeq] at h
        rw [hDeadNe r' h2]; exact hI.gradeA_needs_bind r' h
    · intro r' id hmem hcall; rw [hCalleq] at hcall; exact hI.call_round r' id hmem hcall
    · intro r' id hmem hcalled
      by_cases h2 : r' = r
      · subst h2; exact hClosedSelf
      · rw [hClosedNe r' h2]; exact hI.w_called r' id hmem hcalled
    · intro id b hlg
      exact (hI.grade_A_src id b hlg).imp (fun r'' => hCertTrans r'' b)
    · intro r' id hmem hround hphase
      obtain ⟨hnone, hsome⟩ := hI.est_ret r' id hmem hround hphase
      refine ⟨fun he => ?_, fun b' hb' => ?_⟩
      · obtain ⟨hg0, hno⟩ := hnone he
        refine ⟨(hGradeeq r').trans hg0, fun r₀ hr0 hgr0 => ?_⟩
        rw [hGradeeq] at hgr0
        exact hno r₀ hr0 hgr0
      · exact hDeadMono r' _ (hsome b' hb')
    · intro r' v h
      by_cases h1 : r' + 1 = r
      · rw [h1, hDeadSelf] at h
        rcases Finset.mem_insert.mp h with hnew | hold
        · -- the fresh kill: the spared bit `!b = v` was carried by the harvested
          -- honest caller, whose `call_prov` provenance is the conclusion verbatim
          have hveq : v = !b := by revert hnew; cases v <;> cases b <;> simp
          have hcp := hI.call_prov r' id0 (!b) hFid0 (by rw [h1]; exact hcall0)
          rw [← hveq] at hcp
          rcases hcp with hd | ⟨hg0, hw0⟩
          · exact Or.inl (hDeadMono r' _ hd)
          · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
        · rcases hI.bind_succ r' v (by rw [h1]; exact hold) with hd | ⟨hg0, hw0⟩
          · exact Or.inl (hDeadMono r' _ hd)
          · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
      · rw [hDeadNe (r' + 1) h1] at h
        rcases hI.bind_succ r' v h with hd | ⟨hg0, hw0⟩
        · exact Or.inl (hDeadMono r' _ hd)
        · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
    · intro r' id v hmem hcall
      rw [hCalleq] at hcall
      rcases hI.call_prov r' id v hmem hcall with hd | ⟨hg0, hw0⟩
      · exact Or.inl (hDeadMono r' _ hd)
      · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
    · intro r' id hmem hround hphase v hest
      rcases hI.est_prev r' id hmem hround hphase v hest with hd | ⟨hg0, hw0⟩
      · exact Or.inl (hDeadMono r' _ hd)
      · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
    · intro r' h
      rw [hGradeeq] at h ⊢
      exact hI.c_chain r' h
    · intro id b' h; rw [hCalleq] at h; exact hI.input_g0_perm id b' h
    · -- `flip_alock`: `grade` and every residue component are monotone-transported
      intro r' h
      rcases hI.flip_alock r' h with hg | hd
      · left; rw [hGradeeq]; exact hg
      · right; exact hDissTrans r' hd
    · intro r' id hmem hp
      rcases hI.retg_residue r' id hmem hp with hg | hd
      · left; rw [hGradeeq]; exact hg
      · right; exact hDissTrans r' hd
    · intro r' id hmem hcalled
      rcases hI.wcalled_residue r' id hmem hcalled with hg | hd
      · left; rw [hGradeeq]; exact hg
      · right; exact hDissTrans r' hd
    · intro r' h
      by_cases h2 : r' = r
      · rw [h2]
        exact GBCA.SpecState.quorum_of_eq (hFeq r) (hCalleq r) _hq
      · rw [hDeadNe r' h2] at h
        exact GBCA.SpecState.quorum_of_eq (hFeq r') (hCalleq r') (hI.bound_quorum r' h)
    · -- I26 establishment: the fresh kill's D15 count is the spared bit's pool source
      intro r' v hb'
      by_cases h2 : r' = r
      · rw [h2, hDeadSelf] at hb'
        rcases Finset.mem_insert.mp hb' with hnew | hold
        · have hveq : v = !b := by revert hnew; cases v <;> cases b <;> simp
          rw [hveq]
          exact hI.supp_of_call_count r (!b) _hw
        · exact hI.bind_supp r v hold
      · rw [hDeadNe r' h2] at hb'; exact hI.bind_supp r' v hb'
    · intro r' b' hgf
      rw [hGradeeq] at hgf
      exact GBCA.callSupp_mono (fun id' h => by rw [hCalleq r']; exact h) (hFeq r').ge
        (hI.clock_supp r' b' hgf)
    · -- I28 establishment: the fresh kill records its own guard; old kills keep theirs
      intro r' b' hb'
      have hcnt : ∀ r₀ b₀, P.f + 1 ≤ (Finset.univ.filter
          (fun id' => (g r₀).call id' = some (!b₀) ∨ id' ∈ (g r₀).F)).card →
          P.f + 1 ≤ (Finset.univ.filter
          (fun id' => (g' r₀).call id' = some (!b₀) ∨ id' ∈ (g' r₀).F)).card :=
        fun r₀ b₀ hh => GBCA.callSupp_mono (fun id' h => by rw [hCalleq r₀]; exact h)
          (hFeq r₀).ge hh
      by_cases h2 : r' = r
      · rw [h2] at hb' ⊢
        rw [hDeadSelf] at hb'
        rcases Finset.mem_insert.mp hb' with hnew | hold
        · rw [hnew]; exact hcnt r b _hw
        · exact hcnt r b' (hI.dead_supp r b' hold)
      · rw [hDeadNe r' h2] at hb'
        exact hcnt r' b' (hI.dead_supp r' b' hb')

/-- `flip` (the WCC family's only genuine `τ`-step): resolves round `r`'s coin. Only `F_w`,
`w_bound` and `agree_locked` mention `w`; the coin-agreement corner of `agree_locked` (and the
call-implies-bind fact `w_bound` needs at round `r`) are handed off. -/
theorem Inv.step_wccTau {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ)
    {μw' : PMF (WCC.SpecState P.n)} (hstep : WCC.Step P r (w r) .tau μw')
    {wr' : WCC.SpecState P.n} (hwr' : wr' ∈ μw'.support) :
    Inv P g c (Function.update w r wr') ∧ AbsFrame P g g c c := by
  cases hstep
  case flip hq hv =>
    rw [PMF.mem_support_map_iff] at hwr'
    obtain ⟨o, -, hwr'⟩ := hwr'
    set w' := Function.update w r { w r with val := o.toTVal } with hw'def
    rw [← hwr']
    have hFeq : ∀ r', (w' r').F = (w r').F := by
      intro r'; by_cases h : r' = r
      · subst h; rw [hw'def, Function.update_self]
      · rw [hw'def, Function.update_of_ne h]
    have hValNe : ∀ r', r' ≠ r → (w' r').val = (w r').val := by
      intro r' h; rw [hw'def, Function.update_of_ne h]
    have hValSelf : (w' r).val = o.toTVal := by
      rw [hw'def, Function.update_self]
    have hCalledEq : ∀ r', (w' r').called = (w r').called := by
      intro r'; by_cases h : r' = r
      · subst h; rw [hw'def, Function.update_self]
      · rw [hw'def, Function.update_of_ne h]
    refine And.intro ?_ (AbsFrame.refl P g c)
    refine ⟨hI.F_g, fun r' => (hFeq r').trans (hI.F_w r'), hI.F_card, hI.input_g0,
      hI.input_called, hI.phase_input, hI.down_closed, hI.quiescent, ?_, hI.recv_sound,
      hI.decided_src, hI.a_commit, hI.round_bound, ?_, hI.gradeA_needs_bind, hI.call_round, ?_, ?_,
      hI.est0, hI.grade_A_src, hI.est_ret, ?_, ?_, ?_, hI.c_chain, hI.est_prev_ne,
      ?_, hI.input_g0_perm, ?_, ?_, ?_, hI.retg_residue, ?_, hI.bound_quorum,
      hI.bind_supp, hI.clock_supp, hI.dead_supp, hI.carrier_agree, hI.alock_agree⟩
    · intro r' h
      by_cases h2 : r' = r
      · have hq' : (w r').threshold P := by rw [h2]; exact hq
        have hFcardw : (w r').F.card ≤ P.f := by rw [hI.F_w r']; exact hI.F_card
        have hAne : (Finset.univ.filter
            (fun id => id ∉ (w r').F ∧ (w r').called id)).Nonempty := by
          by_contra hemp
          rw [Finset.not_nonempty_iff_eq_empty] at hemp
          unfold WCC.SpecState.threshold at hq'
          rw [hemp, Finset.empty_union] at hq'
          omega
        obtain ⟨id0, hid0⟩ := hAne
        rw [Finset.mem_filter] at hid0
        obtain ⟨-, hid0F, hid0called⟩ := hid0
        have hid0cF : id0 ∉ c.F := by rw [← hI.F_w r']; exact hid0F
        exact hI.w_called r' id0 hid0cF hid0called
      · rw [hValNe r' h2] at h; exact hI.w_bound r' h
    · intro r' v hlast hbr hcoin id hmem hround
      by_cases h2 : r' = r
      · have hround' : r < (c.procs id).round := by rw [← h2]; exact hround
        exact absurd hv (hI.round_flip r id hmem hround')
      · rw [hValNe r' h2] at hcoin
        exact hI.agree_locked r' v hlast hbr hcoin id hmem hround
    · intro r' id hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.w_called r' id hmem hcalled
    · intro r' id hmem hround
      by_cases h2 : r' = r
      · subst h2; rw [hValSelf]; cases o <;> simp [CoinOutcome.toTVal]
      · rw [hValNe r' h2]; exact hI.round_flip r' id hmem hround
    · intro r' v h
      have hb := hI.bind_succ r' v h
      by_cases h2 : r' = r
      · rw [h2] at hb ⊢
        rcases hb with hbv | ⟨hg0, hw0⟩
        · exact Or.inl hbv
        · rcases hw0 with hh | hh <;> rw [hv] at hh <;> simp at hh
      · rw [hValNe r' h2]; exact hb
    · intro r' id v hmem hcall
      have hcp := hI.call_prov r' id v hmem hcall
      by_cases h2 : r' = r
      · rw [h2] at hcp ⊢
        rcases hcp with hbv | ⟨hg0, hw0⟩
        · exact Or.inl hbv
        · rcases hw0 with hh | hh <;> rw [hv] at hh <;> simp at hh
      · rw [hValNe r' h2]; exact hcp
    · intro r' id hmem hround hphase v hest
      have hep := hI.est_prev r' id hmem hround hphase v hest
      by_cases h2 : r' = r
      · rw [h2] at hep ⊢
        rcases hep with hbv | ⟨hg0, hw0⟩
        · exact Or.inl hbv
        · rcases hw0 with hh | hh <;> rw [hv] at hh <;> simp at hh
      · rw [hValNe r' h2]; exact hep
    · -- `w_order`: pass-through, except the newly-flipped round's predecessor, established via
      -- the same honest-caller `Finset` argument as `w_bound` above, chained through
      -- `w_call_round`/`round_flip`.
      intro r' h
      by_cases h2 : r' = r
      · subst h2; rw [hValSelf]; cases o <;> simp [CoinOutcome.toTVal]
      · by_cases h1 : r' + 1 = r
        · have hq' : (w r).threshold P := hq
          have hFcardw : (w r).F.card ≤ P.f := by rw [hI.F_w r]; exact hI.F_card
          have hAne : (Finset.univ.filter
              (fun id => id ∉ (w r).F ∧ (w r).called id)).Nonempty := by
            by_contra hemp
            rw [Finset.not_nonempty_iff_eq_empty] at hemp
            unfold WCC.SpecState.threshold at hq'
            rw [hemp, Finset.empty_union] at hq'
            omega
          obtain ⟨id0, hid0⟩ := hAne
          rw [Finset.mem_filter] at hid0
          obtain ⟨-, hid0F, hid0called⟩ := hid0
          have hid0cF : id0 ∉ c.F := by rw [← hI.F_w r]; exact hid0F
          have hcr := hI.w_call_round r id0 hid0cF hid0called
          rw [hValNe r' h2]
          exact hI.round_flip r' id0 hid0cF (by omega)
        · rw [hValNe (r' + 1) h1] at h; rw [hValNe r' h2]; exact hI.w_order r' h
    · intro r' id hmem hcalled; rw [hCalledEq] at hcalled; exact hI.w_call_round r' id hmem hcalled
    · -- `flip_alock`'s establishment: the threshold on the newly-flipped round `r` yields an
      -- honest caller (`Finset` pigeonhole, as in `w_bound`/`w_order` above), which feeds
      -- `wcalled_residue` directly.
      intro r' h
      by_cases h2 : r' = r
      · have hq' : (w r').threshold P := by rw [h2]; exact hq
        have hFcardw : (w r').F.card ≤ P.f := by rw [hI.F_w r']; exact hI.F_card
        have hAne : (Finset.univ.filter
            (fun id => id ∉ (w r').F ∧ (w r').called id)).Nonempty := by
          by_contra hemp
          rw [Finset.not_nonempty_iff_eq_empty] at hemp
          unfold WCC.SpecState.threshold at hq'
          rw [hemp, Finset.empty_union] at hq'
          omega
        obtain ⟨id0, hid0⟩ := hAne
        rw [Finset.mem_filter] at hid0
        obtain ⟨-, hid0F, hid0called⟩ := hid0
        have hid0cF : id0 ∉ c.F := by rw [← hI.F_w r']; exact hid0F
        exact hI.wcalled_residue r' id0 hid0cF hid0called
      · rw [hValNe r' h2] at h; exact hI.flip_alock r' h
    · intro id hmem hin r'; rw [hCalledEq]; exact hI.idle_no_wcall id hmem hin r'
    · intro r' id hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.wcalled_residue r' id hmem hcalled

/-- Core `τ`: DECIDED delivery, echo, or byzantine injection. All three leave `procs`/`F`
untouched, so only `recv_sound`/`decided_src` need real work; the `echo` case's honest
sender comes from an `f + 1`-vs-`≤ f` pigeonhole on the delivered senders. -/
theorem Inv.step_coreTau {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w)
    {μc : PMF (CoreState P.n)} (hstep : CoreStep P c .tau μc)
    {c' : CoreState P.n} (hc' : c' ∈ μc.support) :
    Inv P g c' w ∧ AbsFrame P g g c c' := by
  rw [coreStep_tau_iff] at hstep
  rcases hstep with ⟨i, j, b, hs, hr, rfl⟩ | ⟨id, b, hcnt, hs, rfl⟩ | ⟨id, b, hF, rfl⟩
  · -- deliver
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    have hProcs : (c.deliverDecided i j b).procs = c.procs := CoreState.deliverDecided_procs _ _ _ _
    have hFeq : (c.deliverDecided i j b).F = c.F := CoreState.deliverDecided_F _ _ _ _
    have hDS : (c.deliverDecided i j b).decidedSent = c.decidedSent :=
      CoreState.deliverDecided_decidedSent _ _ _ _
    have hCert : ∀ r' b', ACert P g c r' b' → ACert P g (c.deliverDecided i j b) r' b' :=
      fun r' b' => ACert.of_frame rfl (fun _ => rfl) (fun _ _ => rfl)
        (by rw [hFeq] : c.F ⊆ _) (fun id' => by rw [hProcs]) (fun id' => by rw [hProcs])
        (fun id0 v hcar => by unfold Carrier at hcar ⊢; rwa [hProcs] at hcar)
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hFeq ▸ hj)
        (by unfold AHolder at hh ⊢; rwa [hProcs, hDS] at hh)⟩
    refine ⟨fun r => by rw [hFeq]; exact hI.F_g r, fun r => by rw [hFeq]; exact hI.F_w r,
      hFeq ▸ hI.F_card, ?_, ?_, ?_, hI.down_closed, hI.quiescent, hI.w_bound, ?_, ?_, ?_, ?_, ?_,
      hI.gradeA_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.c_chain, ?_,
      hI.w_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_supp r v hb).mono
        (fun id' b' h => by rw [hProcs]; exact h) (fun x hx => by rw [hFeq]; exact hx),
      hI.clock_supp, hI.dead_supp,
      fun r' i0 j0 v v' hm hm' h h' => hI.carrier_agree r' i0 j0 v v' (hFeq ▸ hm) (hFeq ▸ hm')
        (by unfold Carrier at h ⊢; rwa [hProcs] at h)
        (by unfold Carrier at h' ⊢; rwa [hProcs] at h'),
      fun i0 j0 b0 b0' hm hm' h h' => hI.alock_agree i0 j0 b0 b0' (hFeq ▸ hm) (hFeq ▸ hm')
        (by unfold AHolder at h ⊢; rwa [hProcs, hDS] at h)
        (by unfold AHolder at h' ⊢; rwa [hProcs, hDS] at h')⟩
    · intro id' b' hmem hcall
      rw [hProcs]; exact hI.input_g0 id' b' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcall
      rw [hProcs]; exact hI.input_called r id' (hFeq ▸ hmem) hcall
    · intro id' hmem hne
      rw [hProcs] at hne ⊢; exact hI.phase_input id' (hFeq ▸ hmem) hne
    · intro i' j' b' h
      rw [hDS]
      by_cases hij : i' = i ∧ j' = j
      · obtain ⟨rfl, rfl⟩ := hij
        rw [CoreState.deliverDecided_decidedRecv_self, Finset.mem_insert] at h
        rcases h with rfl | h
        · exact hs
        · exact hI.recv_sound i' j' b' h
      · rw [CoreState.deliverDecided_decidedRecv_of_ne _ _ _ _ (by tauto)] at h
        exact hI.recv_sound i' j' b' h
    · intro id' b' hmem h
      rw [hDS] at h
      exact (hI.decided_src id' b' (hFeq ▸ hmem) h).imp (fun r => hCert r b')
    · intro r b' hgr hbr
      obtain ⟨h1, h2, h3, h4⟩ := hI.a_commit r b' hgr hbr
      refine ⟨h1, h2, fun id' hmem hround => ?_,
        fun id0 v hmem hcar => h4 id0 v (hFeq ▸ hmem)
          (by unfold Carrier at hcar ⊢; rwa [hProcs] at hcar)⟩
      rw [hProcs] at hround ⊢; exact h3 id' (hFeq ▸ hmem) hround
    · intro id' hmem r hround
      rw [hProcs] at hround; exact hI.round_bound id' (hFeq ▸ hmem) r hround
    · intro r v hlast hbr hcoin id' hmem hround
      rw [hProcs] at hround ⊢; exact hI.agree_locked r v hlast hbr hcoin id' (hFeq ▸ hmem) hround
    · intro r id' hmem hcall; rw [hProcs]; exact hI.call_round r id' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.w_called r id' (hFeq ▸ hmem) hcalled
    · intro r id' hmem hround
      rw [hProcs] at hround; exact hI.round_flip r id' (hFeq ▸ hmem) hround
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢; exact hI.est0 id' (hFeq ▸ hmem) hround hphase
    · intro id' b' hlg
      rw [hProcs] at hlg
      exact (hI.grade_A_src id' b' hlg).imp (fun r => hCert r b')
    · intro r id' hmem hround hphase
      rw [hProcs] at hround hphase; exact hI.est_ret r id' (hFeq ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_prov r id' v (hFeq ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      rw [hProcs] at hround hphase hest
      exact hI.est_prev r id' (hFeq ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢
      exact hI.est_prev_ne id' (hFeq ▸ hmem) hround hphase
    · intro id' b' h; rw [hProcs]; exact hI.input_g0_perm id' b' h
    · intro r id' hmem hcalled; rw [hProcs]; exact hI.w_call_round r id' (hFeq ▸ hmem) hcalled
    · intro r h
      rcases hI.flip_alock r h with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro id' hmem hin r; rw [hProcs] at hin; exact hI.idle_no_wcall id' (hFeq ▸ hmem) hin r
    · intro r id' hmem hp
      rw [hProcs] at hp
      rcases hI.retg_residue r id' (hFeq ▸ hmem) hp with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro r id' hmem hcalled
      rcases hI.wcalled_residue r id' (hFeq ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
  · -- echo: an honest sender among the `f + 1` counted deliveries
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    have hProcs : (c.sendDecided id b).procs = c.procs := CoreState.sendDecided_procs _ _ _
    have hFeq : (c.sendDecided id b).F = c.F := CoreState.sendDecided_F _ _ _
    have hDR : (c.sendDecided id b).decidedRecv = c.decidedRecv :=
      CoreState.sendDecided_decidedRecv _ _ _
    have hcnt' : P.f + 1 ≤ (Finset.univ.filter (fun j => b ∈ c.decidedRecv id j)).card :=
      hcnt
    have hcard : c.F.card < (Finset.univ.filter (fun j => b ∈ c.decidedRecv id j)).card := by
      have := hI.F_card
      omega
    obtain ⟨j, hjmem, hjF⟩ :=
      (Finset.not_subset (s := Finset.univ.filter (fun j => b ∈ c.decidedRecv id j))
        (t := c.F)).mp (fun hsub => absurd (Finset.card_le_card hsub) (by omega))
    rw [Finset.mem_filter] at hjmem
    have hjsent : b ∈ c.decidedSent j := hI.recv_sound id j b hjmem.2
    obtain ⟨r0, hcert0⟩ := hI.decided_src j b hjF hjsent
    have hCert : ∀ r' b', ACert P g c r' b' → ACert P g (c.sendDecided id b) r' b' :=
      fun r' b' => ACert.of_frame rfl (fun _ => rfl) (fun _ _ => rfl)
        (by rw [hFeq] : c.F ⊆ _) (fun id' => by rw [hProcs]) (fun id' => by rw [hProcs])
        (fun id0 v hcar => by unfold Carrier at hcar ⊢; rwa [hProcs] at hcar)
    have hHold : ∀ i0 b0, i0 ∉ c.F → AHolder P (c.sendDecided id b) i0 b0 →
        ∃ j0, j0 ∉ c.F ∧ AHolder P c j0 b0 := by
      intro i0 b0 hm h
      rcases h with h | h
      · rw [hProcs] at h; exact ⟨i0, hm, Or.inl h⟩
      · rcases (CoreState.mem_sendDecided_decidedSent_iff _ _ _ _ _).mp h with ⟨-, rfl⟩ | h
        · exact ⟨j, hjF, Or.inr hjsent⟩
        · exact ⟨i0, hm, Or.inr h⟩
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => by
        obtain ⟨j0, hj0, hh0⟩ := hHold j b' (hFeq ▸ hj) hh
        exact hpin j0 b' hj0 hh0⟩
    refine ⟨fun r => by rw [hFeq]; exact hI.F_g r, fun r => by rw [hFeq]; exact hI.F_w r,
      hFeq ▸ hI.F_card, ?_, ?_, ?_, hI.down_closed, hI.quiescent, hI.w_bound, ?_, ?_, ?_, ?_, ?_,
      hI.gradeA_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.c_chain, ?_,
      hI.w_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_supp r v hb).mono
        (fun id' b' h => by rw [hProcs]; exact h) (fun x hx => by rw [hFeq]; exact hx),
      hI.clock_supp, hI.dead_supp,
      fun r' i0 j0 v v' hm hm' h h' => hI.carrier_agree r' i0 j0 v v' (hFeq ▸ hm) (hFeq ▸ hm')
        (by unfold Carrier at h ⊢; rwa [hProcs] at h)
        (by unfold Carrier at h' ⊢; rwa [hProcs] at h'),
      fun i0 j0 b0 b0' hm hm' h h' => by
        obtain ⟨ja, hjaF, hja⟩ := hHold i0 b0 (hFeq ▸ hm) h
        obtain ⟨jb, hjbF, hjb⟩ := hHold j0 b0' (hFeq ▸ hm') h'
        exact hI.alock_agree ja jb b0 b0' hjaF hjbF hja hjb⟩
    · intro id' b' hmem hcall
      rw [hProcs]; exact hI.input_g0 id' b' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcall
      rw [hProcs]; exact hI.input_called r id' (hFeq ▸ hmem) hcall
    · intro id' hmem hne
      rw [hProcs] at hne ⊢; exact hI.phase_input id' (hFeq ▸ hmem) hne
    · intro i' j' b' h
      rw [hDR] at h
      exact CoreState.sendDecided_decidedSent_mono _ _ _ (hI.recv_sound i' j' b' h)
    · intro id' b' hmem h
      rw [CoreState.sendDecided_decidedSent] at h
      by_cases hid : id' = id
      · subst hid
        rw [Function.update_self, Finset.mem_insert] at h
        rcases h with rfl | h
        · exact ⟨r0, hCert r0 b' hcert0⟩
        · exact (hI.decided_src id' b' (hFeq ▸ hmem) h).imp (fun r => hCert r b')
      · rw [Function.update_of_ne hid] at h
        exact (hI.decided_src id' b' (hFeq ▸ hmem) h).imp (fun r => hCert r b')
    · intro r b' hgr hbr
      obtain ⟨h1, h2, h3, h4⟩ := hI.a_commit r b' hgr hbr
      refine ⟨h1, h2, fun id' hmem hround => ?_,
        fun id0 v hmem hcar => h4 id0 v (hFeq ▸ hmem)
          (by unfold Carrier at hcar ⊢; rwa [hProcs] at hcar)⟩
      rw [hProcs] at hround ⊢; exact h3 id' (hFeq ▸ hmem) hround
    · intro id' hmem r hround
      rw [hProcs] at hround; exact hI.round_bound id' (hFeq ▸ hmem) r hround
    · intro r v hlast hbr hcoin id' hmem hround
      rw [hProcs] at hround ⊢; exact hI.agree_locked r v hlast hbr hcoin id' (hFeq ▸ hmem) hround
    · intro r id' hmem hcall; rw [hProcs]; exact hI.call_round r id' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.w_called r id' (hFeq ▸ hmem) hcalled
    · intro r id' hmem hround
      rw [hProcs] at hround; exact hI.round_flip r id' (hFeq ▸ hmem) hround
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢; exact hI.est0 id' (hFeq ▸ hmem) hround hphase
    · intro id' b' hlg
      rw [hProcs] at hlg; exact hI.grade_A_src id' b' hlg
    · intro r id' hmem hround hphase
      rw [hProcs] at hround hphase; exact hI.est_ret r id' (hFeq ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_prov r id' v (hFeq ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      rw [hProcs] at hround hphase hest
      exact hI.est_prev r id' (hFeq ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢
      exact hI.est_prev_ne id' (hFeq ▸ hmem) hround hphase
    · intro id' b' h; rw [hProcs]; exact hI.input_g0_perm id' b' h
    · intro r id' hmem hcalled; rw [hProcs]; exact hI.w_call_round r id' (hFeq ▸ hmem) hcalled
    · intro r h
      rcases hI.flip_alock r h with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro id' hmem hin r; rw [hProcs] at hin; exact hI.idle_no_wcall id' (hFeq ▸ hmem) hin r
    · intro r id' hmem hp
      rw [hProcs] at hp
      rcases hI.retg_residue r id' (hFeq ▸ hmem) hp with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro r id' hmem hcalled
      rcases hI.wcalled_residue r id' (hFeq ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
  · -- byzantine DECIDED injection: `id ∈ F`, so honest `decided_src` at `id` is vacuous
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    have hProcs : (c.sendDecided id b).procs = c.procs := CoreState.sendDecided_procs _ _ _
    have hFeq : (c.sendDecided id b).F = c.F := CoreState.sendDecided_F _ _ _
    have hDR : (c.sendDecided id b).decidedRecv = c.decidedRecv :=
      CoreState.sendDecided_decidedRecv _ _ _
    have hCert : ∀ r' b', ACert P g c r' b' → ACert P g (c.sendDecided id b) r' b' :=
      fun r' b' => ACert.of_frame rfl (fun _ => rfl) (fun _ _ => rfl)
        (by rw [hFeq] : c.F ⊆ _) (fun id' => by rw [hProcs]) (fun id' => by rw [hProcs])
        (fun id0 v hcar => by unfold Carrier at hcar ⊢; rwa [hProcs] at hcar)
    have hHold : ∀ i0 b0, i0 ∉ c.F → AHolder P (c.sendDecided id b) i0 b0 →
        AHolder P c i0 b0 := by
      intro i0 b0 hm h
      rcases h with h | h
      · rw [hProcs] at h; exact Or.inl h
      · rcases (CoreState.mem_sendDecided_decidedSent_iff _ _ _ _ _).mp h with ⟨rfl, rfl⟩ | h
        · exact absurd hF hm
        · exact Or.inr h
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hFeq ▸ hj) (hHold j b' (hFeq ▸ hj) hh)⟩
    refine ⟨fun r => by rw [hFeq]; exact hI.F_g r, fun r => by rw [hFeq]; exact hI.F_w r,
      hFeq ▸ hI.F_card, ?_, ?_, ?_, hI.down_closed, hI.quiescent, hI.w_bound, ?_, ?_, ?_, ?_, ?_,
      hI.gradeA_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.c_chain, ?_,
      hI.w_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_supp r v hb).mono
        (fun id' b' h => by rw [hProcs]; exact h) (fun x hx => by rw [hFeq]; exact hx),
      hI.clock_supp, hI.dead_supp,
      fun r' i0 j0 v v' hm hm' h h' => hI.carrier_agree r' i0 j0 v v' (hFeq ▸ hm) (hFeq ▸ hm')
        (by unfold Carrier at h ⊢; rwa [hProcs] at h)
        (by unfold Carrier at h' ⊢; rwa [hProcs] at h'),
      fun i0 j0 b0 b0' hm hm' h h' => hI.alock_agree i0 j0 b0 b0' (hFeq ▸ hm) (hFeq ▸ hm')
        (hHold i0 b0 (hFeq ▸ hm) h) (hHold j0 b0' (hFeq ▸ hm') h')⟩
    · intro id' b' hmem hcall
      rw [hProcs]; exact hI.input_g0 id' b' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcall
      rw [hProcs]; exact hI.input_called r id' (hFeq ▸ hmem) hcall
    · intro id' hmem hne
      rw [hProcs] at hne ⊢; exact hI.phase_input id' (hFeq ▸ hmem) hne
    · intro i' j' b' h
      rw [hDR] at h
      exact CoreState.sendDecided_decidedSent_mono _ _ _ (hI.recv_sound i' j' b' h)
    · intro id' b' hmem h
      rw [CoreState.sendDecided_decidedSent] at h
      by_cases hid : id' = id
      · subst hid; exact absurd (hFeq ▸ hmem) (not_not.mpr hF)
      · rw [Function.update_of_ne hid] at h
        exact (hI.decided_src id' b' (hFeq ▸ hmem) h).imp (fun r => hCert r b')
    · intro r b' hgr hbr
      obtain ⟨h1, h2, h3, h4⟩ := hI.a_commit r b' hgr hbr
      refine ⟨h1, h2, fun id' hmem hround => ?_,
        fun id0 v hmem hcar => h4 id0 v (hFeq ▸ hmem)
          (by unfold Carrier at hcar ⊢; rwa [hProcs] at hcar)⟩
      rw [hProcs] at hround ⊢; exact h3 id' (hFeq ▸ hmem) hround
    · intro id' hmem r hround
      rw [hProcs] at hround; exact hI.round_bound id' (hFeq ▸ hmem) r hround
    · intro r v hlast hbr hcoin id' hmem hround
      rw [hProcs] at hround ⊢; exact hI.agree_locked r v hlast hbr hcoin id' (hFeq ▸ hmem) hround
    · intro r id' hmem hcall; rw [hProcs]; exact hI.call_round r id' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.w_called r id' (hFeq ▸ hmem) hcalled
    · intro r id' hmem hround
      rw [hProcs] at hround; exact hI.round_flip r id' (hFeq ▸ hmem) hround
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢; exact hI.est0 id' (hFeq ▸ hmem) hround hphase
    · intro id' b' hlg
      rw [hProcs] at hlg
      exact (hI.grade_A_src id' b' hlg).imp (fun r => hCert r b')
    · intro r id' hmem hround hphase
      rw [hProcs] at hround hphase; exact hI.est_ret r id' (hFeq ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_prov r id' v (hFeq ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      rw [hProcs] at hround hphase hest
      exact hI.est_prev r id' (hFeq ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢
      exact hI.est_prev_ne id' (hFeq ▸ hmem) hround hphase
    · intro id' b' h; rw [hProcs]; exact hI.input_g0_perm id' b' h
    · intro r id' hmem hcalled; rw [hProcs]; exact hI.w_call_round r id' (hFeq ▸ hmem) hcalled
    · intro r h
      rcases hI.flip_alock r h with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro id' hmem hin r; rw [hProcs] at hin; exact hI.idle_no_wcall id' (hFeq ▸ hmem) hin r
    · intro r id' hmem hp
      rw [hProcs] at hp
      rcases hI.retg_residue r id' (hFeq ▸ hmem) hp with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro r id' hmem hcalled
      rcases hI.wcalled_residue r id' (hFeq ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd

/-- `callW`: the WCC instance only ever touches `.called` (never `.val`/`.F`), and the core
only ever touches `.phase` at `id` (never `.input`/`.est`/`.round`); `Inv` doesn't inspect
either, so this is pure bookkeeping. -/
theorem Inv.step_callW {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ) (id : Fin P.n)
    {μw' : PMF (WCC.SpecState P.n)} (hstepW : WCC.Step P r (w r) (.callW r id) μw')
    {μc : PMF (CoreState P.n)} (hstepC : CoreStep P c (.callW r id) μc)
    {wr' : WCC.SpecState P.n} (hwr' : wr' ∈ μw'.support)
    {c' : CoreState P.n} (hc' : c' ∈ μc.support) :
    Inv P g c' (Function.update w r wr') ∧ AbsFrame P g g c c' := by
  have hWeq : (Function.update w r wr' r).F = (w r).F ∧
      (Function.update w r wr' r).val = (w r).val := by
    rw [Function.update_self]
    cases hstepW with
    | call h => rw [PMF.mem_support_pure_iff] at hwr'; subst hwr'; exact ⟨rfl, rfl⟩
    | callLoop => rw [PMF.mem_support_pure_iff] at hwr'; subst hwr'; exact ⟨rfl, rfl⟩
  have hWNe : ∀ r', r' ≠ r → Function.update w r wr' r' = w r' := fun r' h =>
    Function.update_of_ne h wr' w
  have hFweq : ∀ r', (Function.update w r wr' r').F = (w r').F := by
    intro r'; by_cases h : r' = r
    · subst h; exact hWeq.1
    · rw [hWNe r' h]
  have hValeq : ∀ r', (Function.update w r wr' r').val = (w r').val := by
    intro r'; by_cases h : r' = r
    · subst h; exact hWeq.2
    · rw [hWNe r' h]
  have hCframe : c'.F = c.F ∧ c'.decidedSent = c.decidedSent ∧ c'.decidedRecv = c.decidedRecv ∧
      ∀ id', (c'.procs id').input = (c.procs id').input ∧ (c'.procs id').est = (c.procs id').est ∧
        (c'.procs id').round = (c.procs id').round := by
    rw [coreStep_callW_iff] at hstepC
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
      refine ⟨CoreState.setProc_F _ _ _, CoreState.setProc_decidedSent _ _ _,
        CoreState.setProc_decidedRecv _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [CoreState.setProc_procs_self]; exact ⟨rfl, rfl, rfl⟩
      · rw [CoreState.setProc_procs_ne _ _ _ h]; exact ⟨rfl, rfl, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
      exact ⟨rfl, rfl, rfl, fun id' => ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨hCF, hCDS, hCDR, hCprocs⟩ := hCframe
  have hCstep : ((c.procs id).phase = .toCallW ∧ (c.procs id).round = r ∧
      c' = c.setProc id { c.procs id with phase := .awaitW }) ∨ (id ∈ c.F ∧ c' = c) := by
    rw [coreStep_callW_iff] at hstepC
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inl ⟨hph, hr, hc'⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inr ⟨hF, hc'⟩
  have hLastGrade : ∀ id', (c'.procs id').lastGrade = (c.procs id').lastGrade := by
    rcases hCstep with ⟨-, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · intro id'; rw [hc'eq]; by_cases h : id' = id
      · subst h; rw [CoreState.setProc_procs_self]
      · rw [CoreState.setProc_procs_ne _ _ _ h]
    · intro id'; rw [hc'eq]
  have hCarr : ∀ r₀ id₀ v, Carrier P g c' r₀ id₀ v → Carrier P g c r₀ id₀ v := by
    intro r₀ id₀ v hc0
    rcases hc0 with h | ⟨he, hk⟩
    · exact Or.inl h
    · refine Or.inr ⟨(hCprocs id₀).2.1 ▸ he, ?_⟩
      rcases hCstep with ⟨hph, hrid, hc'eq⟩ | ⟨-, hc'eq⟩
      · by_cases hid : id₀ = id
        · subst hid
          rw [hc'eq, CoreState.setProc_procs_self] at hk
          rcases hk with ⟨hr0, -⟩ | ⟨-, hp⟩
          · exact Or.inl ⟨hr0, Or.inl hph⟩
          · exfalso; rcases hp with hp | hp | hp <;> simp at hp
        · rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hk
          exact hk
      · rw [hc'eq] at hk; exact hk
  have hCert : ∀ r' b', ACert P g c r' b' → ACert P g c' r' b' :=
    fun r' b' => ACert.of_frame rfl (fun _ => rfl) (fun _ _ => rfl)
      (by rw [hCF] : c.F ⊆ _) (fun id' => (hCprocs id').2.2) (fun id' => (hCprocs id').2.1)
      (fun id0 v => hCarr r' id0 v)
  have hHold : ∀ i0 b0, AHolder P c' i0 b0 → AHolder P c i0 b0 := by
    intro i0 b0 h
    unfold AHolder at h ⊢
    rwa [hLastGrade, hCDS] at h
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
    fun v _ hpin j b' hj hh => hpin j b' (hCF ▸ hj) (hHold j b' hh)⟩
  refine ⟨fun r' => hCF ▸ hI.F_g r', fun r' => (hFweq r').trans (hCF ▸ hI.F_w r'), hCF ▸ hI.F_card,
    ?_, ?_, ?_, hI.down_closed, hI.quiescent, ?_, ?_, ?_, ?_, ?_, ?_,
    hI.gradeA_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.c_chain, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
    fun r' v hb => (hI.bind_supp r' v hb).mono
      (fun id' b' h => by rw [(hCprocs id').1]; exact h) (fun x hx => by rw [hCF]; exact hx),
    hI.clock_supp, hI.dead_supp,
    fun r₀ i0 j0 v v' hm hm' h h' => hI.carrier_agree r₀ i0 j0 v v' (hCF ▸ hm) (hCF ▸ hm')
      (hCarr _ _ _ h) (hCarr _ _ _ h'),
    fun i0 j0 b0 b0' hm hm' h h' => hI.alock_agree i0 j0 b0 b0' (hCF ▸ hm) (hCF ▸ hm')
      (hHold _ _ h) (hHold _ _ h')⟩
  · intro id' b' hmem hcall; rw [(hCprocs id').1]; exact hI.input_g0 id' b' (hCF ▸ hmem) hcall
  · intro r' id' hmem hcall
    rw [(hCprocs id').1]; exact hI.input_called r' id' (hCF ▸ hmem) hcall
  · intro id' hmem hne
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid, (hCprocs id).1]
        have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
        exact hI.phase_input id hmem' (by rw [hph]; simp)
      · rw [(hCprocs id').1]
        have hne' : (c.procs id').phase ≠ .idle := by
          rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hne; exact hne
        exact hI.phase_input id' (hCF ▸ hmem) hne'
    · rw [hc'eq] at hne; rw [(hCprocs id').1]; exact hI.phase_input id' (hCF ▸ hmem) hne
  · intro r' h; rw [hValeq] at h; exact hI.w_bound r' h
  · intro i j b h; rw [hCDR] at h; rw [hCDS]; exact hI.recv_sound i j b h
  · intro id' b' hmem h; rw [hCDS] at h
    exact (hI.decided_src id' b' (hCF ▸ hmem) h).imp (fun r' => hCert r' b')
  · intro r' b' hgr hbr
    obtain ⟨h1, h2, h3, h4⟩ := hI.a_commit r' b' hgr hbr
    refine ⟨h1, fun r'' id' b'' hr hmem hcall => h2 r'' id' b'' hr (hCF ▸ hmem) hcall,
      fun id' hmem hround => ?_,
      fun id0 v hmem hcar => h4 id0 v (hCF ▸ hmem) (hCarr r' id0 v hcar)⟩
    rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1]; exact h3 id' (hCF ▸ hmem) hround
  · intro id' hmem r' hround
    rw [(hCprocs id').2.2] at hround; exact hI.round_bound id' (hCF ▸ hmem) r' hround
  · intro r' v hlast hbr hcoin id' hmem hround
    rw [hValeq] at hcoin; rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1]
    exact hI.agree_locked r' v hlast hbr hcoin id' (hCF ▸ hmem) hround
  · intro r' id' hmem hcall
    rw [(hCprocs id').2.2]; exact hI.call_round r' id' (hCF ▸ hmem) hcall
  · intro r' id' hmem hcalled
    by_cases h2 : r' = r
    · rw [h2] at hcalled ⊢
      simp only [Function.update_self] at hcalled
      by_cases hid : id' = id
      · rw [hid] at hmem
        rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · obtain ⟨hnone, hsome⟩ := hI.est_ret r id (hCF ▸ hmem) hr (Or.inl hph)
          by_cases hE : (c.procs id).est = none
          · exact Or.inr (hnone hE).1
          · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hE
            exact Or.inl (fun hemp => by
              have hm := hsome b hb
              rw [hemp] at hm
              simp at hm)
        · exact absurd (hCF ▸ hmem) (not_not.mpr hF)
      · cases hstepW with
        | call h =>
          rw [PMF.mem_support_pure_iff] at hwr'
          subst hwr'
          simp only [Function.update_of_ne hid] at hcalled
          exact hI.w_called r id' (hCF ▸ hmem) hcalled
        | callLoop =>
          rw [PMF.mem_support_pure_iff] at hwr'
          subst hwr'
          exact hI.w_called r id' (hCF ▸ hmem) hcalled
    · rw [hWNe r' h2] at hcalled; exact hI.w_called r' id' (hCF ▸ hmem) hcalled
  · intro r' id' hmem hround
    rw [hValeq]; rw [(hCprocs id').2.2] at hround
    exact hI.round_flip r' id' (hCF ▸ hmem) hround
  · intro id' hmem hround hphase
    rw [(hCprocs id').2.2] at hround
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid] at hphase
        simp only [hc'eq, CoreState.setProc_procs_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · simp only [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hphase
        rw [(hCprocs id').2.1, (hCprocs id').1]; exact hI.est0 id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase
      rw [(hCprocs id').2.1, (hCprocs id').1]; exact hI.est0 id' (hCF ▸ hmem) hround hphase
  · intro id' b' hlg
    rw [hLastGrade] at hlg
    exact (hI.grade_A_src id' b' hlg).imp (fun r' => hCert r' b')
  · intro r' id' hmem hround hphase
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · have hround' : (c.procs id).round = r' := by
          rw [hid] at hround
          simpa [hc'eq, CoreState.setProc_procs_self] using hround
        have hreq : r' = r := hround'.symm.trans hr
        rw [hid, hreq, (hCprocs id).2.1]
        exact hI.est_ret r id (hCF ▸ (hid ▸ hmem)) hr (Or.inl hph)
      · simp only [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hround hphase
        rw [(hCprocs id').2.1]
        exact hI.est_ret r' id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hround hphase
      rw [(hCprocs id').2.1]
      exact hI.est_ret r' id' (hCF ▸ hmem) hround hphase
  · intro r' v h; rw [hValeq]; exact hI.bind_succ r' v h
  · intro r' id' v hmem hcall; rw [hValeq]; exact hI.call_prov r' id' v (hCF ▸ hmem) hcall
  · intro r' id' hmem hround hphase v hest
    rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1] at hest; rw [hValeq]
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid] at hphase
        simp only [hc'eq, CoreState.setProc_procs_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · simp only [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hphase
        exact hI.est_prev r' id' (hCF ▸ hmem) hround hphase v hest
    · rw [hc'eq] at hphase
      exact hI.est_prev r' id' (hCF ▸ hmem) hround hphase v hest
  · intro id' hmem hround hphase
    rw [(hCprocs id').2.2] at hround
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid] at hphase
        simp only [hc'eq, CoreState.setProc_procs_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · simp only [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hphase
        rw [(hCprocs id').2.1]
        exact hI.est_prev_ne id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase
      rw [(hCprocs id').2.1]
      exact hI.est_prev_ne id' (hCF ▸ hmem) hround hphase
  · intro r' h; rw [hValeq] at h ⊢; exact hI.w_order r' h
  · intro id' b' h
    rcases hI.input_g0_perm id' b' h with hin | hf
    · left; rw [(hCprocs id').1]; exact hin
    · right; rw [hCF]; exact hf
  · -- `w_call_round`'s establishment: an honest caller of `WCC_r` just finished `GBCA_r`
    -- (`r ≤ round` from `hr : (c.procs id).round = r`, unaffected by `callW`).
    intro r' id' hmem hcalled
    by_cases h2 : r' = r
    · rw [h2] at hcalled ⊢
      simp only [Function.update_self] at hcalled
      by_cases hid : id' = id
      · rw [hid, (hCprocs id).2.2]
        rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · omega
        · rw [hid] at hmem; exact absurd (hCF ▸ hmem) (not_not.mpr hF)
      · cases hstepW with
        | call h =>
          rw [PMF.mem_support_pure_iff] at hwr'
          subst hwr'
          simp only [Function.update_of_ne hid] at hcalled
          rw [(hCprocs id').2.2]; exact hI.w_call_round r id' (hCF ▸ hmem) hcalled
        | callLoop =>
          rw [PMF.mem_support_pure_iff] at hwr'
          subst hwr'
          rw [(hCprocs id').2.2]; exact hI.w_call_round r id' (hCF ▸ hmem) hcalled
    · rw [hWNe r' h2] at hcalled
      rw [(hCprocs id').2.2]; exact hI.w_call_round r' id' (hCF ▸ hmem) hcalled
  · intro r' h
    rw [hValeq] at h
    rcases hI.flip_alock r' h with hg | hd
    · left; exact hg
    · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
  · intro id' hmem hin r'
    by_cases h2 : r' = r
    · rw [h2, Function.update_self]
      rw [(hCprocs id').1] at hin
      by_cases hid : id' = id
      · exfalso
        rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · rw [hid] at hin
          have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
          exact absurd hin (hI.phase_input id hmem' (by rw [hph]; simp))
        · rw [hid] at hmem; exact hmem (hCF ▸ hF)
      · cases hstepW with
        | call h =>
          rw [PMF.mem_support_pure_iff] at hwr'
          subst hwr'
          simp only [Function.update_of_ne hid]
          exact hI.idle_no_wcall id' (hCF ▸ hmem) hin r
        | callLoop =>
          rw [PMF.mem_support_pure_iff] at hwr'
          subst hwr'
          exact hI.idle_no_wcall id' (hCF ▸ hmem) hin r
    · rw [hWNe r' h2]
      rw [(hCprocs id').1] at hin
      exact hI.idle_no_wcall id' (hCF ▸ hmem) hin r'
  · intro r' id' hmem hp
    rw [(hCprocs id').2.2] at hp
    have hphaseImp : ((c'.procs id').phase = .toCallW ∨ (c'.procs id').phase = .awaitW) →
        ((c.procs id').phase = .toCallW ∨ (c.procs id').phase = .awaitW) := by
      intro hph2
      rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
      · by_cases hid : id' = id
        · exact Or.inl (hid ▸ hph)
        · rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hph2; exact hph2
      · rw [hc'eq] at hph2; exact hph2
    have hp' : ((c.procs id').round = r' ∧
        ((c.procs id').phase = .toCallW ∨ (c.procs id').phase = .awaitW)) ∨
        r' < (c.procs id').round := by
      rcases hp with ⟨hround, hphase⟩ | hlt
      · exact Or.inl ⟨hround, hphaseImp hphase⟩
      · exact Or.inr hlt
    rcases hI.retg_residue r' id' (hCF ▸ hmem) hp' with hg | hd
    · left; exact hg
    · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
  · intro r' id' hmem hcalled
    by_cases h2 : r' = r
    · rw [h2] at hcalled ⊢
      simp only [Function.update_self] at hcalled
      by_cases hid : id' = id
      · rw [hid] at hmem
        rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · rcases hI.retg_residue r id (hCF ▸ hmem) (Or.inl ⟨hr, Or.inl hph⟩) with hg | hd
          · left; exact hg
          · right
            exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
        · exact absurd (hCF ▸ hmem) (not_not.mpr hF)
      · cases hstepW with
        | call h =>
          rw [PMF.mem_support_pure_iff] at hwr'
          subst hwr'
          simp only [Function.update_of_ne hid] at hcalled
          rcases hI.wcalled_residue r id' (hCF ▸ hmem) hcalled with hg | hd
          · left; exact hg
          · right
            exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
        | callLoop =>
          rw [PMF.mem_support_pure_iff] at hwr'
          subst hwr'
          rcases hI.wcalled_residue r id' (hCF ▸ hmem) hcalled with hg | hd
          · left; exact hg
          · right
            exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
    · rw [hWNe r' h2] at hcalled
      rcases hI.wcalled_residue r' id' (hCF ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentResidue.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd

/-- `callG`: the GBCA instance only ever touches `.call` (never `.F`/`.dead`/`.grade`), the
core only ever touches `.phase` at `id` (never `.input`/`.est`/`.round`). `input_g0`/
`input_called`'s honest-fresh-call corner needs "`est = input` before any round-`0` return"
(phase/input coherence, not an explicit `Inv` conjunct) — handed off; `a_commit`'s second
conjunct is derived cleanly from its own third conjunct plus the honest call guard
`est = b`. -/
theorem Inv.step_callG {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ) (id : Fin P.n) (b : Bool)
    {μr : PMF (GBCA.SpecState P.n)} (hstepG : GBCA.Step P r (g r) (.callG r id b) μr)
    {μc : PMF (CoreState P.n)} (hstepC : CoreStep P c (.callG r id b) μc)
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support)
    {c' : CoreState P.n} (hc' : c' ∈ μc.support) :
    Inv P (Function.update g r gr') c' w ∧
      AbsFrame P g (Function.update g r gr') c c' := by
  have hGframe : gr'.F = (g r).F ∧ gr'.dead = (g r).dead ∧ gr'.grade = (g r).grade := by
    cases hstepG with
    | call h => rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'; exact ⟨rfl, rfl, rfl⟩
    | callLoop => rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'; exact ⟨rfl, rfl, rfl⟩
  have hGeq : ∀ r', r' ≠ r → Function.update g r gr' r' = g r' := fun r' h =>
    Function.update_of_ne h gr' g
  have hFgeq : ∀ r', (Function.update g r gr' r').F = (g r').F := by
    intro r'; by_cases h : r' = r
    · subst h; rw [Function.update_self]; exact hGframe.1
    · rw [hGeq r' h]
  have hBindeq : ∀ r', (Function.update g r gr' r').dead = (g r').dead := by
    intro r'; by_cases h : r' = r
    · subst h; rw [Function.update_self]; exact hGframe.2.1
    · rw [hGeq r' h]
  have hGradeeq : ∀ r', (Function.update g r gr' r').grade = (g r').grade := by
    intro r'; by_cases h : r' = r
    · subst h; rw [Function.update_self]; exact hGframe.2.2
    · rw [hGeq r' h]
  have hCframe : c'.F = c.F ∧ c'.decidedSent = c.decidedSent ∧ c'.decidedRecv = c.decidedRecv ∧
      ∀ id', (c'.procs id').input = (c.procs id').input ∧ (c'.procs id').est = (c.procs id').est ∧
        (c'.procs id').round = (c.procs id').round := by
    rw [coreStep_callG_iff] at hstepC
    rcases hstepC with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
      refine ⟨CoreState.setProc_F _ _ _, CoreState.setProc_decidedSent _ _ _,
        CoreState.setProc_decidedRecv _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [CoreState.setProc_procs_self]; exact ⟨rfl, rfl, rfl⟩
      · rw [CoreState.setProc_procs_ne _ _ _ h]; exact ⟨rfl, rfl, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
      exact ⟨rfl, rfl, rfl, fun id' => ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨hCF, hCDS, hCDR, hCprocs⟩ := hCframe
  -- The one fact needing case analysis: `gr'.call`, as an unconditional description
  -- (`Or.inl`: a fresh honest/byz `call` at `id`; `Or.inr`: `callLoop`, unaffected).
  have hGcall : (gr' = { g r with call := Function.update (g r).call id (some b) }) ∨
      gr' = g r := by
    cases hstepG with
    | call h => rw [PMF.mem_support_pure_iff] at hgr'; exact Or.inl hgr'
    | callLoop => rw [PMF.mem_support_pure_iff] at hgr'; exact Or.inr hgr'
  have hCcall : ((c.procs id).phase = .toCallG ∧ (c.procs id).round = r ∧
      (c.procs id).est = some b ∧
      c' = c.setProc id { c.procs id with phase := .awaitG }) ∨ (id ∈ c.F ∧ c' = c) := by
    rw [coreStep_callG_iff] at hstepC
    rcases hstepC with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inl ⟨hph, hr, hest, hc'⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inr ⟨hF, hc'⟩
  -- Every honest fresh call, at any `id'` and any round `r'`, agrees with `est` at that id'.
  have hGcallval : ∀ id' b', gr'.call id' = some b' → id' ≠ id → (g r).call id' = some b' := by
    rcases hGcall with rfl | rfl
    · intro id' b' h hne; simpa [Function.update_of_ne hne] using h
    · intro id' b' h _; exact h
  -- `call` slots are write-once (`Step.call` fires only on an empty slot), so a fresh call
  -- only ever adds to a support count.
  have hCallMono : ∀ id' b', (g r).call id' = some b' → gr'.call id' = some b' := by
    cases hstepG with
    | call _ _ hfresh =>
      rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'
      intro id' b' h'
      show Function.update (g r).call id (some b) id' = some b'
      by_cases hid : id' = id
      · rw [hid] at h'; rw [hfresh] at h'; simp at h'
      · rw [Function.update_of_ne hid]; exact h'
    | callLoop =>
      rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'; exact fun _ _ h => h
  have hGcallSelf : gr'.call id = some b ∨ gr' = g r := by
    rcases hGcall with rfl | rfl
    · left; simp
    · right; rfl
  have hPhaseNe : ∀ id', id' ≠ id → (c'.procs id').phase = (c.procs id').phase := by
    rcases hCcall with ⟨-, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · intro id' hne; rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hne]
    · intro id' _; rw [hc'eq]
  have hLastGradeG : ∀ id', (c'.procs id').lastGrade = (c.procs id').lastGrade := by
    rcases hCcall with ⟨-, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · intro id'; rw [hc'eq]; by_cases h : id' = id
      · subst h; rw [CoreState.setProc_procs_self]
      · rw [CoreState.setProc_procs_ne _ _ _ h]
    · intro id'; rw [hc'eq]
  have hCarrTrans : ∀ r₀ id₀ v, id₀ ∉ c.F →
      Carrier P (Function.update g r gr') c' r₀ id₀ v → Carrier P g c r₀ id₀ v := by
    intro r₀ id₀ v hmem0 hc0
    rcases hc0 with h | ⟨he, hk⟩
    · by_cases h1 : r₀ + 1 = r
      · rw [h1, Function.update_self] at h
        by_cases hid : id₀ = id
        · subst hid
          rcases hGcallSelf with hself | hself
          · rw [hself, Option.some_inj] at h
            rcases hCcall with ⟨hph, hr, hest, -⟩ | ⟨hF, -⟩
            · exact Or.inr ⟨by rw [hest, h], Or.inr ⟨by rw [hr, h1], Or.inr (Or.inl hph)⟩⟩
            · exact absurd hF hmem0
          · rw [hself] at h
            exact Or.inl (by rw [h1]; exact h)
        · have := hGcallval id₀ v h hid
          exact Or.inl (by rw [h1]; exact this)
      · rw [hGeq (r₀ + 1) h1] at h; exact Or.inl h
    · refine Or.inr ⟨(hCprocs id₀).2.1 ▸ he, ?_⟩
      rcases hCcall with ⟨hph, hr, hest, hc'eq⟩ | ⟨-, hc'eq⟩
      · by_cases hid : id₀ = id
        · subst hid
          rw [hc'eq, CoreState.setProc_procs_self] at hk
          rcases hk with ⟨-, hp | hp⟩ | ⟨hr0, -⟩
          · exact absurd hp (by simp)
          · exact absurd hp (by simp)
          · exact Or.inr ⟨hr0, Or.inr (Or.inl hph)⟩
        · rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hk
          exact hk
      · rw [hc'eq] at hk; exact hk
  have hCommitTrans : ∀ r0 b0, ACommit P g c r0 b0 →
      ACommit P (Function.update g r gr') c' r0 b0 := by
    rintro r0 b0 ⟨h1, h2, h3, h4⟩
    refine ⟨fun r'' b'' hrr' hbind =>
        h1 r'' b'' hrr' (by rw [← hBindeq r'']; exact hbind),
      fun r'' id' b'' hrr' hmem hcall => ?_, fun id' hmem hround => ?_,
      fun id0 v hmem hcar => h4 id0 v (hCF ▸ hmem)
        (hCarrTrans r0 id0 v (hCF ▸ hmem) hcar)⟩
    · by_cases hrr : r'' = r
      · rw [hrr, Function.update_self] at hcall
        by_cases hid : id' = id
        · rw [hid] at hcall hmem
          rcases hGcallSelf with hself | hself
          · rw [hself] at hcall; rw [Option.some_inj] at hcall
            rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
            · have hh3 := h3 id (hCF ▸ hmem) (by rw [hr, ← hrr]; exact hrr')
              rw [hest] at hh3; rw [Option.some_inj] at hh3
              rw [← hcall, hh3]
            · exact absurd (hCF ▸ hmem) (not_not.mpr hF)
          · rw [hself] at hcall
            exact h2 r'' id b'' hrr' (hCF ▸ hmem) (by rw [hrr]; exact hcall)
        · have := hGcallval id' b'' hcall hid
          exact h2 r'' id' b'' hrr' (hCF ▸ hmem) (by rw [hrr]; exact this)
      · rw [hGeq r'' hrr] at hcall
        exact h2 r'' id' b'' hrr' (hCF ▸ hmem) hcall
    · rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1]; exact h3 id' (hCF ▸ hmem) hround
  have hCertTrans : ∀ r0 b0, ACert P g c r0 b0 →
      ACert P (Function.update g r gr') c' r0 b0 := by
    rintro r0 b0 ⟨hg1, hd1, hcm⟩
    exact ⟨by rw [hGradeeq]; exact hg1, by rw [hBindeq]; exact hd1, hCommitTrans r0 b0 hcm⟩
  have hHold : ∀ i0 b0, AHolder P c' i0 b0 → AHolder P c i0 b0 := by
    intro i0 b0 h
    unfold AHolder at h ⊢
    rwa [hLastGradeG, hCDS] at h
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
    fun v _ hpin j b' hj hh => hpin j b' (hCF ▸ hj) (hHold j b' hh)⟩
  refine ⟨fun r' => (hFgeq r').trans (hCF ▸ hI.F_g r'), fun r' => hCF ▸ hI.F_w r', hCF ▸ hI.F_card,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, fun r' h => by rw [hGradeeq] at h ⊢; exact hI.c_chain r' h, ?_,
    hI.w_order, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r' v hb => (hI.bind_supp r' v (by rw [← hBindeq r']; exact hb)).mono
      (fun id' b' h => by rw [(hCprocs id').1]; exact h) (fun x hx => by rw [hCF]; exact hx),
    fun r' b' hgf => GBCA.callSupp_mono
      (fun id' h => by
        by_cases hrr : r' = r
        · subst hrr; rw [Function.update_self]; exact hCallMono id' b' h
        · rw [hGeq r' hrr]; exact h)
      (hFgeq r').ge (hI.clock_supp r' b' ((hGradeeq r').symm.trans hgf)),
    fun r' b0 hbd => GBCA.callSupp_mono
      (fun id' h => by
        by_cases hrr : r' = r
        · subst hrr; rw [Function.update_self]; exact hCallMono id' (!b0) h
        · rw [hGeq r' hrr]; exact h)
      (hFgeq r').ge (hI.dead_supp r' b0 (by rw [← hBindeq r']; exact hbd)),
    fun r₀ i0 j0 v v' hm hm' h h' => (hI.carrier_agree r₀ i0 j0 v v' (hCF ▸ hm) (hCF ▸ hm')
      (hCarrTrans r₀ i0 v (hCF ▸ hm) h) (hCarrTrans r₀ j0 v' (hCF ▸ hm') h')).imp
      (fun x => x) (fun hh => (hGradeeq r₀).trans hh),
    fun i0 j0 b0 b0' hm hm' h h' => hI.alock_agree i0 j0 b0 b0' (hCF ▸ hm) (hCF ▸ hm')
      (hHold _ _ h) (hHold _ _ h')⟩
  · -- input_g0
    intro id' b' hmem hcall
    rw [(hCprocs id').1]
    by_cases hr0 : r = 0
    · rw [hr0, Function.update_self] at hcall
      by_cases hid : id' = id
      · rw [hid] at hcall
        rcases hGcallSelf with hself | hself
        · rw [hself] at hcall; rw [Option.some_inj] at hcall
          rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
          · rw [hid]
            have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
            have he0 := hI.est0 id hmem' (hr.trans hr0) (Or.inr (Or.inl hph))
            rw [← he0, hest, hcall]
          · rw [hid] at hmem; exact absurd (hCF ▸ hmem) (not_not.mpr hF)
        · rw [hself, hr0] at hcall
          rw [hid] at hmem ⊢
          exact hI.input_g0 id b' (hCF ▸ hmem) hcall
      · have := hGcallval id' b' hcall hid
        rw [hr0] at this
        exact hI.input_g0 id' b' (hCF ▸ hmem) this
    · rw [hGeq 0 (Ne.symm hr0)] at hcall
      exact hI.input_g0 id' b' (hCF ▸ hmem) hcall
  · -- input_called
    intro r' id' hmem hcall
    rw [(hCprocs id').1]
    by_cases hrr : r' = r
    · rw [hrr, Function.update_self] at hcall
      by_cases hid : id' = id
      · rw [hid] at hcall ⊢
        rcases hGcallSelf with hself | hself
        · rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
          · have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
            exact hI.phase_input id hmem' (by rw [hph]; simp)
          · rw [hid] at hmem; exact absurd (hCF ▸ hmem) (not_not.mpr hF)
        · rw [hself] at hcall; rw [hid] at hmem; exact hI.input_called r id (hCF ▸ hmem) hcall
      · rcases hGcall with hgeq | hgeq
        · rw [hgeq] at hcall; simp only [Function.update_of_ne hid] at hcall
          exact hI.input_called r id' (hCF ▸ hmem) hcall
        · rw [hgeq] at hcall; exact hI.input_called r id' (hCF ▸ hmem) hcall
    · rw [hGeq r' hrr] at hcall
      exact hI.input_called r' id' (hCF ▸ hmem) hcall
  · -- phase_input
    intro id' hmem hne
    rcases hCcall with ⟨hph, hr, hest, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid, (hCprocs id).1]
        have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
        exact hI.phase_input id hmem' (by rw [hph]; simp)
      · rw [(hCprocs id').1]
        rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hne
        exact hI.phase_input id' (hCF ▸ hmem) hne
    · rw [hc'eq] at hne
      rw [(hCprocs id').1]
      exact hI.phase_input id' (hCF ▸ hmem) hne
  · -- down_closed
    intro r' h
    rw [Closed.congr (hBindeq r') (hGradeeq r')]
    exact hI.down_closed r' ((Closed.congr (hBindeq (r' + 1)) (hGradeeq (r' + 1))).mp h)
  · -- quiescent
    obtain ⟨R, hR⟩ := hI.quiescent
    exact ⟨R, fun r' hr' h => hR r' hr' ((Closed.congr (hBindeq r') (hGradeeq r')).mp h)⟩
  · -- w_bound
    intro r' h; rw [Closed.congr (hBindeq r') (hGradeeq r')]; exact hI.w_bound r' h
  · intro i j b' h; rw [hCDR] at h; rw [hCDS]; exact hI.recv_sound i j b' h
  · intro id' b' hmem h
    rw [hCDS] at h
    exact (hI.decided_src id' b' (hCF ▸ hmem) h).imp (fun r0 => hCertTrans r0 b')
  · intro r0 b0 hgr hbr
    rw [hGradeeq] at hgr; rw [hBindeq] at hbr
    exact hCommitTrans r0 b0 (hI.a_commit r0 b0 hgr hbr)
  · intro id' hmem r' hround
    rw [(hCprocs id').2.2] at hround
    rw [Closed.congr (hBindeq r') (hGradeeq r')]
    exact hI.round_bound id' (hCF ▸ hmem) r' hround
  · intro r' v hlast hbr hcoin id' hmem hround
    have hlast' : IsLastBound g r' := ⟨fun h => hlast.1 (by rw [hBindeq]; exact h),
      by rw [← hBindeq (r' + 1)]; exact hlast.2⟩
    rw [hBindeq] at hbr
    rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1]
    exact hI.agree_locked r' v hlast' hbr hcoin id' (hCF ▸ hmem) hround
  · intro r' h; rw [hGradeeq] at h; rw [hBindeq]; exact hI.gradeA_needs_bind r' h
  · intro r' id' hmem hcall
    by_cases hrr : r' = r
    · rw [hrr, Function.update_self] at hcall
      by_cases hid : id' = id
      · rw [hid, (hCprocs id).2.2]
        rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
        · omega
        · rw [hid] at hmem; exact absurd (hCF ▸ hmem) (not_not.mpr hF)
      · rw [(hCprocs id').2.2]
        obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.mp hcall
        have hcv := hGcallval id' b' hb' hid
        rw [hrr]
        exact hI.call_round r id' (hCF ▸ hmem) (by rw [hcv]; simp)
    · rw [hGeq r' hrr] at hcall
      rw [(hCprocs id').2.2]; exact hI.call_round r' id' (hCF ▸ hmem) hcall
  · intro r' id' hmem hcalled
    rw [Closed.congr (hBindeq r') (hGradeeq r')]
    exact hI.w_called r' id' (hCF ▸ hmem) hcalled
  · intro r' id' hmem hround
    rw [(hCprocs id').2.2] at hround
    exact hI.round_flip r' id' (hCF ▸ hmem) hround
  · intro id' hmem hround hphase
    rcases hCcall with ⟨hph, hr, hest, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
        rw [hid, (hCprocs id).2.2] at hround
        rw [hid, (hCprocs id).1, (hCprocs id).2.1]
        exact hI.est0 id hmem' hround (Or.inr (Or.inl hph))
      · rw [(hCprocs id').2.2] at hround
        rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hphase
        rw [(hCprocs id').1, (hCprocs id').2.1]
        exact hI.est0 id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase
      rw [(hCprocs id').2.2] at hround
      rw [(hCprocs id').1, (hCprocs id').2.1]
      exact hI.est0 id' (hCF ▸ hmem) hround hphase
  · intro id' b' hlg
    rw [hLastGradeG] at hlg
    exact (hI.grade_A_src id' b' hlg).imp (fun r0 => hCertTrans r0 b')
  · intro r' id' hmem hround hphase
    rcases hCcall with ⟨hph, hr, hest, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid, hc'eq, CoreState.setProc_procs_self] at hphase
        rcases hphase with h | h <;> simp at h
      · rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hround hphase
        rw [(hCprocs id').2.1]
        obtain ⟨hnone, hsome⟩ := hI.est_ret r' id' (hCF ▸ hmem) hround hphase
        refine ⟨fun he => ?_, fun b hb => ?_⟩
        · obtain ⟨hg0, hno⟩ := hnone he
          refine ⟨by rw [hGradeeq]; exact hg0, fun r₀ hr0 hgr0 => ?_⟩
          rw [hGradeeq] at hgr0
          exact hno r₀ hr0 hgr0
        · rw [hBindeq]; exact hsome b hb
    · rw [hc'eq] at hround hphase
      rw [(hCprocs id').2.1]
      obtain ⟨hnone, hsome⟩ := hI.est_ret r' id' (hCF ▸ hmem) hround hphase
      refine ⟨fun he => ?_, fun b hb => ?_⟩
      · obtain ⟨hg0, hno⟩ := hnone he
        refine ⟨by rw [hGradeeq]; exact hg0, fun r₀ hr0 hgr0 => ?_⟩
        rw [hGradeeq] at hgr0
        exact hno r₀ hr0 hgr0
      · rw [hBindeq]; exact hsome b hb
  · intro r' v h
    rw [hBindeq] at h; rw [hBindeq r', hGradeeq r']
    exact hI.bind_succ r' v h
  · intro r' id' v hmem hcall
    by_cases h1 : r' + 1 = r
    · by_cases hid : id' = id
      · rw [hid] at hcall hmem
        rw [h1, Function.update_self] at hcall
        rcases hGcallSelf with hself | hself
        · rw [hself, Option.some_inj] at hcall
          rcases hCcall with ⟨hph, hr, hest, -⟩ | ⟨hF, -⟩
          · have hround : (c.procs id).round = r' + 1 := by rw [hr, h1]
            have hep := hI.est_prev r' id (hCF ▸ hmem) hround (Or.inr (Or.inl hph)) b hest
            rw [hBindeq r', hGradeeq r']
            rwa [hcall] at hep
          · exact absurd hF (hCF ▸ hmem)
        · rw [hself] at hcall
          rw [hBindeq r', hGradeeq r']
          exact hI.call_prov r' id v (hCF ▸ hmem) (by rw [h1]; exact hcall)
      · rw [h1, Function.update_self] at hcall
        have hcv := hGcallval id' v hcall hid
        rw [hBindeq r', hGradeeq r']
        exact hI.call_prov r' id' v (hCF ▸ hmem) (by rw [h1]; exact hcv)
    · rw [hGeq (r' + 1) h1] at hcall
      rw [hBindeq r', hGradeeq r']
      exact hI.call_prov r' id' v (hCF ▸ hmem) hcall
  · intro r' id' hmem hround hphase v hest
    rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1] at hest
    rw [hBindeq r', hGradeeq r']
    rcases hCcall with ⟨hph, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid] at hmem hround hest
        exact hI.est_prev r' id (hCF ▸ hmem) hround (Or.inr (Or.inl hph)) v hest
      · rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hphase
        exact hI.est_prev r' id' (hCF ▸ hmem) hround hphase v hest
    · rw [hc'eq] at hphase
      exact hI.est_prev r' id' (hCF ▸ hmem) hround hphase v hest
  · intro id' hmem hround hphase
    rw [(hCprocs id').2.2] at hround
    rw [(hCprocs id').2.1]
    rcases hCcall with ⟨hph, hr, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid] at hmem hround ⊢
        exact hI.est_prev_ne id (hCF ▸ hmem) hround (Or.inr (Or.inl hph))
      · rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hphase
        exact hI.est_prev_ne id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase
      exact hI.est_prev_ne id' (hCF ▸ hmem) hround hphase
  · -- `input_g0_perm`: mirrors `input_g0`'s establishment above, with an `id' ∈ F` escape
    -- hatch replacing the honesty hypothesis.
    intro id' b' h
    by_cases hmem : id' ∈ c.F
    · right; rw [hCF]; exact hmem
    · left
      rw [(hCprocs id').1]
      by_cases hr0 : r = 0
      · rw [hr0, Function.update_self] at h
        by_cases hid : id' = id
        · rw [hid] at h
          rcases hGcallSelf with hself | hself
          · rw [hself] at h; rw [Option.some_inj] at h
            rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
            · rw [hid]
              have hmem' : id ∉ c.F := by rw [hid] at hmem; exact hmem
              have he0 := hI.est0 id hmem' (hr.trans hr0) (Or.inr (Or.inl hph))
              rw [← he0, hest, h]
            · rw [hid] at hmem; exact absurd hF hmem
          · rw [hself, hr0] at h
            rw [hid] at hmem ⊢
            rcases hI.input_g0_perm id b' h with hin | hf
            · exact hin
            · exact absurd hf hmem
        · have hcv := hGcallval id' b' h hid
          rw [hr0] at hcv
          rcases hI.input_g0_perm id' b' hcv with hin | hf
          · exact hin
          · exact absurd hf hmem
      · rw [hGeq 0 (Ne.symm hr0)] at h
        rcases hI.input_g0_perm id' b' h with hin | hf
        · exact hin
        · exact absurd hf hmem
  · intro r' id' hmem hcalled
    rw [(hCprocs id').2.2]; exact hI.w_call_round r' id' (hCF ▸ hmem) hcalled
  · intro r' h
    rcases hI.flip_alock r' h with hg | hd
    · left; rw [hGradeeq]; exact hg
    · right
      exact DissentResidue.transport (hBindeq r') (hBindeq (r' - 1))
        (fun h => (hGradeeq (r' - 1)) ▸ h) (fun id' => (hCprocs id').1) hd
  · intro id' hmem hin r'
    rw [(hCprocs id').1] at hin; exact hI.idle_no_wcall id' (hCF ▸ hmem) hin r'
  · intro r' id' hmem hp
    rw [(hCprocs id').2.2] at hp
    have hp' : ((c.procs id').round = r' ∧
        ((c.procs id').phase = .toCallW ∨ (c.procs id').phase = .awaitW)) ∨
        r' < (c.procs id').round := by
      rcases hp with ⟨hround, hphase⟩ | hlt
      · refine Or.inl ⟨hround, ?_⟩
        by_cases hid : id' = id
        · rcases hCcall with ⟨-, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
          · exfalso
            rw [hid, hc'eq, CoreState.setProc_procs_self] at hphase
            rcases hphase with h | h <;> simp at h
          · rw [hid]
            rw [hid, hc'eq] at hphase
            exact hphase
        · rwa [hPhaseNe id' hid] at hphase
      · exact Or.inr hlt
    rw [hGradeeq]
    rcases hI.retg_residue r' id' (hCF ▸ hmem) hp' with hg | hd
    · left; exact hg
    · right; exact DissentResidue.transport (hBindeq r') (hBindeq (r' - 1))
        (fun h => (hGradeeq (r' - 1)) ▸ h) (fun id' => (hCprocs id').1) hd
  · intro r' id' hmem hcalled
    rcases hI.wcalled_residue r' id' (hCF ▸ hmem) hcalled with hg | hd
    · left; rw [hGradeeq]; exact hg
    · right
      exact DissentResidue.transport (hBindeq r') (hBindeq (r' - 1))
        (fun h => (hGradeeq (r' - 1)) ▸ h) (fun id' => (hCprocs id').1) hd
  · intro r' h
    rw [hBindeq] at h
    refine GBCA.SpecState.quorum_mono (hFgeq r').ge (fun id' hne => ?_) (hI.bound_quorum r' h)
    by_cases hrr : r' = r
    · rw [hrr] at hne ⊢
      rw [Function.update_self]
      rcases hGcall with hg | hg
      · rw [hg]
        show Function.update (g r).call id (some b) id' ≠ none
        by_cases hid : id' = id
        · rw [hid, Function.update_self]; simp
        · rw [Function.update_of_ne hid]; exact hne
      · rw [hg]; exact hne
    · rw [hGeq r' hrr]; exact hne

/-- Once a round `r` is not (yet) `C`-locked and its surviving bit `b` is still alive, every
round `r' ≥ r` either has an empty exclusion set or the same live pair, and is never
`C`-locked either: `bind_succ` forces every bit killed at a freshly-bound round `r' + 1` to
be a bit already dead at `r'` — hence `!b`, by the inductive pair — unless `r'` itself just
closed `C`-locked (ruled out by the IH), and `c_chain` propagates the absence of a `C`-lock
downward, so its contrapositive propagates it upward along the induction. -/
theorem Inv.commit_up {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) :
    ∀ r b, (g r).grade ≠ some false → (!b) ∈ (g r).dead → b ∉ (g r).dead →
      ∀ r', r ≤ r' →
        ((g r').dead = ∅ ∨ ((!b) ∈ (g r').dead ∧ b ∉ (g r').dead)) ∧
          (g r').grade ≠ some false := by
  intro r b hg hres hlive r' hrr'
  induction r', hrr' using Nat.le_induction with
  | base => exact ⟨Or.inr ⟨hres, hlive⟩, hg⟩
  | succ r' hrr' ih =>
    refine ⟨?_, fun h => ih.2 (hI.c_chain r' h)⟩
    rcases Finset.eq_empty_or_nonempty ((g (r' + 1)).dead) with hemp | ⟨w', hw'⟩
    · exact Or.inl hemp
    · right
      have hwmem : ∀ x, x ∈ (g (r' + 1)).dead → x = !b := by
        intro x hx
        have hxres : (!(!x)) ∈ (g (r' + 1)).dead := by simpa using hx
        rcases hI.bind_succ r' (!x) hxres with hd | ⟨hgf, -⟩
        · rcases ih.1 with hn | ⟨hpr, hpl⟩
          · rw [hn] at hd; simp at hd
          · have hx' : x ∈ (g r').dead := by simpa using hd
            have hxb : x ≠ b := fun hh => hpl (hh ▸ hx')
            revert hxb; cases x <;> cases b <;> simp
        · exact absurd hgf ih.2
      refine ⟨?_, fun hb0 => ?_⟩
      · have hwb := hwmem w' hw'
        rw [← hwb]; exact hw'
      · have hbb := hwmem b hb0
        exact absurd hbb (by cases b <;> simp)

/-- `C`-locks propagate downward to every earlier round, by iterating `c_chain`. -/
theorem Inv.c_chain_down {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) :
    ∀ r r', r ≤ r' → (g r').grade = some false → (g r).grade = some false := by
  intro r r' hrr'
  induction r', hrr' using Nat.le_induction with
  | base => exact id
  | succ r' hrr' ih => intro h; exact ih (hI.c_chain r' h)

/-- `retG`: the GBCA instance only ever touches `.grade`/`.ret` (never `.F`/`.dead`/`.call`;
`.ret` isn't inspected by `Inv`), the core only ever touches `.est`/`.lastGrade`/`.phase` at
`id` (never `.round`/`.input`). The genuinely hard obligations — `a_commit`'s *new*
round-`r` commitment and `agree_locked`'s est-transfer at `id` — are handed off; they need
GBCA's own Graded-Agreement safety property, not local bookkeeping. -/
theorem Inv.step_retG {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ) (id : Fin P.n) (out : GbcaOut)
    {μr : PMF (GBCA.SpecState P.n)} (hstepG : GBCA.Step P r (g r) (.retG r id out) μr)
    {μc : PMF (CoreState P.n)} (hstepC : CoreStep P c (.retG r id out) μc)
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support)
    {c' : CoreState P.n} (hc' : c' ∈ μc.support) :
    Inv P (Function.update g r gr') c' w ∧
      AbsFrame P g (Function.update g r gr') c c' := by
  have hGframe : gr'.F = (g r).F ∧ gr'.dead = (g r).dead ∧ gr'.call = (g r).call := by
    cases hstepG with
    | retB _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact ⟨rfl, rfl, rfl⟩
    | retA _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact ⟨rfl, rfl, rfl⟩
    | retC _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact ⟨rfl, rfl, rfl⟩
  have hGgradeTrue : (g r).grade = some true → gr'.grade = some true := by
    cases hstepG with
    | retB _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact fun h => h
    | retA _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact fun _ => rfl
    | retC _ _ _ _ hg _ =>
      rw [PMF.mem_support_pure_iff] at hgr'
      intro hgt; rw [hgt] at hg; rcases hg with hg | hg <;> simp at hg
  have hGgradeFalse : (g r).grade = some false → gr'.grade = some false := by
    cases hstepG with
    | retB _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact fun h => h
    | retA _ _ _ _ hg _ => intro hgt; rw [hgt] at hg; rcases hg with hg | hg <;> simp at hg
    | retC _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact fun _ => rfl
  have hGeq : ∀ r', r' ≠ r → Function.update g r gr' r' = g r' := fun r' h =>
    Function.update_of_ne h gr' g
  have hFgeq : ∀ r', (Function.update g r gr' r').F = (g r').F := by
    intro r'; by_cases h : r' = r
    · rw [h, Function.update_self]; exact hGframe.1
    · rw [hGeq r' h]
  have hBindeq : ∀ r', (Function.update g r gr' r').dead = (g r').dead := by
    intro r'; by_cases h : r' = r
    · rw [h, Function.update_self]; exact hGframe.2.1
    · rw [hGeq r' h]
  have hCalleq : ∀ r', (Function.update g r gr' r').call = (g r').call := by
    intro r'; by_cases h : r' = r
    · rw [h, Function.update_self]; exact hGframe.2.2
    · rw [hGeq r' h]
  have hGself : Function.update g r gr' r = gr' := by rw [Function.update_self]
  have hClosedEq : ∀ r', r' ≠ r → (Closed (Function.update g r gr') r' ↔ Closed g r') :=
    fun r' h => Closed.congr (hBindeq r') (by rw [hGeq r' h])
  have hClosedTo : ∀ r', Closed g r' → Closed (Function.update g r gr') r' := by
    intro r' h
    refine Closed.of_frame (hBindeq r') (fun hh => ?_) h
    by_cases h2 : r' = r
    · rw [h2, hGself]; exact hGgradeFalse (by rw [← h2]; exact hh)
    · rw [hGeq r' h2]; exact hh
  have hCframe : c'.F = c.F ∧ c'.decidedSent = c.decidedSent ∧ c'.decidedRecv = c.decidedRecv ∧
      ∀ id', (c'.procs id').input = (c.procs id').input ∧
        (c'.procs id').round = (c.procs id').round := by
    rw [coreStep_retG_iff] at hstepC
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
      refine ⟨CoreState.setProc_F _ _ _, CoreState.setProc_decidedSent _ _ _,
        CoreState.setProc_decidedRecv _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · rw [h, CoreState.setProc_procs_self]; exact ⟨rfl, rfl⟩
      · rw [CoreState.setProc_procs_ne _ _ _ h]; exact ⟨rfl, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact ⟨rfl, rfl, rfl, fun id' => ⟨rfl, rfl⟩⟩
  obtain ⟨hCF, hCDS, hCDR, hCprocs⟩ := hCframe
  have hCstepG : ((c.procs id).phase = .awaitG ∧ (c.procs id).round = r ∧
      c' = c.setProc id { c.procs id with
        est := out.est, lastGrade := some out, phase := .toCallW }) ∨
      (id ∈ c.F ∧ c' = c) := by
    rw [coreStep_retG_iff] at hstepC
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inl ⟨hph, hr, hc'⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inr ⟨hF, hc'⟩
  -- The return either hands out round `r`'s surviving bit (`retA`/`retB`, with its live
  -- pair as fire-time guards) or hands out nothing and locks the round to the C-side
  -- (`retC`).
  have hRetInfo : (∃ v, out.est = some v ∧ v ∉ (g r).dead ∧ (!v) ∈ (g r).dead) ∨
      (out.est = none ∧ gr'.grade = some false) := by
    cases hstepG with
    | retB _ v hlive hdead _ _ => exact Or.inl ⟨v, rfl, hlive, hdead⟩
    | retA _ v hlive hdead _ _ => exact Or.inl ⟨v, rfl, hlive, hdead⟩
    | retC _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'
      exact Or.inr ⟨rfl, by rw [hgr']⟩
  -- A round that is `C`-locked after the return carries the `retC` guards at `g r`: either
  -- they were already there (`retB` leaves the grade alone; `retA` locks the A-side) or this
  -- very return supplied them.
  have hCsupp : gr'.grade = some false → ∀ b, P.f + 1 ≤ (Finset.univ.filter
      (fun id' => (g r).call id' = some b ∨ id' ∈ (g r).F)).card := by
    cases hstepG with
    | retB _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'
      intro hgf b; rw [hgr'] at hgf; exact hI.clock_supp r b hgf
    | retA _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'
      intro hgf; rw [hgr'] at hgf; simp at hgf
    | retC _ _ hwT hwF _ _ =>
      intro _ b; cases b
      · exact hwF
      · exact hwT
  have hGradeTrueOfA : ∀ b, out = .A b → gr'.grade = some true := by
    cases hstepG with
    | retB _ _ _ _ _ _ => intro b h; simp at h
    | retA _ _ _ _ _ _ => intro b h; rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']
    | retC _ _ _ _ _ _ => intro b h; simp at h
  have hGradeNoneTrans : (g r).grade ≠ none → gr'.grade ≠ none := by
    intro hgne hcontra
    obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.mp hgne
    cases b' with
    | true => rw [hGgradeTrue hb'] at hcontra; simp at hcontra
    | false => rw [hGgradeFalse hb'] at hcontra; simp at hcontra
  have hTransport : ∀ r', (g r').grade ≠ none ∨ DissentResidue P g c r' →
      (Function.update g r gr' r').grade ≠ none ∨
        DissentResidue P (Function.update g r gr') c' r' := by
    intro r' hres
    rcases hres with hg | hd
    · left
      by_cases h2 : r' = r
      · rw [h2, Function.update_self]; exact hGradeNoneTrans (h2 ▸ hg)
      · rwa [hGeq r' h2]
    · right
      by_cases hrr1 : r' - 1 = r
      · refine DissentResidue.transport (hBindeq r') (hBindeq (r' - 1)) (fun hgf => ?_)
          (fun id' => (hCprocs id').1) hd
        rw [hrr1, Function.update_self]; exact hGgradeFalse (hrr1 ▸ hgf)
      · exact DissentResidue.transport (hBindeq r') (hBindeq (r' - 1))
          (fun hgf => by rwa [hGeq (r' - 1) hrr1]) (fun id' => (hCprocs id').1) hd
  -- A `C`-locking return at round `r` pulls a `C`-lock below every `A`-locked round under
  -- `r` (its own both-bit supports via `c_chain_of_both_supports`, then `c_chain_down`) —
  -- contradiction.
  have hNoCAbove : ∀ r0, r0 < r → (g r0).grade = some true → gr'.grade = some false →
      False := by
    intro r0 hlt hg0 hgf
    have hr1 : r - 1 + 1 = r := by omega
    have hgf' := hI.c_chain_of_both_supports (r - 1)
      (by rw [hr1]; exact hCsupp hgf true) (by rw [hr1]; exact hCsupp hgf false)
    have hgf0 := hI.c_chain_down r0 (r - 1) (by omega) hgf'
    rw [hg0] at hgf0; simp at hgf0
  -- Carrier reduction: a carrier of the post-state is an old carrier or the freshly
  -- returned `id` itself, holding the return's own output.
  have hRedC : ∀ r₀ i1 v1, Carrier P (Function.update g r gr') c' r₀ i1 v1 →
      Carrier P g c r₀ i1 v1 ∨ (i1 = id ∧ r₀ = r ∧ out.est = some v1) := by
    intro r₀ i1 v1 hc1
    rcases hc1 with hcall | ⟨he, hk⟩
    · exact Or.inl (Or.inl (by rw [← hCalleq (r₀ + 1)]; exact hcall))
    · rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid1 : i1 = id
        · subst hid1
          rw [hc'eq, CoreState.setProc_procs_self] at he hk
          right
          refine ⟨rfl, ?_, he⟩
          rcases hk with ⟨hr0, -⟩ | ⟨-, hp⟩
          · rw [← hr0]; exact hr
          · exfalso; rcases hp with hp | hp | hp <;> simp at hp
        · rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid1] at he hk
          exact Or.inl (Or.inr ⟨he, hk⟩)
      · rw [hc'eq] at he hk
        exact Or.inl (Or.inr ⟨he, hk⟩)
  -- Provenance of a standing round-`r` carrier: the permanent residue or the `C`-lock.
  have hProvC : ∀ j1 v1, j1 ∉ c.F → Carrier P g c r j1 v1 →
      (!v1) ∈ (g r).dead ∨ (g r).grade = some false := by
    intro j1 v1 hj hcar
    rcases hcar with hcall | ⟨he, hk⟩
    · rcases hI.call_prov r j1 v1 hj hcall with hd | ⟨hgf, -⟩
      · exact Or.inl hd
      · exact Or.inr hgf
    · rcases hk with ⟨hr0, hph⟩ | ⟨hr0, hph⟩
      · obtain ⟨-, hsome⟩ := hI.est_ret r j1 hj hr0 hph
        exact Or.inl (hsome v1 he)
      · rcases hI.est_prev r j1 hj hr0 hph v1 he with hd | ⟨hgf, -⟩
        · exact Or.inl hd
        · exact Or.inr hgf
  have hCommitTrans : ∀ r0 b0, (g r0).grade = some true → ACommit P g c r0 b0 →
      ACommit P (Function.update g r gr') c' r0 b0 := by
    rintro r0 b0 hg0 ⟨h1, h2, h3, h4⟩
    refine ⟨fun r' b'' hrr' hb' => h1 r' b'' hrr' (by rw [← hBindeq r']; exact hb'),
      fun r' id' b'' hrr' hmem hcall =>
        h2 r' id' b'' hrr' (hCF ▸ hmem) (by rw [← hCalleq r']; exact hcall),
      fun id' hmem hround => ?_, fun id0 v hmem hcar => ?_⟩
    · rw [(hCprocs id').2] at hround
      rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid : id' = id
        · rw [hid, hc'eq, CoreState.setProc_procs_self]
          have hround' : r0 < r := by rw [hid, hr] at hround; exact hround
          rcases hRetInfo with ⟨v, hoev, hlive, hdead⟩ | ⟨-, hgf⟩
          · show out.est = some b0
            rw [hoev, h1 r v (le_of_lt hround') ⟨hdead, hlive⟩]
          · exact absurd hgf (fun hgf => hNoCAbove r0 hround' hg0 hgf)
        · rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid]
          exact h3 id' (hCF ▸ hmem) hround
      · rw [hc'eq]
        exact h3 id' (hCF ▸ hmem) hround
    · rcases hRedC r0 id0 v hcar with hold | ⟨-, hreq, hev⟩
      · exact h4 id0 v (hCF ▸ hmem) hold
      · subst hreq
        rcases hRetInfo with ⟨u, hoev, hulive, hudead⟩ | ⟨-, hgf⟩
        · have hu : u = v := Option.some_inj.mp (hoev.symm.trans hev)
          rw [← hu]
          exact h1 r0 u le_rfl ⟨hudead, hulive⟩
        · have hgt := hGgradeTrue hg0
          rw [hgf] at hgt
          simp at hgt
  have hCertTrans : ∀ r0 b0, ACert P g c r0 b0 →
      ACert P (Function.update g r gr') c' r0 b0 := by
    rintro r0 b0 ⟨hg0, hres0, hcm⟩
    refine ⟨?_, by rw [hBindeq]; exact hres0, hCommitTrans r0 b0 hg0 hcm⟩
    by_cases h2 : r0 = r
    · rw [h2, hGself]; exact hGgradeTrue (h2 ▸ hg0)
    · rw [hGeq r0 h2]; exact hg0
  -- The *fresh* round-`r` commitment: a live pair at the returning round that is not (yet)
  -- `C`-locked commits everything at and above it, through `commit_up`'s pair invariant.
  have hFreshCommit : ∀ b0, (g r).grade ≠ some false →
      (!b0) ∈ (g r).dead → b0 ∉ (g r).dead →
      ACommit P (Function.update g r gr') c' r b0 := by
    intro b0 hgne hres0 hlive0
    have hCU := hI.commit_up r b0 hgne hres0 hlive0
    have hconj3 : ∀ id', id' ∉ c.F → r < (c.procs id').round →
        (c.procs id').est = some b0 := by
      intro id' hmem2 hround2
      by_cases hgroup : (c.procs id').phase = .toCallW ∨ (c.procs id').phase = .awaitW
      · obtain ⟨hnone, hsome⟩ := hI.est_ret (c.procs id').round id' hmem2 rfl hgroup
        rcases Option.eq_none_or_eq_some ((c.procs id').est) with he | ⟨v, he⟩
        · exfalso
          obtain ⟨hgf, -⟩ := hnone he
          exact (hCU (c.procs id').round (by omega)).2 hgf
        · have hveq := hsome v he
          rw [he]
          rcases (hCU (c.procs id').round (by omega)).1 with hn | ⟨hres', hlive'⟩
          · rw [hn] at hveq; simp at hveq
          · have hvb : v = b0 := by
              by_contra hne
              have hv' : (!v) = b0 := by revert hne; cases v <;> cases b0 <;> simp
              exact hlive' (hv' ▸ hveq)
            rw [hvb]
      · have hphase3 : (c.procs id').phase = .idle ∨ (c.procs id').phase = .toCallG ∨
            (c.procs id').phase = .awaitG := by
          rcases hph2 : (c.procs id').phase with _ | _ | _ | _ | _
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact absurd (Or.inl hph2) hgroup
          · exact absurd (Or.inr hph2) hgroup
        have hround1 : (c.procs id').round ≠ 0 := by omega
        have hne := hI.est_prev_ne id' hmem2 hround1 hphase3
        obtain ⟨v, he⟩ := Option.ne_none_iff_exists'.mp hne
        have hr'eq2 : (c.procs id').round = (c.procs id').round - 1 + 1 := by omega
        have hep := hI.est_prev ((c.procs id').round - 1) id' hmem2 hr'eq2 hphase3 v he
        rw [he]
        rcases hep with hbv | ⟨hgf, -⟩
        · rcases (hCU ((c.procs id').round - 1) (by omega)).1 with hn | ⟨hres', hlive'⟩
          · rw [hn] at hbv; simp at hbv
          · have hvb : v = b0 := by
              by_contra hne
              have hv' : (!v) = b0 := by revert hne; cases v <;> cases b0 <;> simp
              exact hlive' (hv' ▸ hbv)
            rw [hvb]
        · exact absurd hgf (hCU ((c.procs id').round - 1) (by omega)).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r' b'' hrr' hb'
      rw [hBindeq r'] at hb'
      rcases (hCU r' hrr').1 with hn | ⟨hres', hlive'⟩
      · rw [hn] at hb'; exact absurd hb'.1 (by simp)
      · by_contra hne
        have hv' : (!b'') = b0 := by revert hne; cases b'' <;> cases b0 <;> simp
        exact hlive' (hv' ▸ hb'.1)
    · intro r' id' b'' hrr' hmem hcall
      have hr'eq : r' = (r' - 1) + 1 := by omega
      rw [hCalleq] at hcall
      rw [hr'eq] at hcall
      have hcp := hI.call_prov (r' - 1) id' b'' (hCF ▸ hmem) hcall
      have hcu2 := hCU (r' - 1) (by omega)
      rcases hcp with hbv | ⟨hgf, -⟩
      · rcases hcu2.1 with hn | ⟨hres', hlive'⟩
        · rw [hn] at hbv; simp at hbv
        · by_contra hne
          have hv' : (!b'') = b0 := by revert hne; cases b'' <;> cases b0 <;> simp
          exact hlive' (hv' ▸ hbv)
      · exact absurd hgf hcu2.2
    · intro id' hmem hround
      rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid : id' = id
        · exfalso
          have hround' : r < (c.procs id).round := by
            simpa [hid, hc'eq, CoreState.setProc_procs_self] using hround
          omega
        · rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hround ⊢
          exact hconj3 id' (hCF ▸ hmem) hround
      · rw [hc'eq] at hround ⊢
        exact hconj3 id' (hCF ▸ hmem) hround
    · intro id0 v hmem hcar
      rcases hRedC r id0 v hcar with hold | ⟨-, -, hev⟩
      · rcases hProvC id0 v (hCF ▸ hmem) hold with hres | hgf
        · by_contra hne
          have hv' : (!v) = b0 := by revert hne; cases v <;> cases b0 <;> simp
          exact hlive0 (hv' ▸ hres)
        · exact absurd hgf hgne
      · rcases hRetInfo with ⟨u, hoev, hulive, -⟩ | ⟨hoe, -⟩
        · have hu : u = v := Option.some_inj.mp (hoev.symm.trans hev)
          rw [← hu]
          by_contra hne
          have hv' : u = !b0 := by revert hne; cases u <;> cases b0 <;> simp
          exact hulive (hv' ▸ hres0)
        · rw [hoe] at hev; simp at hev
  have hRedH : ∀ i1 b1, AHolder P c' i1 b1 → AHolder P c i1 b1 ∨ (i1 = id ∧ out = .A b1) := by
    intro i1 b1 h1
    rcases h1 with h1 | h1
    · rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid1 : i1 = id
        · subst hid1
          rw [hc'eq, CoreState.setProc_procs_self] at h1
          exact Or.inr ⟨rfl, Option.some_inj.mp h1⟩
        · rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid1] at h1
          exact Or.inl (Or.inl h1)
      · rw [hc'eq] at h1
        exact Or.inl (Or.inl h1)
    · rw [hCDS] at h1
      exact Or.inl (Or.inr h1)
  -- A fresh `A`-return's value against any standing certificate: same round via the
  -- fire-time pair, below via the certificate's commitment, above via the fresh
  -- commitment and the harvested caller of the certificate's spared bit.
  have hpinCert : ∀ b1, out = .A b1 → ∀ r1 b1', ACert P g c r1 b1' → b1' = b1 := by
    intro b1 hout r1 b1' hcert
    rcases hRetInfo with ⟨u, hoev, hulive, hudead⟩ | ⟨hoe, -⟩
    · have hu : u = b1 := by
        rw [hout] at hoev
        simpa using hoev.symm
      have hulive' : b1 ∉ (g r).dead := hu ▸ hulive
      have hudead' : (!b1) ∈ (g r).dead := hu ▸ hudead
      obtain ⟨hg1, hres1, hcm1⟩ := hcert
      rcases lt_trichotomy r1 r with hlt | heq | hgt
      · exact (hcm1.1 r b1 (le_of_lt hlt) ⟨hudead', hulive'⟩).symm
      · subst heq
        by_contra hne
        have hv' : (!b1') = b1 := by revert hne; cases b1 <;> cases b1' <;> simp
        exact hulive' (hv' ▸ hres1)
      · have hgne : (g r).grade ≠ some false := fun hf => by
          have h1 := hGgradeFalse hf
          rw [hGradeTrueOfA b1 hout] at h1
          simp at h1
        have hFC := hFreshCommit b1 hgne hudead' hulive'
        obtain ⟨id0, hid0F, hcall0⟩ := GBCA.exists_honest_caller
          (hI.dead_supp r1 (!b1') hres1) (by rw [hI.F_g r1]; exact hI.F_card)
        have hcall0' : (g r1).call id0 = some b1' := by simpa using hcall0
        have hid0c' : id0 ∉ c'.F := by rw [hCF, ← hI.F_g r1]; exact hid0F
        exact hFC.2.1 r1 id0 b1' hgt hid0c' (by rw [hCalleq r1]; exact hcall0')
    · rw [hout] at hoe; simp at hoe
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
    fun v hcv hpin j b' hj hh => ?_⟩
  case refine_2 =>
    rcases hRedH j b' hh with hold | ⟨-, hout⟩
    · exact hpin j b' (hCF ▸ hj) hold
    · obtain ⟨r1, hcv1⟩ := hcv
      exact (hpinCert b' hout r1 v hcv1).symm
  refine ⟨fun r' => (hFgeq r').trans (hCF ▸ hI.F_g r'), fun r' => hCF ▸ hI.F_w r', hCF ▸ hI.F_card,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, hI.w_order, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id' b' hmem hcall
    rw [(hCprocs id').1]; rw [hCalleq] at hcall
    exact hI.input_g0 id' b' (hCF ▸ hmem) hcall
  · intro r' id' hmem hcall
    rw [(hCprocs id').1]; rw [hCalleq] at hcall; exact hI.input_called r' id' (hCF ▸ hmem) hcall
  · intro id' hmem hne
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid, (hCprocs id).1]
        have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
        exact hI.phase_input id hmem' (by rw [hph]; simp)
      · rw [(hCprocs id').1]
        have hne' : (c.procs id').phase ≠ .idle := by
          rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hne; exact hne
        exact hI.phase_input id' (hCF ▸ hmem) hne'
    · rw [hc'eq] at hne; rw [(hCprocs id').1]; exact hI.phase_input id' (hCF ▸ hmem) hne
  · -- `down_closed`: off the returning round nothing moved; at `r' + 1 = r` a `C`-return's
    -- both-bit support pushes the `C`-lock down one round (`c_chain_of_both_supports`).
    intro r' h
    by_cases h2 : r' = r
    · exact hClosedTo r' (hI.down_closed r' ((hClosedEq (r' + 1) (by omega)).mp h))
    · rw [hClosedEq r' h2]
      by_cases h1 : r' + 1 = r
      · rcases h with hb | hgf
        · refine hI.down_closed r' (Or.inl ?_)
          rw [← hBindeq (r' + 1)]; exact hb
        · have hgself : Function.update g r gr' (r' + 1) = gr' := by rw [h1]; exact hGself
          rw [hgself] at hgf
          exact Or.inr (hI.c_chain_of_both_supports r' (by rw [h1]; exact hCsupp hgf true)
            (by rw [h1]; exact hCsupp hgf false))
      · exact hI.down_closed r' ((hClosedEq (r' + 1) h1).mp h)
  · obtain ⟨R, hR⟩ := hI.quiescent
    exact ⟨max R (r + 1), fun r' hr' h =>
      hR r' (by omega) ((hClosedEq r' (by omega)).mp h)⟩
  · intro r' h; exact hClosedTo r' (hI.w_bound r' h)
  · intro i j b' h; rw [hCDR] at h; rw [hCDS]; exact hI.recv_sound i j b' h
  · intro id' b' hmem h
    rw [hCDS] at h
    exact (hI.decided_src id' b' (hCF ▸ hmem) h).imp (fun r0 => hCertTrans r0 b')
  · intro r0 b0 hgr hbr
    by_cases hr0r : r0 = r
    · rw [hr0r, Function.update_self] at hgr hbr
      have hgne : (g r).grade ≠ some false := fun hf => by
        rw [hGgradeFalse hf] at hgr; simp at hgr
      have hb0eq : (!b0) ∈ (g r).dead ∧ b0 ∉ (g r).dead := by
        rw [← hGframe.2.1]; exact hbr
      rw [hr0r]
      exact hFreshCommit b0 hgne hb0eq.1 hb0eq.2
    · rw [hGeq r0 hr0r] at hgr hbr
      obtain ⟨h1, h2, h3, h4⟩ := hI.a_commit r0 b0 hgr hbr
      refine ⟨fun r' b'' hrr' hb' => by rw [hBindeq] at hb'; exact h1 r' b'' hrr' hb',
        fun r' id' b'' hrr' hmem hcall => by
          rw [hCalleq] at hcall; exact h2 r' id' b'' hrr' (hCF ▸ hmem) hcall,
        fun id' hmem hround => ?_,
        fun id0 v hmem hcar => by
          rcases hRedC r0 id0 v hcar with hold | ⟨-, hreq, -⟩
          · exact h4 id0 v (hCF ▸ hmem) hold
          · exact absurd hreq hr0r⟩
      rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid : id' = id
        · rw [hid] at hround hmem
          have hround' : r0 < (c.procs id).round := by
            simpa [hc'eq, CoreState.setProc_procs_self] using hround
          rw [hid, hc'eq, CoreState.setProc_procs_self]
          by_cases hr0lt : r0 < r
          · rcases hRetInfo with ⟨v, hoev, hlive, hdead⟩ | ⟨-, hgf⟩
            · rw [hoev, h1 r v (le_of_lt hr0lt) ⟨hdead, hlive⟩]
            · exact (hNoCAbove r0 hr0lt hgr hgf).elim
          · exfalso; omega
        · rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hround ⊢
          exact h3 id' (hCF ▸ hmem) hround
      · rw [hc'eq] at hround ⊢
        exact h3 id' (hCF ▸ hmem) hround
  · intro id' hmem r' hround
    rw [(hCprocs id').2] at hround
    exact hClosedTo r' (hI.round_bound id' (hCF ▸ hmem) r' hround)
  · intro r' v hlast hbr hcoin id' hmem hround
    have hlast' : IsLastBound g r' := ⟨fun h => hlast.1 (by rw [hBindeq]; exact h),
      by rw [← hBindeq (r' + 1)]; exact hlast.2⟩
    rw [hBindeq] at hbr
    rw [(hCprocs id').2] at hround
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · -- `id` sits at round `r` with `r' < r` and an agreeing coin at `r'`: round `r' + 1`
        -- can neither have bound (`hlast'`) nor be `C`-locked (`no_cgrade_succ`).
        exfalso
        have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
        have hround' : r' < r := by rw [hid, hr] at hround; exact hround
        have hbnd : v ∉ (g r').dead := hbr.2
        by_cases heq : r' + 1 = r
        · rcases hRetInfo with ⟨u, -, -, hudead⟩ | ⟨-, hgf⟩
          · rw [← heq] at hudead
            rw [hlast'.2] at hudead
            simp at hudead
          · exact hI.no_cgrade_succ_of_supp r' v hcoin hbnd (by rw [heq]; exact hCsupp hgf (!v))
        · rcases hI.round_bound id hmem' (r' + 1) (by omega) with hh | hh
          · exact hh hlast'.2
          · exact hI.no_cgrade_succ r' v hcoin hbnd hh
      · rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid]
        exact hI.agree_locked r' v hlast' hbr hcoin id' (hCF ▸ hmem) hround
    · rw [hc'eq]
      exact hI.agree_locked r' v hlast' hbr hcoin id' (hCF ▸ hmem) hround
  · intro r' h
    by_cases h2 : r' = r
    · rw [h2, hBindeq]
      rcases hRetInfo with ⟨v, -, -, hdead⟩ | ⟨-, hgf⟩
      · exact fun hemp => by rw [hemp] at hdead; simp at hdead
      · exfalso; rw [h2, hGself, hgf] at h; simp at h
    · rw [hGeq r' h2] at h; rw [hBindeq]; exact hI.gradeA_needs_bind r' h
  · intro r' id' hmem hcall
    rw [hCalleq] at hcall
    rw [(hCprocs id').2]
    exact hI.call_round r' id' (hCF ▸ hmem) hcall
  · intro r' id' hmem hcalled
    exact hClosedTo r' (hI.w_called r' id' (hCF ▸ hmem) hcalled)
  · intro r' id' hmem hround
    rw [(hCprocs id').2] at hround
    exact hI.round_flip r' id' (hCF ▸ hmem) hround
  · intro id' hmem hround hphase
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid, hc'eq, CoreState.setProc_procs_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · rw [(hCprocs id').2] at hround
        rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hphase
        rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid]
        exact hI.est0 id' (hCF ▸ hmem) hround hphase
    · rw [(hCprocs id').2] at hround
      rw [hc'eq] at hphase
      rw [hc'eq]
      exact hI.est0 id' (hCF ▸ hmem) hround hphase
  · intro id' b' hlg
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · -- the fresh `A`-return certifies itself: its fire-time pair plus `hFreshCommit`
        rw [hid, hc'eq, CoreState.setProc_procs_self] at hlg
        rw [Option.some_inj] at hlg
        refine ⟨r, by rw [Function.update_self]; exact hGradeTrueOfA b' hlg, ?_, ?_⟩
        · rw [hBindeq]
          rcases hRetInfo with ⟨v, hoev, -, hdead⟩ | ⟨hoe, -⟩
          · have hb'eq : out.est = some b' := by simp [hlg]
            rw [hb'eq] at hoev
            rw [Option.some_inj.mp hoev]
            exact hdead
          · exfalso; rw [hlg] at hoe; simp at hoe
        · rcases hRetInfo with ⟨v, hoev, hlive, hdead⟩ | ⟨hoe, -⟩
          · have hb'eq : out.est = some b' := by simp [hlg]
            rw [hb'eq] at hoev
            have hveq := Option.some_inj.mp hoev
            have hgne : (g r).grade ≠ some false := fun hf => by
              have h1 := hGgradeFalse hf
              rw [hGradeTrueOfA b' hlg] at h1
              simp at h1
            exact hFreshCommit b' hgne (hveq ▸ hdead) (hveq ▸ hlive)
          · exfalso; rw [hlg] at hoe; simp at hoe
      · rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hlg
        exact (hI.grade_A_src id' b' hlg).imp (fun r0 => hCertTrans r0 b')
    · rw [hc'eq] at hlg
      exact (hI.grade_A_src id' b' hlg).imp (fun r0 => hCertTrans r0 b')
  · intro r' id' hmem hround hphase
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · have hround' : (c.procs id).round = r' := by
          rw [hid] at hround
          simpa [hc'eq, CoreState.setProc_procs_self] using hround
        have hreq : r' = r := hround'.symm.trans hr
        simp only [hid, hreq, hc'eq, CoreState.setProc_procs_self]
        refine ⟨fun he => ?_, fun b hb => ?_⟩
        · rcases hRetInfo with ⟨v, hoev, -⟩ | ⟨-, hgf⟩
          · exfalso; rw [hoev] at he; simp at he
          · refine ⟨by rw [Function.update_self]; exact hgf, fun r₀ hr0 hgr0 => ?_⟩
            by_cases hr0eq : r₀ = r
            · rw [hr0eq, Function.update_self] at hgr0
              exact absurd (hgr0.symm.trans hgf) (by simp)
            · rw [hGeq r₀ hr0eq] at hgr0
              exact hNoCAbove r₀ (by omega) hgr0 hgf
        · rw [hBindeq]
          rcases hRetInfo with ⟨v, hoev, -, hdead⟩ | ⟨hoe, -⟩
          · rw [hoev] at hb
            rw [← Option.some_inj.mp hb]
            exact hdead
          · exfalso; rw [hoe] at hb; exact absurd hb (by simp)
      · rw [(hCprocs id').2] at hround
        rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hphase
        obtain ⟨hnone, hsome⟩ := hI.est_ret r' id' (hCF ▸ hmem) hround hphase
        rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid]
        refine ⟨fun he => ?_, fun b hb => by rw [hBindeq]; exact hsome b hb⟩
        obtain ⟨hg0, hno⟩ := hnone he
        refine ⟨?_, fun r₀ hr0 hgr0 => ?_⟩
        · by_cases hrr : r' = r
          · rw [hrr, Function.update_self]; exact hGgradeFalse (by rw [← hrr]; exact hg0)
          · rw [hGeq r' hrr]; exact hg0
        · by_cases hr0eq : r₀ = r
          · rw [hr0eq, Function.update_self] at hgr0
            by_cases hrr : r' = r
            · exact absurd hgr0 (by rw [hGgradeFalse (by rw [← hrr]; exact hg0)]; simp)
            · have hgrfalse : (g r).grade = some false := hI.c_chain_down r r' (by omega) hg0
              rw [hGgradeFalse hgrfalse] at hgr0
              simp at hgr0
          · rw [hGeq r₀ hr0eq] at hgr0
            exact hno r₀ hr0 hgr0
    · rw [hc'eq] at hround hphase
      obtain ⟨hnone, hsome⟩ := hI.est_ret r' id' (hCF ▸ hmem) hround hphase
      rw [hc'eq]
      refine ⟨fun he => ?_, fun b hb => by rw [hBindeq]; exact hsome b hb⟩
      obtain ⟨hg0, hno⟩ := hnone he
      refine ⟨?_, fun r₀ hr0 hgr0 => ?_⟩
      · by_cases hrr : r' = r
        · rw [hrr, Function.update_self]; exact hGgradeFalse (by rw [← hrr]; exact hg0)
        · rw [hGeq r' hrr]; exact hg0
      · by_cases hr0eq : r₀ = r
        · rw [hr0eq, Function.update_self] at hgr0
          by_cases hrr : r' = r
          · exact absurd hgr0 (by rw [hGgradeFalse (by rw [← hrr]; exact hg0)]; simp)
          · have hgrfalse : (g r).grade = some false := hI.c_chain_down r r' (by omega) hg0
            rw [hGgradeFalse hgrfalse] at hgr0
            simp at hgr0
        · rw [hGeq r₀ hr0eq] at hgr0
          exact hno r₀ hr0 hgr0
  · intro r' v h
    rw [hBindeq (r' + 1)] at h
    rcases hI.bind_succ r' v h with hbv | ⟨hgf, hw0⟩
    · rw [hBindeq r']; exact Or.inl hbv
    · by_cases h2 : r' = r
      · rw [h2] at hgf hw0 ⊢; rw [Function.update_self]
        exact Or.inr ⟨hGgradeFalse hgf, hw0⟩
      · rw [hGeq r' h2]; exact Or.inr ⟨hgf, hw0⟩
  · intro r' id' v hmem hcall
    rw [hCalleq] at hcall
    rcases hI.call_prov r' id' v (hCF ▸ hmem) hcall with hbv | ⟨hgf, hw0⟩
    · rw [hBindeq r']; exact Or.inl hbv
    · by_cases h2 : r' = r
      · rw [h2] at hgf hw0 ⊢; rw [Function.update_self]
        exact Or.inr ⟨hGgradeFalse hgf, hw0⟩
      · rw [hGeq r' h2]; exact Or.inr ⟨hgf, hw0⟩
  · intro r' id' hmem hround hphase v hest
    rw [(hCprocs id').2] at hround
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid, hc'eq, CoreState.setProc_procs_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hphase hest
        rcases hI.est_prev r' id' (hCF ▸ hmem) hround hphase v hest with hbv | ⟨hgf, hw0⟩
        · rw [hBindeq r']; exact Or.inl hbv
        · by_cases h2 : r' = r
          · rw [h2] at hgf hw0 ⊢; rw [Function.update_self]
            exact Or.inr ⟨hGgradeFalse hgf, hw0⟩
          · rw [hGeq r' h2]; exact Or.inr ⟨hgf, hw0⟩
    · rw [hc'eq] at hphase hest
      rcases hI.est_prev r' id' (hCF ▸ hmem) hround hphase v hest with hbv | ⟨hgf, hw0⟩
      · rw [hBindeq r']; exact Or.inl hbv
      · by_cases h2 : r' = r
        · rw [h2] at hgf hw0 ⊢; rw [Function.update_self]
          exact Or.inr ⟨hGgradeFalse hgf, hw0⟩
        · rw [hGeq r' h2]; exact Or.inr ⟨hgf, hw0⟩
  · intro r' h
    by_cases h2 : r' = r
    · rw [h2] at h ⊢
      rw [hGeq (r + 1) (by omega)] at h
      rw [Function.update_self]
      exact hGgradeFalse (hI.c_chain r h)
    · by_cases h1 : r' + 1 = r
      · rw [h1, Function.update_self] at h
        rw [hGeq r' h2]
        exact hI.c_chain_of_both_supports r' (by rw [h1]; exact hCsupp h true)
          (by rw [h1]; exact hCsupp h false)
      · rw [hGeq (r' + 1) h1] at h
        rw [hGeq r' h2]
        exact hI.c_chain r' h
  · intro id' hmem hround hphase
    rw [(hCprocs id').2] at hround
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid, hc'eq, CoreState.setProc_procs_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hphase ⊢
        exact hI.est_prev_ne id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase ⊢
      exact hI.est_prev_ne id' (hCF ▸ hmem) hround hphase
  · intro id' b' h
    rw [hCalleq] at h
    rcases hI.input_g0_perm id' b' h with hin | hf
    · left; rw [(hCprocs id').1]; exact hin
    · right; rw [hCF]; exact hf
  · intro r' id' hmem hcalled
    rw [(hCprocs id').2]; exact hI.w_call_round r' id' (hCF ▸ hmem) hcalled
  · intro r' h
    rcases hI.flip_alock r' h with hg | hd
    · left
      by_cases hrr : r' = r
      · rw [hrr, Function.update_self]; exact hGradeNoneTrans (hrr ▸ hg)
      · rwa [hGeq r' hrr]
    · right
      by_cases hrr1 : r' - 1 = r
      · refine DissentResidue.transport (hBindeq r') (hBindeq (r' - 1)) (fun hgf => ?_)
          (fun id' => (hCprocs id').1) hd
        rw [hrr1, Function.update_self]; exact hGgradeFalse (hrr1 ▸ hgf)
      · exact DissentResidue.transport (hBindeq r') (hBindeq (r' - 1))
          (fun hgf => by rwa [hGeq (r' - 1) hrr1]) (fun id' => (hCprocs id').1) hd
  · intro id' hmem hin r'
    rw [(hCprocs id').1] at hin
    exact hI.idle_no_wcall id' (hCF ▸ hmem) hin r'
  · -- `retg_residue`'s establishment: the freshly-`retG`'d `id` at round `r` (`awaitG →
    -- toCallW`) gets a fresh grade/dissent fact from the genuine GBCA return guards
    -- (`retA`/`retC` grade the round outright; `retB`'s dissent converts to `DissentResidue`
    -- via `input_g0`/`call_prov`, mirroring `DissentResidue`'s own provenance argument);
    -- everywhere else is `hTransport`-routed pass-through of the pre-state fact.
    intro r' id' hmem hp
    rcases hp with ⟨hround, hphase⟩ | hlt
    · rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid : id' = id
        · have hround' : (c.procs id).round = r' := by
            rw [hid] at hround
            simpa [hc'eq, CoreState.setProc_procs_self] using hround
          have hreq : r' = r := hround'.symm.trans hr
          rw [hreq, Function.update_self]
          cases hstepG with
          | retA _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; left; rw [hgr']; simp
          | retC _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; left; rw [hgr']; simp
          | retB _ v hlive hdead hw _ =>
            rw [PMF.mem_support_pure_iff] at hgr'
            by_cases hgn : (g r).grade = none
            · right
              obtain ⟨id0, hid0F, hcall0⟩ :=
                GBCA.exists_honest_caller hw (by rw [hI.F_g r]; exact hI.F_card)
              have hcF0 : id0 ∉ c.F := by rw [← hI.F_g r]; exact hid0F
              refine ⟨v, by rw [hBindeq r]; exact hdead, ?_⟩
              by_cases hr0 : r = 0
              · rw [if_pos hr0]
                refine ⟨id0, ?_⟩
                rw [(hCprocs id0).1]
                exact hI.input_g0 id0 (!v) hcF0 (by rw [← hr0]; exact hcall0)
              · rw [if_neg hr0]
                have heqr : r - 1 + 1 = r := by omega
                have hcp := hI.call_prov (r - 1) id0 (!v) hcF0 (by rw [heqr]; exact hcall0)
                rcases hcp with hbv | ⟨hgf, -⟩
                · left; rw [hGeq (r - 1) (by omega)]; simpa using hbv
                · right; rw [hGeq (r - 1) (by omega)]; exact hgf
            · left; rw [hgr']; exact hgn
        · rw [(hCprocs id').2] at hround
          rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid] at hphase
          exact hTransport r' (hI.retg_residue r' id' (hCF ▸ hmem) (Or.inl ⟨hround, hphase⟩))
      · rw [(hCprocs id').2] at hround
        rw [hc'eq] at hphase
        exact hTransport r' (hI.retg_residue r' id' (hCF ▸ hmem) (Or.inl ⟨hround, hphase⟩))
    · rw [(hCprocs id').2] at hlt
      exact hTransport r' (hI.retg_residue r' id' (hCF ▸ hmem) (Or.inr hlt))
  · intro r' id' hmem hcalled
    exact hTransport r' (hI.wcalled_residue r' id' (hCF ▸ hmem) hcalled)
  · intro r' h
    rw [hBindeq] at h
    exact GBCA.SpecState.quorum_of_eq (hFgeq r') (hCalleq r') (hI.bound_quorum r' h)
  · -- I26: `retG` never touches `dead`, pools pass through the `c`-frame
    intro r' v hb
    rw [hBindeq r'] at hb
    exact (hI.bind_supp r' v hb).mono
      (fun id' b' h => by rw [(hCprocs id').1]; exact h) (fun x hx => by rw [hCF]; exact hx)
  · -- I27: `retG` never touches `call`/`F`; off the returning round the grade is untouched
    -- too, and on it `hCsupp` reads the guards straight off the return.
    intro r' b' hgf
    refine GBCA.callSupp_mono (s := g r') (fun id' h => by rw [hCalleq r']; exact h)
      (hFgeq r').ge ?_
    by_cases hrr : r' = r
    · rw [hrr, hGself] at hgf
      rw [hrr]
      exact hCsupp hgf b'
    · rw [hGeq r' hrr] at hgf
      exact hI.clock_supp r' b' hgf
  · -- I28: `retG` never touches `dead`/`call`/`F`
    intro r' b0 hbd
    rw [hBindeq r'] at hbd
    exact GBCA.callSupp_mono (fun id' h => by rw [hCalleq r']; exact h) (hFgeq r').ge
      (hI.dead_supp r' b0 hbd)
  · -- I29 establishment: a fresh value-bearing return's carrier meets every standing
    -- opposite carrier's permanent residue head-on — the return's own liveness guard
    -- refutes it; a `C`-return locks the round's grade instead.
    intro r₀ i0 j0 v v' hm hm' h h'
    have hred : ∀ i1 v1, Carrier P (Function.update g r gr') c' r₀ i1 v1 →
        Carrier P g c r₀ i1 v1 ∨ (i1 = id ∧ r₀ = r ∧ out.est = some v1) := by
      intro i1 v1 hc1
      rcases hc1 with hcall | ⟨he, hk⟩
      · exact Or.inl (Or.inl (by rw [← hCalleq (r₀ + 1)]; exact hcall))
      · rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · by_cases hid1 : i1 = id
          · subst hid1
            rw [hc'eq, CoreState.setProc_procs_self] at he hk
            right
            refine ⟨rfl, ?_, he⟩
            rcases hk with ⟨hr0, -⟩ | ⟨-, hp⟩
            · rw [← hr0]; exact hr
            · exfalso; rcases hp with hp | hp | hp <;> simp at hp
          · rw [hc'eq, CoreState.setProc_procs_ne _ _ _ hid1] at he hk
            exact Or.inl (Or.inr ⟨he, hk⟩)
        · rw [hc'eq] at he hk
          exact Or.inl (Or.inr ⟨he, hk⟩)
    have hprov : ∀ j1 v1, j1 ∉ c.F → Carrier P g c r j1 v1 →
        (!v1) ∈ (g r).dead ∨ (g r).grade = some false := by
      intro j1 v1 hj hcar
      rcases hcar with hcall | ⟨he, hk⟩
      · rcases hI.call_prov r j1 v1 hj hcall with hd | ⟨hgf, -⟩
        · exact Or.inl hd
        · exact Or.inr hgf
      · rcases hk with ⟨hr0, hph⟩ | ⟨hr0, hph⟩
        · obtain ⟨-, hsome⟩ := hI.est_ret r j1 hj hr0 hph
          exact Or.inl (hsome v1 he)
        · rcases hI.est_prev r j1 hj hr0 hph v1 he with hd | ⟨hgf, -⟩
          · exact Or.inl hd
          · exact Or.inr hgf
    have hnewpin : ∀ vnew j1 v1, j1 ∉ c.F → out.est = some vnew → Carrier P g c r j1 v1 →
        v1 = vnew ∨ (g r).grade = some false := by
      intro vnew j1 v1 hj hoev hcar
      rcases hprov j1 v1 hj hcar with hres | hgf
      · rcases hRetInfo with ⟨u, hoev', hulive, -⟩ | ⟨hoe, -⟩
        · have hu : u = vnew := Option.some_inj.mp (hoev'.symm.trans hoev)
          rw [hu] at hulive
          left
          by_contra hne
          have hv' : (!v1) = vnew := by revert hne; cases vnew <;> cases v1 <;> simp
          exact hulive (hv' ▸ hres)
        · rw [hoe] at hoev; simp at hoev
      · exact Or.inr hgf
    have hGradeTo : ∀ r₁, (g r₁).grade = some false →
        (Function.update g r gr' r₁).grade = some false := by
      intro r₁ hgf
      by_cases h2 : r₁ = r
      · rw [h2, hGself]; exact hGgradeFalse (h2 ▸ hgf)
      · rwa [hGeq r₁ h2]
    rcases hred i0 v h with hold0 | ⟨-, hreq0, hev0⟩
    · rcases hred j0 v' h' with hold1 | ⟨-, hreq1, hev1⟩
      · exact (hI.carrier_agree r₀ i0 j0 v v' (hCF ▸ hm) (hCF ▸ hm') hold0 hold1).imp
          (fun x => x) (hGradeTo r₀)
      · rcases hnewpin v' i0 v (hCF ▸ hm) hev1 (hreq1 ▸ hold0) with hvv | hgf
        · exact Or.inl hvv
        · exact Or.inr (by rw [hreq1]; exact hGradeTo r hgf)
    · rcases hred j0 v' h' with hold1 | ⟨-, -, hev1⟩
      · rcases hnewpin v j0 v' (hCF ▸ hm') hev0 (hreq0 ▸ hold1) with hvv | hgf
        · exact Or.inl hvv.symm
        · exact Or.inr (by rw [hreq0]; exact hGradeTo r hgf)
      · exact Or.inl (Option.some_inj.mp (hev0.symm.trans hev1))
  · -- I30 establishment: a fresh `A`-return is compared against every standing honest
    -- holder's certificate through `hpinCert`.
    intro i0 j0 b0 b0' hm hm' h h'
    have hpin : ∀ b1, out = .A b1 → ∀ j1 b1', j1 ∉ c.F → AHolder P c j1 b1' → b1' = b1 := by
      intro b1 hout j1 b1' hj hold
      have hcert : ∃ r1, ACert P g c r1 b1' := by
        rcases hold with h1 | h1
        · exact hI.grade_A_src j1 b1' h1
        · exact hI.decided_src j1 b1' hj h1
      obtain ⟨r1, hcv1⟩ := hcert
      exact hpinCert b1 hout r1 b1' hcv1
    rcases hRedH i0 b0 h with hold0 | ⟨-, hout0⟩
    · rcases hRedH j0 b0' h' with hold1 | ⟨-, hout1⟩
      · exact hI.alock_agree i0 j0 b0 b0' (hCF ▸ hm) (hCF ▸ hm') hold0 hold1
      · exact hpin b0' hout1 i0 b0 (hCF ▸ hm) hold0
    · rcases hRedH j0 b0' h' with hold1 | ⟨-, hout1⟩
      · exact (hpin b0 hout0 j0 b0' (hCF ▸ hm') hold1).symm
      · rw [hout0] at hout1
        simpa using hout1

/-- `retW`: `g` is untouched entirely; the WCC instance only touches `.ret` (not inspected by
`Inv`); the core's `stepRound` touches `est`/`lastGrade`/`round`/`phase` at `id` and
conditionally `decidedSent id` (on an `A`-grade). `round_bound`'s freshly-included round is
covered by `w_bound` (the coin having resolved closes the round); the DECIDED-on-`A`-grade
witness for `decided_src`, and the `a_commit`/`agree_locked` extension to `id`'s new round,
need the cross-round `lastGrade`-to-`(g r).grade/.dead` correlation (GBCA Graded Agreement)
that isn't a local `Inv` consequence — handed off. -/
theorem Inv.step_retW {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) (r : ℕ) (id : Fin P.n) (b : Bool)
    {μw' : PMF (WCC.SpecState P.n)} (hstepW : WCC.Step P r (w r) (.retW r id b) μw')
    {μc : PMF (CoreState P.n)} (hstepC : CoreStep P c (.retW r id b) μc)
    {wr' : WCC.SpecState P.n} (hwr' : wr' ∈ μw'.support)
    {c' : CoreState P.n} (hc' : c' ∈ μc.support) :
    Inv P g c' (Function.update w r wr') ∧ AbsFrame P g g c c' := by
  have hWeq : (Function.update w r wr' r).F = (w r).F ∧
      (Function.update w r wr' r).val = (w r).val := by
    rw [Function.update_self]; cases hstepW with
    | ret _ _ _ _ => rw [PMF.mem_support_pure_iff] at hwr'; rw [hwr']; exact ⟨rfl, rfl⟩
  have hWNe : ∀ r', r' ≠ r → Function.update w r wr' r' = w r' := fun r' h =>
    Function.update_of_ne h wr' w
  have hFweq : ∀ r', (Function.update w r wr' r').F = (w r').F := by
    intro r'; by_cases h : r' = r
    · rw [h]; exact hWeq.1
    · rw [hWNe r' h]
  have hValeq : ∀ r', (Function.update w r wr' r').val = (w r').val := by
    intro r'; by_cases h : r' = r
    · rw [h]; exact hWeq.2
    · rw [hWNe r' h]
  have hWval : (w r).val ≠ .bot := by
    cases hstepW with
    | ret _ _ h1 _ => rcases h1 with h1 | h1 <;> rw [h1] <;> simp
  have hCoinEq : ∀ v', (w r).val = .bit v' → b = v' := by
    cases hstepW with
    | ret _ _ h1 _ =>
      intro v' hv'
      rcases h1 with h1 | h1
      · rw [h1] at hv'; simp at hv'
      · rw [h1] at hv'; simpa using hv'
  have hCalledEq : ∀ r', (Function.update w r wr' r').called = (w r').called := by
    intro r'; by_cases h : r' = r
    · rw [h, Function.update_self]
      cases hstepW with
      | ret _ _ _ _ => rw [PMF.mem_support_pure_iff] at hwr'; rw [hwr']
    · rw [hWNe r' h]
  rw [coreStep_retW_iff] at hstepC
  rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
  · rw [PMF.mem_support_pure_iff] at hc'
    have hFeq : (c.stepRound id b).F = c.F := CoreState.stepRound_F _ _ _
    have hDReq : (c.stepRound id b).decidedRecv = c.decidedRecv :=
      CoreState.stepRound_decidedRecv _ _ _
    have hProcNe : ∀ id', id' ≠ id → (c.stepRound id b).procs id' = c.procs id' := by
      intro id' h; exact CoreState.stepRound_procs_ne _ _ _ h
    have hProcSelf : (c.stepRound id b).procs id = { c.procs id with
        est := some ((c.procs id).est.getD b), lastGrade := none,
        round := (c.procs id).round + 1, phase := .toCallG } := CoreState.stepRound_procs_self _ _ _
    have hInputEq : ((c.stepRound id b).procs id).input = (c.procs id).input := by
      rw [hProcSelf]
    have hRoundEq : ((c.stepRound id b).procs id).round = (c.procs id).round + 1 := by
      rw [hProcSelf]
    have hDSeq : (c.stepRound id b).decidedSent = c.decidedSent ∨
        ∃ b0, (c.procs id).lastGrade = some (.A b0) ∧
          (c.stepRound id b).decidedSent =
            Function.update c.decidedSent id (insert b0 (c.decidedSent id)) := by
      by_cases hA : ∃ b0, (c.procs id).lastGrade = some (.A b0)
      · obtain ⟨b0, hlg⟩ := hA
        exact Or.inr ⟨b0, hlg, CoreState.stepRound_decidedSent_of_A c id b b0 hlg⟩
      · exact Or.inl (CoreState.stepRound_decidedSent_of_not_A c id b (fun b1 heq => hA ⟨b1, heq⟩))
    have hDR2 : ∀ r', DissentResidue P g c r' → DissentResidue P g (c.stepRound id b) r' := by
      intro r' hd
      refine DissentResidue.transport rfl rfl (fun hh => hh) (fun id2 => ?_) hd
      by_cases hid2 : id2 = id
      · rw [hid2]; exact hInputEq
      · rw [hProcNe id2 hid2]
    -- Carrier reduction: a post-`stepRound` carrier is an old one or `id`, now holding the
    -- adopted estimate at the finished round `r`.
    have hRedW : ∀ r₀ i1 v1, Carrier P g (c.stepRound id b) r₀ i1 v1 →
        Carrier P g c r₀ i1 v1 ∨ (i1 = id ∧ r₀ = r ∧ (c.procs id).est.getD b = v1) := by
      intro r₀ i1 v1 hc1
      rcases hc1 with hcall | ⟨he, hk⟩
      · exact Or.inl (Or.inl hcall)
      · by_cases hid1 : i1 = id
        · rw [hid1, hProcSelf] at he hk
          rcases hk with ⟨-, hp | hp⟩ | ⟨hr0, -⟩
          · exact absurd hp (by simp)
          · exact absurd hp (by simp)
          · have hr0' : (c.procs id).round + 1 = r₀ + 1 := by simpa using hr0
            exact Or.inr ⟨hid1, by omega, Option.some_inj.mp he⟩
        · rw [hProcNe i1 hid1] at he hk
          exact Or.inl (Or.inr ⟨he, hk⟩)
    have hIdCarr : ∀ bv, (c.procs id).est = some bv → Carrier P g c r id bv :=
      fun bv hoe => Or.inr ⟨hoe, Or.inl ⟨hr, Or.inr hph⟩⟩
    have hCommitW : ∀ r0 b0, (g r0).grade = some true → ACommit P g c r0 b0 →
        ACommit P g (c.stepRound id b) r0 b0 := by
      rintro r0 b0 hg0 ⟨h1, h2, h3, h4⟩
      refine ⟨h1, fun r' id' b'' hrr' hmem hcall => h2 r' id' b'' hrr' (hFeq ▸ hmem) hcall,
        fun id' hmem hround => ?_, fun id0 v hmem hcar => ?_⟩
      · by_cases hid : id' = id
        · rw [hid, hRoundEq] at hround
          by_cases hle : r0 < (c.procs id).round
          · have hold := h3 id (hFeq ▸ (hid ▸ hmem)) hle
            rw [hid]; simp [hold]
          · have hr0r : r0 = r := (by omega : r0 = (c.procs id).round).trans hr
            rw [hid]; simp only [hProcSelf]
            rcases Option.eq_none_or_eq_some ((c.procs id).est) with hoe | ⟨bv, hoe⟩
            · exfalso
              obtain ⟨hg0', -⟩ :=
                (hI.est_ret r id (hFeq ▸ (hid ▸ hmem)) hr (Or.inr hph)).1 hoe
              rw [hr0r] at hg0
              exact absurd (hg0.symm.trans hg0') (by simp)
            · have hbv0 : bv = b0 :=
                h4 id bv (hFeq ▸ (hid ▸ hmem)) (hr0r ▸ hIdCarr bv hoe)
              simp [hoe, hbv0]
        · rw [hProcNe id' hid] at hround; rw [hProcNe id' hid]
          exact h3 id' (hFeq ▸ hmem) hround
      · rcases hRedW r0 id0 v hcar with hold | ⟨heq0, hreq, hev⟩
        · exact h4 id0 v (hFeq ▸ hmem) hold
        · rcases Option.eq_none_or_eq_some ((c.procs id).est) with hoe | ⟨bv, hoe⟩
          · obtain ⟨hg0', -⟩ :=
              (hI.est_ret r id (hFeq ▸ (heq0 ▸ hmem)) hr (Or.inr hph)).1 hoe
            rw [hreq] at hg0
            exact absurd (hg0.symm.trans hg0') (by simp)
          · have hv : v = bv := by rw [hoe] at hev; simpa using hev.symm
            rw [hv]
            exact h4 id bv (hFeq ▸ (heq0 ▸ hmem)) (hreq ▸ hIdCarr bv hoe)
    have hCertW : ∀ r0 b0, ACert P g c r0 b0 → ACert P g (c.stepRound id b) r0 b0 := by
      rintro r0 b0 ⟨hg0, hres0, hcm⟩
      exact ⟨hg0, hres0, hCommitW r0 b0 hg0 hcm⟩
    have hRedHW : ∀ i1 b1, AHolder P (c.stepRound id b) i1 b1 → AHolder P c i1 b1 := by
      intro i1 b1 h1
      rcases h1 with h1 | h1
      · by_cases hid1 : i1 = id
        · rw [hid1, hProcSelf] at h1; simp at h1
        · rw [hProcNe i1 hid1] at h1; exact Or.inl h1
      · rcases hDSeq with heq | ⟨b2, hlg, heq⟩
        · rw [heq] at h1; exact Or.inr h1
        · rw [heq] at h1
          by_cases hid1 : i1 = id
          · subst hid1
            rw [Function.update_self, Finset.mem_insert] at h1
            rcases h1 with rfl | h1
            · exact Or.inl hlg
            · exact Or.inr h1
          · rw [Function.update_of_ne hid1] at h1
            exact Or.inr h1
    rw [hc']
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertW r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hFeq ▸ hj) (hRedHW j b' hh)⟩
    refine ⟨fun r' => hFeq ▸ hI.F_g r', fun r' => (hFweq r').trans (hFeq ▸ hI.F_w r'),
      hFeq ▸ hI.F_card, ?_, ?_, ?_, hI.down_closed, hI.quiescent,
      fun r' h => hI.w_bound r' (by rw [← hValeq r']; exact h),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.c_chain, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r' v hb2 => (hI.bind_supp r' v hb2).mono
        (fun id2 b2 h => by
          by_cases hid2 : id2 = id
          · rw [hid2, hInputEq]; exact hid2 ▸ h
          · rw [hProcNe id2 hid2]; exact h)
        (fun x hx => by rw [hFeq]; exact hx),
      hI.clock_supp, hI.dead_supp,
      fun r₀ i0 j0 v v' hm hm' h h' => by
        rcases hRedW r₀ i0 v h with hold0 | ⟨heq0, hreq0, hev0⟩
        · rcases hRedW r₀ j0 v' h' with hold1 | ⟨heq1, hreq1, hev1⟩
          · exact hI.carrier_agree r₀ i0 j0 v v' (hFeq ▸ hm) (hFeq ▸ hm') hold0 hold1
          · rcases Option.eq_none_or_eq_some ((c.procs id).est) with hoe | ⟨bv, hoe⟩
            · obtain ⟨hg0, -⟩ :=
                (hI.est_ret r id (hFeq ▸ (heq1 ▸ hm')) hr (Or.inr hph)).1 hoe
              exact Or.inr (by rw [hreq1]; exact hg0)
            · have hv' : v' = bv := by rw [hoe] at hev1; simpa using hev1.symm
              rw [hv']
              exact hI.carrier_agree r₀ i0 id v bv (hFeq ▸ hm) (hFeq ▸ (heq1 ▸ hm')) hold0
                (hreq1 ▸ hIdCarr bv hoe)
        · rcases hRedW r₀ j0 v' h' with hold1 | ⟨heq1, hreq1, hev1⟩
          · rcases Option.eq_none_or_eq_some ((c.procs id).est) with hoe | ⟨bv, hoe⟩
            · obtain ⟨hg0, -⟩ :=
                (hI.est_ret r id (hFeq ▸ (heq0 ▸ hm)) hr (Or.inr hph)).1 hoe
              exact Or.inr (by rw [hreq0]; exact hg0)
            · have hv0 : v = bv := by rw [hoe] at hev0; simpa using hev0.symm
              rw [hv0]
              exact hI.carrier_agree r₀ id j0 bv v' (hFeq ▸ (heq0 ▸ hm)) (hFeq ▸ hm')
                (hreq0 ▸ hIdCarr bv hoe) hold1
          · exact Or.inl (hev0.symm.trans hev1),
      fun i0 j0 b0 b0' hm hm' h h' => hI.alock_agree i0 j0 b0 b0' (hFeq ▸ hm) (hFeq ▸ hm')
        (hRedHW i0 b0 h) (hRedHW j0 b0' h')⟩
    · intro id' b' hmem hcall
      by_cases h : id' = id
      · rw [h] at hmem hcall; rw [h, hInputEq]
        exact hI.input_g0 id b' (hFeq ▸ hmem) hcall
      · rw [hProcNe id' h]; exact hI.input_g0 id' b' (hFeq ▸ hmem) hcall
    · intro r' id' hmem hcall
      by_cases h : id' = id
      · rw [h] at hmem hcall; rw [h, hInputEq]
        exact hI.input_called r' id (hFeq ▸ hmem) hcall
      · rw [hProcNe id' h]; exact hI.input_called r' id' (hFeq ▸ hmem) hcall
    · intro id' hmem hne
      by_cases h : id' = id
      · rw [h, hInputEq]; rw [h] at hmem
        exact hI.phase_input id (hFeq ▸ hmem) (by rw [hph]; simp)
      · rw [hProcNe id' h] at hne ⊢
        exact hI.phase_input id' (hFeq ▸ hmem) hne
    · intro i j b' h
      rw [hDReq] at h
      rcases hDSeq with heq | ⟨b0, hlg, heq⟩
      · rw [heq]; exact hI.recv_sound i j b' h
      · rw [heq]
        by_cases hji : j = id
        -- the sent pool only grows (D12′): the old receipt stays covered
        · rw [hji] at h ⊢
          rw [Function.update_self]
          exact Finset.mem_insert_of_mem (hI.recv_sound i id b' h)
        · rw [Function.update_of_ne hji]; exact hI.recv_sound i j b' h
    · intro id' b' hmem h
      rcases hDSeq with heq | ⟨b0, hlg, heq⟩
      · rw [heq] at h
        exact (hI.decided_src id' b' (hFeq ▸ hmem) h).imp (fun r0 => hCertW r0 b')
      · rw [heq] at h
        by_cases hid : id' = id
        · rw [hid, Function.update_self, Finset.mem_insert] at h
          rcases h with rfl | h
          · exact (hI.grade_A_src id b' hlg).imp (fun r0 => hCertW r0 b')
          · exact (hI.decided_src id b' (hFeq ▸ hid ▸ hmem) h).imp (fun r0 => hCertW r0 b')
        · rw [Function.update_of_ne hid] at h
          exact (hI.decided_src id' b' (hFeq ▸ hmem) h).imp (fun r0 => hCertW r0 b')
    · intro r0 b0 hgr hbr
      exact hCommitW r0 b0 hgr (hI.a_commit r0 b0 hgr hbr)
    · intro id' hmem r' hround
      by_cases h : id' = id
      · rw [h] at hmem; rw [h, hRoundEq] at hround
        by_cases hr' : r' = (c.procs id).round
        · rw [hr', hr]; exact hI.w_bound r hWval
        · exact hI.round_bound id (hFeq ▸ hmem) r' (by omega)
      · rw [hProcNe id' h] at hround; exact hI.round_bound id' (hFeq ▸ hmem) r' hround
    · intro r' v hlast hbr hcoin id' hmem hround
      rw [hValeq] at hcoin
      by_cases hid : id' = id
      · rw [hid, hRoundEq] at hround
        by_cases hle : r' < (c.procs id).round
        · have hold := hI.agree_locked r' v hlast hbr hcoin id (hFeq ▸ (hid ▸ hmem)) hle
          rw [hid]; simp [hold]
        · have hr'eq : r' = (c.procs id).round := by omega
          have hr'r : r' = r := hr'eq.trans hr
          rw [hid]; simp only [hProcSelf]
          obtain ⟨hnone, hsome⟩ := hI.est_ret r id (hFeq ▸ (hid ▸ hmem)) hr (Or.inr hph)
          by_cases holdE : (c.procs id).est = none
          · obtain ⟨hg0, -⟩ := hnone holdE
            have hbeqv : b = v := hCoinEq v (by rw [← hr'r]; exact hcoin)
            simp [holdE, hbeqv]
          · obtain ⟨bv, hbv⟩ := Option.ne_none_iff_exists'.mp holdE
            have hbveq := hsome bv hbv
            rw [hr'r] at hbr
            have hbv0 : bv = v := by
              by_contra hne
              have hv' : (!bv) = v := by revert hne; cases bv <;> cases v <;> simp
              exact hbr.2 (hv' ▸ hbveq)
            simp [hbv, hbv0]
      · rw [hProcNe id' hid] at hround; rw [hProcNe id' hid]
        exact hI.agree_locked r' v hlast hbr hcoin id' (hFeq ▸ hmem) hround
    · exact hI.gradeA_needs_bind
    · intro r' id' hmem hcall
      by_cases h : id' = id
      · rw [h, hRoundEq]; rw [h] at hmem hcall
        exact le_trans (hI.call_round r' id (hFeq ▸ hmem) hcall) (by omega)
      · rw [hProcNe id' h]
        exact hI.call_round r' id' (hFeq ▸ hmem) hcall
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.w_called r' id' (hFeq ▸ hmem) hcalled
    · intro r' id' hmem hround
      by_cases h : id' = id
      · rw [h, hRoundEq] at hround
        rw [hValeq]
        by_cases hlt : r' < (c.procs id).round
        · exact hI.round_flip r' id (hFeq ▸ (h ▸ hmem)) hlt
        · have hreq : r' = (c.procs id).round := by omega
          rw [hreq, hr]; exact hWval
      · rw [hProcNe id' h] at hround
        rw [hValeq]; exact hI.round_flip r' id' (hFeq ▸ hmem) hround
    · intro id' hmem hround hphase
      by_cases h : id' = id
      · exfalso
        rw [h, hRoundEq] at hround
        omega
      · rw [hProcNe id' h] at hround hphase ⊢
        exact hI.est0 id' (hFeq ▸ hmem) hround hphase
    · intro id' b' hlg
      by_cases h : id' = id
      · exfalso; rw [h, hProcSelf] at hlg; simp at hlg
      · rw [hProcNe id' h] at hlg
        exact (hI.grade_A_src id' b' hlg).imp (fun r0 => hCertW r0 b')
    · intro r' id' hmem hround hphase
      by_cases h : id' = id
      · exfalso
        rw [h, hProcSelf] at hphase
        rcases hphase with hp | hp <;> simp at hp
      · rw [hProcNe id' h] at hround hphase
        rw [hProcNe id' h]
        exact hI.est_ret r' id' (hFeq ▸ hmem) hround hphase
    · intro r' v h; rw [hValeq r']; exact hI.bind_succ r' v h
    · intro r' id' v hmem hcall
      rw [hValeq r']; exact hI.call_prov r' id' v (hFeq ▸ hmem) hcall
    · intro r' id' hmem hround hphase v hest
      by_cases hid : id' = id
      · rw [hid, hRoundEq] at hround
        have hreq : r' = r := by omega
        rw [hreq, hValeq r]
        have hveq : (c.procs id).est.getD b = v := by
          have hcopy := hest
          rw [hid, hProcSelf] at hcopy
          exact Option.some_inj.mp hcopy
        have hep := hI.est_ret r id (hFeq ▸ (hid ▸ hmem)) hr (Or.inr hph)
        rcases Option.eq_none_or_eq_some ((c.procs id).est) with hoe | ⟨bv, hoe⟩
        · rw [hoe] at hveq; simp at hveq
          obtain ⟨hg0, -⟩ := hep.1 hoe
          have hWtb : (w r).val = .top ∨ (w r).val = .bit b := by
            cases hstepW with | ret _ _ h1 _ => exact h1
          rw [← hveq]; exact Or.inr ⟨hg0, hWtb.symm⟩
        · rw [hoe] at hveq; simp at hveq
          have hbveq := hep.2 bv hoe
          rw [← hveq]; exact Or.inl hbveq
      · rw [hProcNe id' hid] at hround hphase hest
        rw [hValeq r']
        exact hI.est_prev r' id' (hFeq ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      by_cases hid : id' = id
      · rw [hid, hProcSelf]; simp
      · rw [hProcNe id' hid] at hround hphase ⊢
        exact hI.est_prev_ne id' (hFeq ▸ hmem) hround hphase
    · intro r' h; rw [hValeq] at h ⊢; exact hI.w_order r' h
    · intro id' b' h
      by_cases hid : id' = id
      · rw [hid] at h ⊢
        rcases hI.input_g0_perm id b' h with hin | hf
        · left; rw [hInputEq]; exact hin
        · right; rw [hFeq]; exact hf
      · rw [hProcNe id' hid]
        rcases hI.input_g0_perm id' b' h with hin | hf
        · left; exact hin
        · right; rw [hFeq]; exact hf
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled
      by_cases h : id' = id
      · rw [h, hRoundEq]; rw [h] at hmem hcalled
        exact le_trans (hI.w_call_round r' id (hFeq ▸ hmem) hcalled) (by omega)
      · rw [hProcNe id' h]
        exact hI.w_call_round r' id' (hFeq ▸ hmem) hcalled
    · intro r' h
      rw [hValeq] at h
      rcases hI.flip_alock r' h with hg | hd
      · left; exact hg
      · right
        refine DissentResidue.transport rfl rfl (fun hh => hh) (fun id2 => ?_) hd
        by_cases hid2 : id2 = id
        · rw [hid2]; exact hInputEq
        · rw [hProcNe id2 hid2]
    · intro id' hmem hin r'
      rw [hCalledEq]
      by_cases h : id' = id
      · rw [h] at hmem hin
        rw [h]; rw [hInputEq] at hin
        exact hI.idle_no_wcall id (hFeq ▸ hmem) hin r'
      · rw [hProcNe id' h] at hin
        exact hI.idle_no_wcall id' (hFeq ▸ hmem) hin r'
    · intro r' id' hmem hp
      by_cases hid : id' = id
      · rw [hid] at hmem hp
        rcases hp with ⟨hround, hphase⟩ | hlt0
        · exfalso
          rw [hProcSelf] at hphase
          rcases hphase with h | h <;> simp at h
        · rw [hRoundEq] at hlt0
          by_cases hlt : r' < (c.procs id).round
          · rcases hI.retg_residue r' id (hFeq ▸ hmem) (Or.inr hlt) with hg | hd
            · left; exact hg
            · right; exact hDR2 r' hd
          · have hreq : r' = r := by omega
            rcases hI.retg_residue r id (hFeq ▸ hmem) (Or.inl ⟨hr, Or.inr hph⟩) with hg | hd
            · left; rw [hreq]; exact hg
            · right; rw [hreq]; exact hDR2 r hd
      · rw [hProcNe id' hid] at hp
        rcases hI.retg_residue r' id' (hFeq ▸ hmem) hp with hg | hd
        · left; exact hg
        · right; exact hDR2 r' hd
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled
      rcases hI.wcalled_residue r' id' (hFeq ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact hDR2 r' hd
  · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    refine And.intro ?_ (AbsFrame.refl P g _)
    refine ⟨hI.F_g, fun r' => (hFweq r').trans (hI.F_w r'), hI.F_card,
      hI.input_g0, hI.input_called, hI.phase_input, hI.down_closed, hI.quiescent,
      fun r' h => hI.w_bound r' (by rw [← hValeq r']; exact h),
      hI.recv_sound, hI.decided_src, hI.a_commit, hI.round_bound, ?_,
      hI.gradeA_needs_bind, hI.call_round, ?_, ?_, hI.est0, hI.grade_A_src, hI.est_ret,
      ?_, ?_, ?_, hI.c_chain, hI.est_prev_ne,
      ?_, hI.input_g0_perm, ?_, ?_, ?_, hI.retg_residue, ?_, hI.bound_quorum,
      hI.bind_supp, hI.clock_supp, hI.dead_supp, hI.carrier_agree, hI.alock_agree⟩
    · intro r' v hlast hbr hcoin id' hmem hround
      rw [hValeq] at hcoin
      exact hI.agree_locked r' v hlast hbr hcoin id' hmem hround
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.w_called r' id' hmem hcalled
    · intro r' id' hmem hround
      rw [hValeq]; exact hI.round_flip r' id' hmem hround
    · intro r' v h; rw [hValeq r']; exact hI.bind_succ r' v h
    · intro r' id' v hmem hcall; rw [hValeq r']; exact hI.call_prov r' id' v hmem hcall
    · intro r' id' hmem hround hphase v hest
      rw [hValeq r']; exact hI.est_prev r' id' hmem hround hphase v hest
    · intro r' h; rw [hValeq] at h ⊢; exact hI.w_order r' h
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.w_call_round r' id' hmem hcalled
    · intro r' h; rw [hValeq] at h; exact hI.flip_alock r' h
    · intro id' hmem hin r'; rw [hCalledEq]; exact hI.idle_no_wcall id' hmem hin r'
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.wcalled_residue r' id' hmem hcalled
/-! ### Stage C: `Abs` preservation for the stutter rows

Every one of `hybrid_step_tau`'s seven disjuncts is answered by a stutter — the
ultra-lazy twin (D16) is untouched by every hidden row and only moves at the
visible rows (`callABA`/`retABA`/`fail`), handled in `CoreSim.lean`. All six
lemmas below are instances of a single frame argument: `Abs` inspects only `F`,
the per-process `input`/`returned` projections, and the `g`-side `A`-lock
certificate — and each row preserves all three. -/

/-- `Abs` transfers along any frame that preserves `F`, the per-process
`input`/`returned` projections, and the `A`-certificate/holder-pin package. -/
theorem Abs.frame {P : Params} {g g' : ℕ → GBCA.SpecState P.n} {c c' : CoreState P.n}
    {w w' : ℕ → WCC.SpecState P.n} {a : SpecState P.n} (hA : Abs P g c w a)
    (hF : c'.F = c.F)
    (hin : ∀ id, (c'.procs id).input = (c.procs id).input)
    (hret : ∀ id, (c'.procs id).returned = (c.procs id).returned)
    (hAF : AbsFrame P g g' c c') :
    Abs P g' c' w' a := by
  refine ⟨hA.F_eq.trans hF.symm, fun id => (hA.ret_eq id).trans (hret id).symm,
    hA.coin_bot, ?_⟩
  rcases hA.phase with ⟨hb, hv, hcall, hghost⟩ | ⟨v, hb, hv, hcall, ⟨r, hcv⟩, hpin⟩
  · exact Or.inl ⟨hb, hv, fun id => (hcall id).trans (hin id).symm,
      fun id b h => hghost id b (by rw [← hin id]; exact h)⟩
  · exact Or.inr ⟨v, hb, hv, hcall, hAF.1 r v hcv, hAF.2 v ⟨r, hcv⟩ hpin⟩

/-- `Abs` never reads `w`: the twin never fires rule 5. -/
theorem Abs.w_swap {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w w' : ℕ → WCC.SpecState P.n} {a : SpecState P.n} (hA : Abs P g c w a) :
    Abs P g c w' a :=
  hA.frame rfl (fun _ => rfl) (fun _ => rfl) (AbsFrame.refl P g c)

/-- `bindUnset`: stutters; the row's `AbsFrame` package carries the certificates. -/
theorem Abs.step_gbcaTau {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n} (hA : Abs P g c w a)
    (hI : Inv P g c w) (r : ℕ)
    {μr : PMF (GBCA.SpecState P.n)} (hstep : GBCA.Step P r (g r) .tau μr)
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support) :
    Abs P (Function.update g r gr') c w a :=
  hA.frame rfl (fun _ => rfl) (fun _ => rfl) (Inv.step_gbcaTau hI r hstep hgr').2

/-- Core `τ` (DECIDED delivery/echo/byz injection): stutters; `F`/`procs` untouched. -/
theorem Abs.step_coreTau {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n} (hA : Abs P g c w a)
    (hI : Inv P g c w)
    {μc : PMF (CoreState P.n)} (hstep : CoreStep P c .tau μc)
    {c' : CoreState P.n} (hc' : c' ∈ μc.support) :
    Abs P g c' w a := by
  have hAF := (Inv.step_coreTau hI hstep hc').2
  have hCFrame : c'.F = c.F ∧ c'.procs = c.procs := by
    rw [coreStep_tau_iff] at hstep
    rcases hstep with ⟨i, j, b, hs, hr, rfl⟩ | ⟨id, b, hcnt, hs, rfl⟩ | ⟨id, b, hF, rfl⟩ <;>
      rw [PMF.mem_support_pure_iff] at hc' <;> subst hc'
    · exact ⟨CoreState.deliverDecided_F _ _ _ _, CoreState.deliverDecided_procs _ _ _ _⟩
    · exact ⟨CoreState.sendDecided_F _ _ _, CoreState.sendDecided_procs _ _ _⟩
    · exact ⟨CoreState.sendDecided_F _ _ _, CoreState.sendDecided_procs _ _ _⟩
  exact hA.frame hCFrame.1 (fun id => by rw [hCFrame.2]) (fun id => by rw [hCFrame.2]) hAF

/-- `callG`: stutters; `Abs` reads none of the touched fields, certificates ride the
row's `AbsFrame`. -/
theorem Abs.step_callG {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n}
    (hA : Abs P g c w a) (hI : Inv P g c w) (r : ℕ) (id : Fin P.n) (b : Bool)
    {μr : PMF (GBCA.SpecState P.n)} (hstepG : GBCA.Step P r (g r) (.callG r id b) μr)
    {μc : PMF (CoreState P.n)} (hstepC : CoreStep P c (.callG r id b) μc)
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support)
    {c' : CoreState P.n} (hc' : c' ∈ μc.support) :
    Abs P (Function.update g r gr') c' w a := by
  have hAF := (Inv.step_callG hI r id b hstepG hstepC hgr' hc').2
  have hCFrame : c'.F = c.F ∧ ∀ id', (c'.procs id').input = (c.procs id').input ∧
      (c'.procs id').returned = (c.procs id').returned := by
    rw [coreStep_callG_iff] at hstepC
    rcases hstepC with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩ <;>
      rw [PMF.mem_support_pure_iff] at hc' <;> subst hc'
    · refine ⟨CoreState.setProc_F _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [CoreState.setProc_procs_self]; exact ⟨rfl, rfl⟩
      · rw [CoreState.setProc_procs_ne _ _ _ h]; exact ⟨rfl, rfl⟩
    · exact ⟨rfl, fun id' => ⟨rfl, rfl⟩⟩
  exact hA.frame hCFrame.1 (fun id' => (hCFrame.2 id').1) (fun id' => (hCFrame.2 id').2) hAF

/-- `retG`: stutters; certificates and the holder pin ride the row's `AbsFrame`. -/
theorem Abs.step_retG {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n}
    (hA : Abs P g c w a) (hI : Inv P g c w) (r : ℕ) (id : Fin P.n) (out : GbcaOut)
    {μr : PMF (GBCA.SpecState P.n)} (hstepG : GBCA.Step P r (g r) (.retG r id out) μr)
    {μc : PMF (CoreState P.n)} (hstepC : CoreStep P c (.retG r id out) μc)
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support)
    {c' : CoreState P.n} (hc' : c' ∈ μc.support) :
    Abs P (Function.update g r gr') c' w a := by
  have hAF := (Inv.step_retG hI r id out hstepG hstepC hgr' hc').2
  have hCFrame : c'.F = c.F ∧ ∀ id', (c'.procs id').input = (c.procs id').input ∧
      (c'.procs id').returned = (c.procs id').returned := by
    rw [coreStep_retG_iff] at hstepC
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩ <;>
      rw [PMF.mem_support_pure_iff] at hc' <;> subst hc'
    · refine ⟨CoreState.setProc_F _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [CoreState.setProc_procs_self]; exact ⟨rfl, rfl⟩
      · rw [CoreState.setProc_procs_ne _ _ _ h]; exact ⟨rfl, rfl⟩
    · exact ⟨rfl, fun id' => ⟨rfl, rfl⟩⟩
  exact hA.frame hCFrame.1 (fun id' => (hCFrame.2 id').1) (fun id' => (hCFrame.2 id').2) hAF

/-- `callW`: stutters. -/
theorem Abs.step_callW {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n}
    (hA : Abs P g c w a) (hI : Inv P g c w) (r : ℕ) (id : Fin P.n)
    {μw' : PMF (WCC.SpecState P.n)} (hstepW : WCC.Step P r (w r) (.callW r id) μw')
    {μc : PMF (CoreState P.n)} (hstepC : CoreStep P c (.callW r id) μc)
    {wr' : WCC.SpecState P.n} (hwr' : wr' ∈ μw'.support)
    {c' : CoreState P.n} (hc' : c' ∈ μc.support) :
    Abs P g c' (Function.update w r wr') a := by
  have hAF := (Inv.step_callW hI r id hstepW hstepC hwr' hc').2
  have hCFrame : c'.F = c.F ∧ ∀ id', (c'.procs id').input = (c.procs id').input ∧
      (c'.procs id').returned = (c.procs id').returned := by
    rw [coreStep_callW_iff] at hstepC
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩ <;>
      rw [PMF.mem_support_pure_iff] at hc' <;> subst hc'
    · refine ⟨CoreState.setProc_F _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [CoreState.setProc_procs_self]; exact ⟨rfl, rfl⟩
      · rw [CoreState.setProc_procs_ne _ _ _ h]; exact ⟨rfl, rfl⟩
    · exact ⟨rfl, fun id' => ⟨rfl, rfl⟩⟩
  exact hA.frame hCFrame.1 (fun id' => (hCFrame.2 id').1) (fun id' => (hCFrame.2 id').2) hAF

/-- `retW`: stutters. -/
theorem Abs.step_retW {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n}
    (hA : Abs P g c w a) (hI : Inv P g c w) (r : ℕ) (id : Fin P.n) (b : Bool)
    {μw' : PMF (WCC.SpecState P.n)} (hstepW : WCC.Step P r (w r) (.retW r id b) μw')
    {μc : PMF (CoreState P.n)} (hstepC : CoreStep P c (.retW r id b) μc)
    {wr' : WCC.SpecState P.n} (hwr' : wr' ∈ μw'.support)
    {c' : CoreState P.n} (hc' : c' ∈ μc.support) :
    Abs P g c' (Function.update w r wr') a := by
  have hAF := (Inv.step_retW hI r id b hstepW hstepC hwr' hc').2
  have hCFrame : c'.F = c.F ∧ ∀ id', (c'.procs id').input = (c.procs id').input ∧
      (c'.procs id').returned = (c.procs id').returned := by
    rw [coreStep_retW_iff] at hstepC
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩ <;>
      rw [PMF.mem_support_pure_iff] at hc' <;> subst hc'
    · refine ⟨CoreState.stepRound_F _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [CoreState.stepRound_procs_self _ _ _]; exact ⟨rfl, rfl⟩
      · rw [CoreState.stepRound_procs_ne _ _ _ h]; exact ⟨rfl, rfl⟩
    · exact ⟨rfl, fun id' => ⟨rfl, rfl⟩⟩
  exact hA.frame hCFrame.1 (fun id' => (hCFrame.2 id').1) (fun id' => (hCFrame.2 id').2) hAF

/-! ### Assembly: `Inv` is preserved by every `hybridSpec` step -/

/-- **`Inv` is preserved.** Dispatches on the label class via `hybrid_step_callABA`/
`hybrid_step_retABA`/`hybrid_step_fail` (Stage A1) and `hybrid_step_tau` (Stage A2), calling
the matching `Inv.step_*` helper (Stage B) in each case. -/
theorem Inv.step {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w : ℕ → WCC.SpecState P.n} (hI : Inv P g c w) {l : Lab P.n} {μ : PMF (HState P)}
    (hstep : (hybridSpec P).step (g, (c, w)) l μ)
    {g' : ℕ → GBCA.SpecState P.n} {c' : CoreState P.n} {w' : ℕ → WCC.SpecState P.n}
    (hmem : (g', (c', w')) ∈ μ.support) :
    Inv P g' c' w' := by
  cases l with
  | tau =>
    rcases hybrid_step_tau P g c w μ hstep with
      ⟨r, μr, hstepG, rfl⟩ | ⟨μc, hstepC, rfl⟩ | ⟨r, μw', hstepW, rfl⟩ |
      ⟨r, id, b, μr, μc, hstepG, hstepC, rfl⟩ |
      ⟨r, id, out, μr, μc, hstepG, hstepC, rfl⟩ |
      ⟨r, id, μw', μc, hstepW, hstepC, rfl⟩ |
      ⟨r, id, b, μw', μc, hstepW, hstepC, rfl⟩
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_map_iff] at h1; rw [PMF.mem_support_pure_iff] at h2
      obtain ⟨gr', hgr', heq⟩ := h1
      have hc : c' = c := congrArg Prod.fst h2
      have hw : w' = w := congrArg Prod.snd h2
      rw [← heq, hc, hw]
      exact (Inv.step_gbcaTau hI r hstepG hgr').1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_pure_iff] at h1
      obtain ⟨h2, h3⟩ := h2
      rw [PMF.mem_support_pure_iff] at h3
      rw [h1, h3]
      exact (Inv.step_coreTau hI hstepC h2).1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_pure_iff] at h1
      obtain ⟨h2, h3⟩ := h2
      rw [PMF.mem_support_pure_iff] at h2
      rw [PMF.mem_support_map_iff] at h3
      obtain ⟨wr', hwr', heq⟩ := h3
      rw [h1, h2, ← heq]
      exact (Inv.step_wccTau hI r hstepW hwr').1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_map_iff] at h1
      obtain ⟨h2, h3⟩ := h2
      rw [PMF.mem_support_pure_iff] at h3
      obtain ⟨gr', hgr', heq⟩ := h1
      rw [← heq, h3]
      exact (Inv.step_callG hI r id b hstepG hstepC hgr' h2).1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_map_iff] at h1
      obtain ⟨h2, h3⟩ := h2
      rw [PMF.mem_support_pure_iff] at h3
      obtain ⟨gr', hgr', heq⟩ := h1
      rw [← heq, h3]
      exact (Inv.step_retG hI r id out hstepG hstepC hgr' h2).1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_pure_iff] at h1
      obtain ⟨h2, h3⟩ := h2
      rw [PMF.mem_support_map_iff] at h3
      obtain ⟨wr', hwr', heq⟩ := h3
      rw [h1, ← heq]
      exact (Inv.step_callW hI r id hstepW hstepC hwr' h2).1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_pure_iff] at h1
      obtain ⟨h2, h3⟩ := h2
      rw [PMF.mem_support_map_iff] at h3
      obtain ⟨wr', hwr', heq⟩ := h3
      rw [h1, ← heq]
      exact (Inv.step_retW hI r id b hstepW hstepC hwr' h2).1
  | callABA id b =>
    rw [hybrid_step_callABA] at hstep
    obtain ⟨μc, hstepC, rfl⟩ := hstep
    simp only [mem_support_prodPMF] at hmem
    obtain ⟨h1, h2⟩ := hmem
    rw [PMF.mem_support_pure_iff] at h1
    obtain ⟨h2, h3⟩ := h2
    rw [PMF.mem_support_pure_iff] at h3
    rw [h1, h3]
    exact (Inv.step_callABA hI id b hstepC h2).1
  | retABA id b =>
    rw [hybrid_step_retABA] at hstep
    obtain ⟨μc, hstepC, rfl⟩ := hstep
    simp only [mem_support_prodPMF] at hmem
    obtain ⟨h1, h2⟩ := hmem
    rw [PMF.mem_support_pure_iff] at h1
    obtain ⟨h2, h3⟩ := h2
    rw [PMF.mem_support_pure_iff] at h3
    rw [h1, h3]
    exact (Inv.step_retABA hI id b hstepC h2).1
  | fail id =>
    rw [hybrid_step_fail] at hstep
    subst hstep
    simp only [mem_support_prodPMF] at hmem
    obtain ⟨h1, h2⟩ := hmem
    rw [PMF.mem_support_pure_iff] at h1
    obtain ⟨h2, h3⟩ := h2
    rw [PMF.mem_support_pure_iff] at h2; rw [PMF.mem_support_pure_iff] at h3
    rw [h1, h2, h3]
    exact (Inv.step_fail hI id).1
  | callG r id b =>
    exfalso; unfold hybridSpec at hstep; rw [System.abstract_step] at hstep
    rcases hstep with ⟨hτ, -⟩ | ⟨hnotmem, -⟩
    · exact absurd hτ (by simp)
    · exact hnotmem (Lab.callG_mem_hiddenAPI r id b)
  | retG r id out =>
    exfalso; unfold hybridSpec at hstep; rw [System.abstract_step] at hstep
    rcases hstep with ⟨hτ, -⟩ | ⟨hnotmem, -⟩
    · exact absurd hτ (by simp)
    · exact hnotmem (Lab.retG_mem_hiddenAPI r id out)
  | callW r id =>
    exfalso; unfold hybridSpec at hstep; rw [System.abstract_step] at hstep
    rcases hstep with ⟨hτ, -⟩ | ⟨hnotmem, -⟩
    · exact absurd hτ (by simp)
    · exact hnotmem (Lab.callW_mem_hiddenAPI r id)
  | retW r id b =>
    exfalso; unfold hybridSpec at hstep; rw [System.abstract_step] at hstep
    rcases hstep with ⟨hτ, -⟩ | ⟨hnotmem, -⟩
    · exact absurd hτ (by simp)
    · exact hnotmem (Lab.retW_mem_hiddenAPI r id b)

end ABA
end PLTS
