/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2Extra.Fairness.Simulation.Descent
import Leslie2.Simulation.StrongSoundness
import Leslie2Extra.Fairness.Model.ResolvedScheduler

/-!
# Ranked strong simulation is sound for *fair* trace distributions

This file introduces `FairStrongProbabilisticSimulation`, the fairness-preserving analogue of
`StrongProbabilisticSimulation` (`Simulation/Defs.lean`), and states its soundness theorem

  `fairAchievableTraceDists F_C ⊆ fairAchievableTraceDists F_A`.

Ordinary strong simulation is sound for the *unconstrained* achievable trace distributions
(`StrongProbabilisticSimulation.achievableTraceDists_subset`, `Simulation/Trace.lean`), but it says
nothing about **fairness**: a concrete fair run can be matched, step by step, by an abstract run
that stalls on internal (`τ`) transitions forever and is therefore *unfair*. To carry fairness
across the simulation we equip the two systems with fairness markings `F_C`, `F_A`
(`PLTS.Fairness`, `Model/Fairness.lean`) and add just enough extra data to forbid that stalling.

## The notion

A `FairStrongProbabilisticSimulation F_C F_A R` keeps the two predicates `init` and `step` of an
ordinary strong simulation and additionally carries:

* a **pre-order `le` on concrete states** (`le_refl`, `le_trans`) whose **strict part**
  `lt a b := le a b ∧ ¬ le b a` is required to be well-founded (`lt_wf`). Only `le` and `lt_wf` are
  data; the strict order `lt` is *derived* from `le`, so `le_of_lt` and `lt_of_le_of_lt` are free
  lemmas rather than fields; and
* a **rank condition** folded into `step`: whenever the abstract transition `t_A := s_A -[l]→ μ_A`
  chosen to match a concrete transition `t_C := s_C -[l]→ μ_C` is *unfair* in `F_A`, the concrete
  successors must descend in the order — **strictly** (`lt s'_C s_C`) if `t_C` is *fair* in `F_C`,
  and **non-strictly** (`le s'_C s_C`) if `t_C` is *unfair*, for every `s'_C ∈ μ_C.support`; and
* a **fair-deadlock preservation** clause: if `(s_C, s_A) ∈ R` and `s_C` is a fair deadlock of
  `F_C`, then `s_A` is a fair deadlock of `F_A`.

(The rank clause lives inside `step` rather than in a separate field because it constrains the
*specific* abstract witness `μ_A` produced by `step`, not merely the existence of some matching
transition.)

Forgetting the order data recovers an ordinary `StrongProbabilisticSimulation`
(`FairStrongProbabilisticSimulation.toStrong`), so a fair strong simulation is in particular a
strong simulation and inherits `achievableTraceDists_subset`.

## Why these two conditions are exactly what soundness needs

Drive the **coupled product** `simProd sys_C sys_A R` (`Simulation/Trace.lean`) by a fair
resolved-history execution `pe_C` of `sys_C`, and marginalise onto `sys_A`. On any run:

* **Infinite runs.** Suppose the abstract projection took only finitely many fair steps: fix `N`
  past which every abstract step is unfair. Because `pe_C` is fair, the concrete projection takes
  infinitely many fair steps (`ResolvedProbabilisticExecution.IsFair.inf_fair`). For every step
  after `N` the matched abstract transition is unfair, so the rank clause applies: the concrete rank
  is non-increasing (`le`) at unfair concrete steps and **strictly decreasing** (`lt`) at the
  infinitely many fair concrete steps. Chaining `le` across the gaps and `lt` at each fair step
  (`lt_of_le_of_lt`) produces an infinite `lt`-descending chain of concrete ranks — impossible by
  `lt_wf`. Hence the abstract run takes infinitely many fair steps and is fair.

* **Finite runs.** A run halts only from a fair deadlock (`IsFair.halt_fairDeadlock`), so the
  concrete end state `s_C` is a fair deadlock of `F_C`; its `R`-image `s_A` is then a fair deadlock
  of `F_A` by `fair_deadlock`, so the abstract run ends at a fair deadlock and is fair.

Thus every maximal run of the marginalised abstract execution is fair, i.e. the abstract execution
is fair, and (sharing labels with the concrete run) realises the same trace distribution.

## Proof architecture for `fairAchievableTraceDists_subset`

`fairAchievableTraceDists_subset` is **fully proven and axiom-clean** (`propext`,
`Classical.choice`, `Quot.sound`): trace/initial preservation, the halt clause
(`pe_A_halt_fairDeadlock`),
the infinite clause (`pe_A_inf_fair`, including the well-founded descent), and the König lift
`exists_infinite_coupled_lift` (step 4 for infinite runs — the finitely-branching-tree construction
that turns an infinite consistent abstract run into an infinite consistent coupled run under
`sys_C.ImageFinite`) are all proven. The architecture, reusing the existing resolved-scheduler
machinery:

1. **Resolved coupling lift.** Build a `ResolvedProbabilisticExecution (simProd sys_C sys_A R)`
   driven by `pe_C`'s resolved scheduler, emitting at each step the coupling `ω` supplied by
   `sim.step` (the resolved analogue of `simJointExec`, `Simulation/Trace.lean`). Record, in the
   resolved history, exactly the matched abstract distribution `μ_A`, so that the abstract step's
   fairness in `F_A` is readable back from the run.
2. **Marginalise onto `sys_A`.** Push the coupled resolved execution forward along `Prod.snd` and
   average over the concrete fibres — the resolved analogue of
   `ResolvedProbabilisticExecution.average` / `simExecMarginal` — to obtain
   `pe_A : ResolvedProbabilisticExecution sys_A` with `pe_A.initState = PMF.pure sys_A.init`.
3. **Trace preservation.** `pe_A.traceProbR = pe_C.traceProbR` (labels are shared and the product
   projects onto each factor; mirror `simProd_traceProb_eq` / `traceProb_average` for `traceProbR`).
4. **Consistency lift.** Every `pe_A`-consistent resolved run has a `pe_A`-positive coupled witness
   whose `Prod.fst` projection is a `pe_C`-consistent run of `sys_C` with the recorded abstract
   distributions (the resolved analogue of `simJointExec_probOf_R` + `average` support reasoning).
   For *infinite* runs this is where **finite branching** enters: the coupled scheduler commits to a
   *single* coupling `simCoupleF …` per concrete transition, so — although `simProd` has a continuum
   of couplings as a step *relation* — the *consistent coupled tree* is finitely branching under
   `sys_C.ImageFinite` (finitely many valid `(l, μ_C)` by image-finiteness, one `ω` each, finite
   `ω`-support). König's lemma (`exists_infinite_chain`, `Model/System.lean`) then assembles a
   finite prefix-witness at every length into an infinite coupled witness.
5. **Fairness.** Assemble `pe_A.IsFair F_A` from the witness of step 4:
   * `halt_fairDeadlock` via `sim.fair_deadlock` on the concrete fair deadlock (no finiteness);
   * `inf_fair` via `descent_of_infinitely_often` (the well-founded descent above), using
     `sim.lt_wf`, `sim.le_refl`, `sim.le_trans`, `sim.lt_of_le_of_lt`, and the rank clause of
     `sim.step`.
   Conclude `D ∈ fairAchievableTraceDists F_A`.

## Is finite branching necessary? (the fairness caveat)

**Finite branching of `sys_C` is sufficient** for the fairness half, as above: König lifts the
infinite abstract run to a coupled run, whose concrete projection is a fair `pe_C`-run, and the rank
clause + `lt_wf` finish. There is **no counterexample under `sys_C.ImageFinite`** — the obstruction
one might fear (the marginalised abstract belief "escaping to infinity", as in the `𝒟(sys)` lowering
`lowerFairR` in `Construction/DistFairLower.lean`, which genuinely needs a Prokhorov-tightness /
finite-`State` hypothesis) does **not** arise here, precisely because the coupled scheduler commits
to one coupling per concrete step, so the relevant tree is finitely branching rather than a
continuum. Whether the *unconditional* inclusion (no image-finiteness) holds is left open: without a
finite-branching bound König can fail, and a fair resolved `pe_C` over an infinitely-branching
`sys_C` might have no fair marginalised abstract witness.
-/

open Stream'

namespace PLTS

variable {State_C State_A Label : Type} [Silent Label]

/-! ### The resolved coupled execution (the lift, step 1 of the construction)

The resolved analogue of `simJointExec` (`Simulation/Trace.lean`): drive the coupled product
`simProd sys_C sys_A R` by a *resolved* execution `pe_C` of `sys_C`, consulting `pe_C` on the
*concrete resolved projection* of the product history and emitting, per concrete transition, the
single coupling `simCoupleF`. -/

/-- Project a coupled-product resolved history onto its concrete resolved history: states via
`Prod.fst`, and each recorded coupling `ω` via its concrete marginal `ω.map Prod.fst`. This is the
history `pe_C`'s resolved scheduler is consulted on. -/
noncomputable def concreteProjR (r : ResolvedExec (State_C × State_A) Label) :
    ResolvedExec State_C Label where
  init := r.init.1
  trans := r.trans.map (fun p => ((p.1.1, p.1.2.map Prod.fst), p.2.1))

/-- The current product state of a coupled-product resolved history — its end-state, defaulting to
the initial state on the (never-reached) non-terminating branch. Resolved analogue of
`simLastState`. -/
noncomputable def simLastStateR (r : ResolvedExec (State_C × State_A) Label) : State_C × State_A :=
  open Classical in
  if h : r.trans.Terminates then r.endState h else r.init

/-- Project a coupled-product resolved history onto its **abstract** resolved history: states via
`Prod.snd`, and each recorded coupling `ω` via its abstract marginal `ω.map Prod.snd`. This is the
history the marginalised abstract scheduler is consulted on. -/
noncomputable def absProjR (r : ResolvedExec (State_C × State_A) Label) :
    ResolvedExec State_A Label where
  init := r.init.2
  trans := r.trans.map (fun p => ((p.1.1, p.1.2.map Prod.snd), p.2.2))

omit [Silent Label] in
/-- `absProjR` preserves termination at each index (it is a `Seq.map`). -/
theorem absProjR_terminatedAt_iff (r : ResolvedExec (State_C × State_A) Label) (n : ℕ) :
    (absProjR r).trans.TerminatedAt n ↔ r.trans.TerminatedAt n := by
  unfold Stream'.Seq.TerminatedAt
  change ((r.trans.map _).get? n = none) ↔ _
  rw [Stream'.Seq.map_get?, Option.map_eq_none_iff]

omit [Silent Label] in
/-- `absProjR` preserves termination. -/
theorem absProjR_terminates_iff (r : ResolvedExec (State_C × State_A) Label) :
    (absProjR r).trans.Terminates ↔ r.trans.Terminates :=
  Stream'.Seq.terminates_map_iff

omit [Silent Label] in
/-- A product decoration of a terminating abstract history terminates. -/
theorem terminates_of_absProjR_eq {e_A : ResolvedExec State_A Label} (he : e_A.trans.Terminates)
    {r : ResolvedExec (State_C × State_A) Label} (hr : absProjR r = e_A) : r.trans.Terminates :=
  (absProjR_terminates_iff r).mp (by rw [hr]; exact he)

/-! ### The `absProjR`-fibre reindexing (for `absWeight_le_init`)

The absProjR analogue of the `toExec` `snocDecoration`/`exists_snocDecoration` machinery of
`Model/ResolvedScheduler.lean`. Extending an abstract history `e_A'` by a final abstract step
`((l, ν), s_A')` corresponds, on the product side, to extending a decoration `r'` of `e_A'` by a
final product step `((l, ω), (s_C', s_A'))` with `ω.map Prod.snd = ν` (a *coupling* over the
recorded abstract distribution `ν`) and a chosen concrete successor `s_C'`. The decoration is thus
indexed by
`(r', ω, s_C')` with `ω` ranging over the `Prod.snd`-fibre of `ν`. -/

omit [Silent Label] in
@[simp] theorem absProjR_init (r : ResolvedExec (State_C × State_A) Label) :
    (absProjR r).init = r.init.2 := rfl

omit [Silent Label] in
/-- The abstract projection's state at `n` is the `Prod.snd`-image of the product state at `n`.
Abstract analogue of `ResolvedExec.toExec_stateAt`. -/
theorem absProjR_stateAt (r : ResolvedExec (State_C × State_A) Label) (n : ℕ) :
    (absProjR r).stateAt n = (r.stateAt n).map Prod.snd := by
  cases n with
  | zero => rfl
  | succ k =>
    change ((r.trans.map (fun p => ((p.1.1, p.1.2.map Prod.snd), p.2.2))).get? k).map Prod.snd
        = ((r.trans.get? k).map Prod.snd).map Prod.snd
    rw [Stream'.Seq.map_get?]
    cases r.trans.get? k <;> rfl

omit [Silent Label] in
/-- `absProjR` commutes with appending a final product transition `((l, ω), (s_C', s_A'))`:
projecting the extended history is extending the projected history by `((l, ω.map Prod.snd), s_A')`.
The abstract analogue of `ResolvedExec.toExec_append_singleton`. -/
theorem absProjR_append_singleton (r' : ResolvedExec (State_C × State_A) Label)
    (l : Label) (ω : PMF (State_C × State_A)) (s' : State_C × State_A) :
    absProjR ⟨r'.init, r'.trans.append (Seq.cons ((l, ω), s') Seq.nil)⟩
      = ⟨(absProjR r').init,
          (absProjR r').trans.append (Seq.cons ((l, ω.map Prod.snd), s'.2) Seq.nil)⟩ := by
  unfold absProjR
  simp only [Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil]

omit [Silent Label] in
/-- A product decoration of the empty abstract history `⟨s₀, nil⟩` is itself `⟨(s_C, s₀), nil⟩` for
some concrete `s_C`; in particular its `trans` is empty. Abstract analogue of
`eq_nil_of_toExec_nil`. -/
theorem trans_nil_of_absProjR_nil {r : ResolvedExec (State_C × State_A) Label} {s₀ : State_A}
    (hr : absProjR r = ⟨s₀, Seq.nil⟩) : r.trans = Seq.nil := by
  have hz : (absProjR r).trans.TerminatedAt 0 := by
    rw [hr]; exact Stream'.Seq.terminatedAt_zero_iff.mpr rfl
  exact Stream'.Seq.terminatedAt_zero_iff.mp ((absProjR_terminatedAt_iff r 0).mp hz)

/-- Extend a decoration `r'` of `e_A'` by a coupling `ω` over `ν` and a concrete successor `s_C'`,
yielding a decoration of `e_A' ++ ((l, ν), s_A')`. The forward object of the fibre reindexing. -/
def absSnocDecoration (e_A' : ResolvedExec State_A Label) (l : Label) (ν : PMF State_A)
    (s_A' : State_A)
    (p : {r' : ResolvedExec (State_C × State_A) Label // absProjR r' = e_A'} ×
      {ω : PMF (State_C × State_A) // ω.map Prod.snd = ν} × State_C) :
    {r : ResolvedExec (State_C × State_A) Label //
      absProjR r = ⟨e_A'.init, e_A'.trans.append (Seq.cons ((l, ν), s_A') Seq.nil)⟩} :=
  ⟨⟨p.1.1.init, p.1.1.trans.append (Seq.cons ((l, p.2.1.1), (p.2.2, s_A')) Seq.nil)⟩, by
    rw [absProjR_append_singleton, p.2.1.2, p.1.2]⟩

omit [Silent Label] in
theorem absSnocDecoration_injective {e_A' : ResolvedExec State_A Label}
    (he' : e_A'.trans.Terminates) (l : Label) (ν : PMF State_A) (s_A' : State_A) :
    Function.Injective (@absSnocDecoration State_C State_A Label e_A' l ν s_A') := by
  rintro ⟨⟨r₁, hr₁⟩, ⟨ω₁, hω₁⟩, sC₁⟩ ⟨⟨r₂, hr₂⟩, ⟨ω₂, hω₂⟩, sC₂⟩ h
  have hAlt :
      (⟨r₁.init, r₁.trans.append (Seq.cons ((l, ω₁), (sC₁, s_A')) Seq.nil)⟩ :
          ResolvedExec (State_C × State_A) Label)
        = ⟨r₂.init, r₂.trans.append (Seq.cons ((l, ω₂), (sC₂, s_A')) Seq.nil)⟩ :=
    congrArg Subtype.val h
  rw [AlterSeq.mk.injEq] at hAlt
  obtain ⟨h_init, h_trans⟩ := hAlt
  have ht₁ : r₁.trans.Terminates := terminates_of_absProjR_eq he' hr₁
  have ht₂ : r₂.trans.Terminates := terminates_of_absProjR_eq he' hr₂
  have hlast : ((l, ω₁), (sC₁, s_A')) = ((l, ω₂), (sC₂, s_A')) :=
    Stream'.Seq.append_singleton_inj_right r₁.trans r₂.trans ht₁ ht₂ _ _ h_trans
  have htr : r₁.trans = r₂.trans :=
    Stream'.Seq.append_singleton_inj_left r₁.trans r₂.trans ht₁ ht₂ _ _ h_trans
  have hω : ω₁ = ω₂ := congrArg (fun x => x.1.2) hlast
  have hsC : sC₁ = sC₂ := congrArg (fun x => x.2.1) hlast
  have hr : r₁ = r₂ := by
    cases r₁ with | mk i₁ t₁ => cases r₂ with | mk i₂ t₂ => cases h_init; cases htr; rfl
  subst hr; subst hω; subst hsC
  rfl

omit [Silent Label] in
theorem exists_absSnocDecoration {e_A' : ResolvedExec State_A Label}
    (he' : e_A'.trans.Terminates) (l : Label) (ν : PMF State_A) (s_A' : State_A)
    (r : {r : ResolvedExec (State_C × State_A) Label //
      absProjR r = ⟨e_A'.init, e_A'.trans.append (Seq.cons ((l, ν), s_A') Seq.nil)⟩}) :
    ∃ p, absSnocDecoration e_A' l ν s_A' p = r := by
  have hmap : r.1.trans.map (fun p => ((p.1.1, p.1.2.map Prod.snd), p.2.2))
      = e_A'.trans.append (Seq.cons ((l, ν), s_A') Seq.nil) := by
    have := congrArg AlterSeq.trans r.2
    rwa [show (absProjR r.1).trans = _ from rfl] at this
  have hs1 : (Seq.cons ((l, ν), s_A') Seq.nil : Seq ((Label × PMF State_A) × State_A)).Terminates :=
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
  have hE : (e_A'.trans.append (Seq.cons ((l, ν), s_A') Seq.nil)).Terminates :=
    ⟨_, Stream'.Seq.terminatedAt_append_find he' hs1.choose_spec⟩
  have hRterm : r.1.trans.Terminates := terminates_of_absProjR_eq hE r.2
  have hne : r.1.trans.toList hRterm ≠ [] := by
    intro hnil
    have htrans_nil : r.1.trans = Seq.nil := by
      have h := Stream'.Seq.ofList_toList r.1.trans hRterm
      rw [hnil, Stream'.Seq.ofList_nil] at h
      exact h.symm
    rw [htrans_nil, Stream'.Seq.map_nil] at hmap
    have h0 : (e_A'.trans.append (Seq.cons ((l, ν), s_A') Seq.nil)).get? (Nat.find he')
        = some ((l, ν), s_A') := by
      have := Stream'.Seq.get?_append_find he' (Seq.cons ((l, ν), s_A') Seq.nil) 0
      rw [Nat.add_zero] at this
      rw [this]; rfl
    rw [← hmap] at h0
    simp at h0
  obtain ⟨prev, last, hprev, hsplit, _, _⟩ := Stream'.Seq.exists_split_last r.1.trans hRterm hne
  have hmap' : (prev.map (fun p => ((p.1.1, p.1.2.map Prod.snd), p.2.2))).append
        (Seq.cons ((fun p => ((p.1.1, p.1.2.map Prod.snd), p.2.2)) last) Seq.nil)
      = e_A'.trans.append (Seq.cons ((l, ν), s_A') Seq.nil) := by
    have h1 : (prev.append (Seq.cons last Seq.nil)).map
          (fun p => ((p.1.1, p.1.2.map Prod.snd), p.2.2))
        = e_A'.trans.append (Seq.cons ((l, ν), s_A') Seq.nil) := by rw [← hsplit]; exact hmap
    rwa [Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil] at h1
  have htprevmap : (prev.map (fun p => ((p.1.1, p.1.2.map Prod.snd), p.2.2))).Terminates :=
    Stream'.Seq.terminates_map_iff.mpr hprev
  have hprevmap : prev.map (fun p => ((p.1.1, p.1.2.map Prod.snd), p.2.2)) = e_A'.trans :=
    Stream'.Seq.append_singleton_inj_left _ _ htprevmap he' _ _ hmap'
  have hlast : (fun p => ((p.1.1, p.1.2.map Prod.snd), p.2.2)) last = ((l, ν), s_A') :=
    Stream'.Seq.append_singleton_inj_right _ _ htprevmap he' _ _ hmap'
  -- decompose the found `last` product step
  have hlab : last.1.1 = l := congrArg (fun x => x.1.1) hlast
  have hmapsnd : last.1.2.map Prod.snd = ν := congrArg (fun x => x.1.2) hlast
  have hsA : last.2.2 = s_A' := congrArg (fun x => x.2) hlast
  have hlast_eq : last = ((l, last.1.2), (last.2.1, s_A')) := by
    obtain ⟨⟨ll, ωω⟩, ⟨sc, sa⟩⟩ := last
    simp only at hlab hsA
    subst hlab; subst hsA; rfl
  have h_init : r.1.init.2 = e_A'.init := by
    have := congrArg AlterSeq.init r.2
    rwa [show (absProjR r.1).init = r.1.init.2 from rfl] at this
  refine ⟨(⟨⟨r.1.init, prev⟩, ?_⟩, ⟨last.1.2, hmapsnd⟩, last.2.1), ?_⟩
  · unfold absProjR
    rw [hprevmap]
    change (⟨r.1.init.2, e_A'.trans⟩ : ResolvedExec State_A Label) = e_A'
    rw [h_init]
  · apply Subtype.ext
    change (⟨r.1.init, prev.append (Seq.cons ((l, last.1.2), (last.2.1, s_A')) Seq.nil)⟩ :
      ResolvedExec (State_C × State_A) Label) = r.1
    rw [← hlast_eq, ← hsplit]

/-- A **ranked (fair) strong probabilistic simulation** from `sys_C` to `sys_A`, along a state
relation `R : State_C → State_A → Prop`, that preserves the *fair* achievable trace distributions
for the markings `F_C : Fairness sys_C` and `F_A : Fairness sys_A`.

It is an ordinary strong simulation (`init`, `step`) equipped with a **pre-order `le`** on concrete
states whose **strict part `lt a b := le a b ∧ ¬ le b a`** is well-founded — subject to a rank
condition (folded into `step`) and a fair-deadlock preservation clause:

* `init`: the initial concrete state is `R`-related to the initial abstract state.
* `step`: every concrete transition `s_C -[l]→ μ_C` from an `R`-related pair `(s_C, s_A)` is matched
  by a strong abstract transition `s_A -[l]→ μ_A` with `PMFRel R μ_C μ_A`, and — *when the matching
  transition `μ_A` is unfair in `F_A`* — the concrete successors descend in the order: **strictly**
  (`lt s'_C s_C`, spelled out as `le s'_C s_C ∧ ¬ le s_C s'_C`) if `μ_C` is fair in `F_C`,
  **non-strictly** (`le s'_C s_C`) if `μ_C` is unfair, for every `s'_C ∈ μ_C.support`.
* `fair_deadlock`: an `R`-image of a fair deadlock of `F_C` is a fair deadlock of `F_A`.

The order data is exactly what makes an abstract run that answers a fair concrete run with unfair
`τ`-steps unable to stall forever: strict descent at the (infinitely many) fair concrete steps,
against the well-founded strict order `lt`, forces the abstract side to fire fairly infinitely
often. The strict order `lt` is *derived* from `le` (`FairStrongProbabilisticSimulation.lt`), so
`le_of_lt`, transitivity of `lt`, and `lt_of_le_of_lt` are all free lemmas. -/
structure FairStrongProbabilisticSimulation
    {sys_C : System State_C Label} {sys_A : System State_A Label}
    (F_C : Fairness sys_C) (F_A : Fairness sys_A)
    (R : State_C → State_A → Prop) where
  /-- The initial concrete state is matched by the initial abstract state. -/
  init : R sys_C.init sys_A.init
  /-- A pre-order on concrete states (the "rank"). Its strict part `lt a b := le a b ∧ ¬ le b a` is
  the order along which fair steps make progress. -/
  le : State_C → State_C → Prop
  /-- `le` is reflexive (pre-order). -/
  le_refl : ∀ s, le s s
  /-- `le` is transitive (pre-order). -/
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  /-- The **strict part** of `le` is well-founded: no infinite strictly-descending chain of
  ranks. -/
  lt_wf : WellFounded (fun a b => le a b ∧ ¬ le b a)
  /-- Every concrete transition is matched by a strong abstract transition coupled by `R`; and if
  that abstract transition is *unfair* in `F_A`, the concrete successors descend in the order —
  strictly (`le s'_C s_C ∧ ¬ le s_C s'_C`) when the concrete transition is fair, non-strictly
  (`le s'_C s_C`) when it is unfair. -/
  step : ∀ s_C s_A, R s_C s_A →
    ∀ l μ_C, sys_C.step s_C l μ_C →
    ∃ μ_A, sys_A.step s_A l μ_A ∧ PMFRel R μ_C μ_A ∧
      (¬ F_A.fair s_A l μ_A →
        (F_C.fair s_C l μ_C → ∀ s'_C ∈ μ_C.support, le s'_C s_C ∧ ¬ le s_C s'_C) ∧
        (¬ F_C.fair s_C l μ_C → ∀ s'_C ∈ μ_C.support, le s'_C s_C))
  /-- Fair deadlocks are reflected: the `R`-image of a fair deadlock of `F_C` is a fair deadlock of
  `F_A`. -/
  fair_deadlock : ∀ s_C s_A, R s_C s_A → F_C.FairDeadlock s_C → F_A.FairDeadlock s_A

namespace FairStrongProbabilisticSimulation

variable {sys_C : System State_C Label} {sys_A : System State_A Label}
  {F_C : Fairness sys_C} {F_A : Fairness sys_A} {R : State_C → State_A → Prop}

/-- The **strict part** of the rank pre-order `le`: `lt a b` (`a` strictly below `b`) means
`le a b ∧ ¬ le b a`. This is the order along which fair steps make progress; `lt_wf` is its
well-foundedness. -/
def lt (sim : FairStrongProbabilisticSimulation F_C F_A R) (a b : State_C) : Prop :=
  sim.le a b ∧ ¬ sim.le b a

/-- The strict part implies the pre-order. -/
theorem le_of_lt (sim : FairStrongProbabilisticSimulation F_C F_A R) {a b : State_C}
    (h : sim.lt a b) : sim.le a b := h.1

/-- `lt` is compatible with `le`: a `le`-step below a `lt`-step is a `lt`-step (derived from the
pre-order axioms, no longer taken as data). -/
theorem lt_of_le_of_lt (sim : FairStrongProbabilisticSimulation F_C F_A R) {a b c : State_C}
    (hab : sim.le a b) (hbc : sim.lt b c) : sim.lt a c :=
  ⟨sim.le_trans hab hbc.1, fun hca => hbc.2 (sim.le_trans hca hab)⟩

/-- Forgetting the order and fairness data, a fair strong simulation is an ordinary
`StrongProbabilisticSimulation`. In particular it inherits
`StrongProbabilisticSimulation.achievableTraceDists_subset` (soundness for the *unconstrained*
achievable trace distributions). -/
def toStrong (sim : FairStrongProbabilisticSimulation F_C F_A R) :
    StrongProbabilisticSimulation sys_C sys_A R where
  init := sim.init
  step s_C s_A h l μ_C hstep := by
    obtain ⟨μ_A, hstepA, hrel, _⟩ := sim.step s_C s_A h l μ_C hstep
    exact ⟨μ_A, hstepA, hrel⟩

/-! ### The **fair** coupling extractor

Unlike `simCouple` (`Simulation/Trace.lean`), which picks an *arbitrary* `PMFRel` witness through
`sim.toStrong` and hence forgets the rank clause, `simCoupleF` extracts the coupling from
`sim.step`'s own witness — the one that **carries the rank clause** (`simCoupleF_rank`). Its
abstract marginal
`(simCoupleF …).map Prod.snd` is therefore the rank-respecting `μ_A`, which is exactly what the
fairness descent (Phase 4) needs. It has the same marginal/step interface as `simCouple`
(`simCoupleF_map_fst`, `simCoupleF_step`), so the trace development is unaffected. -/

/-- The coupling from `sim.step`'s fair witness (the rank-respecting one). -/
noncomputable def simCoupleF (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (p : State_C × State_A) (l : Label) (μ_C : PMF State_C) : PMF (State_C × State_A) :=
  open Classical in
  if h : R p.1 p.2 ∧ sys_C.step p.1 l μ_C then
    ((sim.step p.1 p.2 h.1 l μ_C h.2).choose_spec.2.1).choose
  else PMF.pure p

/-- First marginal of the fair coupling is `μ_C`. -/
theorem simCoupleF_map_fst (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (p : State_C × State_A) (l : Label) (μ_C : PMF State_C)
    (h : R p.1 p.2 ∧ sys_C.step p.1 l μ_C) :
    (simCoupleF sim p l μ_C).map Prod.fst = μ_C := by
  rw [simCoupleF, dif_pos h]
  exact ((sim.step p.1 p.2 h.1 l μ_C h.2).choose_spec.2.1).choose_spec.1

/-- Second marginal of the fair coupling is `sim.step`'s abstract witness `μ_A`. -/
theorem simCoupleF_map_snd (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (p : State_C × State_A) (l : Label) (μ_C : PMF State_C)
    (h : R p.1 p.2 ∧ sys_C.step p.1 l μ_C) :
    (simCoupleF sim p l μ_C).map Prod.snd = (sim.step p.1 p.2 h.1 l μ_C h.2).choose := by
  rw [simCoupleF, dif_pos h]
  exact ((sim.step p.1 p.2 h.1 l μ_C h.2).choose_spec.2.1).choose_spec.2.1

/-- The fair coupling realises a valid `simProd`-step from `p`. -/
theorem simCoupleF_step (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (p : State_C × State_A) (l : Label) (μ_C : PMF State_C)
    (h : R p.1 p.2 ∧ sys_C.step p.1 l μ_C) :
    (simProd sys_C sys_A R).step p l (simCoupleF sim p l μ_C) := by
  have hspec := (sim.step p.1 p.2 h.1 l μ_C h.2).choose_spec
  have hrel := hspec.2.1.choose_spec
  refine ⟨?_, ?_, ?_⟩
  · rw [simCoupleF_map_fst sim p l μ_C h]; exact h.2
  · rw [simCoupleF, dif_pos h, hrel.2.1]; exact hspec.1
  · intro q hq; rw [simCoupleF, dif_pos h] at hq; exact hrel.2.2 q hq

/-- **The rank clause is preserved by the fair coupling.** If the recorded abstract marginal
`(simCoupleF …).map Prod.snd` is *unfair* in `F_A`, the concrete successors descend — strictly if
the concrete transition is fair, non-strictly otherwise. This is the fairness content the arbitrary
`simCouple` lacks. -/
theorem simCoupleF_rank (sim : FairStrongProbabilisticSimulation F_C F_A R)
    (p : State_C × State_A) (l : Label) (μ_C : PMF State_C)
    (h : R p.1 p.2 ∧ sys_C.step p.1 l μ_C)
    (hunfair : ¬ F_A.fair p.2 l ((simCoupleF sim p l μ_C).map Prod.snd)) :
    (F_C.fair p.1 l μ_C → ∀ s'_C ∈ μ_C.support, sim.lt s'_C p.1) ∧
    (¬ F_C.fair p.1 l μ_C → ∀ s'_C ∈ μ_C.support, sim.le s'_C p.1) := by
  rw [simCoupleF_map_snd sim p l μ_C h] at hunfair
  exact (sim.step p.1 p.2 h.1 l μ_C h.2).choose_spec.2.2 hunfair

/-- The **resolved coupled scheduler**: on a product resolved history `r`, run `pe_C`'s resolved
scheduler on the concrete resolved projection `concreteProjR r`; for each emitted `(l, μ_C)`, if the
`R`/step guard holds at the current joint state `simLastStateR r`, emit `(l, simCoupleF …)`, else
halt. Resolved analogue of `simJointSched`; validity is `simCoupleF_step` on the forced guard. The
fair coupling `simCoupleF` (not the arbitrary `simCouple`) is used so the recorded abstract
marginals carry the rank clause (`simCoupleF_rank`), needed for fair soundness. -/
noncomputable def simJointSchedR
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R) :
    ResolvedScheduler (simProd sys_C sys_A R) where
  next r :=
    open Classical in
    (pe_C.scheduler.next (concreteProjR r)).bind (fun o =>
      match o with
      | none => PMF.pure none
      | some (l, μ_C) =>
        if h : R (simLastStateR r).1 (simLastStateR r).2 ∧
            sys_C.step (simLastStateR r).1 l μ_C then
          PMF.pure (some (l, simCoupleF sim (simLastStateR r) l μ_C))
        else PMF.pure none)
  valid := by
    classical
    intro r n s r_term_n r_stateAt_eq l ω h_supp
    -- Identify `s = r.endState`, i.e. `s = simLastStateR r` (mirrors `simJointSched.valid`).
    have hT : r.trans.Terminates := ⟨n, r_term_n⟩
    have h_find_le : Nat.find hT ≤ n := Nat.find_le r_term_n
    have h_n_le : n ≤ Nat.find hT := by
      by_contra h_lt
      push Not at h_lt
      rcases n with _ | m
      · exact absurd h_lt (Nat.not_lt_zero _)
      · have hk_ge : Nat.find hT ≤ m := Nat.lt_succ_iff.mp h_lt
        have h_term_k : r.trans.TerminatedAt m :=
          Stream'.Seq.terminated_stable r.trans hk_ge (Nat.find_spec hT)
        have h_state_none : r.stateAt (m + 1) = none := by
          change (r.trans.get? m).map Prod.snd = none
          rw [show r.trans.get? m = none from h_term_k]; rfl
        rw [h_state_none] at r_stateAt_eq
        exact Option.some_ne_none s r_stateAt_eq.symm
    have h_n_eq : n = Nat.find hT := le_antisymm h_n_le h_find_le
    have h_s_eq : s = r.endState hT := by
      have h := AlterSeq.stateAt_find_eq_endState r hT
      rw [← h_n_eq] at h; rw [h] at r_stateAt_eq
      exact (Option.some.inj r_stateAt_eq).symm
    have h_last : simLastStateR r = s := by rw [h_s_eq, simLastStateR, dif_pos hT]
    -- The emitted `(l, ω)` forces the guard true, so `simCouple` is a real coupling.
    change some (l, ω) ∈ ((pe_C.scheduler.next (concreteProjR r)).bind (fun o =>
      match o with
      | none => PMF.pure none
      | some (l', μ_C) =>
        if h : R (simLastStateR r).1 (simLastStateR r).2 ∧
            sys_C.step (simLastStateR r).1 l' μ_C then
          PMF.pure (some (l', simCoupleF sim (simLastStateR r) l' μ_C))
        else PMF.pure none)).support at h_supp
    rw [PMF.mem_support_bind_iff] at h_supp
    obtain ⟨o, _, h_supp⟩ := h_supp
    cases o with
    | none =>
      rw [PMF.mem_support_pure_iff] at h_supp
      exact absurd h_supp.symm (by simp)
    | some lμ =>
      obtain ⟨l', μ_C⟩ := lμ
      simp only at h_supp
      by_cases hg : R (simLastStateR r).1 (simLastStateR r).2 ∧
          sys_C.step (simLastStateR r).1 l' μ_C
      · rw [dif_pos hg, PMF.mem_support_pure_iff] at h_supp
        rw [Option.some.injEq, Prod.mk.injEq] at h_supp
        obtain ⟨rfl, rfl⟩ := h_supp
        rw [h_last] at hg ⊢
        exact simCoupleF_step sim s l μ_C hg
      · rw [dif_neg hg, PMF.mem_support_pure_iff] at h_supp
        exact absurd h_supp (by simp)

/-- The **resolved coupled execution**: Dirac on the joint initial state, driven by the coupled
resolved scheduler. Its `Prod.snd`-marginalisation (step 2) is the abstract witness `pe_A`. -/
noncomputable def simJointExecR
    (pe_C : ResolvedProbabilisticExecution sys_C)
    (sim : FairStrongProbabilisticSimulation F_C F_A R) :
    ResolvedProbabilisticExecution (simProd sys_C sys_A R) where
  initState := PMF.pure (simProd sys_C sys_A R).init
  scheduler := simJointSchedR pe_C sim

end FairStrongProbabilisticSimulation

end PLTS
