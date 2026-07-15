/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2Extra.Fairness.Construction.DistFairTrace
import Leslie2Extra.Fairness.Simulation.Soundness

/-!
# Halting fairness of the reconstructed scheduler

The reconstructed resolved scheduler `lowerSched F s` (`Construction/DistFair.lean`) satisfies the
**halt clause** of `IsFair F`: it schedules `none` (halts) only from an `F`-fair deadlock. This is
one of the two obligations of `(⟨δ_{sys.init}, lowerSched F s⟩).IsFair F` needed to close the
superset inclusion `fairAchievableTraceDists F.dist ⊆ fairAchievableTraceDists F`.

## Strategy

Suppose the reconstructed scheduler halts at a consistent concrete history `r`
(`lowerNext F s r none ≠ 0`). Then:

* consistency forces `r` reachable (`lowerDenom r ≠ 0`), so `lowerNext r none = lowerArrHalt r /
  lowerDenom r ≠ 0`, hence `lowerArrHalt r ≠ 0` — some chain config `⟨de, r, none⟩` has nonzero
  reach-mass;
* that config is `Coupled` (`last r ∈ (last de).support`) and its pending emission `none` was drawn
  from the *abstract* scheduler `s` (`s.next de none ≠ 0`);
* `de` is a consistent run of the abstract execution `⟨δ_{𝒟f.init}, s⟩` (via
  `lowerMde_eq_probOfR` + `probOfR_ne_zero_imp_consistent`), so the abstract fairness of `s` gives
  `F.dist.FairDeadlock (last de)` — the belief `last de` is a fair deadlock of `𝒟f(sys, F)`;
* every reachable belief is `Resolvable` (`reach_de_resolvable`), and a `Resolvable` fair deadlock
  is
  a *genuine* one (`AllFairDeadlock`, i.e. every state in its support is an `F`-fair deadlock —
  `resolvable_fairDeadlock_imp_allFairDeadlock`, since a `CommonFairLabel` belief admits a fair
  hyperstep, `commonFairLabel_imp_dist_fairEnabled`);
* finally `last r ∈ (last de).support` and `AllFairDeadlock (last de)` give
  `F.FairDeadlock (last r)`.
-/

open Stream'

namespace PLTS

variable {State Label : Type} [Silent Label] {sys : System State Label}

/-! ### From `CommonFairLabel` to a fair hyperstep -/

/-- **A `CommonFairLabel` belief is fair-enabled in `𝒟f(sys, F)`.** If every state of `ν` admits a
fair transition under the *same* label `l`, then `ν` admits an `F.dist`-fair hyperstep.
Construction:
pick (by choice) a fair `μ_ s` for each `s ∈ ν.support`; cluster the pushforward to Diracs,
`ω := (ν.bind μ_).map PMF.pure`, so every successor belief is a Dirac (hence `Resolvable` by
`resolvable_pure`, discharging the clustering restriction). Witness kernel `p := fun s => PMF.pure
(μ_ s)`:
* `hyperStep`: `(p s).support = {μ_ s}` and `sys.step s l (μ_ s)` (`F.step_of_fair`), with
  `ω.bind id = ν.bind μ_ = ν.bind (fun s => (p s).bind id)` (`(M.map PMF.pure).bind id = M`);
* fairness: `∀ s ∈ ν.support, ∀ μ' ∈ (p s).support, F.fair s l μ'` (i.e. `F.fair s l (μ_ s)`), same
  bind identity. -/
theorem commonFairLabel_imp_dist_fairEnabled (F : Fairness sys) (ν : PMF State)
    (h : F.CommonFairLabel ν) : F.dist.FairEnabled ν := by
  classical
  obtain ⟨l, hl⟩ := h
  -- pick a fair transition `μ_ s` from each state `s ∈ ν.support`
  set μ_ : State → PMF State := fun s => if hs : s ∈ ν.support then (hl s hs).choose else PMF.pure s
    with hμ_def
  have hfair_ : ∀ s (hs : s ∈ ν.support), F.fair s l (μ_ s) := by
    intro s hs
    have : μ_ s = (hl s hs).choose := by rw [hμ_def]; exact dif_pos hs
    rw [this]; exact (hl s hs).choose_spec
  -- cluster the pushforward to Diracs
  set ω : PMF (PMF State) := (ν.bind μ_).map PMF.pure with hω_def
  -- key bind identity: `ω.bind id = ν.bind μ_`
  have hbind : ω.bind id = ν.bind μ_ := by
    rw [hω_def, PMF.bind_map]
    exact PMF.bind_pure (ν.bind μ_)
  -- witness kernel
  set p : State → PMF (PMF State) := fun s => PMF.pure (μ_ s) with hp_def
  have hp_bind : (fun s => (p s).bind id) = μ_ := by
    funext s; rw [hp_def]; exact PMF.pure_bind (μ_ s) id
  refine ⟨l, ω, ⟨⟨?_, ?_⟩, p, ?_, ?_⟩⟩
  · -- hyperStep sys ν l (ω.bind id)
    refine ⟨p, ?_, ?_⟩
    · intro s hs μ' hμ'
      rw [hp_def, PMF.mem_support_pure_iff] at hμ'
      subst hμ'
      exact F.step_of_fair s l (μ_ s) (hfair_ s hs)
    · rw [hbind, hp_bind]
  · -- ∀ ν' ∈ ω.support, F.Resolvable ν'
    intro ν' hν'
    rw [hω_def, PMF.mem_support_map_iff] at hν'
    obtain ⟨x, _, rfl⟩ := hν'
    exact F.resolvable_pure x
  · -- ∀ s ∈ ν.support, ∀ μ' ∈ (p s).support, F.fair s l μ'
    intro s hs μ' hμ'
    rw [hp_def, PMF.mem_support_pure_iff] at hμ'
    subst hμ'
    exact hfair_ s hs
  · -- ω.bind id = ν.bind (fun s => (p s).bind id)
    rw [hbind, hp_bind]

/-- **A `Resolvable` fair deadlock is a genuine (all-states) fair deadlock.** `Resolvable ν` is
`CommonFairLabel ν ∨ AllFairDeadlock ν`; the first disjunct is impossible under
`F.dist.FairDeadlock ν` (`commonFairLabel_imp_dist_fairEnabled` would make `ν` fair-enabled), so
`AllFairDeadlock ν` holds. -/
theorem resolvable_fairDeadlock_imp_allFairDeadlock (F : Fairness sys) (ν : PMF State)
    (hres : F.Resolvable ν) (hdead : F.dist.FairDeadlock ν) : F.AllFairDeadlock ν := by
  rcases hres with hcfl | hall
  · exact absurd (commonFairLabel_imp_dist_fairEnabled F ν hcfl) hdead
  · exact hall

/-! ### Every reachable belief is resolvable -/

/-- **Reachable beliefs are `Resolvable`.** The last belief `lastStateOf c.de` of any config with
nonzero reach-mass at any level is `Resolvable`. Induction on the level `n`:

* `n = 0`: the start config has `de = ⟨PMF.pure sys.init, nil⟩`, so `lastStateOf c.de = PMF.pure
  sys.init` (`lastStateOf_nil`), `Resolvable` by `resolvable_pure`;
* `n + 1`: peel a predecessor `c₀` with `LowerStep c₀ c ≠ 0`; then `c₀.h = some (l, ω)`,
  `c.de = c₀.de.append ((l, ω), dq)` with `dq = lastStateOf c.de` and (from the `ω dq` weight
  factor)
  `dq ∈ ω.support`. `reachProb_pending_step` (on the reachable `c₀`) gives
  `(sys.distF F).step (lastStateOf c₀.de) l ω`, whose resolvability clause
  (`∀ ν ∈ ω.support, F.Resolvable ν`) applied to `dq` yields `F.Resolvable dq`. -/
theorem reach_de_resolvable (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (n : ℕ) (c : LowerConfig sys) (hne : LowerReachAfter F s n c ≠ 0) :
    F.Resolvable (lastStateOf c.de) := by
  classical
  induction n generalizing c with
  | zero =>
    rw [LowerReachAfter_zero] at hne
    by_cases hc : c.de = ⟨PMF.pure sys.init, Seq.nil⟩ ∧ c.e = ⟨sys.init, Seq.nil⟩
    · rw [hc.1, lastStateOf_nil]
      exact F.resolvable_pure sys.init
    · rw [if_neg hc] at hne; exact absurd rfl hne
  | succ k ih =>
    rw [LowerReachAfter_succ] at hne
    obtain ⟨c₀, hc₀⟩ := tsum_ne_zero_exists hne
    have hreach₀ : LowerReachAfter F s k c₀ ≠ 0 := fun h => hc₀ (by rw [h, zero_mul])
    have hstep : LowerStep F s c₀ c ≠ 0 := fun h => hc₀ (by rw [h, mul_zero])
    -- `LowerReachProb F s c₀ ≠ 0` from a single nonzero summand.
    have hrp₀ : LowerReachProb F s c₀ ≠ 0 := by
      intro h0
      apply hreach₀
      have hle : LowerReachAfter F s k c₀ ≤ LowerReachProb F s c₀ :=
        ENNReal.le_tsum k
      rw [h0] at hle
      exact le_antisymm hle bot_le
    -- Unfold `LowerStep` to extract `c₀.h = some (l₀, ω₀)`, the append shape, and `ω₀ dq ≠ 0`.
    revert hstep
    unfold LowerStep
    cases hh : c₀.h with
    | none => intro hstep; exact absurd rfl hstep
    | some lω =>
      obtain ⟨l₀, ω₀⟩ := lω
      simp only
      set μ' : PMF State := lastMuOf c.e with hμ'
      by_cases hif : c.de.init = c₀.de.init ∧ c.e.init = c₀.e.init ∧
          c.de.trans = c₀.de.trans.append (Seq.cons ((l₀, ω₀), lastStateOf c.de) Seq.nil) ∧
          c.e.trans = c₀.e.trans.append (Seq.cons ((l₀, μ'), lastStateOf c.e) Seq.nil)
      · rw [if_pos hif]
        intro hweight
        -- nonzero weight ⇒ ω₀ (lastStateOf c.de) ≠ 0, i.e. lastStateOf c.de ∈ ω₀.support
        have hωdq : ω₀ (lastStateOf c.de) ≠ 0 := by
          intro h0
          apply hweight
          simp only [h0, mul_zero, zero_mul]
        have hmem : lastStateOf c.de ∈ ω₀.support := (PMF.mem_support_iff _ _).mpr hωdq
        -- the pending step out of `c₀` is a valid `𝒟f`-step, whose resolvability clause applies.
        have hstepdf : (sys.distF F).step (lastStateOf c₀.de) l₀ ω₀ :=
          (reachProb_pending_step F s c₀ hrp₀ l₀ ω₀ hh).2
        exact hstepdf.2 (lastStateOf c.de) hmem
      · rw [if_neg hif]; intro hstep; exact absurd rfl hstep

/-! ### The halt clause -/

/-- **Halting fairness of `lowerSched`.** If the reconstructed scheduler halts (`none`) at a
consistent terminating history `r`, then `r`'s last state is an `F`-fair deadlock. Given the
abstract
execution `⟨δ_{𝒟f.init}, s⟩` is `F.dist`-fair. Full argument in the module docstring.

Steps: `consistent_imp_probOfR_ne_zero` + `probOfR_eq_lowerMe` + `lowerMe_eq_lowerDenom` give
`lowerDenom r ≠ 0`, so `lowerNext r none = lowerArrHalt r / lowerDenom r`; `hnone` forces
`lowerArrHalt r ≠ 0`, and `tsum_ne_zero_exists` a `de` with `LowerReachProb ⟨de, r, none⟩ ≠ 0`.
`reachAfter_coupled` gives `Coupled ⟨de,r,none⟩` (so `de`/`r` terminate and
`lastStateOf r ∈ (lastStateOf de).support`); `reachAfter_next_ne_zero` gives `s.next de none ≠ 0`.
`lowerMde_eq_probOfR` turns `LowerReachProb ⟨de,r,none⟩ ≠ 0` (a summand of the `de`-marginal) into
`(⟨δ,s⟩).probOfR de ≠ 0`, so `probOfR_ne_zero_imp_consistent` gives `Consistent de`; `h_fair`'s halt
clause then gives `F.dist.FairDeadlock (de.endState _) = F.dist.FairDeadlock (lastStateOf de)`.
`reach_de_resolvable` gives `F.Resolvable (lastStateOf de)`, so
`resolvable_fairDeadlock_imp_allFairDeadlock` gives `F.AllFairDeadlock (lastStateOf de)`; applied to
`lastStateOf r ∈ (lastStateOf de).support` this is `F.FairDeadlock (lastStateOf r) =
F.FairDeadlock (r.endState hr)`. -/
theorem lowerSched_halt_fairDeadlock (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (h_fair : (⟨PMF.pure (sys.distF F).init, s⟩ :
        ResolvedProbabilisticExecution (sys.distF F)).IsFair F.dist)
    (r : ResolvedExec State Label) (hr : r.trans.Terminates)
    (hcons : (⟨PMF.pure sys.init, lowerSched F s⟩ :
        ResolvedProbabilisticExecution sys).Consistent r)
    (hnone : (⟨PMF.pure sys.init, lowerSched F s⟩ :
        ResolvedProbabilisticExecution sys).scheduler.next r none ≠ 0) :
    F.FairDeadlock (r.endState hr) := by
  classical
  set pe : ResolvedProbabilisticExecution sys := ⟨PMF.pure sys.init, lowerSched F s⟩ with hpe
  -- The scheduler's emission at `r` is `lowerNext F s r`.
  have hnone' : lowerNext F s r none ≠ 0 := hnone
  -- Consistency ⇒ positive path mass ⇒ `lowerDenom r ≠ 0`.
  have hprob : pe.probOfR r hr ≠ 0 :=
    FairStrongProbabilisticSimulation.consistent_imp_probOfR_ne_zero pe r hcons hr
  have hdenom : lowerDenom F s r ≠ 0 := by
    have h1 : pe.probOfR r hr = lowerMe F s r := probOfR_eq_lowerMe F s r hr
    rw [lowerMe_eq_lowerDenom F s r] at h1
    rw [h1] at hprob
    exact hprob
  -- `lowerNext r none = lowerArrHalt r / lowerDenom r`, so `hnone'` forces `lowerArrHalt r ≠ 0`.
  have hnext_eq : lowerNext F s r none = lowerArrHalt F s r / lowerDenom F s r := by
    unfold lowerNext
    rw [dif_neg hdenom]
    rfl
  have hhalt : lowerArrHalt F s r ≠ 0 := by
    intro h0
    apply hnone'
    rw [hnext_eq, h0, ENNReal.zero_div]
  -- Extract a `de` with `LowerReachProb ⟨de, r, none⟩ ≠ 0`.
  have hhalt' : (∑' de : ResolvedExec (PMF State) Label,
      LowerReachProb F s ⟨de, r, none⟩) ≠ 0 := hhalt
  obtain ⟨de, hde⟩ := tsum_ne_zero_exists hhalt'
  -- Extract a level `N` witnessing the reach-mass of `⟨de, r, none⟩`.
  have hde' : (∑' N, LowerReachAfter F s N ⟨de, r, none⟩) ≠ 0 := hde
  obtain ⟨N, hN⟩ := tsum_ne_zero_exists hde'
  -- Coupling: `de`/`r` terminate and `lastStateOf r ∈ (lastStateOf de).support`.
  have hcoup : Coupled (⟨de, r, none⟩ : LowerConfig sys) := reachAfter_coupled F s N _ hN
  obtain ⟨hde_term, hr_term, hmem⟩ := hcoup
  -- The pending emission `none` was drawn from the abstract scheduler: `s.next de none ≠ 0`.
  have hs_none : s.next de none ≠ 0 := reachAfter_next_ne_zero F s N _ hN
  -- `de` is a consistent run of `⟨δ_{𝒟f.init}, s⟩`.
  have hde_prob : (⟨PMF.pure (sys.distF F).init, s⟩ :
      ResolvedProbabilisticExecution (sys.distF F)).probOfR de hde_term ≠ 0 := by
    rw [← lowerMde_eq_probOfR F s de hde_term]
    -- `LowerReachProb ⟨de, r, none⟩` is a summand of the `de`-marginal.
    intro h0
    apply hde
    have hle : LowerReachProb F s ⟨de, r, none⟩
        ≤ ∑' (e : ResolvedExec State Label) (h : Option (Label × PMF (PMF State))),
            LowerReachProb F s ⟨de, e, h⟩ := by
      calc LowerReachProb F s ⟨de, r, none⟩
          ≤ ∑' h : Option (Label × PMF (PMF State)), LowerReachProb F s ⟨de, r, h⟩ :=
            ENNReal.le_tsum none
        _ ≤ ∑' (e : ResolvedExec State Label) (h : Option (Label × PMF (PMF State))),
            LowerReachProb F s ⟨de, e, h⟩ := ENNReal.le_tsum r
    rw [h0] at hle
    exact le_antisymm hle bot_le
  have hde_cons : (⟨PMF.pure (sys.distF F).init, s⟩ :
      ResolvedProbabilisticExecution (sys.distF F)).Consistent de :=
    FairStrongProbabilisticSimulation.probOfR_ne_zero_imp_consistent _ de hde_term hde_prob
  -- Abstract halt clause: `lastStateOf de` is an `F.dist`-fair deadlock.
  have hde_dead : F.dist.FairDeadlock (de.endState hde_term) :=
    h_fair.halt_fairDeadlock de hde_term hde_cons hs_none
  have hlast_de : de.endState hde_term = lastStateOf de := by
    unfold lastStateOf; rw [dif_pos hde_term]
  rw [hlast_de] at hde_dead
  -- `lastStateOf de` is resolvable, so a genuine fair deadlock.
  have hde_res : F.Resolvable (lastStateOf de) := reach_de_resolvable F s N _ hN
  have hde_all : F.AllFairDeadlock (lastStateOf de) :=
    resolvable_fairDeadlock_imp_allFairDeadlock F (lastStateOf de) hde_res hde_dead
  -- `lastStateOf r ∈ (lastStateOf de).support` ⇒ `F.FairDeadlock (lastStateOf r)`.
  have hr_dead : F.FairDeadlock (lastStateOf r) := hde_all (lastStateOf r) hmem
  have hlast_r : r.endState hr = lastStateOf r := by
    unfold lastStateOf; rw [dif_pos hr]
  rw [hlast_r]
  exact hr_dead

/-! ### The infinite-fairness clause

`inf_fair` for `⟨δ_{sys.init}, lowerSched F s⟩`: every infinite consistent concrete run `r` takes
infinitely many `F`-fair steps. Unlike the halt clause this needs a **finite-branching hypothesis on
the abstract scheduler `s`** (`SchedFinBranch`): `s` emits finitely many transitions at each
history,
each with finitely-supported next-belief distribution. (Note: `(sys.distF F).ImageFinite` would NOT
suffice/be natural — `𝒟f`'s step relation is not image-finite because of clustering freedom; the
finiteness must be imposed on the scheduler, which only emits finitely many specific `ω`'s.)

**Strategy.** König-lift the infinite concrete run `r` to an infinite abstract run `de` coupled with
it at every prefix (`exists_infinite_coupled_de`, mirroring `exists_infinite_coupled_lift` in
`Simulation/Fair/Soundness.lean`). Then `de` is consistent with `⟨δ_{𝒟f.init}, s⟩` and infinite, so
the *given* abstract fairness `h_fair.inf_fair de` supplies infinitely many `F.dist`-fair abstract
steps; each transfers to an `F`-fair concrete step by `tKernel_fair` (the sampled `μₙ` lies in the
kernel of the fair emission, and `qₚₙ ∈ βₙ.support` by `Coupled`). No rank/descent is needed here
(the abstract scheduler is given fair, not constructed). -/

/-- **Finite-branching hypothesis on the abstract `𝒟f`-scheduler.** At every history `de`, `s` emits
finitely many transitions with positive probability, and each emitted next-belief distribution `ω`
has finite support. This is the finite-branching condition König needs on the shadowing tree. -/
def SchedFinBranch (F : Fairness sys) (s : ResolvedScheduler (sys.distF F)) : Prop :=
  ∀ de : ResolvedExec (PMF State) Label,
    (s.next de).support.Finite ∧
      ∀ l (ω : PMF (PMF State)), some (l, ω) ∈ (s.next de).support → ω.support.Finite

/-! ### Finite-prefix (`take`) API

Re-proved copies (from `Simulation/Fair/Soundness.lean`, where they are `private`) of the generic
`AlterSeq.take` facts the König lift needs to read recorded transitions, end-states, and consistency
at each finite prefix. -/

/-- `Seq.take n s` reads back `s.get?` below `n`. -/
private theorem seq_getElem?_take {α : Type} (t : Seq α) (n m : ℕ) (h : m < n) :
    (Seq.take n t)[m]? = t.get? m := by
  induction n generalizing t m with
  | zero => omega
  | succ k ih =>
    induction t using Stream'.Seq.recOn with
    | nil => simp [Stream'.Seq.take_nil, Stream'.Seq.get?_nil]
    | cons a t =>
      rw [Stream'.Seq.take_succ_cons]
      cases m with
      | zero => simp [Stream'.Seq.get?_cons_zero]
      | succ j =>
        rw [List.getElem?_cons_succ, Stream'.Seq.get?_cons_succ]
        exact ih t j (Nat.lt_of_succ_lt_succ h)

omit [Silent Label] in
/-- The finite prefix `r.take n` records the same transitions as `r` below `n`. -/
private theorem take_trans_get? {S : Type} (r : ResolvedExec S Label) {n m : ℕ} (h : m < n) :
    (r.take n).trans.get? m = r.trans.get? m := by
  change (Seq.ofList (Seq.take n r.trans)).get? m = _
  rw [Stream'.Seq.ofList_get?, seq_getElem?_take r.trans n m h]

omit [Silent Label] in
/-- The length-`n` prefix always terminates (it is a finite list). -/
private theorem take_terminates {S : Type} (r : ResolvedExec S Label) (n : ℕ) :
    (r.take n).trans.Terminates :=
  Stream'.Seq.terminates_ofList _

omit [Silent Label] in
/-- For an infinite `r`, the length-`n` prefix terminates exactly at `n`. -/
private theorem take_terminatedAt {S : Type} (r : ResolvedExec S Label) (n : ℕ)
    (hinf : ¬ r.trans.Terminates) : (r.take n).trans.TerminatedAt n := by
  change (Seq.ofList (Seq.take n r.trans)).get? n = none
  rw [Stream'.Seq.ofList_get?]
  apply List.getElem?_eq_none
  have hlen : (Seq.take n r.trans).length = n :=
    Stream'.Seq.length_take_of_le_length (fun h => absurd h hinf)
  omega

omit [Silent Label] in
/-- If `r` terminates at `L` and `L ≤ m`, then `r.take m = r.take L` (extra prefix is empty). -/
private theorem take_eq_of_terminatedAt {S : Type} (r : ResolvedExec S Label) {L m : ℕ}
    (hL : r.trans.TerminatedAt L) (hLm : L ≤ m) : r.take m = r.take L := by
  unfold AlterSeq.take
  simp only [AlterSeq.mk.injEq, true_and]
  congr 1
  apply List.ext_getElem?
  intro j
  rw [Stream'.Seq.getElem?_take, Stream'.Seq.getElem?_take]
  by_cases hj : j < L
  · rw [if_pos hj, if_pos (Nat.lt_of_lt_of_le hj hLm)]
  · rw [if_neg hj]
    have hLj : L ≤ j := Nat.le_of_not_lt hj
    have hnone : r.trans.get? j = none := Stream'.Seq.le_stable r.trans hLj hL
    by_cases hjm : j < m
    · rw [if_pos hjm, hnone]
    · rw [if_neg hjm]

omit [Silent Label] in
/-- For an infinite `r`, the length-`m` prefix terminates *minimally* at `m`. -/
private theorem take_terminatedAt_min {S : Type} (r : ResolvedExec S Label) (m : ℕ)
    (hinf : ¬ r.trans.Terminates) : ∀ k < m, ¬ (r.take m).trans.TerminatedAt k := by
  intro k hk ht
  have : (r.take m).trans.get? k = r.trans.get? k := take_trans_get? r hk
  rw [ht] at this
  exact hinf ⟨k, this.symm⟩

omit [Silent Label] in
/-- The length-`n` prefix always terminates at `n` (the list has length `≤ n`). -/
private theorem take_terminatedAt_self {S : Type} (r : ResolvedExec S Label) (n : ℕ) :
    (r.take n).trans.TerminatedAt n := by
  change (Seq.ofList (Seq.take n r.trans)).get? n = none
  rw [Stream'.Seq.ofList_get?]
  exact List.getElem?_eq_none (Nat.le_trans Stream'.Seq.length_take_le (Nat.le_refl n))

omit [Silent Label] in
/-- For an infinite `r`, the canonical terminating index of `r.take n` is `n`. -/
private theorem take_find {S : Type} (r : ResolvedExec S Label) (n : ℕ)
    (hinf : ¬ r.trans.Terminates) : Nat.find (take_terminates r n) = n := by
  apply le_antisymm
  · exact Nat.find_le (take_terminatedAt r n hinf)
  · rw [Nat.le_find_iff]
    intro m hm
    change ¬ (Seq.ofList (Seq.take n r.trans)).get? m = none
    rw [Stream'.Seq.ofList_get?, seq_getElem?_take r.trans n m hm]
    exact fun hc => hinf ⟨m, hc⟩

omit [Silent Label] in
/-- `r.take n` reads the same state as `r` at positions `≤ n`. -/
private theorem take_stateAt {S : Type} (r : ResolvedExec S Label) {n m : ℕ} (hm : m ≤ n) :
    (r.take n).stateAt m = r.stateAt m := by
  cases m with
  | zero => rfl
  | succ k =>
    change ((r.take n).trans.get? k).map Prod.snd = (r.trans.get? k).map Prod.snd
    rw [take_trans_get? r (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hm)]

omit [Silent Label] in
/-- For an infinite `r`, the end-state of the length-`n` prefix is `r.stateAt n`. -/
private theorem take_endState {S : Type} (r : ResolvedExec S Label) (n : ℕ)
    (hinf : ¬ r.trans.Terminates) {s : S} (hs : r.stateAt n = some s) :
    (r.take n).endState (take_terminates r n) = s := by
  have hfind := take_find r n hinf
  have heq := AlterSeq.stateAt_find_eq_endState (r.take n) (take_terminates r n)
  rw [hfind, take_stateAt r (Nat.le_refl n), hs] at heq
  exact (Option.some.inj heq).symm

omit [Silent Label] in
/-- For infinite `r` with `r.stateAt n = some s`, `lastStateOf (r.take n) = s`. -/
private theorem lastStateOf_take {S : Type} (r : ResolvedExec S Label) (n : ℕ)
    (hinf : ¬ r.trans.Terminates) {s : S} (hs : r.stateAt n = some s) :
    lastStateOf (r.take n) = s := by
  unfold lastStateOf
  rw [dif_pos (take_terminates r n)]
  exact take_endState r n hinf hs

omit [Silent Label] in
/-- Nested prefixes collapse: for `m ≤ n`, `(r.take n).take m = r.take m`. -/
private theorem take_take {S : Type} (r : ResolvedExec S Label) (n m : ℕ) (hmn : m ≤ n) :
    (r.take n).take m = r.take m := by
  unfold AlterSeq.take
  simp only [AlterSeq.mk.injEq, true_and]
  congr 1
  apply List.ext_getElem?
  intro j
  rw [Stream'.Seq.getElem?_take, Stream'.Seq.getElem?_take]
  by_cases hj : j < m
  · rw [if_pos hj, if_pos hj, Stream'.Seq.ofList_get?, seq_getElem?_take r.trans n j
      (Nat.lt_of_lt_of_le hj hmn)]
  · rw [if_neg hj, if_neg hj]

omit [Silent Label] in
/-- A history terminated at `n` equals its own length-`n` prefix. -/
private theorem take_self_of_terminatedAt {S : Type} (r : ResolvedExec S Label) (n : ℕ)
    (hT : r.trans.TerminatedAt n) : r.take n = r := by
  obtain ⟨i, t⟩ := r
  apply AlterSeq.mk.injEq .. |>.mpr
  refine ⟨rfl, ?_⟩
  apply Stream'.Seq.ext
  intro m
  by_cases hm : m < n
  · change (Seq.ofList (Seq.take n t)).get? m = _
    rw [Stream'.Seq.ofList_get?, seq_getElem?_take t n m hm]
  · have hmn : n ≤ m := Nat.le_of_not_lt hm
    have e1 : (Seq.ofList (Seq.take n t)).get? m = none := by
      rw [Stream'.Seq.ofList_get?]
      apply List.getElem?_eq_none
      exact Nat.le_trans (Stream'.Seq.length_take_le) hmn
    change (Seq.ofList (Seq.take n t)).get? m = t.get? m
    rw [e1, Stream'.Seq.le_stable t hmn hT]

omit [Silent Label] in
/-- **Consistency restricts to prefixes.** If `r` is `pe`-consistent, so is every finite prefix
`r.take n`. -/
private theorem consistent_take {S : Type} {sys : System S Label}
    (pe : ResolvedProbabilisticExecution sys) (r : ResolvedExec S Label)
    (hcons : pe.Consistent r) (n : ℕ) : pe.Consistent (r.take n) := by
  refine ⟨hcons.1, ?_⟩
  intro m l μ s' hget
  have hmn : m < n := by
    by_contra hc
    have : (r.take n).trans.get? m = none := by
      change (Seq.ofList (Seq.take n r.trans)).get? m = none
      rw [Stream'.Seq.ofList_get?]
      apply List.getElem?_eq_none
      exact Nat.le_trans (Stream'.Seq.length_take_le) (Nat.le_of_not_lt hc)
    rw [this] at hget; exact absurd hget (by simp)
  rw [take_trans_get? r hmn] at hget
  obtain ⟨hnext, hμ⟩ := hcons.2 m l μ s' hget
  refine ⟨?_, hμ⟩
  have htk : (r.take n).take m = r.take m := take_take r n m (Nat.le_of_lt hmn)
  rw [htk]; exact hnext

omit [Silent Label] in
/-- **Prefix of an append.** If `a` is `b` extended by one transition (`a.trans =
b.trans.append (cons X nil)`, same init) and `b` terminates *minimally* at `k`, then `a.take k = b`.
-/
private theorem take_of_append_singleton {S : Type} (a b : ResolvedExec S Label) (k : ℕ)
    (X : (Label × PMF S) × S) (hi : a.init = b.init)
    (happ : a.trans = b.trans.append (Seq.cons X Seq.nil))
    (hT : b.trans.TerminatedAt k) (hmin : ∀ j < k, ¬ b.trans.TerminatedAt j) :
    a.take k = b := by
  -- `b = b.take k`, and `a.take k = b.take k` (agree below `k`).
  rw [← take_self_of_terminatedAt b k hT]
  unfold AlterSeq.take
  simp only [AlterSeq.mk.injEq]
  refine ⟨hi, ?_⟩
  congr 1
  apply List.ext_getElem?
  intro j
  rw [Stream'.Seq.getElem?_take, Stream'.Seq.getElem?_take]
  by_cases hj : j < k
  · rw [if_pos hj, if_pos hj, happ]
    exact Stream'.Seq.get?_append_before_length (hmin j hj)
  · rw [if_neg hj, if_neg hj]

/-- **Termination transfer along label-sync.** If `c` is reachable at level `n`, then `c.de.trans`
terminates minimally at `n` (same as `c.e.trans`, via `reachAfter_labels_eq`). -/
private theorem reachAfter_de_length (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (n : ℕ) (c : LowerConfig sys) (hne : LowerReachAfter F s n c ≠ 0) :
    c.de.trans.TerminatedAt n ∧ ∀ k < n, ¬ c.de.trans.TerminatedAt k := by
  classical
  obtain ⟨hterm, hmin⟩ := reachAfter_length F s n c hne
  have hlab : c.e.trans.map (fun p => p.1.1) = c.de.trans.map (fun p => p.1.1) :=
    reachAfter_labels_eq F s n c hne
  -- `TerminatedAt` is preserved by `map`, so transfers across `hlab`.
  have hiff : ∀ k, c.de.trans.TerminatedAt k ↔ c.e.trans.TerminatedAt k := by
    intro k
    constructor
    · intro ht
      have h1 : (c.de.trans.map (fun p => p.1.1)).get? k = none := by
        rw [Stream'.Seq.map_get?, ht]; rfl
      rw [← hlab, Stream'.Seq.map_get?] at h1
      rcases hc : c.e.trans.get? k with _ | v
      · exact hc
      · rw [hc] at h1; simp at h1
    · intro ht
      have h1 : (c.e.trans.map (fun p => p.1.1)).get? k = none := by
        rw [Stream'.Seq.map_get?, ht]; rfl
      rw [hlab, Stream'.Seq.map_get?] at h1
      rcases hc : c.de.trans.get? k with _ | v
      · exact hc
      · rw [hc] at h1; simp at h1
  exact ⟨(hiff n).mpr hterm, fun k hk ht => hmin k hk ((hiff k).mp ht)⟩

/-- **Init of a reachable abstract run.** Every reachable config's abstract run starts at
`PMF.pure sys.init` (the chain's initial belief). -/
private theorem reachAfter_de_init (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (n : ℕ) (c : LowerConfig sys) (hne : LowerReachAfter F s n c ≠ 0) :
    c.de.init = PMF.pure sys.init := by
  classical
  induction n generalizing c with
  | zero =>
    rw [LowerReachAfter_zero] at hne
    by_cases hc : c.de = ⟨PMF.pure sys.init, Seq.nil⟩ ∧ c.e = ⟨sys.init, Seq.nil⟩
    · rw [hc.1]
    · rw [if_neg hc] at hne; exact absurd rfl hne
  | succ k ih =>
    rw [LowerReachAfter_succ] at hne
    obtain ⟨c₀, hc₀⟩ := tsum_ne_zero_exists hne
    have hreach₀ : LowerReachAfter F s k c₀ ≠ 0 := fun h => hc₀ (by rw [h, zero_mul])
    have hstep : LowerStep F s c₀ c ≠ 0 := fun h => hc₀ (by rw [h, mul_zero])
    have hinit₀ : c₀.de.init = PMF.pure sys.init := ih c₀ hreach₀
    -- `LowerStep c₀ c ≠ 0` forces `c.de.init = c₀.de.init`.
    revert hstep
    unfold LowerStep
    cases hh : c₀.h with
    | none => intro hstep; exact absurd rfl hstep
    | some lω =>
      obtain ⟨l₀, ω₀⟩ := lω
      simp only
      set μ' : PMF State := lastMuOf c.e with hμ'
      by_cases hif : c.de.init = c₀.de.init ∧ c.e.init = c₀.e.init ∧
          c.de.trans = c₀.de.trans.append (Seq.cons ((l₀, ω₀), lastStateOf c.de) Seq.nil) ∧
          c.e.trans = c₀.e.trans.append (Seq.cons ((l₀, μ'), lastStateOf c.e) Seq.nil)
      · rw [if_pos hif]; intro _; rw [hif.1, hinit₀]
      · rw [if_neg hif]; intro hstep; exact absurd rfl hstep

/-- **A reachable abstract run is consistent** with the abstract execution `⟨δ_{𝒟f.init}, s⟩`.
From `LowerReachProb ⟨D, e, h⟩ ≠ 0`, the `de`-marginal `∑' e h, LowerReachProb ⟨D,e,h⟩ =
probOfR D ≠ 0` (`lowerMde_eq_probOfR`), hence `Consistent D`
(`probOfR_ne_zero_imp_consistent`). -/
private theorem reachProb_de_consistent (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (D : ResolvedExec (PMF State) Label) (e : ResolvedExec State Label)
    (h : Option (Label × PMF (PMF State))) (hDterm : D.trans.Terminates)
    (hne : LowerReachProb F s ⟨D, e, h⟩ ≠ 0) :
    (⟨PMF.pure (sys.distF F).init, s⟩ :
        ResolvedProbabilisticExecution (sys.distF F)).Consistent D := by
  classical
  have hprob : (⟨PMF.pure (sys.distF F).init, s⟩ :
      ResolvedProbabilisticExecution (sys.distF F)).probOfR D hDterm ≠ 0 := by
    rw [← lowerMde_eq_probOfR F s D hDterm]
    intro h0
    apply hne
    have hle : LowerReachProb F s ⟨D, e, h⟩
        ≤ ∑' (e : ResolvedExec State Label) (h : Option (Label × PMF (PMF State))),
            LowerReachProb F s ⟨D, e, h⟩ := by
      calc LowerReachProb F s ⟨D, e, h⟩
          ≤ ∑' h : Option (Label × PMF (PMF State)), LowerReachProb F s ⟨D, e, h⟩ :=
            ENNReal.le_tsum h
        _ ≤ ∑' (e : ResolvedExec State Label) (h : Option (Label × PMF (PMF State))),
            LowerReachProb F s ⟨D, e, h⟩ := ENNReal.le_tsum e
    rw [h0] at hle
    exact le_antisymm hle bot_le
  exact FairStrongProbabilisticSimulation.probOfR_ne_zero_imp_consistent _ D hDterm hprob

/-- **One-step chain peel.** If `c` is reachable at level `k+1`, there is a level-`k`-reachable
predecessor whose `de`/`e` are exactly `c`'s length-`k` prefixes. -/
private theorem reachAfter_peel (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (k : ℕ) (c : LowerConfig sys) (hne : LowerReachAfter F s (k + 1) c ≠ 0) :
    ∃ c₀ : LowerConfig sys, LowerReachAfter F s k c₀ ≠ 0 ∧
      c₀.de = c.de.take k ∧ c₀.e = c.e.take k := by
  classical
  rw [LowerReachAfter_succ] at hne
  obtain ⟨c₀, hc₀⟩ := tsum_ne_zero_exists hne
  have hreach₀ : LowerReachAfter F s k c₀ ≠ 0 := fun h => hc₀ (by rw [h, zero_mul])
  have hstep : LowerStep F s c₀ c ≠ 0 := fun h => hc₀ (by rw [h, mul_zero])
  -- `c₀.e` / `c₀.de` terminate minimally at `k`.
  obtain ⟨hEterm₀, hEmin₀⟩ := reachAfter_length F s k c₀ hreach₀
  obtain ⟨hDterm₀, hDmin₀⟩ := reachAfter_de_length F s k c₀ hreach₀
  -- Extract the append shape from `LowerStep c₀ c ≠ 0`.
  revert hstep
  unfold LowerStep
  cases hh : c₀.h with
  | none => intro hstep; exact absurd rfl hstep
  | some lω =>
    obtain ⟨l₀, ω₀⟩ := lω
    simp only
    set μ' : PMF State := lastMuOf c.e with hμ'
    by_cases hif : c.de.init = c₀.de.init ∧ c.e.init = c₀.e.init ∧
        c.de.trans = c₀.de.trans.append (Seq.cons ((l₀, ω₀), lastStateOf c.de) Seq.nil) ∧
        c.e.trans = c₀.e.trans.append (Seq.cons ((l₀, μ'), lastStateOf c.e) Seq.nil)
    · rw [if_pos hif]
      intro _
      obtain ⟨hdeinit, heinit, hdetrans, hetrans⟩ := hif
      refine ⟨c₀, hreach₀, ?_, ?_⟩
      · exact (take_of_append_singleton c.de c₀.de k _ hdeinit hdetrans hDterm₀ hDmin₀).symm
      · exact (take_of_append_singleton c.e c₀.e k _ heinit hetrans hEterm₀ hEmin₀).symm
    · rw [if_neg hif]; intro hstep; exact absurd rfl hstep

omit [Silent Label] in
/-- Two histories agreeing below `n`, both terminated at `n`, are equal. -/
private theorem resolvedExec_eq_of_take_get?
    {S : Type} (w₁ w₂ : ResolvedExec S Label) (n : ℕ)
    (hi : w₁.init = w₂.init)
    (hle : w₁.take n = w₂.take n)
    (hn : w₁.trans.get? n = w₂.trans.get? n)
    (hT₁ : w₁.trans.TerminatedAt (n + 1)) (hT₂ : w₂.trans.TerminatedAt (n + 1)) :
    w₁ = w₂ := by
  obtain ⟨i₁, t₁⟩ := w₁
  obtain ⟨i₂, t₂⟩ := w₂
  simp only at hi; subst hi
  congr 1
  apply Stream'.Seq.ext
  intro m
  rcases lt_trichotomy m n with hm | hm | hm
  · have := congrArg (fun (e : ResolvedExec S Label) => e.trans.get? m) hle
    simpa only [take_trans_get? _ hm] using this
  · subst hm; exact hn
  · have e1 : t₁.get? m = none :=
      Stream'.Seq.le_stable _ (Nat.succ_le_of_lt hm) hT₁
    have e2 : t₂.get? m = none :=
      Stream'.Seq.le_stable _ (Nat.succ_le_of_lt hm) hT₂
    rw [e1, e2]

/-- **Finite branching set.** Under `SchedFinBranch`, the emissions-with-outcome
`{((l,ω), dq) | some (l,ω) ∈ (s.next de).support ∧ dq ∈ ω.support}` at any history `de` form a
finite
set — a `Set.Finite.biUnion` over the (finite) emission set, each fibre `ω.support` finite. This is
the finiteness target the König children inject into (via a child's last recorded transition).
Mirror `positive_histories_finite`/`hFinTarget` in `Simulation/Fair/Soundness.lean`. -/
theorem step_emissions_finite (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (hbr : SchedFinBranch F s) (de : ResolvedExec (PMF State) Label) :
    {p : (Label × PMF (PMF State)) × PMF State |
      some p.1 ∈ (s.next de).support ∧ p.2 ∈ p.1.2.support}.Finite := by
  classical
  obtain ⟨hnextFin, hωFin⟩ := hbr de
  -- The set of emissions `lω = (l, ω)` with `some lω ∈ (s.next de).support` is finite: it is the
  -- image of `(s.next de).support` under `Option.get`/preimage of `some`.
  have hemitFin : {lω : Label × PMF (PMF State) | some lω ∈ (s.next de).support}.Finite := by
    apply Set.Finite.of_finite_image (f := (fun lω => (some lω : Option (Label × PMF (PMF State)))))
    · apply Set.Finite.subset hnextFin
      rintro _ ⟨lω, hlω, rfl⟩
      exact hlω
    · exact fun _ _ _ _ h => Option.some.inj h
  -- `biUnion` over the finite emission set, each fibre `ω.support` finite.
  apply Set.Finite.subset
    (Set.Finite.biUnion hemitFin
      (fun lω hlω => (hωFin lω.1 lω.2 hlω).image (fun dq => (lω, dq))))
  rintro ⟨⟨l, ω⟩, dq⟩ ⟨hemit, hdq⟩
  exact Set.mem_biUnion hemit ⟨dq, hdq, rfl⟩

/-- **Arbitrary-length coupled prefix.** For a consistent concrete run `r` and any `n`, there is a
length-`n` abstract run `De` all of whose prefixes shadow the corresponding prefixes of `r` — i.e.
`⟨De.take i, r.take i, ·⟩` is chain-reachable for every `i ≤ n`. Supplies the finite chains for
König.

Construction: `r` consistent ⇒ `r.take n` consistent (restrict) ⇒ `probOfR (r.take n) ≠ 0`
(`consistent_imp_probOfR_ne_zero`) `= lowerMe (r.take n)` (`probOfR_eq_lowerMe`) `≠ 0`, so some
`⟨De, r.take n, H⟩` is reachable (`lowerMe` def + `tsum_ne_zero_exists`); `reachAfter_length` pins
its
level to `n` and forces `De.trans.TerminatedAt n`. Prefix-shadowing (`∀ i ≤ n`) is the chain
analogue
of `probOfR_take_ne_zero`: a reachable level-`(k+1)` config's tsum-predecessor is exactly its
level-`k` prefix config (both `de` and `e` lose their last transition), so shadowing propagates down
by induction; `reachAfter_labels_eq` gives `De.take i`'s `e`-part `= r.take i`. -/
theorem exists_shadowing_prefix (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (r : ResolvedExec State Label)
    (hcons : (⟨PMF.pure sys.init, lowerSched F s⟩ :
        ResolvedProbabilisticExecution sys).Consistent r) (n : ℕ) :
    ∃ De : ResolvedExec (PMF State) Label,
      De.init = PMF.pure sys.init ∧ De.trans.TerminatedAt n ∧
      ∀ i, i ≤ n → ∃ H, LowerReachProb F s ⟨De.take i, r.take i, H⟩ ≠ 0 := by
  classical
  -- `r.take n` is consistent, so has positive path mass = `lowerMe (r.take n)`.
  have hTn : (r.take n).trans.Terminates := take_terminates r n
  have hcons_n : (⟨PMF.pure sys.init, lowerSched F s⟩ :
      ResolvedProbabilisticExecution sys).Consistent (r.take n) := consistent_take _ r hcons n
  have hprob : (⟨PMF.pure sys.init, lowerSched F s⟩ :
      ResolvedProbabilisticExecution sys).probOfR (r.take n) hTn ≠ 0 :=
    FairStrongProbabilisticSimulation.consistent_imp_probOfR_ne_zero _ (r.take n) hcons_n hTn
  rw [probOfR_eq_lowerMe F s (r.take n) hTn] at hprob
  -- Extract `De` and `H` with `LowerReachProb ⟨De, r.take n, H⟩ ≠ 0`.
  unfold lowerMe at hprob
  obtain ⟨De, hDe⟩ := tsum_ne_zero_exists hprob
  obtain ⟨H, hH⟩ := tsum_ne_zero_exists hDe
  -- Extract the reach level `L`.
  have hH' : (∑' N, LowerReachAfter F s N ⟨De, r.take n, H⟩) ≠ 0 := hH
  obtain ⟨L, hL⟩ := tsum_ne_zero_exists hH'
  -- `r.take n` (hence `De`) terminates minimally at `L`.
  obtain ⟨hEterm, hEmin⟩ := reachAfter_length F s L ⟨De, r.take n, H⟩ hL
  obtain ⟨hDterm, _⟩ := reachAfter_de_length F s L ⟨De, r.take n, H⟩ hL
  -- `L ≤ n` (the prefix `r.take n` has length `≤ n`).
  have hLn : L ≤ n := by
    by_contra hc
    push Not at hc
    exact hEmin n hc (take_terminatedAt_self r n)
  refine ⟨De, ?_, ?_, ?_⟩
  · -- `De.init = PMF.pure sys.init`.
    exact reachAfter_de_init F s L ⟨De, r.take n, H⟩ hL
  · -- `De.trans.TerminatedAt n`.
    exact Stream'.Seq.terminated_stable De.trans hLn hDterm
  · -- Prefix shadowing: peel from level `L` down to level `i`.
    -- Step 1: `∀ i ≤ L`, a reachable level-`i` config is `⟨De.take i, (r.take n).take i, ·⟩`.
    have hpeel : ∀ d, d ≤ L → ∃ c' : LowerConfig sys,
        LowerReachAfter F s (L - d) c' ≠ 0 ∧
          c'.de = De.take (L - d) ∧ c'.e = (r.take n).take (L - d) := by
      intro d
      induction d with
      | zero =>
        intro _
        refine ⟨⟨De, r.take n, H⟩, by rwa [Nat.sub_zero], ?_, ?_⟩
        · rw [Nat.sub_zero]; exact (take_self_of_terminatedAt De L hDterm).symm
        · rw [Nat.sub_zero]; exact (take_self_of_terminatedAt (r.take n) L hEterm).symm
      | succ d ih =>
        intro hd
        obtain ⟨c', hc'reach, hc'de, hc'e⟩ := ih (Nat.le_of_succ_le hd)
        -- `L - d = (L - (d+1)) + 1`.
        have hstep_eq : L - d = (L - (d + 1)) + 1 := by omega
        rw [hstep_eq] at hc'reach hc'de hc'e
        obtain ⟨c₀, hc₀reach, hc₀de, hc₀e⟩ := reachAfter_peel F s (L - (d + 1)) c' hc'reach
        refine ⟨c₀, hc₀reach, ?_, ?_⟩
        · rw [hc₀de, hc'de, take_take De ((L - (d + 1)) + 1) (L - (d + 1)) (Nat.le_succ _)]
        · rw [hc₀e, hc'e,
            take_take (r.take n) ((L - (d + 1)) + 1) (L - (d + 1)) (Nat.le_succ _)]
    -- Key: for `i` between `L` and `n`, `r.take i = r.take L` and `De.take i = De`.
    -- (`r.trans` actually terminates at `L` whenever `L < n`.)
    intro i hi
    by_cases hiL : i ≤ L
    · -- Peel to level `i` (take `d := L - i`).
      obtain ⟨c', hc'reach, hc'de, hc'e⟩ := hpeel (L - i) (Nat.sub_le L i)
      rw [show L - (L - i) = i from by omega] at hc'reach hc'de hc'e
      refine ⟨c'.h, ?_⟩
      have hle : LowerReachAfter F s i c' ≤ LowerReachProb F s c' := ENNReal.le_tsum i
      have hne' : LowerReachProb F s c' ≠ 0 := fun h => hc'reach (le_antisymm (h ▸ hle) bot_le)
      have hceq : c' = ⟨De.take i, r.take i, c'.h⟩ := by
        obtain ⟨cde, ce, ch⟩ := c'
        simp only at hc'de hc'e ⊢
        rw [hc'de, hc'e, take_take r n i (Nat.le_trans hiL hLn)]
      rwa [hceq] at hne'
    · -- `L < i ≤ n`: then `L < n`, so `r.trans.TerminatedAt L`; `De`/`r.take i` collapse.
      push Not at hiL
      have hLltn : L < n := Nat.lt_of_lt_of_le hiL hi
      have hrL : r.trans.TerminatedAt L := by
        have := hEterm
        rw [show (⟨De, r.take n, H⟩ : LowerConfig sys).e = r.take n from rfl] at this
        change (r.take n).trans.get? L = none at this
        rwa [take_trans_get? r hLltn] at this
      -- `De.take i = De`.
      have hDei : De.take i = De :=
        take_self_of_terminatedAt De i
          (Stream'.Seq.terminated_stable De.trans (Nat.le_of_lt hiL) hDterm)
      -- `r.take i = r.take n` (both collapse to `r.take L`).
      have hri : r.take i = r.take n := by
        rw [take_eq_of_terminatedAt r hrL (Nat.le_of_lt hiL),
          take_eq_of_terminatedAt r hrL (Nat.le_of_lt hLltn)]
      refine ⟨H, ?_⟩
      rw [hDei, hri]; exact hH

/-- **König lift.** An infinite consistent concrete run `r` lifts to an infinite abstract run `de`
that is consistent with `⟨δ_{𝒟f.init}, s⟩` and shadows `r` at every prefix. The single point where
`SchedFinBranch` is used. **Mirror `exists_infinite_coupled_lift` (`Simulation/Fair/Soundness.lean`,
König tree + reconstruction).**

* Nodes = abstract runs `de` (level `n` = length `n`, shadowing `r.take n`); `succ n de de'` :
  `de'.take n = de ∧ de'.trans.TerminatedAt (n+1) ∧ ∃ h, LowerReachProb ⟨de', r.take (n+1), h⟩ ≠ 0`;
  `root = ⟨PMF.pure sys.init, Seq.nil⟩`.
* Finite branching: a child `de'` is `de` extended by its last transition `de'.trans.get? n`;
  reachability of `⟨de', r.take (n+1), _⟩` ⇒ `de'` consistent with `⟨δ, s⟩`
  (`lowerMde_eq_probOfR` + `probOfR_ne_zero_imp_consistent`) ⇒ its last transition `((l,ω),dq)` has
  `some (l,ω) ∈ (s.next de).support` and `dq ∈ ω.support`; so `de' ↦ de'.trans.get? n` injects the
  children into `step_emissions_finite F s hbr de` — finite.
* Chains of every length: `exists_shadowing_prefix` with `f i := De.take i` (`take_take`,
  `reachAfter_length` for the terminated-at level).
* König (`exists_infinite_chain`, `Model/System.lean`) gives an infinite path `f`; reconstruct
  `de.trans.get? n := (f (n+1)).trans.get? n` (as in the template), yielding `de.take n = f n`,
  `¬ de.trans.Terminates`, each prefix shadowing, and (per-prefix consistency ⇒) `Consistent de`. -/
theorem exists_infinite_coupled_de (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (hbr : SchedFinBranch F s) (r : ResolvedExec State Label) (hinf : ¬ r.trans.Terminates)
    (hcons : (⟨PMF.pure sys.init, lowerSched F s⟩ :
        ResolvedProbabilisticExecution sys).Consistent r) :
    ∃ de : ResolvedExec (PMF State) Label,
      ¬ de.trans.Terminates ∧
      (⟨PMF.pure (sys.distF F).init, s⟩ :
          ResolvedProbabilisticExecution (sys.distF F)).Consistent de ∧
      ∀ n, ∃ H, LowerReachProb F s ⟨de.take n, r.take n, H⟩ ≠ 0 := by
  classical
  -- The König tree.  Nodes = abstract runs `de`.  Level-`n` node: length-`n` (terminated at `n`),
  -- shadowing `r.take n`.  `succ n de de'` extends `de` by one step to a level-`n+1` node.
  set root : ResolvedExec (PMF State) Label := ⟨PMF.pure sys.init, Seq.nil⟩ with hroot
  set succ : ℕ → ResolvedExec (PMF State) Label → ResolvedExec (PMF State) Label → Prop :=
    fun n de de' =>
      de'.take n = de ∧ de'.trans.TerminatedAt (n + 1) ∧
        ∃ h : Option (Label × PMF (PMF State)),
          LowerReachProb F s ⟨de', r.take (n + 1), h⟩ ≠ 0
    with hsucc
  -- **(A) König chains of every length.**
  have hchain : ∀ n : ℕ, ∃ f : ℕ → ResolvedExec (PMF State) Label,
      f 0 = root ∧ ∀ i, i < n → succ i (f i) (f (i + 1)) := by
    intro n
    obtain ⟨De, hDeinit, hDeterm, hDeshadow⟩ := exists_shadowing_prefix F s r hcons n
    refine ⟨fun i => De.take i, ?_, ?_⟩
    · -- `f 0 = root`.
      change De.take 0 = root
      apply AlterSeq.mk.injEq .. |>.mpr
      exact ⟨hDeinit, rfl⟩
    · intro i hi
      refine ⟨take_take De (i + 1) i (Nat.le_succ i), ?_, ?_⟩
      · -- `(De.take (i+1)).trans.TerminatedAt (i+1)`.
        exact take_terminatedAt_self De (i + 1)
      · -- shadowing at `i+1`.
        obtain ⟨H, hH⟩ := hDeshadow (i + 1) hi
        exact ⟨H, hH⟩
  -- **(B) Finite branching.**  A child `de'` of `de` at level `n` is determined by its single last
  -- transition `de'.trans.get? n`, which injects into `step_emissions_finite F s hbr de`.
  have hfinChildren : ∀ (n : ℕ) (de : ResolvedExec (PMF State) Label),
      {de' | succ n de de'}.Finite := by
    intro n de
    -- **Per-child data.**  For any child `de'`, its `n`-th transition `((l, ω), dq)` has
    -- `some (l, ω) ∈ (s.next de).support` and `dq ∈ ω.support`.
    have hchildData : ∀ de' ∈ {de' | succ n de de'},
        ∃ (l : Label) (ω : PMF (PMF State)) (dq : PMF State),
          de'.trans.get? n = some ((l, ω), dq) ∧
          some (l, ω) ∈ (s.next de).support ∧ dq ∈ ω.support := by
      rintro de' ⟨htake, hterm, H, hH⟩
      -- Reachability at some level `N`; the `e`-part `r.take (n+1)` fixes `N = n+1`.
      obtain ⟨N, hN⟩ := tsum_ne_zero_exists hH
      obtain ⟨hEterm', hEmin'⟩ := reachAfter_length F s N ⟨de', r.take (n + 1), H⟩ hN
      obtain ⟨hDterm', hDmin'⟩ := reachAfter_de_length F s N ⟨de', r.take (n + 1), H⟩ hN
      -- `N = n+1` (the `e`-part `r.take (n+1)` terminates minimally at `n+1`).
      have hNeq : N = n + 1 := by
        have hchange : (⟨de', r.take (n + 1), H⟩ : LowerConfig sys).e = r.take (n + 1) := rfl
        rw [hchange] at hEterm' hEmin'
        apply Nat.le_antisymm
        · -- `N ≤ n+1`: else `hEmin' (n+1)` contradicts `take_terminatedAt`.
          by_contra hc
          push Not at hc
          exact hEmin' (n + 1) hc (take_terminatedAt r (n + 1) hinf)
        · -- `n+1 ≤ N`: else `take_terminatedAt_min N` contradicts `hEterm'`.
          by_contra hc
          push Not at hc
          exact take_terminatedAt_min r (n + 1) hinf N hc hEterm'
      subst hNeq
      -- `de'` has an `n`-th transition (it terminates minimally at `n+1`).
      have hne : ¬ de'.trans.TerminatedAt n := hDmin' n (Nat.lt_succ_self n)
      obtain ⟨t, hgett⟩ := Option.ne_none_iff_exists'.mp hne
      obtain ⟨⟨l, ω⟩, dq⟩ := t
      -- `de'` is consistent with `⟨δ, s⟩`, so its `n`-th step is scheduler-supported.
      have hcons' : (⟨PMF.pure (sys.distF F).init, s⟩ :
          ResolvedProbabilisticExecution (sys.distF F)).Consistent de' :=
        reachProb_de_consistent F s de' (r.take (n + 1)) H ⟨n + 1, hDterm'⟩ hH
      obtain ⟨hnext, hωdq⟩ := hcons'.2 n l ω dq hgett
      -- `de'.take n = de`, so `s.next de (some (l,ω)) ≠ 0`.
      rw [htake] at hnext
      exact ⟨l, ω, dq, hgett, (PMF.mem_support_iff _ _).mpr hnext,
        (PMF.mem_support_iff _ _).mpr hωdq⟩
    -- Inject children into `step_emissions_finite F s hbr de` via `de' ↦ de'.trans.get? n`.
    set g : ResolvedExec (PMF State) Label → Option ((Label × PMF (PMF State)) × PMF State) :=
      fun de' => de'.trans.get? n with hg
    apply Set.Finite.of_injOn (f := g)
      (t := (fun p => some p) '' {p : (Label × PMF (PMF State)) × PMF State |
        some p.1 ∈ (s.next de).support ∧ p.2 ∈ p.1.2.support})
    · rintro de' hde'
      obtain ⟨l, ω, dq, hgett, hsupp, hdqsupp⟩ := hchildData de' hde'
      exact ⟨((l, ω), dq), ⟨hsupp, hdqsupp⟩, by simp only [hg]; exact hgett.symm⟩
    · -- Injectivity on children.
      rintro de'₁ hde'₁ de'₂ hde'₂ heq
      obtain ⟨l₁, ω₁, dq₁, hget₁, _, _⟩ := hchildData de'₁ hde'₁
      obtain ⟨l₂, ω₂, dq₂, hget₂, _, _⟩ := hchildData de'₂ hde'₂
      rw [hg] at heq
      have hgeteq : de'₁.trans.get? n = de'₂.trans.get? n := heq
      obtain ⟨htake₁, hterm₁, _⟩ := hde'₁
      obtain ⟨htake₂, hterm₂, _⟩ := hde'₂
      refine resolvedExec_eq_of_take_get? de'₁ de'₂ n ?_ (by rw [htake₁, htake₂]) hgeteq
        hterm₁ hterm₂
      -- `de'₁.init = de'₂.init` from `de'.take n = de`.
      have e1 : de'₁.init = de.init := by rw [← htake₁]; rfl
      have e2 : de'₂.init = de.init := by rw [← htake₂]; rfl
      rw [e1, e2]
    · exact (step_emissions_finite F s hbr de).image _
  -- `r.init = sys.init` from `hcons`'s init clause.
  have hrinit : r.init = sys.init := by
    have h1 : (⟨PMF.pure sys.init, lowerSched F s⟩ :
        ResolvedProbabilisticExecution sys).initState r.init ≠ 0 := hcons.1
    change (PMF.pure sys.init) r.init ≠ 0 at h1
    rw [PMF.pure_apply] at h1
    by_contra hc; rw [if_neg hc] at h1; exact h1 rfl
  -- **(C) König's lemma.**
  obtain ⟨f, hf0, hfstep⟩ := exists_infinite_chain succ root hfinChildren hchain
  have hfstep' : ∀ i, (f (i + 1)).take i = f i ∧ (f (i + 1)).trans.TerminatedAt (i + 1) ∧
      ∃ h, LowerReachProb F s ⟨f (i + 1), r.take (i + 1), h⟩ ≠ 0 := hfstep
  -- **Prefix stability.**  `(f j).take i = f i` for `i ≤ j`.
  have hstable : ∀ i j, i ≤ j → (f j).take i = f i := by
    intro i j hij
    induction j with
    | zero =>
      obtain rfl : i = 0 := Nat.le_zero.mp hij
      rw [hf0]; rfl
    | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hij) with hlt | heq
      · have hik : i ≤ k := Nat.lt_succ_iff.mp hlt
        rw [← take_take (f (k + 1)) k i hik, (hfstep' k).1]
        exact ih hik
      · subst heq; exact take_self_of_terminatedAt (f (k + 1)) (k + 1) (hfstep' k).2.1
  -- Each `f (n+1)` has a genuine `n`-th transition.
  have hsome : ∀ n, (f (n + 1)).trans.get? n ≠ none := by
    intro n htn
    -- Reachability at some level fixes the length to `n+1`, so `de'` is not terminated at `n`.
    obtain ⟨H, hH⟩ := (hfstep' n).2.2
    obtain ⟨N, hN⟩ := tsum_ne_zero_exists hH
    obtain ⟨hEterm', hEmin'⟩ := reachAfter_length F s N ⟨f (n + 1), r.take (n + 1), H⟩ hN
    obtain ⟨hDterm', hDmin'⟩ := reachAfter_de_length F s N ⟨f (n + 1), r.take (n + 1), H⟩ hN
    have hchange : (⟨f (n + 1), r.take (n + 1), H⟩ : LowerConfig sys).e = r.take (n + 1) := rfl
    rw [hchange] at hEterm' hEmin'
    have hNeq : N = n + 1 := by
      apply Nat.le_antisymm
      · by_contra hc; push Not at hc
        exact hEmin' (n + 1) hc (take_terminatedAt r (n + 1) hinf)
      · by_contra hc; push Not at hc
        exact take_terminatedAt_min r (n + 1) hinf N hc hEterm'
    subst hNeq
    exact hDmin' n (Nat.lt_succ_self n) htn
  -- Position-`n` transition is `f m`'s for any `m > n`.
  have hgetstable : ∀ n m, n < m → (f m).trans.get? n = (f (n + 1)).trans.get? n := by
    intro n m hnm
    have h1 : (f m).take (n + 1) = f (n + 1) := hstable (n + 1) m hnm
    rw [← h1, take_trans_get? (f m) (Nat.lt_succ_self n)]
  -- **(D) Assemble the infinite abstract run `de`.**
  have hstreamSeq : ∀ n, (fun m => (f (m + 1)).trans.get? m) n = none →
      (fun m => (f (m + 1)).trans.get? m) (n + 1) = none := fun n hn => absurd hn (hsome n)
  set de : ResolvedExec (PMF State) Label :=
    ⟨PMF.pure sys.init, ⟨fun n => (f (n + 1)).trans.get? n, hstreamSeq _⟩⟩ with hde
  have hdeget : ∀ n, de.trans.get? n = (f (n + 1)).trans.get? n := fun n => rfl
  have hdeinf : ¬ de.trans.Terminates := by
    rintro ⟨n, hn⟩
    rw [Stream'.Seq.TerminatedAt, hdeget n] at hn
    exact hsome n hn
  -- `de.take n = f n`.
  have hdetake : ∀ n, de.take n = f n := by
    intro n
    have hfnterm : (f n).trans.TerminatedAt n := by
      cases n with
      | zero => rw [hf0]; exact Stream'.Seq.terminatedAt_nil
      | succ k => exact (hfstep' k).2.1
    have hfninit : (f n).init = PMF.pure sys.init := by
      have := hstable 0 n (Nat.zero_le n)
      rw [hf0] at this
      have h2 : (f n).init = ((f n).take 0).init := rfl
      rw [h2, this]
    apply AlterSeq.mk.injEq .. |>.mpr
    refine ⟨hfninit.symm, ?_⟩
    apply Stream'.Seq.ext
    intro m
    by_cases hm : m < n
    · rw [Stream'.Seq.ofList_get?, seq_getElem?_take de.trans n m hm, hdeget m,
        ← hgetstable m n hm]
    · have hle : n ≤ m := Nat.le_of_not_lt hm
      rw [Stream'.Seq.ofList_get?]
      rw [List.getElem?_eq_none (Nat.le_trans Stream'.Seq.length_take_le hle),
        Stream'.Seq.le_stable (f n).trans hle hfnterm]
  refine ⟨de, hdeinf, ⟨?_, ?_⟩, ?_⟩
  · -- Initial mass.
    change (PMF.pure (sys.distF F).init) de.init ≠ 0
    rw [show de.init = PMF.pure sys.init from rfl]
    rw [PMF.pure_apply, if_pos (show PMF.pure sys.init = (sys.distF F).init from rfl)]
    exact one_ne_zero
  · -- Step consistency at each `n`: transfer from the reachable node `f (n+1)`.
    intro n l ω dq hget
    obtain ⟨H, hH⟩ := (hfstep' n).2.2
    have hDterm' : (f (n + 1)).trans.Terminates := ⟨n + 1, (hfstep' n).2.1⟩
    have hconsn : (⟨PMF.pure (sys.distF F).init, s⟩ :
        ResolvedProbabilisticExecution (sys.distF F)).Consistent (f (n + 1)) :=
      reachProb_de_consistent F s (f (n + 1)) (r.take (n + 1)) H hDterm' hH
    have hgetn : (f (n + 1)).trans.get? n = some ((l, ω), dq) := by
      rw [← hdeget n]; exact hget
    obtain ⟨hnext, hωdq⟩ := hconsn.2 n l ω dq hgetn
    refine ⟨?_, hωdq⟩
    -- `(f (n+1)).take n = f n = de.take n`.
    rw [hdetake n, ← (hfstep' n).1]
    exact hnext
  · -- Prefix shadowing.
    intro n
    rw [hdetake n]
    cases n with
    | zero =>
      -- `f 0 = root = ⟨δ, nil⟩`; take any `h` in `s.next root`'s support.
      rw [hf0]
      -- `r.take 0 = ⟨sys.init, nil⟩`.
      have hr0 : r.take 0 = ⟨sys.init, Seq.nil⟩ := by
        apply AlterSeq.mk.injEq .. |>.mpr
        exact ⟨hrinit, rfl⟩
      rw [hr0]
      -- `s.next root` is a PMF, so its support is nonempty.
      obtain ⟨h0, hh0⟩ := PMF.support_nonempty (s.next ⟨PMF.pure sys.init, Seq.nil⟩)
      refine ⟨h0, ?_⟩
      -- `LowerReachAfter 0 ⟨root, ⟨init, nil⟩, h0⟩ = s.next root h0 ≠ 0`.
      have hle : LowerReachAfter F s 0 ⟨⟨PMF.pure sys.init, Seq.nil⟩, ⟨sys.init, Seq.nil⟩, h0⟩
          ≤ LowerReachProb F s ⟨⟨PMF.pure sys.init, Seq.nil⟩, ⟨sys.init, Seq.nil⟩, h0⟩ :=
        ENNReal.le_tsum 0
      intro h0eq
      rw [LowerReachAfter_zero, if_pos ⟨rfl, rfl⟩] at hle
      rw [h0eq] at hle
      exact (PMF.mem_support_iff _ _).mp hh0 (le_antisymm hle bot_le)
    | succ k =>
      obtain ⟨H, hH⟩ := (hfstep' k).2.2
      exact ⟨H, hH⟩

/-- **Infinite fairness of `lowerSched`.** Under `SchedFinBranch F s` and abstract fairness of
`⟨δ_{𝒟f.init}, s⟩`, every infinite consistent concrete run `r` takes infinitely many `F`-fair steps.

Proof: `exists_infinite_coupled_de` gives an infinite `de` consistent with `⟨δ, s⟩`, shadowing `r`;
`h_fair.inf_fair de (¬terminates) (Consistent) N` gives `n ≥ N` with `F.dist.FairStepAt de n`, i.e.
`de.stateAt n = some β`, `de.trans.get? n = some ((l,ω),dq)`, `F.dist.fair β l ω`. Take the
shadowing
`⟨de.take (n+1), r.take (n+1), H⟩` reachable and peel its last chain step to the predecessor
`⟨de.take n, r.take n, some (l,ω)⟩`: from the nonzero `LowerStep` weight read off
`μₙ ∈ (tKernel β l ω qₚ).support` (its `tKernel(μₙ)` factor), where `μₙ` is `r`'s `n`-th recorded
transition and `qₚ = lastStateOf (r.take n) = r.stateAt n = β`'s coupled state; `reachAfter_coupled`
gives `qₚ ∈ β.support`; label-sync (`reachAfter_labels_eq`) gives the shared label `l`. Then
`tKernel_fair F β l ω qₚ μₙ … : F.fair qₚ l μₙ`, which is `F.FairStepAt r n`
(`r.stateAt n = qₚ`, `r.trans.get? n = some ((l, μₙ), qₙ)`). -/
theorem lowerSched_inf_fair (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (hbr : SchedFinBranch F s)
    (h_fair : (⟨PMF.pure (sys.distF F).init, s⟩ :
        ResolvedProbabilisticExecution (sys.distF F)).IsFair F.dist)
    (r : ResolvedExec State Label) (hinf : ¬ r.trans.Terminates)
    (hcons : (⟨PMF.pure sys.init, lowerSched F s⟩ :
        ResolvedProbabilisticExecution sys).Consistent r) (N : ℕ) :
    ∃ n, N ≤ n ∧ F.FairStepAt r n := by
  classical
  -- Lift `r` to an infinite consistent abstract run `de` shadowing `r`.
  obtain ⟨de, hde_inf, hde_cons, hde_shadow⟩ :=
    exists_infinite_coupled_de F s hbr r hinf hcons
  -- The abstract fairness of `⟨δ, s⟩` gives an `F.dist`-fair abstract step `n ≥ N`.
  obtain ⟨n, hNn, β, l, ω, dq, hβ, hgetde, hfair⟩ := h_fair.inf_fair de hde_inf hde_cons N
  refine ⟨n, hNn, ?_⟩
  -- Shadowing config `c := ⟨de.take (n+1), r.take (n+1), H⟩` reachable at some level `M`.
  obtain ⟨H, hH⟩ := hde_shadow (n + 1)
  set c : LowerConfig sys := ⟨de.take (n + 1), r.take (n + 1), H⟩ with hc
  obtain ⟨M, hM⟩ := tsum_ne_zero_exists hH
  -- `M = n+1` (the `e`-part terminates minimally at `n+1`).
  obtain ⟨hEterm, hEmin⟩ := reachAfter_length F s M c hM
  have hcE : c.e = r.take (n + 1) := rfl
  rw [hcE] at hEterm hEmin
  have hMeq : M = n + 1 := by
    apply Nat.le_antisymm
    · by_contra hcM; push Not at hcM
      exact hEmin (n + 1) hcM (take_terminatedAt r (n + 1) hinf)
    · by_contra hcM; push Not at hcM
      exact take_terminatedAt_min r (n + 1) hinf M hcM hEterm
  subst hMeq
  -- Peel one chain step: predecessor `c₀`.
  rw [LowerReachAfter_succ] at hM
  obtain ⟨c₀, hc₀⟩ := tsum_ne_zero_exists hM
  have hreach₀ : LowerReachAfter F s n c₀ ≠ 0 := fun h => hc₀ (by rw [h, zero_mul])
  have hstep : LowerStep F s c₀ c ≠ 0 := fun h => hc₀ (by rw [h, mul_zero])
  -- `Coupled c₀`, and `c₀`'s runs terminate minimally at `n`.
  have hcoup₀ : Coupled c₀ := reachAfter_coupled F s n c₀ hreach₀
  obtain ⟨hDterm₀, hEterm₀, hmem₀⟩ := hcoup₀
  obtain ⟨hEmin₀'', hEmin₀⟩ := reachAfter_length F s n c₀ hreach₀
  obtain ⟨hDmin₀'', hDmin₀⟩ := reachAfter_de_length F s n c₀ hreach₀
  -- Read off the `LowerStep` structure.
  revert hstep
  unfold LowerStep
  cases hh : c₀.h with
  | none => intro hstep; exact absurd rfl hstep
  | some lω =>
    obtain ⟨l₀, ω₀⟩ := lω
    simp only
    set μ' : PMF State := lastMuOf c.e with hμ'def
    by_cases hif : c.de.init = c₀.de.init ∧ c.e.init = c₀.e.init ∧
        c.de.trans = c₀.de.trans.append (Seq.cons ((l₀, ω₀), lastStateOf c.de) Seq.nil) ∧
        c.e.trans = c₀.e.trans.append (Seq.cons ((l₀, μ'), lastStateOf c.e) Seq.nil)
    · rw [if_pos hif]
      intro hweight
      obtain ⟨hdeinit, heinit, hdetrans, hetrans⟩ := hif
      -- `c₀.de = de.take n`, `c₀.e = r.take n`.
      have hc₀de : c₀.de = de.take n := by
        rw [← take_of_append_singleton c.de c₀.de n _ hdeinit hdetrans hDmin₀'' hDmin₀]
        change (de.take (n + 1)).take n = de.take n
        exact take_take de (n + 1) n (Nat.le_succ n)
      have hc₀e : c₀.e = r.take n := by
        rw [← take_of_append_singleton c.e c₀.e n _ heinit hetrans hEmin₀'' hEmin₀]
        change (r.take (n + 1)).take n = r.take n
        exact take_take r (n + 1) n (Nat.le_succ n)
      -- `r.stateAt n = some qₚ`.
      obtain ⟨qₚ, hqₚ⟩ : ∃ qₚ, r.stateAt n = some qₚ := by
        cases hcq : r.stateAt n with
        | none =>
          exfalso
          cases n with
          | zero => simp [AlterSeq.stateAt] at hcq
          | succ k =>
            change (r.trans.get? k).map Prod.snd = none at hcq
            have hterm : r.trans.TerminatedAt k := by
              cases hk : r.trans.get? k with
              | none => exact hk
              | some v => rw [hk] at hcq; simp at hcq
            exact hinf ⟨k, hterm⟩
        | some qₚ => exact ⟨qₚ, rfl⟩
      -- `lastStateOf c₀.de = β`, `lastStateOf c₀.e = qₚ`.
      have hlast_de : lastStateOf c₀.de = β := by
        rw [hc₀de]; exact lastStateOf_take de n hde_inf hβ
      have hlast_e : lastStateOf c₀.e = qₚ := by
        rw [hc₀e]; exact lastStateOf_take r n hinf hqₚ
      -- `qₚ ∈ β.support`.
      have hqβ : qₚ ∈ β.support := by
        rw [← hlast_e, ← hlast_de]; exact hmem₀
      -- Identify the abstract last transition: `l₀ = l`, `ω₀ = ω`, `lastStateOf c.de = dq`.
      have hde_get_n : c.de.trans.get? n = some ((l, ω), dq) := by
        change (de.take (n + 1)).trans.get? n = _
        rw [take_trans_get? de (Nat.lt_succ_self n)]; exact hgetde
      have hde_get_n' : c.de.trans.get? n = some ((l₀, ω₀), lastStateOf c.de) := by
        rw [hdetrans]
        have hlen : n = Nat.find hDterm₀ := by
          apply le_antisymm
          · rw [Nat.le_find_iff]; intro m hm; exact hDmin₀ m hm
          · exact Nat.find_le hDmin₀''
        rw [hlen]
        have := Stream'.Seq.get?_append_find hDterm₀
          (Seq.cons ((l₀, ω₀), lastStateOf c.de) Seq.nil) 0
        rw [Nat.add_zero] at this
        rw [this]; rfl
      rw [hde_get_n] at hde_get_n'
      obtain ⟨⟨hl₀, hω₀⟩, hdq⟩ := Prod.mk.injEq .. ▸ (Prod.mk.injEq .. ▸ Option.some.inj hde_get_n')
      -- Identify the concrete last transition of `r`: `r.trans.get? n = some ((l, μ'), qₙ)`.
      have he_get_n : c.e.trans.get? n = some ((l₀, μ'), lastStateOf c.e) := by
        rw [hetrans]
        have hlen : n = Nat.find hEterm₀ := by
          apply le_antisymm
          · rw [Nat.le_find_iff]; intro m hm; exact hEmin₀ m hm
          · exact Nat.find_le hEmin₀''
        rw [hlen]
        have := Stream'.Seq.get?_append_find hEterm₀
          (Seq.cons ((l₀, μ'), lastStateOf c.e) Seq.nil) 0
        rw [Nat.add_zero] at this
        rw [this]; rfl
      have hr_get_n : r.trans.get? n = some ((l, μ'), lastStateOf c.e) := by
        have h1 : c.e.trans.get? n = r.trans.get? n := by
          change (r.take (n + 1)).trans.get? n = _
          exact take_trans_get? r (Nat.lt_succ_self n)
        rw [← h1, he_get_n, hl₀]
      -- `μ' ∈ (tKernel β l ω qₚ).support` from the weight's leading factor.
      have hker_ne : (tKernel F (lastStateOf c₀.de) l₀ ω₀ (lastStateOf c₀.e)) μ' ≠ 0 := by
        intro h0
        apply hweight
        rw [h0, zero_mul, zero_mul, zero_mul, zero_mul]
      rw [hlast_de, hlast_e, ← hl₀, ← hω₀] at hker_ne
      have hμmem : μ' ∈ (tKernel F β l ω qₚ).support := (PMF.mem_support_iff _ _).mpr hker_ne
      -- `F.fair qₚ l μ'`.
      have hfair_r : F.fair qₚ l μ' := tKernel_fair F β l ω qₚ μ' hμmem hqβ hfair
      -- Assemble `F.FairStepAt r n`.
      exact ⟨qₚ, l, μ', lastStateOf c.e, hqₚ, hr_get_n, hfair_r⟩
    · rw [if_neg hif]; intro hstep; exact absurd rfl hstep

/-! ### Fairness of the reconstructed execution, and the superset inclusion -/

/-- **The reconstructed concrete execution is fair.** Combining the two clauses:
`lowerSched_halt_fairDeadlock` (halt) and `lowerSched_inf_fair` (infinite, under `SchedFinBranch`),
`⟨δ_{sys.init}, lowerSched F s⟩` is `IsFair F` whenever the abstract `⟨δ_{𝒟f.init}, s⟩` is
`F.dist`-fair and `s` is finitely branching. -/
theorem lowerSched_isFair (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (hbr : SchedFinBranch F s)
    (h_fair : (⟨PMF.pure (sys.distF F).init, s⟩ :
        ResolvedProbabilisticExecution (sys.distF F)).IsFair F.dist) :
    (⟨PMF.pure sys.init, lowerSched F s⟩ : ResolvedProbabilisticExecution sys).IsFair F :=
  ⟨fun r h hcons hnone => lowerSched_halt_fairDeadlock F s h_fair r h hcons hnone,
   fun r hinf hcons N => lowerSched_inf_fair F s hbr h_fair r hinf hcons N⟩

/-- **Superset inclusion (the reverse of `fairAchievableTraceDists_subset_distF`).** Every fair
`𝒟f(sys, F)`-achievable trace distribution is fair-achievable on `sys`, provided every fair
`𝒟f`-execution (from the Dirac initial belief) has a finitely-branching scheduler (`hbr`). Witnessed
by the algorithmic lowering `⟨δ_{sys.init}, lowerSched F pe.scheduler⟩`: `lowerSched_isFair`
supplies
`IsFair F` and `lowerSched_traceProbR` the trace equality.

Together with `fairAchievableTraceDists_subset_distF` this gives the fair `𝒟f`-invariance
`fairAchievableTraceDists F = fairAchievableTraceDists F.dist` (under the two transfer hypotheses).
-/
theorem fairAchievableTraceDists_distF_subset (F : Fairness sys)
    (hbr : ∀ pe : ResolvedProbabilisticExecution (sys.distF F),
      pe.initState = PMF.pure (sys.distF F).init → pe.IsFair F.dist →
        SchedFinBranch F pe.scheduler) :
    fairAchievableTraceDists F.dist ⊆ fairAchievableTraceDists F := by
  rintro D ⟨pe, h_init, h_fair, h_tp⟩
  -- Re-express the abstract fairness/traces in the canonical `⟨δ_{𝒟f.init}, pe.scheduler⟩` form.
  have h_fair' : (⟨PMF.pure (sys.distF F).init, pe.scheduler⟩ :
      ResolvedProbabilisticExecution (sys.distF F)).IsFair F.dist := by
    rw [← h_init]; exact h_fair
  refine ⟨⟨PMF.pure sys.init, lowerSched F pe.scheduler⟩, rfl, ?_, ?_⟩
  · exact lowerSched_isFair F pe.scheduler
      (hbr ⟨PMF.pure (sys.distF F).init, pe.scheduler⟩ rfl h_fair') h_fair'
  · intro τ
    rw [lowerSched_traceProbR F pe.scheduler τ]
    have htp' : (⟨PMF.pure (sys.distF F).init, pe.scheduler⟩ :
        ResolvedProbabilisticExecution (sys.distF F)).traceProbR τ = pe.traceProbR τ := by
      rw [← h_init]
    rw [htp']; exact h_tp τ

end PLTS
