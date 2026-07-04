/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Expansion.ProbOf

/-!
# The concrete scheduler of the unfolding algorithm

Given a `sys^w`-scheduler `ws`, this file defines the concrete `sys`-scheduler
`expandSched ws` that realises the unfolded execution — the memoryless scheduler
whose path distribution reproduces the reaching probabilities of the algorithm's
configurations.

The scheduler at a concrete history `exec` is a Bayesian posterior over the next
inner draw, conditioned on the running concrete trajectory. It is defined as a
ratio of two reaching probabilities:

* `reachArr ws exec` (the **normalizer**) — the probability of *reaching* `exec`,
  counted at the **arrival** configuration: a config with `e ⌢ e' = exec` whose
  segment `e'` is longer than a state (`e'.trans ≠ nil`). Each run passes through
  exactly one such config per non-empty concrete prefix (since `e ⌢ e'` only ever
  grows, via the inner instruction), so this counts each run once — and crucially
  it is defined even when the run later *diverges* (an arriving run still has the
  prefix `exec`). The empty initial prefix `⟨init, nil⟩` has no arrival config, so
  it is carved out to `1` (the root is reached with probability `1`).

* `reachDep ws exec l μ` (the **numerator**) — the probability of being at a
  **departure** configuration: a config with `e ⌢ e' = exec` whose next inner draw
  is `t = some (l, μ)`. This is the source of the next concrete transition (the
  inner instruction then samples the next state from `μ`); it too is hit at most
  once per run, by monotonicity of `e ⌢ e'`.

The mass on a proper step `some (l, μ)` is `reachDep / reachArr`; the halt label
`⊥` (`none`) takes the **remaining** mass `1 - ∑ (proper masses)`, which absorbs
exactly the runs that reach `exec` but never depart it — i.e. halt *or* diverge
there (the correct stopping mass for a cylinder trace probability).
-/

open Stream'

namespace PLTS

variable {State Label : Type} [Silent Label] {sys : System State Label}

/-- The full concrete trajectory of a configuration: the committed concrete
execution `e` followed by the in-progress segment `e'`. -/
def Config.concat (c : Config sys) : AlterSeq State Label :=
  ⟨c.e.init, c.e.trans.append c.e'.trans⟩

open Classical in
/-- **Arrival reach** (the scheduler's normalizer): the probability of reaching the
concrete trajectory `exec`, counted at the unique *arrival* configuration
(`c.concat = exec` with a nonempty segment `c.e'.trans ≠ nil`). The empty initial
prefix `⟨init, nil⟩` has no arrival configuration and is reached with probability
`1`, so it is carved out. -/
noncomputable def reachArr (ws : Scheduler sys^w) (exec : AlterSeq State Label) : ENNReal :=
  if exec = ⟨sys.init, Seq.nil⟩ then 1
  else ∑' c : {c : Config sys // c.concat = exec ∧ c.e'.trans ≠ Seq.nil}, reachProb ws c.1

/-- **Departure reach** for the step `(l, μ)` (the scheduler's numerator): the
probability of being at a *departure* configuration — `c.concat = exec` whose next
inner draw is `t = some (l, μ)` — the source of the next concrete transition. -/
noncomputable def reachDep (ws : Scheduler sys^w) (exec : AlterSeq State Label)
    (l : Label) (μ : PMF State) : ENNReal :=
  ∑' c : {c : Config sys // c.concat = exec ∧ c.t = some (l, μ)}, reachProb ws c.1

/-- The mass function of `expandSched ws` at the concrete history `exec`: a proper
step `some (l, μ)` gets the posterior `reachDep / reachArr`, and the halt label
`⊥ = none` gets the remaining mass (the halt-or-diverge stopping mass). -/
noncomputable def expandMass (ws : Scheduler sys^w) (exec : AlterSeq State Label) :
    Option (Label × PMF State) → ENNReal
  | some (l, μ) => reachDep ws exec l μ / reachArr ws exec
  | none => 1 - ∑' p : Label × PMF State, reachDep ws exec p.1 p.2 / reachArr ws exec

/-- A nonzero guarded weight `if P then a else 0` forces its guard `P`. -/
private theorem of_ite_ne_zero {P : Prop} [Decidable P] {a : ENNReal}
    (h : (if P then a else 0) ≠ 0) : P := by
  by_contra hP; rw [if_neg hP] at h; exact h rfl

/-- A nonzero guarded weight `if P then a else 0` has nonzero branch `a`. -/
private theorem ne_zero_of_ite_ne_zero {P : Prop} [Decidable P] {a : ENNReal}
    (h : (if P then a else 0) ≠ 0) : a ≠ 0 := by
  intro ha; rw [ha, ite_self] at h; exact h rfl

omit [Silent Label] in
/-- At any terminated position `n` of a finite execution, the recorded state `s` is `lastOf e`. -/
private theorem lastOf_of_stateAt {e : AlterSeq State Label} {n : ℕ} {s : State}
    (hterm : e.trans.TerminatedAt n) (hstate : e.stateAt n = some s) : lastOf e = s := by
  have hT : e.trans.Terminates := ⟨n, hterm⟩
  have h_find_le : Nat.find hT ≤ n := Nat.find_le hterm
  have h_n_le : n ≤ Nat.find hT := by
    by_contra h_lt
    push Not at h_lt
    rcases n with _ | m
    · exact absurd h_lt (Nat.not_lt_zero _)
    · have hk_ge : Nat.find hT ≤ m := Nat.lt_succ_iff.mp h_lt
      have h_term_k : e.trans.TerminatedAt m :=
        Stream'.Seq.terminated_stable e.trans hk_ge (Nat.find_spec hT)
      have h_state_none : e.stateAt (m + 1) = none := by
        change (e.trans.get? m).map Prod.snd = none
        rw [show e.trans.get? m = none from h_term_k]; rfl
      rw [h_state_none] at hstate
      exact Option.some_ne_none s hstate.symm
  have h_n_eq : n = Nat.find hT := le_antisymm h_n_le h_find_le
  have h := AlterSeq.stateAt_find_eq_endState e hT
  rw [← h_n_eq] at h; rw [h] at hstate
  rw [lastOf_eq_endState e hT]; exact Option.some.inj hstate

open Classical in
/-- If a configuration with a pending inner draw (`c.t = some p`) is reachable, then its weak
step is active (`c.wt = some q`): the inner-loop `t` is only ever set while a weak step runs. -/
private theorem reachAfter_t_wt (ws : Scheduler sys^w) (n : ℕ) (c : Config sys)
    (p : Label × PMF State) (hreach : reachAfter ws n c ≠ 0) (ht : c.t = some p) :
    ∃ q, c.wt = some q := by
  cases n with
  | zero =>
    simp only [reachAfter] at hreach
    by_cases hcond : (c.we = (⟨sys.init, Seq.nil⟩ : AlterSeq State Label) ∧
        c.e = ⟨sys.init, Seq.nil⟩ ∧ c.e' = ⟨sys.init, Seq.nil⟩ ∧
        (∀ p, c.wt = some p → c.s = schedOf sys sys.init p.1 p.2) ∧
        (c.wt = none → c.s = Scheduler.halt sys))
    · rw [if_pos hcond] at hreach
      have h2 := (mul_ne_zero_iff.mp hreach).2
      cases hwt : c.wt with
      | none => exfalso; rw [hwt] at h2; simp only [ht] at h2; simp at h2
      | some q => exact ⟨q, rfl⟩
    · rw [if_neg hcond] at hreach; exact absurd rfl hreach
  | succ m =>
    rw [reachAfter] at hreach
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, reachAfter ws m c₀ * step ws c₀ c ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hreach (ENNReal.tsum_eq_zero.mpr hcon)
    have hstep := (mul_ne_zero_iff.mp hc₀).2
    obtain ⟨we₀, e₀, wt₀, s₀, e'₀, t₀⟩ := c₀
    cases wt₀ with
    | none => simp only [step] at hstep; exact absurd rfl hstep
    | some wtp =>
      obtain ⟨lw, μw⟩ := wtp
      cases t₀ with
      | some tp =>
        obtain ⟨l', μ'⟩ := tp
        simp only [step] at hstep
        obtain ⟨_, _, hcwt, _, _, _⟩ := of_ite_ne_zero hstep
        exact ⟨(lw, μw), hcwt⟩
      | none =>
        simp only [step] at hstep
        have h2 := (mul_ne_zero_iff.mp (ne_zero_of_ite_ne_zero hstep)).2
        cases hwt : c.wt with
        | none => exfalso; rw [hwt] at h2; simp only [ht] at h2; simp at h2
        | some q => exact ⟨q, rfl⟩

open Classical in
/-- **Inner-draw membership.** A reachable configuration with pending inner draw `c.t = some p`
has that draw in the support of its witness scheduler: `some p ∈ (c.s.next c.e').support`. -/
private theorem reachProb_t_mem (ws : Scheduler sys^w) (c : Config sys) (p : Label × PMF State)
    (h : reachProb ws c ≠ 0) (ht : c.t = some p) : some p ∈ (c.s.next c.e').support := by
  rw [reachProb] at h
  obtain ⟨n, hn⟩ : ∃ n, reachAfter ws n c ≠ 0 := by
    by_contra hcon; push Not at hcon; exact h (ENNReal.tsum_eq_zero.mpr hcon)
  obtain ⟨q, hq⟩ := reachAfter_t_wt ws n c p hn ht
  have hpos := reachAfter_inner_pos ws n c hn q hq
  rw [ht] at hpos
  exact (PMF.mem_support_iff _ _).mpr hpos

/-- The `tsum` over an `Option` type splits off the `none` term. -/
private theorem tsum_option_eq {α : Type} (g : Option α → ENNReal) :
    ∑' o, g o = g none + ∑' a, g (some a) := by
  rw [← Equiv.tsum_eq (Equiv.optionEquivSumPUnit.{0,0} α).symm g,
    Summable.tsum_sum (f := fun c => g ((Equiv.optionEquivSumPUnit.{0,0} α).symm c))
      ENNReal.summable ENNReal.summable, add_comm]
  congr 1
  rw [tsum_eq_single PUnit.unit (by rintro ⟨⟩ h; exact absurd rfl h)]
  rfl

/-! ### Indicator-sum framework for the flow argument

The proof of `reachDep_sum_le` is a *flow-conservation* argument on the configuration Markov
chain. We collect the reaching mass over configuration sets cut out by a predicate `P`, at the
level of `reachProb` (`RP`) and per instruction-count (`RA`), and reduce the inequality to a
per-level OUTER-step conservation identity (`pli`) that telescopes. -/

omit [Silent Label] in
/-- An append equals `nil` only if both parts are `nil`. -/
theorem append_eq_nil {α : Type} {s t : Seq α} (h : s.append t = Seq.nil) :
    s = Seq.nil ∧ t = Seq.nil := by
  induction s using Stream'.Seq.recOn with
  | nil => rw [Stream'.Seq.nil_append] at h; exact ⟨rfl, h⟩
  | cons x s' => rw [Stream'.Seq.cons_append] at h; exact absurd h Stream'.Seq.cons_ne_nil

/-- Distribute a guard over a `tsum`. -/
private theorem ite_tsum_zero {ι : Type*} (P : Prop) [Decidable P] (f : ι → ENNReal) :
    (if P then ∑' i, f i else 0) = ∑' i, if P then f i else 0 := by
  by_cases h : P
  · simp only [if_pos h]
  · simp only [if_neg h, tsum_zero]

omit [Silent Label] in
open Classical in
/-- A subtype `tsum` rewritten as a guarded `tsum` over the whole type. -/
private theorem tsum_subtype_ite {P : Config sys → Prop} (f : Config sys → ENNReal) :
    (∑' c : {c : Config sys // P c}, f c.1) = ∑' c, if P c then f c else 0 :=
  (tsum_subtype {c | P c} f).trans (tsum_congr fun c => by rw [Set.indicator_apply]; congr 1)

omit [Silent Label] in
open Classical in
/-- The `tsum` of a guarded `some`-indicator over the draw collapses to a `≠ none` guard. -/
private theorem tsum_ite_some {a : ENNReal} (o : Option (Label × PMF State)) :
    (∑' p : Label × PMF State, if o = some p then a else 0) = if o ≠ none then a else 0 := by
  cases o with
  | none => rw [tsum_congr (fun p => if_neg (by simp)), tsum_zero, if_neg (by simp)]
  | some p =>
    rw [tsum_eq_single p (fun q hq => if_neg (by intro h; exact hq (Option.some.inj h).symm)),
      if_pos rfl, if_pos (Option.some_ne_none p)]

omit [Silent Label] in
open Classical in
/-- Pull a constant guard `A` out of a guarded `some`-indicator `tsum`. -/
private theorem tsum_ite_and_some {a : ENNReal} (A : Prop) (o : Option (Label × PMF State)) :
    (∑' p : Label × PMF State, if A ∧ o = some p then a else 0)
      = if A ∧ o ≠ none then a else 0 := by
  by_cases hA : A
  · simp only [hA, true_and]; exact tsum_ite_some o
  · simp only [hA, false_and, if_false, tsum_zero]

open Classical in
/-- **Reaching mass** over the configurations satisfying `P`. -/
private noncomputable def RP (ws : Scheduler sys^w) (P : Config sys → Prop) : ENNReal :=
  ∑' c : Config sys, if P c then reachProb ws c else 0

open Classical in
/-- **Level-`n` reaching mass** over the configurations satisfying `P`. -/
private noncomputable def RA (ws : Scheduler sys^w) (P : Config sys → Prop) (n : ℕ) : ENNReal :=
  ∑' c : Config sys, if P c then reachAfter ws n c else 0

open Classical in
/-- `RP` is the sum over instruction-counts of `RA`. -/
private theorem RP_eq_tsum_RA (ws : Scheduler sys^w) (P : Config sys → Prop) :
    RP ws P = ∑' n, RA ws P n := by
  calc RP ws P = ∑' c, if P c then ∑' n, reachAfter ws n c else 0 := by simp only [RP, reachProb]
    _ = ∑' c, ∑' n, if P c then reachAfter ws n c else 0 :=
        tsum_congr (fun c => ite_tsum_zero (P c) _)
    _ = ∑' n, ∑' c, if P c then reachAfter ws n c else 0 := ENNReal.tsum_comm
    _ = ∑' n, RA ws P n := by simp only [RA]

open Classical in
/-- Additivity of `RA` over a binary split of the predicate. -/
private theorem RA_split (ws : Scheduler sys^w) (P Q : Config sys → Prop) (n : ℕ) :
    RA ws P n = RA ws (fun c => P c ∧ Q c) n + RA ws (fun c => P c ∧ ¬ Q c) n := by
  simp only [RA]; rw [← ENNReal.tsum_add]
  refine tsum_congr (fun c => ?_); by_cases hP : P c <;> by_cases hQ : Q c <;> simp [hP, hQ]

open Classical in
/-- `RA` only depends on the predicate up to logical equivalence. -/
private theorem RA_congr (ws : Scheduler sys^w) {P Q : Config sys → Prop} (h : ∀ c, P c ↔ Q c)
    (n : ℕ) : RA ws P n = RA ws Q n := by
  simp only [RA]; exact tsum_congr (fun c => if_congr (h c) rfl rfl)

open Classical in
/-- Additivity of `RP` over a binary split of the predicate. -/
private theorem RP_split (ws : Scheduler sys^w) (P Q : Config sys → Prop) :
    RP ws P = RP ws (fun c => P c ∧ Q c) + RP ws (fun c => P c ∧ ¬ Q c) := by
  simp only [RP]; rw [← ENNReal.tsum_add]
  refine tsum_congr (fun c => ?_); by_cases hP : P c <;> by_cases hQ : Q c <;> simp [hP, hQ]

open Classical in
/-- Monotonicity of `RP` in the predicate. -/
private theorem RP_mono (ws : Scheduler sys^w) {P Q : Config sys → Prop} (h : ∀ c, P c → Q c) :
    RP ws P ≤ RP ws Q := by
  simp only [RP]; refine ENNReal.tsum_le_tsum (fun c => ?_)
  by_cases hP : P c
  · rw [if_pos hP, if_pos (h c hP)]
  · rw [if_neg hP]; positivity

open Classical in
/-- `RP` only depends on the predicate up to logical equivalence. -/
private theorem RP_congr (ws : Scheduler sys^w) {P Q : Config sys → Prop} (h : ∀ c, P c ↔ Q c) :
    RP ws P = RP ws Q := by
  simp only [RP]; exact tsum_congr (fun c => if_congr (h c) rfl rfl)

open Classical in
/-- `RP` of an unsatisfiable predicate is `0`. -/
private theorem RP_eq_zero (ws : Scheduler sys^w) {P : Config sys → Prop} (h : ∀ c, ¬ P c) :
    RP ws P = 0 := by
  simp only [RP]; exact ENNReal.tsum_eq_zero.mpr (fun c => if_neg (h c))

/-! ### The configuration predicates of the flow argument (all at a fixed trajectory `exec`) -/

/-- **Reset** configurations at `exec`: trajectory `exec`, empty current segment. -/
private def pReset (exec : AlterSeq State Label) (c : Config sys) : Prop :=
  c.concat = exec ∧ c.e'.trans = Seq.nil

/-- **OUTER-source** configurations at `exec`: trajectory `exec`, halted inner loop, active
weak step (the configurations whose OUTER instruction resets to `exec`). -/
private def pOut (exec : AlterSeq State Label) (c : Config sys) : Prop :=
  c.concat = exec ∧ c.t = none ∧ ∃ q, c.wt = some q

/-- **Fresh departures** at `exec`: a reset config that immediately drew a real inner step. -/
private def pDfresh (exec : AlterSeq State Label) (c : Config sys) : Prop :=
  c.concat = exec ∧ c.e'.trans = Seq.nil ∧ c.t ≠ none

/-- **Empty-step** configurations at `exec`: a reset config with halted inner loop but an active
weak step (the source of an empty/`τ`-only weak step — the divergence slack). -/
private def pE (exec : AlterSeq State Label) (c : Config sys) : Prop :=
  c.concat = exec ∧ c.e'.trans = Seq.nil ∧ c.t = none ∧ ∃ q, c.wt = some q

/-- **Halt** configurations at `exec`: a reset config with halted inner loop and no weak step. -/
private def pH (exec : AlterSeq State Label) (c : Config sys) : Prop :=
  c.concat = exec ∧ c.e'.trans = Seq.nil ∧ c.t = none ∧ ¬ ∃ q, c.wt = some q

/-- **Arrival/no-departure** configurations at `exec`: an OUTER-source with a nonempty segment. -/
private def pAnone (exec : AlterSeq State Label) (c : Config sys) : Prop :=
  c.concat = exec ∧ c.t = none ∧ (∃ q, c.wt = some q) ∧ c.e'.trans ≠ Seq.nil

open Classical in
/-- The reset configurations split into fresh departures, empty-step, and halt configurations. -/
private theorem RA_reset_partition (ws : Scheduler sys^w) (exec : AlterSeq State Label) (m : ℕ) :
    RA ws (pReset exec) m
      = RA ws (pDfresh exec) m + RA ws (pE exec) m + RA ws (pH exec) m := by
  rw [RA_split ws (pReset exec) (fun c => c.t ≠ none) m,
    RA_congr ws (P := fun c => pReset exec c ∧ c.t ≠ none) (Q := pDfresh exec)
      (fun c => by unfold pReset pDfresh; tauto) m,
    RA_congr ws (P := fun c => pReset exec c ∧ ¬ c.t ≠ none)
      (Q := fun c => pReset exec c ∧ c.t = none) (fun c => by unfold pReset; tauto) m,
    RA_split ws (fun c => pReset exec c ∧ c.t = none) (fun c => ∃ q, c.wt = some q) m,
    RA_congr ws (P := fun c => (pReset exec c ∧ c.t = none) ∧ ∃ q, c.wt = some q)
      (Q := pE exec) (fun c => by unfold pReset pE; tauto) m,
    RA_congr ws (P := fun c => (pReset exec c ∧ c.t = none) ∧ ¬ ∃ q, c.wt = some q)
      (Q := pH exec) (fun c => by unfold pReset pH; tauto) m, add_assoc]

open Classical in
/-- The OUTER-source configurations split into arrival/no-departure and empty-step. -/
private theorem RA_out_partition (ws : Scheduler sys^w) (exec : AlterSeq State Label) (m : ℕ) :
    RA ws (pOut exec) m = RA ws (pAnone exec) m + RA ws (pE exec) m := by
  rw [RA_split ws (pOut exec) (fun c => c.e'.trans ≠ Seq.nil) m,
    RA_congr ws (P := fun c => pOut exec c ∧ c.e'.trans ≠ Seq.nil) (Q := pAnone exec)
      (fun c => by unfold pOut pAnone; tauto) m,
    RA_congr ws (P := fun c => pOut exec c ∧ ¬ c.e'.trans ≠ Seq.nil) (Q := pE exec)
      (fun c => by unfold pOut pE; tauto) m]

open Classical in
/-- **Total OUTER outflow is `1`.** Summing the OUTER `step` weight from a halted-inner predecessor
over all targets is `1` (the next `(wt, t)` draws PMF-normalise). -/
private theorem step_outer_total (ws : Scheduler sys^w)
    (we₀ e₀ e'₀ : AlterSeq State Label) (lw : Label) (μw : PMF State) (s₀ : Scheduler sys) :
    (∑' c : Config sys, step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩ c) = 1 := by
  have hbij : (∑' c : Config sys, step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩ c)
      = ∑' pr : Option (Label × PMF State) × Option (Label × PMF State),
          step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩
            (entryCfg sys ⟨we₀.init, we₀.trans.append (Seq.cons (lw,
                lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label))
                Seq.nil)⟩ ⟨e₀.init, e₀.trans.append e'₀.trans⟩
              (lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label))
              pr.1 pr.2) :=
    entry_draw_reindex (step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩)
      ⟨we₀.init, we₀.trans.append (Seq.cons (lw,
          lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label))
          Seq.nil)⟩ ⟨e₀.init, e₀.trans.append e'₀.trans⟩
        (lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label)) (by
      intro c hcne
      simp only [step] at hcne
      obtain ⟨he, hwe2, he', hsome, hnone⟩ := of_ite_ne_zero hcne
      exact ⟨hwe2, he, he', hsome, hnone⟩)
  rw [hbij, ENNReal.tsum_prod',
    tsum_congr (fun wt => entryCfg_step_inner ws we₀ e₀ e'₀ lw μw s₀ wt)]
  exact (ws.next _).tsum_coe

open Classical in
/-- **Reset-step collapse (concrete-side analogue of `entryStep_collapse`).** Summing the `step`
weight from `c₀` into the reset configurations at `exec` is `1` exactly when `c₀` is an
OUTER-source at `exec` (active weak step, halted inner loop, `c₀.concat = exec`), and `0`
otherwise. -/
private theorem reset_step_sum (ws : Scheduler sys^w) (exec : AlterSeq State Label)
    (c₀ : Config sys) :
    (∑' c : Config sys, if pReset exec c then step ws c₀ c else 0)
      = if (∃ q, c₀.wt = some q) ∧ c₀.t = none ∧ c₀.concat = exec then 1 else 0 := by
  obtain ⟨we₀, e₀, wt₀, s₀, e'₀, t₀⟩ := c₀
  cases wt₀ with
  | none =>
    rw [if_neg (by rintro ⟨⟨q, hq⟩, -, -⟩; simp at hq)]
    exact ENNReal.tsum_eq_zero.mpr (fun c => by simp only [step, ite_self])
  | some wtp =>
    obtain ⟨lw, μw⟩ := wtp
    cases t₀ with
    | some tp =>
      obtain ⟨l', μ'⟩ := tp
      rw [if_neg (by rintro ⟨-, ht, -⟩; simp at ht)]
      refine ENNReal.tsum_eq_zero.mpr (fun c => ?_)
      by_cases hp : pReset exec c
      · rw [if_pos hp]
        simp only [step]
        rw [if_neg]
        rintro ⟨-, -, -, -, -, htr⟩
        rw [hp.2] at htr
        exact append_cons_ne_nil _ _ _ htr.symm
      · rw [if_neg hp]
    | none =>
      rw [show (∑' c : Config sys, if pReset exec c
              then step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩ c else 0)
            = ∑' c : Config sys, if (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label)
                  = exec
              then step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩ c else 0 from ?_]
      · rw [← ite_tsum_zero, step_outer_total ws we₀ e₀ e'₀ lw μw s₀]
        refine if_congr ?_ rfl rfl
        constructor
        · intro h; exact ⟨⟨(lw, μw), rfl⟩, rfl, h⟩
        · rintro ⟨-, -, h⟩; exact h
      · refine tsum_congr (fun c => ?_)
        by_cases hstep : step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩ c = 0
        · rw [hstep, ite_self, ite_self]
        · refine if_congr ?_ rfl rfl
          simp only [step] at hstep
          obtain ⟨he, hwe2, he', hsome, hnone⟩ := of_ite_ne_zero hstep
          have hce'nil : c.e'.trans = Seq.nil := by rw [he']
          have hconcat : c.concat
              = (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label) := by
            unfold Config.concat
            rw [he, hce'nil, Stream'.Seq.append_nil]
          constructor
          · rintro ⟨hc1, -⟩; exact hconcat ▸ hc1
          · intro h; exact ⟨hconcat.trans h, hce'nil⟩

open Classical in
/-- **Per-level OUTER conservation identity (PLI).** The reset mass at level `n+1` equals the
OUTER-source mass at level `n`: every reset configuration is produced by exactly the OUTER
instruction of an OUTER-source, with total weight `1`. -/
private theorem pli (ws : Scheduler sys^w) (exec : AlterSeq State Label) (n : ℕ) :
    RA ws (pReset exec) (n + 1) = RA ws (pOut exec) n := by
  simp only [RA]
  calc (∑' c, if pReset exec c then reachAfter ws (n + 1) c else 0)
      = ∑' c, if pReset exec c then ∑' c₀, reachAfter ws n c₀ * step ws c₀ c else 0 := by
        refine tsum_congr (fun c => ?_); rw [reachAfter]
    _ = ∑' c, ∑' c₀, if pReset exec c then reachAfter ws n c₀ * step ws c₀ c else 0 :=
        tsum_congr (fun c => ite_tsum_zero _ _)
    _ = ∑' c₀, ∑' c, if pReset exec c then reachAfter ws n c₀ * step ws c₀ c else 0 :=
        ENNReal.tsum_comm
    _ = ∑' c₀, reachAfter ws n c₀
          * ∑' c, if pReset exec c then step ws c₀ c else 0 := by
        refine tsum_congr (fun c₀ => ?_)
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr (fun c => by rw [mul_ite, mul_zero])
    _ = ∑' c₀, reachAfter ws n c₀
          * if (∃ q, c₀.wt = some q) ∧ c₀.t = none ∧ c₀.concat = exec then 1 else 0 := by
        refine tsum_congr (fun c₀ => by rw [reset_step_sum ws exec c₀])
    _ = ∑' c₀, if pOut exec c₀ then reachAfter ws n c₀ else 0 := by
        refine tsum_congr (fun c₀ => ?_)
        by_cases h : (∃ q, c₀.wt = some q) ∧ c₀.t = none ∧ c₀.concat = exec
        · rw [if_pos h, mul_one, if_pos (by unfold pOut; exact ⟨h.2.2, h.2.1, h.1⟩)]
        · rw [if_neg h, mul_zero,
            if_neg (by unfold pOut; rintro ⟨hc, ht, hq⟩; exact h ⟨hq, ht, hc⟩)]

open Classical in
/-- **The telescoped flow bound.** The fresh-departure plus halt mass at `exec` is at most the
arrival mass plus the (level-0) reset mass. The empty-step slack `pE` (potentially `⊤` for a
`τ`-diverging trajectory) is dropped via a per-level additive telescoping invariant. -/
private theorem tele (ws : Scheduler sys^w) (exec : AlterSeq State Label) :
    RP ws (pDfresh exec) + RP ws (pH exec)
      ≤ RP ws (pAnone exec) + RA ws (pReset exec) 0 := by
  set g : ℕ → ENNReal := fun n => RA ws (pDfresh exec) n + RA ws (pH exec) n with hg
  set e : ℕ → ENNReal := fun n => RA ws (pE exec) n with he
  set a : ℕ → ENNReal := fun n => RA ws (pAnone exec) n with ha
  have H1 : ∀ n, g (n + 1) + e (n + 1) = a n + e n := by
    intro n
    have hpli := pli ws exec n
    rw [RA_reset_partition ws exec (n + 1), RA_out_partition ws exec n] at hpli
    simp only [hg, he, ha]; rw [← hpli]; abel
  have key : ∀ N, (∑ n ∈ Finset.range N, g (n + 1)) + e N
      = (∑ n ∈ Finset.range N, a n) + e 0 := by
    intro N
    induction N with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      calc (∑ n ∈ Finset.range M, g (n + 1)) + g (M + 1) + e (M + 1)
          = (∑ n ∈ Finset.range M, g (n + 1)) + (g (M + 1) + e (M + 1)) := by abel
        _ = (∑ n ∈ Finset.range M, g (n + 1)) + (a M + e M) := by rw [H1 M]
        _ = ((∑ n ∈ Finset.range M, g (n + 1)) + e M) + a M := by abel
        _ = ((∑ n ∈ Finset.range M, a n) + e 0) + a M := by rw [ih]
        _ = (∑ n ∈ Finset.range M, a n) + a M + e 0 := by abel
  have hpartial : ∀ N, (∑ n ∈ Finset.range N, g (n + 1)) ≤ (∑' n, a n) + e 0 := by
    intro N
    calc (∑ n ∈ Finset.range N, g (n + 1))
        ≤ (∑ n ∈ Finset.range N, g (n + 1)) + e N := le_self_add
      _ = (∑ n ∈ Finset.range N, a n) + e 0 := key N
      _ ≤ (∑' n, a n) + e 0 := by gcongr; exact ENNReal.sum_le_tsum _
  have htail : (∑' n, g (n + 1)) ≤ (∑' n, a n) + e 0 := by
    rw [ENNReal.tsum_eq_iSup_nat]; exact iSup_le hpartial
  have hRPg : RP ws (pDfresh exec) + RP ws (pH exec) = ∑' n, g n := by
    rw [RP_eq_tsum_RA ws (pDfresh exec), RP_eq_tsum_RA ws (pH exec), ← ENNReal.tsum_add]
  have hRPa : RP ws (pAnone exec) = ∑' n, a n := by
    rw [RP_eq_tsum_RA ws (pAnone exec)]
  have hreset0 : RA ws (pReset exec) 0 = g 0 + e 0 := by
    rw [RA_reset_partition ws exec 0]; simp only [hg, he]; abel
  rw [hRPg, hRPa, hreset0, show (∑' n, g n) = g 0 + ∑' n, g (n + 1) from
      tsum_eq_zero_add' ENNReal.summable]
  calc g 0 + ∑' n, g (n + 1) ≤ g 0 + ((∑' n, a n) + e 0) := by gcongr
    _ = (∑' n, a n) + (g 0 + e 0) := by abel

/-- **Shared-with-departures arrivals** at `exec`: arrival config (nonempty segment) with an
active inner draw. The common part of the departure and arrival sums. -/
private def pAsome (exec : AlterSeq State Label) (c : Config sys) : Prop :=
  c.concat = exec ∧ c.e'.trans ≠ Seq.nil ∧ c.t ≠ none

/-- **Arrivals without a pending draw** at `exec`: arrival config with halted inner loop. -/
private def pAnoneFull (exec : AlterSeq State Label) (c : Config sys) : Prop :=
  c.concat = exec ∧ c.e'.trans ≠ Seq.nil ∧ c.t = none

open Classical in
/-- The arrival reach is the `RP` mass of the arrival predicate (off the root). -/
private theorem reachArr_eq_RP (ws : Scheduler sys^w) (exec : AlterSeq State Label)
    (hne : exec ≠ ⟨sys.init, Seq.nil⟩) :
    reachArr ws exec = RP ws (fun c => c.concat = exec ∧ c.e'.trans ≠ Seq.nil) := by
  rw [reachArr, if_neg hne, RP]
  exact tsum_subtype_ite (P := fun c => c.concat = exec ∧ c.e'.trans ≠ Seq.nil) (reachProb ws)

open Classical in
/-- `reachDep` as a guarded `tsum` over all configurations. -/
private theorem reachDep_subtype (ws : Scheduler sys^w) (exec : AlterSeq State Label)
    (p : Label × PMF State) :
    reachDep ws exec p.1 p.2
      = ∑' c : Config sys, if c.concat = exec ∧ c.t = some p then reachProb ws c else 0 :=
  (tsum_subtype_ite (P := fun c => c.concat = exec ∧ c.t = some (p.1, p.2)) (reachProb ws)).trans
    (tsum_congr (fun c => by congr 1))

open Classical in
/-- The total departure reach is the `RP` mass of the departure predicate. -/
private theorem reachDep_sum_eq_RP (ws : Scheduler sys^w) (exec : AlterSeq State Label) :
    (∑' p : Label × PMF State, reachDep ws exec p.1 p.2)
      = RP ws (fun c => c.concat = exec ∧ c.t ≠ none) := by
  rw [tsum_congr (fun p => reachDep_subtype ws exec p), ENNReal.tsum_comm, RP]
  refine tsum_congr (fun c => ?_)
  rw [tsum_ite_and_some (c.concat = exec) c.t]; congr 1

omit [Silent Label] in
/-- A configuration whose trajectory is the root has an empty current segment. -/
private theorem concat_root_e'_nil {c : Config sys} (h : c.concat = ⟨sys.init, Seq.nil⟩) :
    c.e'.trans = Seq.nil :=
  (append_eq_nil (congrArg AlterSeq.trans h)).2

open Classical in
/-- The start distribution has total mass `1`. -/
private theorem reachAfter_zero_total (ws : Scheduler sys^w) :
    (∑' c : Config sys, reachAfter ws 0 c) = 1 := by
  have hsupp : Function.support (reachAfter ws 0)
      ⊆ {c : Config sys | c.we = ⟨sys.init, Seq.nil⟩ ∧ c.e'.trans = Seq.nil} := by
    intro c hc
    have hcne := Function.mem_support.mp hc
    simp only [reachAfter] at hcne
    obtain ⟨hwe, _, he', _, _⟩ := of_ite_ne_zero hcne
    exact ⟨hwe, congrArg AlterSeq.trans he'⟩
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  refine Eq.trans (tsum_congr fun c => ?_) (base_sum ws)
  exact (reachProb_eq_reachAfter_zero ws c.1 (by rw [c.2.1]) c.2.2).symm

open Classical in
/-- Off the root, no start configuration is a reset configuration at `exec`. -/
private theorem RA_reset_zero_of_ne_root (ws : Scheduler sys^w) (exec : AlterSeq State Label)
    (hroot : exec ≠ ⟨sys.init, Seq.nil⟩) : RA ws (pReset exec) 0 = 0 := by
  simp only [RA]
  refine ENNReal.tsum_eq_zero.mpr (fun c => ?_)
  by_cases hp : pReset exec c
  · rw [if_pos hp]
    by_contra hne
    simp only [reachAfter] at hne
    obtain ⟨_, he, he', _, _⟩ := of_ite_ne_zero hne
    apply hroot
    rw [← hp.1]
    simp only [Config.concat, he, he', Stream'.Seq.nil_append]
  · rw [if_neg hp]

open Classical in
/-- **KEY FLOW INEQUALITY.** The total departure mass at a concrete trajectory `exec` is at most
its arrival mass: `∑ₚ reachDep exec p ≤ reachArr exec`. Equivalently, every run that departs the
prefix `exec` first arrives at it. Stated uniformly in `exec` so the `reachArr exec = 0` case
forces the LHS to `0`, which makes the `0/0` posterior in `expandMass` well-defined. -/
private theorem reachDep_sum_le (ws : Scheduler sys^w) (exec : AlterSeq State Label) :
    (∑' p : Label × PMF State, reachDep ws exec p.1 p.2) ≤ reachArr ws exec := by
  rw [reachDep_sum_eq_RP ws exec]
  have hD : RP ws (fun c => c.concat = exec ∧ c.t ≠ none)
      = RP ws (pAsome exec) + RP ws (pDfresh exec) := by
    rw [RP_split ws (fun c => c.concat = exec ∧ c.t ≠ none) (fun c => c.e'.trans ≠ Seq.nil)]
    congr 1
    · exact RP_congr ws (fun c => by unfold pAsome; tauto)
    · exact RP_congr ws (fun c => by unfold pDfresh; tauto)
  by_cases hroot : exec = ⟨sys.init, Seq.nil⟩
  · rw [reachArr, if_pos hroot, hD]
    have hAsome0 : RP ws (pAsome exec) = 0 :=
      RP_eq_zero ws (fun c hc => absurd (concat_root_e'_nil (hroot ▸ hc.1)) hc.2.1)
    have hAnone0 : RP ws (pAnone exec) = 0 :=
      RP_eq_zero ws (fun c hc => absurd (concat_root_e'_nil (hroot ▸ hc.1)) hc.2.2.2)
    rw [hAsome0, zero_add]
    calc RP ws (pDfresh exec)
        ≤ RP ws (pDfresh exec) + RP ws (pH exec) := le_self_add
      _ ≤ RP ws (pAnone exec) + RA ws (pReset exec) 0 := tele ws exec
      _ = RA ws (pReset exec) 0 := by rw [hAnone0, zero_add]
      _ ≤ ∑' c, reachAfter ws 0 c := by
          simp only [RA]; refine ENNReal.tsum_le_tsum (fun c => ?_)
          by_cases hp : pReset exec c
          · rw [if_pos hp]
          · rw [if_neg hp]; positivity
      _ = 1 := reachAfter_zero_total ws
  · rw [reachArr_eq_RP ws exec hroot, hD]
    have hA : RP ws (fun c => c.concat = exec ∧ c.e'.trans ≠ Seq.nil)
        = RP ws (pAsome exec) + RP ws (pAnoneFull exec) := by
      rw [RP_split ws (fun c => c.concat = exec ∧ c.e'.trans ≠ Seq.nil) (fun c => c.t ≠ none)]
      congr 1
      · exact RP_congr ws (fun c => by unfold pAsome; tauto)
      · exact RP_congr ws (fun c => by unfold pAnoneFull; tauto)
    rw [hA]
    have hbound : RP ws (pDfresh exec) ≤ RP ws (pAnone exec) := by
      calc RP ws (pDfresh exec)
          ≤ RP ws (pDfresh exec) + RP ws (pH exec) := le_self_add
        _ ≤ RP ws (pAnone exec) + RA ws (pReset exec) 0 := tele ws exec
        _ = RP ws (pAnone exec) := by rw [RA_reset_zero_of_ne_root ws exec hroot, add_zero]
    have hmono : RP ws (pAnone exec) ≤ RP ws (pAnoneFull exec) :=
      RP_mono ws (fun c hc => ⟨hc.1, hc.2.2.2, hc.2.1⟩)
    gcongr
    exact hbound.trans hmono

/-- `expandMass ws exec` is a probability distribution (normalization obligation:
the proper-step masses sum to `≤ 1`, since departures are a subset of arrivals, so
the remainder given to `⊥` is well-defined and the total is `1`). -/
theorem expandMass_hasSum (ws : Scheduler sys^w) (exec : AlterSeq State Label) :
    HasSum (expandMass ws exec) 1 := by
  rw [ENNReal.summable.hasSum_iff, tsum_option_eq (expandMass ws exec)]
  have hsome : ∀ p : Label × PMF State,
      expandMass ws exec (some p) = reachDep ws exec p.1 p.2 / reachArr ws exec := by
    rintro ⟨l, μ⟩; rfl
  have hnone : expandMass ws exec none
      = 1 - ∑' p : Label × PMF State, reachDep ws exec p.1 p.2 / reachArr ws exec := rfl
  rw [tsum_congr hsome, hnone]
  apply tsub_add_cancel_of_le
  rw [show (∑' p : Label × PMF State, reachDep ws exec p.1 p.2 / reachArr ws exec)
        = (∑' p : Label × PMF State, reachDep ws exec p.1 p.2) / reachArr ws exec from by
      simp_rw [div_eq_mul_inv]; rw [ENNReal.tsum_mul_right]]
  exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact reachDep_sum_le ws exec)

/-- **The concrete scheduler of the unfolding algorithm.** Maps a concrete history
`exec` to the posterior over its next inner draw: `reachDep / reachArr` on each
proper step, the remainder on `⊥`. (Validity obligation: any emitted `some (l, μ)`
comes from a departure configuration whose `t` was drawn by the witness scheduler,
so `sys.step (last exec) l μ` holds.) -/
noncomputable def expandSched (ws : Scheduler sys^w) : Scheduler sys where
  next exec := ⟨expandMass ws exec, expandMass_hasSum ws exec⟩
  valid e n s hterm hstate l μ hmem := by
    rw [PMF.mem_support_iff] at hmem
    change expandMass ws e (some (l, μ)) ≠ 0 at hmem
    rw [expandMass] at hmem
    have hdep : reachDep ws e l μ ≠ 0 := by
      intro h0; rw [h0, ENNReal.zero_div] at hmem; exact hmem rfl
    rw [reachDep] at hdep
    obtain ⟨c, hc⟩ : ∃ c : {c : Config sys // c.concat = e ∧ c.t = some (l, μ)},
        reachProb ws c.1 ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hdep (ENNReal.tsum_eq_zero.mpr hcon)
    obtain ⟨hconcat, hct⟩ := c.2
    have hmem' := reachProb_t_mem ws c.1 (l, μ) hc hct
    obtain ⟨hEfin, hfin', hinit', -⟩ := reachProb_inv ws c.1 hc
    have hstep' : sys.step (lastOf c.1.e') l μ :=
      c.1.s.valid c.1.e' (Nat.find hfin') (lastOf c.1.e') (Nat.find_spec hfin')
        (by rw [AlterSeq.stateAt_find_eq_endState c.1.e' hfin', lastOf_eq_endState c.1.e' hfin'])
        l μ hmem'
    have hlast : lastOf e = lastOf c.1.e' := by
      rw [← congrArg lastOf hconcat]
      exact lastOf_append_eq c.1.e c.1.e' hEfin hfin' hinit'
    rw [← lastOf_of_stateAt hterm hstate, hlast]; exact hstep'

/-! ### The arrival inner-recursion and the concrete-side fidelity

`reachArr_step` is the concrete-side analogue of `reachProb_we_step`: it expresses the arrival
mass at a one-transition-longer trajectory as the departure mass mixed against the drawn `μ`.
`probOf_eq_reachArr` then assembles, by cons-end induction, the fidelity of the unfolding
scheduler `expandSched ws` against `reachArr`. -/

omit [Silent Label] in
/-- If `s` terminates and `s.append t` terminates, then so does the suffix `t`. -/
private theorem terminates_suffix {α : Type} {s t : Seq α}
    (hs : s.Terminates) (h : (s.append t).Terminates) : t.Terminates := by
  refine ⟨Nat.find h, ?_⟩
  have happ : (s.append t).TerminatedAt (Nat.find hs + Nat.find h) :=
    Stream'.Seq.terminated_stable _ (Nat.le_add_left (Nat.find h) (Nat.find hs)) (Nat.find_spec h)
  have hget := Stream'.Seq.get?_append_find hs t (Nat.find h)
  change t.get? (Nat.find h) = none
  rw [← hget]; exact happ

open Classical in
/-- The committed concrete execution always starts at `sys.init`. (`e` is `⟨init, nil⟩` at
the start and only ever grows by appending / resetting to `eN = ⟨e.init, …⟩`, never changing
its `init`.) -/
private theorem reachAfter_e_init (ws : Scheduler sys^w) :
    ∀ (n : ℕ) (c : Config sys), reachAfter ws n c ≠ 0 → c.e.init = sys.init := by
  intro n
  induction n with
  | zero =>
    intro c hreach
    by_cases hcond : (c.we = (⟨sys.init, Seq.nil⟩ : AlterSeq State Label) ∧
        c.e = ⟨sys.init, Seq.nil⟩ ∧ c.e' = ⟨sys.init, Seq.nil⟩ ∧
        (∀ p, c.wt = some p → c.s = schedOf sys sys.init p.1 p.2) ∧
        (c.wt = none → c.s = Scheduler.halt sys))
    · rw [hcond.2.1]
    · simp only [reachAfter] at hreach; rw [if_neg hcond] at hreach; exact absurd rfl hreach
  | succ n ih =>
    intro c hreach
    rw [reachAfter] at hreach
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, reachAfter ws n c₀ * step ws c₀ c ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hreach (ENNReal.tsum_eq_zero.mpr hcon)
    rw [mul_ne_zero_iff] at hc₀
    obtain ⟨hreach₀, hstep⟩ := hc₀
    have hinit₀ := ih c₀ hreach₀
    obtain ⟨we₀, e₀, wt₀, s₀, e'₀, t₀⟩ := c₀
    cases wt₀ with
    | none => simp only [step] at hstep; exact absurd rfl hstep
    | some wtp =>
      obtain ⟨lw, μw⟩ := wtp
      cases t₀ with
      | none =>
        simp only [step] at hstep
        rw [(of_ite_ne_zero hstep).1]; exact hinit₀
      | some tp =>
        obtain ⟨l', μ'⟩ := tp
        simp only [step] at hstep
        rw [(of_ite_ne_zero hstep).2.1]; exact hinit₀

/-- The committed concrete execution of any reachable configuration starts at `sys.init`. -/
private theorem reachProb_e_init (ws : Scheduler sys^w) (c : Config sys)
    (h : reachProb ws c ≠ 0) : c.e.init = sys.init := by
  rw [reachProb] at h
  obtain ⟨n, hn⟩ : ∃ n, reachAfter ws n c ≠ 0 := by
    by_contra hcon; push Not at hcon; exact h (ENNReal.tsum_eq_zero.mpr hcon)
  exact reachAfter_e_init ws n c hn

/-- A reachable configuration with a pending inner draw (`c.t = some p`) has an active weak
step (`∃ q, c.wt = some q`). -/
private theorem reachProb_t_wt (ws : Scheduler sys^w) (c : Config sys)
    (p : Label × PMF State) (h : reachProb ws c ≠ 0) (ht : c.t = some p) :
    ∃ q, c.wt = some q := by
  rw [reachProb] at h
  obtain ⟨n, hn⟩ : ∃ n, reachAfter ws n c ≠ 0 := by
    by_contra hcon; push Not at hcon; exact h (ENNReal.tsum_eq_zero.mpr hcon)
  exact reachAfter_t_wt ws n c p hn ht

/-- A reachable configuration has a terminating full concrete trajectory `c.concat`. -/
private theorem reachProb_concat_terminates (ws : Scheduler sys^w) (c : Config sys)
    (h : reachProb ws c ≠ 0) : c.concat.trans.Terminates := by
  obtain ⟨hEfin, he'fin, -, -⟩ := reachProb_inv ws c h
  change (c.e.trans.append c.e'.trans).Terminates
  exact ⟨_, Stream'.Seq.terminatedAt_append_find hEfin (Nat.find_spec he'fin)⟩

open Classical in
/-- **Arrival-step collapse (concrete-side analogue of `entryStep_collapse`).** Summing the `step`
weight from `c₀` into the *arrival* configurations at the one-transition-longer trajectory
`exec ⌢ (l, s')` collapses, per drawn `μ`, to `μ s'` exactly when `c₀` is a *departure* at
`exec` with inner draw `t = some (l, μ)` and an active weak step; `0` otherwise. The arrivals are
the INNER children of `c₀`, whose only free choice is the next inner draw (which PMF-normalises). -/
private theorem arrivalStep_collapse (ws : Scheduler sys^w) (exec : AlterSeq State Label)
    (hexec : exec.trans.Terminates) (l : Label) (s' : State) (c₀ : Config sys) :
    (∑' c : {c : Config sys //
        c.concat = ⟨exec.init, exec.trans.append (Seq.cons (l, s') Seq.nil)⟩ ∧
          c.e'.trans ≠ Seq.nil}, step ws c₀ c.1)
      = ∑' μ : PMF State,
          if (∃ q, c₀.wt = some q) ∧ c₀.t = some (l, μ) ∧ c₀.concat = exec then μ s' else 0 := by
  set child : AlterSeq State Label :=
    ⟨exec.init, exec.trans.append (Seq.cons (l, s') Seq.nil)⟩ with hchild
  obtain ⟨we₀, e₀, wt₀, s₀, e'₀, t₀⟩ := c₀
  cases wt₀ with
  | none =>
    have hL : (∑' c : {c : Config sys // c.concat = child ∧ c.e'.trans ≠ Seq.nil},
        step ws ⟨we₀, e₀, none, s₀, e'₀, t₀⟩ c.1) = 0 :=
      ENNReal.tsum_eq_zero.mpr (fun c => by simp only [step])
    rw [hL, eq_comm]
    exact ENNReal.tsum_eq_zero.mpr (fun μ => if_neg (by rintro ⟨⟨q, hq⟩, -, -⟩; simp at hq))
  | some wtp =>
    obtain ⟨lw, μw⟩ := wtp
    cases t₀ with
    | none =>
      have hL : (∑' c : {c : Config sys // c.concat = child ∧ c.e'.trans ≠ Seq.nil},
          step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩ c.1) = 0 := by
        refine ENNReal.tsum_eq_zero.mpr (fun c => ?_)
        simp only [step]
        rw [if_neg]
        rintro ⟨-, -, he', -, -⟩
        exact c.2.2 (by rw [he'])
      rw [hL, eq_comm]
      exact ENNReal.tsum_eq_zero.mpr (fun μ => if_neg (by rintro ⟨-, ht, -⟩; simp at ht))
    | some tp =>
      obtain ⟨l', μ'⟩ := tp
      have hchild_term : (exec.trans.append (Seq.cons (l, s') Seq.nil)).Terminates :=
        ⟨_, Stream'.Seq.terminatedAt_append_find hexec
          (show (Seq.cons (l, s') Seq.nil).TerminatedAt 1 from rfl)⟩
      -- Canonical form of any INNER arrival target reached from this source.
      have hcanon : ∀ c : Config sys,
          step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, some (l', μ')⟩ c ≠ 0 → c.concat = child →
          l' = l ∧ (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label) = exec ∧
            c = ⟨we₀, e₀, some (lw, μw), s₀,
              ⟨e'₀.init, e'₀.trans.append (Seq.cons (l', s') Seq.nil)⟩, c.t⟩ := by
        intro c hstep hcc
        simp only [step] at hstep
        obtain ⟨hwe, he, hcwt, hcs, he'i, he't⟩ := of_ite_ne_zero hstep
        have hcc2 : e₀.trans.append c.e'.trans = exec.trans.append (Seq.cons (l, s') Seq.nil) := by
          have h := congrArg AlterSeq.trans hcc
          rw [hchild] at h
          change c.e.trans.append c.e'.trans = exec.trans.append (Seq.cons (l, s') Seq.nil) at h
          rw [he] at h; exact h
        rw [he't, ← Stream'.Seq.append_assoc] at hcc2
        have happ_term : (e₀.trans.append e'₀.trans).Terminates :=
          terminates_of_append_terminates (s := e₀.trans.append e'₀.trans)
            (s' := Seq.cons (l', lastOf c.e') Seq.nil) (by rw [hcc2]; exact hchild_term)
        have hpair : (l', lastOf c.e') = (l, s') :=
          Stream'.Seq.append_singleton_inj_right _ _ happ_term hexec _ _ hcc2
        have hAeq : e₀.trans.append e'₀.trans = exec.trans :=
          Stream'.Seq.append_singleton_inj_left _ _ happ_term hexec _ _ hcc2
        have hlast : lastOf c.e' = s' := congrArg Prod.snd hpair
        have hinit : e₀.init = exec.init := by
          have h := congrArg AlterSeq.init hcc
          rw [hchild] at h
          change c.e.init = exec.init at h
          rw [he] at h; exact h
        refine ⟨congrArg Prod.fst hpair, by rw [hinit, hAeq], ?_⟩
        have hce' : c.e' = (⟨e'₀.init, e'₀.trans.append (Seq.cons (l', s') Seq.nil)⟩
            : AlterSeq State Label) := by
          calc c.e' = ⟨c.e'.init, c.e'.trans⟩ := rfl
            _ = ⟨e'₀.init, e'₀.trans.append (Seq.cons (l', s') Seq.nil)⟩ := by
                rw [he'i, he't, hlast]
        calc c = (⟨c.we, c.e, c.wt, c.s, c.e', c.t⟩ : Config sys) := rfl
          _ = ⟨we₀, e₀, some (lw, μw), s₀,
              ⟨e'₀.init, e'₀.trans.append (Seq.cons (l', s') Seq.nil)⟩, c.t⟩ := by
                rw [hwe, he, hcwt, hcs, hce']
      by_cases hlc : l' = l ∧
          (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label) = exec
      · -- **Value `μ' s'`.**
        obtain ⟨hll, heCexec⟩ := hlc
        have htr : e₀.trans.append e'₀.trans = exec.trans := congrArg AlterSeq.trans heCexec
        have hin : e₀.init = exec.init := by
          have h := congrArg AlterSeq.init heCexec; exact h
        have happ : (e₀.trans.append e'₀.trans).Terminates := by rw [htr]; exact hexec
        have he'₀fin : e'₀.trans.Terminates :=
          terminates_suffix (terminates_of_append_terminates happ) happ
        have hlast' : lastOf (⟨e'₀.init, e'₀.trans.append (Seq.cons (l', s') Seq.nil)⟩
            : AlterSeq State Label) = s' :=
          lastOf_append_singleton ⟨e'₀.init, e'₀.trans⟩ he'₀fin l' s'
        have harr : ∀ t : Option (Label × PMF State),
            (⟨we₀, e₀, some (lw, μw), s₀,
                ⟨e'₀.init, e'₀.trans.append (Seq.cons (l', s') Seq.nil)⟩, t⟩ : Config sys).concat
              = child ∧
            (⟨we₀, e₀, some (lw, μw), s₀,
                ⟨e'₀.init, e'₀.trans.append (Seq.cons (l', s') Seq.nil)⟩, t⟩
                : Config sys).e'.trans ≠ Seq.nil := by
          intro t
          refine ⟨?_, append_cons_ne_nil _ _ _⟩
          change (⟨e₀.init, e₀.trans.append (e'₀.trans.append (Seq.cons (l', s') Seq.nil))⟩
              : AlterSeq State Label) = child
          rw [hchild, ← Stream'.Seq.append_assoc, htr, hll, hin]
        have hreindex : (∑' c : {c : Config sys // c.concat = child ∧ c.e'.trans ≠ Seq.nil},
            step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, some (l', μ')⟩ c.1)
            = ∑' t : Option (Label × PMF State),
                step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, some (l', μ')⟩
                  ⟨we₀, e₀, some (lw, μw), s₀,
                    ⟨e'₀.init, e'₀.trans.append (Seq.cons (l', s') Seq.nil)⟩, t⟩ :=
          tsum_eq_tsum_of_ne_zero_bij
            (i := fun x => ⟨⟨we₀, e₀, some (lw, μw), s₀,
                ⟨e'₀.init, e'₀.trans.append (Seq.cons (l', s') Seq.nil)⟩, x.1⟩, harr x.1⟩)
            (by
              rintro ⟨ta, hta⟩ ⟨tb, htb⟩ hab
              exact Subtype.ext (congrArg Config.t (congrArg Subtype.val hab)))
            (by
              intro c hc
              have hstep : step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, some (l', μ')⟩ c.1 ≠ 0 := hc
              obtain ⟨-, -, hceq⟩ := hcanon c.1 hstep c.2.1
              refine ⟨⟨c.1.t, ?_⟩, Subtype.ext hceq.symm⟩
              change step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, some (l', μ')⟩
                ⟨we₀, e₀, some (lw, μw), s₀,
                  ⟨e'₀.init, e'₀.trans.append (Seq.cons (l', s') Seq.nil)⟩, c.1.t⟩ ≠ 0
              rw [← hceq]; exact hstep)
            (by intro x; rfl)
        have hval : ∀ t : Option (Label × PMF State),
            step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, some (l', μ')⟩
              ⟨we₀, e₀, some (lw, μw), s₀,
                ⟨e'₀.init, e'₀.trans.append (Seq.cons (l', s') Seq.nil)⟩, t⟩
            = μ' s' * s₀.next ⟨e'₀.init, e'₀.trans.append (Seq.cons (l', s') Seq.nil)⟩ t := by
          intro t
          simp only [step]
          rw [if_pos ⟨trivial, trivial, trivial, trivial, trivial, by rw [hlast']⟩, hlast']
        have hL : (∑' c : {c : Config sys // c.concat = child ∧ c.e'.trans ≠ Seq.nil},
            step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, some (l', μ')⟩ c.1) = μ' s' := by
          rw [hreindex, tsum_congr hval, ENNReal.tsum_mul_left,
            (s₀.next ⟨e'₀.init, e'₀.trans.append (Seq.cons (l', s') Seq.nil)⟩).tsum_coe, mul_one]
        rw [hL, eq_comm]
        rw [tsum_eq_single μ' (fun μ hμ => if_neg (by
          rintro ⟨-, hsome, -⟩
          exact hμ (congrArg Prod.snd (Option.some.inj hsome)).symm))]
        have hguard : (∃ q, (⟨we₀, e₀, some (lw, μw), s₀, e'₀, some (l', μ')⟩ : Config sys).wt
              = some q) ∧
            (⟨we₀, e₀, some (lw, μw), s₀, e'₀, some (l', μ')⟩ : Config sys).t = some (l, μ') ∧
            (⟨we₀, e₀, some (lw, μw), s₀, e'₀, some (l', μ')⟩ : Config sys).concat = exec :=
          ⟨⟨(lw, μw), rfl⟩, by
              change (some (l', μ') : Option (Label × PMF State)) = some (l, μ'); rw [hll], heCexec⟩
        rw [if_pos hguard]
      · -- **Value `0`.**
        have hL : (∑' c : {c : Config sys // c.concat = child ∧ c.e'.trans ≠ Seq.nil},
            step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, some (l', μ')⟩ c.1) = 0 := by
          refine ENNReal.tsum_eq_zero.mpr (fun c => ?_)
          by_contra hne
          obtain ⟨hll, heC, -⟩ := hcanon c.1 hne c.2.1
          exact hlc ⟨hll, heC⟩
        rw [hL, eq_comm]
        refine ENNReal.tsum_eq_zero.mpr (fun μ => if_neg ?_)
        rintro ⟨-, hsome, heC⟩
        exact hlc ⟨congrArg Prod.fst (Option.some.inj hsome), heC⟩

open Classical in
/-- **Arrival inner-recursion.** The arrival mass at the one-transition-longer trajectory
`exec ⌢ (l, s')` equals the departure mass at `exec` mixed against the drawn end-state
distribution `μ`: `reachArr (exec ⌢ (l, s')) = ∑' μ, reachDep exec l μ · μ s'`. Each run that
arrives at `exec ⌢ (l, s')` first departs `exec` via an inner draw `(l, μ)`, then samples
`s' ∼ μ`. -/
theorem reachArr_step (ws : Scheduler sys^w) (exec : AlterSeq State Label) (l : Label)
    (s' : State) :
    reachArr ws ⟨exec.init, exec.trans.append (Seq.cons (l, s') Seq.nil)⟩
      = ∑' μ : PMF State, reachDep ws exec l μ * μ s' := by
  set child : AlterSeq State Label :=
    ⟨exec.init, exec.trans.append (Seq.cons (l, s') Seq.nil)⟩ with hchild
  have hchild_ne : child ≠ ⟨sys.init, Seq.nil⟩ := by
    rw [hchild]
    intro h
    exact append_cons_ne_nil exec.trans (l, s') Seq.nil (congrArg AlterSeq.trans h)
  by_cases hexec : exec.trans.Terminates
  · -- **Terminating case** — the genuine recursion.
    rw [reachArr, if_neg hchild_ne]
    -- Sub-step 1: `reachProb_fixpoint` + Tonelli over the arrivals.
    have step1 : (∑' c : {c : Config sys // c.concat = child ∧ c.e'.trans ≠ Seq.nil},
          reachProb ws c.1)
        = ∑' c₀ : Config sys, reachProb ws c₀ * (∑' c : {c : Config sys //
            c.concat = child ∧ c.e'.trans ≠ Seq.nil}, step ws c₀ c.1) := by
      have hrw : ∀ c : {c : Config sys // c.concat = child ∧ c.e'.trans ≠ Seq.nil},
          reachProb ws c.1 = ∑' c₀, reachProb ws c₀ * step ws c₀ c.1 := by
        intro c
        rw [reachProb_fixpoint]
        have h0 : reachAfter ws 0 c.1 = 0 := by
          rw [reachAfter, if_neg]
          rintro ⟨-, -, he', -, -⟩
          exact c.2.2 (by rw [he'])
        rw [h0, zero_add]
      rw [tsum_congr hrw, ENNReal.tsum_comm]
      exact tsum_congr (fun c₀ => ENNReal.tsum_mul_left)
    -- Sub-step 2: collapse + reindex onto the departures at `exec`.
    have hμ : ∀ μ : PMF State,
        (∑' c₀ : Config sys, reachProb ws c₀ *
            if (∃ q, c₀.wt = some q) ∧ c₀.t = some (l, μ) ∧ c₀.concat = exec then μ s' else 0)
          = reachDep ws exec l μ * μ s' := by
      intro μ
      rw [reachDep_subtype ws exec (l, μ), ← ENNReal.tsum_mul_right]
      refine tsum_congr (fun c₀ => ?_)
      by_cases hH : c₀.concat = exec ∧ c₀.t = some (l, μ)
      · rw [if_pos hH]
        by_cases hq : ∃ q, c₀.wt = some q
        · rw [if_pos ⟨hq, hH.2, hH.1⟩]
        · have hrp : reachProb ws c₀ = 0 := by
            by_contra hne; exact hq (reachProb_t_wt ws c₀ (l, μ) hne hH.2)
          rw [if_neg (fun hG => hq hG.1), mul_zero, hrp, zero_mul]
      · rw [if_neg hH, zero_mul, if_neg (fun hG => hH ⟨hG.2.2, hG.2.1⟩), mul_zero]
    rw [step1,
      tsum_congr (fun c₀ => by
        rw [arrivalStep_collapse ws exec hexec l s' c₀, ← ENNReal.tsum_mul_left]),
      ENNReal.tsum_comm]
    exact tsum_congr hμ
  · -- **Non-terminating case** — both sides vanish (no reachable config has trajectory `exec`).
    have hLHS : reachArr ws child = 0 := by
      rw [reachArr, if_neg hchild_ne]
      refine ENNReal.tsum_eq_zero.mpr (fun c => ?_)
      by_contra hne
      apply hexec
      have hct := reachProb_concat_terminates ws c.1 hne
      rw [c.2.1, hchild] at hct
      exact terminates_of_append_terminates hct
    have hRHS : (∑' μ : PMF State, reachDep ws exec l μ * μ s') = 0 := by
      refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
      have hd : reachDep ws exec l μ = 0 := by
        rw [reachDep]
        refine ENNReal.tsum_eq_zero.mpr (fun c => ?_)
        by_contra hne
        apply hexec
        have hct := reachProb_concat_terminates ws c.1 hne
        rw [c.2.1] at hct
        exact hct
      rw [hd, zero_mul]
    rw [hLHS, hRHS]

open Classical in
/-- The list-indexed core of `probOf_eq_reachArr`: the claim for trajectories of the canonical
form `⟨sys.init, ofList L⟩`. Proved by reverse (cons-end) induction on `L`. -/
private theorem reachArr_aux (ws : Scheduler sys^w) (L : List (Label × State)) :
    (⟨PMF.pure sys.init, expandSched ws⟩ : ProbabilisticExecution sys).probOf
        ⟨sys.init, Seq.ofList L⟩ (Stream'.Seq.terminates_ofList L)
      = reachArr ws ⟨sys.init, Seq.ofList L⟩ := by
  induction L using List.reverseRecOn with
  | nil =>
    have hLHS : (⟨PMF.pure sys.init, expandSched ws⟩ : ProbabilisticExecution sys).probOf
        ⟨sys.init, Seq.ofList ([] : List (Label × State))⟩
        (Stream'.Seq.terminates_ofList []) = 1 := by
      rw [ProbabilisticExecution.probOf_congr _ ⟨sys.init, Seq.ofList []⟩ ⟨sys.init, Seq.nil⟩
          (by rw [Stream'.Seq.ofList_nil]) (Stream'.Seq.terminates_ofList [])
          Stream'.Seq.terminates_nil,
        ProbabilisticExecution.probOf_nil]
      exact PMF.pure_apply_self sys.init
    rw [hLHS, show (Seq.ofList ([] : List (Label × State)) : Seq (Label × State)) = Seq.nil from
        Stream'.Seq.ofList_nil, reachArr, if_pos rfl]
  | append_singleton L' last ih =>
    obtain ⟨l, x⟩ := last
    have hofl : (Seq.ofList (L' ++ [(l, x)]) : Seq (Label × State))
        = (Seq.ofList L').append (Seq.cons (l, x) Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have hterm_app : ((Seq.ofList L').append (Seq.cons (l, x) Seq.nil)).Terminates := by
      rw [← hofl]; exact Stream'.Seq.terminates_ofList _
    have hnext : ∀ μ : PMF State,
        (⟨PMF.pure sys.init, expandSched ws⟩ : ProbabilisticExecution sys).scheduler.next
            ⟨sys.init, Seq.ofList L'⟩ (some (l, μ))
          = reachDep ws ⟨sys.init, Seq.ofList L'⟩ l μ / reachArr ws ⟨sys.init, Seq.ofList L'⟩ :=
      fun _ => rfl
    have hker : (⟨PMF.pure sys.init, expandSched ws⟩ : ProbabilisticExecution sys).kernel
          ⟨sys.init, Seq.ofList L'⟩ (l, x)
        = ∑' μ : PMF State,
            (reachDep ws ⟨sys.init, Seq.ofList L'⟩ l μ / reachArr ws ⟨sys.init, Seq.ofList L'⟩)
              * μ x := by
      rw [ProbabilisticExecution.kernel]
      exact tsum_congr (fun μ => by rw [hnext μ])
    -- Factorise the LHS by the cons-end recursion; rewrite the RHS by `reachArr_step`.
    rw [ProbabilisticExecution.probOf_congr _ ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩
        ⟨sys.init, (Seq.ofList L').append (Seq.cons (l, x) Seq.nil)⟩ (by rw [hofl])
        (Stream'.Seq.terminates_ofList _) hterm_app,
      ProbabilisticExecution.probOf_append_singleton _ sys.init (Seq.ofList L')
        (Stream'.Seq.terminates_ofList _) (l, x) hterm_app, ih, hker,
      show (⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ : AlterSeq State Label)
          = ⟨(⟨sys.init, Seq.ofList L'⟩ : AlterSeq State Label).init,
              (⟨sys.init, Seq.ofList L'⟩ : AlterSeq State Label).trans.append
                (Seq.cons (l, x) Seq.nil)⟩ from by rw [hofl],
      reachArr_step ws ⟨sys.init, Seq.ofList L'⟩ l x]
    by_cases hz : reachArr ws ⟨sys.init, Seq.ofList L'⟩ = 0
    · rw [hz, zero_mul, eq_comm]
      refine ENNReal.tsum_eq_zero.mpr (fun μ => ?_)
      have hd0 : reachDep ws ⟨sys.init, Seq.ofList L'⟩ l μ = 0 := by
        have hle := reachDep_sum_le ws ⟨sys.init, Seq.ofList L'⟩
        rw [hz, nonpos_iff_eq_zero] at hle
        exact ENNReal.tsum_eq_zero.mp hle (l, μ)
      rw [hd0, zero_mul]
    · have hle : reachArr ws ⟨sys.init, Seq.ofList L'⟩ ≤ 1 := by
        rw [← ih]
        calc (⟨PMF.pure sys.init, expandSched ws⟩ : ProbabilisticExecution sys).probOf
                ⟨sys.init, Seq.ofList L'⟩ (Stream'.Seq.terminates_ofList L')
            ≤ (⟨PMF.pure sys.init, expandSched ws⟩ : ProbabilisticExecution sys).init
                (⟨sys.init, Seq.ofList L'⟩ : AlterSeq State Label).init :=
              ProbabilisticExecution.probOf_le_init _ _ _
          _ = 1 := PMF.pure_apply_self sys.init
      have htop : reachArr ws ⟨sys.init, Seq.ofList L'⟩ ≠ ⊤ :=
        (hle.trans_lt ENNReal.one_lt_top).ne
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr (fun μ => ?_)
      rw [← mul_assoc, ENNReal.mul_div_cancel hz htop]

/-- **Concrete-side fidelity.** The probability that the unfolding scheduler `expandSched ws`
produces the finite trajectory `exec` equals its arrival reach `reachArr ws exec`. (The kernel of
`expandSched` at each prefix is the Bayesian posterior `reachDep / reachArr`, so the cylinder
probability telescopes into the arrival mass.) Proved by reduction to `reachArr_aux`. -/
theorem probOf_eq_reachArr (ws : Scheduler sys^w) (exec : AlterSeq State Label)
    (h : exec.trans.Terminates) :
    (⟨PMF.pure sys.init, expandSched ws⟩ : ProbabilisticExecution sys).probOf exec h
      = reachArr ws exec := by
  by_cases hinit : exec.init = sys.init
  · obtain ⟨ei, et⟩ := exec
    subst hinit
    set L := et.toList h with hLdef
    have hL : et = Seq.ofList L := (Stream'.Seq.ofList_toList et h).symm
    rw [ProbabilisticExecution.probOf_congr _ ⟨sys.init, et⟩ ⟨sys.init, Seq.ofList L⟩
        (by rw [hL]) h (Stream'.Seq.terminates_ofList L), reachArr_aux ws L, hL]
  · rw [ProbabilisticExecution.probOf_init_factor (expandSched ws) (PMF.pure sys.init) exec h,
      PMF.pure_apply_of_ne _ _ hinit, zero_mul, eq_comm,
      reachArr, if_neg (fun hr => hinit (by rw [hr]))]
    refine ENNReal.tsum_eq_zero.mpr (fun c => ?_)
    by_contra hne
    apply hinit
    have h1 := reachProb_e_init ws c.1 hne
    have h2 : c.1.e.init = exec.init := by
      have hh := congrArg AlterSeq.init c.2.1
      change c.1.e.init = exec.init at hh
      exact hh
    rw [h1] at h2
    exact h2.symm

end PLTS
