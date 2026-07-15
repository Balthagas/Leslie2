/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2Extra.Fairness.Model.ResolvedScheduler

/-!
# A finite-branching gap between resolved and plain fair trace distributions

This file formalizes the counterexample showing
`fairAchievableTraceDists CEfair ≠ fairAchievableTraceDistsPlain CEfair` for an image-finite
system — the resolved-history scheduler model is strictly more expressive than plain schedulers for
sure-fair trace distributions. Headline results: `CESys_imageFinite`, `peR_isFair`, `D_CE_mem_R`,
`D_CE_not_mem_plain`, `fairAchievableTraceDists_ne_plain`.
-/

namespace PLTS

open Stream'

/-! ### Finite-branching counterexample: `fairAchievableTraceDists ⊋ fairAchievableTraceDistsPlain`

The coincidence is **false even for image-finite systems**. A *resolved* scheduler achieves a
**sure**-fair trace distribution that no *plain* scheduler achieves, so the `⊆` inclusion fails
under `sys.ImageFinite`; only `⊇` (`fairAchievableTraceDistsPlain_subset`) holds.

**Gadget** (image-finite: two transitions per state, each of support size two). States `q_n`
(`n : ℕ`), `q'_n`, and a deadlock `b`; `q_0` initial. From `q_n`, two silent (`τ`) transitions,
both landing in `{q_{n+1}, q'_n}` — so a plain scheduler observes only "advanced" vs "exited",
never which transition produced it:
* fair   `μ_A = ½·δ_{q_{n+1}} + ½·δ_{q'_n}`  (exits w.p. ½ — marked fair),
* unfair `μ_B = ⅔·δ_{q_{n+1}} + ⅓·δ_{q'_n}`  (exits w.p. ⅓ — marked unfair).
From `q'_n` a single **external** transition labelled `n` leads to `b` (a fair deadlock).

**Resolved witness `σ_R`.** At `q_0` flip a coin (½ `μ_A`, ½ `μ_B`); thereafter, reading its own
`μ`-history, strictly **alternate** fair/unfair until it exits. Every never-exiting run alternates
⇒ infinitely many fair steps ⇒ fair; every exiting run halts at the fair deadlock `b`. So `σ_R` is
**sure-fair**, and its trace `[n]` (the exit index) has distribution `D` = a genuine ½/½ **mixture**
of the two starting parities' exit-index laws. Hence `D ∈ fairAchievableTraceDists F`.

**No fair plain scheduler achieves `D`.** After `k` non-exit steps the plain history is "advanced
`k` times", determined by `k` alone, so a plain scheduler emits `μ_A` w.p. `α_k`, `μ_B` w.p.
`1 − α_k` (it cannot halt at `q_k`, which is not a fair deadlock). Its per-step exit rate is
`ρ_k = ½·α_k + ⅓·(1 − α_k) ∈ [⅓, ½]`.
* *Sure-fairness forces `ρ_k = ½` infinitely often.* The all-`μ_B` run `q_0 → q_1 → q_2 → ⋯` is
  consistent whenever `α_k < 1` for every `k`, yet takes no fair step; excluding every
  eventually-all-unfair run needs `α_k = 1` (so `ρ_k = ½`) at infinitely many `k`.
* *`D` forces `ρ_k < ½` at every `k`.* The exit rates are pinned by `D` via
  `ρ_k = D(k) / P(survive to k)`, and for `σ_R` each is a posterior mixture with weight
  `p_k = P(started fair ∣ survived to k) ∈ (0, 1)`; both parities keep positive posterior, so
  `ρ_k ∈ (⅓, ½)` — **strictly** below `½` — for all `k`.
These are incompatible, so `D ∉ fairAchievableTraceDistsPlain F`.

**Remarks.**
* The coin flip is essential: under deterministic alternation `D`'s conditional rate is exactly `½`
  on even steps, where a plain scheduler *can* force fair; the mixture pushes the rate strictly
  below `½` everywhere, leaving no slot for the forced-fair `½`-rate steps.
* It is a **sure**-fairness phenomenon: `pe.average` is *a.s.*-fair and *does* achieve `D`. The
  obstruction is the support-level "kill the measure-zero all-unfair run", made `D`-visible because
  the two indistinguishable transitions differ in *weight* — hence in the branching rate into the
  label-emitting exit `q'_n`.
* So no fair de-resolution of `σ_R` exists: the resolved model is strictly more expressive for
  sure-fair trace distributions, even under image-finiteness.
-/

/-! ### A concrete finite-branching gadget for the counterexample

This section builds, in Lean, the image-finite gadget sketched in the comment above: states `q n`,
`q' n`, and a deadlock `bin`; from `q n` two silent (`τ`) transitions `μ_A` (fair, exits w.p. ½) and
`μ_B` (unfair, exits w.p. ⅓) both landing in `{q (n+1), q' n}`; from `q' n` a single external step
labelled `n` to `bin`. The resolved scheduler `sigmaR` coin-flips the first transition and then
strictly alternates fair/unfair by reading its own `μ`-history. This is the *foundation* of the
counterexample; fairness of `peR` and its trace distribution are treated in a later stage. -/

namespace FairCounterexample

-- `PMF.bernoulli` (and `PMF.bernoulli_apply`) are deprecated in favour of `bernoulliMeasure`, but
-- the latter is a `Measure`, not a `PMF`; the two-point `PMF`s here genuinely need the `PMF` form.
set_option linter.deprecated false

/-- Gadget states: the corridor states `q n`, the exit states `q' n`, and the deadlock `bin`. -/
inductive CEState | q (n : ℕ) | q' (n : ℕ) | bin
  deriving DecidableEq

/-- Gadget labels: `τ := none`, and the external label `n := some n`. -/
abbrev CELabel := Option ℕ

instance : Silent CELabel := ⟨none⟩

instance : Countable CEState := by
  apply Function.Injective.countable (f := fun s => match s with
    | CEState.q n => (Sum.inl n : ℕ ⊕ ℕ ⊕ Unit)
    | CEState.q' n => Sum.inr (Sum.inl n)
    | CEState.bin => Sum.inr (Sum.inr ()))
  intro a b h
  cases a <;> cases b <;> simp_all

/-- The **fair** transition from `q n`: a coin exiting to `q' n` w.p. ½, else advancing to
`q (n+1)`. -/
noncomputable def muA (n : ℕ) : PMF CEState :=
  (PMF.bernoulli (1 / 2) (by norm_num [div_le_one])).map
    (fun b => if b then CEState.q (n + 1) else CEState.q' n)

/-- The **unfair** transition from `q n`: exits to `q' n` w.p. ⅓, else advances to `q (n+1)`. -/
noncomputable def muB (n : ℕ) : PMF CEState :=
  (PMF.bernoulli (2 / 3) (by norm_num [div_le_one])).map
    (fun b => if b then CEState.q (n + 1) else CEState.q' n)

@[simp] theorem muA_q_succ (n : ℕ) : muA n (CEState.q (n + 1)) = 1 / 2 := by
  simp only [muA, PMF.map_apply, tsum_bool, Bool.false_eq_true, if_false, if_true,
    PMF.bernoulli_apply, cond_true, cond_false]
  simp

@[simp] theorem muA_q' (n : ℕ) : muA n (CEState.q' n) = 1 / 2 := by
  simp only [muA, PMF.map_apply, tsum_bool, Bool.false_eq_true, if_false, if_true,
    PMF.bernoulli_apply, cond_true, cond_false]
  simp

@[simp] theorem muB_q_succ (n : ℕ) : muB n (CEState.q (n + 1)) = 2 / 3 := by
  simp only [muB, PMF.map_apply, tsum_bool, Bool.false_eq_true, if_false, if_true,
    PMF.bernoulli_apply, cond_true, cond_false]
  simp

@[simp] theorem muB_q' (n : ℕ) : muB n (CEState.q' n) = 1 / 3 := by
  simp only [muB, PMF.map_apply, tsum_bool, Bool.false_eq_true, if_false, if_true,
    PMF.bernoulli_apply, cond_true, cond_false]
  rw [show (1 - 2 / 3 : NNReal) = 1 / 3 from by
    rw [← NNReal.coe_inj, NNReal.coe_sub (by norm_num [div_le_one])]; push_cast; norm_num]
  push_cast; norm_num

/-- The fair and unfair transitions differ: they have different exit probabilities. -/
theorem muA_ne_muB (n : ℕ) : muA n ≠ muB n := by
  intro h
  have hval := congrArg (fun μ => μ (CEState.q' n)) h
  simp only [muA_q', muB_q'] at hval
  rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at hval
  norm_num at hval

/-- `muA n` is supported on `{q (n+1), q' n}`. -/
theorem muA_support_subset (n : ℕ) :
    (muA n).support ⊆ {CEState.q (n + 1), CEState.q' n} := by
  intro s hs
  rw [muA, PMF.mem_support_map_iff] at hs
  obtain ⟨b, _, rfl⟩ := hs
  cases b <;> simp

/-- `muB n` is supported on `{q (n+1), q' n}`. -/
theorem muB_support_subset (n : ℕ) :
    (muB n).support ⊆ {CEState.q (n + 1), CEState.q' n} := by
  intro s hs
  rw [muB, PMF.mem_support_map_iff] at hs
  obtain ⟨b, _, rfl⟩ := hs
  cases b <;> simp

/-- The gadget's step relation: from `q n` the two silent transitions `μ_A`/`μ_B`; from `q' n` the
single external step labelled `n` to `bin`; `bin` is a deadlock. -/
def CEstep : CEState → CELabel → PMF CEState → Prop := fun s l μ =>
  match s with
  | CEState.q n  => l = Silent.τ ∧ (μ = muA n ∨ μ = muB n)
  | CEState.q' n => l = some n ∧ μ = PMF.pure CEState.bin
  | CEState.bin  => False

/-- The gadget system, started from `q 0`. -/
noncomputable def CESys : System CEState CELabel := ⟨CEState.q 0, CEstep⟩

/-- The fairness marking: `μ_A` is the fair transition from `q n`, and every external step (from
`q' n`) is fair; `μ_B` is unfair. -/
def CEfairMark : CEState → CELabel → PMF CEState → Prop := fun s l μ =>
  match s with
  | CEState.q n  => l = Silent.τ ∧ μ = muA n
  | CEState.q' n => l = some n ∧ μ = PMF.pure CEState.bin
  | CEState.bin  => False

/-- The fairness marking as a `Fairness CESys`: `μ_A` and all external steps are fair. -/
noncomputable def CEfair : Fairness CESys where
  fair := CEfairMark
  step_of_fair := by
    intro s l μ hf
    cases s with
    | q n => exact ⟨hf.1, Or.inl hf.2⟩
    | q' n => exact hf
    | bin => exact hf.elim
  fair_of_external := by
    intro s l μ hstep hext
    cases s with
    | q n => exact absurd hstep.1 hext
    | q' n => exact hstep
    | bin => exact hstep.elim

/-- **The gadget is image-finite.** Each state has finitely many outgoing transitions (two from
`q n`, one from `q' n`, none from `bin`), each with finite support (`μ_A`/`μ_B` land in two states,
`pure bin` in one). -/
theorem CESys_imageFinite : CESys.ImageFinite := by
  refine ⟨fun s => ?_, fun s l μ hstep => ?_⟩
  · cases s with
    | q n =>
      apply Set.Finite.subset (Set.toFinite
        ({((Silent.τ : CELabel), muA n), ((Silent.τ : CELabel), muB n)} :
          Set (CELabel × PMF CEState)))
      rintro ⟨l, μ⟩ hp
      change CEstep (CEState.q n) l μ at hp
      obtain ⟨rfl, h⟩ := hp
      rcases h with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (Set.mem_singleton_iff.mpr (by rw [h]))
    | q' n =>
      apply Set.Finite.subset (Set.finite_singleton ((some n : CELabel), PMF.pure CEState.bin))
      rintro ⟨l, μ⟩ hp
      change CEstep (CEState.q' n) l μ at hp
      obtain ⟨rfl, rfl⟩ := hp; rfl
    | bin =>
      apply Set.Finite.subset Set.finite_empty
      rintro ⟨l, μ⟩ hp
      change CEstep CEState.bin l μ at hp
      exact hp.elim
  · cases s with
    | q n =>
      obtain ⟨_, h⟩ := hstep
      rcases h with h | h
      · rw [h]; exact (Set.toFinite _).subset (muA_support_subset n)
      · rw [h]; exact (Set.toFinite _).subset (muB_support_subset n)
    | q' n =>
      obtain ⟨_, rfl⟩ := hstep; rw [PMF.support_pure]; exact Set.finite_singleton _
    | bin => exact hstep.elim

open Classical in
/-- **The resolved witness `σ_R`.** At `q 0` it flips a coin (½ `μ_A`, ½ `μ_B`); at `q n` (`n > 0`)
it reads the transition it just took (recorded at position `n-1` of its own `μ`-history) and plays
the *opposite* one — strictly alternating fair/unfair. From `q' n` it fires the external label `n`;
at `bin` it halts. -/
noncomputable def sigmaR : ResolvedScheduler CESys where
  next := fun r =>
    if h : r.trans.Terminates then
      match r.endState h with
      | CEState.q n =>
          if n = 0 then
            (PMF.bernoulli (1 / 2) (by norm_num [div_le_one])).map
              (fun b => some ((Silent.τ : CELabel), if b then muA 0 else muB 0))
          else
            let lastμ := (r.trans.get? (n - 1)).map (fun p => p.1.2)
            if lastμ = some (muA (n - 1)) then PMF.pure (some ((Silent.τ : CELabel), muB n))
            else PMF.pure (some ((Silent.τ : CELabel), muA n))
      | CEState.q' n => PMF.pure (some ((some n : CELabel), PMF.pure CEState.bin))
      | CEState.bin => PMF.pure none
    else PMF.pure none
  valid := by
    classical
    intro r n s hterm hstate l μ hsupp
    have h_term : r.trans.Terminates := ⟨n, hterm⟩
    have h_find_le : Nat.find h_term ≤ n := Nat.find_le hterm
    have h_n_le : n ≤ Nat.find h_term := by
      by_contra h_lt
      push Not at h_lt
      rcases n with _ | k
      · exact absurd h_lt (Nat.not_lt_zero _)
      · have hk_ge : Nat.find h_term ≤ k := Nat.lt_succ_iff.mp h_lt
        have h_term_k : r.trans.TerminatedAt k :=
          Stream'.Seq.terminated_stable r.trans hk_ge (Nat.find_spec h_term)
        have h_state_none : r.stateAt (k + 1) = none := by
          change (r.trans.get? k).map Prod.snd = none
          rw [show r.trans.get? k = none from h_term_k]; rfl
        rw [h_state_none] at hstate
        exact Option.some_ne_none s hstate.symm
    have h_n_eq : n = Nat.find h_term := le_antisymm h_n_le h_find_le
    have h_s_eq : s = r.endState h_term := by
      have h := AlterSeq.stateAt_find_eq_endState r h_term
      rw [← h_n_eq] at h; rw [h] at hstate
      exact (Option.some.inj hstate).symm
    subst h_s_eq
    change CESys.step (r.endState h_term) l μ
    rw [dif_pos h_term] at hsupp
    generalize hE : r.endState h_term = e at hsupp ⊢
    cases e with
    | q m =>
      dsimp only [] at hsupp
      by_cases hm : m = 0
      · subst hm
        rw [if_pos rfl, PMF.mem_support_map_iff] at hsupp
        obtain ⟨b, _, hb⟩ := hsupp
        cases b
        · simp only [Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb; exact ⟨rfl, Or.inr rfl⟩
        · simp only [if_true, Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb; exact ⟨rfl, Or.inl rfl⟩
      · rw [if_neg hm] at hsupp
        by_cases hlast : (r.trans.get? (m - 1)).map (fun p => p.1.2) = some (muA (m - 1))
        · rw [if_pos hlast, PMF.mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at hsupp
          obtain ⟨rfl, rfl⟩ := hsupp; exact ⟨rfl, Or.inr rfl⟩
        · rw [if_neg hlast, PMF.mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at hsupp
          obtain ⟨rfl, rfl⟩ := hsupp; exact ⟨rfl, Or.inl rfl⟩
    | q' m =>
      dsimp only [] at hsupp
      rw [PMF.mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at hsupp
      obtain ⟨rfl, rfl⟩ := hsupp
      exact ⟨rfl, rfl⟩
    | bin => simp at hsupp

/-- The resolved probabilistic execution driven by `sigmaR`, started from the Dirac initial
distribution `PMF.pure CESys.init = PMF.pure (q 0)` expected by `fairAchievableTraceDists`. -/
noncomputable def peR : ResolvedProbabilisticExecution CESys := ⟨PMF.pure CESys.init, sigmaR⟩

/-! ### Prefix (`take`) reading lemmas

The `inf_fair` argument reads `sigmaR` at the length-`n` prefix `r.take n` of an infinite run. Since
`(r.take n).trans = Seq.ofList (r.trans.take n)` is always a finite list, the prefix terminates at
`n` (for infinite `r`), its `endState` is `r.stateAt n`, and its recorded transitions below `n`
agree with `r`'s. -/

/-- `Seq.take n s` reads back `s.get?` below `n`. -/
private theorem seq_getElem?_take {α : Type} (s : Seq α) (n m : ℕ) (h : m < n) :
    (Seq.take n s)[m]? = s.get? m := by
  induction n generalizing s m with
  | zero => omega
  | succ k ih =>
    induction s using Stream'.Seq.recOn with
    | nil => simp [Stream'.Seq.take_nil, Stream'.Seq.get?_nil]
    | cons a t =>
      rw [Stream'.Seq.take_succ_cons]
      cases m with
      | zero => simp [Stream'.Seq.get?_cons_zero]
      | succ j =>
        rw [List.getElem?_cons_succ, Stream'.Seq.get?_cons_succ]
        exact ih t j (Nat.lt_of_succ_lt_succ h)

/-- The finite prefix `r.take n` records the same transitions as `r` below `n`. -/
private theorem take_trans_get? (r : ResolvedExec CEState CELabel) {n m : ℕ} (h : m < n) :
    (r.take n).trans.get? m = r.trans.get? m := by
  change (Seq.ofList (Seq.take n r.trans)).get? m = _
  rw [Stream'.Seq.ofList_get?, seq_getElem?_take r.trans n m h]

/-- For an infinite `r`, the length-`n` prefix terminates exactly at `n`. -/
private theorem take_terminatedAt (r : ResolvedExec CEState CELabel) (n : ℕ)
    (hinf : ¬ r.trans.Terminates) : (r.take n).trans.TerminatedAt n := by
  change (Seq.ofList (Seq.take n r.trans)).get? n = none
  rw [Stream'.Seq.ofList_get?]
  apply List.getElem?_eq_none
  have hlen : (Seq.take n r.trans).length = n :=
    Stream'.Seq.length_take_of_le_length (fun h => absurd h hinf)
  omega

/-- The length-`n` prefix always terminates (it is a finite list). -/
private theorem take_terminates (r : ResolvedExec CEState CELabel) (n : ℕ) :
    (r.take n).trans.Terminates :=
  Stream'.Seq.terminates_ofList _

/-- For an infinite `r`, the canonical terminating index of `r.take n` is `n`. -/
private theorem take_find (r : ResolvedExec CEState CELabel) (n : ℕ)
    (hinf : ¬ r.trans.Terminates) : Nat.find (take_terminates r n) = n := by
  apply le_antisymm
  · exact Nat.find_le (take_terminatedAt r n hinf)
  · rw [Nat.le_find_iff]
    intro m hm
    change ¬ (Seq.ofList (Seq.take n r.trans)).get? m = none
    rw [Stream'.Seq.ofList_get?, seq_getElem?_take r.trans n m hm]
    exact fun hc => hinf ⟨m, hc⟩

/-- For an infinite `r`, the end-state of the length-`n` prefix is `r.stateAt n`. -/
private theorem take_endState (r : ResolvedExec CEState CELabel) (n : ℕ)
    (hinf : ¬ r.trans.Terminates) {s : CEState} (hs : r.stateAt n = some s) :
    (r.take n).endState (take_terminates r n) = s := by
  have hfind := take_find r n hinf
  have heq := AlterSeq.stateAt_find_eq_endState (r.take n) (take_terminates r n)
  rw [hfind] at heq
  have hstate : (r.take n).stateAt n = r.stateAt n := by
    cases n with
    | zero => rfl
    | succ k =>
      change ((r.take (k + 1)).trans.get? k).map Prod.snd = (r.trans.get? k).map Prod.snd
      rw [take_trans_get? r (Nat.lt_succ_self k)]
  rw [hstate, hs] at heq
  exact (Option.some.inj heq).symm

/-! ### Fairness of `peR`

We now prove `peR.IsFair CEfair`. The `halt_fairDeadlock` clause is easy: `sigmaR` only emits
`none` at `bin`, and `bin` is a fair deadlock. The `inf_fair` clause is the crux: every infinite
consistent run walks the corridor `q 0 → q 1 → q 2 → ⋯` (never exiting through `q' _`, which would
force termination), and along it `sigmaR` strictly alternates fair/unfair by reading its own
`μ`-history — so one of every two consecutive steps is fair. -/

/-- The `bin` state is a fair deadlock: no transition (hence no fair transition) leaves it. -/
private theorem fairDeadlock_bin : CEfair.FairDeadlock CEState.bin := by
  rintro ⟨l, μ, hf⟩
  cases l <;> exact hf.elim

/-- `sigmaR` emits `none` only at `bin`: if `sigmaR.next r none ≠ 0` then `r` ends at `bin`. All the
other branches put a `some …` value in support (the coin is a `.map` onto `some …`, the
alternate/exit branches are `PMF.pure (some …)`). -/
private theorem sigmaR_none_endState (r : ResolvedExec CEState CELabel) (h : r.trans.Terminates)
    (hnone : sigmaR.next r none ≠ 0) : r.endState h = CEState.bin := by
  have hsupp : (none : Option (CELabel × PMF CEState)) ∈ (sigmaR.next r).support :=
    (PMF.mem_support_iff _ _).mpr hnone
  rw [sigmaR] at hsupp
  simp only [dif_pos h] at hsupp
  generalize hE : r.endState h = e at hsupp ⊢
  cases e with
  | q n =>
    exfalso
    dsimp only at hsupp
    by_cases hn : n = 0
    · subst hn; rw [if_pos rfl, PMF.mem_support_map_iff] at hsupp
      obtain ⟨b, _, hb⟩ := hsupp; exact Option.some_ne_none _ hb
    · rw [if_neg hn] at hsupp
      by_cases hlast : (r.trans.get? (n - 1)).map (fun p => p.1.2) = some (muA (n - 1))
      · rw [if_pos hlast, PMF.mem_support_pure_iff] at hsupp
        exact Option.some_ne_none _ hsupp.symm
      · rw [if_neg hlast, PMF.mem_support_pure_iff] at hsupp
        exact Option.some_ne_none _ hsupp.symm
  | q' n =>
    exfalso; dsimp only at hsupp
    rw [PMF.mem_support_pure_iff] at hsupp; exact Option.some_ne_none _ hsupp.symm
  | bin => rfl

/-! ### The corridor walk of an infinite consistent run

The following lemmas establish that every infinite `peR`-consistent run walks the corridor
`q 0 → q 1 → q 2 → ⋯` forever. The key obstructions — never entering `q' _` or `bin` — hold because
`sigmaR` from `q' k` is forced to `bin`, and `bin` is a `none`-only (halting) state, contradicting
the infinitude of a consistent run. -/

/-- `sigmaR` at a prefix ending in `q n` only proposes `some (Silent.τ, muA n)` or
`some (Silent.τ, muB n)`: its support avoids `q' _`/`bin`-producing steps. -/
private theorem sigmaR_q_support (r' : ResolvedExec CEState CELabel) (h : r'.trans.Terminates)
    (n : ℕ) (hend : r'.endState h = CEState.q n) (x : Option (CELabel × PMF CEState))
    (hx : x ∈ (sigmaR.next r').support) :
    x = some ((Silent.τ : CELabel), muA n) ∨ x = some ((Silent.τ : CELabel), muB n) := by
  rw [sigmaR] at hx; simp only [dif_pos h, hend] at hx
  by_cases hn : n = 0
  · subst hn; rw [if_pos rfl, PMF.mem_support_map_iff] at hx
    obtain ⟨b, _, hb⟩ := hx; cases b
    · right; rw [← hb]; simp
    · left; rw [← hb]; simp
  · rw [if_neg hn] at hx
    by_cases hlast : (r'.trans.get? (n - 1)).map (fun p => p.1.2) = some (muA (n - 1))
    · rw [if_pos hlast, PMF.mem_support_pure_iff] at hx; right; exact hx
    · rw [if_neg hlast, PMF.mem_support_pure_iff] at hx; left; exact hx

/-- An infinite consistent run never visits `bin`: `bin` is a `none`-only state, so consistency
(which needs an outgoing transition at every position of an infinite run) fails there. -/
private theorem no_bin (r : ResolvedExec CEState CELabel) (hinf : ¬ r.trans.Terminates)
    (hcons : peR.Consistent r) (m : ℕ) (hm : r.stateAt m = some CEState.bin) : False := by
  obtain ⟨lμs, hget⟩ : ∃ x, r.trans.get? m = some x := by
    rcases hx : r.trans.get? m with _ | x
    · exact absurd ⟨m, hx⟩ hinf
    · exact ⟨x, rfl⟩
  obtain ⟨⟨l, μ⟩, s'⟩ := lμs
  obtain ⟨hsched, _⟩ := hcons.2 m l μ s' hget
  change sigmaR.next (r.take m) (some (l, μ)) ≠ 0 at hsched
  have hend : (r.take m).endState (take_terminates r m) = CEState.bin := take_endState r m hinf hm
  have hnext : sigmaR.next (r.take m) = PMF.pure none := by
    rw [sigmaR]; simp only [dif_pos (take_terminates r m)]; rw [hend]
  rw [hnext, PMF.pure_apply] at hsched; simp at hsched

/-- An infinite consistent run never visits `q' k`: `sigmaR` from `q' k` is forced to `bin`, which
`no_bin` then rules out. -/
private theorem no_q' (r : ResolvedExec CEState CELabel) (hinf : ¬ r.trans.Terminates)
    (hcons : peR.Consistent r) (m k : ℕ) (hm : r.stateAt m = some (CEState.q' k)) : False := by
  obtain ⟨lμs, hget⟩ : ∃ x, r.trans.get? m = some x := by
    rcases hx : r.trans.get? m with _ | x
    · exact absurd ⟨m, hx⟩ hinf
    · exact ⟨x, rfl⟩
  obtain ⟨⟨l, μ⟩, s'⟩ := lμs
  obtain ⟨hsched, hμs'⟩ := hcons.2 m l μ s' hget
  change sigmaR.next (r.take m) (some (l, μ)) ≠ 0 at hsched
  have hend : (r.take m).endState (take_terminates r m) = CEState.q' k := take_endState r m hinf hm
  have hnext : sigmaR.next (r.take m)
      = PMF.pure (some ((some k : CELabel), PMF.pure CEState.bin)) := by
    rw [sigmaR]; simp only [dif_pos (take_terminates r m)]; rw [hend]
  rw [hnext, PMF.pure_apply] at hsched
  have heq : (some (l, μ) : Option (CELabel × PMF CEState))
      = some (some k, PMF.pure CEState.bin) := by
    by_contra hne; simp [hne] at hsched
  rw [Option.some.injEq, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hs' : s' = CEState.bin := by
    have := (PMF.mem_support_iff _ _).mpr hμs'
    rwa [PMF.mem_support_pure_iff] at this
  subst hs'; apply no_bin r hinf hcons (m + 1)
  change (r.trans.get? m).map Prod.snd = some CEState.bin; rw [hget]; rfl

/-- The transition distribution `μ` recorded at step `n` of `r` (with an irrelevant default off the
support of the run). -/
private noncomputable def run_mu (r : ResolvedExec CEState CELabel) (n : ℕ) : PMF CEState :=
  ((r.trans.get? n).map (fun p => p.1.2)).getD (muA 0)

/-- One corridor step: from `q n` a consistent infinite run takes `((Silent.τ, run_mu r n),
q (n+1))` with `run_mu r n ∈ {muA n, muB n}` (the exit target `q' n` is ruled out by `no_q'`). -/
private theorem run_step (r : ResolvedExec CEState CELabel) (hinf : ¬ r.trans.Terminates)
    (hcons : peR.Consistent r) (n : ℕ) (hn : r.stateAt n = some (CEState.q n)) :
    r.trans.get? n = some (((Silent.τ : CELabel), run_mu r n), CEState.q (n + 1)) ∧
      (run_mu r n = muA n ∨ run_mu r n = muB n) := by
  obtain ⟨lμs, hget⟩ : ∃ x, r.trans.get? n = some x := by
    rcases hx : r.trans.get? n with _ | x
    · exact absurd ⟨n, hx⟩ hinf
    · exact ⟨x, rfl⟩
  obtain ⟨⟨l, μ⟩, s'⟩ := lμs
  obtain ⟨hsched, hμs'⟩ := hcons.2 n l μ s' hget
  change sigmaR.next (r.take n) (some (l, μ)) ≠ 0 at hsched
  have hend : (r.take n).endState (take_terminates r n) = CEState.q n := take_endState r n hinf hn
  have hsupp : (some (l, μ) : Option (CELabel × PMF CEState)) ∈ (sigmaR.next (r.take n)).support :=
    (PMF.mem_support_iff _ _).mpr hsched
  have hlμ := sigmaR_q_support (r.take n) (take_terminates r n) n hend (some (l, μ)) hsupp
  have hlμ' : (l = Silent.τ ∧ μ = muA n) ∨ (l = Silent.τ ∧ μ = muB n) := by
    rcases hlμ with h | h
    · left; rw [Option.some.injEq, Prod.mk.injEq] at h; exact h
    · right; rw [Option.some.injEq, Prod.mk.injEq] at h; exact h
  have hrun : run_mu r n = μ := by rw [run_mu, hget]; rfl
  have hμs'2 : s' ∈ μ.support := (PMF.mem_support_iff _ _).mpr hμs'
  have hs'mem : s' = CEState.q (n + 1) ∨ s' = CEState.q' n := by
    have hsub : μ.support ⊆ {CEState.q (n + 1), CEState.q' n} := by
      rcases hlμ' with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact muA_support_subset n
      · exact muB_support_subset n
    have := hsub hμs'2; simpa using this
  have hs' : s' = CEState.q (n + 1) := by
    rcases hs'mem with h | h
    · exact h
    · exfalso; apply no_q' r hinf hcons (n + 1) n
      change (r.trans.get? n).map Prod.snd = some (CEState.q' n); rw [hget, h]; rfl
  subst hs'
  refine ⟨?_, ?_⟩
  · rw [hget]; rcases hlμ' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hrun]
  · rw [hrun]; rcases hlμ' with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · left; rfl
    · right; rfl

/-- **The corridor walk.** Every infinite consistent run has, at each `n`, `stateAt n = q n`,
transition `((Silent.τ, run_mu r n), q (n+1))`, and `run_mu r n ∈ {muA n, muB n}`. -/
private theorem run_advances (r : ResolvedExec CEState CELabel) (hinf : ¬ r.trans.Terminates)
    (hcons : peR.Consistent r) (n : ℕ) :
    r.stateAt n = some (CEState.q n) ∧
      r.trans.get? n = some (((Silent.τ : CELabel), run_mu r n), CEState.q (n + 1)) ∧
      (run_mu r n = muA n ∨ run_mu r n = muB n) := by
  induction n with
  | zero =>
    have hinit : r.stateAt 0 = some (CEState.q 0) := by
      have h0 := hcons.1
      change (PMF.pure CESys.init) r.init ≠ 0 at h0
      rw [PMF.pure_apply] at h0
      have : r.init = CESys.init := by by_contra hne; simp [hne] at h0
      change some r.init = some (CEState.q 0); rw [this]; rfl
    exact ⟨hinit, run_step r hinf hcons 0 hinit⟩
  | succ k ih =>
    obtain ⟨_, hget, _⟩ := ih
    have hst' : r.stateAt (k + 1) = some (CEState.q (k + 1)) := by
      change (r.trans.get? k).map Prod.snd = some (CEState.q (k + 1)); rw [hget]; rfl
    exact ⟨hst', run_step r hinf hcons (k + 1) hst'⟩

open Classical in
/-- The exact one-step distribution of `sigmaR` at the length-`(n+1)` prefix of an infinite run:
reading its own `μ`-history it plays PURE the *opposite* of `run_mu r n`. -/
private theorem sigmaR_next_succ (r : ResolvedExec CEState CELabel) (hinf : ¬ r.trans.Terminates)
    (hcons : peR.Consistent r) (n : ℕ) :
    sigmaR.next (r.take (n + 1)) =
      (if run_mu r n = muA n then PMF.pure (some ((Silent.τ : CELabel), muB (n + 1)))
       else PMF.pure (some ((Silent.τ : CELabel), muA (n + 1)))) := by
  obtain ⟨_, hget, _⟩ := run_advances r hinf hcons n
  have hst' : r.stateAt (n + 1) = some (CEState.q (n + 1)) := by
    change (r.trans.get? n).map Prod.snd = _; rw [hget]; rfl
  have hend := take_endState r (n + 1) hinf hst'
  rw [sigmaR]; simp only [dif_pos (take_terminates r (n + 1)), hend]
  rw [if_neg (Nat.succ_ne_zero n)]
  have hlast : ((r.take (n + 1)).trans.get? ((n + 1) - 1)).map (fun p => p.1.2)
      = some (run_mu r n) := by
    rw [Nat.add_sub_cancel, take_trans_get? r (Nat.lt_succ_self n), hget]; rfl
  rw [hlast, Nat.add_sub_cancel]
  by_cases h : run_mu r n = muA n
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (by intro hc; exact h (Option.some.inj hc))]

open Classical in
/-- Consistency pins `run_mu r (n+1)` to the sole support value of `sigmaR.next (r.take (n+1))`. -/
private theorem run_mu_succ_eq (r : ResolvedExec CEState CELabel) (hinf : ¬ r.trans.Terminates)
    (hcons : peR.Consistent r) (n : ℕ) :
    run_mu r (n + 1) = (if run_mu r n = muA n then muB (n + 1) else muA (n + 1)) := by
  obtain ⟨_, hget, _⟩ := run_advances r hinf hcons (n + 1)
  obtain ⟨hsched, _⟩ := hcons.2 (n + 1) Silent.τ (run_mu r (n + 1)) (CEState.q (n + 2)) hget
  change sigmaR.next (r.take (n + 1)) (some (Silent.τ, run_mu r (n + 1))) ≠ 0 at hsched
  rw [sigmaR_next_succ r hinf hcons n] at hsched
  by_cases h : run_mu r n = muA n
  · rw [if_pos h] at hsched ⊢; rw [PMF.pure_apply] at hsched
    have : (some ((Silent.τ : CELabel), run_mu r (n + 1))) = some (Silent.τ, muB (n + 1)) := by
      by_contra hne; simp [hne] at hsched
    rw [Option.some.injEq, Prod.mk.injEq] at this; exact this.2
  · rw [if_neg h] at hsched ⊢; rw [PMF.pure_apply] at hsched
    have : (some ((Silent.τ : CELabel), run_mu r (n + 1))) = some (Silent.τ, muA (n + 1)) := by
      by_contra hne; simp [hne] at hsched
    rw [Option.some.injEq, Prod.mk.injEq] at this; exact this.2

open Classical in
/-- **Strict alternation.** Step `n+1` is fair (`muA`) iff step `n` was unfair (`muB`). -/
private theorem alternation (r : ResolvedExec CEState CELabel) (hinf : ¬ r.trans.Terminates)
    (hcons : peR.Consistent r) (n : ℕ) :
    run_mu r (n + 1) = muA (n + 1) ↔ run_mu r n = muB n := by
  rw [run_mu_succ_eq r hinf hcons n]
  obtain ⟨_, _, hmem⟩ := run_advances r hinf hcons n
  by_cases h : run_mu r n = muA n
  · rw [if_pos h]
    constructor
    · intro heq; exact absurd heq.symm (muA_ne_muB (n + 1))
    · intro hB; rw [h] at hB; exact absurd hB (muA_ne_muB n)
  · rw [if_neg h]
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    rcases hmem with h' | h'
    · exact absurd h' h
    · exact h'

/-- A step of an infinite consistent run is fair exactly when it took the fair transition `muA`. -/
private theorem fairStep_iff (r : ResolvedExec CEState CELabel) (hinf : ¬ r.trans.Terminates)
    (hcons : peR.Consistent r) (n : ℕ) :
    CEfair.FairStepAt r n ↔ run_mu r n = muA n := by
  obtain ⟨hst, hget, _⟩ := run_advances r hinf hcons n
  constructor
  · rintro ⟨s, l, μ, s', hs, hg, hfair⟩
    rw [hget] at hg; rw [hst] at hs
    obtain rfl := Option.some.inj hs
    rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hg
    obtain ⟨⟨rfl, rfl⟩, _⟩ := hg
    exact hfair.2
  · intro hmu
    exact ⟨CEState.q n, Silent.τ, run_mu r n, CEState.q (n + 1), hst, hget, ⟨rfl, hmu⟩⟩

/-- **`peR` is resolved-fair.** It halts only at the fair deadlock `bin`, and every infinite
consistent run — walking the corridor and alternating fair/unfair — takes a fair step at `n` or
`n+1` for every `n`, hence infinitely often. -/
theorem peR_isFair : peR.IsFair CEfair where
  halt_fairDeadlock := by
    intro r h _ hnone
    rw [sigmaR_none_endState r h hnone]; exact fairDeadlock_bin
  inf_fair := by
    intro r hinf hcons N
    obtain ⟨_, _, hmem⟩ := run_advances r hinf hcons N
    rcases hmem with hA | hB
    · exact ⟨N, le_refl N, (fairStep_iff r hinf hcons N).mpr hA⟩
    · exact ⟨N + 1, Nat.le_succ N,
        (fairStep_iff r hinf hcons (N + 1)).mpr ((alternation r hinf hcons N).mpr hB)⟩

/-! ### `D` is resolved-fair-achievable

The trace distribution `D_CE` produced by `peR` is, by construction, resolved-fair achievable:
`peR` starts from `pure CESys.init` and is fair (`peR_isFair`), and its trace distribution is
`peR.traceProbR` definitionally. -/

/-- The trace distribution realised by the resolved witness `peR`. -/
noncomputable def D_CE : Seq CELabel → ENNReal := fun τ => peR.traceProbR τ

/-- **`D_CE` is resolved-fair achievable.** Witnessed by `peR`: correct initial distribution, fair
(`peR_isFair`), trace distribution `D_CE` by definition. This is the substance of the separator —
combined with the (informal) impossibility for plain schedulers, it shows the resolved fair set is
strictly larger. -/
theorem D_CE_mem_R : D_CE ∈ fairAchievableTraceDists CEfair :=
  ⟨peR, rfl, peR_isFair, fun _ => rfl⟩

/-! ### The single-external-label trace `[some k]` and its unique tight realiser

The plain (non-resolved) trace probability of the observation `traceK k = [some k]` is realised by
exactly one tight terminating execution: advance silently `q 0 → q 1 → ⋯ → q k`, silently exit to
`q' k`, then take the external `some k`-step to `bin`. We compute the resulting `probOf` as a
product of one-step kernels — the computational core of the separator's plain-scheduler side. -/

/-- The single-external-label trace: the observation of the one external label `k`. -/
def traceK (k : ℕ) : Seq CELabel := Seq.cons (some k) Seq.nil

/-- The `k` advancing silent steps `q 0 → q 1 → ⋯ → q k` (as a transition list). -/
def advList (k : ℕ) : List (CELabel × CEState) :=
  (List.range k).map (fun i => ((Silent.τ : CELabel), CEState.q (i + 1)))

/-- The unique tight realiser of `traceK k`: advance silently to `q k`, silently exit to `q' k`,
then take the external `some k`-step to `bin`. -/
def exitExec (k : ℕ) : AlterSeq CEState CELabel :=
  ⟨CEState.q 0,
    Seq.ofList (advList k ++ [((Silent.τ : CELabel), CEState.q' k), (some k, CEState.bin)])⟩

theorem exitExec_terminates (k : ℕ) : (exitExec k).trans.Terminates :=
  Stream'.Seq.terminates_ofList _

/-- Filtering a `Seq.ofList` commutes with `List.filter` (for a decidable predicate written as a
`Prop`-valued `filter`). Used to compute the trace on the explicit transition list. -/
private theorem filter_ofList {α : Type} (p : α → Prop) [DecidablePred p] (l : List α) :
    (Seq.ofList l).filter p = Seq.ofList (l.filter (fun a => decide (p a))) := by
  induction l with
  | nil => rw [Stream'.Seq.ofList_nil, Stream'.Seq.filter_nil, List.filter_nil,
      Stream'.Seq.ofList_nil]
  | cons a t ih =>
    rw [Stream'.Seq.ofList_cons, List.filter_cons]
    by_cases h : p a
    · rw [Stream'.Seq.filter_cons_pos a _ h, if_pos (by simpa using h), Stream'.Seq.ofList_cons, ih]
    · rw [Stream'.Seq.filter_cons_neg a _ h, if_neg (by simpa using h), ih]

theorem exitExec_trace (k : ℕ) : CESys.trace (exitExec k) = traceK k := by
  classical
  unfold System.trace exitExec
  rw [filter_ofList]
  have hfilter : (advList k ++ [((Silent.τ : CELabel), CEState.q' k), (some k, CEState.bin)]).filter
      (fun a => decide (¬ a.1 = Silent.τ)) = [(some k, CEState.bin)] := by
    rw [List.filter_append]
    have hadv : (advList k).filter (fun a => decide (¬ a.1 = Silent.τ)) = [] := by
      rw [advList, List.filter_map]
      rw [List.filter_eq_nil_iff.mpr (by intro x _; simp)]
      rfl
    rw [hadv, List.nil_append]
    simp [Silent.τ]
  rw [hfilter, Stream'.Seq.ofList_cons, Stream'.Seq.map_cons, Stream'.Seq.ofList_nil,
    Stream'.Seq.map_nil]
  rfl

/-- The length of the advance list is `k`. -/
private theorem advList_length (k : ℕ) : (advList k).length = k := by
  rw [advList, List.length_map, List.length_range]

theorem exitExec_isTight (k : ℕ) : CESys.IsTight (exitExec k) := by
  refine Or.inr ⟨k + 1, some k, CEState.bin, ?_, ?_, by simp [Silent.τ]⟩
  · change (Seq.ofList (advList k ++ [((Silent.τ : CELabel), CEState.q' k),
        (some k, CEState.bin)])).get? (k + 1) = some (some k, CEState.bin)
    rw [Stream'.Seq.ofList_get?, List.getElem?_append_right (by rw [advList_length]; omega),
      advList_length]
    simp
  · change (Seq.ofList (advList k ++ [((Silent.τ : CELabel), CEState.q' k),
        (some k, CEState.bin)])).get? (k + 2) = none
    rw [Stream'.Seq.ofList_get?]
    apply List.getElem?_eq_none
    rw [List.length_append, advList_length]
    simp

/-! ### The kernel product for `exitExec k`

`probOf (exitExec k)` factors, by peeling from the end, into the product of the `k` advancing
kernels `q j → q (j+1)`, the silent-exit kernel `q k → q' k`, and the external kernel `q' k → bin`.
The advancing product is proved by an induction over `advList` mirroring `probOf_eN`. -/

/-- The history of an infinite run at `q j`: the pure advance `q 0 → ⋯ → q j`. -/
def advPrefix (j : ℕ) : AlterSeq CEState CELabel := ⟨CEState.q 0, Seq.ofList (advList j)⟩

/-- The history at `q' k`: the pure advance to `q k` followed by the silent exit to `q' k`. -/
def qExitPrefix (k : ℕ) : AlterSeq CEState CELabel :=
  ⟨CEState.q 0, Seq.ofList (advList k ++ [((Silent.τ : CELabel), CEState.q' k)])⟩

/-- `advList` grows by one advancing step. -/
private theorem advList_succ (j : ℕ) :
    advList (j + 1) = advList j ++ [((Silent.τ : CELabel), CEState.q (j + 1))] := by
  rw [advList, advList, List.range_succ, List.map_append, List.map_cons, List.map_nil]

private theorem advPrefix_terminates (j : ℕ) : (advPrefix j).trans.Terminates :=
  Stream'.Seq.terminates_ofList _

/-- The `probOf` of the pure advance to `q k` is the product of the advancing kernels. -/
private theorem probOf_advPrefix (pe : ProbabilisticExecution CESys)
    (h0 : pe.initState = PMF.pure (CEState.q 0)) (k : ℕ) :
    pe.probOf (advPrefix k) (advPrefix_terminates k)
      = ∏ j ∈ Finset.range k,
          pe.kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q (j + 1)) := by
  induction k with
  | zero =>
    have h_eq : advPrefix 0 = ⟨CEState.q 0, (Seq.nil : Seq (CELabel × CEState))⟩ := by
      simp only [advPrefix, advList, List.range_zero, List.map_nil, Stream'.Seq.ofList_nil]
    rw [pe.probOf_congr (advPrefix 0) _ h_eq (advPrefix_terminates 0) Stream'.Seq.terminates_nil,
      pe.probOf_nil, Finset.range_zero, Finset.prod_empty]
    change pe.init (CEState.q 0) = 1
    rw [pe.init_eq_initState, h0]
    exact PMF.pure_apply_self _
  | succ j ih =>
    have hsq : (Seq.ofList (advList j)).Terminates := Stream'.Seq.terminates_ofList _
    have h_eq : advPrefix (j + 1) =
        ⟨CEState.q 0, (Seq.ofList (advList j)).append
          (Seq.cons ((Silent.τ : CELabel), CEState.q (j + 1)) Seq.nil)⟩ := by
      simp only [advPrefix]
      congr 1
      rw [advList_succ, Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    rw [pe.probOf_congr (advPrefix (j + 1)) _ h_eq (advPrefix_terminates (j + 1))
        (h_eq ▸ advPrefix_terminates (j + 1)),
      pe.probOf_append_singleton (CEState.q 0) (Seq.ofList (advList j)) hsq
        ((Silent.τ : CELabel), CEState.q (j + 1)),
      Finset.prod_range_succ]
    rw [pe.probOf_congr (⟨CEState.q 0, Seq.ofList (advList j)⟩ : AlterSeq CEState CELabel)
      (advPrefix j) rfl hsq (advPrefix_terminates j), ih]
    rfl

private theorem qExitPrefix_terminates (k : ℕ) : (qExitPrefix k).trans.Terminates :=
  Stream'.Seq.terminates_ofList _

/-- **The kernel product for `exitExec k`.** Peeling the external step `q' k → bin` and the silent
exit `q k → q' k`, then the advancing product, gives `probOf (exitExec k)` as the product of the `k`
advancing kernels, the silent-exit kernel, and the external kernel. -/
theorem probOf_exitExec (pe : ProbabilisticExecution CESys)
    (h0 : pe.initState = PMF.pure (CEState.q 0)) (k : ℕ) :
    pe.probOf (exitExec k) (exitExec_terminates k)
      = (∏ j ∈ Finset.range k, pe.kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q (j + 1)))
        * pe.kernel (advPrefix k) ((Silent.τ : CELabel), CEState.q' k)
        * pe.kernel (qExitPrefix k) ((some k : CELabel), CEState.bin) := by
  -- Peel the external step `q' k → bin`.
  have hexit : exitExec k =
      ⟨CEState.q 0, (Seq.ofList (advList k ++ [((Silent.τ : CELabel), CEState.q' k)])).append
        (Seq.cons ((some k : CELabel), CEState.bin) Seq.nil)⟩ := by
    simp only [exitExec]
    congr 1
    rw [show advList k ++ [((Silent.τ : CELabel), CEState.q' k), (some k, CEState.bin)]
          = (advList k ++ [((Silent.τ : CELabel), CEState.q' k)]) ++ [(some k, CEState.bin)] from by
        simp,
      Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
  rw [pe.probOf_congr (exitExec k) _ hexit (exitExec_terminates k) (hexit ▸ exitExec_terminates k),
    pe.probOf_append_singleton (CEState.q 0)
      (Seq.ofList (advList k ++ [((Silent.τ : CELabel), CEState.q' k)]))
      (Stream'.Seq.terminates_ofList _) ((some k : CELabel), CEState.bin)]
  -- The truncated prefix is `qExitPrefix k`; peel the silent exit `q k → q' k`.
  have hqe : (⟨CEState.q 0, Seq.ofList (advList k ++ [((Silent.τ : CELabel), CEState.q' k)])⟩ :
      AlterSeq CEState CELabel) = qExitPrefix k := rfl
  rw [pe.probOf_congr _ (qExitPrefix k) hqe (Stream'.Seq.terminates_ofList _)
    (qExitPrefix_terminates k)]
  have hqe2 : qExitPrefix k =
      ⟨CEState.q 0, (Seq.ofList (advList k)).append
        (Seq.cons ((Silent.τ : CELabel), CEState.q' k) Seq.nil)⟩ := by
    simp only [qExitPrefix]
    congr 1
    rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
  rw [pe.probOf_congr (qExitPrefix k) _ hqe2 (qExitPrefix_terminates k)
      (hqe2 ▸ qExitPrefix_terminates k),
    pe.probOf_append_singleton (CEState.q 0) (Seq.ofList (advList k))
      (Stream'.Seq.terminates_ofList _) ((Silent.τ : CELabel), CEState.q' k)]
  -- The remaining prefix is `advPrefix k`; apply the advancing product.
  rw [pe.probOf_congr (⟨CEState.q 0, Seq.ofList (advList k)⟩ : AlterSeq CEState CELabel)
      (advPrefix k) rfl (Stream'.Seq.terminates_ofList _) (advPrefix_terminates k),
    probOf_advPrefix pe h0 k]
  -- The two remaining kernels are at the `advPrefix k` / `qExitPrefix k` histories.
  rfl

/-! ### Uniqueness of the tight realiser and the collapse of `traceProb`

Any tight terminating execution with trace `[some k]` and **nonzero** `probOf` under a
`q 0`-initial plain execution must be `exitExec k`: scheduler validity forces every transition to be
a genuine `CESys`-step, and the corridor structure then pins the whole run. Hence the defining
`tsum` of `traceProb pe (traceK k)` collapses to the single summand `probOf (exitExec k)`. -/

/-- A nonzero one-step kernel forces a genuine `CESys`-step from the end of the (terminating) base
prefix: some emitted `μ` is a valid transition and lands on `s'`. -/
private theorem kernel_ne_zero_step (pe : ProbabilisticExecution CESys)
    (base : AlterSeq CEState CELabel) (hb : base.trans.Terminates)
    (l : CELabel) (s' : CEState) (hk : pe.kernel base (l, s') ≠ 0) :
    ∃ μ, CESys.step (base.endState hb) l μ ∧ s' ∈ μ.support := by
  unfold ProbabilisticExecution.kernel at hk
  obtain ⟨μ, hμ⟩ : ∃ μ, pe.scheduler.next base (some ((l, s').1, μ)) * μ (l, s').2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hk (by simp only [hc, tsum_zero])
  refine ⟨μ, ?_, (PMF.mem_support_iff _ _).mpr (right_ne_zero_of_mul hμ)⟩
  have hsupp : some (l, μ) ∈ (pe.scheduler.next base).support :=
    (PMF.mem_support_iff _ _).mpr (left_ne_zero_of_mul hμ)
  exact pe.scheduler.valid base (Nat.find hb) (base.endState hb) (Nat.find_spec hb)
    (AlterSeq.stateAt_find_eq_endState base hb) l μ hsupp

/-- The advancing segment from `q n` up to `q k` (empty when `k ≤ n`). -/
private def advSeg (n k : ℕ) : List (CELabel × CEState) :=
  (List.range (k - n)).map (fun i => ((Silent.τ : CELabel), CEState.q (n + 1 + i)))

private theorem advSeg_zero (k : ℕ) : advSeg 0 k = advList k := by
  unfold advSeg advList
  simp only [Nat.sub_zero]
  apply List.map_congr_left
  intro i _; simp [Nat.add_comm]

private theorem advSeg_cons (n k : ℕ) (h : n < k) :
    advSeg n k = ((Silent.τ : CELabel), CEState.q (n + 1)) :: advSeg (n + 1) k := by
  unfold advSeg
  have hsub : k - n = (k - (n + 1)) + 1 := by omega
  rw [hsub, List.range_succ_eq_map, List.map_cons]
  simp only [Nat.add_zero]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro i _; simp only [Function.comp_apply]; congr 2; omega

private theorem advSeg_self (k : ℕ) : advSeg k k = [] := by unfold advSeg; simp

/-- The advancing segment carries only silent labels, so it contributes nothing to the trace. -/
private theorem advSeg_filter (n k : ℕ) :
    (advSeg n k).filter (fun p => decide (¬ p.1 = Silent.τ)) = [] := by
  rw [advSeg, List.filter_map, List.filter_eq_nil_iff.mpr (by intro x _; simp)]
  rfl

/-- **Structural shape of a nonzero-probability tight run.** From a terminating base ending at
`q n`, any transition list `L` with nonzero path weight whose external labels are `[some k]` and
which ends externally is the advance `q n → q k`, then the silent exit `q k → q' k`, then the
external `some k`-step to `bin`. -/
private theorem run_shape (pe : ProbabilisticExecution CESys) (k : ℕ) :
    ∀ (L : List (CELabel × CEState)) (base : AlterSeq CEState CELabel)
      (hb : base.trans.Terminates) (n : ℕ), base.endState hb = CEState.q n →
      pe.pathWeight base L ≠ 0 →
      (L.filter (fun p => decide (¬ p.1 = Silent.τ))).map Prod.fst = [some k] →
      (∀ p, L.getLast? = some p → ¬ p.1 = Silent.τ) →
      n ≤ k ∧
        L = advSeg n k ++ [((Silent.τ : CELabel), CEState.q' k), (some k, CEState.bin)] := by
  intro L
  induction L with
  | nil =>
    intro base hb n _ _ hfilter _
    simp only [List.filter_nil, List.map_nil] at hfilter
    exact absurd hfilter.symm (by simp)
  | cons a L ih =>
    intro base hb n hend hpw hfilter hlast
    -- Peel the first step: its kernel is nonzero, so it is a valid `CESys`-step from `q n`.
    obtain ⟨la, sa⟩ := a
    rw [pe.pathWeight_cons base la sa L] at hpw
    have hk0 : pe.kernel base (la, sa) ≠ 0 := left_ne_zero_of_mul hpw
    obtain ⟨μ, hstep, hsmem⟩ := kernel_ne_zero_step pe base hb la sa hk0
    rw [hend] at hstep
    change CEstep (CEState.q n) la μ at hstep
    obtain ⟨hla, hμ⟩ := hstep
    subst hla
    -- The base extended by `(τ, sa)` ends at `sa`.
    set base' : AlterSeq CEState CELabel :=
      ⟨base.init, base.trans.append (Seq.cons ((Silent.τ : CELabel), sa) Seq.nil)⟩ with hbase'
    have hb' : base'.trans.Terminates :=
      ⟨Nat.find hb + 1, Stream'.Seq.terminatedAt_append_find hb
        (show (Seq.cons ((Silent.τ : CELabel), sa) Seq.nil).TerminatedAt 1 from rfl)⟩
    have hend' : base'.endState hb' = sa := by
      have := AlterSeq.endState_append_singleton base hb (Silent.τ : CELabel) sa
      exact this
    have hpw' : pe.pathWeight base' L ≠ 0 := right_ne_zero_of_mul hpw
    -- `sa` is `q (n+1)` (advance) or `q' n` (exit).
    have hsa : sa = CEState.q (n + 1) ∨ sa = CEState.q' n := by
      rcases hμ with rfl | rfl
      · have := muA_support_subset n hsmem; simpa using this
      · have := muB_support_subset n hsmem; simpa using this
    rcases hsa with rfl | rfl
    · -- Advance step `q n → q (n+1)`; recurse.
      have hfilter' : (L.filter (fun p => decide (¬ p.1 = Silent.τ))).map Prod.fst = [some k] := by
        rw [List.filter_cons, if_neg (by simp)] at hfilter
        exact hfilter
      have hlast' : ∀ p, L.getLast? = some p → ¬ p.1 = Silent.τ := by
        intro p hp
        apply hlast p
        cases hLnil : L with
        | nil => rw [hLnil] at hp; simp at hp
        | cons b L' =>
          rw [List.getLast?_cons_cons]
          rw [hLnil] at hp
          exact hp
      obtain ⟨hle, hrec⟩ := ih base' hb' (n + 1) hend' hpw' hfilter' hlast'
      have hnk : n < k := hle
      refine ⟨le_of_lt hnk, ?_⟩
      rw [advSeg_cons n k hnk, List.cons_append]
      congr 1
    · -- Exit step `q n → q' n`; the next step must be the external `some n`-step to `bin`, so
      -- `n = k`, and the run ends at `bin`.
      -- `L` is nonempty (else the trace `(τ, q' n) :: L` would be empty).
      cases hLnil : L with
      | nil =>
        exfalso
        rw [hLnil, List.filter_cons, if_neg (by simp), List.filter_nil, List.map_nil] at hfilter
        exact absurd hfilter.symm (by simp)
      | cons b L' =>
        obtain ⟨lb, sb⟩ := b
        rw [hbase', hLnil, pe.pathWeight_cons _ lb sb L'] at hpw'
        have hk0' : pe.kernel base' (lb, sb) ≠ 0 := left_ne_zero_of_mul hpw'
        obtain ⟨ν, hstepb, hsb⟩ := kernel_ne_zero_step pe base' hb' lb sb hk0'
        rw [hend'] at hstepb
        change CEstep (CEState.q' n) lb ν at hstepb
        obtain ⟨hlb, hν⟩ := hstepb
        subst hlb hν
        rw [PMF.mem_support_pure_iff] at hsb
        subst hsb
        -- Read off `n = k` from the (single) external label.
        rw [hLnil, List.filter_cons, if_neg (by simp), List.filter_cons, if_pos (by simp),
          List.map_cons] at hfilter
        have hnk : some n = some k := by
          have h2 := List.cons.inj hfilter
          exact h2.1
        obtain rfl := Option.some.inj hnk
        refine ⟨le_refl n, ?_⟩
        rw [advSeg_self n, List.nil_append]
        refine congrArg (List.cons _) (congrArg (List.cons _) ?_)
        -- After `(some n, bin)` the run must end: from `bin` no valid step exists.
        set base'' : AlterSeq CEState CELabel :=
          ⟨base'.init, base'.trans.append (Seq.cons ((some n : CELabel), CEState.bin) Seq.nil)⟩
          with hbase''
        have hb'' : base''.trans.Terminates :=
          ⟨Nat.find hb' + 1, Stream'.Seq.terminatedAt_append_find hb'
            (show (Seq.cons ((some n : CELabel), CEState.bin) Seq.nil).TerminatedAt 1 from rfl)⟩
        have hend'' : base''.endState hb'' = CEState.bin :=
          AlterSeq.endState_append_singleton base' hb' (some n : CELabel) CEState.bin
        have hpwbin : pe.pathWeight base'' L' ≠ 0 := right_ne_zero_of_mul hpw'
        cases hL'nil : L' with
        | nil => rfl
        | cons c L'' =>
          exfalso
          obtain ⟨lc, sc⟩ := c
          rw [hL'nil, pe.pathWeight_cons base'' lc sc L''] at hpwbin
          have hk0'' : pe.kernel base'' (lc, sc) ≠ 0 := left_ne_zero_of_mul hpwbin
          obtain ⟨ρ, hstepc, _⟩ := kernel_ne_zero_step pe base'' hb'' lc sc hk0''
          rw [hend''] at hstepc
          exact hstepc

/-- `Seq.ofList` is injective (via `toList_ofList`). -/
private theorem ofList_inj {α : Type} {a b : List α} (h : Seq.ofList a = Seq.ofList b) : a = b := by
  have ha : (Seq.ofList a).toList (Stream'.Seq.terminates_ofList a) = a :=
    Stream'.Seq.toList_ofList a
  have hb : (Seq.ofList b).toList (Stream'.Seq.terminates_ofList b) = b :=
    Stream'.Seq.toList_ofList b
  rw [← ha, ← hb]
  congr 1

/-- **Uniqueness of the tight `traceK k`-realiser** (among nonzero-probability executions).
Scheduler validity turns `probOf e ≠ 0` into per-step `CESys`-validity, and `run_shape` then pins
the whole transition list; the initial mass pins `e.init = q 0`. -/
private theorem tight_traceK_unique (pe : ProbabilisticExecution CESys)
    (h0 : pe.initState = PMF.pure (CEState.q 0)) (k : ℕ) (e : AlterSeq CEState CELabel)
    (hT : e.trans.Terminates) (hne : pe.probOf e hT ≠ 0)
    (htr : CESys.trace e = traceK k) (htight : CESys.IsTight e) : e = exitExec k := by
  classical
  set L := e.trans.toList hT with hLdef
  have heL : e = ⟨e.init, Seq.ofList L⟩ := by
    calc e = ⟨e.init, e.trans⟩ := rfl
      _ = ⟨e.init, Seq.ofList L⟩ := by rw [hLdef, Stream'.Seq.ofList_toList]
  -- Factor `probOf` and read off `e.init = q 0` and the path weight.
  have hpf : pe.probOf ⟨e.init, Seq.ofList L⟩ (Stream'.Seq.terminates_ofList L)
      = pe.init e.init * pe.pathWeight ⟨e.init, Seq.nil⟩ L :=
    pe.probOf_eq_pathWeight e.init L (Stream'.Seq.terminates_ofList L)
  have hne' : pe.init e.init * pe.pathWeight ⟨e.init, Seq.nil⟩ L ≠ 0 := by
    rw [← hpf]
    rw [pe.probOf_congr ⟨e.init, Seq.ofList L⟩ e heL.symm (Stream'.Seq.terminates_ofList L) hT]
    exact hne
  have hinit : pe.init e.init ≠ 0 := left_ne_zero_of_mul hne'
  have hei : e.init = CEState.q 0 := by
    rw [pe.init_eq_initState, h0, PMF.pure_apply] at hinit
    by_contra hc
    rw [if_neg hc] at hinit
    exact hinit rfl
  have hpw : pe.pathWeight ⟨CEState.q 0, Seq.nil⟩ L ≠ 0 := by
    rw [← hei]; exact right_ne_zero_of_mul hne'
  -- Bridge the trace/tightness conditions to the label list.
  obtain ⟨htlab, htgl⟩ := (CESys.tight_iff (traceK k) e hT).mp ⟨htr, htight⟩
  set labs := (e.trans.toList hT).map Prod.fst with hlabsdef
  -- Trace ⇒ the `run_shape` filter condition.
  have hfilter : (L.filter (fun p => decide (¬ p.1 = Silent.τ))).map Prod.fst = [some k] := by
    have h1 : (Seq.ofList labs).filter (fun l => ¬ l = Silent.τ) = traceK k := htlab
    rw [filter_ofList] at h1
    have h2 : labs.filter (fun l => decide (¬ l = Silent.τ)) = [some k] := by
      apply ofList_inj
      rw [h1, traceK]
      rw [show (Seq.cons (some k) Seq.nil : Seq CELabel) = Seq.ofList [some k] from by
        rw [Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]]
    rw [hlabsdef, ← hLdef, List.filter_map] at h2
    exact h2
  -- Tightness ⇒ the `run_shape` getLast condition.
  have hlastc : ∀ p, L.getLast? = some p → ¬ p.1 = Silent.τ := by
    intro p hp
    apply htgl p.1
    rw [hlabsdef, ← hLdef, List.getLast?_map, hp]
    rfl
  have hendbase : (⟨CEState.q 0, (Seq.nil : Seq (CELabel × CEState))⟩ :
      AlterSeq CEState CELabel).endState Stream'.Seq.terminates_nil = CEState.q 0 :=
    AlterSeq.endState_of_trans_nil _ rfl Stream'.Seq.terminates_nil
  obtain ⟨_, hshape⟩ := run_shape pe k L ⟨CEState.q 0, Seq.nil⟩ Stream'.Seq.terminates_nil 0
    hendbase hpw hfilter hlastc
  rw [advSeg_zero] at hshape
  rw [heL, hei, hshape]
  rfl

/-- **`traceProb` collapses to a single `probOf`.** The trace probability of the single external
label `k` under any `q 0`-initial plain execution is the probability of the unique tight realiser
`exitExec k`. -/
theorem traceProb_traceK (pe : ProbabilisticExecution CESys)
    (h0 : pe.initState = PMF.pure (CEState.q 0)) (k : ℕ) :
    CESys.traceProb pe (traceK k) = pe.probOf (exitExec k) (exitExec_terminates k) := by
  classical
  unfold System.traceProb
  set S := {e : AlterSeq CEState CELabel //
    e.trans.Terminates ∧ CESys.trace e = traceK k ∧ CESys.IsTight e} with hS
  rw [tsum_eq_single
    (⟨exitExec k, exitExec_terminates k, exitExec_trace k, exitExec_isTight k⟩ : S)]
  intro e' hne'
  by_contra hp
  apply hne'
  have heq : e'.1 = exitExec k :=
    tight_traceK_unique pe h0 k e'.1 e'.2.1 hp e'.2.2.1 e'.2.2.2
  exact Subtype.ext heq

/-! ### Step 1 — the one-step kernels of an arbitrary plain execution

For *any* plain `pe` on `CESys`, the advancing / exit / external kernels evaluate to closed forms in
terms of `sigmaR`-agnostic scheduler masses `pmA pe j` (mass on `muA j`) and `pmB pe j` (mass on
`muB j`). Scheduler validity restricts the defining `tsum` over `μ` to the two-point support
`{muA j, muB j}`. -/

/-- Restriction of a `tsum` to a two-point support. -/
private theorem tsum_two_of_support {β : Type} (f : β → ENNReal) (a b : β) (hab : a ≠ b)
    (hsupp : Function.support f ⊆ {a, b}) : ∑' x, f x = f a + f b := by
  classical
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  have hfin : Set.Finite ({a, b} : Set β) := (Set.finite_singleton b).insert a
  have : Fintype (↑({a, b} : Set β)) := hfin.fintype
  rw [tsum_fintype]
  rw [show (Finset.univ : Finset (↑({a, b} : Set β)))
      = {⟨a, by simp⟩, ⟨b, by simp⟩} from ?_]
  · rw [Finset.sum_pair (by simp [Subtype.ext_iff, hab])]
  · ext ⟨x, hx⟩
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h <;> subst h <;> simp [Subtype.ext_iff]

/-- Scheduler mass that `pe` puts on the fair transition `muA j` at the advance prefix. -/
noncomputable def pmA (pe : ProbabilisticExecution CESys) (j : ℕ) : ENNReal :=
  pe.scheduler.next (advPrefix j) (some ((Silent.τ : CELabel), muA j))

/-- Scheduler mass that `pe` puts on the unfair transition `muB j` at `advPrefix j`. -/
noncomputable def pmB (pe : ProbabilisticExecution CESys) (j : ℕ) : ENNReal :=
  pe.scheduler.next (advPrefix j) (some ((Silent.τ : CELabel), muB j))

/-- `endState` respects equality of the underlying `AlterSeq` (the termination proofs are
irrelevant). -/
private theorem endState_congr (e e' : AlterSeq CEState CELabel) (h : e = e')
    (he : e.trans.Terminates) (he' : e'.trans.Terminates) : e.endState he = e'.endState he' := by
  subst h; rfl

/-- The end-state of the advance prefix `advPrefix j` is `q j`. -/
private theorem advPrefix_endState (j : ℕ) :
    (advPrefix j).endState (advPrefix_terminates j) = CEState.q j := by
  induction j with
  | zero =>
    apply AlterSeq.endState_of_trans_nil
    simp [advPrefix, advList, Stream'.Seq.ofList_nil]
  | succ k _ =>
    have h_eq : advPrefix (k + 1) =
        ⟨CEState.q 0, (Seq.ofList (advList k)).append
          (Seq.cons ((Silent.τ : CELabel), CEState.q (k + 1)) Seq.nil)⟩ := by
      simp only [advPrefix]
      congr 1
      rw [advList_succ, Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    rw [endState_congr _ _ h_eq (advPrefix_terminates (k + 1))
      (h_eq ▸ advPrefix_terminates (k + 1))]
    exact AlterSeq.endState_append_singleton ⟨CEState.q 0, Seq.ofList (advList k)⟩
      (Stream'.Seq.terminates_ofList _) (Silent.τ : CELabel) (CEState.q (k + 1))

/-- The end-state of the exit prefix `qExitPrefix k` is `q' k`. -/
private theorem qExitPrefix_endState (k : ℕ) :
    (qExitPrefix k).endState (qExitPrefix_terminates k) = CEState.q' k := by
  have h_eq : qExitPrefix k =
      ⟨CEState.q 0, (Seq.ofList (advList k)).append
        (Seq.cons ((Silent.τ : CELabel), CEState.q' k) Seq.nil)⟩ := by
    simp only [qExitPrefix]
    congr 1
    rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
  rw [endState_congr _ _ h_eq (qExitPrefix_terminates k)
    (h_eq ▸ qExitPrefix_terminates k)]
  exact AlterSeq.endState_append_singleton ⟨CEState.q 0, Seq.ofList (advList k)⟩
    (Stream'.Seq.terminates_ofList _) (Silent.τ : CELabel) (CEState.q' k)

/-- Support restriction of `pe.scheduler.next (advPrefix j)`: any emitted `μ` at label `τ` is a
`CESys`-step from `q j`, hence `muA j` or `muB j`. -/
private theorem next_advPrefix_support (pe : ProbabilisticExecution CESys) (j : ℕ) (μ : PMF CEState)
    (hμ : some ((Silent.τ : CELabel), μ) ∈ (pe.scheduler.next (advPrefix j)).support) :
    μ = muA j ∨ μ = muB j := by
  have hstep := pe.scheduler.valid (advPrefix j) (Nat.find (advPrefix_terminates j))
    ((advPrefix j).endState (advPrefix_terminates j)) (Nat.find_spec (advPrefix_terminates j))
    (AlterSeq.stateAt_find_eq_endState _ _) (Silent.τ) μ hμ
  rw [advPrefix_endState j] at hstep
  exact hstep.2

/-- The support of `μ ↦ next (advPrefix j) (some (τ, μ)) * μ s` is contained in `{muA j, muB j}`. -/
private theorem advKernel_support (pe : ProbabilisticExecution CESys) (j : ℕ) (s : CEState) :
    (Function.support (fun μ : PMF CEState =>
      pe.scheduler.next (advPrefix j) (some ((Silent.τ : CELabel), μ)) * μ s))
      ⊆ {muA j, muB j} := by
  intro μ hμ
  have h1 : pe.scheduler.next (advPrefix j) (some ((Silent.τ : CELabel), μ)) ≠ 0 :=
    left_ne_zero_of_mul (Function.mem_support.mp hμ)
  have := next_advPrefix_support pe j μ ((PMF.mem_support_iff _ _).mpr h1)
  rcases this with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- The advancing kernel `q j → q (j+1)`: `pmA · ½ + pmB · ⅔`. -/
private theorem advK_eq (pe : ProbabilisticExecution CESys) (j : ℕ) :
    pe.kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q (j + 1))
      = pmA pe j * (1 / 2) + pmB pe j * (2 / 3) := by
  unfold ProbabilisticExecution.kernel
  rw [tsum_two_of_support _ (muA j) (muB j) (muA_ne_muB j)
    (advKernel_support pe j (CEState.q (j + 1)))]
  rw [muA_q_succ, muB_q_succ]
  rfl

/-- The exit kernel `q j → q' j`: `pmA · ½ + pmB · ⅓`. -/
private theorem exitK_eq (pe : ProbabilisticExecution CESys) (j : ℕ) :
    pe.kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q' j)
      = pmA pe j * (1 / 2) + pmB pe j * (1 / 3) := by
  unfold ProbabilisticExecution.kernel
  rw [tsum_two_of_support _ (muA j) (muB j) (muA_ne_muB j)
    (advKernel_support pe j (CEState.q' j))]
  rw [muA_q', muB_q']
  rfl

/-- Support restriction at `qExitPrefix k`: the only step from `q' k` is `(some k, pure bin)`. -/
private theorem next_qExitPrefix_support (pe : ProbabilisticExecution CESys) (k : ℕ) (l : CELabel)
    (μ : PMF CEState) (hμ : some (l, μ) ∈ (pe.scheduler.next (qExitPrefix k)).support) :
    l = some k ∧ μ = PMF.pure CEState.bin := by
  have hstep := pe.scheduler.valid (qExitPrefix k) (Nat.find (qExitPrefix_terminates k))
    ((qExitPrefix k).endState (qExitPrefix_terminates k)) (Nat.find_spec (qExitPrefix_terminates k))
    (AlterSeq.stateAt_find_eq_endState _ _) l μ hμ
  rw [qExitPrefix_endState k] at hstep
  exact hstep

/-- The external kernel `q' k → bin`: it equals the scheduler mass on `(some k, pure bin)`. -/
private theorem ext_eq (pe : ProbabilisticExecution CESys) (k : ℕ) :
    pe.kernel (qExitPrefix k) ((some k : CELabel), CEState.bin)
      = pe.scheduler.next (qExitPrefix k) (some ((some k : CELabel), PMF.pure CEState.bin)) := by
  unfold ProbabilisticExecution.kernel
  rw [tsum_eq_single (PMF.pure CEState.bin) ?_]
  · rw [PMF.pure_apply]; simp
  · intro μ hμ
    by_cases hm : pe.scheduler.next (qExitPrefix k) (some ((some k : CELabel), μ)) = 0
    · rw [hm, zero_mul]
    · exfalso
      exact hμ (next_qExitPrefix_support pe k (some k) μ ((PMF.mem_support_iff _ _).mpr hm)).2

/-! ### Step 2 — fairness consequences and the all-`μ_B` infinite run

`q j` and `q' j` are not `CEfair`-fair-deadlocks. The infinite all-`μ_B` run `muBRun` walks the
corridor `q 0 → q 1 → ⋯`, recording `muB n` at every step (never fair); it is `pe`-consistent
exactly when `pmB pe n ≠ 0` for all `n`, so an `inf_fair` scheduler must fail that somewhere. -/

/-- `q j` is not a fair deadlock: `muA j` is a fair transition from it. -/
private theorem qj_not_fairDeadlock (j : ℕ) : ¬ CEfair.FairDeadlock (CEState.q j) :=
  fun hd => hd ⟨Silent.τ, muA j, rfl, rfl⟩

/-- `q' j` is not a fair deadlock: the external step `some j` is fair from it. -/
private theorem qj'_not_fairDeadlock (j : ℕ) : ¬ CEfair.FairDeadlock (CEState.q' j) :=
  fun hd => hd ⟨some j, PMF.pure CEState.bin, rfl, rfl⟩

/-- The infinite resolved run that plays the unfair `muB n` at every corridor step, walking
`q 0 → q 1 → q 2 → ⋯` forever. -/
noncomputable def muBRun : ResolvedExec CEState CELabel :=
  ⟨CEState.q 0,
    ⟨fun n => some (((Silent.τ : CELabel), muB n), CEState.q (n + 1)),
      by intro n h; exact absurd h (by simp)⟩⟩

private theorem muBRun_get? (n : ℕ) :
    muBRun.trans.get? n = some (((Silent.τ : CELabel), muB n), CEState.q (n + 1)) := rfl

private theorem muBRun_notTerminates : ¬ muBRun.trans.Terminates := by
  rintro ⟨n, hn⟩
  rw [Stream'.Seq.TerminatedAt, muBRun_get?] at hn
  exact absurd hn (by simp)

private theorem muBRun_stateAt (n : ℕ) : muBRun.stateAt n = some (CEState.q n) := by
  cases n with
  | zero => rfl
  | succ k => change (muBRun.trans.get? k).map Prod.snd = _; rw [muBRun_get?]; rfl

private theorem muBRun_toExec_get? (n : ℕ) :
    muBRun.toExec.trans.get? n = some (((Silent.τ : CELabel), CEState.q (n + 1))) := by
  change (muBRun.trans.map _).get? n = _
  rw [Stream'.Seq.map_get?, muBRun_get?]; rfl

/-- The plain image of the length-`n` prefix of `muBRun` is the advance prefix `advPrefix n`. -/
private theorem muBRun_toExec_take (n : ℕ) : muBRun.toExec.take n = advPrefix n := by
  unfold AlterSeq.take advPrefix
  congr 1
  have hlist : muBRun.toExec.trans.take n = advList n := by
    apply List.ext_getElem?
    intro m
    by_cases hm : m < n
    · rw [seq_getElem?_take muBRun.toExec.trans n m hm, muBRun_toExec_get?, advList]
      simp [hm]
    · push Not at hm
      have hlen : (Stream'.Seq.take n muBRun.toExec.trans).length = n :=
        Stream'.Seq.length_take_of_le_length (fun h => absurd h (by
          rw [ResolvedExec.toExec_terminates_iff]; exact muBRun_notTerminates))
      rw [List.getElem?_eq_none (by rw [hlen]; exact hm),
        List.getElem?_eq_none (by rw [advList_length]; exact hm)]
  rw [hlist]

/-- `muBRun` records only unfair steps, so it takes **no** fair step at any position. -/
private theorem muBRun_no_fairStep (n : ℕ) : ¬ CEfair.FairStepAt muBRun n := by
  rintro ⟨s, l, μ, s', hs, hg, hfair⟩
  rw [muBRun_stateAt] at hs
  obtain rfl := Option.some.inj hs
  rw [muBRun_get?] at hg
  rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hg
  obtain ⟨⟨rfl, rfl⟩, _⟩ := hg
  exact absurd hfair.2.symm (muA_ne_muB n)

/-- If `pe` puts positive mass on `muB` at every corridor step, then `muBRun` is `pe`-consistent. -/
private theorem muBRun_consistent (pe : ProbabilisticExecution CESys)
    (h0 : pe.initState (CEState.q 0) ≠ 0) (hpmB : ∀ n, pmB pe n ≠ 0) :
    pe.Consistent muBRun := by
  refine ⟨h0, ?_⟩
  intro n l μ s' hget
  rw [muBRun_get?] at hget
  rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hget
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hget
  refine ⟨?_, ?_⟩
  · rw [muBRun_toExec_take n]; exact hpmB n
  · rw [muB_q_succ]; norm_num

/-- A `tsum` whose support is contained in a `Finset` collapses to the finite sum. -/
private theorem tsum_eq_sum_of_support {β : Type} (f : β → ENNReal) (s : Finset β)
    (hsupp : Function.support f ⊆ ↑s) : ∑' x, f x = ∑ x ∈ s, f x := by
  rw [tsum_eq_sum (s := s)]
  intro x hx
  by_contra h
  exact hx (hsupp (Function.mem_support.mpr h))

/-- Full support restriction at `advPrefix k`: any emitted `some (l, μ)` has `l = τ` and
`μ ∈ {muA k, muB k}`. -/
private theorem next_advPrefix_support_full (pe : ProbabilisticExecution CESys) (k : ℕ)
    (l : CELabel) (μ : PMF CEState)
    (hμ : some (l, μ) ∈ (pe.scheduler.next (advPrefix k)).support) :
    l = Silent.τ ∧ (μ = muA k ∨ μ = muB k) := by
  have hstep := pe.scheduler.valid (advPrefix k) (Nat.find (advPrefix_terminates k))
    ((advPrefix k).endState (advPrefix_terminates k)) (Nat.find_spec (advPrefix_terminates k))
    (AlterSeq.stateAt_find_eq_endState _ _) l μ hμ
  rw [advPrefix_endState k] at hstep
  exact hstep

/-- **No halt at `q k` ⇒ full step mass.** If `pe` never halts at the advance prefix `advPrefix k`,
then its two step masses sum to one: `pmA + pmB = 1`. -/
private theorem pmA_add_pmB_of_no_halt (pe : ProbabilisticExecution CESys) (k : ℕ)
    (hnohalt : pe.scheduler.next (advPrefix k) none = 0) : pmA pe k + pmB pe k = 1 := by
  classical
  have htot : ∑' o, pe.scheduler.next (advPrefix k) o = 1 :=
    (pe.scheduler.next (advPrefix k)).tsum_coe
  set S : Finset (Option (CELabel × PMF CEState)) :=
    {none, some ((Silent.τ : CELabel), muA k), some ((Silent.τ : CELabel), muB k)} with hSdef
  have hsupp : Function.support (fun o => pe.scheduler.next (advPrefix k) o) ⊆ ↑S := by
    intro o ho
    have hne := Function.mem_support.mp ho
    match o with
    | none => simp [hSdef]
    | some (l, μ) =>
      obtain ⟨rfl, hm⟩ :=
        next_advPrefix_support_full pe k l μ ((PMF.mem_support_iff _ _).mpr hne)
      rcases hm with rfl | rfl <;> simp [hSdef]
  rw [tsum_eq_sum_of_support _ S hsupp] at htot
  have hne1 : (none : Option (CELabel × PMF CEState)) ∉
      ({some ((Silent.τ : CELabel), muA k), some ((Silent.τ : CELabel), muB k)} :
        Finset (Option (CELabel × PMF CEState))) := by simp
  have hne2 : some ((Silent.τ : CELabel), muA k) ∉
      ({some ((Silent.τ : CELabel), muB k)} : Finset (Option (CELabel × PMF CEState))) := by
    simp [muA_ne_muB k]
  rw [hSdef, Finset.sum_insert hne1, Finset.sum_insert hne2, Finset.sum_singleton, hnohalt,
    zero_add] at htot
  exact htot

/-- **The all-unfair contradiction.** No `CEfair`-fair `pe` starting at `q 0` can put positive mass
on `muB` at *every* corridor step: `muBRun` would then be an infinite consistent run with no fair
step, contradicting `inf_fair`. -/
private theorem not_all_pmB_pos (pe : ProbabilisticExecution CESys)
    (h0 : pe.initState (CEState.q 0) ≠ 0) (hfair : pe.IsFair CEfair) :
    ¬ ∀ n, pmB pe n ≠ 0 := by
  intro hpmB
  obtain ⟨n, _, hfairstep⟩ :=
    hfair.inf_fair muBRun muBRun_notTerminates (muBRun_consistent pe h0 hpmB) 0
  exact muBRun_no_fairStep n hfairstep

/-! ### Reachability of `q k` for a plain `pe`

To use `IsFair.halt_fairDeadlock` at `q k` we need a *finite consistent resolved run* reaching it.
When `pe` has a positive advancing kernel at every earlier step, the run `reachRun pe k`, decorating
the advance with a `μ ∈ {muA i, muB i}` of positive mass, is consistent, ends at `q k`,
and has plain image `advPrefix k`. -/

open Classical in
/-- A distribution of positive scheduler mass among `{muA j, muB j}` (used to decorate a reaching
run). If `pe` puts positive mass on `muA j` we pick it, else `muB j`. -/
noncomputable def chooseμ (pe : ProbabilisticExecution CESys) (j : ℕ) : PMF CEState :=
  if pmA pe j ≠ 0 then muA j else muB j

/-- `chooseμ pe j` lands on `q (j+1)` with positive probability. -/
private theorem chooseμ_lands (pe : ProbabilisticExecution CESys) (j : ℕ) :
    chooseμ pe j (CEState.q (j + 1)) ≠ 0 := by
  unfold chooseμ
  split
  · rw [muA_q_succ]; norm_num
  · rw [muB_q_succ]; norm_num

/-- If the advancing kernel at `advPrefix j` is positive, `pe` puts positive mass on the chosen
transition. -/
private theorem chooseμ_next_ne (pe : ProbabilisticExecution CESys) (j : ℕ)
    (hadv : pe.kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q (j + 1)) ≠ 0) :
    pe.scheduler.next (advPrefix j) (some ((Silent.τ : CELabel), chooseμ pe j)) ≠ 0 := by
  unfold chooseμ
  by_cases hA : pmA pe j ≠ 0
  · rw [if_pos hA]; exact hA
  · rw [if_neg hA]
    push Not at hA
    intro hpB
    apply hadv
    rw [advK_eq, hA]
    change pmB pe j = 0 at hpB
    rw [hpB]; simp

/-- The finite resolved run decorating the advance `q 0 → ⋯ → q k` with the chosen transitions. -/
noncomputable def reachRun (pe : ProbabilisticExecution CESys) (k : ℕ) :
    ResolvedExec CEState CELabel :=
  ⟨CEState.q 0, Seq.ofList ((List.range k).map
    (fun i => (((Silent.τ : CELabel), chooseμ pe i), CEState.q (i + 1))))⟩

private theorem reachRun_terminates (pe : ProbabilisticExecution CESys) (k : ℕ) :
    (reachRun pe k).trans.Terminates := Stream'.Seq.terminates_ofList _

private theorem reachRun_trans_get? (pe : ProbabilisticExecution CESys) (k n : ℕ) (hn : n < k) :
    (reachRun pe k).trans.get? n
      = some (((Silent.τ : CELabel), chooseμ pe n), CEState.q (n + 1)) := by
  change (Seq.ofList _).get? n = _
  rw [Stream'.Seq.ofList_get?, List.getElem?_map, List.getElem?_range hn]; rfl

private theorem reachRun_trans_none (pe : ProbabilisticExecution CESys) (k n : ℕ) (hn : k ≤ n) :
    (reachRun pe k).trans.get? n = none := by
  change (Seq.ofList _).get? n = none
  rw [Stream'.Seq.ofList_get?, List.getElem?_eq_none]
  rw [List.length_map, List.length_range]; omega

private theorem reachRun_toExec (pe : ProbabilisticExecution CESys) (k : ℕ) :
    (reachRun pe k).toExec = advPrefix k := by
  unfold ResolvedExec.toExec advPrefix
  congr 1
  apply Stream'.Seq.ext
  intro n
  by_cases hn : n < k
  · rw [Stream'.Seq.map_get?, reachRun_trans_get? pe k n hn, Stream'.Seq.ofList_get?, advList,
      List.getElem?_map, List.getElem?_range hn]; rfl
  · push Not at hn
    rw [Stream'.Seq.map_get?, reachRun_trans_none pe k n hn, Stream'.Seq.ofList_get?, advList,
      List.getElem?_map, List.getElem?_eq_none (by rw [List.length_range]; omega)]; rfl

/-- The end-state of a resolved run equals that of its plain image (the visited states agree). -/
private theorem endState_toExec (r : ResolvedExec CEState CELabel) (h : r.trans.Terminates) :
    r.endState h = r.toExec.endState ((ResolvedExec.toExec_terminates_iff r).mpr h) := by
  have h' := (ResolvedExec.toExec_terminates_iff r).mpr h
  have hfind : Nat.find h = Nat.find h' :=
    Nat.find_congr' (fun {n} => (ResolvedExec.toExec_terminatedAt_iff r n).symm)
  apply Option.some.inj
  rw [← AlterSeq.stateAt_find_eq_endState r h, ← AlterSeq.stateAt_find_eq_endState r.toExec h',
    ← hfind, ResolvedExec.toExec_stateAt]

private theorem reachRun_endState (pe : ProbabilisticExecution CESys) (k : ℕ) :
    (reachRun pe k).endState (reachRun_terminates pe k) = CEState.q k := by
  rw [endState_toExec, endState_congr _ _ (reachRun_toExec pe k) _ (advPrefix_terminates k),
    advPrefix_endState k]

/-- Prefix of the advance prefix is a smaller advance prefix. -/
private theorem advPrefix_take (k n : ℕ) (hn : n ≤ k) : (advPrefix k).take n = advPrefix n := by
  unfold AlterSeq.take advPrefix
  congr 1
  have hlist : Stream'.Seq.take n (Seq.ofList (advList k)) = advList n := by
    apply List.ext_getElem?
    intro m
    by_cases hm : m < n
    · rw [seq_getElem?_take (Seq.ofList (advList k)) n m hm, Stream'.Seq.ofList_get?,
        advList, advList, List.getElem?_map, List.getElem?_map, List.getElem?_range (by omega),
        List.getElem?_range hm]
    · push Not at hm
      rw [List.getElem?_eq_none (le_trans Stream'.Seq.length_take_le hm),
        List.getElem?_eq_none (by rw [advList_length]; exact hm)]
  rw [hlist]

/-- `reachRun pe k` is `pe`-consistent, provided every earlier advancing kernel is positive. -/
private theorem reachRun_consistent (pe : ProbabilisticExecution CESys)
    (h0 : pe.initState (CEState.q 0) ≠ 0)
    (hadv : ∀ j < k, pe.kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q (j + 1)) ≠ 0) :
    pe.Consistent (reachRun pe k) := by
  refine ⟨h0, ?_⟩
  intro n l μ s' hget
  rcases lt_or_ge n k with hn | hn
  · rw [reachRun_trans_get? pe k n hn, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hget
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hget
    refine ⟨?_, ?_⟩
    · rw [reachRun_toExec pe k, advPrefix_take k n (le_of_lt hn)]
      exact chooseμ_next_ne pe n (hadv n hn)
    · exact chooseμ_lands pe n
  · rw [reachRun_trans_none pe k n hn] at hget; exact absurd hget.symm (by simp)

/-- **No halt at a reachable `q k`.** For a `CEfair`-fair `pe` from `q 0` with all earlier advancing
kernels positive, `pe` cannot halt at `q k` (else `q k` would be a fair deadlock). So its two step
masses sum to one. -/
private theorem pmA_add_pmB_reachable (pe : ProbabilisticExecution CESys)
    (h0 : pe.initState (CEState.q 0) ≠ 0) (hfair : pe.IsFair CEfair) (k : ℕ)
    (hadv : ∀ j < k, pe.kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q (j + 1)) ≠ 0) :
    pmA pe k + pmB pe k = 1 := by
  apply pmA_add_pmB_of_no_halt
  by_contra hnone
  have hcons := reachRun_consistent pe h0 hadv
  have := hfair.halt_fairDeadlock (reachRun pe k) (reachRun_terminates pe k) hcons
    (by rw [reachRun_toExec pe k]; exact hnone)
  rw [reachRun_endState pe k] at this
  exact qj_not_fairDeadlock k this

/-- The decorated run reaching `q' k`: extend `reachRun pe k` by the exit step `q k → q' k`. -/
noncomputable def reachExitList (pe : ProbabilisticExecution CESys) (k : ℕ) :
    List ((CELabel × PMF CEState) × CEState) :=
  ((List.range k).map (fun i => (((Silent.τ : CELabel), chooseμ pe i), CEState.q (i + 1))))
    ++ [(((Silent.τ : CELabel), chooseμ pe k), CEState.q' k)]

noncomputable def reachRunExit (pe : ProbabilisticExecution CESys) (k : ℕ) :
    ResolvedExec CEState CELabel := ⟨CEState.q 0, Seq.ofList (reachExitList pe k)⟩

private theorem reachRunExit_terminates (pe : ProbabilisticExecution CESys) (k : ℕ) :
    (reachRunExit pe k).trans.Terminates := Stream'.Seq.terminates_ofList _

private theorem reachRunExit_get?_lt (pe : ProbabilisticExecution CESys) (k n : ℕ) (hn : n < k) :
    (reachRunExit pe k).trans.get? n
      = some (((Silent.τ : CELabel), chooseμ pe n), CEState.q (n + 1)) := by
  change (Seq.ofList _).get? n = _
  rw [Stream'.Seq.ofList_get?, reachExitList, List.getElem?_append_left (by
    rw [List.length_map, List.length_range]; omega), List.getElem?_map, List.getElem?_range hn]; rfl

private theorem reachRunExit_get?_k (pe : ProbabilisticExecution CESys) (k : ℕ) :
    (reachRunExit pe k).trans.get? k
      = some (((Silent.τ : CELabel), chooseμ pe k), CEState.q' k) := by
  change (Seq.ofList _).get? k = _
  rw [Stream'.Seq.ofList_get?, reachExitList, List.getElem?_append_right (by
    rw [List.length_map, List.length_range]), List.length_map, List.length_range]
  simp

private theorem reachRunExit_get?_gt (pe : ProbabilisticExecution CESys) (k n : ℕ) (hn : k < n) :
    (reachRunExit pe k).trans.get? n = none := by
  change (Seq.ofList _).get? n = none
  rw [Stream'.Seq.ofList_get?, List.getElem?_eq_none]
  rw [reachExitList, List.length_append, List.length_map, List.length_range, List.length_singleton]
  omega

private theorem reachRunExit_toExec (pe : ProbabilisticExecution CESys) (k : ℕ) :
    (reachRunExit pe k).toExec = qExitPrefix k := by
  unfold ResolvedExec.toExec qExitPrefix reachRunExit
  congr 1
  have hmap : (reachExitList pe k).map (fun p => (p.1.1, p.2))
      = advList k ++ [((Silent.τ : CELabel), CEState.q' k)] := by
    rw [reachExitList, List.map_append, advList, List.map_map]; rfl
  apply Stream'.Seq.ext
  intro n
  rw [Stream'.Seq.map_get?]
  change Option.map _ ((Seq.ofList (reachExitList pe k)).get? n) = _
  rw [Stream'.Seq.ofList_get?, Stream'.Seq.ofList_get?, ← List.getElem?_map, hmap]

private theorem reachRunExit_endState (pe : ProbabilisticExecution CESys) (k : ℕ) :
    (reachRunExit pe k).endState (reachRunExit_terminates pe k) = CEState.q' k := by
  rw [endState_toExec, endState_congr _ _ (reachRunExit_toExec pe k) _ (qExitPrefix_terminates k),
    qExitPrefix_endState k]

/-- Prefix of the exit prefix below `k` is a smaller advance prefix. -/
private theorem qExitPrefix_take (k n : ℕ) (hn : n ≤ k) :
    (qExitPrefix k).take n = advPrefix n := by
  unfold AlterSeq.take qExitPrefix advPrefix
  congr 1
  have hlist : Stream'.Seq.take n (Seq.ofList (advList k ++ [((Silent.τ : CELabel), CEState.q' k)]))
      = advList n := by
    apply List.ext_getElem?
    intro m
    by_cases hm : m < n
    · rw [seq_getElem?_take _ n m hm, Stream'.Seq.ofList_get?,
        List.getElem?_append_left (by rw [advList_length]; omega), advList, advList,
        List.getElem?_map, List.getElem?_map, List.getElem?_range (by omega),
        List.getElem?_range hm]
    · push Not at hm
      rw [List.getElem?_eq_none (le_trans Stream'.Seq.length_take_le hm),
        List.getElem?_eq_none (by rw [advList_length]; exact hm)]
  rw [hlist]

/-- The chosen `μ` at the exit step has positive scheduler mass when the exit kernel is positive. -/
private theorem chooseμ_next_ne_exit (pe : ProbabilisticExecution CESys) (k : ℕ)
    (hexit : pe.kernel (advPrefix k) ((Silent.τ : CELabel), CEState.q' k) ≠ 0) :
    pe.scheduler.next (advPrefix k) (some ((Silent.τ : CELabel), chooseμ pe k)) ≠ 0 := by
  unfold chooseμ
  by_cases hA : pmA pe k ≠ 0
  · rw [if_pos hA]; exact hA
  · rw [if_neg hA]
    push Not at hA
    intro hpB
    apply hexit
    rw [exitK_eq, hA]
    change pmB pe k = 0 at hpB
    rw [hpB]; simp

/-- `chooseμ pe k` lands on `q' k` with positive probability. -/
private theorem chooseμ_lands_exit (pe : ProbabilisticExecution CESys) (k : ℕ) :
    chooseμ pe k (CEState.q' k) ≠ 0 := by
  unfold chooseμ
  split
  · rw [muA_q']; norm_num
  · rw [muB_q']; norm_num

/-- `reachRunExit pe k` is `pe`-consistent (earlier advancing kernels positive, exit kernel at `k`
positive). -/
private theorem reachRunExit_consistent (pe : ProbabilisticExecution CESys)
    (h0 : pe.initState (CEState.q 0) ≠ 0)
    (hadv : ∀ j < k, pe.kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q (j + 1)) ≠ 0)
    (hexit : pe.kernel (advPrefix k) ((Silent.τ : CELabel), CEState.q' k) ≠ 0) :
    pe.Consistent (reachRunExit pe k) := by
  refine ⟨h0, ?_⟩
  intro n l μ s' hget
  rcases lt_trichotomy n k with hn | hn | hn
  · rw [reachRunExit_get?_lt pe k n hn, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hget
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hget
    refine ⟨?_, chooseμ_lands pe n⟩
    rw [reachRunExit_toExec pe k, qExitPrefix_take k n (le_of_lt hn)]
    exact chooseμ_next_ne pe n (hadv n hn)
  · subst hn
    rw [reachRunExit_get?_k pe n, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hget
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hget
    refine ⟨?_, chooseμ_lands_exit pe n⟩
    rw [reachRunExit_toExec pe n, qExitPrefix_take n n (le_refl n)]
    exact chooseμ_next_ne_exit pe n hexit
  · rw [reachRunExit_get?_gt pe k n hn] at hget; exact absurd hget.symm (by simp)

/-- **`ext = 1` at a reachable `q' k`.** For a fair `pe` reaching `q' k`, the only step is the
external `(some k, pure bin)`: no halt (q' k not a fair deadlock), and validity leaves only that
emission — so the external kernel is one. -/
private theorem ext_one_reachable (pe : ProbabilisticExecution CESys)
    (h0 : pe.initState (CEState.q 0) ≠ 0) (hfair : pe.IsFair CEfair) (k : ℕ)
    (hadv : ∀ j < k, pe.kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q (j + 1)) ≠ 0)
    (hexit : pe.kernel (advPrefix k) ((Silent.τ : CELabel), CEState.q' k) ≠ 0) :
    pe.kernel (qExitPrefix k) ((some k : CELabel), CEState.bin) = 1 := by
  classical
  have hnone : pe.scheduler.next (qExitPrefix k) none = 0 := by
    by_contra hn
    have hcons := reachRunExit_consistent pe h0 hadv hexit
    have := hfair.halt_fairDeadlock (reachRunExit pe k) (reachRunExit_terminates pe k) hcons
      (by rw [reachRunExit_toExec pe k]; exact hn)
    rw [reachRunExit_endState pe k] at this
    exact qj'_not_fairDeadlock k this
  rw [ext_eq]
  have htot : ∑' o, pe.scheduler.next (qExitPrefix k) o = 1 :=
    (pe.scheduler.next (qExitPrefix k)).tsum_coe
  set S : Finset (Option (CELabel × PMF CEState)) :=
    {none, some ((some k : CELabel), PMF.pure CEState.bin)} with hSdef
  have hsupp : Function.support (fun o => pe.scheduler.next (qExitPrefix k) o) ⊆ ↑S := by
    intro o ho
    have hne := Function.mem_support.mp ho
    match o with
    | none => simp [hSdef]
    | some (l, μ) =>
      obtain ⟨rfl, rfl⟩ :=
        next_qExitPrefix_support pe k l μ ((PMF.mem_support_iff _ _).mpr hne)
      simp [hSdef]
  rw [tsum_eq_sum_of_support _ S hsupp] at htot
  have hne1 : (none : Option (CELabel × PMF CEState)) ∉
      ({some ((some k : CELabel), PMF.pure CEState.bin)} :
        Finset (Option (CELabel × PMF CEState))) := by simp
  rw [hSdef, Finset.sum_insert hne1, Finset.sum_singleton, hnone, zero_add] at htot
  exact htot

/-! ### Step 3 — the resolved witness `peR.average` and its exit rate below ½

`peR.average` is a *plain* scheduler realising `D_CE` (`traceProb_average`). It never halts on the
corridor (`sigmaR` only emits `none` at `bin`), so `pmA + pmB = 1` and `ext = 1` there; and it plays
`muB` with positive posterior mass (`avg_pmB_pos`), pushing its per-step exit rate strictly below
½. -/

/-- Shorthand: the advancing / exit / external kernels of the resolved witness `peR.average`. -/
private noncomputable def advKR (j : ℕ) : ENNReal :=
  (peR.average).kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q (j + 1))
private noncomputable def exitKR (k : ℕ) : ENNReal :=
  (peR.average).kernel (advPrefix k) ((Silent.τ : CELabel), CEState.q' k)

/-- The initial distribution of `peR.average` is the Dirac at `q 0`. -/
private theorem avg_initState : (peR.average).initState = PMF.pure (CEState.q 0) := rfl

/-- Every decoration of `advPrefix j` ends at `q j`. -/
private theorem decoration_advPrefix_endState (j : ℕ)
    (r' : {r' : ResolvedExec CEState CELabel // r'.toExec = advPrefix j}) :
    r'.1.endState (ResolvedExec.terminates_of_toExec_eq (advPrefix_terminates j) r'.2)
      = CEState.q j := by
  rw [endState_toExec, endState_congr _ _ r'.2 _ (advPrefix_terminates j), advPrefix_endState]

/-- Every decoration of `qExitPrefix k` ends at `q' k`. -/
private theorem decoration_qExitPrefix_endState (k : ℕ)
    (r' : {r' : ResolvedExec CEState CELabel // r'.toExec = qExitPrefix k}) :
    r'.1.endState (ResolvedExec.terminates_of_toExec_eq (qExitPrefix_terminates k) r'.2)
      = CEState.q' k := by
  rw [endState_toExec, endState_congr _ _ r'.2 _ (qExitPrefix_terminates k), qExitPrefix_endState]

/-- The scheduler mass `pmB` is at most one (it is a coordinate of a `PMF`). -/
private theorem pmB_le_one (pe : ProbabilisticExecution CESys) (j : ℕ) : pmB pe j ≤ 1 :=
  PMF.coe_le_one _ _

/-! ### The unfair-play witness `decB j`

To show `peR.average` plays `muB j` with positive posterior mass we exhibit one `sigmaR`-decoration
of `advPrefix j` that reaches `q j` and — reading its own `μ`-history — plays `muB j` next. The
decoration records at step `i` the distribution `muPat j i`, alternating so that its *last* step
(`i = j-1`) is the fair `muA (j-1)`; then `sigmaR` at `q j` plays PURE `muB j`. -/

/-- The recorded distribution at step `i` of the unfair-play decoration of `advPrefix j`: it
alternates so that step `j-1` is fair (`muA (j-1)`). -/
noncomputable def muPat (j i : ℕ) : PMF CEState := if (i + j) % 2 = 0 then muB i else muA i

/-- `muPat j i` lands on `q (i+1)` with positive mass (both `muA`/`muB` advance). -/
private theorem muPat_lands (j i : ℕ) : muPat j i (CEState.q (i + 1)) ≠ 0 := by
  unfold muPat
  split
  · rw [muB_q_succ]; norm_num
  · rw [muA_q_succ]; norm_num

/-- The last step of `decB j` (position `j-1`, for `j ≥ 1`) is the fair transition `muA (j-1)`. -/
private theorem muPat_last (j : ℕ) (hj : 1 ≤ j) : muPat j (j - 1) = muA (j - 1) := by
  unfold muPat
  rw [if_neg]
  have : (j - 1) + j = 2 * j - 1 := by omega
  rw [this]
  omega

/-- The finite resolved run decorating `q 0 → ⋯ → q j` with the alternating `muPat j` steps. -/
noncomputable def decB (j : ℕ) : ResolvedExec CEState CELabel :=
  ⟨CEState.q 0, Seq.ofList ((List.range j).map
    (fun i => (((Silent.τ : CELabel), muPat j i), CEState.q (i + 1))))⟩

private theorem decB_terminates (j : ℕ) : (decB j).trans.Terminates :=
  Stream'.Seq.terminates_ofList _

private theorem decB_trans_get? (j n : ℕ) (hn : n < j) :
    (decB j).trans.get? n = some (((Silent.τ : CELabel), muPat j n), CEState.q (n + 1)) := by
  change (Seq.ofList _).get? n = _
  rw [Stream'.Seq.ofList_get?, List.getElem?_map, List.getElem?_range hn]; rfl

private theorem decB_trans_none (j n : ℕ) (hn : j ≤ n) : (decB j).trans.get? n = none := by
  change (Seq.ofList _).get? n = none
  rw [Stream'.Seq.ofList_get?, List.getElem?_eq_none]
  rw [List.length_map, List.length_range]; omega

private theorem decB_toExec (j : ℕ) : (decB j).toExec = advPrefix j := by
  unfold ResolvedExec.toExec advPrefix
  congr 1
  apply Stream'.Seq.ext
  intro n
  by_cases hn : n < j
  · rw [Stream'.Seq.map_get?, decB_trans_get? j n hn, Stream'.Seq.ofList_get?, advList,
      List.getElem?_map, List.getElem?_range hn]; rfl
  · push Not at hn
    rw [Stream'.Seq.map_get?, decB_trans_none j n hn, Stream'.Seq.ofList_get?, advList,
      List.getElem?_map, List.getElem?_eq_none (by rw [List.length_range]; omega)]; rfl

private theorem decB_endState (j : ℕ) :
    (decB j).endState (decB_terminates j) = CEState.q j := by
  rw [endState_toExec, endState_congr _ _ (decB_toExec j) _ (advPrefix_terminates j),
    advPrefix_endState j]

/-- The `n`-prefix of `decB j` (for `n ≤ j`) is the corresponding prefix of `decB`; its transitions
below `n` agree with `decB j`. -/
private theorem decB_take_trans_get? (j n m : ℕ) (hm : m < n) :
    ((decB j).take n).trans.get? m = (decB j).trans.get? m := by
  change (Seq.ofList (Seq.take n (decB j).trans)).get? m = _
  rw [Stream'.Seq.ofList_get?, seq_getElem?_take (decB j).trans n m hm]

private theorem decB_take_terminates (j n : ℕ) : ((decB j).take n).trans.Terminates :=
  Stream'.Seq.terminates_ofList _

/-- The `n`-prefix of `decB j` (for `n ≤ j`) ends at `q n`: it decorates `advPrefix n`. -/
private theorem decB_take_endState (j n : ℕ) (hn : n ≤ j) :
    ((decB j).take n).endState (decB_take_terminates j n) = CEState.q n := by
  have htoExec : ResolvedExec.toExec ((decB j).take n) = advPrefix n := by
    rw [ResolvedExec.toExec_take, decB_toExec, advPrefix_take j n hn]
  rw [endState_toExec, endState_congr _ _ htoExec _ (advPrefix_terminates n),
    advPrefix_endState n]

/-- `probOfR` respects equality of the underlying run (termination proofs are irrelevant). -/
private theorem probOfR_congr' (r r' : ResolvedExec CEState CELabel) (h : r = r')
    (hr : r.trans.Terminates) (hr' : r'.trans.Terminates) :
    peR.probOfR r hr = peR.probOfR r' hr' := by subst h; rfl

/-- `Seq.take` of a `Seq.ofList` is `List.take` (local copy; `Weak.Scheduler` is not imported). -/
private theorem take_ofList_local {γ : Type} (L : List γ) (k : ℕ) :
    Stream'.Seq.take k (Stream'.Seq.ofList L) = L.take k := by
  induction k generalizing L with
  | zero => simp [Stream'.Seq.take]
  | succ n ih =>
    cases L with
    | nil => simp [Stream'.Seq.take]
    | cons a t =>
      rw [Stream'.Seq.ofList_cons, Stream'.Seq.take_succ_cons, List.take_succ_cons, ih]

open Classical in
/-- At the `i`-prefix of `decB j` (`i < j`), `sigmaR` plays the recorded transition `muPat j i` with
positive mass. For `i = 0` this is the initial coin (both `muA 0`/`muB 0` have mass ½); for `i ≥ 1`
it is the pure alternation, which reads `muPat j (i-1)` and emits `muPat j i` by parity. -/
private theorem sigmaR_plays_muPat (j i : ℕ) (hi : i < j) :
    sigmaR.next ((decB j).take i) (some ((Silent.τ : CELabel), muPat j i)) ≠ 0 := by
  have hterm := decB_take_terminates j i
  have hend := decB_take_endState j i (le_of_lt hi)
  rw [sigmaR]; simp only [dif_pos hterm, hend]
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    rw [if_pos rfl, PMF.map_apply, tsum_bool]
    have hmuPat0 : muPat j 0 = muA 0 ∨ muPat j 0 = muB 0 := by
      unfold muPat; split
      · exact Or.inr rfl
      · exact Or.inl rfl
    rcases hmuPat0 with h0 | h0
    · rw [h0]; intro hz; rw [add_eq_zero] at hz
      obtain ⟨_, hz2⟩ := hz
      rw [if_pos (by simp), PMF.bernoulli_apply] at hz2; simp at hz2
    · rw [h0]; intro hz; rw [add_eq_zero] at hz
      obtain ⟨hz1, _⟩ := hz
      rw [if_pos (by simp), PMF.bernoulli_apply] at hz1; simp at hz1
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hipos.ne'
    rw [if_neg (Nat.succ_ne_zero n)]
    have hlast : (((decB j).take (n + 1)).trans.get? ((n + 1) - 1)).map (fun p => p.1.2)
        = some (muPat j n) := by
      rw [Nat.add_sub_cancel, decB_take_trans_get? j (n + 1) n (Nat.lt_succ_self n),
        decB_trans_get? j n (by omega)]; rfl
    rw [hlast, Nat.succ_sub_one]
    by_cases hA : muPat j n = muA n
    · have hne : muPat j (n + 1) = muB (n + 1) := by
        unfold muPat
        rw [if_pos]
        have hp0 : (n + j) % 2 ≠ 0 := by
          intro hc; unfold muPat at hA; rw [if_pos hc] at hA; exact (muA_ne_muB n) hA.symm
        omega
      rw [if_pos (by rw [hA]), hne, PMF.pure_apply]; simp
    · have hB : muPat j n = muB n := by
        unfold muPat at hA ⊢
        by_cases hp0 : (n + j) % 2 = 0
        · rw [if_pos hp0]
        · rw [if_neg hp0] at hA; exact absurd rfl hA
      have hne : muPat j (n + 1) = muA (n + 1) := by
        unfold muPat
        rw [if_neg]
        have hp0 : (n + j) % 2 = 0 := by
          by_contra hc; unfold muPat at hB; rw [if_neg hc] at hB; exact (muA_ne_muB n) hB
        omega
      rw [if_neg (by rw [hB]; exact fun hc => (muA_ne_muB n) (Option.some.inj hc).symm), hne,
        PMF.pure_apply]; simp

/-- The transition list of `decB j`. -/
private noncomputable def decBList (j : ℕ) : List ((CELabel × PMF CEState) × CEState) :=
  (List.range j).map (fun i => (((Silent.τ : CELabel), muPat j i), CEState.q (i + 1)))

private theorem decBList_length (j : ℕ) : (decBList j).length = j := by
  rw [decBList, List.length_map, List.length_range]

/-- The `k`-prefix of `decB j` reads off the first `k` entries of `decBList j`. -/
private theorem decB_take_eq (j k : ℕ) :
    (decB j).take k = ⟨CEState.q 0, Seq.ofList ((decBList j).take k)⟩ := by
  unfold AlterSeq.take decB decBList
  congr 1
  rw [take_ofList_local]

/-- The `(k+1)`-prefix of `decB j` (`k < j`) is the `k`-prefix appended with the `k`-th step. -/
private theorem decB_take_succ_append (j k : ℕ) (hk : k < j) :
    (decB j).take (k + 1) =
      ⟨CEState.q 0, ((decB j).take k).trans.append
        (Seq.cons (((Silent.τ : CELabel), muPat j k), CEState.q (k + 1)) Seq.nil)⟩ := by
  have hget : (decBList j).take (k + 1)
      = (decBList j).take k ++ [(((Silent.τ : CELabel), muPat j k), CEState.q (k + 1))] := by
    rw [List.take_succ]
    congr 1
    rw [decBList, List.getElem?_map, List.getElem?_range hk]; rfl
  rw [decB_take_eq j (k + 1), hget, Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons,
    Stream'.Seq.ofList_nil]
  change (⟨CEState.q 0, _⟩ : ResolvedExec CEState CELabel) = _
  rw [decB_take_eq j k]

/-- **`probOfR ((decB j).take k) ≠ 0`** (`k ≤ j`). Each of its steps has positive `rkernel`:
`sigmaR` plays `muPat j i` (`sigmaR_plays_muPat`) and `muPat j i` advances (`muPat_lands`). -/
private theorem probOfR_decB_take_ne_zero (j k : ℕ) (hk : k ≤ j) :
    peR.probOfR ((decB j).take k) (decB_take_terminates j k) ≠ 0 := by
  induction k with
  | zero =>
    have h0 : (decB j).take 0 = ⟨CEState.q 0, Seq.nil⟩ := by
      rw [decB_take_eq j 0, List.take_zero, Stream'.Seq.ofList_nil]
    rw [probOfR_congr' _ _ h0 (decB_take_terminates j 0) Stream'.Seq.terminates_nil,
      peR.probOfR_nil]
    change (PMF.pure CESys.init) (CEState.q 0) ≠ 0
    have : CESys.init = CEState.q 0 := rfl
    rw [this, PMF.pure_apply_self]; norm_num
  | succ k ih =>
    have hklt : k < j := hk
    have happ := decB_take_succ_append j k hklt
    have htermApp : (((decB j).take k).trans.append
        (Seq.cons (((Silent.τ : CELabel), muPat j k), CEState.q (k + 1)) Seq.nil)).Terminates := by
      have := decB_take_terminates j (k + 1); rwa [happ] at this
    rw [probOfR_congr' _ _ happ (decB_take_terminates j (k + 1)) htermApp,
      peR.probOfR_append_singleton (CEState.q 0) ((decB j).take k).trans
      (decB_take_terminates j k) _ htermApp]
    apply mul_ne_zero
    · exact ih (le_of_lt hklt)
    · rw [ResolvedProbabilisticExecution.rkernel]
      apply mul_ne_zero
      · exact sigmaR_plays_muPat j k hklt
      · exact muPat_lands j k

/-- `decB j` is its own length-`j` prefix. -/
private theorem decB_take_self (j : ℕ) : (decB j).take j = decB j := by
  rw [decB_take_eq j j]
  unfold decB decBList
  rw [List.take_of_length_le (le_of_eq (by rw [List.length_map, List.length_range]))]

open Classical in
/-- **The final move of `decB j` is `muB j`.** `sigmaR` at the full decoration (ending at `q j`)
plays `some (τ, muB j)` with positive mass: for `j = 0` via the initial coin (mass ½), and for
`j ≥ 1` via the pure alternation reading the last step `muPat j (j-1) = muA (j-1)`. -/
private theorem sigmaR_decB_plays_muB (j : ℕ) :
    sigmaR.next (decB j) (some ((Silent.τ : CELabel), muB j)) ≠ 0 := by
  have hend := decB_endState j
  rw [sigmaR]; simp only [dif_pos (decB_terminates j), hend]
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    rw [if_pos rfl, PMF.map_apply, tsum_bool]
    intro hz; rw [add_eq_zero] at hz
    obtain ⟨hz1, _⟩ := hz
    rw [if_pos (by simp), PMF.bernoulli_apply] at hz1; simp at hz1
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjpos.ne'
    rw [if_neg (Nat.succ_ne_zero n)]
    have hlast : ((decB (n + 1)).trans.get? ((n + 1) - 1)).map (fun p => p.1.2)
        = some (muPat (n + 1) n) := by
      rw [Nat.add_sub_cancel, decB_trans_get? (n + 1) n (Nat.lt_succ_self n)]; rfl
    have hmuA : muPat (n + 1) n = muA n := by
      have := muPat_last (n + 1) (by omega)
      rwa [Nat.add_sub_cancel] at this
    rw [hlast, hmuA, Nat.succ_sub_one, if_pos rfl, PMF.pure_apply]; simp

/-- `peR.average` plays the unfair transition `muB j` with strictly positive posterior mass.
Witnessed by the `sigmaR`-decoration `decB j` of `advPrefix j`: it reaches `q j` (`decB_toExec`),
has positive `probOfR` (`probOfR_decB_take_ne_zero`), and plays `muB j` next
(`sigmaR_decB_plays_muB`). Feeding this single decoration into `average_next_some` (via `le_tsum`)
makes the posterior marginal strictly positive. -/
private theorem avg_pmB_pos (j : ℕ) : 0 < pmB (peR.average) j := by
  rw [pos_iff_ne_zero, pmB, peR.average_next_some (advPrefix j) (advPrefix_terminates j)
    (Silent.τ) (muB j)]
  apply mul_ne_zero _ (by
    rw [ENNReal.inv_ne_zero]
    exact (((peR.avgWeight_le_init (advPrefix j) (advPrefix_terminates j)).trans
      (PMF.coe_le_one _ _)).trans_lt ENNReal.one_lt_top).ne)
  -- The single decoration `decB j` contributes positively to the numerator.
  have hr' : (decB j).toExec = advPrefix j := decB_toExec j
  set r' : {r' : ResolvedExec CEState CELabel // r'.toExec = advPrefix j} := ⟨decB j, hr'⟩
  have hterm : (decB j).trans.Terminates :=
    ResolvedExec.terminates_of_toExec_eq (advPrefix_terminates j) r'.2
  have hpos : peR.probOfR r'.1 hterm
      * peR.scheduler.next r'.1 (some ((Silent.τ : CELabel), muB j)) ≠ 0 := by
    apply mul_ne_zero
    · have := probOfR_decB_take_ne_zero j j (le_refl j)
      rwa [probOfR_congr' _ _ (decB_take_self j) (decB_take_terminates j j) hterm] at this
    · exact sigmaR_decB_plays_muB j
  have hle := ENNReal.le_tsum (f := fun r' : {r' : ResolvedExec CEState CELabel //
      r'.toExec = advPrefix j} => peR.probOfR r'.1
        (ResolvedExec.terminates_of_toExec_eq (advPrefix_terminates j) r'.2)
      * peR.scheduler.next r'.1 (some ((Silent.τ : CELabel), muB j))) r'
  exact fun hz => hpos (le_antisymm (hz ▸ hle) bot_le)

/-- The advancing kernel of `peR.average` is positive (it carries at least the `muB` mass). -/
private theorem advKR_pos (j : ℕ) : 0 < advKR j := by
  rw [advKR, advK_eq]
  have hB : 0 < pmB (peR.average) j * (2 / 3) :=
    ENNReal.mul_pos (avg_pmB_pos j).ne' (by norm_num)
  exact lt_of_lt_of_le hB le_add_self

/-- `advPrefix (j+1)` is `advPrefix j` extended by the advancing step `q j → q (j+1)`. -/
private theorem advPrefix_succ_append (j : ℕ) : advPrefix (j + 1) =
    ⟨(advPrefix j).init,
      (advPrefix j).trans.append (Seq.cons ((Silent.τ : CELabel), CEState.q (j + 1)) Seq.nil)⟩ := by
  simp only [advPrefix]
  congr 1
  rw [advList_succ, Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]

/-- `qExitPrefix k` is `advPrefix k` extended by the silent exit `q k → q' k`. -/
private theorem qExitPrefix_append (k : ℕ) : qExitPrefix k =
    ⟨(advPrefix k).init,
      (advPrefix k).trans.append (Seq.cons ((Silent.τ : CELabel), CEState.q' k) Seq.nil)⟩ := by
  simp only [qExitPrefix, advPrefix]
  congr 1
  rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]

/-- `avgWeight` recursion along the corridor:
`avgWeight (advPrefix (j+1)) = avgWeight (advPrefix j) * advKR j`. -/
private theorem avgWeight_advPrefix_succ (j : ℕ) :
    peR.avgWeight (advPrefix (j + 1)) (advPrefix_terminates (j + 1))
      = peR.avgWeight (advPrefix j) (advPrefix_terminates j) * advKR j := by
  have happ : ((advPrefix j).trans.append
      (Seq.cons ((Silent.τ : CELabel), CEState.q (j + 1)) Seq.nil)).Terminates := by
    have := advPrefix_terminates (j + 1); rwa [advPrefix_succ_append j] at this
  rw [peR.avgWeight_congr (advPrefix (j + 1)) _ (advPrefix_succ_append j)
    (advPrefix_terminates (j + 1)) happ]
  exact (peR.avgWeight_average_step (advPrefix j) (advPrefix_terminates j)
    (Silent.τ) (CEState.q (j + 1)) happ).symm

/-- The base marginal: the empty advance prefix has weight `1` (the Dirac initial mass). -/
private theorem avgWeight_advPrefix_zero :
    peR.avgWeight (advPrefix 0) (advPrefix_terminates 0) = 1 := by
  have heq : advPrefix 0 = ⟨CEState.q 0, (Seq.nil : Seq (CELabel × CEState))⟩ := by
    simp only [advPrefix, advList, List.range_zero, List.map_nil, Stream'.Seq.ofList_nil]
  rw [peR.avgWeight_congr (advPrefix 0) _ heq (advPrefix_terminates 0) Stream'.Seq.terminates_nil,
    peR.avgWeight_nil]
  change (PMF.pure CESys.init) (CEState.q 0) = 1
  exact PMF.pure_apply_self _

/-- **The advance prefix has positive marginal weight** (a product of positive kernels). -/
private theorem avgWeight_advPrefix_pos (j : ℕ) :
    0 < peR.avgWeight (advPrefix j) (advPrefix_terminates j) := by
  induction j with
  | zero => rw [avgWeight_advPrefix_zero]; norm_num
  | succ k ih =>
    rw [avgWeight_advPrefix_succ k]
    exact ENNReal.mul_pos ih.ne' (advKR_pos k).ne'

/-- `peR.average` never halts on the corridor: every decoration of `advPrefix j` ends at
`q j ≠ bin`, where `sigmaR` emits no `none`. -/
private theorem avg_no_halt_next (j : ℕ) : (peR.average).scheduler.next (advPrefix j) none = 0 := by
  classical
  have hW : peR.avgWeight (advPrefix j) (advPrefix_terminates j) ≠ 0 :=
    (avgWeight_advPrefix_pos j).ne'
  rw [peR.average_next_none (advPrefix j) (advPrefix_terminates j) hW]
  have hnum : (∑' r' : {r' : ResolvedExec CEState CELabel // r'.toExec = advPrefix j},
      peR.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq (advPrefix_terminates j) r'.2)
        * peR.scheduler.next r'.1 none) = 0 := by
    refine ENNReal.tsum_eq_zero.mpr (fun r' => ?_)
    have hσ : peR.scheduler.next r'.1 none = 0 := by
      by_contra hc
      have := sigmaR_none_endState r'.1
        (ResolvedExec.terminates_of_toExec_eq (advPrefix_terminates j) r'.2) hc
      rw [decoration_advPrefix_endState j r'] at this
      exact absurd this (by simp)
    rw [hσ, mul_zero]
  rw [hnum, zero_mul]

/-- On the corridor, `peR.average` puts full mass on the two silent transitions: `pmA + pmB = 1`. -/
private theorem avg_pmA_add_pmB (j : ℕ) : pmA (peR.average) j + pmB (peR.average) j = 1 :=
  pmA_add_pmB_of_no_halt (peR.average) j (avg_no_halt_next j)

/-- **The exit rate of `peR.average` is strictly below ½.** With `pmA + pmB = 1` and `pmB > 0`,
`exitKR = ½·pmA + ⅓·pmB < ½·(pmA + pmB) = ½`. -/
private theorem exitKR_lt_half (k : ℕ) : exitKR k < 1 / 2 := by
  rw [exitKR, exitK_eq]
  set a := pmA (peR.average) k
  set b := pmB (peR.average) k
  have hsum : a + b = 1 := avg_pmA_add_pmB k
  have hb : 0 < b := avg_pmB_pos k
  have hble : b ≤ 1 := pmB_le_one (peR.average) k
  have ha : a ≤ 1 := by rw [← hsum]; exact le_self_add
  have hafin : a ≠ ⊤ := (ha.trans_lt ENNReal.one_lt_top).ne
  have hbfin : b ≠ ⊤ := (hble.trans_lt ENNReal.one_lt_top).ne
  have hkey : b * (1 / 3) < b * (1 / 2) := by
    rw [mul_comm b (1 / 3), mul_comm b (1 / 2)]
    exact ENNReal.mul_lt_mul_left hb.ne' hbfin (by norm_num)
  calc a * (1 / 2) + b * (1 / 3)
      < a * (1 / 2) + b * (1 / 2) :=
        (ENNReal.add_lt_add_iff_left (ENNReal.mul_ne_top hafin (by norm_num))).mpr hkey
    _ = (a + b) * (1 / 2) := by rw [add_mul]
    _ = 1 / 2 := by rw [hsum, one_mul]

/-- `avgWeight (qExitPrefix k) = avgWeight (advPrefix k) * exitKR k`. -/
private theorem avgWeight_qExitPrefix_eq (k : ℕ) :
    peR.avgWeight (qExitPrefix k) (qExitPrefix_terminates k)
      = peR.avgWeight (advPrefix k) (advPrefix_terminates k) * exitKR k := by
  have happ : ((advPrefix k).trans.append
      (Seq.cons ((Silent.τ : CELabel), CEState.q' k) Seq.nil)).Terminates := by
    have := qExitPrefix_terminates k; rwa [qExitPrefix_append k] at this
  rw [peR.avgWeight_congr (qExitPrefix k) _ (qExitPrefix_append k)
    (qExitPrefix_terminates k) happ]
  exact (peR.avgWeight_average_step (advPrefix k) (advPrefix_terminates k)
    (Silent.τ) (CEState.q' k) happ).symm

/-- The exit prefix `qExitPrefix k` also has positive marginal weight. -/
private theorem avgWeight_qExitPrefix_pos (k : ℕ) :
    0 < peR.avgWeight (qExitPrefix k) (qExitPrefix_terminates k) := by
  rw [avgWeight_qExitPrefix_eq k]
  refine ENNReal.mul_pos (avgWeight_advPrefix_pos k).ne' ?_
  have : 0 < exitKR k := by
    rw [exitKR, exitK_eq]
    have hA : 0 < pmA (peR.average) k * (1 / 2) ∨ 0 < pmB (peR.average) k * (1 / 3) :=
      Or.inr (ENNReal.mul_pos (avg_pmB_pos k).ne' (by norm_num))
    rcases hA with h | h
    · exact lt_of_lt_of_le h le_self_add
    · exact lt_of_lt_of_le h le_add_self
  exact this.ne'

/-- **`ext = 1` for `peR.average`.** The only decoration-step from `q' k` is the external
`(some k, pure bin)`, so the average external kernel is one. -/
private theorem avg_ext_one (k : ℕ) :
    (peR.average).kernel (qExitPrefix k) ((some k : CELabel), CEState.bin) = 1 := by
  classical
  rw [ext_eq]
  have hW : peR.avgWeight (qExitPrefix k) (qExitPrefix_terminates k) ≠ 0 :=
    (avgWeight_qExitPrefix_pos k).ne'
  rw [peR.average_next_some (qExitPrefix k) (qExitPrefix_terminates k)
    (some k) (PMF.pure CEState.bin)]
  -- The numerator equals `avgWeight`, since every decoration plays `some k, pure bin` w.p. 1.
  have hnum : (∑' r' : {r' : ResolvedExec CEState CELabel // r'.toExec = qExitPrefix k},
      peR.probOfR r'.1 (ResolvedExec.terminates_of_toExec_eq (qExitPrefix_terminates k) r'.2)
        * peR.scheduler.next r'.1 (some ((some k : CELabel), PMF.pure CEState.bin)))
      = peR.avgWeight (qExitPrefix k) (qExitPrefix_terminates k) := by
    rw [ResolvedProbabilisticExecution.avgWeight]
    refine tsum_congr (fun r' => ?_)
    have hσ : peR.scheduler.next r'.1 (some ((some k : CELabel), PMF.pure CEState.bin)) = 1 := by
      change sigmaR.next r'.1 _ = 1
      have hterm := ResolvedExec.terminates_of_toExec_eq (qExitPrefix_terminates k) r'.2
      rw [sigmaR]
      simp only [dif_pos hterm, decoration_qExitPrefix_endState k r']
      rw [PMF.pure_apply]; simp
    rw [hσ, mul_one]
  rw [hnum, ENNReal.mul_inv_cancel hW]
  exact (((peR.avgWeight_le_init (qExitPrefix k) (qExitPrefix_terminates k)).trans
    (PMF.coe_le_one _ _)).trans_lt ENNReal.one_lt_top).ne

/-! ### Step 4 — matching a fair plain `pe` to `peR.average`, and the contradiction

The exit factorisation `traceProb pe (traceK k) = (∏ advK) · exitK k · ext k` holds for every
`q 0`-initial plain `pe`. Since `D_CE (traceK k) > 0`, a `pe` matching `D_CE` has every factor
positive — hence `q j`/`q' k` reachable, `pmA + pmB = 1`, and `ext = 1`. An induction pins
`advK pe = advKR`, `exitK pe = exitKR`, so `exitK pe k < ½`, forcing `pmB pe k > 0` for all `k`,
contradicting `not_all_pmB_pos`. -/

/-- The generic exit factorisation of the trace probability of `traceK k`. -/
private theorem traceProb_factor (pe : ProbabilisticExecution CESys)
    (h0 : pe.initState = PMF.pure (CEState.q 0)) (k : ℕ) :
    CESys.traceProb pe (traceK k)
      = (∏ j ∈ Finset.range k,
          pe.kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q (j + 1)))
        * pe.kernel (advPrefix k) ((Silent.τ : CELabel), CEState.q' k)
        * pe.kernel (qExitPrefix k) ((some k : CELabel), CEState.bin) := by
  rw [traceProb_traceK pe h0 k, probOf_exitExec pe h0 k]

/-- `D_CE (traceK k)` in factored form (for `peR.average`). -/
private theorem D_CE_factor (k : ℕ) :
    D_CE (traceK k)
      = (∏ j ∈ Finset.range k, advKR j) * exitKR k
        * (peR.average).kernel (qExitPrefix k) ((some k : CELabel), CEState.bin) := by
  rw [D_CE, ← peR.traceProb_average (traceK k),
    traceProb_factor (peR.average) avg_initState k]
  rfl

/-- Each factor of `D_CE (traceK k)` is positive, so `D_CE (traceK k) > 0`. -/
private theorem D_CE_traceK_pos (k : ℕ) : 0 < D_CE (traceK k) := by
  rw [D_CE_factor k, avg_ext_one k, mul_one]
  refine ENNReal.mul_pos ?_ ?_
  · exact (CanonicallyOrderedAdd.prod_pos.mpr (fun j _ => advKR_pos j)).ne'
  · have : 0 < exitKR k := by
      rw [exitKR, exitK_eq]
      exact lt_of_lt_of_le (ENNReal.mul_pos (avg_pmB_pos k).ne' (by norm_num)) le_add_self
    rw [exitKR] at this; exact this.ne'

/-- The advancing product of `peR.average` is finite (a product of kernels, each ≤ 1). -/
private theorem advKR_prod_ne_top (k : ℕ) :
    (∏ j ∈ Finset.range k, advKR j) ≠ ⊤ := by
  apply ENNReal.prod_ne_top
  intro j _
  rw [advKR]
  exact ((ProbabilisticExecution.kernel_le_one _ _ _).trans_lt ENNReal.one_lt_top).ne

/-- The advancing and exit kernels sum to the total silent mass `pmA + pmB`. -/
private theorem advK_add_exitK (pe : ProbabilisticExecution CESys) (j : ℕ) :
    pe.kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q (j + 1))
      + pe.kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q' j)
      = pmA pe j + pmB pe j := by
  rw [advK_eq, exitK_eq]
  set a := pmA pe j
  set b := pmB pe j
  have h1 : ((1 : ENNReal) / 2 + 1 / 2) = 1 := by
    rw [ENNReal.div_add_div_same, show (1 : ENNReal) + 1 = 2 from by norm_num,
      ENNReal.div_self (by norm_num) (by norm_num)]
  have h2 : ((2 : ENNReal) / 3 + 1 / 3) = 1 := by
    rw [ENNReal.div_add_div_same, show (2 : ENNReal) + 1 = 3 from by norm_num,
      ENNReal.div_self (by norm_num) (by norm_num)]
  rw [show a * (1 / 2) + b * (2 / 3) + (a * (1 / 2) + b * (1 / 3))
      = a * (1 / 2 + 1 / 2) + b * (2 / 3 + 1 / 3) from by ring, h1, h2, mul_one, mul_one]

/-- For `peR.average` too, `advKR + exitKR = 1` (the total silent mass is one). -/
private theorem advKR_add_exitKR (j : ℕ) : advKR j + exitKR j = 1 := by
  rw [advKR, exitKR, advK_add_exitK, avg_pmA_add_pmB]

/-- The exit kernel is at most one (a coordinate of a `PMF`-driven kernel). -/
private theorem exitK_le_one (pe : ProbabilisticExecution CESys) (j : ℕ) :
    pe.kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q' j) ≤ 1 :=
  ProbabilisticExecution.kernel_le_one _ _ _

/-! The core matching induction, packaged as: a fair `pe` matching `D_CE` has
`advK pe = advKR` and `exitK pe = exitKR` at every corridor step. -/

/-- Positivity of all factors of a matching `pe`'s trace probability. -/
private theorem matching_factors_pos (pe : ProbabilisticExecution CESys)
    (h0 : pe.initState = PMF.pure (CEState.q 0))
    (htp : ∀ τ, CESys.traceProb pe τ = D_CE τ) (k : ℕ) :
    (∀ j < k, 0 < pe.kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q (j + 1))) ∧
      0 < pe.kernel (advPrefix k) ((Silent.τ : CELabel), CEState.q' k) ∧
      0 < pe.kernel (qExitPrefix k) ((some k : CELabel), CEState.bin) := by
  have hpos : 0 < CESys.traceProb pe (traceK k) := by rw [htp]; exact D_CE_traceK_pos k
  rw [traceProb_factor pe h0 k] at hpos
  have hprod : 0 < (∏ j ∈ Finset.range k,
      pe.kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q (j + 1))) := by
    rcases eq_zero_or_pos (∏ j ∈ Finset.range k,
        pe.kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q (j + 1))) with h | h
    · rw [h, zero_mul, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact h
  have hexit : 0 < pe.kernel (advPrefix k) ((Silent.τ : CELabel), CEState.q' k) := by
    rcases eq_zero_or_pos (pe.kernel (advPrefix k) ((Silent.τ : CELabel), CEState.q' k))
      with h | h
    · rw [h, mul_zero, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact h
  have hext : 0 < pe.kernel (qExitPrefix k) ((some k : CELabel), CEState.bin) := by
    rcases eq_zero_or_pos (pe.kernel (qExitPrefix k) ((some k : CELabel), CEState.bin))
      with h | h
    · rw [h, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact h
  refine ⟨?_, hexit, hext⟩
  intro j hj
  exact CanonicallyOrderedAdd.prod_pos.mp hprod j (Finset.mem_range.mpr hj)

/-- A matching fair `pe` reaches every `q k`, so `pmA + pmB = 1`. -/
private theorem matching_pmA_add_pmB (pe : ProbabilisticExecution CESys)
    (h0 : pe.initState = PMF.pure (CEState.q 0)) (hfair : pe.IsFair CEfair)
    (htp : ∀ τ, CESys.traceProb pe τ = D_CE τ) (k : ℕ) :
    pmA pe k + pmB pe k = 1 := by
  have h0' : pe.initState (CEState.q 0) ≠ 0 := by rw [h0, PMF.pure_apply]; simp
  apply pmA_add_pmB_reachable pe h0' hfair k
  intro j hj
  exact ((matching_factors_pos pe h0 htp (j + 1)).1 j (Nat.lt_succ_self j)).ne'

/-- A matching fair `pe` reaches every `q' k`, so `ext = 1`. -/
private theorem matching_ext_one (pe : ProbabilisticExecution CESys)
    (h0 : pe.initState = PMF.pure (CEState.q 0)) (hfair : pe.IsFair CEfair)
    (htp : ∀ τ, CESys.traceProb pe τ = D_CE τ) (k : ℕ) :
    pe.kernel (qExitPrefix k) ((some k : CELabel), CEState.bin) = 1 := by
  have h0' : pe.initState (CEState.q 0) ≠ 0 := by rw [h0, PMF.pure_apply]; simp
  obtain ⟨hadv, hexit, _⟩ := matching_factors_pos pe h0 htp k
  exact ext_one_reachable pe h0' hfair k (fun j hj => (hadv j hj).ne') hexit.ne'

/-- **The matching induction.** A fair `pe` matching `D_CE` has `advK pe k = advKR k` and
`exitK pe k = exitKR k` for every `k`. Equal advancing products up to `k` and the matched
factorisation (both `ext = 1`) cancel to give `exitK pe k = exitKR k`; then
`advK pe k = 1 - exitK pe k = 1 - exitKR k = advKR k`. -/
private theorem matching_step (pe : ProbabilisticExecution CESys)
    (h0 : pe.initState = PMF.pure (CEState.q 0)) (hfair : pe.IsFair CEfair)
    (htp : ∀ τ, CESys.traceProb pe τ = D_CE τ) :
    ∀ k, pe.kernel (advPrefix k) ((Silent.τ : CELabel), CEState.q (k + 1)) = advKR k ∧
      pe.kernel (advPrefix k) ((Silent.τ : CELabel), CEState.q' k) = exitKR k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hprodeq : (∏ j ∈ Finset.range k,
        pe.kernel (advPrefix j) ((Silent.τ : CELabel), CEState.q (j + 1)))
        = ∏ j ∈ Finset.range k, advKR j :=
      Finset.prod_congr rfl (fun j hj => (ih j (Finset.mem_range.mp hj)).1)
    have hmatch : CESys.traceProb pe (traceK k) = D_CE (traceK k) := htp _
    rw [traceProb_factor pe h0 k, matching_ext_one pe h0 hfair htp k, mul_one,
      D_CE_factor k, avg_ext_one k, mul_one, hprodeq] at hmatch
    have hProdPos : 0 < ∏ j ∈ Finset.range k, advKR j :=
      CanonicallyOrderedAdd.prod_pos.mpr (fun j _ => advKR_pos j)
    have hexiteq : pe.kernel (advPrefix k) ((Silent.τ : CELabel), CEState.q' k) = exitKR k :=
      (ENNReal.mul_right_inj hProdPos.ne' (advKR_prod_ne_top k)).mp hmatch
    refine ⟨?_, hexiteq⟩
    have hsumpe : pe.kernel (advPrefix k) ((Silent.τ : CELabel), CEState.q (k + 1))
        + pe.kernel (advPrefix k) ((Silent.τ : CELabel), CEState.q' k) = 1 := by
      rw [advK_add_exitK]; exact matching_pmA_add_pmB pe h0 hfair htp k
    have hexitfin : pe.kernel (advPrefix k) ((Silent.τ : CELabel), CEState.q' k) ≠ ⊤ :=
      ((exitK_le_one pe k).trans_lt ENNReal.one_lt_top).ne
    have hexitRfin : exitKR k ≠ ⊤ :=
      (((exitKR_lt_half k).le.trans (by norm_num)).trans_lt ENNReal.one_lt_top).ne
    have hadv : pe.kernel (advPrefix k) ((Silent.τ : CELabel), CEState.q (k + 1))
        = 1 - pe.kernel (advPrefix k) ((Silent.τ : CELabel), CEState.q' k) := by
      rw [← hsumpe, ENNReal.add_sub_cancel_right hexitfin]
    rw [hadv, hexiteq, eq_comm, ← advKR_add_exitKR k, ENNReal.add_sub_cancel_right hexitRfin]

/-- Combining the matching with `exitKR < ½` forces `pmB pe k > 0` at every step. -/
private theorem matching_pmB_pos (pe : ProbabilisticExecution CESys)
    (h0 : pe.initState = PMF.pure (CEState.q 0)) (hfair : pe.IsFair CEfair)
    (htp : ∀ τ, CESys.traceProb pe τ = D_CE τ) (k : ℕ) : 0 < pmB pe k := by
  have hexiteq := (matching_step pe h0 hfair htp k).2
  rw [exitK_eq] at hexiteq
  have hexitlt : pmA pe k * (1 / 2) + pmB pe k * (1 / 3) < 1 / 2 := by
    rw [hexiteq]; exact exitKR_lt_half k
  by_contra hb
  push Not at hb
  have hb0 : pmB pe k = 0 := nonpos_iff_eq_zero.mp hb
  have hsum : pmA pe k + pmB pe k = 1 := matching_pmA_add_pmB pe h0 hfair htp k
  rw [hb0, add_zero] at hsum
  rw [hb0, hsum] at hexitlt
  simp at hexitlt

/-- **`D_CE ∉ fairAchievableTraceDistsPlain CEfair`.** No fair plain scheduler achieves the resolved
witness's trace distribution: matching would force `peR.average`'s sub-½ exit rate onto `pe`, hence
`pmB pe k > 0` at every step, whose all-unfair run contradicts sure-fairness. -/
theorem D_CE_not_mem_plain : D_CE ∉ fairAchievableTraceDistsPlain CEfair := by
  rintro ⟨pe, h0, hfair, htp⟩
  have h0q : pe.initState = PMF.pure (CEState.q 0) := h0
  have h0' : pe.initState (CEState.q 0) ≠ 0 := by rw [h0q, PMF.pure_apply]; simp
  exact not_all_pmB_pos pe h0' hfair (fun k => (matching_pmB_pos pe h0q hfair htp k).ne')

/-- **The separation theorem.** The resolved-history fair achievable set is strictly larger than the
plain one: `D_CE` lies in the former (`D_CE_mem_R`) but not the latter (`D_CE_not_mem_plain`). -/
theorem fairAchievableTraceDists_ne_plain :
    fairAchievableTraceDists CEfair ≠ fairAchievableTraceDistsPlain CEfair :=
  fun h => D_CE_not_mem_plain (h ▸ D_CE_mem_R)

end FairCounterexample

end PLTS
