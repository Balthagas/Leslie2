/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Weak.Step
import MyMathlibProject.Construction.WeakClosure

/-!
# Weak-transition characterizations

Analytic "workhorse" lemmas relating the weak transitions `weakTau` /
`weakStep` to the hyper-steps of the weak closure `sys^w`. These are the
transition-level content behind the simulation equivalences in
`Simulation/Equivalences.lean`, and are independent of the simulation
definitions in `Simulation/Defs.lean`. See the section note below for the
three lemma families (source-decomposition, source-mixing, target-convexity).
-/

open Stream'

namespace PLTS

variable {α β State State_C State_A Label : Type} [Silent Label]

/-! #### Analytic workhorses

The four transition-level lemmas reduce to these. They isolate the genuine
content (the Kraft bound `WeakScheduler.haltMass_tsum_le_one` they rely on lives
in `Weak/Bounds.lean` alongside the other antichain bounds):

* `weakTau_exists_pointwise` / `weakStep_exists_pointwise` — **source-
  decomposition**: a weak transition from a distribution `μ` splits, via its
  single witness scheduler dispatched on the (observable) start state, into
  per-point weak transitions;
* `weakTau_of_pointwise` / `weakStep_of_pointwise` — **source-mixing**: the
  converse recombination (one scheduler dispatching on the start state);
* `weakTau_bind` / `weakStep_bind` — **target-convexity**: a *mixture of
  schedulers from a single point* `pure s` recombines into one weak transition
  (the genuine crux, needs a posterior-weighted mixing scheduler). -/

/-- **Source-decomposition for `weakTau`.** -/
theorem weakTau_exists_pointwise {sys : System State Label} {μ ν : PMF State}
    (h : weakTau sys μ ν) :
    ∃ ρ : State → PMF State,
      (∀ s ∈ μ.support, weakTau sys (PMF.pure s) (ρ s)) ∧ ν = μ.bind ρ := by
  classical
  set σ := h.witnessScheduler with hσ
  -- per-point total halting mass and end-state pushforward
  set T : State → ENNReal := fun s => ∑' e, σ.haltMass (PMF.pure s) e with hT
  set F : State → State → ENNReal :=
    fun s x => ∑' e, σ.haltMass (PMF.pure s) e * (if e.1.endState e.2 = x then 1 else 0) with hF
  -- (1) the rows of `F` sum to `T`.
  have hFsum : ∀ s, (∑' x, F s x) = T s := by
    intro s
    simp only [hF, hT]
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun e => ?_)
    rw [ENNReal.tsum_mul_left]
    rw [show (∑' x, (if e.1.endState e.2 = x then (1 : ENNReal) else 0)) = 1 from by
      rw [tsum_eq_single (e.1.endState e.2)]
      · simp
      · intro b hb; simp [Ne.symm hb]]
    rw [mul_one]
  -- (2) the source-average of `T` is `1` (a.s. halting from `μ`).
  have havg : (∑' s, μ s * T s) = 1 := by
    rw [← h.witness_halts]
    simp only [hT]
    rw [show (∑' e, σ.haltMass μ e) = ∑' e, ∑' s, μ s * σ.haltMass (PMF.pure s) e from
      tsum_congr (fun e => σ.haltMass_init_mix μ e)]
    rw [ENNReal.tsum_comm]
    exact tsum_congr (fun s => (ENNReal.tsum_mul_left).symm)
  -- (3) each `T s ≤ 1` (Kraft bound).
  have hTle : ∀ s, T s ≤ 1 := fun s => WeakScheduler.haltMass_tsum_le_one σ (PMF.pure s)
  -- (4) on the support, `T s = 1`: the average being `1` forces each weighted term maximal.
  have hTeq : ∀ s ∈ μ.support, T s = 1 := by
    intro s hs
    rw [PMF.mem_support_iff] at hs
    by_contra hne
    have hlt : T s < 1 := lt_of_le_of_ne (hTle s) hne
    have hstrict : μ s * T s < μ s := by
      calc μ s * T s < μ s * 1 := ENNReal.mul_lt_mul_right hs (μ.apply_ne_top s) hlt
        _ = μ s := mul_one _
    have hle : ∀ a, μ a * T a ≤ μ a := fun a => mul_le_of_le_one_right' (hTle a)
    have hcontra : (∑' a, μ a * T a) < (∑' a, μ a) :=
      ENNReal.hasSum_lt hle hstrict (by rw [havg]; exact ENNReal.one_ne_top)
        ENNReal.summable.hasSum ENNReal.summable.hasSum
    rw [havg, μ.tsum_coe] at hcontra
    exact lt_irrefl 1 hcontra
  -- (5) the per-point τ-closure outcome: rows of `F` where they normalise, else `pure s`.
  refine ⟨fun s => if hs : T s = 1 then ⟨F s, by
      have hsum : (∑' x, F s x) = 1 := by rw [hFsum s, hs]
      rw [← hsum]; exact ENNReal.summable.hasSum⟩ else PMF.pure s, ?_, ?_⟩
  -- (6a) each support point is τ-related to its row of `F`.
  · intro s hs
    have hTs : T s = 1 := hTeq s hs
    refine ⟨σ, hTs, fun x => ?_⟩
    simp only [dif_pos hTs]
    rfl
  -- (6b) `ν` is the source-mix of the per-point outcomes.
  · refine PMF.ext (fun x => ?_)
    rw [PMF.bind_apply]
    rw [h.witness_pushforward x]
    -- ν x = ∑' s, μ s * F s x
    have hνx : (∑' e, σ.haltMass μ e * (if e.1.endState e.2 = x then (1 : ENNReal) else 0))
        = ∑' s, μ s * F s x := by
      calc (∑' e, σ.haltMass μ e * (if e.1.endState e.2 = x then (1 : ENNReal) else 0))
          = ∑' e, (∑' s, μ s * σ.haltMass (PMF.pure s) e)
              * (if e.1.endState e.2 = x then (1 : ENNReal) else 0) :=
            tsum_congr (fun e => by rw [σ.haltMass_init_mix μ e])
        _ = ∑' e, ∑' s, μ s
              * (σ.haltMass (PMF.pure s) e
              * (if e.1.endState e.2 = x then (1 : ENNReal) else 0)) := by
            refine tsum_congr (fun e => ?_)
            rw [← ENNReal.tsum_mul_right]
            exact tsum_congr (fun s => by ring)
        _ = ∑' s, ∑' e, μ s
              * (σ.haltMass (PMF.pure s) e * (if e.1.endState e.2 = x then (1 : ENNReal) else 0)) :=
            ENNReal.tsum_comm
        _ = ∑' s, μ s * F s x := tsum_congr (fun s => ENNReal.tsum_mul_left)
    rw [hνx]
    refine tsum_congr (fun s => ?_)
    by_cases h0 : μ s = 0
    · rw [h0, zero_mul, zero_mul]
    · have hTs : T s = 1 := hTeq s ((PMF.mem_support_iff μ s).mpr h0)
      congr 1
      simp only [dif_pos hTs]
      rfl

/-- **Source-mixing for `weakTau`.** -/
theorem weakTau_of_pointwise {sys : System State Label} {μ : PMF State}
    (ρ : State → PMF State) (h : ∀ s ∈ μ.support, weakTau sys (PMF.pure s) (ρ s)) :
    weakTau sys μ (μ.bind ρ) := by
  classical
  -- The per-state continuation: on the support use the witness scheduler, off it `stop`.
  set k : State → WeakScheduler sys :=
    fun s => if hs : s ∈ μ.support then (h s hs).witnessScheduler else WeakScheduler.stop sys
    with hk
  -- The composite scheduler: stop, then immediately hand off to `k`.
  set σ : WeakScheduler sys := WeakScheduler.bind (WeakScheduler.stop sys) k with hσ
  -- `probOf` under `stop` of any non-nil execution vanishes (mirrors `weakTau_refl`).
  have hprob_nonnil : ∀ (μ' : PMF State) (e' : AlterSeq State Label)
      (he : e'.trans.Terminates), e'.trans ≠ Seq.nil →
      (⟨μ', (WeakScheduler.stop sys).toScheduler⟩
        : ProbabilisticExecution sys).probOf e' he = 0 := by
    intro μ' e' he hne
    set pe : ProbabilisticExecution sys :=
      ⟨μ', (WeakScheduler.stop sys).toScheduler⟩ with hpe
    have hker : ∀ (e'' : AlterSeq State Label) (st : Label × State), pe.kernel e'' st = 0 := by
      intro e'' st
      unfold ProbabilisticExecution.kernel
      have h0 : ∀ ν : PMF State, pe.scheduler.next e'' (some (st.1, ν)) = 0 := by
        intro ν; exact PMF.pure_apply_of_ne _ _ (by simp)
      simp only [h0, zero_mul, tsum_zero]
    obtain ⟨init', trans'⟩ := e'
    simp only at he hne ⊢
    have hnonempty : trans'.toList he ≠ [] := by
      intro hnil; apply hne
      have := Stream'.Seq.ofList_toList trans' he
      rw [hnil, Stream'.Seq.ofList_nil] at this; exact this.symm
    obtain ⟨previous, last, h_prev, h_split, _, _⟩ :=
      Stream'.Seq.exists_split_last trans' he hnonempty
    subst h_split
    rw [ProbabilisticExecution.probOf_append_singleton _ _ _ h_prev _ he, hker, mul_zero]
  -- `stop`'s halt mass at the nil fiber `⟨a, nil⟩` from source `μ'` is `μ' a`.
  have hstop_nil : ∀ (μ' : PMF State) (a : State),
      (WeakScheduler.stop sys).haltMass μ'
          ⟨⟨a, Seq.nil⟩, Stream'.Seq.terminates_nil⟩ = μ' a := by
    intro μ' a
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState]
    rw [show (WeakScheduler.stop sys).toScheduler.next ⟨a, Seq.nil⟩ none = 1 from
      PMF.pure_apply_self none, mul_one]
  -- `stop`'s halt mass at any non-nil execution is `0`.
  have hstop_nonnil : ∀ (μ' : PMF State)
      (e' : {e : AlterSeq State Label // e.trans.Terminates}),
      e'.1.trans ≠ Seq.nil → (WeakScheduler.stop sys).haltMass μ' e' = 0 := by
    intro μ' e' hne
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [hprob_nonnil μ' e'.1 e'.2 hne, zero_mul]
  -- `haltMass (pure s)` vanishes when the execution starts elsewhere.
  have hk_init_ne : ∀ (κ : WeakScheduler sys) (s : State)
      (e' : {e : AlterSeq State Label // e.trans.Terminates}),
      e'.1.init ≠ s → κ.haltMass (PMF.pure s) e' = 0 := by
    intro κ s e' hne
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [ProbabilisticExecution.probOf_init_factor κ.toScheduler (PMF.pure s) e'.1 e'.2,
      PMF.pure_apply_of_ne _ _ hne, zero_mul, zero_mul]
  -- **Core helper.** From a Dirac start, the composite collapses to the continuation `k`.
  have hcore : ∀ (s : State) (e' : {e : AlterSeq State Label // e.trans.Terminates}),
      σ.haltMass (PMF.pure s) e' = (k s).haltMass (PMF.pure s) e' := by
    intro s e'
    rw [hσ, WeakScheduler.bind_haltMass]
    -- `stateAfter e'.1 0 = e'.1.init`.
    have hsa0 : WeakScheduler.stateAfter e'.1 0 = e'.1.init := rfl
    -- only the `j = 0` term survives.
    rw [Finset.sum_eq_single 0]
    · -- the `j = 0` term: `take 0 = []`, `drop 0 = trans`, `stateAfter _ 0 = init`.
      rw [Stream'.Seq.take_zero, hsa0]
      -- the `stop`-factor is `(pure s) e'.1.init` (its execution is the nil fiber at `e'.1.init`).
      have hstopfac : (WeakScheduler.stop sys).haltMass (PMF.pure s)
            ⟨⟨e'.1.init, Seq.ofList []⟩, Stream'.Seq.terminates_ofList _⟩
          = (PMF.pure s) e'.1.init := by
        rw [WeakScheduler.haltMass_congr_eq (WeakScheduler.stop sys) (PMF.pure s)
          (show (⟨⟨e'.1.init, Seq.ofList []⟩, Stream'.Seq.terminates_ofList _⟩
              : {e : AlterSeq State Label // e.trans.Terminates}).1
            = (⟨⟨e'.1.init, Seq.nil⟩, Stream'.Seq.terminates_nil⟩
              : {e : AlterSeq State Label // e.trans.Terminates}).1 from by
            simp only [Seq.ofList_nil])]
        exact hstop_nil (PMF.pure s) e'.1.init
      -- the `k`-factor is `(k e'.1.init).haltMass (pure e'.1.init) e'`.
      have hkfac : (k e'.1.init).haltMass (PMF.pure e'.1.init)
            ⟨⟨e'.1.init, e'.1.trans.drop 0⟩, WeakScheduler.drop_terminates e'.2 0⟩
          = (k e'.1.init).haltMass (PMF.pure e'.1.init) e' :=
        WeakScheduler.haltMass_congr_eq _ _ (show
          (⟨⟨e'.1.init, e'.1.trans.drop 0⟩, WeakScheduler.drop_terminates e'.2 0⟩
            : {e : AlterSeq State Label // e.trans.Terminates}).1 = e'.1 from by
          simp only [Stream'.Seq.drop_zero])
      rw [hstopfac, hkfac]
      -- now case on whether `e'.1.init = s`.
      by_cases hinit : e'.1.init = s
      · subst hinit
        rw [PMF.pure_apply_self, one_mul]
      · rw [PMF.pure_apply_of_ne s e'.1.init hinit, zero_mul,
          hk_init_ne (k s) s e' hinit]
    · -- terms with `j ≥ 1` vanish: the `stop`-factor is on a non-nil prefix.
      intro j hjmem hjne
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjne
      apply mul_eq_zero_of_left
      refine hstop_nonnil (PMF.pure s) _ ?_
      simp only [ne_eq]
      intro hnil
      -- `ofList (take (n+1) trans) = nil` forces `take (n+1) trans = []`.
      have hlist : (Stream'.Seq.take (n + 1) e'.1.trans) = [] :=
        Stream'.Seq.ofList_injective (by rw [hnil, Stream'.Seq.ofList_nil])
      -- but `j = n+1 ≤ length`, so its take has length `n+1 ≠ 0`.
      have hjle : n + 1 ≤ e'.1.trans.length e'.2 := by
        have := Finset.mem_range.mp hjmem; omega
      have hlen : (Stream'.Seq.take (n + 1) e'.1.trans).length = n + 1 :=
        Stream'.Seq.length_take_of_le_length (fun _ => hjle)
      rw [hlist] at hlen
      simp at hlen
    · intro hcontra; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) hcontra
  -- **General integration identity.** Integrating any `g` over the composite's
  -- halting end-states is the source-average of integrating against each `k s`.
  have hintegrate : ∀ g : State → ENNReal,
      (∑' e, σ.haltMass μ e * g (e.1.endState e.2))
        = ∑' s, μ s * (∑' e, (k s).haltMass (PMF.pure s) e * g (e.1.endState e.2)) := by
    intro g
    calc (∑' e, σ.haltMass μ e * g (e.1.endState e.2))
        = ∑' e, (∑' s, μ s * σ.haltMass (PMF.pure s) e) * g (e.1.endState e.2) :=
          tsum_congr (fun e => by rw [σ.haltMass_init_mix μ e])
      _ = ∑' e, (∑' s, μ s * (k s).haltMass (PMF.pure s) e) * g (e.1.endState e.2) :=
          tsum_congr (fun e => by
            congr 1; exact tsum_congr (fun s => by rw [hcore s e]))
      _ = ∑' e, ∑' s, μ s * ((k s).haltMass (PMF.pure s) e * g (e.1.endState e.2)) := by
          refine tsum_congr (fun e => ?_)
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr (fun s => by ring)
      _ = ∑' s, ∑' e, μ s * ((k s).haltMass (PMF.pure s) e * g (e.1.endState e.2)) :=
          ENNReal.tsum_comm
      _ = ∑' s, μ s * (∑' e, (k s).haltMass (PMF.pure s) e * g (e.1.endState e.2)) :=
          tsum_congr (fun s => ENNReal.tsum_mul_left)
  -- On the support, `k s` is the per-state witness, so its row integrates correctly.
  have hk_eq : ∀ (s : State) (hs : s ∈ μ.support), k s = (h s hs).witnessScheduler := by
    intro s hs; rw [hk]; exact dif_pos hs
  refine ⟨σ, ?_, ?_⟩
  · -- **Total halting mass is 1.**
    have h1 := hintegrate (fun _ => 1)
    simp only [mul_one] at h1
    rw [h1]
    rw [show (∑' s, μ s * ∑' e, (k s).haltMass (PMF.pure s) e) = ∑' s, μ s from
      tsum_congr (fun s => ?_), μ.tsum_coe]
    by_cases hs : s ∈ μ.support
    · rw [hk_eq s hs, (h s hs).witness_halts, mul_one]
    · rw [PMF.mem_support_iff, not_not] at hs; rw [hs, zero_mul]
  · -- **Pushforward to `μ.bind ρ`.**
    intro x
    have hx := hintegrate (fun y => if y = x then 1 else 0)
    rw [PMF.bind_apply, hx]
    refine tsum_congr (fun s => ?_)
    by_cases hs : s ∈ μ.support
    · congr 1
      rw [hk_eq s hs, ← (h s hs).witness_pushforward x]
    · rw [PMF.mem_support_iff, not_not] at hs; rw [hs, zero_mul, zero_mul]

/-- **Source-decomposition for `weakStep`.** -/
theorem weakStep_exists_pointwise {sys : System State Label}
    {μ ν : PMF State} {l : Label} (h : weakStep sys μ l ν) :
    ∃ ρ : State → PMF State,
      (∀ s ∈ μ.support, weakStep sys (PMF.pure s) l (ρ s)) ∧ ν = μ.bind ρ := by
  classical
  obtain ⟨m, m', h1, h2, h3⟩ := h
  obtain ⟨ρ1, hρ1, hm⟩ := weakTau_exists_pointwise h1
  obtain ⟨p, hp_step, hm'⟩ := h2
  obtain ⟨ρ2, hρ2, hν⟩ := weakTau_exists_pointwise h3
  -- per-source post-hyperStep distribution and final continuation
  set M : State → PMF State := fun s => (ρ1 s).bind (fun t => (p t).bind id) with hM
  set ρ : State → PMF State := fun s => (M s).bind ρ2 with hρ
  -- support transport: a point in `(ρ1 s).support` lands in `m.support`
  have htm : ∀ s ∈ μ.support, ∀ t ∈ (ρ1 s).support, t ∈ m.support := by
    intro s hs t ht
    rw [hm]; exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨s, hs, ht⟩
  refine ⟨ρ, ?_, ?_⟩
  · intro s hs
    refine ⟨ρ1 s, M s, hρ1 s hs, ⟨p, ?_, rfl⟩, ?_⟩
    · intro t ht ζ hζ
      exact hp_step t (htm s hs t ht) ζ hζ
    · refine weakTau_of_pointwise ρ2 (fun t ht => hρ2 t ?_)
      rw [hM, PMF.mem_support_bind_iff] at ht
      obtain ⟨t₀, ht₀, ht⟩ := ht
      rw [hm']; exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨t₀, htm s hs t₀ ht₀, ht⟩
  · rw [hν, hm', hm, hρ]
    simp only [hM, PMF.bind_bind]

/-- **Posterior-mixing for `hyperStep`.** A `q`-indexed family of hyper-steps
`hyperStep sys (m x) l (n x)` combines into a single hyper-step from the mixed
source `q.bind m` to the mixed target `q.bind n`. The mixing kernel routes each
end-state `t` through the Bayesian posterior over `x` given `t` (numerator
`q x * (m x) t`, normalized by `(q.bind m) t`). -/
private theorem hyperStep_mix {sys : System State Label} {X : Type}
    {l : Label} (q : PMF X) (m n : X → PMF State)
    (H : ∀ x ∈ q.support, hyperStep sys (m x) l (n x)) :
    hyperStep sys (q.bind m) l (q.bind n) := by
  classical
  set pk : X → State → PMF (PMF State) :=
    fun x => if hx : x ∈ q.support then (H x hx).kernel else fun t => PMF.pure (PMF.pure t)
    with hpk
  set num : State → X → ENNReal := fun t x => q x * (m x) t with hnum
  have hnumsum : ∀ t, (∑' x, num t x) = (q.bind m) t := by
    intro t; rw [hnum, PMF.bind_apply]
  set post : (t : State) → (q.bind m) t ≠ 0 → PMF X :=
    fun t ht => PMF.normalize (num t) (by rw [hnumsum]; exact ht)
      (by rw [hnumsum]; exact (q.bind m).apply_ne_top t) with hpost
  have hZ : ∀ t (ht : (q.bind m) t ≠ 0) x, (q.bind m) t * (post t ht) x = num t x := by
    intro t ht x
    rw [hpost, PMF.normalize_apply, hnumsum, ← mul_assoc, mul_comm ((q.bind m) t) (num t x),
      mul_assoc, ENNReal.mul_inv_cancel ht ((q.bind m).apply_ne_top t), mul_one]
  set P : State → PMF (PMF State) :=
    fun t => if ht : (q.bind m) t = 0 then PMF.pure (PMF.pure t)
      else (post t ht).bind (fun x => pk x t) with hP
  have hP_pos : ∀ t (ht : (q.bind m) t ≠ 0), P t = (post t ht).bind (fun x => pk x t) := by
    intro t ht; rw [hP]; exact dif_neg ht
  have hpkbind : ∀ x ∈ q.support, (m x).bind (fun t => (pk x t).bind id) = n x := by
    intro x hx
    have hpkx : pk x = (H x hx).kernel := by rw [hpk]; exact dif_pos hx
    rw [hpkx]; exact ((H x hx).post_eq_bind).symm
  refine ⟨P, ?_, ?_⟩
  · intro t ht ζ hζ
    have htne : (q.bind m) t ≠ 0 := (PMF.mem_support_iff _ t).mp ht
    rw [hP_pos t htne, PMF.mem_support_bind_iff] at hζ
    obtain ⟨x, hx, hζ⟩ := hζ
    have hnumne : num t x ≠ 0 := by
      rw [hpost, PMF.mem_support_normalize_iff] at hx; exact hx
    rw [hnum, mul_ne_zero_iff] at hnumne
    have hxq : x ∈ q.support := (PMF.mem_support_iff q x).mpr hnumne.1
    have htm : t ∈ (m x).support := (PMF.mem_support_iff (m x) t).mpr hnumne.2
    have hpkx : pk x = (H x hxq).kernel := by rw [hpk]; exact dif_pos hxq
    rw [hpkx] at hζ
    exact (H x hxq).kernel_step t htm ζ hζ
  · refine PMF.ext (fun y => ?_)
    conv_rhs => rw [PMF.bind_apply]
    have hterm : ∀ t, (q.bind m) t * ((P t).bind id) y
        = ∑' x, num t x * ((pk x t).bind id) y := by
      intro t
      by_cases ht : (q.bind m) t = 0
      · rw [ht, zero_mul]
        refine (ENNReal.tsum_eq_zero.mpr (fun x => ?_)).symm
        have hz : (∑' x, num t x) = 0 := by rw [hnumsum]; exact ht
        rw [ENNReal.tsum_eq_zero] at hz
        rw [hz x, zero_mul]
      · rw [hP_pos t ht,
          show ((post t ht).bind (fun x => pk x t)).bind id
            = (post t ht).bind (fun x => (pk x t).bind id) from PMF.bind_bind _ _ _,
          PMF.bind_apply (post t ht), ← ENNReal.tsum_mul_left]
        refine tsum_congr (fun x => ?_)
        rw [← mul_assoc, hZ t ht x]
    rw [tsum_congr hterm, ENNReal.tsum_comm]
    conv_lhs => rw [PMF.bind_apply]
    refine tsum_congr (fun x => ?_)
    by_cases hx : x ∈ q.support
    · rw [hnum]
      simp only
      rw [show (∑' t, q x * (m x) t * ((pk x t).bind id) y)
          = q x * ∑' t, (m x) t * ((pk x t).bind id) y from by
        rw [← ENNReal.tsum_mul_left]; exact tsum_congr (fun t => by ring)]
      congr 1
      rw [← PMF.bind_apply, hpkbind x hx]
    · rw [PMF.mem_support_iff, not_not] at hx
      rw [hx, zero_mul]
      refine (ENNReal.tsum_eq_zero.mpr (fun t => ?_)).symm
      rw [hnum]
      simp only [hx, zero_mul]

/-- **Target-convexity for `weakTau`** (the crux). -/
theorem weakTau_bind {sys : System State Label} {s : State}
    {q : PMF (PMF State)} (h : ∀ τ ∈ q.support, weakTau sys (PMF.pure s) τ) :
    weakTau sys (PMF.pure s) (q.bind id) := by
  classical
  -- Per-target witness scheduler: on the support use the τ-witness, off it `stop`.
  set schOf : PMF State → WeakScheduler sys :=
    fun τ => if hτ : τ ∈ q.support then (h τ hτ).witnessScheduler else WeakScheduler.stop sys
    with hschOf
  -- The probabilistic execution from `pure s` under each per-target scheduler.
  set peOf : PMF State → ProbabilisticExecution sys :=
    fun τ => ⟨PMF.pure s, (schOf τ).toScheduler⟩ with hpeOf
  -- Belief numerator: posterior-weighted, un-normalized emission weight at prefix `E`.
  set g : AlterSeq State Label → Option (Label × PMF State) → ENNReal :=
    fun E o => ∑' τ, q τ * (if hT : E.trans.Terminates then (peOf τ).probOf E hT else 0)
      * (schOf τ).next E o with hg
  -- Total belief mass at prefix `E` (the normalizer).
  set W : AlterSeq State Label → ENNReal := fun E => ∑' o, g E o with hW
  -- `W E` collapses to the posterior-weighted prefix probability (the `next` factor sums to 1).
  have hWeq : ∀ E, W E
      = ∑' τ, q τ * (if hT : E.trans.Terminates then (peOf τ).probOf E hT else 0) := by
    intro E
    rw [hW]
    calc (∑' o, g E o)
        = ∑' o, ∑' τ, q τ
            * (if hT : E.trans.Terminates then (peOf τ).probOf E hT else 0)
            * (schOf τ).next E o := by rfl
      _ = ∑' τ, ∑' o, q τ
            * (if hT : E.trans.Terminates then (peOf τ).probOf E hT else 0)
            * (schOf τ).next E o := ENNReal.tsum_comm
      _ = ∑' τ, q τ * (if hT : E.trans.Terminates then (peOf τ).probOf E hT else 0) := by
          refine tsum_congr (fun τ => ?_)
          rw [ENNReal.tsum_mul_left, ((schOf τ).next E).tsum_coe, mul_one]
  -- `W E ≤ 1`: each prefix probability is ≤ `(pure s) E.init ≤ 1`, weighted by `q`.
  have hWle : ∀ E, W E ≤ 1 := by
    intro E
    rw [hWeq E]
    calc (∑' τ, q τ * (if hT : E.trans.Terminates then (peOf τ).probOf E hT else 0))
        ≤ ∑' τ, q τ := by
          refine ENNReal.tsum_le_tsum (fun τ => ?_)
          split
          · rename_i hT
            calc q τ * (peOf τ).probOf E hT
                ≤ q τ * (peOf τ).init E.init := by
                  gcongr; exact (peOf τ).probOf_le_init E hT
              _ ≤ q τ * 1 := by
                  gcongr; rw [hpeOf]; exact PMF.coe_le_one _ _
              _ = q τ := mul_one _
          · simp
      _ = 1 := q.tsum_coe
  have hWtop : ∀ E, W E ≠ ⊤ := fun E => ne_top_of_le_ne_top ENNReal.one_ne_top (hWle E)
  -- `∑' o, g E o = W E` (definitional unfold of `W`).
  have hgsum : ∀ E, (∑' o, g E o) = W E := fun E => rfl
  -- The mixing scheduler `σ*`: normalize the belief numerator `g E` (default `pure none`).
  set σ : WeakScheduler sys :=
    { next := fun E => if hW0 : W E = 0 then PMF.pure none
        else PMF.normalize (g E) (by rw [hgsum]; exact hW0) (by rw [hgsum]; exact hWtop E)
      valid := by
        intro e n s' hterm hstate l μ hsupp
        by_cases hW0 : W e = 0
        · rw [dif_pos hW0, PMF.mem_support_iff,
            PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
          exact absurd rfl hsupp
        · simp only [dif_neg hW0, PMF.mem_support_normalize_iff] at hsupp
          -- `hsupp : g e (some (l,μ)) ≠ 0`; `g e o` is defeq to the τ-tsum.
          have hex : ¬ (∀ τ, q τ
              * (if hT : e.trans.Terminates then (peOf τ).probOf e hT else 0)
              * (schOf τ).next e (some (l, μ)) = 0) := by
            rw [← ENNReal.tsum_eq_zero]; exact hsupp
          push Not at hex
          obtain ⟨τ, hτ0⟩ := hex
          have hnext : (schOf τ).next e (some (l, μ)) ≠ 0 := by
            intro h0; exact hτ0 (by rw [h0, mul_zero])
          exact (schOf τ).valid e n s' hterm hstate l μ ((PMF.mem_support_iff _ _).mpr hnext)
      internal_only := by
        intro e l μ hsupp
        by_cases hW0 : W e = 0
        · rw [dif_pos hW0, PMF.mem_support_iff,
            PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
          exact absurd rfl hsupp
        · simp only [dif_neg hW0, PMF.mem_support_normalize_iff] at hsupp
          have hex : ¬ (∀ τ, q τ
              * (if hT : e.trans.Terminates then (peOf τ).probOf e hT else 0)
              * (schOf τ).next e (some (l, μ)) = 0) := by
            rw [← ENNReal.tsum_eq_zero]; exact hsupp
          push Not at hex
          obtain ⟨τ, hτ0⟩ := hex
          have hnext : (schOf τ).next e (some (l, μ)) ≠ 0 := by
            intro h0; exact hτ0 (by rw [h0, mul_zero])
          exact (schOf τ).internal_only e l μ ((PMF.mem_support_iff _ _).mpr hnext) }
    with hσ
  -- The composite probabilistic execution from `pure s`.
  set pe : ProbabilisticExecution sys := ⟨PMF.pure s, σ.toScheduler⟩ with hpe
  -- `next` of `σ` rewritten explicitly (no `dif` clutter).
  have hnext_def : ∀ E o, σ.next E o
      = if W E = 0 then (PMF.pure none) o else g E o * (W E)⁻¹ := by
    intro E o
    by_cases hW0 : W E = 0
    · rw [if_pos hW0]
      have : σ.next E = PMF.pure none := by rw [hσ]; exact dif_pos hW0
      rw [this]
    · rw [if_neg hW0]
      have : σ.next E = PMF.normalize (g E) (by rw [hgsum]; exact hW0)
          (by rw [hgsum]; exact hWtop E) := by rw [hσ]; exact dif_neg hW0
      rw [this, PMF.normalize_apply]
  -- **Cancellation:** `W E * σ.next E o = g E o`.
  have hcancel : ∀ E o, W E * σ.next E o = g E o := by
    intro E o
    rw [hnext_def]
    by_cases hW0 : W E = 0
    · rw [if_pos hW0, hW0, zero_mul]
      -- `g E o = 0` since `∑' o', g E o' = W E = 0`.
      have : ∀ o', g E o' = 0 := by
        rw [← ENNReal.tsum_eq_zero, hgsum]; exact hW0
      exact (this o).symm
    · rw [if_neg hW0, ← mul_assoc, mul_comm (W E) (g E o), mul_assoc,
        ENNReal.mul_inv_cancel hW0 (hWtop E), mul_one]
  -- `pe.probOf E = W E` when `E` terminates (a packaging of `hWeq`).
  have hprobW : ∀ (E : AlterSeq State Label) (hT : E.trans.Terminates),
      (∑' τ, q τ * (peOf τ).probOf E hT) = W E := by
    intro E hT
    rw [hWeq E]
    exact tsum_congr (fun τ => by rw [dif_pos hT])
  -- `pe.kernel` mixing identity at a prefix `E` (the inductive core).
  have hker_mix : ∀ (E : AlterSeq State Label) (hT : E.trans.Terminates) (last : Label × State),
      (∑' τ, q τ * (peOf τ).probOf E hT) * pe.kernel E last
        = ∑' τ, q τ * (peOf τ).probOf E hT * (peOf τ).kernel E last := by
    intro E hT last
    -- LHS = `W E * pe.kernel E last`.
    rw [hprobW E hT]
    -- expand `pe.kernel`; `pe.scheduler.next = σ.next` definitionally.
    change W E * (∑' μ, σ.next E (some (last.1, μ)) * μ last.2)
      = ∑' τ, q τ * (peOf τ).probOf E hT
          * (∑' μ, (schOf τ).next E (some (last.1, μ)) * μ last.2)
    -- push `W E` into the μ-sum.
    rw [← ENNReal.tsum_mul_left]
    -- `W E * (σ.next E (some (last.1, μ)) * μ last.2) = g E (some(last.1,μ)) * μ last.2`.
    have hstep : ∀ μ', W E * (σ.next E (some (last.1, μ')) * μ' last.2)
        = (∑' τ, q τ * (peOf τ).probOf E hT
            * (schOf τ).next E (some (last.1, μ'))) * μ' last.2 := by
      intro μ'
      rw [← mul_assoc, hcancel E (some (last.1, μ'))]
      -- `g E (some (last.1, μ'))` expands to the τ-sum (with the `dif_pos hT` branch).
      congr 1
      exact tsum_congr (fun τ => by rw [dif_pos hT])
    rw [tsum_congr hstep]
    -- push `* μ' last.2` inside the τ-sum, then swap τ/μ' and refactor.
    calc (∑' μ', (∑' τ, q τ * (peOf τ).probOf E hT
              * (schOf τ).next E (some (last.1, μ'))) * μ' last.2)
        = ∑' μ', ∑' τ, (q τ * (peOf τ).probOf E hT
              * (schOf τ).next E (some (last.1, μ'))) * μ' last.2 :=
          tsum_congr (fun μ' => ENNReal.tsum_mul_right.symm)
      _ = ∑' τ, ∑' μ', (q τ * (peOf τ).probOf E hT
              * (schOf τ).next E (some (last.1, μ'))) * μ' last.2 := ENNReal.tsum_comm
      _ = ∑' τ, q τ * (peOf τ).probOf E hT
              * (∑' μ', (schOf τ).next E (some (last.1, μ')) * μ' last.2) := by
          refine tsum_congr (fun τ => ?_)
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr (fun μ' => ?_)
          rw [mul_assoc]
  -- **Path-measure identity:** `pe.probOf = q`-mixture of `peOf τ` path-measures.
  have hprob : ∀ (e : AlterSeq State Label) (hFin : e.trans.Terminates),
      pe.probOf e hFin = ∑' τ, q τ * (peOf τ).probOf e hFin := by
    -- Generalize over the trans-list and start state, induct cons-end.
    suffices hgen : ∀ (L : List (Label × State)) (s₀ : State)
        (hFin : (Seq.ofList L : Seq (Label × State)).Terminates),
        pe.probOf ⟨s₀, Seq.ofList L⟩ hFin
          = ∑' τ, q τ * (peOf τ).probOf ⟨s₀, Seq.ofList L⟩ hFin by
      intro e hFin
      have hofl : (Seq.ofList (e.trans.toList hFin) : Seq (Label × State)) = e.trans :=
        Stream'.Seq.ofList_toList e.trans hFin
      have hFin' : (Seq.ofList (e.trans.toList hFin) : Seq (Label × State)).Terminates := by
        rw [hofl]; exact hFin
      have hkey := hgen (e.trans.toList hFin) e.init hFin'
      rw [pe.probOf_congr ⟨e.init, Seq.ofList (e.trans.toList hFin)⟩ e
        (by cases e; simp only [hofl]) hFin' hFin] at hkey
      rw [hkey]
      refine tsum_congr (fun τ => ?_)
      congr 1
      exact (peOf τ).probOf_congr ⟨e.init, Seq.ofList (e.trans.toList hFin)⟩ e
        (by cases e; simp only [hofl]) hFin' hFin
    intro L
    induction L using List.reverseRecOn with
    | nil =>
      intro s₀ hFin
      simp only [Stream'.Seq.ofList_nil]
      rw [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState]
      -- RHS: `∑' τ, q τ * (peOf τ).init s₀ = ∑' τ, q τ * (pure s) s₀`.
      have hrhs : ∀ τ, q τ
          * (peOf τ).probOf ⟨s₀, (Seq.nil : Seq (Label × State))⟩ Stream'.Seq.terminates_nil
          = q τ * (PMF.pure s) s₀ := by
        intro τ
        rw [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState]
      rw [tsum_congr hrhs, ENNReal.tsum_mul_right, q.tsum_coe, one_mul]
    | append_singleton rest last ih =>
      intro s₀ hFin
      -- `ofList (rest ++ [last]) = (ofList rest).append (cons last nil)`.
      have hsplit : (Seq.ofList (rest ++ [last]) : Seq (Label × State))
          = (Seq.ofList rest).append (Seq.cons last Seq.nil) := by
        rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
      have hrest_fin : (Seq.ofList rest : Seq (Label × State)).Terminates :=
        Stream'.Seq.terminates_ofList _
      -- the prefix execution.
      set E : AlterSeq State Label := ⟨s₀, Seq.ofList rest⟩ with hE
      -- rewrite both `probOf`s along the split into append-singleton form.
      have hFinS : ((Seq.ofList rest).append (Seq.cons last Seq.nil)).Terminates := by
        rw [← hsplit]; exact hFin
      rw [pe.probOf_congr ⟨s₀, Seq.ofList (rest ++ [last])⟩
          ⟨s₀, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩ (by rw [hsplit]) hFin hFinS,
        pe.probOf_append_singleton s₀ (Seq.ofList rest) hrest_fin last hFinS,
        show pe.probOf E hrest_fin = ∑' τ, q τ * (peOf τ).probOf E hrest_fin from
          ih s₀ hrest_fin]
      rw [tsum_congr (fun τ => by
        rw [(peOf τ).probOf_congr ⟨s₀, Seq.ofList (rest ++ [last])⟩
          ⟨s₀, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩ (by rw [hsplit]) hFin hFinS,
          (peOf τ).probOf_append_singleton s₀ (Seq.ofList rest) hrest_fin last hFinS,
          ← mul_assoc] : ∀ τ, q τ * (peOf τ).probOf ⟨s₀, Seq.ofList (rest ++ [last])⟩ hFin
            = q τ * (peOf τ).probOf E hrest_fin * (peOf τ).kernel E last)]
      exact hker_mix E hrest_fin last
  -- **Halting-mass identity:** `σ.haltMass = q`-mixture of `schOf τ`'s halt masses.
  have hhalt : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      σ.haltMass (PMF.pure s) e
        = ∑' τ, q τ * (schOf τ).haltMass (PMF.pure s) e := by
    intro e
    -- unfold both sides to `probOf · * next · none`.
    change pe.probOf e.1 e.2 * σ.next e.1 none
      = ∑' τ, q τ * ((peOf τ).probOf e.1 e.2 * (schOf τ).next e.1 none)
    -- `pe.probOf e.1 e.2 = W e.1`, then `W e.1 * σ.next e.1 none = g e.1 none` by `hcancel`.
    rw [hprob e.1 e.2, hprobW e.1 e.2, hcancel e.1 none]
    -- `g e.1 none = ∑' τ, q τ * (peOf τ).probOf e.1 e.2 * (schOf τ).next e.1 none`.
    refine tsum_congr (fun τ => ?_)
    rw [dif_pos e.2, mul_assoc]
  refine ⟨σ, ?_, ?_⟩
  · -- **Total halting mass is 1.**
    rw [tsum_congr hhalt]
    -- `∑' e, ∑' τ, q τ * (schOf τ).haltMass (pure s) e = ∑' τ, q τ * 1 = 1`.
    rw [ENNReal.tsum_comm]
    rw [show (∑' τ, ∑' e, q τ * (schOf τ).haltMass (PMF.pure s) e) = ∑' τ, q τ from
      tsum_congr (fun τ => ?_), q.tsum_coe]
    rw [ENNReal.tsum_mul_left]
    by_cases hτ : τ ∈ q.support
    · rw [hschOf]; simp only [dif_pos hτ]
      rw [(h τ hτ).witness_halts, mul_one]
    · rw [PMF.mem_support_iff, not_not] at hτ; rw [hτ, zero_mul]
  · -- **Pushforward to `q.bind id`.**
    intro x
    rw [PMF.bind_apply]
    -- LHS goal: `(q.bind id) x = ∑' e, σ.haltMass · * [end=x]`.
    rw [tsum_congr (fun e => by rw [hhalt e] :
      ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
        σ.haltMass (PMF.pure s) e * (if e.1.endState e.2 = x then (1 : ENNReal) else 0)
          = (∑' τ, q τ * (schOf τ).haltMass (PMF.pure s) e)
              * (if e.1.endState e.2 = x then (1 : ENNReal) else 0))]
    -- push the indicator into the τ-sum and swap.
    rw [tsum_congr (fun e => ENNReal.tsum_mul_right.symm :
      ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
        (∑' τ, q τ * (schOf τ).haltMass (PMF.pure s) e)
            * (if e.1.endState e.2 = x then (1 : ENNReal) else 0)
          = ∑' τ, q τ * (schOf τ).haltMass (PMF.pure s) e
              * (if e.1.endState e.2 = x then (1 : ENNReal) else 0))]
    rw [ENNReal.tsum_comm]
    refine (tsum_congr (fun τ => ?_)).symm
    -- per τ: `q τ * τ x = ∑' e, q τ * (schOf τ).haltMass · * [end=x]`.
    -- reassociate and factor `q τ` out of the `e`-sum.
    rw [tsum_congr (fun e => mul_assoc (q τ) _ _ :
      ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
        q τ * (schOf τ).haltMass (PMF.pure s) e
            * (if e.1.endState e.2 = x then (1 : ENNReal) else 0)
          = q τ * ((schOf τ).haltMass (PMF.pure s) e
              * (if e.1.endState e.2 = x then (1 : ENNReal) else 0)))]
    rw [ENNReal.tsum_mul_left]
    -- the inner `e`-sum is `τ x` on support; off support `q τ = 0`.
    by_cases hτ : τ ∈ q.support
    · congr 1
      rw [hschOf]; simp only [dif_pos hτ]
      exact ((h τ hτ).witness_pushforward x).symm
    · rw [PMF.mem_support_iff, not_not] at hτ
      rw [hτ, zero_mul, zero_mul]

/-- **Posterior-mixing for `weakTau`.** A `q`-indexed family of τ-closures
`weakTau sys (m x) (ν x)` combines into a single τ-closure from the mixed source
`q.bind m` to the mixed target `q.bind ν`, via the same Bayesian-posterior
mixing scheduler (composed with the per-point τ-witnesses through
`weakTau_bind`). -/
private theorem weakTau_mix {sys : System State Label} {X : Type}
    (q : PMF X) (m ν : X → PMF State)
    (H : ∀ x ∈ q.support, weakTau sys (m x) (ν x)) :
    weakTau sys (q.bind m) (q.bind ν) := by
  classical
  set ρ : X → State → PMF State :=
    fun x => if hx : x ∈ q.support then (weakTau_exists_pointwise (H x hx)).choose
      else fun t => PMF.pure t with hρ
  have hρ_spec : ∀ x (hx : x ∈ q.support),
      (∀ t ∈ (m x).support, weakTau sys (PMF.pure t) (ρ x t)) ∧ ν x = (m x).bind (ρ x) := by
    intro x hx
    have hch := (weakTau_exists_pointwise (H x hx)).choose_spec
    have hρx : ρ x = (weakTau_exists_pointwise (H x hx)).choose := by rw [hρ]; exact dif_pos hx
    rw [hρx]; exact hch
  set num : State → X → ENNReal := fun t x => q x * (m x) t with hnum
  have hnumsum : ∀ t, (∑' x, num t x) = (q.bind m) t := by
    intro t; rw [hnum, PMF.bind_apply]
  set post : (t : State) → (q.bind m) t ≠ 0 → PMF X :=
    fun t ht => PMF.normalize (num t) (by rw [hnumsum]; exact ht)
      (by rw [hnumsum]; exact (q.bind m).apply_ne_top t) with hpost
  have hZ : ∀ t (ht : (q.bind m) t ≠ 0) x, (q.bind m) t * (post t ht) x = num t x := by
    intro t ht x
    rw [hpost, PMF.normalize_apply, hnumsum, ← mul_assoc, mul_comm ((q.bind m) t) (num t x),
      mul_assoc, ENNReal.mul_inv_cancel ht ((q.bind m).apply_ne_top t), mul_one]
  set R : State → PMF State :=
    fun t => if ht : (q.bind m) t = 0 then PMF.pure t
      else (post t ht).bind (fun x => ρ x t) with hR
  have hR_pos : ∀ t (ht : (q.bind m) t ≠ 0), R t = (post t ht).bind (fun x => ρ x t) := by
    intro t ht; rw [hR]; exact dif_neg ht
  have hnum_supp : ∀ t x, num t x ≠ 0 → x ∈ q.support ∧ t ∈ (m x).support := by
    intro t x hne
    rw [hnum, mul_ne_zero_iff] at hne
    exact ⟨(PMF.mem_support_iff q x).mpr hne.1, (PMF.mem_support_iff (m x) t).mpr hne.2⟩
  have hpt : ∀ t ∈ (q.bind m).support, weakTau sys (PMF.pure t) (R t) := by
    intro t ht
    have htne : (q.bind m) t ≠ 0 := (PMF.mem_support_iff _ t).mp ht
    rw [hR_pos t htne]
    have hbind : ((post t htne).map (fun x => ρ x t)).bind id
        = (post t htne).bind (fun x => ρ x t) := by
      rw [PMF.map, PMF.bind_bind]; simp [PMF.pure_bind]
    rw [← hbind]
    refine weakTau_bind ?_
    intro τ hτ
    obtain ⟨x, hx, hxτ⟩ := (PMF.mem_support_map_iff _ _ τ).mp hτ
    have hnumne : num t x ≠ 0 := by
      rw [hpost, PMF.mem_support_normalize_iff] at hx; exact hx
    obtain ⟨hxq, htm⟩ := hnum_supp t x hnumne
    rw [← hxτ]
    exact (hρ_spec x hxq).1 t htm
  have hmain := weakTau_of_pointwise R hpt
  have heq : (q.bind m).bind R = q.bind ν := by
    refine PMF.ext (fun y => ?_)
    conv_lhs => rw [PMF.bind_apply]
    have hterm : ∀ t, (q.bind m) t * (R t) y = ∑' x, num t x * (ρ x t) y := by
      intro t
      by_cases ht : (q.bind m) t = 0
      · rw [ht, zero_mul]
        refine (ENNReal.tsum_eq_zero.mpr (fun x => ?_)).symm
        have hz : (∑' x, num t x) = 0 := by rw [hnumsum]; exact ht
        rw [ENNReal.tsum_eq_zero] at hz
        rw [hz x, zero_mul]
      · rw [hR_pos t ht, PMF.bind_apply (post t ht), ← ENNReal.tsum_mul_left]
        refine tsum_congr (fun x => ?_)
        rw [← mul_assoc, hZ t ht x]
    rw [tsum_congr hterm, ENNReal.tsum_comm]
    conv_rhs => rw [PMF.bind_apply]
    refine tsum_congr (fun x => ?_)
    by_cases hx : x ∈ q.support
    · rw [hnum]
      simp only
      rw [show (∑' t, q x * (m x) t * (ρ x t) y)
          = q x * ∑' t, (m x) t * (ρ x t) y from by
        rw [← ENNReal.tsum_mul_left]; exact tsum_congr (fun t => by ring)]
      congr 1
      rw [← PMF.bind_apply, ← (hρ_spec x hx).2]
    · rw [PMF.mem_support_iff, not_not] at hx
      rw [hx, zero_mul]
      refine ENNReal.tsum_eq_zero.mpr (fun t => ?_)
      rw [hnum]
      simp only [hx, zero_mul]
  rw [heq] at hmain
  exact hmain

/-- **Source-mixing for `weakStep`.** A `μ`-indexed family of weak steps from
single points recombines into one weak step from the mixed source `μ`. The three
layers (τ-closure, hyper-step, τ-closure) are mixed separately via
`weakTau_of_pointwise`, `hyperStep_mix` and `weakTau_mix`. -/
theorem weakStep_of_pointwise {sys : System State Label} {μ : PMF State}
    {l : Label} (ρ : State → PMF State)
    (h : ∀ s ∈ μ.support, weakStep sys (PMF.pure s) l (ρ s)) :
    weakStep sys μ l (μ.bind ρ) := by
  classical
  -- per-point witnesses for the three layers (junk off support)
  set a : State → PMF State :=
    fun s => if hs : s ∈ μ.support then (h s hs).choose else PMF.pure s with ha
  set b : State → PMF State :=
    fun s => if hs : s ∈ μ.support then (h s hs).choose_spec.choose else PMF.pure s with hb
  have hspec : ∀ s (hs : s ∈ μ.support),
      weakTau sys (PMF.pure s) (a s) ∧ hyperStep sys (a s) l (b s)
        ∧ weakTau sys (b s) (ρ s) := by
    intro s hs
    have h1 := (h s hs).choose_spec.choose_spec
    have hax : a s = (h s hs).choose := by rw [ha]; exact dif_pos hs
    have hbx : b s = (h s hs).choose_spec.choose := by rw [hb]; exact dif_pos hs
    rw [hax, hbx]; exact h1
  refine ⟨μ.bind a, μ.bind b, ?_, ?_, ?_⟩
  · exact weakTau_of_pointwise a (fun s hs => (hspec s hs).1)
  · exact hyperStep_mix μ a b (fun s hs => (hspec s hs).2.1)
  · exact weakTau_mix μ b ρ (fun s hs => (hspec s hs).2.2)

/-- **Target-convexity for `weakStep`** (the crux). A mixture (`q.bind id`) of
weak-step targets, all reached from the *same* single point `pure s`, is itself a
weak-step target from `pure s`. The pre-τ-closure is recombined by the
target-convexity lemma `weakTau_bind`; the hyper-step and post-τ-closure layers
are mixed by `hyperStep_mix` and `weakTau_mix`. -/
theorem weakStep_bind {sys : System State Label} {s : State} {l : Label}
    {q : PMF (PMF State)} (h : ∀ τ ∈ q.support, weakStep sys (PMF.pure s) l τ) :
    weakStep sys (PMF.pure s) l (q.bind id) := by
  classical
  -- per-target witnesses for the three layers (junk off support)
  set a : PMF State → PMF State :=
    fun τ => if hτ : τ ∈ q.support then (h τ hτ).choose else PMF.pure s with ha
  set b : PMF State → PMF State :=
    fun τ => if hτ : τ ∈ q.support then (h τ hτ).choose_spec.choose else PMF.pure s with hb
  have hspec : ∀ τ (hτ : τ ∈ q.support),
      weakTau sys (PMF.pure s) (a τ) ∧ hyperStep sys (a τ) l (b τ)
        ∧ weakTau sys (b τ) τ := by
    intro τ hτ
    have h1 := (h τ hτ).choose_spec.choose_spec
    have haτ : a τ = (h τ hτ).choose := by rw [ha]; exact dif_pos hτ
    have hbτ : b τ = (h τ hτ).choose_spec.choose := by rw [hb]; exact dif_pos hτ
    rw [haτ, hbτ]; exact h1
  refine ⟨q.bind a, q.bind b, ?_, ?_, ?_⟩
  · -- pre: weakTau sys (pure s) (q.bind a), via weakTau_bind on q.map a
    have hbind : (q.map a).bind id = q.bind a := by
      rw [PMF.map, PMF.bind_bind]; simp [PMF.pure_bind]
    rw [← hbind]
    refine weakTau_bind ?_
    intro τ' hτ'
    obtain ⟨τ, hτ, hτaτ⟩ := (PMF.mem_support_map_iff _ _ τ').mp hτ'
    rw [← hτaτ]
    exact (hspec τ hτ).1
  · exact hyperStep_mix q a b (fun τ hτ => (hspec τ hτ).2.1)
  · exact weakTau_mix q b id (fun τ hτ => (hspec τ hτ).2.2)

/-- **(A1).** A `weakTau` from a distribution `μ` is a `hyperStep` over the weak
closure `sys^w`. -/
theorem hyperStep_weakClosure_of_weakTau {sys : System State Label}
    {μ ν : PMF State} {l : Label} (hl : (l = Silent.τ)) (h : weakTau sys μ ν) :
    hyperStep sys^w μ l ν := by
  obtain ⟨ρ, hρ, hν⟩ := weakTau_exists_pointwise h
  refine ⟨fun s => PMF.pure (ρ s), ?_, ?_⟩
  · intro s hs τ hτ
    rw [PMF.mem_support_pure_iff] at hτ; subst hτ
    exact Or.inl ⟨hl, hρ s hs⟩
  · rw [hν]; simp only [PMF.pure_bind, id_eq]

/-- **(A2).** A `hyperStep` over `sys^w` at an internal label collapses to a
single `weakTau` from the distribution. -/
theorem weakTau_of_hyperStep_weakClosure {sys : System State Label}
    {μ ν : PMF State} {l : Label} (hl : (l = Silent.τ)) (h : hyperStep sys^w μ l ν) :
    weakTau sys μ ν := by
  obtain ⟨p, hp, hν⟩ := h
  have hpt : ∀ s ∈ μ.support, weakTau sys (PMF.pure s) ((p s).bind id) := by
    intro s hs
    refine weakTau_bind ?_
    intro τ hτ
    rcases hp s hs τ hτ with ⟨_, hwt⟩ | ⟨hi, _⟩
    · exact hwt
    · exact absurd hl hi
  rw [hν]
  exact weakTau_of_pointwise _ hpt

/-- **(B1).** A `weakStep` from a distribution `μ` is a `hyperStep` over the weak
closure `sys^w`. -/
theorem hyperStep_weakClosure_of_weakStep {sys : System State Label}
    {μ ν : PMF State} {l : Label} (hl : ¬ (l = Silent.τ)) (h : weakStep sys μ l ν) :
    hyperStep sys^w μ l ν := by
  obtain ⟨ρ, hρ, hν⟩ := weakStep_exists_pointwise h
  refine ⟨fun s => PMF.pure (ρ s), ?_, ?_⟩
  · intro s hs τ hτ
    rw [PMF.mem_support_pure_iff] at hτ; subst hτ
    exact Or.inr ⟨hl, hρ s hs⟩
  · rw [hν]; simp only [PMF.pure_bind, id_eq]

/-- **(B2).** A `hyperStep` over `sys^w` at an external label collapses to a
single `weakStep` from the distribution. -/
theorem weakStep_of_hyperStep_weakClosure {sys : System State Label}
    {μ ν : PMF State} {l : Label} (hl : ¬ (l = Silent.τ)) (h : hyperStep sys^w μ l ν) :
    weakStep sys μ l ν := by
  obtain ⟨p, hp, hν⟩ := h
  have hpt : ∀ s ∈ μ.support, weakStep sys (PMF.pure s) l ((p s).bind id) := by
    intro s hs
    refine weakStep_bind ?_
    intro τ hτ
    rcases hp s hs τ hτ with ⟨hi, _⟩ | ⟨_, hws⟩
    · exact absurd hi hl
    · exact hws
  rw [hν]
  exact weakStep_of_pointwise _ hpt

end PLTS
