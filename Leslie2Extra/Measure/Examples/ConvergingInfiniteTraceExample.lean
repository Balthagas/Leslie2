/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2Extra.Measure.Examples.InfiniteTraceExample

/-!
# A worked example: an infinite trace as the limit of a converging phenomenon

Here the process is genuinely random at *every* step: after emitting `n` copies of
`a`, it continues with probability `P (n+1) / P n` and halts otherwise, where
`P n = 1/2 + (1/2)^(n+1)`. There is **no deterministic `aω` tail** — at each step
there is a real chance to stop. The survival probabilities
`traceProb (aⁿ) = P n = 1/2 + (1/2)^(n+1)` form a strictly decreasing sequence
converging to `1/2`, and the infinite trace picks up exactly that limit:

* `contExec.traceMeasure {aω} = ⨅ₙ traceProb (aⁿ) = 1/2`,

with `1/2 = ⨅ₙ P n` the limit of the converging phenomenon. The initial state is a
Dirac (`Unit`), so this is an *achievable* trace measure, with all randomness in
the scheduler.
-/

open MeasureTheory ProbabilityTheory Finset Stream' Filter Topology

namespace PLTS
namespace ConvergingInfiniteTraceExample

open InfiniteTraceExample (L2 aOmega aOmega_get? iInter_cone_eq_aOmega eN eN_terminates)

/-! ### The survival sequence `P n = 1/2 + (1/2)^(n+1)` -/

/-- The survival probability after `n` steps. Strictly decreasing, `P 0 = 1`, limit `1/2`. -/
noncomputable def P (n : ℕ) : ENNReal := 1 / 2 + (1 / 2) ^ (n + 1)

@[simp] theorem P_zero : P 0 = 1 := by
  rw [P, pow_one]; exact ENNReal.add_halves 1

theorem P_ge_half (n : ℕ) : (1 : ENNReal) / 2 ≤ P n := le_self_add

theorem P_ne_top (n : ℕ) : P n ≠ ⊤ := by
  rw [P]; exact ENNReal.add_ne_top.mpr ⟨by norm_num, ENNReal.pow_ne_top (by norm_num)⟩

theorem P_ne_zero (n : ℕ) : P n ≠ 0 :=
  fun h => by have := P_ge_half n; rw [h] at this; simp at this

theorem P_antitone : Antitone P := by
  intro m n hmn
  have hpow : (1 / 2 : ENNReal) ^ (n + 1) ≤ (1 / 2) ^ (m + 1) := by
    rw [show n + 1 = (m + 1) + (n - m) from by omega, pow_add]
    exact mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le (by norm_num))
  simp only [P]
  exact add_le_add le_rfl hpow

/-- **The limit of the converging phenomenon is `1/2`.** -/
theorem iInf_P : ⨅ n, P n = 1 / 2 := by
  have h0 : Tendsto (fun n => (1 / 2 : ENNReal) ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have h1 : Tendsto (fun n => (1 / 2 : ENNReal) ^ (n + 1)) atTop (𝓝 0) :=
    h0.comp (tendsto_add_atTop_nat 1)
  have hP : Tendsto P atTop (𝓝 (1 / 2)) := by
    have h2 := h1.const_add (1 / 2 : ENNReal)
    rwa [add_zero] at h2
  exact tendsto_nhds_unique (tendsto_atTop_iInf P_antitone) hP

/-! ### The system: continue with probability `P (n+1) / P n`, else halt -/

/-- The continue-probability after `n` steps. -/
noncomputable def contProb (n : ℕ) : ENNReal := P (n + 1) / P n

theorem contProb_le_one (n : ℕ) : contProb n ≤ 1 := by
  rw [contProb]
  calc P (n + 1) / P n ≤ P n / P n := by gcongr; exact P_antitone (Nat.le_succ n)
    _ = 1 := ENNReal.div_self (P_ne_zero n) (P_ne_top n)

open Classical in
/-- The one-step distribution after `n` steps: emit `a` (to the single state) with
probability `contProb n`, halt otherwise. -/
noncomputable def stepPMFn (n : ℕ) : PMF (Option (L2 × PMF Unit)) :=
  ⟨fun o => if o = some (L2.a, PMF.pure ()) then contProb n
            else if o = none then 1 - contProb n else 0, by
    classical
    rw [ENNReal.summable.hasSum_iff, ENNReal.tsum_eq_add_tsum_ite (some (L2.a, PMF.pure ()))]
    rw [if_pos rfl, tsum_eq_single none]
    · rw [if_neg (by simp : ¬ ((none : Option (L2 × PMF Unit)) = some (L2.a, PMF.pure ()))),
          if_neg (by simp : ¬ ((none : Option (L2 × PMF Unit)) = some (L2.a, PMF.pure ()))),
          if_pos rfl]
      exact add_tsub_cancel_of_le (contProb_le_one n)
    · intro b' hb'
      by_cases hb : b' = some (L2.a, PMF.pure ())
      · rw [if_pos hb]
      · rw [if_neg hb, if_neg hb, if_neg hb']⟩

/-- A one-state system that only ever performs the external step `a`. -/
noncomputable def contSys : System Unit L2 where
  init := ()
  step _ l μ := l = L2.a ∧ μ = PMF.pure ()

/-- The scheduler: continue/halt according to `stepPMFn` indexed by the history length. -/
noncomputable def contSched : Scheduler contSys where
  next e := open Classical in
    if h : e.trans.Terminates then stepPMFn (e.trans.length h) else PMF.pure none
  valid := by
    classical
    intro e n s hterm_n _ l μ h_supp
    have hterm : e.trans.Terminates := ⟨n, hterm_n⟩
    rw [dif_pos hterm, PMF.mem_support_iff] at h_supp
    have hval : (stepPMFn (e.trans.length hterm)) (some (l, μ))
        = if some (l, μ) = some (L2.a, PMF.pure ()) then contProb (e.trans.length hterm)
          else if some (l, μ) = none then 1 - contProb (e.trans.length hterm) else 0 := rfl
    rw [hval] at h_supp
    by_cases h : some (l, μ) = some (L2.a, PMF.pure ())
    · rw [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨h.1, h.2⟩
    · rw [if_neg h, if_neg (by simp : ¬ (some (l, μ) = none))] at h_supp
      exact absurd rfl h_supp

noncomputable def contExec : ProbabilisticExecution contSys := ⟨PMF.pure (), contSched⟩

/-! ### Every finite `a`-cone has mass `P n` (the crux) -/

/-- `length` of `Seq.ofList` is `List.length` (re-derived locally). -/
private theorem length_ofList {γ : Type} (L : List γ) :
    (Stream'.Seq.ofList L).length (Stream'.Seq.terminates_ofList L) = L.length := by
  rw [← Stream'.Seq.length_toList, Stream'.Seq.toList_ofList]

open Classical in
/-- `stepPMFn k` on the `a`-labelled step continues iff the emitted PMF is `pure ()`. -/
private theorem stepPMFn_some_a (k : ℕ) (μ : PMF Unit) :
    (stepPMFn k) (some (L2.a, μ)) = if μ = PMF.pure () then contProb k else 0 := by
  classical
  change (if some (L2.a, μ) = some (L2.a, PMF.pure ()) then contProb k
        else if some (L2.a, μ) = none then 1 - contProb k else 0)
      = if μ = PMF.pure () then contProb k else 0
  by_cases hμ : μ = PMF.pure ()
  · rw [if_pos (by rw [hμ]), if_pos hμ]
  · rw [if_neg (by rw [Option.some.injEq, Prod.mk.injEq]; rintro ⟨_, h2⟩; exact hμ h2),
        if_neg (by simp), if_neg hμ]

/-- The one-step kernel on the `a`-step after `k` steps is `contProb k`. -/
private theorem kernel_len (k : ℕ) :
    contExec.kernel ⟨(), Seq.ofList (List.replicate k (L2.a, ()))⟩ (L2.a, ()) = contProb k := by
  classical
  change (∑' μ : PMF Unit,
      contExec.scheduler.next ⟨(), Seq.ofList (List.replicate k (L2.a, ()))⟩ (some (L2.a, μ))
        * μ ())
    = contProb k
  have hnext :
      contExec.scheduler.next ⟨(), Seq.ofList (List.replicate k (L2.a, ()))⟩ = stepPMFn k := by
    change (if h : (Seq.ofList (List.replicate k (L2.a, ())) : Seq (L2 × Unit)).Terminates then
           stepPMFn ((Seq.ofList (List.replicate k (L2.a, ()))).length h) else PMF.pure none)
        = stepPMFn k
    rw [dif_pos (Stream'.Seq.terminates_ofList _), length_ofList, List.length_replicate]
  rw [hnext]
  simp only [stepPMFn_some_a]
  rw [tsum_eq_single (PMF.pure ())]
  · rw [if_pos rfl, PMF.pure_apply_self, mul_one]
  · intro μ hμ
    rw [if_neg hμ, zero_mul]

/-- The `n`-fold `a`-execution has probability `P n`. -/
private theorem probOf_eN (n : ℕ) : contExec.probOf (eN n) (eN_terminates n) = P n := by
  induction n with
  | zero =>
    have h_eq : eN 0 = ⟨(), (Seq.nil : Seq (L2 × Unit))⟩ := by
      simp only [eN, List.replicate_zero, Stream'.Seq.ofList_nil]
    rw [contExec.probOf_congr (eN 0) ⟨(), Seq.nil⟩ h_eq (eN_terminates 0)
        Stream'.Seq.terminates_nil, contExec.probOf_nil]
    change (PMF.pure () : PMF Unit) () = P 0
    rw [PMF.pure_apply_self, P_zero]
  | succ n ih =>
    have hsq : (Seq.ofList (List.replicate n (L2.a, ())) : Seq (L2 × Unit)).Terminates :=
      Stream'.Seq.terminates_ofList _
    have h_eq : eN (n + 1) = ⟨(),
        (Seq.ofList (List.replicate n (L2.a, ()))).append (Seq.cons (L2.a, ()) Seq.nil)⟩ := by
      simp only [eN]
      congr 1
      rw [List.replicate_succ', Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons,
        Stream'.Seq.ofList_nil]
    rw [contExec.probOf_congr (eN (n + 1)) _ h_eq (eN_terminates (n + 1))
        (h_eq ▸ eN_terminates (n + 1)),
      contExec.probOf_append_singleton () (Seq.ofList (List.replicate n (L2.a, ()))) hsq (L2.a, ()),
      kernel_len n,
      show contExec.probOf ⟨(), Seq.ofList (List.replicate n (L2.a, ()))⟩ hsq = P n from ih,
      contProb]
    exact ENNReal.mul_div_cancel' (fun h => absurd h (P_ne_zero n)) (fun h => absurd h (P_ne_top n))

/-- The scheduler never emits a non-`a` label, so any step with `l ≠ a` has zero mass. -/
private theorem next_some_ne_a (e : AlterSeq Unit L2) (l : L2) (μ : PMF Unit) (hl : ¬ l = L2.a) :
    contExec.scheduler.next e (some (l, μ)) = 0 := by
  classical
  change (if h : e.trans.Terminates then stepPMFn (e.trans.length h) else PMF.pure none)
      (some (l, μ)) = 0
  by_cases hT : e.trans.Terminates
  · rw [dif_pos hT]
    change (if some (l, μ) = some (L2.a, PMF.pure ()) then contProb (e.trans.length hT)
          else if some (l, μ) = none then 1 - contProb (e.trans.length hT) else 0) = 0
    rw [if_neg (by rw [Option.some.injEq, Prod.mk.injEq]; rintro ⟨h1, _⟩; exact hl h1),
        if_neg (by simp)]
  · rw [dif_neg hT]
    exact PMF.pure_apply_of_ne _ _ (Option.some_ne_none _)

/-- Any step with a non-`a` label has zero kernel mass. -/
private theorem kernel_zero_of_ne_a (e : AlterSeq Unit L2) (l : L2) (s : Unit) (hl : ¬ l = L2.a) :
    contExec.kernel e (l, s) = 0 := by
  change (∑' μ : PMF Unit, contExec.scheduler.next e (some (l, μ)) * μ s) = 0
  rw [ENNReal.tsum_eq_zero]
  intro μ
  rw [next_some_ne_a e l μ hl, zero_mul]

/-- Any execution containing a non-`a` transition has probability `0`. -/
private theorem probOf_zero_of_nonA (i : Unit) :
    ∀ (L : List (L2 × Unit)), (∃ p ∈ L, ¬ p.1 = L2.a) →
      contExec.probOf ⟨i, Seq.ofList L⟩ (Stream'.Seq.terminates_ofList L) = 0 := by
  intro L
  induction L using List.reverseRecOn with
  | nil => rintro ⟨p, hp, -⟩; cases hp
  | append_singleton rest last ih =>
    intro hex
    obtain ⟨l0, s0⟩ := last
    have hrest_term : (Seq.ofList rest : Seq (L2 × Unit)).Terminates :=
      Stream'.Seq.terminates_ofList _
    have happ_trans : (Seq.ofList (rest ++ [(l0, s0)]) : Seq (L2 × Unit))
        = (Seq.ofList rest).append (Seq.cons (l0, s0) Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have heq : (⟨i, Seq.ofList (rest ++ [(l0, s0)])⟩ : AlterSeq Unit L2)
        = ⟨i, (Seq.ofList rest).append (Seq.cons (l0, s0) Seq.nil)⟩ := by rw [happ_trans]
    rw [contExec.probOf_congr _ _ heq (Stream'.Seq.terminates_ofList _)
        (happ_trans ▸ Stream'.Seq.terminates_ofList (rest ++ [(l0, s0)])),
      contExec.probOf_append_singleton i (Seq.ofList rest) hrest_term (l0, s0)]
    by_cases hlast : l0 = L2.a
    · have hrest_ex : ∃ p ∈ rest, ¬ p.1 = L2.a := by
        obtain ⟨p, hp, hpa⟩ := hex
        rw [List.mem_append] at hp
        rcases hp with hp | hp
        · exact ⟨p, hp, hpa⟩
        · rw [List.mem_singleton] at hp; subst hp; exact absurd hlast hpa
      rw [ih hrest_ex, zero_mul]
    · rw [kernel_zero_of_ne_a (⟨i, Seq.ofList rest⟩ : AlterSeq Unit L2) l0 s0 hlast, mul_zero]

/-- Filtering a list-sequence all of whose elements satisfy `p` leaves it unchanged. -/
private theorem filter_ofList_all {γ : Type} {p : γ → Prop} :
    ∀ (M : List γ), (∀ x ∈ M, p x) → (Stream'.Seq.ofList M).filter p = Stream'.Seq.ofList M := by
  intro M
  induction M with
  | nil => intro _; rw [Stream'.Seq.ofList_nil, Stream'.Seq.filter_nil]
  | cons a t ih =>
    intro hall
    rw [Stream'.Seq.ofList_cons,
      Stream'.Seq.filter_cons_pos a _ (hall a List.mem_cons_self),
      ih (fun x hx => hall x (List.mem_cons_of_mem a hx))]

/-- **`traceProb (aⁿ) = P n`** — the strictly decreasing survival sequence. -/
theorem traceProb_aN (n : ℕ) :
    contSys.traceProb contExec (Seq.ofList (List.replicate n L2.a)) = P n := by
  classical
  unfold System.traceProb
  rw [tsum_eq_single
    ⟨eN n, eN_terminates n, InfiniteTraceExample.trace_eN n, InfiniteTraceExample.isTight_eN n⟩]
  · exact probOf_eN n
  · rintro ⟨e, hterm, htrace, htight⟩ hne
    by_cases hAllA : ∀ p ∈ e.trans.toList hterm, p.1 = L2.a
    · -- Every transition is `a`; combined with tightness and trace `= aⁿ`, force `e = eN n`.
      have htt := (contSys.tight_iff (Seq.ofList (List.replicate n L2.a)) e hterm).mp
        ⟨htrace, htight⟩
      have hall_ne_tau : ∀ x ∈ (e.trans.toList hterm).map Prod.fst, ¬ x = Silent.τ := by
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        rw [hAllA p hp]
        exact InfiniteTraceExample.a_ne_tau
      have hfilter := htt.1
      rw [filter_ofList_all ((e.trans.toList hterm).map Prod.fst) hall_ne_tau] at hfilter
      have hmapeq : (e.trans.toList hterm).map Prod.fst = List.replicate n L2.a :=
        Stream'.Seq.ofList_injective hfilter
      have hlen : (e.trans.toList hterm).length = n := by
        have hc := congrArg List.length hmapeq
        rwa [List.length_map, List.length_replicate] at hc
      have hL : e.trans.toList hterm = List.replicate n (L2.a, ()) := by
        have hall2 : ∀ b ∈ e.trans.toList hterm, b = (L2.a, ()) := fun p hp =>
          Prod.ext_iff.mpr ⟨hAllA p hp, rfl⟩
        have hrep := List.eq_replicate_length.mpr hall2
        rwa [hlen] at hrep
      have hfinal : e = eN n := by
        have h1 : e.trans = (eN n).trans := by
          change e.trans = Seq.ofList (List.replicate n (L2.a, ()))
          rw [← Stream'.Seq.ofList_toList e.trans hterm, hL]
        have h2 : e.init = (eN n).init := rfl
        calc e = ⟨e.init, e.trans⟩ := rfl
          _ = ⟨(eN n).init, (eN n).trans⟩ := by rw [h1, h2]
          _ = eN n := rfl
      exact absurd (Subtype.ext hfinal) hne
    · -- Some transition is non-`a`; the scheduler assigns it zero mass.
      simp only [not_forall, exists_prop] at hAllA
      rw [contExec.probOf_congr e ⟨e.init, Seq.ofList (e.trans.toList hterm)⟩
        (by calc e = ⟨e.init, e.trans⟩ := rfl
              _ = ⟨e.init, Seq.ofList (e.trans.toList hterm)⟩ := by
                rw [Stream'.Seq.ofList_toList])
        hterm (Stream'.Seq.terminates_ofList _)]
      exact probOf_zero_of_nonA e.init (e.trans.toList hterm) hAllA

theorem traceMeasure_cone_aN (n : ℕ) :
    contExec.traceMeasure (cone (List.replicate n L2.a)) = P n := by
  rw [contExec.traceMeasure_cone, traceProb_aN]

/-! ### Assembly -/

/-- **The infinite trace `aω` has measure `1/2`, the limit of the strictly
decreasing survival probabilities `P n`** (neither `0` nor `1`). -/
theorem traceMeasure_aOmega_converging : contExec.traceMeasure {aOmega} = 1 / 2 := by
  rw [← iInter_cone_eq_aOmega]
  have hanti : Antitone (fun n => cone (List.replicate n L2.a)) := by
    intro m n hmn σ hσ k v hk
    rw [Stream'.Seq.ofList_get?, List.getElem?_replicate] at hk
    have hkm : k < m := by by_contra hc; rw [if_neg hc] at hk; exact absurd hk (by simp)
    rw [if_pos hkm] at hk
    apply hσ k v
    rw [Stream'.Seq.ofList_get?, List.getElem?_replicate, if_pos (lt_of_lt_of_le hkm hmn)]
    exact hk
  have hmeas : ∀ n, NullMeasurableSet (cone (List.replicate n L2.a)) contExec.traceMeasure :=
    fun n => (measurableSet_cone _).nullMeasurableSet
  have hfin : ∃ n, contExec.traceMeasure (cone (List.replicate n L2.a)) ≠ ⊤ := by
    refine ⟨0, ?_⟩; rw [traceMeasure_cone_aN]; exact P_ne_top 0
  rw [hanti.measure_iInter hmeas hfin]
  simp only [traceMeasure_cone_aN]
  exact iInf_P

end ConvergingInfiniteTraceExample
end PLTS
