/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Measure.Examples.InfiniteTraceExample

/-!
# A worked example: an infinite trace with measure `1/2`

Refining `InfiniteTraceExample`, here a coin is flipped in the *initial
distribution*: with probability `1/2` the system starts in the `true` state and
emits `a` forever (trace `aω`); with probability `1/2` it starts in `false` and
halts immediately (empty trace). The infinite trace `aω` therefore has measure
exactly `1/2` — strictly between `0` and `1`:

* `mixExec.traceMeasure {aω} = 1/2`.

The computation uses that `traceProb` is **linear in the initial distribution**
(`ProbabilisticExecution.probOf_init_mix`), reducing to the two Dirac cases
`traceProb_true (aⁿ) = 1` (the `aω` branch) and `traceProb_false (aⁿ) = 0` (the
halting branch), which are combined with the `1/2 : 1/2` coin.
-/

open MeasureTheory ProbabilityTheory Finset Stream'

namespace PLTS
namespace HalfInfiniteTraceExample

open InfiniteTraceExample (L2 aOmega aOmega_get? iInter_cone_eq_aOmega)

/-- The fair coin on the initial state (`true` with prob `1/2`, `false` with prob `1/2`). -/
noncomputable def bern : PMF Bool :=
  ⟨fun _ => 1 / 2, by
    rw [ENNReal.summable.hasSum_iff, tsum_bool]; exact ENNReal.add_halves 1⟩

/-- A two-state system: `true` loops on `a`, `false` halts. The step relation allows
the `a`-to-`true` transition from any state (the halting is enacted by the scheduler). -/
noncomputable def mixSys : System Bool L2 where
  init := true
  step _ l μ := l = L2.a ∧ μ = PMF.pure true

/-- The scheduler: emit `a` (to `true`) while the current state is `true`, else halt. -/
noncomputable def mixSched : Scheduler mixSys where
  next e := open Classical in
    if h : e.trans.Terminates then
      (if e.endState h then PMF.pure (some (L2.a, PMF.pure true)) else PMF.pure none)
    else PMF.pure none
  valid := by
    classical
    intro e n s hterm_n _ l μ h_supp
    have hterm : e.trans.Terminates := ⟨n, hterm_n⟩
    rw [dif_pos hterm] at h_supp
    by_cases hb : e.endState hterm = true
    · rw [if_pos hb, PMF.mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at h_supp
      obtain ⟨rfl, rfl⟩ := h_supp
      exact ⟨rfl, rfl⟩
    · rw [if_neg hb, PMF.mem_support_pure_iff] at h_supp
      exact absurd h_supp (by simp)

/-- The mixed-initial-distribution execution. -/
noncomputable def mixExec : ProbabilisticExecution mixSys := ⟨bern, mixSched⟩

@[simp] theorem bern_true : bern true = 1 / 2 := rfl
@[simp] theorem bern_false : bern false = 1 / 2 := rfl

/-! ### The two Dirac branches -/

/-- The Dirac-`true` execution: `a`-loops forever. -/
private noncomputable def peTrue : ProbabilisticExecution mixSys := ⟨PMF.pure true, mixSched⟩

/-- The finite `a`-loop of length `n` from state `true`. -/
private def et (n : ℕ) : AlterSeq Bool L2 := ⟨true, Seq.ofList (List.replicate n (L2.a, true))⟩

private theorem et_terminates (n : ℕ) : (et n).trans.Terminates := Seq.terminates_ofList _

/-- `endState` is invariant under changing the (equal) execution. -/
private theorem endState_congr' (e e' : AlterSeq Bool L2) (heq : e = e')
    (h : e.trans.Terminates) (h' : e'.trans.Terminates) : e.endState h = e'.endState h' := by
  subst heq; rfl

/-- The end state of a list-form execution is the destination of its last step. -/
private theorem endState_ofList' (s₀ : Bool) (L : List (L2 × Bool)) :
    (⟨s₀, Seq.ofList L⟩ : AlterSeq Bool L2).endState (Seq.terminates_ofList L)
      = (L.getLast?.map Prod.snd).getD s₀ := by
  induction L using List.reverseRecOn with
  | nil =>
    rw [AlterSeq.endState_of_trans_nil _ Stream'.Seq.ofList_nil]
    rfl
  | append_singleton L x _ =>
    obtain ⟨l, s⟩ := x
    have happ_trans : (Seq.ofList (L ++ [(l, s)]) : Seq (L2 × Bool))
        = (Seq.ofList L).append (Seq.cons (l, s) Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have heq : (⟨s₀, Seq.ofList (L ++ [(l, s)])⟩ : AlterSeq Bool L2)
        = ⟨s₀, (Seq.ofList L).append (Seq.cons (l, s) Seq.nil)⟩ := by rw [happ_trans]
    rw [endState_congr' _ _ heq (Seq.terminates_ofList _)
        (happ_trans ▸ Seq.terminates_ofList (L ++ [(l, s)]))]
    rw [show (⟨s₀, (Seq.ofList L).append (Seq.cons (l, s) Seq.nil)⟩ : AlterSeq Bool L2).endState
          (happ_trans ▸ Seq.terminates_ofList (L ++ [(l, s)])) = s from
        AlterSeq.endState_append_singleton ⟨s₀, Seq.ofList L⟩ (Seq.terminates_ofList L) l s]
    simp

/-- Every `replicate`-prefix from `true` ends in state `true`. -/
private theorem endState_replicate_true (k : ℕ) :
    (⟨true, Seq.ofList (List.replicate k (L2.a, true))⟩ : AlterSeq Bool L2).endState
      (Seq.terminates_ofList _) = true := by
  rw [endState_ofList']
  cases k with
  | zero => rfl
  | succ j => rw [List.getLast?_replicate]; simp

/-- From a `true`-ending prefix the scheduler emits `a` to `true` with kernel mass `1`. -/
private theorem kernel_true (e : AlterSeq Bool L2) (h : e.trans.Terminates)
    (hend : e.endState h = true) : peTrue.kernel e (L2.a, true) = 1 := by
  classical
  change (∑' μ : PMF Bool, peTrue.scheduler.next e (some (L2.a, μ)) * μ true) = 1
  have hn : peTrue.scheduler.next e = PMF.pure (some (L2.a, PMF.pure true)) := by
    have hrw : peTrue.scheduler.next e = if h' : e.trans.Terminates then
        (if e.endState h' = true then PMF.pure (some (L2.a, PMF.pure true)) else PMF.pure none)
        else PMF.pure none := rfl
    rw [hrw, dif_pos h, if_pos hend]
  rw [tsum_eq_single (PMF.pure true)]
  · rw [hn, PMF.pure_apply, if_pos rfl, one_mul, PMF.pure_apply_self]
  · intro μ hμ
    have hneg : ¬ (some (L2.a, μ) = some (L2.a, PMF.pure true)) := by
      intro heq; injection heq with h'; injection h' with _ h2; exact hμ h2
    rw [hn, PMF.pure_apply, if_neg hneg, zero_mul]

/-- The `n`-fold `a`-loop from `true` has probability `1`. -/
private theorem probOf_et (n : ℕ) : peTrue.probOf (et n) (et_terminates n) = 1 := by
  induction n with
  | zero =>
    have h_eq : et 0 = ⟨true, (Seq.nil : Seq (L2 × Bool))⟩ := by
      simp only [et, List.replicate_zero, Stream'.Seq.ofList_nil]
    rw [peTrue.probOf_congr (et 0) ⟨true, Seq.nil⟩ h_eq (et_terminates 0) Seq.terminates_nil,
      peTrue.probOf_nil]
    change (PMF.pure true : PMF Bool) true = 1
    exact PMF.pure_apply_self true
  | succ n ih =>
    have hsq : (Seq.ofList (List.replicate n (L2.a, true))).Terminates := Seq.terminates_ofList _
    have h_eq : et (n + 1) = ⟨true,
        (Seq.ofList (List.replicate n (L2.a, true))).append (Seq.cons (L2.a, true) Seq.nil)⟩ := by
      simp only [et]
      congr 1
      rw [List.replicate_succ', Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons,
        Stream'.Seq.ofList_nil]
    rw [peTrue.probOf_congr (et (n + 1)) _ h_eq (et_terminates (n + 1))
        (h_eq ▸ et_terminates (n + 1)),
      peTrue.probOf_append_singleton true (Seq.ofList (List.replicate n (L2.a, true))) hsq
        (L2.a, true),
      kernel_true _ hsq (endState_replicate_true n), mul_one]
    exact ih

/-- Its trace is `a` repeated `n` times. -/
private theorem trace_et (n : ℕ) : mixSys.trace (et n) = Seq.ofList (List.replicate n L2.a) := by
  induction n with
  | zero =>
    have h0 : et 0 = ⟨true, (Seq.nil : Seq (L2 × Bool))⟩ := by
      simp only [et, List.replicate_zero, Stream'.Seq.ofList_nil]
    rw [h0, System.trace_init, List.replicate_zero, Stream'.Seq.ofList_nil]
  | succ n ih =>
    have h_eq : et (n + 1) =
        ⟨true, Seq.cons (L2.a, true) (Seq.ofList (List.replicate n (L2.a, true)))⟩ := by
      simp only [et]
      congr 1
      rw [List.replicate_succ, Stream'.Seq.ofList_cons]
    rw [h_eq, System.trace_cons_external mixSys true L2.a true
        (Seq.ofList (List.replicate n (L2.a, true))) InfiniteTraceExample.a_ne_tau,
      show (⟨true, Seq.ofList (List.replicate n (L2.a, true))⟩ : AlterSeq Bool L2) = et n from rfl,
      ih, List.replicate_succ, Stream'.Seq.ofList_cons]

/-- It is tight. -/
private theorem isTight_et (n : ℕ) : mixSys.IsTight (et n) := by
  cases n with
  | zero =>
    refine Or.inl ?_
    change (Seq.ofList (List.replicate 0 (L2.a, true))).TerminatedAt 0
    rw [List.replicate_zero, Stream'.Seq.ofList_nil]
    exact Stream'.Seq.terminatedAt_nil
  | succ k =>
    refine Or.inr ⟨k, L2.a, true, ?_, ?_, InfiniteTraceExample.a_ne_tau⟩
    · change (Seq.ofList (List.replicate (k + 1) (L2.a, true))).get? k = some (L2.a, true)
      simp [Stream'.Seq.ofList_get?]
    · change (Seq.ofList (List.replicate (k + 1) (L2.a, true))).get? (k + 1) = none
      simp [Stream'.Seq.ofList_get?]

/-- **The `true` branch is the deterministic `a`-loop:** every finite cone has full mass. -/
theorem traceProb_true (n : ℕ) :
    mixSys.traceProb ⟨PMF.pure true, mixSched⟩ (Seq.ofList (List.replicate n L2.a)) = 1 := by
  change mixSys.traceProb peTrue (Seq.ofList (List.replicate n L2.a)) = 1
  refine le_antisymm ?_ ?_
  · rw [← peTrue.traceMeasure_cone]
    exact prob_le_one
  · rw [← probOf_et n]
    exact ENNReal.le_tsum
      (⟨et n, et_terminates n, trace_et n, isTight_et n⟩ :
        {e : AlterSeq Bool L2 // e.trans.Terminates ∧
          mixSys.trace e = Seq.ofList (List.replicate n L2.a) ∧ mixSys.IsTight e})

/-- The Dirac-`false` execution: halts immediately. -/
private noncomputable def peFalse : ProbabilisticExecution mixSys := ⟨PMF.pure false, mixSched⟩

/-- From the halted prefix `⟨false, nil⟩` the scheduler stops (`pure none`). -/
private theorem next_false_nil :
    peFalse.scheduler.next ⟨false, Seq.nil⟩ = PMF.pure none := by
  classical
  have hend : (⟨false, Seq.nil⟩ : AlterSeq Bool L2).endState Stream'.Seq.terminates_nil = false :=
    AlterSeq.endState_of_trans_nil _ rfl _
  have hrw : peFalse.scheduler.next ⟨false, Seq.nil⟩ =
      if h' : (Seq.nil : Seq (L2 × Bool)).Terminates then
        (if (⟨false, Seq.nil⟩ : AlterSeq Bool L2).endState h' = true then
          PMF.pure (some (L2.a, PMF.pure true)) else PMF.pure none)
      else PMF.pure none := rfl
  rw [hrw, dif_pos Stream'.Seq.terminates_nil, if_neg (by rw [hend]; decide)]

/-- The kernel from the halted prefix is `0`. -/
private theorem kernel_false_nil (x : L2 × Bool) :
    peFalse.kernel ⟨false, Seq.nil⟩ x = 0 := by
  change (∑' μ : PMF Bool, peFalse.scheduler.next ⟨false, Seq.nil⟩ (some (x.1, μ)) * μ x.2) = 0
  rw [next_false_nil]
  simp [PMF.pure_apply]

/-- From `false`, no nonempty execution has positive probability: the last kernel is `0`. -/
private theorem probOf_false_nonempty :
    ∀ (L : List (L2 × Bool)), L ≠ [] →
      peFalse.probOf ⟨false, Seq.ofList L⟩ (Seq.terminates_ofList L) = 0 := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton rest last ih =>
    intro _
    have hrest_term : (Seq.ofList rest).Terminates := Seq.terminates_ofList _
    have happ_trans : (Seq.ofList (rest ++ [last]) : Seq (L2 × Bool))
        = (Seq.ofList rest).append (Seq.cons last Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have heq : (⟨false, Seq.ofList (rest ++ [last])⟩ : AlterSeq Bool L2)
        = ⟨false, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩ := by rw [happ_trans]
    rw [peFalse.probOf_congr _ _ heq (Seq.terminates_ofList _)
        (happ_trans ▸ Seq.terminates_ofList (rest ++ [last])),
      peFalse.probOf_append_singleton false (Seq.ofList rest) hrest_term last]
    rcases eq_or_ne rest [] with hrest | hrest
    · subst hrest
      have hk : peFalse.kernel ⟨false, Seq.ofList ([] : List (L2 × Bool))⟩ last = 0 := by
        rw [show (⟨false, Seq.ofList ([] : List (L2 × Bool))⟩ : AlterSeq Bool L2)
              = ⟨false, Seq.nil⟩ from by rw [Stream'.Seq.ofList_nil]]
        exact kernel_false_nil last
      rw [hk, mul_zero]
    · rw [ih hrest, zero_mul]

/-- **The `false` branch halts:** it never produces a nonempty trace. -/
theorem traceProb_false {n : ℕ} (hn : 1 ≤ n) :
    mixSys.traceProb ⟨PMF.pure false, mixSched⟩ (Seq.ofList (List.replicate n L2.a)) = 0 := by
  change mixSys.traceProb peFalse (Seq.ofList (List.replicate n L2.a)) = 0
  unfold System.traceProb
  rw [ENNReal.tsum_eq_zero]
  intro e
  by_cases hinit : e.1.init = false
  · have hnil : e.1.trans.toList e.2.1 ≠ [] := by
      intro hemp
      have htrans_nil : e.1.trans = Seq.nil := by
        rw [← Stream'.Seq.ofList_toList e.1.trans e.2.1, hemp, Stream'.Seq.ofList_nil]
      have htr : mixSys.trace e.1 = Seq.nil := by
        have hce : e.1 = ⟨e.1.init, Seq.nil⟩ := by rw [← htrans_nil]
        rw [hce, System.trace_init]
      rw [e.2.2.1] at htr
      have h0 : (Seq.ofList (List.replicate n L2.a)).get? 0 = some L2.a := by
        rw [Stream'.Seq.ofList_get?, List.getElem?_replicate, if_pos (by omega)]
      rw [htr] at h0
      exact absurd h0 (by simp)
    have h_eq : e.1 = ⟨false, Seq.ofList (e.1.trans.toList e.2.1)⟩ := by
      rw [Stream'.Seq.ofList_toList e.1.trans e.2.1, ← hinit]
    rw [peFalse.probOf_congr e.1 _ h_eq e.2.1 (Seq.terminates_ofList _)]
    exact probOf_false_nonempty _ hnil
  · have hle := peFalse.probOf_le_init e.1 e.2.1
    rw [show peFalse.init e.1.init = 0 from
      PMF.pure_apply_of_ne false e.1.init hinit] at hle
    exact nonpos_iff_eq_zero.mp hle

/-- `traceProb` is linear in the initial distribution. -/
theorem traceProb_init_mix (μ : PMF Bool) (τ : Seq L2) :
    mixSys.traceProb ⟨μ, mixSched⟩ τ = ∑' s, μ s * mixSys.traceProb ⟨PMF.pure s, mixSched⟩ τ := by
  unfold System.traceProb
  have key : ∀ e : {e : AlterSeq Bool L2 //
      e.trans.Terminates ∧ mixSys.trace e = τ ∧ mixSys.IsTight e},
      (⟨μ, mixSched⟩ : ProbabilisticExecution mixSys).probOf e.1 e.2.1
        = ∑' s, μ s * (⟨PMF.pure s, mixSched⟩ : ProbabilisticExecution mixSys).probOf e.1 e.2.1 :=
    fun e => ProbabilisticExecution.probOf_init_mix mixSched μ e.1 e.2.1
  rw [tsum_congr key, ENNReal.tsum_comm]
  exact tsum_congr (fun _ => ENNReal.tsum_mul_left)

/-! ### Assembly -/

/-- **Every finite `a`-cone has mass `1/2`** (for `n ≥ 1`). -/
theorem traceProb_mix_aN {n : ℕ} (hn : 1 ≤ n) :
    mixSys.traceProb mixExec (Seq.ofList (List.replicate n L2.a)) = 1 / 2 := by
  rw [show mixExec = (⟨bern, mixSched⟩ : ProbabilisticExecution mixSys) from rfl,
    traceProb_init_mix]
  rw [tsum_bool, bern_true, bern_false, traceProb_true, traceProb_false hn, mul_one, mul_zero,
    zero_add]

/-- Every finite `a`-cone has mass at least `1/2`. -/
theorem traceProb_mix_ge (n : ℕ) :
    (1 : ENNReal) / 2 ≤ mixSys.traceProb mixExec (Seq.ofList (List.replicate n L2.a)) := by
  rw [show mixExec = (⟨bern, mixSched⟩ : ProbabilisticExecution mixSys) from rfl,
    traceProb_init_mix, tsum_bool, bern_true, bern_false, traceProb_true, mul_one]
  exact le_add_self

theorem traceMeasure_cone_mix_aN {n : ℕ} (hn : 1 ≤ n) :
    mixExec.traceMeasure (cone (List.replicate n L2.a)) = 1 / 2 := by
  rw [mixExec.traceMeasure_cone, traceProb_mix_aN hn]

/-- **The infinite trace `aω` gets measure exactly `1/2`** — strictly between `0` and `1`. -/
theorem traceMeasure_aOmega_half : mixExec.traceMeasure {aOmega} = 1 / 2 := by
  rw [← iInter_cone_eq_aOmega]
  have hanti : Antitone (fun n => cone (List.replicate n L2.a)) := by
    intro m n hmn σ hσ k v hk
    rw [Stream'.Seq.ofList_get?, List.getElem?_replicate] at hk
    have hkm : k < m := by by_contra hc; rw [if_neg hc] at hk; exact absurd hk (by simp)
    rw [if_pos hkm] at hk
    apply hσ k v
    rw [Stream'.Seq.ofList_get?, List.getElem?_replicate, if_pos (lt_of_lt_of_le hkm hmn)]
    exact hk
  have hmeas : ∀ n, NullMeasurableSet (cone (List.replicate n L2.a)) mixExec.traceMeasure :=
    fun n => (measurableSet_cone _).nullMeasurableSet
  have hfin : ∃ n, mixExec.traceMeasure (cone (List.replicate n L2.a)) ≠ ⊤ := by
    refine ⟨1, ?_⟩
    rw [traceMeasure_cone_mix_aN le_rfl]
    exact (by norm_num : (1 : ENNReal) / 2 ≠ ⊤)
  rw [hanti.measure_iInter hmeas hfin]
  refine le_antisymm ?_ ?_
  · calc ⨅ n, mixExec.traceMeasure (cone (List.replicate n L2.a))
        ≤ mixExec.traceMeasure (cone (List.replicate 1 L2.a)) := iInf_le _ 1
      _ = 1 / 2 := traceMeasure_cone_mix_aN le_rfl
  · refine le_iInf fun n => ?_
    rw [mixExec.traceMeasure_cone]
    exact traceProb_mix_ge n

end HalfInfiniteTraceExample
end PLTS
