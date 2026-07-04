/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Measure.Trace

/-!
# A worked example: the trace measure gives infinite traces their correct weight

The finite-cone semantics `System.traceProb` assigns probability `0` to every
*infinite* trace (its sum ranges over finite executions). The genuine trace
measure `traceMeasure` does not: it assigns each infinite trace the (correct)
limiting weight of its finite prefixes.

We verify this on the simplest possible example: a one-state system that emits the
external label `a` forever. The infinite trace `aω` is realised with probability
`1`, and indeed:

* `traceProb detSys detExec aω = 0`  (the finite-cone value — misses it);
* `detExec.traceMeasure {aω} = 1`    (the measure — gets it right).
-/

open MeasureTheory ProbabilityTheory Finset Stream'

namespace PLTS
namespace InfiniteTraceExample

/-- Two labels: `τ` (silent) and `a` (external). -/
inductive L2 where
  | tau : L2
  | a : L2
  deriving DecidableEq, Fintype

instance : Silent L2 := ⟨L2.tau⟩
instance : Countable L2 := Finite.to_countable

@[simp] theorem a_ne_tau : ¬ (L2.a = Silent.τ) := by decide

/-- A one-state system that only ever performs the external step `a`. -/
noncomputable def detSys : System Unit L2 where
  init := ()
  step _ l μ := l = L2.a ∧ μ = PMF.pure ()

/-- The deterministic scheduler that always emits `a`. -/
noncomputable def detSched : Scheduler detSys where
  next _ := PMF.pure (some (L2.a, PMF.pure ()))
  valid := by
    intro e n s _ _ l μ hsupp
    rw [PMF.mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at hsupp
    obtain ⟨rfl, rfl⟩ := hsupp
    exact ⟨rfl, rfl⟩

noncomputable def detExec : ProbabilisticExecution detSys := ⟨PMF.pure (), detSched⟩

/-- The finite execution doing `a` exactly `n` times. -/
def eN (n : ℕ) : AlterSeq Unit L2 := ⟨(), Seq.ofList (List.replicate n (L2.a, ()))⟩

theorem eN_terminates (n : ℕ) : (eN n).trans.Terminates := Seq.terminates_ofList _

/-- The one-step kernel of `detExec` on the `a`-step is `1`. -/
theorem kernel_detExec (e : AlterSeq Unit L2) : detExec.kernel e (L2.a, ()) = 1 := by
  change (∑' μ : PMF Unit, detExec.scheduler.next e (some (L2.a, μ)) * μ ()) = 1
  have hn : detExec.scheduler.next e = PMF.pure (some (L2.a, PMF.pure ())) := rfl
  rw [tsum_eq_single (PMF.pure ())]
  · rw [hn, PMF.pure_apply, if_pos rfl, one_mul, PMF.pure_apply_self]
  · intro μ hμ
    have hneg : ¬ (some (L2.a, μ) = some (L2.a, PMF.pure ())) := by
      intro h; injection h with h'; injection h' with _ h2; exact hμ h2
    rw [hn, PMF.pure_apply, if_neg hneg, zero_mul]

/-- The `n`-fold `a` execution has probability `1`. -/
theorem probOf_eN (n : ℕ) : detExec.probOf (eN n) (eN_terminates n) = 1 := by
  induction n with
  | zero =>
    have h_eq : eN 0 = ⟨(), (Seq.nil : Seq (L2 × Unit))⟩ := by
      simp only [eN, List.replicate_zero, Stream'.Seq.ofList_nil]
    rw [detExec.probOf_congr (eN 0) ⟨(), Seq.nil⟩ h_eq (eN_terminates 0) Stream'.Seq.terminates_nil,
      detExec.probOf_nil]
    change (PMF.pure () : PMF Unit) () = 1
    exact PMF.pure_apply_self ()
  | succ n ih =>
    have hsq : (Seq.ofList (List.replicate n (L2.a, ()))).Terminates :=
      Stream'.Seq.terminates_ofList _
    have h_eq : eN (n + 1) =
        ⟨(), (Seq.ofList (List.replicate n (L2.a, ()))).append (Seq.cons (L2.a, ()) Seq.nil)⟩ := by
      simp only [eN]
      congr 1
      rw [List.replicate_succ', Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons,
        Stream'.Seq.ofList_nil]
    rw [detExec.probOf_congr (eN (n + 1)) _ h_eq (eN_terminates (n + 1))
        (h_eq ▸ eN_terminates (n + 1)),
      detExec.probOf_append_singleton () (Seq.ofList (List.replicate n (L2.a, ()))) hsq (L2.a, ()),
      kernel_detExec, mul_one]
    exact ih

/-- Its trace is `a` repeated `n` times. -/
theorem trace_eN (n : ℕ) :
    detSys.trace (eN n) = Seq.ofList (List.replicate n L2.a) := by
  induction n with
  | zero =>
    have h0 : eN 0 = ⟨(), (Seq.nil : Seq (L2 × Unit))⟩ := by
      simp only [eN, List.replicate_zero, Stream'.Seq.ofList_nil]
    rw [h0, System.trace_init, List.replicate_zero, Stream'.Seq.ofList_nil]
  | succ n ih =>
    have h_eq : eN (n + 1) =
        ⟨(), Seq.cons (L2.a, ()) (Seq.ofList (List.replicate n (L2.a, ())))⟩ := by
      simp only [eN]
      congr 1
      rw [List.replicate_succ, Stream'.Seq.ofList_cons]
    rw [h_eq, System.trace_cons_external detSys () L2.a ()
      (Seq.ofList (List.replicate n (L2.a, ()))) a_ne_tau,
      show (⟨(), Seq.ofList (List.replicate n (L2.a, ()))⟩ : AlterSeq Unit L2) = eN n from rfl, ih,
      List.replicate_succ, Stream'.Seq.ofList_cons]

/-- It is tight. -/
theorem isTight_eN (n : ℕ) : detSys.IsTight (eN n) := by
  cases n with
  | zero =>
    refine Or.inl ?_
    change (Seq.ofList (List.replicate 0 (L2.a, ()))).TerminatedAt 0
    rw [List.replicate_zero, Stream'.Seq.ofList_nil]
    exact Stream'.Seq.terminatedAt_nil
  | succ k =>
    refine Or.inr ⟨k, L2.a, (), ?_, ?_, a_ne_tau⟩
    · change (Seq.ofList (List.replicate (k + 1) (L2.a, ()))).get? k = some (L2.a, ())
      simp [Stream'.Seq.ofList_get?]
    · change (Seq.ofList (List.replicate (k + 1) (L2.a, ()))).get? (k + 1) = none
      simp [Stream'.Seq.ofList_get?]

/-- **Every finite cone has full mass.** -/
theorem traceProb_aN (n : ℕ) :
    detSys.traceProb detExec (Seq.ofList (List.replicate n L2.a)) = 1 := by
  refine le_antisymm ?_ ?_
  · rw [← detExec.traceMeasure_cone]
    exact prob_le_one
  · rw [← probOf_eN n]
    exact ENNReal.le_tsum
      (⟨eN n, eN_terminates n, trace_eN n, isTight_eN n⟩ :
        {e : AlterSeq Unit L2 // e.trans.Terminates ∧
          detSys.trace e = Seq.ofList (List.replicate n L2.a) ∧ detSys.IsTight e})

theorem traceMeasure_cone_aN (n : ℕ) :
    detExec.traceMeasure (cone (List.replicate n L2.a)) = 1 := by
  rw [detExec.traceMeasure_cone, traceProb_aN]

/-- The infinite trace `aω`. -/
def aOmega : Seq L2 := ⟨fun _ => some L2.a, by intro n h; simp at h⟩

@[simp] theorem aOmega_get? (k : ℕ) : aOmega.get? k = some L2.a := rfl

/-- The infinite trace `aω` is exactly the intersection of all finite `a`-cones. -/
theorem iInter_cone_eq_aOmega :
    (⋂ n, cone (List.replicate n L2.a)) = {aOmega} := by
  ext σ
  simp only [Set.mem_iInter, Set.mem_singleton_iff, cone, Set.mem_setOf_eq]
  constructor
  · intro h
    apply Stream'.Seq.ext
    intro k
    rw [aOmega_get?]
    have hk : (Seq.ofList (List.replicate (k + 1) L2.a)).get? k = some L2.a := by
      rw [Stream'.Seq.ofList_get?, List.getElem?_replicate, if_pos (Nat.lt_succ_self k)]
    exact h (k + 1) k L2.a hk
  · intro h n k v hv
    subst h
    rw [aOmega_get?]
    have hv' : v = L2.a := by
      rw [Stream'.Seq.ofList_get?, List.getElem?_replicate] at hv
      by_cases hkn : k < n
      · rw [if_pos hkn] at hv; exact (Option.some.inj hv).symm
      · rw [if_neg hkn] at hv; exact absurd hv (by simp)
    rw [hv']

/-- **The measure gives the infinite trace `aω` its correct weight `1`.** -/
theorem traceMeasure_aOmega : detExec.traceMeasure {aOmega} = 1 := by
  rw [← iInter_cone_eq_aOmega]
  have hanti : Antitone (fun n => cone (List.replicate n L2.a)) := by
    intro m n hmn σ hσ k v hk
    rw [Stream'.Seq.ofList_get?, List.getElem?_replicate] at hk
    have hkm : k < m := by
      by_contra hc
      rw [if_neg hc] at hk
      exact absurd hk (by simp)
    rw [if_pos hkm] at hk
    apply hσ k v
    rw [Stream'.Seq.ofList_get?, List.getElem?_replicate, if_pos (lt_of_lt_of_le hkm hmn)]
    exact hk
  have hmeas : ∀ n, NullMeasurableSet (cone (List.replicate n L2.a)) detExec.traceMeasure :=
    fun n => (measurableSet_cone _).nullMeasurableSet
  have hfin : ∃ n, detExec.traceMeasure (cone (List.replicate n L2.a)) ≠ ⊤ := by
    refine ⟨0, ?_⟩
    rw [traceMeasure_cone_aN]
    exact ENNReal.one_ne_top
  rw [hanti.measure_iInter hmeas hfin]
  simp [traceMeasure_cone_aN]

/-- **By contrast, the finite-cone semantics misses it: `traceProb aω = 0`.** -/
theorem traceProb_aOmega : detSys.traceProb detExec aOmega = 0 := by
  haveI : IsEmpty {e : AlterSeq Unit L2 //
      e.trans.Terminates ∧ detSys.trace e = aOmega ∧ detSys.IsTight e} := by
    refine ⟨fun e => ?_⟩
    obtain ⟨e, hterm, htrace, -⟩ := e
    have h1 : (detSys.trace e).Terminates := by
      unfold System.trace
      rw [Stream'.Seq.terminates_map_iff]
      exact Stream'.Seq.terminates_filter _ _ hterm
    rw [htrace] at h1
    obtain ⟨N, hN⟩ := h1
    have hN' : aOmega.get? N = none := hN
    rw [aOmega_get?] at hN'
    exact absurd hN' (by simp)
  unfold System.traceProb
  exact tsum_empty

end InfiniteTraceExample
end PLTS
