/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Measure.Coordinates
import MyMathlibProject.Model.Trace

/-!
# The Ionescu–Tulcea measure of a probabilistic execution

Using the coordinate dictionary from `Measure/Coordinates.lean`, this file turns a
`ProbabilisticExecution` (over countable `State`/`Label`) into a genuine
probability measure `trajMeasure` on the trajectory space `Π n, TrajCoord n`, and
proves the **bridge lemma** `trajMeasure_cylinder`: the measure of the cylinder of
a finite execution `e` equals the existing `probOf e`. So the new measure literally
extends `probOf` — it agrees with it on every cylinder and additionally assigns
mass to infinite trajectories.

Mathlib's Ionescu–Tulcea construction is used as a **black box**: `trajMeasure` is
*the* probability measure whose one-step conditional law is the kernel `κ`. We only
ever touch it through `traj_map_frestrictLe` (finite marginal) and
`partialTraj_succ_of_le` (unfold one step), never its internal construction.
-/

open MeasureTheory ProbabilityTheory Finset Stream'

namespace PLTS

variable {State Label : Type} [Countable State] [Countable Label]
  {sys : System State Label}

/-- `tsum` over an `Option` type splits as the `none` value plus the `tsum` over
the `some`-fibres (local `ENNReal` specialisation). -/
private theorem tsum_option_enn {β : Type*} (f : Option β → ENNReal) :
    (∑' x, f x) = f none + ∑' y, f (some y) := by
  rw [ENNReal.tsum_eq_add_tsum_ite none]
  congr 1
  rw [tsum_eq_tsum_of_ne_zero_bij (i := fun y : {y : β // f (some y) ≠ 0} => some y.1)]
  · intro a b hab; exact Subtype.ext (Option.some_injective β hab)
  · intro x hx
    cases hx2 : (x : Option β) with
    | none => simp [Function.mem_support, hx2] at hx
    | some y =>
      refine ⟨⟨y, ?_⟩, ?_⟩
      · simp only [Function.mem_support] at hx ⊢; rw [hx2] at hx; simpa using hx
      · simp
  · intro y; simp

/-! ### The one-step distribution and kernel -/

omit [Countable State] [Countable Label] in
/-- Regroup the total step mass: summing the concrete one-step kernel over all
next `(l, s')` equals the scheduler's total mass on non-halt emissions. -/
private theorem tsum_kernel_eq (pe : ProbabilisticExecution sys) (e : AlterSeq State Label) :
    (∑' p : Label × State, pe.kernel e p)
      = ∑' x : Label × PMF State, pe.scheduler.next e (some x) := by
  unfold ProbabilisticExecution.kernel
  rw [ENNReal.tsum_prod', ENNReal.tsum_prod']
  refine tsum_congr (fun l => ?_)
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun μ => ?_)
  change (∑' s : State, pe.scheduler.next e (some (l, μ)) * μ s) = pe.scheduler.next e (some (l, μ))
  rw [ENNReal.tsum_mul_left, μ.tsum_coe, mul_one]

/-- The one-step distribution over the next coordinate at a live history `e`:
mass `next e none` on halting (`none`), mass `kernel e (l, s')` on each step
`some (l, s')`. Total mass `1`, so it is a genuine `PMF`. -/
noncomputable def ProbabilisticExecution.stepPMF (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) : PMF (Option (Label × State)) :=
  ⟨fun o => o.elim (pe.scheduler.next e none) (fun ls => pe.kernel e ls), by
    rw [ENNReal.summable.hasSum_iff, tsum_option_enn]
    change pe.scheduler.next e none + (∑' p : Label × State, pe.kernel e p) = 1
    rw [tsum_kernel_eq, ← tsum_option_enn]
    exact (pe.scheduler.next e).tsum_coe⟩

omit [Countable State] [Countable Label] in
@[simp] theorem ProbabilisticExecution.stepPMF_some (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (l : Label) (s : State) :
    pe.stepPMF e (some (l, s)) = pe.kernel e (l, s) := rfl

/-- `PMF.toMeasure` at a discrete coordinate type, routing the measurable space
through the `TrajCoord` head so instance search succeeds (there is no bare
`MeasurableSpace State`). -/
noncomputable def coordMeasure {n : ℕ} (p : PMF (TrajCoord State Label n)) :
    Measure (TrajCoord State Label n) := p.toMeasure

instance instCoordMeasureProb {n : ℕ} (p : PMF (TrajCoord State Label n)) :
    IsProbabilityMeasure (coordMeasure p) := by unfold coordMeasure; infer_instance

omit [Countable State] [Countable Label] in
theorem coordMeasure_apply_singleton {n : ℕ} (p : PMF (TrajCoord State Label n))
    (a : TrajCoord State Label n) : coordMeasure p {a} = p a := by
  unfold coordMeasure
  rw [PMF.toMeasure_apply_singleton _ a (measurableSet_singleton _)]

open Classical in
/-- The Ionescu–Tulcea one-step kernel: from a history tuple, emit the next
coordinate. If already halted, stay halted (`none`); otherwise use `stepPMF` on the
reconstructed live history. -/
noncomputable def ProbabilisticExecution.κ (pe : ProbabilisticExecution sys) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → TrajCoord State Label i) (TrajCoord State Label (n + 1)) :=
  Kernel.ofFunOfCountable (fun x =>
    if halted x then coordMeasure (n := n + 1) (PMF.pure none)
    else coordMeasure (n := n + 1) (pe.stepPMF (recon x)))

instance (pe : ProbabilisticExecution sys) (n : ℕ) : IsMarkovKernel (pe.κ n) := by
  classical
  refine ⟨fun x => ?_⟩
  change IsProbabilityMeasure (if halted x then coordMeasure (n := n + 1) (PMF.pure none)
    else coordMeasure (n := n + 1) (pe.stepPMF (recon x)))
  split_ifs <;> infer_instance

/-- **B3.** The kernel at an execution's history tuple, on a concrete next step,
is the concrete one-step kernel. -/
theorem ProbabilisticExecution.kappa_tup_some (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (hFin : e.trans.Terminates) (l : Label) (s : State) :
    (pe.κ (e.trans.length hFin)) (tup e (e.trans.length hFin))
        ({some (l, s)} : Set (TrajCoord State Label (e.trans.length hFin + 1)))
      = pe.kernel e (l, s) := by
  classical
  have hx : (pe.κ (e.trans.length hFin)) (tup e (e.trans.length hFin))
      = coordMeasure (n := e.trans.length hFin + 1) (pe.stepPMF e) := by
    change (if halted (tup e (e.trans.length hFin)) then
        coordMeasure (n := e.trans.length hFin + 1) (PMF.pure none)
      else coordMeasure (n := e.trans.length hFin + 1)
          (pe.stepPMF (recon (tup e (e.trans.length hFin))))) = _
    rw [if_neg (not_halted_tup e hFin), recon_tup e hFin]
  rw [hx]
  exact (coordMeasure_apply_singleton (n := e.trans.length hFin + 1) (pe.stepPMF e)
    (some (l, s))).trans rfl

/-! ### The trajectory measure -/

/-- The initial-coordinate measure of a probabilistic execution. -/
noncomputable def ProbabilisticExecution.initMeasure (pe : ProbabilisticExecution sys) :
    Measure (TrajCoord State Label 0) :=
  coordMeasure (n := 0) pe.initState

instance (pe : ProbabilisticExecution sys) : IsProbabilityMeasure pe.initMeasure := by
  rw [ProbabilisticExecution.initMeasure]; infer_instance

/-- The **trajectory measure** of a probabilistic execution: the Ionescu–Tulcea
measure whose one-step conditional law is `κ`. This is the genuine probability
measure induced by `pe` on the space of (finite-or-infinite) trajectories. -/
noncomputable def ProbabilisticExecution.trajMeasure (pe : ProbabilisticExecution sys) :
    Measure (Π n, TrajCoord State Label n) :=
  Kernel.trajMeasure pe.initMeasure (pe.κ)

instance (pe : ProbabilisticExecution sys) : IsProbabilityMeasure pe.trajMeasure := by
  rw [ProbabilisticExecution.trajMeasure]; infer_instance

/-! ### The bridge lemma (C) -/

open Preorder

omit [Countable State] [Countable Label] in
/-- The `Seq.length` of `Seq.ofList L` is just `L.length`. -/
private theorem length_ofList (L : List (Label × State)) (h : (Seq.ofList L).Terminates) :
    (Seq.ofList L).length h = L.length := by
  refine le_antisymm (Seq.length_le_iff.mpr (Seq.terminatedAt_ofList L)) ?_
  by_contra hlt
  have hlt' : (Seq.ofList L).length h < L.length := Nat.lt_of_not_le hlt
  have hterm : (Seq.ofList L).TerminatedAt ((Seq.ofList L).length h) :=
    Seq.length_le_iff.mp le_rfl
  rw [Seq.TerminatedAt, Seq.ofList_get?, List.getElem?_eq_none_iff] at hterm
  omega

omit [Countable State] [Countable Label] in
/-- Over the singleton index set `Iic 0`, a history tuple equals `tup e 0` iff its
initial coordinate matches `e.init`. -/
private theorem eq_tup_zero_iff (e : AlterSeq State Label)
    (x₀ : (i : Iic 0) → TrajCoord State Label i) :
    x₀ = tup e 0 ↔ initCoord x₀ = e.init := by
  constructor
  · rintro rfl; rfl
  · intro h
    funext i
    obtain ⟨j, hj⟩ := i
    have hj0 : j = 0 := Nat.le_zero.mp (Finset.mem_Iic.mp hj)
    subst hj0
    exact h

/-- `kappa_tup_some` specialised to a history built from a list, indexed directly by
`rest.length` (avoiding the `Seq.length` wrapper). -/
private theorem kappa_tup_ofList_some (pe : ProbabilisticExecution sys) (i₀ : State)
    (rest : List (Label × State)) (l : Label) (s : State) :
    (pe.κ rest.length) (tup (⟨i₀, Seq.ofList rest⟩ : AlterSeq State Label) rest.length)
        ({some (l, s)} : Set (TrajCoord State Label (rest.length + 1)))
      = pe.kernel (⟨i₀, Seq.ofList rest⟩ : AlterSeq State Label) (l, s) := by
  have hFin : (Seq.ofList rest).Terminates := Seq.terminates_ofList rest
  have hL : (⟨i₀, Seq.ofList rest⟩ : AlterSeq State Label).trans.length hFin = rest.length :=
    length_ofList rest hFin
  have key := pe.kappa_tup_some (⟨i₀, Seq.ofList rest⟩ : AlterSeq State Label) hFin l s
  rw [hL] at key
  exact key

omit [Countable State] [Countable Label] in
/-- Restricting the `(n+1)`-tuple of `⟨i₀, rest ++ [last]⟩` down to `Iic n` gives the
`n`-tuple of the truncated execution `⟨i₀, rest⟩`. -/
private theorem frestrictLe₂_tup_succ (i₀ : State) (rest : List (Label × State))
    (last : Label × State) :
    frestrictLe₂ (Nat.le_succ rest.length)
        (tup (⟨i₀, Seq.ofList (rest ++ [last])⟩ : AlterSeq State Label) (rest.length + 1))
      = tup (⟨i₀, Seq.ofList rest⟩ : AlterSeq State Label) rest.length := by
  funext i
  obtain ⟨m, hm⟩ := i
  rw [frestrictLe₂_apply]
  change coord (⟨i₀, Seq.ofList (rest ++ [last])⟩ : AlterSeq State Label) m
    = coord (⟨i₀, Seq.ofList rest⟩ : AlterSeq State Label) m
  cases m with
  | zero => rfl
  | succ k =>
    change (Seq.ofList (rest ++ [last])).get? k = (Seq.ofList rest).get? k
    rw [Seq.ofList_get?, Seq.ofList_get?,
      List.getElem?_append_left (Nat.lt_of_succ_le (Finset.mem_Iic.mp hm))]

omit [Countable State] [Countable Label] in
/-- The preimage under the gluing map `IicProdIoc n (n+1)` of the singleton `{tup e (n+1)}`
is the product of the truncated tuple singleton with the single last-coordinate point. -/
private theorem IicProdIoc_preimage_tup (i₀ : State) (rest : List (Label × State))
    (last : Label × State) :
    IicProdIoc rest.length (rest.length + 1) ⁻¹'
        ({tup (⟨i₀, Seq.ofList (rest ++ [last])⟩ : AlterSeq State Label) (rest.length + 1)} :
          Set ((i : Iic (rest.length + 1)) → TrajCoord State Label i))
      = {tup (⟨i₀, Seq.ofList rest⟩ : AlterSeq State Label) rest.length}
          ×ˢ {restrict₂ Ioc_subset_Iic_self
            (tup (⟨i₀, Seq.ofList (rest ++ [last])⟩ : AlterSeq State Label)
              (rest.length + 1))} := by
  conv_lhs => rw [← Set.univ_pi_singleton]
  rw [IicProdIoc_preimage (Nat.le_succ _)]
  congr 1
  · conv_rhs => rw [← frestrictLe₂_tup_succ i₀ rest last, ← Set.univ_pi_singleton]
    rfl
  · conv_rhs => rw [← Set.univ_pi_singleton]
    rfl

omit [Countable State] [Countable Label] in
/-- The preimage under `piSingleton n` of the singleton last-coordinate point is the
singleton `{some last}` — i.e. the concrete next step is recovered. -/
private theorem piSingleton_preimage_y (i₀ : State) (rest : List (Label × State))
    (last : Label × State) :
    (MeasurableEquiv.piSingleton rest.length) ⁻¹'
        {restrict₂ Ioc_subset_Iic_self
          (tup (⟨i₀, Seq.ofList (rest ++ [last])⟩ : AlterSeq State Label) (rest.length + 1))}
      = ({some last} : Set (TrajCoord State Label (rest.length + 1))) := by
  have hsymm : (MeasurableEquiv.piSingleton rest.length).symm
      (restrict₂ Ioc_subset_Iic_self
        (tup (⟨i₀, Seq.ofList (rest ++ [last])⟩ : AlterSeq State Label) (rest.length + 1)))
      = some last := by
    change (Seq.ofList (rest ++ [last])).get? rest.length = some last
    rw [Seq.ofList_get?, List.getElem?_concat_length]
  ext w
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  rw [← hsymm]
  exact (MeasurableEquiv.piSingleton rest.length).apply_eq_iff_eq_symm_apply

open Classical in
/-- Auxiliary form of C1, phrased over a *list* `L` (decoupling the induction variable
from the execution `e`), proved by reverse (cons-end) induction on `L`. -/
private theorem partialTraj_singleton_aux (pe : ProbabilisticExecution sys) (i₀ : State)
    (L : List (Label × State)) (x₀ : (i : Iic 0) → TrajCoord State Label i) :
    Kernel.partialTraj (pe.κ) 0 L.length x₀
        ({tup (⟨i₀, Seq.ofList L⟩ : AlterSeq State Label) L.length} :
          Set ((i : Iic L.length) → TrajCoord State Label i))
      = (if initCoord x₀ = i₀ then 1 else 0)
        * (⟨PMF.pure i₀, pe.scheduler⟩ : ProbabilisticExecution sys).probOf
            ⟨i₀, Seq.ofList L⟩ (Seq.terminates_ofList L) := by
  induction L using List.reverseRecOn with
  | nil =>
    have hp : (⟨PMF.pure i₀, pe.scheduler⟩ : ProbabilisticExecution sys).probOf
        ⟨i₀, Seq.ofList []⟩ (Seq.terminates_ofList []) = 1 := by
      rw [ProbabilisticExecution.probOf_congr _ ⟨i₀, Seq.ofList []⟩ ⟨i₀, Seq.nil⟩
        (by rw [Seq.ofList_nil]) _ Seq.terminates_nil, ProbabilisticExecution.probOf_nil]
      exact PMF.pure_apply_self i₀
    simp only [List.length_nil]
    rw [Kernel.partialTraj_self, Kernel.id_apply,
      Measure.dirac_apply' _ (measurableSet_singleton _), hp, mul_one]
    by_cases h : initCoord x₀ = i₀
    · have hmem : x₀ ∈ ({tup (⟨i₀, Seq.ofList []⟩ : AlterSeq State Label) 0} : Set _) := by
        rw [Set.mem_singleton_iff, eq_tup_zero_iff]; exact h
      rw [if_pos h, Set.indicator_of_mem hmem, Pi.one_apply]
    · have hmem : x₀ ∉ ({tup (⟨i₀, Seq.ofList []⟩ : AlterSeq State Label) 0} : Set _) := by
        rw [Set.mem_singleton_iff, eq_tup_zero_iff]; exact h
      rw [if_neg h, Set.indicator_of_notMem hmem]
  | append_singleton rest last ih =>
    obtain ⟨l, s⟩ := last
    have happ : Seq.ofList (rest ++ [(l, s)])
        = (Seq.ofList rest).append (Seq.cons (l, s) Seq.nil) := by
      rw [Seq.ofList_append, Seq.ofList_cons, Seq.ofList_nil]
    have h_app : ((Seq.ofList rest).append (Seq.cons (l, s) Seq.nil)).Terminates :=
      happ ▸ Seq.terminates_ofList (rest ++ [(l, s)])
    have hRHS : (⟨PMF.pure i₀, pe.scheduler⟩ : ProbabilisticExecution sys).probOf
          ⟨i₀, Seq.ofList (rest ++ [(l, s)])⟩ (Seq.terminates_ofList (rest ++ [(l, s)]))
        = (⟨PMF.pure i₀, pe.scheduler⟩ : ProbabilisticExecution sys).probOf
            ⟨i₀, Seq.ofList rest⟩ (Seq.terminates_ofList rest)
          * pe.kernel ⟨i₀, Seq.ofList rest⟩ (l, s) := by
      rw [ProbabilisticExecution.probOf_congr _ ⟨i₀, Seq.ofList (rest ++ [(l, s)])⟩
          ⟨i₀, (Seq.ofList rest).append (Seq.cons (l, s) Seq.nil)⟩ (by rw [happ])
          (Seq.terminates_ofList (rest ++ [(l, s)])) h_app]
      exact ProbabilisticExecution.probOf_append_singleton _ i₀ (Seq.ofList rest)
        (Seq.terminates_ofList rest) (l, s) h_app
    have hK : ∀ b : (i : ↥(Iic rest.length)) → TrajCoord State Label ↑i,
        ((pe.κ rest.length).map ⇑(MeasurableEquiv.piSingleton rest.length)) b
            {restrict₂ Ioc_subset_Iic_self
              (tup (⟨i₀, Seq.ofList (rest ++ [(l, s)])⟩ : AlterSeq State Label)
                (rest.length + 1))}
          = (pe.κ rest.length) b {some (l, s)} := fun b => by
      rw [Kernel.map_apply' _ (MeasurableEquiv.piSingleton rest.length).measurable _
        (measurableSet_singleton _), piSingleton_preimage_y i₀ rest (l, s)]
    rw [show (rest ++ [(l, s)]).length = rest.length + 1 from by simp,
      Kernel.partialTraj_succ_of_le (Nat.zero_le rest.length),
      Kernel.map_apply' _ measurable_IicProdIoc _ (measurableSet_singleton _),
      IicProdIoc_preimage_tup i₀ rest (l, s),
      Kernel.comp_apply' _ _ _ ((measurableSet_singleton _).prod (measurableSet_singleton _))]
    simp only [Kernel.prod_apply_prod, hK, Kernel.id_apply,
      Measure.dirac_apply' _ (measurableSet_singleton _)]
    rw [lintegral_countable',
      tsum_eq_single (tup (⟨i₀, Seq.ofList rest⟩ : AlterSeq State Label) rest.length)
        (fun b hb => by
          rw [Set.indicator_of_notMem (by rwa [Set.mem_singleton_iff]), zero_mul, zero_mul]),
      Set.indicator_of_mem (Set.mem_singleton_iff.mpr rfl), Pi.one_apply, one_mul,
      kappa_tup_ofList_some pe i₀ rest l s, ih, hRHS]
    ring

open Classical in
/-- **C1.** The finite marginal (`partialTraj`) at the tuple singleton of a finite
execution equals `probOf` from a Dirac initial state. -/
theorem ProbabilisticExecution.partialTraj_singleton (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (hFin : e.trans.Terminates)
    (x₀ : (i : Finset.Iic 0) → TrajCoord State Label i) :
    Kernel.partialTraj (pe.κ) 0 (e.trans.length hFin) x₀
        ({tup e (e.trans.length hFin)} : Set ((i : Finset.Iic (e.trans.length hFin)) →
          TrajCoord State Label i))
      = (if initCoord x₀ = e.init then 1 else 0)
          * (⟨PMF.pure e.init, pe.scheduler⟩ : ProbabilisticExecution sys).probOf e hFin := by
  have he : (⟨e.init, Seq.ofList (e.trans.toList hFin)⟩ : AlterSeq State Label) = e := by
    rw [Seq.ofList_toList]
  have key := partialTraj_singleton_aux pe e.init (e.trans.toList hFin) x₀
  rw [Seq.length_toList,
    ProbabilisticExecution.probOf_congr _ ⟨e.init, Seq.ofList (e.trans.toList hFin)⟩ e he
      (Seq.terminates_ofList _) hFin, he] at key
  exact key

/-- **Bridge lemma.** The trajectory measure of the cylinder of a finite execution
`e` equals `probOf e`. The new measure extends `probOf`. -/
theorem ProbabilisticExecution.trajMeasure_cylinder (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (hFin : e.trans.Terminates) :
    pe.trajMeasure (cylinder (Finset.Iic (e.trans.length hFin))
        ({tup e (e.trans.length hFin)} : Set ((i : Finset.Iic (e.trans.length hFin)) →
          TrajCoord State Label i)))
      = pe.probOf e hFin := by
  rw [show cylinder (Iic (e.trans.length hFin)) ({tup e (e.trans.length hFin)} : Set _)
      = frestrictLe (e.trans.length hFin) ⁻¹' {tup e (e.trans.length hFin)} from rfl,
    ← Measure.map_apply (measurable_frestrictLe _) (measurableSet_singleton _),
    ProbabilisticExecution.trajMeasure]
  unfold Kernel.trajMeasure
  rw [Measure.map_comp _ _ (measurable_frestrictLe _), Kernel.traj_map_frestrictLe,
    Measure.comp_eq_sum_of_countable, Measure.sum_apply _ (measurableSet_singleton _)]
  simp only [Measure.smul_apply, smul_eq_mul, ProbabilisticExecution.partialTraj_singleton]
  refine (tsum_eq_single (tup e 0) (fun a ha => ?_)).trans ?_
  · rw [if_neg (fun h => ha ((eq_tup_zero_iff e a).mpr h)), zero_mul, mul_zero]
  · rw [initCoord_tup, if_pos rfl, one_mul]
    erw [MeasurableEquiv.map_apply, MeasurableEquiv.preimage_symm, Set.image_singleton,
      ProbabilisticExecution.initMeasure, coordMeasure_apply_singleton]
    exact (ProbabilisticExecution.probOf_init_factor pe.scheduler pe.initState e hFin).symm

end PLTS
