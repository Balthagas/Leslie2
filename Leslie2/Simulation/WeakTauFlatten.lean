/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Simulation.Equivalences
import Leslie2.Weak.Bounds

/-!
# Flattening a `𝒟(sys^w)`-internal weak transition

An internal weak transition of the lifted system `𝒟(sys^w)` out of a Dirac
macro-state collapses to an internal weak transition of `sys` itself:

`weakTau_flatten : weakTau (𝒟(sys^w)) (PMF.pure μ) Ν → weakTau sys μ (Ν.bind id)`

Each single internal macro-step collapses through the proven bridge
`weakTau_of_hyperStep_weakClosure` (`weakTau_of_distStep` below); the content
of the theorem is the **ω-composition**: countably many a.s.-halting
`sys`-`weakTau`s, glued along an a.s.-halting macro-run, compose into one
a.s.-halting `sys`-`weakTau` whose end-state distribution is the macro
end-state mixture `Ν.bind id`. Together with
`StrongProbabilisticSimulation.weakTau_lift` and the forward⇔strong
correspondence, this discharges `weakTau_lift_pure` — see the reduction in
`Simulation/Transitivity.lean`.

Architecture:

* **macro-halt depth strata** — the halting mass of the macro-scheduler is
  stratified by macro-depth (`macroHaltDepth`), summing to the flatten target
  `Ν.bind id` (`macroHalt_tsum_depth`, `macroHalted_iSup_eq_one`);
* **inner-witness extraction** — each macro-emission is realized by a
  classical `sys`-scheduler witness (`innerWitness`) with exact halting
  integral (`innerWitness_integrate`) and pushforward;
* **the flattening scheduler** — a belief scheduler `flatSched` over segmented
  hidden configurations (`FlatSeg`/`DConfig`), whose step kernel is the
  posterior of algorithm-side reach weights (the `WeakClosure` `expandSched`
  pattern), with Bayes-coupled junctions between macro-levels and empty
  segments acting as the stall resolvent;
* **fidelity** — the path measure of `flatSched` equals the config reach sum
  (`probOf_eq_reachArrM`), giving the halt-mass identity;
* **the renewal bound** — a depth-induction lower bound on the halting
  integral (`renewal_step_le`, `condDepthSum_le_fHM`) closes the a.s.-halting
  and pushforward obligations.
-/

open Stream'
open scoped BigOperators

namespace PLTS

variable {State Label : Type} [Silent Label]

/-! ### One macro-step collapses through the proven bridge -/

/-- A single internal step of `𝒟(sys^w)` out of the macro-state `m` is an
internal weak transition of `sys` from `m` to the successor mixture. -/
theorem weakTau_of_distStep {sys : System State Label} {m : PMF State}
    {ω : PMF (PMF State)} (h : (𝒟(sys^w)).step m Silent.τ ω) :
    weakTau sys m (ω.bind id) := by
  have h' : hyperStep (sys^w) m Silent.τ (ω.bind id) := h
  exact weakTau_of_hyperStep_weakClosure rfl h'

/-! ### The flattening theorem

`weakTau_flatten` is stated and proved at the end of the file, witnessed by
the honest reach-arrival flattening scheduler `flatSched`. The decision-point
carrier admits EMPTY completed segments: a finite stall chain (macro steps
realized by empty inner runs) is a run of empty segments whose `segWeight`
factors are exactly the Bayes-coupled resolvent terms, so stall mass flows
through the junctions instead of misfiling into the halt reach. -/

/-! ### Macro-history extension -/

/-- Append one internal (`τ`) macro-transition into `m'` onto the macro-history
`E`. -/
def macroExtend (E : AlterSeq (PMF State) Label) (m' : PMF State) :
    AlterSeq (PMF State) Label :=
  ⟨E.init, E.trans.append (Seq.cons (Silent.τ, m') Seq.nil)⟩

/-- The one-step extension of a terminating macro-history again terminates. -/
theorem macroExtend_term {E : AlterSeq (PMF State) Label}
    (hT : E.trans.Terminates) (m' : PMF State) :
    (macroExtend E m').trans.Terminates :=
  ⟨Nat.find hT + 1,
    Stream'.Seq.terminatedAt_append_find hT
      (show (Seq.cons (Silent.τ, m') Seq.nil : Seq (Label × PMF State)).TerminatedAt 1 from rfl)⟩

/-- The end-state of a one-step extension is the appended macro-state `m'`. -/
theorem macroExtend_endState {E : AlterSeq (PMF State) Label}
    (hT : E.trans.Terminates) (m' : PMF State) :
    (macroExtend E m').endState (macroExtend_term hT m') = m' :=
  AlterSeq.endState_append_singleton E hT Silent.τ m'

open Classical in
/-- **`g`-integrated collapse for an abstract scheduler.** If `S`'s halting
pushforward (from `PMF.pure μ0`) is the macro-mixture `Ν` (hypothesis `hpush`),
then integrating any `g` over the halting macro end-state equals integrating `g`
against `Ν`. Re-derivation of the `weakTau.integrate` argument, decoupled from
the classical witness extraction. -/
private theorem macroIntegrate_of_pushforward {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) (Ν : PMF (PMF State))
    (hpush : ∀ m, Ν m = ∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
        S.haltMass (PMF.pure μ0) E * (if E.1.endState E.2 = m then 1 else 0))
    (g : PMF State → ENNReal) :
    (∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
        S.haltMass (PMF.pure μ0) E * g (E.1.endState E.2))
      = ∑' m, Ν m * g m := by
  classical
  symm
  calc (∑' m, Ν m * g m)
      = ∑' m, (∑' E, S.haltMass (PMF.pure μ0) E *
            (if E.1.endState E.2 = m then 1 else 0)) * g m :=
        tsum_congr (fun m => by rw [hpush m])
    _ = ∑' m, ∑' E, S.haltMass (PMF.pure μ0) E *
            (if E.1.endState E.2 = m then 1 else 0) * g m :=
        tsum_congr (fun m => by rw [ENNReal.tsum_mul_right])
    _ = ∑' E, ∑' m, S.haltMass (PMF.pure μ0) E *
            (if E.1.endState E.2 = m then 1 else 0) * g m := ENNReal.tsum_comm
    _ = ∑' E, S.haltMass (PMF.pure μ0) E * g (E.1.endState E.2) := by
        refine tsum_congr (fun E => ?_)
        rw [tsum_congr (fun m => by ring :
            ∀ m, S.haltMass (PMF.pure μ0) E * (if E.1.endState E.2 = m then 1 else 0) * g m
              = S.haltMass (PMF.pure μ0) E *
                ((if E.1.endState E.2 = m then 1 else 0) * g m)),
          ENNReal.tsum_mul_left]
        congr 1
        rw [tsum_eq_single (E.1.endState E.2)
            (fun m' hm' => by rw [if_neg (fun heq => hm' heq.symm), zero_mul]),
          if_pos rfl, one_mul]

/-- **Flattened halting sub-distribution at macro-depth `k`.** The mass that,
under scheduler `S` run from `PMF.pure μ0`, halts along a terminating macro-run
of exactly `k` internal macro-steps, pushed forward to `State` through the macro
end-state. Summing over `k` recovers the whole flattened mixture
(`macroHalt_tsum_depth`). -/
noncomputable def macroHaltDepth {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) (k : ℕ) : State → ENNReal :=
  fun s => ∑' E : {E : {e : AlterSeq (PMF State) Label // e.trans.Terminates} //
      E.1.trans.length E.2 = k},
    S.haltMass (PMF.pure μ0) E.1 * (E.1.1.endState E.1.2) s

open Classical in
/-- **Macro-depth stratification.** The end-state mixture `Ν.bind id` of a
macro-`weakTau` (captured abstractly by the pushforward `hpush` of an
a.s.-stopping scheduler `S`) equals the countable sum, over macro-depth `k`, of
the depth-`k` flattened halting sub-distributions. Proof: expand `Ν.bind id`
pointwise (`PMF.bind_apply`), collapse the macro end-state integral
(`macroIntegrate_of_pushforward` at `g := (· s)`), then stratify the execution
sum by transition-length via the fiber equivalence `Equiv.sigmaFiberEquiv` and
`ENNReal.tsum_sigma'`. -/
theorem macroHalt_tsum_depth {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) {Ν : PMF (PMF State)}
    (hpush : ∀ m, Ν m = ∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
        S.haltMass (PMF.pure μ0) E * (if E.1.endState E.2 = m then 1 else 0))
    (s : State) :
    (Ν.bind id) s = ∑' k : ℕ, macroHaltDepth S μ0 k s := by
  classical
  have key : (∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
        S.haltMass (PMF.pure μ0) E * (E.1.endState E.2) s)
      = ∑' k : ℕ, macroHaltDepth S μ0 k s := by
    rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv
        (fun E : {e : AlterSeq (PMF State) Label // e.trans.Terminates} =>
          E.1.trans.length E.2)), ENNReal.tsum_sigma']
    rfl
  rw [PMF.bind_apply, ← key]
  exact (macroIntegrate_of_pushforward S μ0 Ν hpush (fun m => m s)).symm

/-! ### Stratification: depth-`k` halting totals sum to the halting mass -/

/-- Total mass of the depth-`k` flattened halting sub-distribution
`macroHaltDepth`: the halting mass carried by terminating macro-runs of exactly
`k` internal steps. -/
theorem macroHaltDepth_total {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) (k : ℕ) :
    (∑' s, macroHaltDepth S μ0 k s)
      = ∑' E : {E : {e : AlterSeq (PMF State) Label // e.trans.Terminates} //
          E.1.trans.length E.2 = k}, S.haltMass (PMF.pure μ0) E.1 := by
  unfold macroHaltDepth
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro E
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

/-- **Depth totals sum to the total halting mass.** Summing the depth-`k` halting
totals over `k` recovers the scheduler's whole halting mass from `PMF.pure μ0`
(reverse of the fiber stratification). -/
theorem macroHaltDepth_tsum {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) :
    (∑' k : ℕ, ∑' s, macroHaltDepth S μ0 k s)
      = ∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
          S.haltMass (PMF.pure μ0) E := by
  simp_rw [macroHaltDepth_total]
  rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv
      (fun E : {e : AlterSeq (PMF State) Label // e.trans.Terminates} =>
        E.1.trans.length E.2)), ENNReal.tsum_sigma']
  rfl

/-- **Halted total rises to `1` under a.s.-halting.** If the scheduler `S` halts
almost surely from `PMF.pure μ0` (`hhalt`), the supremum over the truncation depth
`n` of the halting mass accumulated in the first `n` macro-depths is `1`
(partial sums of the depth totals). -/
theorem macroHalted_iSup_eq_one {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (hhalt : (∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
        S.haltMass (PMF.pure μ0) E) = 1) :
    (⨆ n : ℕ, ∑ k ∈ Finset.range n, ∑' s, macroHaltDepth S μ0 k s) = 1 := by
  rw [← ENNReal.tsum_eq_iSup_nat, macroHaltDepth_tsum]
  exact hhalt

/-! ### The per-emission inner witnesses

The hidden configuration behind an observed `sys`-history `e` is a
*decomposition* of `e` into completed inner macro-segments plus a current
in-progress inner prefix; the carrier and the belief weight are defined by
recursion mirroring one another. Per-macro-step inner witnesses are extracted
classically from `weakTau_of_distStep`, exactly as
`weakTau.witnessScheduler`. -/

open Classical in
/-- **Per-emission inner witness.** For a macro-state `m : PMF State` and a
macro-emission `ω : PMF (PMF State)`, the witnessing internal `sys`-scheduler for
the single-macro-step weak transition `weakTau sys m (ω.bind id)`
(`weakTau_of_distStep`); off the support (no such internal macro-step) it is the
immediately-stopping scheduler. Classical, mirroring `weakTau.witnessScheduler`. -/
noncomputable def innerWitness (sys : System State Label) (m : PMF State)
    (ω : PMF (PMF State)) : WeakScheduler sys :=
  if h : (𝒟(sys^w)).step m Silent.τ ω then (weakTau_of_distStep h).witnessScheduler
  else WeakScheduler.stop sys

/-- On the support, the inner witness's `g`-integrated halting end-state equals
the `g`-integral against the macro-mixture `ω.bind id` (the single-step collapse,
`g`-integrated). Taking `g = [· = s]` gives the end-state pushforward. -/
theorem innerWitness_integrate {sys : System State Label} {m : PMF State}
    {ω : PMF (PMF State)} (h : (𝒟(sys^w)).step m Silent.τ ω) (g : State → ENNReal) :
    (∑' e, (innerWitness sys m ω).haltMass m e * g (e.1.endState e.2))
      = ∑' s, (ω.bind id) s * g s := by
  rw [innerWitness, dif_pos h]; exact (weakTau_of_distStep h).integrate g

open Classical in
/-- On the support, the inner witness's halting end-state pushforward is the
macro-mixture `ω.bind id`. -/
theorem innerWitness_pushforward {sys : System State Label} {m : PMF State}
    {ω : PMF (PMF State)} (h : (𝒟(sys^w)).step m Silent.τ ω) (s : State) :
    (ω.bind id) s
      = ∑' e, (innerWitness sys m ω).haltMass m e * (if e.1.endState e.2 = s then 1 else 0) := by
  rw [innerWitness, dif_pos h]; exact (weakTau_of_distStep h).witness_pushforward s

/-! ### The conditional depth totals `condDepth`

The conditional depth total `condDepth` is a `pathWeight`-weighted halt-mass
sum over the `k`-step continuations of a base macro-history; it satisfies a
front-peel recursion, and at the root it is the global depth-`k` halting mass
(via `probOf_eq_pathWeight` and the Dirac collapse of the source). -/

/-- The conditional depth-`k` halt total from base macro-history `E`: the total
mass, over the `k`-step continuations of `E`, of the path-weight to the
continuation times the scheduler-stop probability there. -/
private noncomputable def condDepth {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) (k : ℕ)
    (E : AlterSeq (PMF State) Label) : ENNReal :=
  ∑' K : {K : List (Label × PMF State) // K.length = k},
    (⟨PMF.pure μ0, S.toScheduler⟩ : ProbabilisticExecution (𝒟(sys^w))).pathWeight E K.1
      * S.next ⟨E.init, E.trans.append (Seq.ofList K.1)⟩ none

/-- Split an `ENNReal` tsum over `Option γ` into the `none` value plus the tsum
over `some`. (Local copy of `Scheduler`'s private helper.) -/
private theorem tsumOpt {γ : Type} (f : Option γ → ENNReal) :
    (∑' o, f o) = f none + ∑' n, f (some n) := by
  rw [← (Equiv.optionEquivSumPUnit.{0} γ).symm.tsum_eq f,
    Summable.tsum_sum ENNReal.summable ENNReal.summable, add_comm]
  congr 1
  rw [tsum_eq_single PUnit.unit (by rintro ⟨⟩ h; exact absurd rfl h)]
  rfl

/-- `condDepth` at depth `0` is the scheduler-stop probability at `E`. -/
private theorem condDepth_zero {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) (E : AlterSeq (PMF State) Label) :
    condDepth S μ0 0 E = S.next E none := by
  unfold condDepth
  rw [tsum_eq_single (⟨[], rfl⟩ : {K : List (Label × PMF State) // K.length = 0})
    (fun K hK => absurd (Subtype.ext (List.length_eq_zero_iff.mp K.2)) hK)]
  have hpw : (⟨PMF.pure μ0, S.toScheduler⟩ :
      ProbabilisticExecution (𝒟(sys^w))).pathWeight E [] = 1 := by
    unfold ProbabilisticExecution.pathWeight; rw [List.reverseRecOn_nil]
  rw [hpw, one_mul, Stream'.Seq.ofList_nil, Stream'.Seq.append_nil]

/-- Cons bijection: length-`(k+1)` lists ↔ (head, length-`k` tail). -/
private def consLenEquiv {γ : Type} (k : ℕ) :
    (γ × {K : List γ // K.length = k}) ≃ {L : List γ // L.length = k + 1} where
  toFun p := ⟨p.1 :: p.2.1, by rw [List.length_cons, p.2.2]⟩
  invFun L := (L.1.head (List.ne_nil_of_length_pos (by rw [L.2]; exact Nat.succ_pos k)),
    ⟨L.1.tail, by rw [List.length_tail, L.2, Nat.add_sub_cancel]⟩)
  left_inv := by
    rintro ⟨x, ⟨K, hK⟩⟩
    exact Prod.ext rfl (Subtype.ext (by simp))
  right_inv := by
    rintro ⟨L, hL⟩
    exact Subtype.ext (List.cons_head_tail _)

/-- One-step recursion of `condDepth`: front-peel of the continuation list. -/
private theorem condDepth_succ {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) (k : ℕ)
    (E : AlterSeq (PMF State) Label) :
    condDepth S μ0 (k + 1) E
      = ∑' o, (S.next E) o * (match o with
          | none => 0
          | some (_, ω) => ∑' m', ω m' * condDepth S μ0 k (macroExtend E m')) := by
  have hzero : ∀ (l : Label) (ω : PMF (PMF State)), l ≠ Silent.τ →
      S.next E (some (l, ω)) = 0 := fun l ω hl => by
    by_contra hne
    exact hl (S.internal_only E l ω ((PMF.mem_support_iff _ _).mpr hne))
  -- the common normal form both sides reduce to
  set C : ENNReal := ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
      * ∑' m', ω m' * condDepth S μ0 k (macroExtend E m') with hC
  have hRHS : (∑' o, (S.next E) o * (match o with
        | none => (0 : ENNReal)
        | some (_, ω) => ∑' m', ω m' * condDepth S μ0 k (macroExtend E m'))) = C := by
    rw [tsumOpt (fun o => (S.next E) o * (match o with
        | none => (0 : ENNReal)
        | some (_, ω) => ∑' m', ω m' * condDepth S μ0 k (macroExtend E m')))]
    simp only [mul_zero, zero_add]
    rw [ENNReal.tsum_prod']
    rw [tsum_eq_single Silent.τ (fun l hl => by
      rw [ENNReal.tsum_eq_zero]; intro ω; rw [hzero l ω hl, zero_mul])]
  have hker0 : ∀ (l : Label) (m' : PMF State), l ≠ Silent.τ →
      (⟨PMF.pure μ0, S.toScheduler⟩ :
        ProbabilisticExecution (𝒟(sys^w))).kernel E (l, m') = 0 := by
    intro l m' hl
    unfold ProbabilisticExecution.kernel
    rw [ENNReal.tsum_eq_zero]
    intro ω
    rw [hzero l ω hl, zero_mul]
  have hpath : ∀ (l : Label) (m' : PMF State)
      (K' : {K : List (Label × PMF State) // K.length = k}),
      (⟨PMF.pure μ0, S.toScheduler⟩ :
          ProbabilisticExecution (𝒟(sys^w))).pathWeight E ((l, m') :: K'.1)
          * S.next ⟨E.init, E.trans.append (Seq.ofList ((l, m') :: K'.1))⟩ none
        = (⟨PMF.pure μ0, S.toScheduler⟩ :
            ProbabilisticExecution (𝒟(sys^w))).kernel E (l, m')
          * ((⟨PMF.pure μ0, S.toScheduler⟩ :
              ProbabilisticExecution (𝒟(sys^w))).pathWeight
                ⟨E.init, E.trans.append (Seq.cons (l, m') Seq.nil)⟩ K'.1
              * S.next ⟨E.init, (E.trans.append (Seq.cons (l, m') Seq.nil)).append
                  (Seq.ofList K'.1)⟩ none) := by
    intro l m' K'
    rw [ProbabilisticExecution.pathWeight_cons,
      show E.trans.append (Seq.ofList ((l, m') :: K'.1))
          = (E.trans.append (Seq.cons (l, m') Seq.nil)).append (Seq.ofList K'.1) from by
        rw [Stream'.Seq.ofList_cons, Stream'.Seq.append_assoc, Stream'.Seq.cons_append,
          Stream'.Seq.nil_append]]
    ring
  have hLHS : condDepth S μ0 (k + 1) E = C := by
    unfold condDepth
    rw [← Equiv.tsum_eq (consLenEquiv (γ := Label × PMF State) k),
      ENNReal.tsum_prod', ENNReal.tsum_prod']
    simp only [consLenEquiv, Equiv.coe_fn_mk]
    rw [tsum_congr (fun l => tsum_congr (fun m' => tsum_congr (fun K' => hpath l m' K'))),
      tsum_congr (fun l => tsum_congr (fun _ => ENNReal.tsum_mul_left)),
      tsum_eq_single Silent.τ (fun l hl => by
        rw [ENNReal.tsum_eq_zero]; intro m'; rw [hker0 l m' hl, zero_mul])]
    rw [hC]
    simp only [ProbabilisticExecution.kernel]
    rw [tsum_congr (fun _ => ENNReal.tsum_mul_right.symm), ENNReal.tsum_comm]
    apply tsum_congr; intro ω
    rw [tsum_congr (fun m' => mul_assoc _ _ _), ENNReal.tsum_mul_left]
    rfl
  rw [hLHS]; exact hRHS.symm

/-- Length-`k` terminating macro-histories ↔ (initial macro-state, length-`k`
transition list). -/
private def rootEquiv (k : ℕ) :
    (PMF State × {K : List (Label × PMF State) // K.length = k})
      ≃ {E : {e : AlterSeq (PMF State) Label // e.trans.Terminates} //
          E.1.trans.length E.2 = k} where
  toFun p := ⟨⟨⟨p.1, Seq.ofList p.2.1⟩, Stream'.Seq.terminates_ofList p.2.1⟩, by
    rw [WeakScheduler.length_ofList]; exact p.2.2⟩
  invFun E := (E.1.1.init, ⟨E.1.1.trans.toList E.1.2, by
    rw [Stream'.Seq.length_toList]; exact E.2⟩)
  left_inv := by
    rintro ⟨s, ⟨K, hK⟩⟩
    exact Prod.ext rfl (Subtype.ext (Stream'.Seq.toList_ofList K))
  right_inv := by
    rintro ⟨⟨⟨i, tr⟩, hterm⟩, hlen⟩
    refine Subtype.ext (Subtype.ext ?_)
    change (⟨i, Seq.ofList (tr.toList hterm)⟩ : AlterSeq (PMF State) Label) = ⟨i, tr⟩
    rw [Stream'.Seq.ofList_toList]

/-- At the root, `condDepth` is the global depth-`k` halting mass. -/
private theorem condDepth_root {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) (k : ℕ) :
    condDepth S μ0 k ⟨μ0, Seq.nil⟩
      = ∑' E : {E : {e : AlterSeq (PMF State) Label // e.trans.Terminates} //
          E.1.trans.length E.2 = k}, S.haltMass (PMF.pure μ0) E.1 := by
  have hsummand : ∀ (s : PMF State) (K : {K : List (Label × PMF State) // K.length = k}),
      S.haltMass (PMF.pure μ0) (rootEquiv k (s, K)).1
        = PMF.pure μ0 s * ((⟨PMF.pure μ0, S.toScheduler⟩ :
            ProbabilisticExecution (𝒟(sys^w))).pathWeight ⟨s, Seq.nil⟩ K.1
              * S.next ⟨s, Seq.ofList K.1⟩ none) := by
    intro s K
    show S.haltMass (PMF.pure μ0)
        ⟨⟨s, Seq.ofList K.1⟩, Stream'.Seq.terminates_ofList K.1⟩ = _
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [ProbabilisticExecution.probOf_eq_pathWeight,
      ProbabilisticExecution.init_eq_initState, mul_assoc]
  unfold condDepth
  simp only [Stream'.Seq.nil_append]
  rw [← Equiv.tsum_eq (rootEquiv k), ENNReal.tsum_prod']
  rw [tsum_congr (fun s => tsum_congr (fun K => hsummand s K))]
  rw [tsum_congr (fun s => ENNReal.tsum_mul_left)]
  rw [tsum_eq_single μ0 (fun s hs => by rw [PMF.pure_apply, if_neg hs, zero_mul]),
    PMF.pure_apply_self, one_mul]

/-! ### The segment machinery

The segment/weight/connection machinery
(`FlatSeg`/`segTrans`/`segSrc`/`segHist`/`segWeight`/`chained`/`moveTerm`, and
`endState_append_shift`/`chained_endState`) behind the decision-point carrier
`DConfig`: the hidden configuration behind an observed `sys`-history is a list
of completed inner macro-segments; the belief weight is defined by recursion
mirroring the segment list. -/

/-- A completed inner macro-segment behind an observed `sys`-history: the
macro-emission `emit`, the sampled successor macro-state `succ`, and the
completed inner `sys`-execution `run` (a terminating run of the associated
`innerWitness`). -/
structure FlatSeg (State Label : Type) where
  /-- The macro-emission `ω : PMF (PMF State)` chosen for this macro-step. -/
  emit : PMF (PMF State)
  /-- The sampled successor macro-state `m' ~ emit`. -/
  succ : PMF State
  /-- The completed inner `sys`-execution witnessing this macro-step. -/
  run : AlterSeq State Label
  /-- The inner execution terminates. -/
  runT : run.trans.Terminates

variable {sys : System State Label}

/-- The concatenated transition sequence of the completed segments' inner runs,
followed by the current prefix `c`. Fold-append per D1. -/
noncomputable def segTrans :
    List (FlatSeg State Label) → Stream'.Seq (Label × State) → Stream'.Seq (Label × State)
  | [], c => c
  | List.cons seg rest, c => seg.run.trans.append (segTrans rest c)

/-- The current source macro-state after the completed segments, threading from
the root source `src0`: the last segment's successor (or `src0` if none). -/
noncomputable def segSrc (src0 : PMF State) : List (FlatSeg State Label) → PMF State
  | [] => src0
  | List.cons seg rest => segSrc seg.succ rest

/-- The current macro-history after the completed segments, threading from the
root history `E` by `macroExtend` at each segment's successor. -/
noncomputable def segHist (E : AlterSeq (PMF State) Label) :
    List (FlatSeg State Label) → AlterSeq (PMF State) Label
  | [] => E
  | List.cons seg rest => segHist (macroExtend E seg.succ) rest

/-- The belief path-weight of the completed segments: the macro path-measure of
the chosen emissions/successors times each inner run's halting mass, by recursion
mirroring the segment list. Threads the current source `src0` and macro-history
`E`. -/
noncomputable def segWeight (S : WeakScheduler (𝒟(sys^w))) (src0 : PMF State)
    (E : AlterSeq (PMF State) Label) : List (FlatSeg State Label) → ENNReal
  | [] => 1
  | List.cons seg rest =>
      S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
        * ((innerWitness sys src0 seg.emit).haltMass src0 ⟨seg.run, seg.runT⟩
            / (seg.emit.bind id) (seg.run.endState seg.runT))
        * segWeight S seg.succ (macroExtend E seg.succ) rest

/-- Connection predicate: threading the connecting state `s0`, each completed
run starts where the previous one ended, and the current prefix starts where the
last completed run ended (or at `s0` if there are none). Forces the config to be a
genuine decomposition of a single connected `sys`-execution. -/
def chained (s0 : State) : List (FlatSeg State Label) → State → Prop
  | [], curInit => curInit = s0
  | List.cons seg rest, curInit =>
      seg.run.init = s0 ∧ chained (seg.run.endState seg.runT) rest curInit

open Classical in
/-- The next-move contribution of a config's *current* inner run (belief over the
emission `ω`) at prefix `cur`, source `src`, macro-history `Ec`:
* `some (l, ν)`: the current inner run continues, emitting `(l, ν)` — path measure
  to `cur` under `innerWitness src ω`, times its next move, summed over `ω`
  weighted by the macro choice `S.next Ec (some (τ, ω))`.
* `none`: the composite halts at the macro-boundary — only when the current prefix
  is empty (the completed runs reconstruct all of `e`), contributing `S.next Ec none`. -/
noncomputable def moveTerm (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (Ec : AlterSeq (PMF State) Label)
    (cur : {p : AlterSeq State Label // p.trans.Terminates}) :
    Option (Label × PMF State) → ENNReal
  | none => if cur.1.trans = Stream'.Seq.nil then S.next Ec none else 0
  | some (l, ν) => ∑' ω : PMF (PMF State), S.next Ec (some (Silent.τ, ω))
      * (⟨src, (innerWitness sys src ω).toScheduler⟩
          : ProbabilisticExecution sys).probOf cur.1 cur.2
      * (innerWitness sys src ω).next cur.1 (some (l, ν))

/-- **End-state after append.** Appending `B` after `A` yields an end-state that
is the end-state of `⟨endState of A, B⟩` — the last transition wins, and when `B`
is empty the end-state of `A` carries through. -/
theorem endState_append_shift (i : State) (A B : Stream'.Seq (Label × State))
    (hA : A.Terminates) (hAB : (A.append B).Terminates) (hB : B.Terminates) :
    (⟨i, A.append B⟩ : AlterSeq State Label).endState hAB
      = (⟨(⟨i, A⟩ : AlterSeq State Label).endState hA, B⟩ : AlterSeq State Label).endState hB := by
  classical
  rw [AlterSeq.endState_eq_getLast?, AlterSeq.endState_eq_getLast?,
    AlterSeq.endState_eq_getLast?]
  have htl : (A.append B).toList hAB = A.toList hA ++ B.toList hB :=
    Stream'.Seq.toList_append A B hA hB hAB
  simp only [htl]
  cases hBl : B.toList hB with
  | nil => simp only [List.append_nil, List.getLast?_nil, Option.elim]
  | cons x xs =>
    have hne : (x :: xs) ≠ [] := by simp
    rw [List.getLast?_append_of_ne_nil _ hne]
    cases hgl : (x :: xs).getLast? with
    | none => simp at hgl
    | some z => simp only [Option.elim]

/-- **Chained end-state.** When a config `chained`s from `s0` and its segments'
runs (with the current prefix) reconstruct `e`'s transitions, the composite
end-state is the current prefix's end-state. -/
theorem chained_endState :
    ∀ (segs : List (FlatSeg State Label)) (s0 : State)
      (cur : {p : AlterSeq State Label // p.trans.Terminates})
      (hT : (⟨s0, segTrans segs cur.1.trans⟩ : AlterSeq State Label).trans.Terminates),
      chained s0 segs cur.1.init →
      (⟨s0, segTrans segs cur.1.trans⟩ : AlterSeq State Label).endState hT
        = cur.1.endState cur.2
  | [], s0, cur, hT, hch => by
      have hs : cur.1.init = s0 := hch
      refine AlterSeq.endState_congr_pub ?_ hT cur.2
      simp only [segTrans]
      rw [← hs]
  | List.cons seg rest, s0, cur, hT, hch => by
      simp only [segTrans] at hT ⊢
      simp only [chained] at hch
      have hAterm : seg.run.trans.Terminates := seg.runT
      have hBterm : (segTrans rest cur.1.trans).Terminates := by
        refine ⟨Nat.find hT, ?_⟩
        have happ : (seg.run.trans.append (segTrans rest cur.1.trans)).TerminatedAt
            (Nat.find hAterm + Nat.find hT) :=
          Stream'.Seq.terminated_stable _ (Nat.le_add_left (Nat.find hT) (Nat.find hAterm))
            (Nat.find_spec hT)
        have hget := Stream'.Seq.get?_append_find hAterm (segTrans rest cur.1.trans) (Nat.find hT)
        change (segTrans rest cur.1.trans).get? (Nat.find hT) = none
        rw [← hget]; exact happ
      rw [endState_append_shift s0 seg.run.trans (segTrans rest cur.1.trans) hAterm hT hBterm]
      have heqseg : (⟨s0, seg.run.trans⟩ : AlterSeq State Label) = seg.run := by rw [← hch.1]
      have hj : (⟨s0, seg.run.trans⟩ : AlterSeq State Label).endState hAterm
          = seg.run.endState seg.runT :=
        AlterSeq.endState_congr_pub heqseg hAterm seg.runT
      rw [hj]
      exact chained_endState rest (seg.run.endState seg.runT) cur hBterm hch.2

/-- **Monotone `tsum`↔`iSup` interchange.** For an `ENNReal` family monotone in
its `ℕ` parameter, the countable sum of the pointwise suprema equals the supremum
of the countable sums (monotone convergence for the counting measure). -/
theorem tsum_iSup_of_monotone {ι : Type} (f : ℕ → ι → ENNReal)
    (hf : ∀ i, Monotone (fun n => f n i)) :
    ∑' i, ⨆ n, f n i = ⨆ n, ∑' i, f n i := by
  rw [ENNReal.tsum_eq_iSup_sum]
  simp_rw [ENNReal.finsetSum_iSup_of_monotone (f := fun a n => f n a) hf]
  rw [iSup_comm]
  simp_rw [← ENNReal.tsum_eq_iSup_sum]

/-- **The decision-point carrier.** A hidden configuration behind an observed
`sys`-history: completed inner segments `segs` (each nonempty, enforced by
`dConsistent`) plus the current in-progress inner prefix `cur`. -/
structure DConfig (State Label : Type) where
  /-- Completed inner macro-segments (all nonempty at a decision point). -/
  segs : List (FlatSeg State Label)
  /-- Current in-progress inner prefix (may be empty at a fresh decision point). -/
  cur : AlterSeq State Label
  /-- The current prefix terminates. -/
  curT : cur.trans.Terminates

/-- Consistency of a `DConfig` with an observed history `e`: the segments and
the current prefix reconstruct `e`'s transitions, and the runs chain from
`e.init`. **Stall-resolvent widening:** completed segments may be EMPTY —
a finite stall chain between decision points is represented by empty-run
segments, whose `segWeight` factors are exactly the Bayes-coupled resolvent
terms `S.next E (τ,ω) · ω m' · haltMass src ⟨t,nil⟩ / (ω.bind id) t`. -/
def dConsistent (e : AlterSeq State Label) (c : DConfig State Label) : Prop :=
  segTrans c.segs c.cur.trans = e.trans ∧ chained e.init c.segs c.cur.init

/-- Dropping the exact length of a terminating left factor from an `append`
recovers the right factor. -/
private theorem drop_append_length {α : Type} (A Y : Stream'.Seq α)
    (hA : A.Terminates) : (A.append Y).drop (A.length hA) = Y := by
  apply Stream'.Seq.ext
  intro m
  rw [Stream'.Seq.drop_get?]
  exact Stream'.Seq.get?_append_find hA Y m

/-- Length is additive over `append` of terminating sequences. -/
private theorem length_append_seq {α : Type} (A B : Stream'.Seq α)
    (hA : A.Terminates) (hB : B.Terminates) (hAB : (A.append B).Terminates) :
    (A.append B).length hAB = A.length hA + B.length hB := by
  rw [← Stream'.Seq.length_toList _ hAB,
    Stream'.Seq.toList_append A B hA hB hAB, List.length_append,
    Stream'.Seq.length_toList, Stream'.Seq.length_toList]

/-- Length is invariant under equality of the underlying sequence. -/
private theorem length_congr {α : Type} (s t : Stream'.Seq α)
    (hs : s.Terminates) (ht : t.Terminates) (h : s = t) : s.length hs = t.length ht := by
  subst h; rfl

/-- `DConfig` reindexes as a `(segs, current)` pair. -/
private def dcE : DConfig State Label ≃
    List (FlatSeg State Label) × {q : AlterSeq State Label // q.trans.Terminates} where
  toFun c := (c.segs, ⟨c.cur, c.curT⟩)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl

/-- `FlatSeg` reindexes as `(emit, succ, run)`. -/
private def flatSegEquiv : FlatSeg State Label ≃
    PMF (PMF State) × PMF State × {q : AlterSeq State Label // q.trans.Terminates} where
  toFun s := (s.emit, s.succ, ⟨s.run, s.runT⟩)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv := fun ⟨_, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, ⟨_, _⟩⟩ => rfl

/-- Peel the head of a `List`-indexed `ENNReal` tsum. -/
private def listOptEquiv (X : Type) : List X ≃ Option (X × List X) where
  toFun l := l.casesOn none (fun x t => some (x, t))
  invFun o := o.casesOn List.nil (fun p => List.cons p.1 p.2)
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | ⟨_, _⟩) <;> rfl

private theorem listSplit {X : Type} (f : List X → ENNReal) :
    ∑' l : List X, f l = f [] + ∑' q : X × List X, f (q.1 :: q.2) := by
  have h := tsumOpt (fun o => f ((listOptEquiv X).symm o))
  rw [Equiv.tsum_eq (listOptEquiv X).symm f] at h
  exact h

/-- The residual observed history after peeling a first segment `seg` from `e`:
start at the segment's end-state, transitions are `e`'s with the run's prefix
dropped. -/
private noncomputable def dResidual
    (e : {q : AlterSeq State Label // q.trans.Terminates})
    (seg : FlatSeg State Label) : {q : AlterSeq State Label // q.trans.Terminates} :=
  ⟨⟨seg.run.endState seg.runT,
      e.1.trans.drop (seg.run.trans.length seg.runT)⟩,
    WeakScheduler.drop_terminates e.2 _⟩

/-- A first segment `seg` is a legal peel from `e`: its run starts at `e.init`,
its transition prefix is a genuine prefix of `e`'s transitions. The run
may be EMPTY — a stall peel, whose residual is `e` itself. -/
private def segPre (e : {q : AlterSeq State Label // q.trans.Terminates})
    (seg : FlatSeg State Label) : Prop :=
  seg.run.init = e.1.init
    ∧ seg.run.trans.append (e.1.trans.drop (seg.run.trans.length seg.runT)) = e.1.trans

/-- **Segment-peeling decomposition of `dConsistent`.** A config with a head
segment is consistent with `e` iff that head is a legal prefix peel (`segPre`)
and the tail config is consistent with the residual history. -/
private theorem dConsistent_cons_iff
    (e : {q : AlterSeq State Label // q.trans.Terminates})
    (seg : FlatSeg State Label) (rest : List (FlatSeg State Label))
    (curA : AlterSeq State Label) (hcur : curA.trans.Terminates) :
    dConsistent e.1 ⟨seg :: rest, curA, hcur⟩ ↔
      segPre e seg ∧ dConsistent (dResidual e seg).1 ⟨rest, curA, hcur⟩ := by
  have hdrop : (seg.run.trans.append (segTrans rest curA.trans)).drop
        (seg.run.trans.length seg.runT) = segTrans rest curA.trans :=
    drop_append_length seg.run.trans (segTrans rest curA.trans) seg.runT
  simp only [dConsistent, segPre, dResidual, segTrans, chained,
    List.forall_mem_cons]
  constructor
  · rintro ⟨htrans, hinit, hchain⟩
    have hYeq : e.1.trans.drop (seg.run.trans.length seg.runT) = segTrans rest curA.trans := by
      rw [← htrans]; exact hdrop
    refine ⟨⟨hinit, ?_⟩, ?_, hchain⟩
    · rw [hYeq]; exact htrans
    · exact hYeq.symm
  · rintro ⟨⟨hinit, hpre⟩, hseg, hchain⟩
    refine ⟨?_, hinit, hchain⟩
    rw [hseg]; exact hpre

/-- A config with no completed segments is consistent with `e` iff its current
prefix *is* `e`. -/
private theorem dConsistent_nil_iff
    (e cur : {q : AlterSeq State Label // q.trans.Terminates}) :
    dConsistent e.1 ⟨[], cur.1, cur.2⟩ ↔ cur = e := by
  constructor
  · rintro ⟨htr, hin⟩
    obtain ⟨cval, cproof⟩ := cur
    obtain ⟨ci, ct⟩ := cval
    apply Subtype.ext
    show (⟨ci, ct⟩ : AlterSeq State Label) = e.1
    have e1 : ci = e.1.init := hin
    have e2 : ct = e.1.trans := htr
    rw [e1, e2]
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- Integrating a test `g` against a `PMF.bind` splits as the source-weighted sum
of the branch integrals (the `∑'`-form of `∫ g d(p.bind f) = ∑ₐ p a · ∫ g d(f a)`). -/
private theorem tsum_bind_mul {γ : Type} (p : PMF γ) (f : γ → PMF State)
    (g : State → ENNReal) :
    (∑' s, (p.bind f) s * g s) = ∑' a, p a * ∑' s, f a s * g s := by
  have h1 : (∑' s, (p.bind f) s * g s) = ∑' s, ∑' a, p a * f a s * g s :=
    tsum_congr fun s => by rw [PMF.bind_apply, ENNReal.tsum_mul_right]
  rw [h1, ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun s => by ring

/-- `condDepth` one-step recursion, unfolded to a sum over macro-emissions `ω`
and their successor sources `m'`. -/
private theorem condDepth_succ' (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (k : ℕ) (E : AlterSeq (PMF State) Label) :
    condDepth S μ0 (k + 1) E
      = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * ∑' m', ω m' * condDepth S μ0 k (macroExtend E m') := by
  have hzero : ∀ (l : Label) (ω : PMF (PMF State)), l ≠ Silent.τ →
      S.next E (some (l, ω)) = 0 := fun l ω hl => by
    by_contra hne
    exact hl (S.internal_only E l ω ((PMF.mem_support_iff _ _).mpr hne))
  rw [condDepth_succ, tsumOpt (fun o => (S.next E) o * (match o with
      | none => (0 : ENNReal)
      | some (_, ω) => ∑' m', ω m' * condDepth S μ0 k (macroExtend E m')))]
  simp only [mul_zero, zero_add]
  rw [ENNReal.tsum_prod']
  rw [tsum_eq_single Silent.τ (fun l hl => by
    rw [ENNReal.tsum_eq_zero]; intro ω; rw [hzero l ω hl, zero_mul])]

/-- Appending a finite list to a terminating macro-history's transitions again
terminates. -/
private theorem append_ofList_term (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) (K : List (Label × PMF State)) :
    (E.trans.append (Seq.ofList K)).Terminates :=
  ⟨Nat.find hT + Nat.find (Stream'.Seq.terminates_ofList K),
    Stream'.Seq.terminatedAt_append_find hT
      (Nat.find_spec (Stream'.Seq.terminates_ofList K))⟩

/-- The `g := [· = s]`-weighted conditional depth-`k` halt total from base
macro-history `E`: `condDepth` with the extra factor of the depth-`k`
continuation's macro end-state evaluated at `s`. -/
private noncomputable def condDepthG (S : WeakScheduler (𝒟(sys^w))) (k : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (s : State) : ENNReal :=
  ∑' K : {K : List (Label × PMF State) // K.length = k},
    (⟨PMF.pure E.init, S.toScheduler⟩ : ProbabilisticExecution (𝒟(sys^w))).pathWeight E K.1
      * S.next ⟨E.init, E.trans.append (Seq.ofList K.1)⟩ none
      * (⟨E.init, E.trans.append (Seq.ofList K.1)⟩ :
          AlterSeq (PMF State) Label).endState (append_ofList_term E hT K.1) s

/-- `condDepthG` at depth `0` is the stop probability at `E` times `E`'s own
macro end-state at `s`. -/
private theorem condDepthG_zero (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (s : State) :
    condDepthG S 0 E hT s = S.next E none * (E.endState hT) s := by
  unfold condDepthG
  rw [tsum_eq_single (⟨[], rfl⟩ : {K : List (Label × PMF State) // K.length = 0})
    (fun K hK => absurd (Subtype.ext (List.length_eq_zero_iff.mp K.2)) hK)]
  have hpw : (⟨PMF.pure E.init, S.toScheduler⟩ :
      ProbabilisticExecution (𝒟(sys^w))).pathWeight E [] = 1 := by
    unfold ProbabilisticExecution.pathWeight; rw [List.reverseRecOn_nil]
  rw [hpw, one_mul]
  have hE : (⟨E.init, E.trans.append (Seq.ofList ([] : List (Label × PMF State)))⟩
      : AlterSeq (PMF State) Label) = E := by
    rw [Stream'.Seq.ofList_nil, Stream'.Seq.append_nil]
  congr 1
  · rw [hE]
  · congr 1
    exact AlterSeq.endState_congr_pub hE (append_ofList_term E hT []) hT

/-- One-step recursion of `condDepthG` in the `∑ω`-form (front-peel of the
continuation list; the end-state factor rides along the `consLenEquiv` peel). -/
private theorem condDepthG_succ' (S : WeakScheduler (𝒟(sys^w))) (k : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (s : State) :
    condDepthG S (k + 1) E hT s
      = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * ∑' m', ω m' * condDepthG S k (macroExtend E m') (macroExtend_term hT m') s := by
  have hzero : ∀ (l : Label) (ω : PMF (PMF State)), l ≠ Silent.τ →
      S.next E (some (l, ω)) = 0 := fun l ω hl => by
    by_contra hne
    exact hl (S.internal_only E l ω ((PMF.mem_support_iff _ _).mpr hne))
  have hker0 : ∀ (l : Label) (m' : PMF State), l ≠ Silent.τ →
      (⟨PMF.pure E.init, S.toScheduler⟩ :
        ProbabilisticExecution (𝒟(sys^w))).kernel E (l, m') = 0 := by
    intro l m' hl
    unfold ProbabilisticExecution.kernel
    rw [ENNReal.tsum_eq_zero]; intro ω; rw [hzero l ω hl, zero_mul]
  have hText : ∀ (l : Label) (m' : PMF State),
      (⟨E.init, E.trans.append (Seq.cons (l, m') Seq.nil)⟩ :
        AlterSeq (PMF State) Label).trans.Terminates :=
    fun l m' => ⟨Nat.find hT + 1, Stream'.Seq.terminatedAt_append_find hT
      (show (Seq.cons (l, m') Seq.nil : Seq (Label × PMF State)).TerminatedAt 1 from rfl)⟩
  have hpath : ∀ (l : Label) (m' : PMF State)
      (K' : {K : List (Label × PMF State) // K.length = k}),
      (⟨PMF.pure E.init, S.toScheduler⟩ :
          ProbabilisticExecution (𝒟(sys^w))).pathWeight E ((l, m') :: K'.1)
          * S.next ⟨E.init, E.trans.append (Seq.ofList ((l, m') :: K'.1))⟩ none
          * (⟨E.init, E.trans.append (Seq.ofList ((l, m') :: K'.1))⟩ :
              AlterSeq (PMF State) Label).endState (append_ofList_term E hT _) s
        = (⟨PMF.pure E.init, S.toScheduler⟩ :
            ProbabilisticExecution (𝒟(sys^w))).kernel E (l, m')
          * ((⟨PMF.pure E.init, S.toScheduler⟩ :
              ProbabilisticExecution (𝒟(sys^w))).pathWeight
                ⟨E.init, E.trans.append (Seq.cons (l, m') Seq.nil)⟩ K'.1
            * S.next ⟨E.init, (E.trans.append (Seq.cons (l, m') Seq.nil)).append
                (Seq.ofList K'.1)⟩ none
            * (⟨E.init, (E.trans.append (Seq.cons (l, m') Seq.nil)).append
                (Seq.ofList K'.1)⟩ : AlterSeq (PMF State) Label).endState
                (append_ofList_term ⟨E.init, E.trans.append (Seq.cons (l, m') Seq.nil)⟩
                  (hText l m') K'.1) s) := by
    intro l m' K'
    have hHeq : E.trans.append (Seq.ofList ((l, m') :: K'.1))
        = (E.trans.append (Seq.cons (l, m') Seq.nil)).append (Seq.ofList K'.1) := by
      rw [Stream'.Seq.ofList_cons, Stream'.Seq.append_assoc, Stream'.Seq.cons_append,
        Stream'.Seq.nil_append]
    have hAeq : (⟨E.init, E.trans.append (Seq.ofList ((l, m') :: K'.1))⟩ :
          AlterSeq (PMF State) Label)
        = ⟨E.init, (E.trans.append (Seq.cons (l, m') Seq.nil)).append (Seq.ofList K'.1)⟩ := by
      rw [hHeq]
    have hnext : S.next ⟨E.init, E.trans.append (Seq.ofList ((l, m') :: K'.1))⟩ none
        = S.next ⟨E.init, (E.trans.append (Seq.cons (l, m') Seq.nil)).append
            (Seq.ofList K'.1)⟩ none := by rw [hHeq]
    have hend : (⟨E.init, E.trans.append (Seq.ofList ((l, m') :: K'.1))⟩ :
            AlterSeq (PMF State) Label).endState (append_ofList_term E hT _)
        = (⟨E.init, (E.trans.append (Seq.cons (l, m') Seq.nil)).append
            (Seq.ofList K'.1)⟩ : AlterSeq (PMF State) Label).endState
            (append_ofList_term ⟨E.init, E.trans.append (Seq.cons (l, m') Seq.nil)⟩
              (hText l m') K'.1) :=
      AlterSeq.endState_congr_pub hAeq _ _
    rw [ProbabilisticExecution.pathWeight_cons, hnext, hend]
    ring
  unfold condDepthG
  rw [← Equiv.tsum_eq (consLenEquiv (γ := Label × PMF State) k),
    ENNReal.tsum_prod', ENNReal.tsum_prod']
  simp only [consLenEquiv, Equiv.coe_fn_mk]
  rw [tsum_congr (fun l => tsum_congr (fun m' => tsum_congr (fun K' => hpath l m' K'))),
    tsum_congr (fun l => tsum_congr (fun _ => ENNReal.tsum_mul_left)),
    tsum_eq_single Silent.τ (fun l hl => by
      rw [ENNReal.tsum_eq_zero]; intro m'; rw [hker0 l m' hl, zero_mul])]
  simp only [ProbabilisticExecution.kernel]
  rw [tsum_congr (fun _ => ENNReal.tsum_mul_right.symm), ENNReal.tsum_comm]
  apply tsum_congr; intro ω
  rw [tsum_congr (fun m' => mul_assoc _ _ _), ENNReal.tsum_mul_left]
  rfl

/-- At the root, `condDepthG` is the global depth-`k` end-state pushforward
`macroHaltDepth`. -/
private theorem condDepthG_root (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (k : ℕ) (s : State) :
    condDepthG S k ⟨μ0, Seq.nil⟩ Stream'.Seq.terminates_nil s = macroHaltDepth S μ0 k s := by
  have hsummand : ∀ (i : PMF State) (K : {K : List (Label × PMF State) // K.length = k}),
      S.haltMass (PMF.pure μ0) (rootEquiv k (i, K)).1
          * ((rootEquiv k (i, K)).1.1.endState (rootEquiv k (i, K)).1.2) s
        = PMF.pure μ0 i * ((⟨PMF.pure μ0, S.toScheduler⟩ :
            ProbabilisticExecution (𝒟(sys^w))).pathWeight ⟨i, Seq.nil⟩ K.1
              * S.next ⟨i, Seq.ofList K.1⟩ none
              * ((⟨i, Seq.ofList K.1⟩ : AlterSeq (PMF State) Label).endState
                  (Stream'.Seq.terminates_ofList K.1)) s) := by
    intro i K
    show S.haltMass (PMF.pure μ0)
        ⟨⟨i, Seq.ofList K.1⟩, Stream'.Seq.terminates_ofList K.1⟩
        * ((⟨i, Seq.ofList K.1⟩ : AlterSeq (PMF State) Label).endState
            (Stream'.Seq.terminates_ofList K.1)) s = _
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [ProbabilisticExecution.probOf_eq_pathWeight,
      ProbabilisticExecution.init_eq_initState]
    ring
  unfold macroHaltDepth
  rw [← Equiv.tsum_eq (rootEquiv k), ENNReal.tsum_prod',
    tsum_congr (fun i => tsum_congr (fun K => hsummand i K)),
    tsum_congr (fun i => ENNReal.tsum_mul_left),
    tsum_eq_single μ0 (fun i hi => by rw [PMF.pure_apply, if_neg hi, zero_mul]),
    PMF.pure_apply_self, one_mul]
  unfold condDepthG
  refine tsum_congr (fun K => ?_)
  have hnil : (Seq.nil.append (Seq.ofList K.1) : Seq (Label × PMF State)) = Seq.ofList K.1 :=
    Stream'.Seq.nil_append _
  have hAeq : (⟨μ0, Seq.nil.append (Seq.ofList K.1)⟩ : AlterSeq (PMF State) Label)
      = ⟨μ0, Seq.ofList K.1⟩ := by rw [hnil]
  rw [show S.next ⟨μ0, Seq.nil.append (Seq.ofList K.1)⟩ none
        = S.next ⟨μ0, Seq.ofList K.1⟩ none from by rw [hnil],
    AlterSeq.endState_congr_pub hAeq
      (append_ofList_term ⟨μ0, Seq.nil⟩ Stream'.Seq.terminates_nil K.1)
      (Stream'.Seq.terminates_ofList K.1)]

/-! ### The honest reach-arrival flattening scheduler `flatSched`

Transplant of `expandSched` (`WeakClosure/Scheduler.lean`) to the two-level
`𝒟(sys^w)` composite: the normalizer is the ARRIVAL reach `reachArrM` (reach
at a decision-point config with a NONEMPTY current inner run). The step kernel
is the posterior `reachDepM / reachArrM`; the halt label `⊥` takes the
remaining (halt-or-diverge) mass. -/

/-- **Current-run reach** at prefix `cur` (source `src`, macro-history `Ec`): the
belief mass of the current fresh inner run reaching `cur`, marginalized over the
macro-emission `ω` (`S.next Ec (τ,ω)`) and threaded through `innerWitness`'s path
measure. The arrival analogue of `moveTerm`'s `some`-branch with the trailing
inner move dropped. -/
noncomputable def curReach (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (Ec : AlterSeq (PMF State) Label)
    (cur : {p : AlterSeq State Label // p.trans.Terminates}) : ENNReal :=
  ∑' ω : PMF (PMF State), S.next Ec (some (Silent.τ, ω))
    * (⟨src, (innerWitness sys src ω).toScheduler⟩
        : ProbabilisticExecution sys).probOf cur.1 cur.2

/-- **Config reach** — the honest joint probability the composite reaches the
decision-point config `c` (rooted at macro-history `E`, source `μ0`): the
completed segments' belief path-weight `segWeight` times the current run's reach
`curReach`. -/
noncomputable def reachM (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label) (c : DConfig State Label) : ENNReal :=
  segWeight S μ0 E c.segs
    * curReach S (segSrc μ0 c.segs) (segHist E c.segs) ⟨c.cur, c.curT⟩

open Classical in
/-- **Arrival reach** (the scheduler's normalizer) at observed history `e`: the
total config reach over ARRIVAL configs — consistent with `e` and with a NONEMPTY
current inner run (`c.cur.trans ≠ nil`). The empty history carries no arrival
config, so it is carved to the source mass `μ0 e.init` (the reach of the empty
concrete prefix, `probOf ⟨s0,nil⟩ = μ0 s0`). -/
noncomputable def reachArrM (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) : ENNReal :=
  if e.1.trans = Stream'.Seq.nil then μ0 e.1.init
  else ∑' c : DConfig State Label,
    (if dConsistent e.1 c ∧ c.cur.trans ≠ Stream'.Seq.nil then (1 : ENNReal) else 0)
      * reachM S μ0 E c

open Classical in
/-- **Departure reach** for the step `(l, ν)` (the scheduler's numerator): the
total reach mass at a config consistent with `e` whose current inner run departs
next with move `some (l, ν)`, built
on the junction-divided `segWeight`, so it is consistent with the
arrival reach `reachArrM`/`reachM`; `∑' c consistent, segWeight · moveTerm`. -/
noncomputable def reachDepM (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {e : AlterSeq State Label // e.trans.Terminates})
    (l : Label) (ν : PMF State) : ENNReal :=
  ∑' c : DConfig State Label,
    (if dConsistent e.1 c then (1 : ENNReal) else 0)
      * segWeight S μ0 E c.segs
      * moveTerm S (segSrc μ0 c.segs) (segHist E c.segs) ⟨c.cur, c.curT⟩ (some (l, ν))

/-- **Departure move mass** at the current run: the total next-move mass of the
current inner run reaching `cur`, marginalized over the emission `ω`. Equal to
`∑' (l,ν), moveTerm (some (l,ν))`. -/
noncomputable def depMove (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (Ec : AlterSeq (PMF State) Label)
    (cur : {p : AlterSeq State Label // p.trans.Terminates}) : ENNReal :=
  ∑' ω : PMF (PMF State), S.next Ec (some (Silent.τ, ω))
    * (⟨src, (innerWitness sys src ω).toScheduler⟩
        : ProbabilisticExecution sys).probOf cur.1 cur.2
    * ∑' lν : Label × PMF State, (innerWitness sys src ω).next cur.1 (some lν)

/-- **Halt-at-`cur` reach**: the belief mass that the current inner run reaches
`cur` and then halts (`⊥`), marginalized over the emission `ω`. -/
noncomputable def haltReach (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (Ec : AlterSeq (PMF State) Label)
    (cur : {p : AlterSeq State Label // p.trans.Terminates}) : ENNReal :=
  ∑' ω : PMF (PMF State), S.next Ec (some (Silent.τ, ω))
    * (⟨src, (innerWitness sys src ω).toScheduler⟩
        : ProbabilisticExecution sys).probOf cur.1 cur.2
    * (innerWitness sys src ω).next cur.1 none

/-- **The current-run reach splits** into departures plus the halt reach: at the
current prefix the inner witness is a PMF, so its next-move total is `1`. -/
theorem curReach_split (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (Ec : AlterSeq (PMF State) Label)
    (cur : {p : AlterSeq State Label // p.trans.Terminates}) :
    curReach S src Ec cur = depMove S src Ec cur + haltReach S src Ec cur := by
  rw [depMove, haltReach, curReach, ← ENNReal.tsum_add]
  refine tsum_congr (fun ω => ?_)
  rw [← mul_add,
    show (∑' lν : Label × PMF State, (innerWitness sys src ω).next cur.1 (some lν))
        + (innerWitness sys src ω).next cur.1 none = 1 from by
      rw [add_comm, ← tsumOpt (fun o => (innerWitness sys src ω).next cur.1 o), PMF.tsum_coe],
    mul_one]

open Classical in
/-- Generic config-sum carrier over an arbitrary current-run kernel `k`, mirroring
`dW`; the head-peeling recursion transplants verbatim. -/
private noncomputable def genW
    (k : PMF State → AlterSeq (PMF State) Label →
      {q : AlterSeq State Label // q.trans.Terminates} → ENNReal)
    (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) : ENNReal :=
  ∑' p : List (FlatSeg State Label) × {q : AlterSeq State Label // q.trans.Terminates},
    (if dConsistent e.1 ⟨p.1, p.2.1, p.2.2⟩ then (1 : ENNReal) else 0)
      * segWeight S src E p.1
      * k (segSrc src p.1) (segHist E p.1) p.2

open Classical in
/-- Base case of the generic peel: the no-segment configs contribute `k` at `e`. -/
private theorem genBase
    (k : PMF State → AlterSeq (PMF State) Label →
      {q : AlterSeq State Label // q.trans.Terminates} → ENNReal)
    (S : WeakScheduler (𝒟(sys^w))) (src : PMF State) (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) :
    (∑' cur : {q : AlterSeq State Label // q.trans.Terminates},
      (if dConsistent e.1 (⟨[], cur.1, cur.2⟩ : DConfig State Label) then (1 : ENNReal) else 0)
        * segWeight S src E ([] : List (FlatSeg State Label))
        * k (segSrc src ([] : List (FlatSeg State Label)))
            (segHist E ([] : List (FlatSeg State Label))) cur)
      = k src E e := by
  rw [tsum_eq_single e ?_]
  · rw [if_pos ((dConsistent_nil_iff e e).mpr rfl)]
    simp [segWeight, segSrc, segHist]
  · intro cur hne
    rw [if_neg (fun hc => hne ((dConsistent_nil_iff e cur).mp hc)), zero_mul, zero_mul]

open Classical in
/-- Per-segment reduction of the generic peel. -/
private theorem genSeg
    (k : PMF State → AlterSeq (PMF State) Label →
      {q : AlterSeq State Label // q.trans.Terminates} → ENNReal)
    (S : WeakScheduler (𝒟(sys^w))) (src : PMF State) (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) (seg : FlatSeg State Label) :
    (∑' rest : List (FlatSeg State Label),
      ∑' cur : {q : AlterSeq State Label // q.trans.Terminates},
        (if dConsistent e.1 ⟨seg :: rest, cur.1, cur.2⟩ then (1 : ENNReal) else 0)
          * segWeight S src E (seg :: rest)
          * k (segSrc src (seg :: rest)) (segHist E (seg :: rest)) cur)
      = (if segPre e seg then (1 : ENNReal) else 0)
          * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
              * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
                  / (seg.emit.bind id) (seg.run.endState seg.runT)))
          * genW k S seg.succ (macroExtend E seg.succ) (dResidual e seg) := by
  by_cases hsp : segPre e seg
  · rw [if_pos hsp, one_mul]
    unfold genW
    rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_left]
    refine tsum_congr (fun rest => ?_)
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr (fun cur => ?_)
    simp only [dConsistent_cons_iff, hsp, true_and]
    show (if dConsistent (dResidual e seg).1 ⟨rest, cur.1, cur.2⟩ then (1 : ENNReal) else 0)
        * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
            * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
                / (seg.emit.bind id) (seg.run.endState seg.runT))
            * segWeight S seg.succ (macroExtend E seg.succ) rest)
        * k (segSrc seg.succ rest) (segHist (macroExtend E seg.succ) rest) cur
      = (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
          * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
              / (seg.emit.bind id) (seg.run.endState seg.runT)))
        * ((if dConsistent (dResidual e seg).1 ⟨rest, cur.1, cur.2⟩ then (1 : ENNReal) else 0)
            * segWeight S seg.succ (macroExtend E seg.succ) rest
            * k (segSrc seg.succ rest) (segHist (macroExtend E seg.succ) rest) cur)
    ring
  · rw [if_neg hsp, zero_mul, zero_mul]
    have hzero : ∀ (rest : List (FlatSeg State Label))
        (cur : {q : AlterSeq State Label // q.trans.Terminates}),
        (if dConsistent e.1 ⟨seg :: rest, cur.1, cur.2⟩ then (1 : ENNReal) else 0)
            * segWeight S src E (seg :: rest)
            * k (segSrc src (seg :: rest)) (segHist E (seg :: rest)) cur = 0 := by
      intro rest cur
      rw [if_neg (fun hc => hsp ((dConsistent_cons_iff e seg rest cur.1 cur.2).mp hc).1),
        zero_mul, zero_mul]
    simp only [hzero, tsum_zero]

open Classical in
/-- **The generic peeling recursion.** -/
private theorem genW_peel
    (k : PMF State → AlterSeq (PMF State) Label →
      {q : AlterSeq State Label // q.trans.Terminates} → ENNReal)
    (S : WeakScheduler (𝒟(sys^w))) (src : PMF State) (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) :
    genW k S src E e = k src E e
      + ∑' seg : FlatSeg State Label,
          (if segPre e seg then (1 : ENNReal) else 0)
            * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
                * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
                    / (seg.emit.bind id) (seg.run.endState seg.runT)))
            * genW k S seg.succ (macroExtend E seg.succ) (dResidual e seg) := by
  conv_lhs => rw [genW, ENNReal.tsum_prod', listSplit]
  rw [genBase]
  congr 1
  rw [ENNReal.tsum_prod']
  exact tsum_congr (fun seg => genSeg k S src E e seg)

open Classical in
/-- **Boundary absorption.** The peeled head segments that reconstruct all of `e`
(residual empty) contribute at most the arrival halt-reach at `e`: their macro
successor mass sums against `emit` to `≤ 1`, and each such head's inner run halts
exactly at `e`. -/
private theorem boundaryHalt_le (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) :
    (∑' seg : FlatSeg State Label,
      (if segPre e seg ∧ (dResidual e seg).1.trans = Stream'.Seq.nil then (1 : ENNReal) else 0)
        * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
            * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
                / (seg.emit.bind id) (seg.run.endState seg.runT)))
        * seg.succ (seg.run.endState seg.runT))
      ≤ haltReach S src E e := by
  -- `(x / c) * c ≤ x` unconditionally in `ENNReal` (the junction W2 cancellation).
  have hdmc : ∀ x c : ENNReal, x / c * c ≤ x := by
    intro x c
    rcases eq_or_ne c 0 with hc | hc
    · simp [hc]
    rcases eq_or_ne c ⊤ with hc' | hc'
    · simp [hc', ENNReal.div_top]
    · rw [ENNReal.div_mul_cancel hc hc']
  have hstep : (∑' seg : FlatSeg State Label,
      (if segPre e seg ∧ (dResidual e seg).1.trans = Stream'.Seq.nil then (1 : ENNReal) else 0)
        * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
            * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
                / (seg.emit.bind id) (seg.run.endState seg.runT)))
        * seg.succ (seg.run.endState seg.runT))
      ≤ ∑' seg : FlatSeg State Label,
          (if seg.run = e.1 then (1 : ENNReal) else 0)
            * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
                * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
                    / (seg.emit.bind id) (seg.run.endState seg.runT)))
            * seg.succ (seg.run.endState seg.runT) := by
    refine ENNReal.tsum_le_tsum (fun seg => ?_)
    by_cases hP : segPre e seg ∧ (dResidual e seg).1.trans = Stream'.Seq.nil
    · have hrun : seg.run = e.1 := by
        obtain ⟨⟨hi, happ⟩, hnil⟩ := hP
        have hd : e.1.trans.drop (seg.run.trans.length seg.runT) = Stream'.Seq.nil := hnil
        rw [hd, Stream'.Seq.append_nil] at happ
        calc seg.run = ⟨seg.run.init, seg.run.trans⟩ := rfl
          _ = ⟨e.1.init, e.1.trans⟩ := by rw [hi, happ]
          _ = e.1 := rfl
      rw [if_pos hP, if_pos hrun]
    · rw [if_neg hP, zero_mul, zero_mul]
      positivity
  refine hstep.trans ?_
  have hreindex : (∑' seg : FlatSeg State Label,
      (if seg.run = e.1 then (1 : ENNReal) else 0)
        * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
            * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
                / (seg.emit.bind id) (seg.run.endState seg.runT)))
        * seg.succ (seg.run.endState seg.runT))
      = ∑' t : PMF (PMF State) × PMF State × {q : AlterSeq State Label // q.trans.Terminates},
          (if t.2.2.1 = e.1 then (1 : ENNReal) else 0)
            * (S.next E (some (Silent.τ, t.1)) * t.1 t.2.1
                * ((innerWitness sys src t.1).haltMass src t.2.2
                    / (t.1.bind id) (t.2.2.1.endState t.2.2.2)))
            * t.2.1 (t.2.2.1.endState t.2.2.2) :=
    Equiv.tsum_eq flatSegEquiv (fun t => (if t.2.2.1 = e.1 then (1 : ENNReal) else 0)
      * (S.next E (some (Silent.τ, t.1)) * t.1 t.2.1
          * ((innerWitness sys src t.1).haltMass src t.2.2
              / (t.1.bind id) (t.2.2.1.endState t.2.2.2)))
      * t.2.1 (t.2.2.1.endState t.2.2.2))
  rw [hreindex, ENNReal.tsum_prod']
  have hunfold : haltReach S src E e
      = ∑' emit : PMF (PMF State), S.next E (some (Silent.τ, emit))
          * (innerWitness sys src emit).haltMass src e := by
    rw [haltReach]
    refine tsum_congr (fun ω => ?_)
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [mul_assoc]
  rw [hunfold]
  refine ENNReal.tsum_le_tsum (fun emit => ?_)
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  calc (∑' run : {q : AlterSeq State Label // q.trans.Terminates}, ∑' succ : PMF State,
          (if run.1 = e.1 then (1 : ENNReal) else 0)
            * (S.next E (some (Silent.τ, emit)) * emit succ
                * ((innerWitness sys src emit).haltMass src run
                    / (emit.bind id) (run.1.endState run.2)))
            * succ (run.1.endState run.2))
      = ∑' run : {q : AlterSeq State Label // q.trans.Terminates},
          (if run.1 = e.1 then (1 : ENNReal) else 0) * S.next E (some (Silent.τ, emit))
            * ((innerWitness sys src emit).haltMass src run
                / (emit.bind id) (run.1.endState run.2))
            * (emit.bind id) (run.1.endState run.2) := by
        refine tsum_congr (fun run => ?_)
        rw [show (∑' succ : PMF State,
              (if run.1 = e.1 then (1 : ENNReal) else 0)
                * (S.next E (some (Silent.τ, emit)) * emit succ
                    * ((innerWitness sys src emit).haltMass src run
                        / (emit.bind id) (run.1.endState run.2)))
                * succ (run.1.endState run.2))
            = ((if run.1 = e.1 then (1 : ENNReal) else 0) * S.next E (some (Silent.τ, emit))
                  * ((innerWitness sys src emit).haltMass src run
                      / (emit.bind id) (run.1.endState run.2)))
                * ∑' succ : PMF State, emit succ * succ (run.1.endState run.2) from by
          rw [← ENNReal.tsum_mul_left]; exact tsum_congr (fun succ => by ring)]
        rw [PMF.bind_apply]
        simp only [id_eq]
    _ ≤ ∑' run : {q : AlterSeq State Label // q.trans.Terminates},
          (if run.1 = e.1 then (1 : ENNReal) else 0) * S.next E (some (Silent.τ, emit))
            * (innerWitness sys src emit).haltMass src run := by
        refine ENNReal.tsum_le_tsum (fun run => ?_)
        rw [mul_assoc]
        exact mul_le_mul_left' (hdmc _ _) _
    _ = S.next E (some (Silent.τ, emit)) * (innerWitness sys src emit).haltMass src e := by
        rw [tsum_eq_single e (fun run hrun => by
          rw [if_neg (fun hc => hrun (Subtype.ext hc)), zero_mul, zero_mul]), if_pos rfl,
          one_mul]

/-- The macro scheduler's proper-move mass is a sub-probability. -/
private theorem macroSome_le_one (S : WeakScheduler (𝒟(sys^w)))
    (Ec : AlterSeq (PMF State) Label) :
    (∑' ω : PMF (PMF State), S.next Ec (some (Silent.τ, ω))) ≤ 1 := by
  calc (∑' ω : PMF (PMF State), S.next Ec (some (Silent.τ, ω)))
      ≤ ∑' p : Label × PMF (PMF State), S.next Ec (some p) :=
        ENNReal.tsum_comp_le_tsum_of_injective
          (fun a b h => congrArg Prod.snd h) (fun p => S.next Ec (some p))
    _ ≤ ∑' o, S.next Ec o := by rw [tsumOpt]; exact le_add_self
    _ = 1 := PMF.tsum_coe _

/-- **`depMove` is bounded by the source mass at the current prefix's start.** The
inner witnesses' proper-move totals and the macro `τ`-mass are sub-probabilities,
and `probOf ≤ init`. Bounds the fresh-reset (empty-current) departures. -/
private theorem depMove_le_init (S : WeakScheduler (𝒟(sys^w))) (s : PMF State)
    (Ec : AlterSeq (PMF State) Label)
    (cur : {q : AlterSeq State Label // q.trans.Terminates}) :
    depMove S s Ec cur ≤ s cur.1.init := by
  rw [depMove]
  have hbound : ∀ ω : PMF (PMF State),
      S.next Ec (some (Silent.τ, ω))
          * (⟨s, (innerWitness sys s ω).toScheduler⟩ : ProbabilisticExecution sys).probOf cur.1 cur.2
          * ∑' lν : Label × PMF State, (innerWitness sys s ω).next cur.1 (some lν)
        ≤ S.next Ec (some (Silent.τ, ω)) * s cur.1.init := by
    intro ω
    have htail : (∑' lν : Label × PMF State, (innerWitness sys s ω).next cur.1 (some lν)) ≤ 1 := by
      calc (∑' lν : Label × PMF State, (innerWitness sys s ω).next cur.1 (some lν))
          ≤ (innerWitness sys s ω).next cur.1 none
              + ∑' lν : Label × PMF State, (innerWitness sys s ω).next cur.1 (some lν) := le_add_self
        _ = ∑' o, (innerWitness sys s ω).next cur.1 o :=
            (tsumOpt (fun o => (innerWitness sys s ω).next cur.1 o)).symm
        _ = 1 := PMF.tsum_coe _
    calc S.next Ec (some (Silent.τ, ω))
            * (⟨s, (innerWitness sys s ω).toScheduler⟩ : ProbabilisticExecution sys).probOf cur.1 cur.2
            * ∑' lν : Label × PMF State, (innerWitness sys s ω).next cur.1 (some lν)
        ≤ S.next Ec (some (Silent.τ, ω))
            * (⟨s, (innerWitness sys s ω).toScheduler⟩ : ProbabilisticExecution sys).probOf cur.1 cur.2
            * 1 := by gcongr
      _ = S.next Ec (some (Silent.τ, ω))
            * (⟨s, (innerWitness sys s ω).toScheduler⟩
                : ProbabilisticExecution sys).probOf cur.1 cur.2 := mul_one _
      _ ≤ S.next Ec (some (Silent.τ, ω)) * s cur.1.init := by
          gcongr
          exact ProbabilisticExecution.probOf_le_init _ _ _
  calc (∑' ω : PMF (PMF State),
          S.next Ec (some (Silent.τ, ω))
            * (⟨s, (innerWitness sys s ω).toScheduler⟩ : ProbabilisticExecution sys).probOf cur.1 cur.2
            * ∑' lν : Label × PMF State, (innerWitness sys s ω).next cur.1 (some lν))
      ≤ ∑' ω : PMF (PMF State), S.next Ec (some (Silent.τ, ω)) * s cur.1.init :=
        ENNReal.tsum_le_tsum hbound
    _ = (∑' ω : PMF (PMF State), S.next Ec (some (Silent.τ, ω))) * s cur.1.init := by
        rw [ENNReal.tsum_mul_right]
    _ ≤ 1 * s cur.1.init := by gcongr; exact macroSome_le_one S Ec
    _ = s cur.1.init := one_mul _

open Classical in
/-- **The seg-count-truncated peel carrier.** `genWd k d` sums the configs
with at most `d` completed segments (empty stall segments included). Its
supremum over `d` recovers `genW` (`genW_eq_iSup_genWd`), and it satisfies the
truncated peel recursion (`genWd_zero`/`genWd_succ`) that powers the
resolvent bounds: with the widened `segPre`, empty heads recurse at the SAME
observed history, so the plain `Nat` induction on the budget `d` replaces the
induction on the observed length. -/
private noncomputable def genWd
    (k : PMF State → AlterSeq (PMF State) Label →
      {q : AlterSeq State Label // q.trans.Terminates} → ENNReal)
    (S : WeakScheduler (𝒟(sys^w))) (d : ℕ) (src : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) : ENNReal :=
  ∑' p : List (FlatSeg State Label) × {q : AlterSeq State Label // q.trans.Terminates},
    (if dConsistent e.1 ⟨p.1, p.2.1, p.2.2⟩ ∧ p.1.length ≤ d then (1 : ENNReal) else 0)
      * segWeight S src E p.1
      * k (segSrc src p.1) (segHist E p.1) p.2

open Classical in
/-- The truncations exhaust `genW`: pointwise the guard is monotone in `d` and
eventually agrees with the unrestricted one. -/
private theorem genW_eq_iSup_genWd
    (k : PMF State → AlterSeq (PMF State) Label →
      {q : AlterSeq State Label // q.trans.Terminates} → ENNReal)
    (S : WeakScheduler (𝒟(sys^w))) (src : PMF State) (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) :
    genW k S src E e = ⨆ d : ℕ, genWd k S d src E e := by
  have hmono : ∀ p : List (FlatSeg State Label) ×
      {q : AlterSeq State Label // q.trans.Terminates},
      Monotone (fun d : ℕ =>
        (if dConsistent e.1 ⟨p.1, p.2.1, p.2.2⟩ ∧ p.1.length ≤ d then (1 : ENNReal) else 0)
          * segWeight S src E p.1 * k (segSrc src p.1) (segHist E p.1) p.2) := by
    intro p d d' hdd'
    refine mul_le_mul_right' (mul_le_mul_right' ?_ _) _
    by_cases hg : dConsistent e.1 ⟨p.1, p.2.1, p.2.2⟩ ∧ p.1.length ≤ d
    · rw [if_pos hg, if_pos ⟨hg.1, hg.2.trans hdd'⟩]
    · rw [if_neg hg]; exact zero_le'
  rw [genW, show (⨆ d : ℕ, genWd k S d src E e)
      = ∑' p : List (FlatSeg State Label) × {q : AlterSeq State Label // q.trans.Terminates},
          ⨆ d : ℕ,
            (if dConsistent e.1 ⟨p.1, p.2.1, p.2.2⟩ ∧ p.1.length ≤ d then (1 : ENNReal) else 0)
              * segWeight S src E p.1 * k (segSrc src p.1) (segHist E p.1) p.2 from
    (tsum_iSup_of_monotone _ hmono).symm]
  refine tsum_congr (fun p => ?_)
  refine le_antisymm ?_ (iSup_le (fun d => ?_))
  · refine le_trans (le_of_eq ?_) (le_iSup _ p.1.length)
    by_cases hc : dConsistent e.1 ⟨p.1, p.2.1, p.2.2⟩
    · rw [if_pos hc, if_pos ⟨hc, le_rfl⟩]
    · rw [if_neg hc, if_neg (fun h => hc h.1)]
  · refine mul_le_mul_right' (mul_le_mul_right' ?_ _) _
    by_cases hg : dConsistent e.1 ⟨p.1, p.2.1, p.2.2⟩ ∧ p.1.length ≤ d
    · rw [if_pos hg, if_pos hg.1]
    · rw [if_neg hg]; exact zero_le'

open Classical in
/-- Budget `0`: only the no-segment configs contribute, i.e. the base kernel. -/
private theorem genWd_zero
    (k : PMF State → AlterSeq (PMF State) Label →
      {q : AlterSeq State Label // q.trans.Terminates} → ENNReal)
    (S : WeakScheduler (𝒟(sys^w))) (src : PMF State) (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) :
    genWd k S 0 src E e = k src E e := by
  rw [genWd, ENNReal.tsum_prod', listSplit]
  have h2 : (∑' q : FlatSeg State Label × List (FlatSeg State Label),
      ∑' cur : {q : AlterSeq State Label // q.trans.Terminates},
        (if dConsistent e.1 ⟨q.1 :: q.2, cur.1, cur.2⟩ ∧ (q.1 :: q.2).length ≤ 0
            then (1 : ENNReal) else 0)
          * segWeight S src E (q.1 :: q.2)
          * k (segSrc src (q.1 :: q.2)) (segHist E (q.1 :: q.2)) cur) = 0 := by
    refine ENNReal.tsum_eq_zero.mpr (fun q => ENNReal.tsum_eq_zero.mpr (fun cur => ?_))
    rw [if_neg (fun h => by simpa using h.2), zero_mul, zero_mul]
  rw [h2, add_zero]
  rw [tsum_eq_single e ?_]
  · rw [if_pos ⟨(dConsistent_nil_iff e e).mpr rfl, by simp⟩]
    simp [segWeight, segSrc, segHist]
  · intro cur hne
    rw [if_neg (fun hc => hne ((dConsistent_nil_iff e cur).mp hc.1)), zero_mul, zero_mul]

open Classical in
/-- Budget `d + 1`: the truncated peel — base kernel plus one (possibly empty)
head segment, the tail truncated at budget `d`. -/
private theorem genWd_succ
    (k : PMF State → AlterSeq (PMF State) Label →
      {q : AlterSeq State Label // q.trans.Terminates} → ENNReal)
    (S : WeakScheduler (𝒟(sys^w))) (d : ℕ) (src : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) :
    genWd k S (d + 1) src E e = k src E e
      + ∑' seg : FlatSeg State Label,
          (if segPre e seg then (1 : ENNReal) else 0)
            * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
                * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
                    / (seg.emit.bind id) (seg.run.endState seg.runT)))
            * genWd k S d seg.succ (macroExtend E seg.succ) (dResidual e seg) := by
  conv_lhs => rw [genWd, ENNReal.tsum_prod', listSplit]
  congr 1
  · rw [tsum_eq_single e ?_]
    · rw [if_pos ⟨(dConsistent_nil_iff e e).mpr rfl, by simp⟩]
      simp [segWeight, segSrc, segHist]
    · intro cur hne
      rw [if_neg (fun hc => hne ((dConsistent_nil_iff e cur).mp hc.1)), zero_mul, zero_mul]
  rw [ENNReal.tsum_prod']
  refine tsum_congr (fun seg => ?_)
  by_cases hsp : segPre e seg
  · rw [if_pos hsp, one_mul]
    rw [genWd, ENNReal.tsum_prod', ← ENNReal.tsum_mul_left]
    refine tsum_congr (fun rest => ?_)
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr (fun cur => ?_)
    simp only [dConsistent_cons_iff, hsp, true_and, List.length_cons,
      Nat.add_le_add_iff_right]
    show (if dConsistent (dResidual e seg).1 ⟨rest, cur.1, cur.2⟩ ∧ rest.length ≤ d
          then (1 : ENNReal) else 0)
        * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
            * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
                / (seg.emit.bind id) (seg.run.endState seg.runT))
            * segWeight S seg.succ (macroExtend E seg.succ) rest)
        * k (segSrc seg.succ rest) (segHist (macroExtend E seg.succ) rest) cur
      = (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
          * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
              / (seg.emit.bind id) (seg.run.endState seg.runT)))
        * ((if dConsistent (dResidual e seg).1 ⟨rest, cur.1, cur.2⟩ ∧ rest.length ≤ d
              then (1 : ENNReal) else 0)
            * segWeight S seg.succ (macroExtend E seg.succ) rest
            * k (segSrc seg.succ rest) (segHist (macroExtend E seg.succ) rest) cur)
    ring
  · rw [if_neg hsp, zero_mul, zero_mul]
    refine ENNReal.tsum_eq_zero.mpr (fun rest => ENNReal.tsum_eq_zero.mpr (fun cur => ?_))
    rw [if_neg (fun hc => hsp ((dConsistent_cons_iff e seg rest cur.1 cur.2).mp hc.1).1),
      zero_mul, zero_mul]

open Classical in
/-- **The nil-history resolvent departure bound.** At an empty
observed history every peel is a stall peel (empty run at `e.init`, residual
again empty), so the truncated departure carrier is the finite stall resolvent;
it is bounded by the source mass at the observed state. Induction on the budget:
the stall boundary is absorbed by `boundaryHalt_le` into `haltReach`, and
`depMove + haltReach = curReach ≤ src(init)`. -/
private theorem genWd_dep_nil (S : WeakScheduler (𝒟(sys^w))) :
    ∀ (d : ℕ) (src : PMF State) (E : AlterSeq (PMF State) Label)
      (e : {q : AlterSeq State Label // q.trans.Terminates}),
      e.1.trans = Stream'.Seq.nil →
      genWd (fun s Ec c => depMove S s Ec c) S d src E e ≤ src e.1.init := by
  have hcur : ∀ (src : PMF State) (E : AlterSeq (PMF State) Label)
      (e : {q : AlterSeq State Label // q.trans.Terminates}),
      curReach S src E e ≤ src e.1.init := by
    intro src E e
    calc curReach S src E e
        ≤ ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω)) * src e.1.init :=
          ENNReal.tsum_le_tsum (fun ω =>
            mul_le_mul_left' (ProbabilisticExecution.probOf_le_init _ _ _) _)
      _ = (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))) * src e.1.init := by
          rw [ENNReal.tsum_mul_right]
      _ ≤ 1 * src e.1.init := by gcongr; exact macroSome_le_one S E
      _ = src e.1.init := one_mul _
  intro d
  induction d with
  | zero =>
    intro src E e h
    rw [genWd_zero]
    exact depMove_le_init S src E e
  | succ d IH =>
    intro src E e h
    rw [genWd_succ]
    have hres : ∀ seg : FlatSeg State Label, segPre e seg →
        (dResidual e seg).1.trans = Stream'.Seq.nil := by
      rintro seg ⟨hinit, happ⟩
      have hT : (seg.run.trans.append
          (e.1.trans.drop (seg.run.trans.length seg.runT))).Terminates := by
        rw [happ]; exact e.2
      have hsum : seg.run.trans.length seg.runT
          + (e.1.trans.drop (seg.run.trans.length seg.runT)).length
              (WeakScheduler.drop_terminates e.2 _) = 0 := by
        rw [← length_append_seq seg.run.trans _ seg.runT
              (WeakScheduler.drop_terminates e.2 _) hT,
          length_congr _ e.1.trans hT e.2 happ, Stream'.Seq.length_eq_zero.mpr h]
      have hlen0 : (e.1.trans.drop (seg.run.trans.length seg.runT)).length
          (WeakScheduler.drop_terminates e.2 _) = 0 := by omega
      exact Stream'.Seq.length_eq_zero.mp hlen0
    have hbdy : (∑' seg : FlatSeg State Label,
        (if segPre e seg then (1 : ENNReal) else 0)
          * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
              * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
                  / (seg.emit.bind id) (seg.run.endState seg.runT)))
          * genWd (fun s Ec c => depMove S s Ec c) S d seg.succ (macroExtend E seg.succ)
              (dResidual e seg))
        ≤ haltReach S src E e := by
      refine le_trans ?_ (boundaryHalt_le S src E e)
      refine ENNReal.tsum_le_tsum (fun seg => ?_)
      by_cases hsp : segPre e seg
      · rw [if_pos hsp, if_pos ⟨hsp, hres seg hsp⟩]
        gcongr
        exact IH seg.succ (macroExtend E seg.succ) (dResidual e seg) (hres seg hsp)
      · rw [if_neg hsp, if_neg (fun hc => hsp hc.1)]
        simp
    calc depMove S src E e
          + ∑' seg : FlatSeg State Label,
            (if segPre e seg then (1 : ENNReal) else 0)
              * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
                  * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
                      / (seg.emit.bind id) (seg.run.endState seg.runT)))
              * genWd (fun s Ec c => depMove S s Ec c) S d seg.succ (macroExtend E seg.succ)
                  (dResidual e seg)
        ≤ depMove S src E e + haltReach S src E e := add_le_add le_rfl hbdy
      _ = curReach S src E e := (curReach_split S src E e).symm
      _ ≤ src e.1.init := hcur src E e

/-- The nil-history resolvent departure bound, `genW` form. -/
private theorem genW_dep_nil (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates})
    (h : e.1.trans = Stream'.Seq.nil) :
    genW (fun s Ec c => depMove S s Ec c) S src E e ≤ src e.1.init := by
  rw [genW_eq_iSup_genWd]
  exact iSup_le (fun d => genWd_dep_nil S d src E e h)

open Classical in
/-- **Departures ⊆ arrivals (config-sum form, truncated).** For a nonempty
observed history the budget-`d` departure config-sum is at most the (full)
arrival config-sum. Plain induction on the budget — empty (stall) heads
recurse at the same history via the inner IH, nonempty heads with empty residual
fall to LEMMA A + `boundaryHalt_le`, the rest to the IH at the residual. -/
private theorem genDepD_le_genArr (S : WeakScheduler (𝒟(sys^w))) :
    ∀ (d : ℕ) (src : PMF State) (E : AlterSeq (PMF State) Label)
      (e : {q : AlterSeq State Label // q.trans.Terminates}),
      e.1.trans ≠ Stream'.Seq.nil →
      genWd (fun s Ec c => depMove S s Ec c) S d src E e
        ≤ genW (fun s Ec c => if c.1.trans ≠ Stream'.Seq.nil then curReach S s Ec c else 0)
            S src E e := by
  intro d
  induction d with
  | zero =>
    intro src E e hne
    rw [genWd_zero, genW_peel]
    refine le_trans ?_ le_self_add
    show depMove S src E e ≤ if e.1.trans ≠ Stream'.Seq.nil then curReach S src E e else 0
    rw [if_pos hne, curReach_split S src E e]
    exact le_self_add
  | succ d IH =>
    intro src E e hne
    rw [genWd_succ,
      genW_peel (fun s Ec c => if c.1.trans ≠ Stream'.Seq.nil then curReach S s Ec c else 0)
        S src E e]
    rw [if_pos hne, curReach_split S src E e, add_assoc]
    refine add_le_add le_rfl ?_
    calc (∑' seg : FlatSeg State Label,
            (if segPre e seg then (1 : ENNReal) else 0)
              * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
                  * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
                      / (seg.emit.bind id) (seg.run.endState seg.runT)))
              * genWd (fun s Ec c => depMove S s Ec c) S d seg.succ (macroExtend E seg.succ)
                  (dResidual e seg))
        ≤ ∑' seg : FlatSeg State Label,
            ((if segPre e seg then (1 : ENNReal) else 0)
                * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
                    * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
                        / (seg.emit.bind id) (seg.run.endState seg.runT)))
                * genW (fun s Ec c => if c.1.trans ≠ Stream'.Seq.nil then curReach S s Ec c else 0)
                    S seg.succ (macroExtend E seg.succ) (dResidual e seg)
              + (if segPre e seg ∧ (dResidual e seg).1.trans = Stream'.Seq.nil
                    then (1 : ENNReal) else 0)
                  * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
                      * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
                          / (seg.emit.bind id) (seg.run.endState seg.runT)))
                  * seg.succ (seg.run.endState seg.runT)) := by
          refine ENNReal.tsum_le_tsum (fun seg => ?_)
          by_cases hsp : segPre e seg
          · simp only [if_pos hsp, one_mul]
            by_cases hrn : (dResidual e seg).1.trans = Stream'.Seq.nil
            · rw [if_pos ⟨hsp, hrn⟩, one_mul]
              refine le_trans ?_ le_add_self
              gcongr
              exact genWd_dep_nil S d seg.succ (macroExtend E seg.succ) (dResidual e seg) hrn
            · rw [if_neg (fun h => hrn h.2), zero_mul, zero_mul, add_zero]
              gcongr
              exact IH seg.succ (macroExtend E seg.succ) (dResidual e seg) hrn
          · rw [if_neg hsp, zero_mul, zero_mul]
            positivity
      _ = (∑' seg : FlatSeg State Label,
            (if segPre e seg then (1 : ENNReal) else 0)
              * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
                  * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
                      / (seg.emit.bind id) (seg.run.endState seg.runT)))
              * genW (fun s Ec c => if c.1.trans ≠ Stream'.Seq.nil then curReach S s Ec c else 0)
                  S seg.succ (macroExtend E seg.succ) (dResidual e seg))
          + ∑' seg : FlatSeg State Label,
            (if segPre e seg ∧ (dResidual e seg).1.trans = Stream'.Seq.nil then (1 : ENNReal) else 0)
              * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
                  * ((innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
                      / (seg.emit.bind id) (seg.run.endState seg.runT)))
              * seg.succ (seg.run.endState seg.runT) := ENNReal.tsum_add
      _ ≤ _ := by
          rw [add_comm (haltReach S src E e)]
          gcongr
          exact boundaryHalt_le S src E e

open Classical in
/-- **Departures ⊆ arrivals (config-sum form).** Via the truncation
supremum. -/
private theorem genDep_le_genArr (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates})
    (hne : e.1.trans ≠ Stream'.Seq.nil) :
    genW (fun s Ec c => depMove S s Ec c) S src E e
      ≤ genW (fun s Ec c => if c.1.trans ≠ Stream'.Seq.nil then curReach S s Ec c else 0)
          S src E e := by
  rw [genW_eq_iSup_genWd]
  exact iSup_le (fun d => genDepD_le_genArr S d src E e hne)

/-- The total proper-move mass of the current run is `depMove`. -/
private theorem moveSum_eq_depMove (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (Ec : AlterSeq (PMF State) Label)
    (cur : {q : AlterSeq State Label // q.trans.Terminates}) :
    (∑' p : Label × PMF State, moveTerm S src Ec cur (some p)) = depMove S src Ec cur := by
  have h1 : (∑' p : Label × PMF State, moveTerm S src Ec cur (some p))
      = ∑' p : Label × PMF State, ∑' ω : PMF (PMF State),
          S.next Ec (some (Silent.τ, ω))
            * (⟨src, (innerWitness sys src ω).toScheduler⟩
                : ProbabilisticExecution sys).probOf cur.1 cur.2
            * (innerWitness sys src ω).next cur.1 (some p) :=
    tsum_congr (fun p => rfl)
  rw [h1, ENNReal.tsum_comm, depMove]
  refine tsum_congr (fun ω => ?_)
  rw [ENNReal.tsum_mul_left]

open Classical in
/-- The current-run reach guarded by a nonempty current prefix (the arrival kernel). -/
private noncomputable def curReachG (S : WeakScheduler (𝒟(sys^w))) (s : PMF State)
    (Ec : AlterSeq (PMF State) Label)
    (c : {q : AlterSeq State Label // q.trans.Terminates}) : ENNReal :=
  if c.1.trans ≠ Stream'.Seq.nil then curReach S s Ec c else 0

open Classical in
/-- `genW` reindexed over the `DConfig` carrier. -/
private theorem genW_eq_dconfig
    (k : PMF State → AlterSeq (PMF State) Label →
      {q : AlterSeq State Label // q.trans.Terminates} → ENNReal)
    (S : WeakScheduler (𝒟(sys^w))) (src : PMF State) (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) :
    genW k S src E e = ∑' c : DConfig State Label,
      (if dConsistent e.1 c then (1 : ENNReal) else 0) * segWeight S src E c.segs
        * k (segSrc src c.segs) (segHist E c.segs) ⟨c.cur, c.curT⟩ := by
  rw [genW]
  exact (Equiv.tsum_eq dcE _).symm

open Classical in
/-- **Departures ⊆ arrivals (kernel form).** The total departure reach is at most
the arrival reach, so the halt label gets a well-defined remainder. -/
theorem reachDepM_sum_le (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) :
    (∑' p : Label × PMF State, reachDepM S μ0 E e p.1 p.2) ≤ reachArrM S μ0 E e := by
  have hdep : (∑' p : Label × PMF State, reachDepM S μ0 E e p.1 p.2)
      = genW (depMove S) S μ0 E e := by
    rw [genW_eq_dconfig]
    simp_rw [reachDepM]
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun c => ?_)
    rw [ENNReal.tsum_mul_left, moveSum_eq_depMove]
  rw [hdep]
  by_cases hnil : e.1.trans = Stream'.Seq.nil
  · rw [reachArrM, if_pos hnil]
    exact genW_dep_nil S μ0 E e hnil
  · rw [reachArrM, if_neg hnil]
    refine (genDep_le_genArr S μ0 E e hnil).trans ?_
    show genW (curReachG S) S μ0 E e ≤ _
    rw [genW_eq_dconfig]
    refine ENNReal.tsum_le_tsum (fun c => ?_)
    simp only [curReachG]
    by_cases hdc : dConsistent e.1 c
    · by_cases hcnil : c.cur.trans = Stream'.Seq.nil
      · simp [hdc, hcnil]
      · simp [hdc, hcnil, reachM]
    · simp [hdc]


end PLTS
