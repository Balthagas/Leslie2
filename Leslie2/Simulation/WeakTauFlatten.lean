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

/-- Append a single transition `(l, s')` at the end of a terminating prefix. -/
private noncomputable def snocT (cur : {q : AlterSeq State Label // q.trans.Terminates})
    (l : Label) (s' : State) : {q : AlterSeq State Label // q.trans.Terminates} :=
  ⟨⟨cur.1.init, cur.1.trans.append (Stream'.Seq.cons (l, s') Stream'.Seq.nil)⟩,
    ⟨_, Stream'.Seq.terminatedAt_append_find cur.2
      (Nat.find_spec (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil))⟩⟩

/-- The current prefix of a `snocT` is nonempty (it ends in the appended step). -/
private theorem snocT_trans_ne_nil (cur : {q : AlterSeq State Label // q.trans.Terminates})
    (l : Label) (s' : State) : (snocT cur l s').1.trans ≠ Stream'.Seq.nil := by
  show cur.1.trans.append (Stream'.Seq.cons (l, s') Stream'.Seq.nil) ≠ Stream'.Seq.nil
  generalize cur.1.trans = t
  apply Stream'.Seq.recOn t
  · rw [Stream'.Seq.nil_append]; exact Stream'.Seq.cons_ne_nil
  · intro x t'; rw [Stream'.Seq.cons_append]; exact Stream'.Seq.cons_ne_nil

/-- `segTrans` distributes over a right `append`: the completed segments'
concatenation is prepended, so appending after the current prefix commutes. -/
private theorem segTrans_append (segs : List (FlatSeg State Label))
    (X Y : Stream'.Seq (Label × State)) :
    segTrans segs (X.append Y) = (segTrans segs X).append Y := by
  induction segs with
  | nil => rfl
  | cons seg rest ih =>
    show seg.run.trans.append (segTrans rest (X.append Y))
      = (seg.run.trans.append (segTrans rest X)).append Y
    rw [ih, Stream'.Seq.append_assoc]

/-- **Landing identity (pointwise).** The current-run reach at a prefix extended
by `(l, s')` equals the departure move mass at `(l, ν)` mixed against the drawn
`ν`'s mass at `s'`. Uses `probOf_append_singleton` inside the inner witness. -/
private theorem curReach_snoc (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (Ec : AlterSeq (PMF State) Label)
    (cur : {q : AlterSeq State Label // q.trans.Terminates}) (l : Label) (s' : State) :
    curReach S src Ec (snocT cur l s')
      = ∑' ν : PMF State, moveTerm S src Ec cur (some (l, ν)) * ν s' := by
  have hkey : ∀ ω : PMF (PMF State),
      (⟨src, (innerWitness sys src ω).toScheduler⟩ : ProbabilisticExecution sys).probOf
          (snocT cur l s').1 (snocT cur l s').2
        = (⟨src, (innerWitness sys src ω).toScheduler⟩ : ProbabilisticExecution sys).probOf
              cur.1 cur.2
          * ∑' ν : PMF State, (innerWitness sys src ω).next cur.1 (some (l, ν)) * ν s' := by
    intro ω
    rw [ProbabilisticExecution.probOf_congr _ (snocT cur l s').1
        ⟨cur.1.init, cur.1.trans.append (Stream'.Seq.cons (l, s') Stream'.Seq.nil)⟩ rfl
        (snocT cur l s').2 (snocT cur l s').2,
      ProbabilisticExecution.probOf_append_singleton _ cur.1.init cur.1.trans cur.2 (l, s')
        (snocT cur l s').2]
    rfl
  have hL : curReach S src Ec (snocT cur l s')
      = ∑' ω : PMF (PMF State), S.next Ec (some (Silent.τ, ω))
          * ((⟨src, (innerWitness sys src ω).toScheduler⟩ : ProbabilisticExecution sys).probOf
                cur.1 cur.2
            * ∑' ν : PMF State, (innerWitness sys src ω).next cur.1 (some (l, ν)) * ν s') := by
    rw [curReach]; exact tsum_congr (fun ω => by rw [hkey ω])
  rw [hL]
  have e1 : ∀ ν : PMF State, moveTerm S src Ec cur (some (l, ν)) * ν s'
      = ∑' ω : PMF (PMF State), S.next Ec (some (Silent.τ, ω))
          * (⟨src, (innerWitness sys src ω).toScheduler⟩ : ProbabilisticExecution sys).probOf
              cur.1 cur.2
          * (innerWitness sys src ω).next cur.1 (some (l, ν)) * ν s' := by
    intro ν; rw [moveTerm, ENNReal.tsum_mul_right]
  rw [tsum_congr e1, ENNReal.tsum_comm]
  refine tsum_congr (fun ω => ?_)
  rw [← mul_assoc, ← ENNReal.tsum_mul_left]
  refine tsum_congr (fun ν => ?_)
  exact (mul_assoc _ _ _).symm

/-- `segTrans` of a terminating current prefix (all segment runs terminate) again
terminates. -/
private theorem segTrans_terminates (segs : List (FlatSeg State Label))
    (c : Stream'.Seq (Label × State)) (hc : c.Terminates) :
    (segTrans segs c).Terminates := by
  induction segs with
  | nil => exact hc
  | cons seg rest ih =>
    exact ⟨_, Stream'.Seq.terminatedAt_append_find seg.runT (Nat.find_spec ih)⟩

/-- **Consistency is preserved by a shared final `snoc`.** A config with current
prefix extended by `(l, s')` is consistent with the `snoc`-extended history iff the
original config is consistent with the original history (append cancels via
`segTrans_append` + `append_singleton_inj_left`). -/
private theorem dConsistent_snoc_iff (e : {q : AlterSeq State Label // q.trans.Terminates})
    (l : Label) (s' : State) (segs : List (FlatSeg State Label))
    (cur : {q : AlterSeq State Label // q.trans.Terminates}) :
    dConsistent (snocT e l s').1 ⟨segs, (snocT cur l s').1, (snocT cur l s').2⟩
      ↔ dConsistent e.1 ⟨segs, cur.1, cur.2⟩ := by
  have hAterm : (segTrans segs cur.1.trans).Terminates :=
    segTrans_terminates segs cur.1.trans cur.2
  unfold dConsistent
  constructor
  · rintro ⟨h2, h3⟩
    refine ⟨?_, h3⟩
    rw [show (⟨segs, (snocT cur l s').1, (snocT cur l s').2⟩ : DConfig State Label).cur.trans
        = cur.1.trans.append (Stream'.Seq.cons (l, s') Stream'.Seq.nil) from rfl,
      segTrans_append] at h2
    exact Stream'.Seq.append_singleton_inj_left _ _ hAterm e.2 (l, s') (l, s') h2
  · rintro ⟨h2, h3⟩
    refine ⟨?_, h3⟩
    show segTrans segs (cur.1.trans.append (Stream'.Seq.cons (l, s') Stream'.Seq.nil))
      = e.1.trans.append (Stream'.Seq.cons (l, s') Stream'.Seq.nil)
    rw [segTrans_append, h2]

open Classical in
/-- For a nonempty observed history, `reachArrM` is the `genW`-carrier of the
current-run kernel guarded by a nonempty current prefix. -/
private theorem reachArrM_of_ne_nil (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) (h : e.1.trans ≠ Stream'.Seq.nil) :
    reachArrM S μ0 E e = genW (curReachG S) S μ0 E e := by
  rw [reachArrM, if_neg h, genW_eq_dconfig]
  refine tsum_congr (fun c => ?_)
  simp only [curReachG]
  by_cases hdc : dConsistent e.1 c
  · by_cases hcnil : c.cur.trans = Stream'.Seq.nil
    · simp [hdc, hcnil]
    · simp [hdc, hcnil, reachM]
  · simp [hdc]

open Classical in
/-- The `genW`-carrier of the landing kernel is the departure reach mixed against
the drawn `ν`. -/
private theorem genW_landKer (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) (l : Label) (s' : State) :
    genW (fun (s : PMF State) (Ec : AlterSeq (PMF State) Label)
        (c : {q : AlterSeq State Label // q.trans.Terminates}) =>
        ∑' ν : PMF State, moveTerm S s Ec c (some (l, ν)) * ν s') S μ0 E e
      = ∑' ν : PMF State, reachDepM S μ0 E e l ν * ν s' := by
  rw [genW_eq_dconfig]
  have hr : ∀ ν : PMF State, reachDepM S μ0 E e l ν * ν s'
      = ∑' c : DConfig State Label, ((if dConsistent e.1 c then (1 : ENNReal) else 0)
          * segWeight S μ0 E c.segs
          * moveTerm S (segSrc μ0 c.segs) (segHist E c.segs) ⟨c.cur, c.curT⟩ (some (l, ν)))
        * ν s' := by
    intro ν; rw [reachDepM, ENNReal.tsum_mul_right]
  rw [tsum_congr hr, ENNReal.tsum_comm]
  refine tsum_congr (fun c => ?_)
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr (fun ν => ?_)
  ring

/-- Appending a fixed final step is injective on terminating prefixes. -/
private theorem snocT_injective (l : Label) (s' : State) :
    Function.Injective
      (fun cur : {q : AlterSeq State Label // q.trans.Terminates} => snocT cur l s') := by
  rintro ⟨⟨ai, at'⟩, aT⟩ ⟨⟨bi, bt'⟩, bT⟩ h
  have h1 : (⟨ai, at'.append (Stream'.Seq.cons (l, s') Stream'.Seq.nil)⟩ : AlterSeq State Label)
      = ⟨bi, bt'.append (Stream'.Seq.cons (l, s') Stream'.Seq.nil)⟩ := congrArg Subtype.val h
  have hi : ai = bi := congrArg AlterSeq.init h1
  have ht : at' = bt' :=
    Stream'.Seq.append_singleton_inj_left _ _ aT bT _ _ (congrArg AlterSeq.trans h1)
  subst hi; subst ht; rfl

open Classical in
/-- A nonempty current prefix consistent with a `snoc`-history must itself end in
the appended step, hence lies in the range of the `snoc` map. -/
private theorem dcon_snoc_mem_range (e : {q : AlterSeq State Label // q.trans.Terminates})
    (l : Label) (s' : State) (segs : List (FlatSeg State Label))
    (cur : {q : AlterSeq State Label // q.trans.Terminates})
    (hnil : cur.1.trans ≠ Stream'.Seq.nil)
    (hdc : dConsistent (snocT e l s').1 ⟨segs, cur.1, cur.2⟩) :
    cur ∈ Set.range (fun cur' : {q : AlterSeq State Label // q.trans.Terminates} =>
      snocT cur' l s') := by
  have hne : cur.1.trans.toList cur.2 ≠ [] := by
    intro h0
    exact hnil (by rw [← Stream'.Seq.ofList_toList cur.1.trans cur.2, h0, Stream'.Seq.ofList_nil])
  obtain ⟨prev, lastEl, hprevT, hsplit, -, -⟩ :=
    Stream'.Seq.exists_split_last cur.1.trans cur.2 hne
  have h2 : segTrans segs cur.1.trans
      = e.1.trans.append (Stream'.Seq.cons (l, s') Stream'.Seq.nil) := hdc.1
  rw [hsplit, segTrans_append] at h2
  have hlast : lastEl = (l, s') :=
    Stream'.Seq.append_singleton_inj_right _ _
      (segTrans_terminates segs prev hprevT) e.2 _ _ h2
  refine ⟨⟨⟨cur.1.init, prev⟩, hprevT⟩, ?_⟩
  apply Subtype.ext
  show (⟨cur.1.init, prev.append (Stream'.Seq.cons (l, s') Stream'.Seq.nil)⟩ : AlterSeq State Label)
    = cur.1
  rw [← hlast, ← hsplit]

open Classical in
/-- **The arrival-config reindex.** The arrival `genW`-carrier at the `snoc`-history
equals the landing `genW`-carrier at the original history: an arrival config whose
current run ends in `(l, s')` is exactly a config at `e` whose current run then
departs with a `(l, ν)`-move landing at `s'` (bijection via `snocT`). -/
private theorem genW_curReachG_snoc (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) (l : Label) (s' : State) :
    genW (curReachG S) S μ0 E (snocT e l s')
      = genW (fun (s : PMF State) (Ec : AlterSeq (PMF State) Label)
          (c : {q : AlterSeq State Label // q.trans.Terminates}) =>
          ∑' ν : PMF State, moveTerm S s Ec c (some (l, ν)) * ν s') S μ0 E e := by
  rw [genW, genW]
  set F0 : (List (FlatSeg State Label) × {q : AlterSeq State Label // q.trans.Terminates})
      → ENNReal := fun p =>
    (if dConsistent (snocT e l s').1 ⟨p.1, p.2.1, p.2.2⟩ then (1 : ENNReal) else 0)
      * segWeight S μ0 E p.1
      * curReachG S (segSrc μ0 p.1) (segHist E p.1) p.2 with hF0
  have hΦinj : Function.Injective
      (fun p : List (FlatSeg State Label) × {q : AlterSeq State Label // q.trans.Terminates} =>
        (p.1, snocT p.2 l s')) := by
    intro p1 p2 h
    obtain ⟨a1, b1⟩ := p1
    obtain ⟨a2, b2⟩ := p2
    have hfst : a1 = a2 := congrArg Prod.fst h
    have hsnd : b1 = b2 := snocT_injective l s' (congrArg Prod.snd h)
    rw [hfst, hsnd]
  have hf : Function.support F0 ⊆ Set.range
      (fun p : List (FlatSeg State Label) × {q : AlterSeq State Label // q.trans.Terminates} =>
        (p.1, snocT p.2 l s')) := by
    intro p hp
    rw [Function.mem_support, hF0] at hp
    have hdc : dConsistent (snocT e l s').1 ⟨p.1, p.2.1, p.2.2⟩ := by
      by_contra hc
      exact hp (by simp only [hc, if_false, zero_mul])
    have hnil : p.2.1.trans ≠ Stream'.Seq.nil := by
      intro h0
      exact hp (by simp only [curReachG, h0, ne_eq, not_true_eq_false, if_false, mul_zero])
    obtain ⟨cur', hcur'⟩ := dcon_snoc_mem_range e l s' p.1 p.2 hnil hdc
    have hcur'' : snocT cur' l s' = p.2 := hcur'
    refine ⟨(p.1, cur'), ?_⟩
    show (p.1, snocT cur' l s') = p
    rw [hcur'']
  rw [← Function.Injective.tsum_eq hΦinj hf]
  refine tsum_congr (fun p => ?_)
  have hcr : curReachG S (segSrc μ0 p.1) (segHist E p.1) (snocT p.2 l s')
      = ∑' ν : PMF State, moveTerm S (segSrc μ0 p.1) (segHist E p.1) p.2 (some (l, ν)) * ν s' := by
    have h1 : curReachG S (segSrc μ0 p.1) (segHist E p.1) (snocT p.2 l s')
        = curReach S (segSrc μ0 p.1) (segHist E p.1) (snocT p.2 l s') :=
      if_pos (snocT_trans_ne_nil p.2 l s')
    rw [h1, curReach_snoc]
  show (if dConsistent (snocT e l s').1 ⟨p.1, (snocT p.2 l s').1, (snocT p.2 l s').2⟩
        then (1 : ENNReal) else 0) * segWeight S μ0 E p.1
      * curReachG S (segSrc μ0 p.1) (segHist E p.1) (snocT p.2 l s')
    = (if dConsistent e.1 ⟨p.1, p.2.1, p.2.2⟩ then (1 : ENNReal) else 0) * segWeight S μ0 E p.1
      * (∑' ν : PMF State, moveTerm S (segSrc μ0 p.1) (segHist E p.1) p.2 (some (l, ν)) * ν s')
  simp only [hcr, dConsistent_snoc_iff]

/-- **The arrival-step identity (the crux).** Extending the observed history by a
step `(l, s')` decomposes the arrival reach as: depart at `e` with move `(l, ν)`,
then the drawn `ν` lands at `s'`. -/
theorem reachArrM_snoc (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) (l : Label) (s' : State) :
    reachArrM S μ0 E (snocT e l s') = ∑' ν : PMF State, reachDepM S μ0 E e l ν * ν s' := by
  rw [reachArrM_of_ne_nil S μ0 E (snocT e l s') (snocT_trans_ne_nil e l s'),
    genW_curReachG_snoc, genW_landKer]

/-- `reachArrM` depends only on the underlying execution, not its termination proof. -/
private theorem reachArrM_congr (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (a b : {q : AlterSeq State Label // q.trans.Terminates}) (h : a.1 = b.1) :
    reachArrM S μ0 E a = reachArrM S μ0 E b := by
  obtain ⟨av, aT⟩ := a
  obtain ⟨bv, bT⟩ := b
  cases h
  rfl

/-- The mass function of `flatSched` at observed history `e`: a proper step
`some (l,ν)` gets the posterior `reachDepM / reachArrM`; the halt label `⊥` takes
the remaining (halt-or-diverge) mass. Mirrors `expandMass`. -/
noncomputable def flatMass (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) :
    Option (Label × PMF State) → ENNReal
  | some (l, ν) => reachDepM S μ0 E e l ν / reachArrM S μ0 E e
  | none => 1 - ∑' p : Label × PMF State, reachDepM S μ0 E e p.1 p.2 / reachArrM S μ0 E e

/-- `flatMass` is a probability distribution: the proper-step masses sum to `≤ 1`
(departures ⊆ arrivals, `reachDepM_sum_le`), so `⊥` gets a well-defined remainder
and the total is `1`. Mirrors `expandMass_hasSum`. -/
theorem flatMass_hasSum (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) :
    HasSum (flatMass S μ0 E e) 1 := by
  rw [ENNReal.summable.hasSum_iff, tsumOpt (flatMass S μ0 E e)]
  have hsome : ∀ p : Label × PMF State,
      flatMass S μ0 E e (some p) = reachDepM S μ0 E e p.1 p.2 / reachArrM S μ0 E e := by
    rintro ⟨l, ν⟩; rfl
  have hnone : flatMass S μ0 E e none
      = 1 - ∑' p : Label × PMF State, reachDepM S μ0 E e p.1 p.2 / reachArrM S μ0 E e := rfl
  rw [tsum_congr hsome, hnone]
  apply tsub_add_cancel_of_le
  rw [show (∑' p : Label × PMF State, reachDepM S μ0 E e p.1 p.2 / reachArrM S μ0 E e)
        = (∑' p : Label × PMF State, reachDepM S μ0 E e p.1 p.2) / reachArrM S μ0 E e from by
      simp_rw [div_eq_mul_inv]; rw [ENNReal.tsum_mul_right]]
  exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact reachDepM_sum_le S μ0 E e)

open Classical in
/-- **The honest reach-arrival flattening scheduler.** At each observed history the
posterior over the next inner draw is `reachDepM / reachArrM` (halt takes the
remainder). `valid`/`internal_only` delegate to the departure config's inner
witness `innerWitness`. -/
noncomputable def flatSched (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label) : WeakScheduler sys where
  next e := if hT : e.trans.Terminates then
      ⟨flatMass S μ0 E ⟨e, hT⟩, flatMass_hasSum S μ0 E ⟨e, hT⟩⟩
    else PMF.pure none
  valid := by
    classical
    intro e n s hterm hstate l ν hsupp
    by_cases hT : e.trans.Terminates
    · rw [dif_pos hT, PMF.mem_support_iff] at hsupp
      change flatMass S μ0 E ⟨e, hT⟩ (some (l, ν)) ≠ 0 at hsupp
      have hgne : reachDepM S μ0 E ⟨e, hT⟩ l ν ≠ 0 := by
        intro h0
        apply hsupp
        show reachDepM S μ0 E ⟨e, hT⟩ l ν / reachArrM S μ0 E ⟨e, hT⟩ = 0
        rw [h0, ENNReal.zero_div]
      rw [reachDepM] at hgne
      obtain ⟨c, hc⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hgne)
      have hguard : dConsistent e c := by
        by_contra hcon
        rw [if_neg hcon, zero_mul, zero_mul] at hc; exact hc rfl
      have hmove : moveTerm S (segSrc μ0 c.segs) (segHist E c.segs) ⟨c.cur, c.curT⟩
          (some (l, ν)) ≠ 0 := right_ne_zero_of_mul hc
      simp only [moveTerm] at hmove
      obtain ⟨ω, hω⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hmove)
      have hnext : (innerWitness sys (segSrc μ0 c.segs) ω).next c.cur (some (l, ν)) ≠ 0 :=
        right_ne_zero_of_mul hω
      have hsend : s = e.endState hT := by
        have hle1 : Nat.find hT ≤ n := Nat.find_le hterm
        have hle2 : n ≤ Nat.find hT := by
          by_contra hlt
          push_neg at hlt
          obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
          have hget : e.trans.get? m = none :=
            Stream'.Seq.terminated_stable e.trans (by omega) (Nat.find_spec hT)
          rw [hm] at hstate
          change (e.trans.get? m).map Prod.snd = some s at hstate
          rw [hget] at hstate; simp at hstate
        have hn : n = Nat.find hT := le_antisymm hle2 hle1
        rw [hn, AlterSeq.stateAt_find_eq_endState e hT] at hstate
        exact (Option.some.inj hstate).symm
      have heqe : (⟨e.init, segTrans c.segs c.cur.trans⟩ : AlterSeq State Label) = e := by
        rw [hguard.1]
      have hTeq' : (⟨e.init, segTrans c.segs c.cur.trans⟩ :
          AlterSeq State Label).trans.Terminates := by rw [heqe]; exact hT
      have hcend : e.endState hT = c.cur.endState c.curT := by
        rw [← AlterSeq.endState_congr_pub heqe hTeq' hT]
        exact chained_endState c.segs e.init ⟨c.cur, c.curT⟩ hTeq' hguard.2
      have hstepIW := (innerWitness sys (segSrc μ0 c.segs) ω).valid c.cur
        (Nat.find c.curT) (c.cur.endState c.curT) (Nat.find_spec c.curT)
        (AlterSeq.stateAt_find_eq_endState c.cur c.curT) l ν
        ((PMF.mem_support_iff _ _).mpr hnext)
      rw [hsend, hcend]; exact hstepIW
    · rw [dif_neg hT, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
      exact absurd rfl hsupp
  internal_only := by
    classical
    intro e l ν hsupp
    by_cases hT : e.trans.Terminates
    · rw [dif_pos hT, PMF.mem_support_iff] at hsupp
      change flatMass S μ0 E ⟨e, hT⟩ (some (l, ν)) ≠ 0 at hsupp
      have hgne : reachDepM S μ0 E ⟨e, hT⟩ l ν ≠ 0 := by
        intro h0
        apply hsupp
        show reachDepM S μ0 E ⟨e, hT⟩ l ν / reachArrM S μ0 E ⟨e, hT⟩ = 0
        rw [h0, ENNReal.zero_div]
      rw [reachDepM] at hgne
      obtain ⟨c, hc⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hgne)
      have hmove : moveTerm S (segSrc μ0 c.segs) (segHist E c.segs) ⟨c.cur, c.curT⟩
          (some (l, ν)) ≠ 0 := right_ne_zero_of_mul hc
      simp only [moveTerm] at hmove
      obtain ⟨ω, hω⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hmove)
      have hnext : (innerWitness sys (segSrc μ0 c.segs) ω).next c.cur (some (l, ν)) ≠ 0 :=
        right_ne_zero_of_mul hω
      exact (innerWitness sys (segSrc μ0 c.segs) ω).internal_only c.cur l ν
        ((PMF.mem_support_iff _ _).mpr hnext)
    · rw [dif_neg hT, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
      exact absurd rfl hsupp

open Classical in
/-- **List-indexed core of the fidelity theorem.** For the canonical terminating
execution `⟨s0, ofList L⟩`, the composite `flatSched`-probability equals its arrival
reach. Proved by cons-end induction on `L`. -/
private theorem reachArrM_aux (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label) (s0 : State) (L : List (Label × State)) :
    (⟨μ0, (flatSched S μ0 E).toScheduler⟩ : ProbabilisticExecution sys).probOf
        ⟨s0, Stream'.Seq.ofList L⟩ (Stream'.Seq.terminates_ofList L)
      = reachArrM S μ0 E ⟨⟨s0, Stream'.Seq.ofList L⟩, Stream'.Seq.terminates_ofList L⟩ := by
  induction L using List.reverseRecOn with
  | nil =>
    rw [ProbabilisticExecution.probOf_congr _ ⟨s0, Stream'.Seq.ofList []⟩ ⟨s0, Stream'.Seq.nil⟩
        (by rw [Stream'.Seq.ofList_nil]) (Stream'.Seq.terminates_ofList [])
        Stream'.Seq.terminates_nil,
      ProbabilisticExecution.probOf_nil,
      reachArrM_congr S μ0 E ⟨⟨s0, Stream'.Seq.ofList []⟩, Stream'.Seq.terminates_ofList []⟩
        ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
        (by show (⟨s0, Stream'.Seq.ofList []⟩ : AlterSeq State Label) = ⟨s0, Stream'.Seq.nil⟩
            rw [Stream'.Seq.ofList_nil]),
      reachArrM, if_pos rfl]
    rfl
  | append_singleton L' last ih =>
    obtain ⟨l, x⟩ := last
    have hofl : (Stream'.Seq.ofList (L' ++ [(l, x)]) : Stream'.Seq (Label × State))
        = (Stream'.Seq.ofList L').append (Stream'.Seq.cons (l, x) Stream'.Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have happ_term : ((Stream'.Seq.ofList L').append
        (Stream'.Seq.cons (l, x) Stream'.Seq.nil)).Terminates := by
      rw [← hofl]; exact Stream'.Seq.terminates_ofList _
    have hnext : ∀ ν : PMF State,
        (flatSched S μ0 E).next ⟨s0, Stream'.Seq.ofList L'⟩ (some (l, ν))
          = reachDepM S μ0 E ⟨⟨s0, Stream'.Seq.ofList L'⟩, Stream'.Seq.terminates_ofList L'⟩ l ν
            / reachArrM S μ0 E ⟨⟨s0, Stream'.Seq.ofList L'⟩, Stream'.Seq.terminates_ofList L'⟩ := by
      intro ν
      rw [show (flatSched S μ0 E).next ⟨s0, Stream'.Seq.ofList L'⟩
          = ⟨flatMass S μ0 E ⟨⟨s0, Stream'.Seq.ofList L'⟩, Stream'.Seq.terminates_ofList L'⟩,
              flatMass_hasSum S μ0 E
                ⟨⟨s0, Stream'.Seq.ofList L'⟩, Stream'.Seq.terminates_ofList L'⟩⟩
          from dif_pos (Stream'.Seq.terminates_ofList L')]
      rfl
    have hker : (⟨μ0, (flatSched S μ0 E).toScheduler⟩ : ProbabilisticExecution sys).kernel
          ⟨s0, Stream'.Seq.ofList L'⟩ (l, x)
        = ∑' ν : PMF State,
            (reachDepM S μ0 E ⟨⟨s0, Stream'.Seq.ofList L'⟩, Stream'.Seq.terminates_ofList L'⟩ l ν
              / reachArrM S μ0 E ⟨⟨s0, Stream'.Seq.ofList L'⟩, Stream'.Seq.terminates_ofList L'⟩)
              * ν x := by
      rw [ProbabilisticExecution.kernel]
      exact tsum_congr (fun ν => by rw [hnext ν])
    rw [ProbabilisticExecution.probOf_congr _ ⟨s0, Stream'.Seq.ofList (L' ++ [(l, x)])⟩
        ⟨s0, (Stream'.Seq.ofList L').append (Stream'.Seq.cons (l, x) Stream'.Seq.nil)⟩
        (by rw [hofl]) (Stream'.Seq.terminates_ofList _) happ_term,
      ProbabilisticExecution.probOf_append_singleton _ s0 (Stream'.Seq.ofList L')
        (Stream'.Seq.terminates_ofList L') (l, x) happ_term, ih, hker,
      reachArrM_congr S μ0 E
        ⟨⟨s0, Stream'.Seq.ofList (L' ++ [(l, x)])⟩, Stream'.Seq.terminates_ofList _⟩
        (snocT ⟨⟨s0, Stream'.Seq.ofList L'⟩, Stream'.Seq.terminates_ofList L'⟩ l x)
        (by show (⟨s0, Stream'.Seq.ofList (L' ++ [(l, x)])⟩ : AlterSeq State Label)
              = ⟨s0, (Stream'.Seq.ofList L').append (Stream'.Seq.cons (l, x) Stream'.Seq.nil)⟩
            rw [hofl]),
      reachArrM_snoc]
    by_cases hz : reachArrM S μ0 E
        ⟨⟨s0, Stream'.Seq.ofList L'⟩, Stream'.Seq.terminates_ofList L'⟩ = 0
    · rw [hz, zero_mul, eq_comm]
      refine ENNReal.tsum_eq_zero.mpr (fun ν => ?_)
      have hle := reachDepM_sum_le S μ0 E ⟨⟨s0, Stream'.Seq.ofList L'⟩, Stream'.Seq.terminates_ofList L'⟩
      rw [hz, nonpos_iff_eq_zero] at hle
      rw [ENNReal.tsum_eq_zero.mp hle (l, ν), zero_mul]
    · have hle : reachArrM S μ0 E
          ⟨⟨s0, Stream'.Seq.ofList L'⟩, Stream'.Seq.terminates_ofList L'⟩ ≤ 1 := by
        rw [← ih]
        exact (ProbabilisticExecution.probOf_le_init _ _ _).trans (PMF.coe_le_one _ _)
      have htop : reachArrM S μ0 E
          ⟨⟨s0, Stream'.Seq.ofList L'⟩, Stream'.Seq.terminates_ofList L'⟩ ≠ ⊤ :=
        (hle.trans_lt ENNReal.one_lt_top).ne
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr (fun ν => ?_)
      rw [← mul_assoc, ENNReal.mul_div_cancel hz htop]

/-- **The fidelity lemma.** The probability that the honest reach-arrival
flattening scheduler `flatSched` (sourced at `μ0`) produces the terminating
concrete execution `e` equals its arrival reach `reachArrM`. -/
theorem probOf_eq_reachArrM (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) :
    (⟨μ0, (flatSched S μ0 E).toScheduler⟩ : ProbabilisticExecution sys).probOf e.1 e.2
      = reachArrM S μ0 E e := by
  obtain ⟨⟨ei, et⟩, eT⟩ := e
  rw [ProbabilisticExecution.probOf_congr _ ⟨ei, et⟩ ⟨ei, Stream'.Seq.ofList (et.toList eT)⟩
      (by rw [Stream'.Seq.ofList_toList et eT]) eT (Stream'.Seq.terminates_ofList _),
    reachArrM_congr S μ0 E ⟨⟨ei, et⟩, eT⟩
      ⟨⟨ei, Stream'.Seq.ofList (et.toList eT)⟩, Stream'.Seq.terminates_ofList _⟩
      (by show (⟨ei, et⟩ : AlterSeq State Label) = ⟨ei, Stream'.Seq.ofList (et.toList eT)⟩
          rw [Stream'.Seq.ofList_toList et eT])]
  exact reachArrM_aux S μ0 E ei (et.toList eT)

/-- **The honest halted-arrival reach** at observed history `e`: the arrival reach
`reachArrM` minus the total departure reach `∑' p, reachDepM`. This is the mass
that arrives at a decision point consistent with `e` and does NOT depart next — the
`haltReach`-side of `curReach_split`, plus the fresh-reset boundary — i.e. the
composite halts here. Departures ⊆ arrivals (`reachDepM_sum_le`) keeps it honest. -/
noncomputable def reachArrHalt (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) : ENNReal :=
  reachArrM S μ0 E e - ∑' p : Label × PMF State, reachDepM S μ0 E e p.1 p.2

/-- **The halt-mass identity.** The halting mass of `flatSched` at the
terminating execution `e` is exactly the honest halted-arrival reach. The
haltMass-side analogue of the fidelity `probOf_eq_reachArrM`: `haltMass =
probOf · next(⊥) = reachArrM · flatMass(⊥) = reachArrM − ∑ reachDepM`, the last
step by ENNReal div-cancel under the departures ⊆ arrivals bound. -/
theorem flatSched_haltMass (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) :
    (flatSched S μ0 E).haltMass μ0 e = reachArrHalt S μ0 E e := by
  obtain ⟨ev, eT⟩ := e
  have key : ∀ x y : ENNReal, y ≤ x → x ≠ ⊤ → x * (1 - y / x) = x - y := by
    intro x y hyx hxtop
    rcases eq_or_ne x 0 with hx | hx
    · subst hx; rw [le_zero_iff.mp hyx]; simp
    · rw [ENNReal.mul_sub (fun _ _ => hxtop), mul_one, ← mul_div_assoc, mul_comm x y,
        mul_div_assoc, ENNReal.div_self hx hxtop, mul_one]
  have hnext : (flatSched S μ0 E).toScheduler.next ev none
      = flatMass S μ0 E ⟨ev, eT⟩ none := by
    show (flatSched S μ0 E).next ev none = _
    simp only [flatSched, dif_pos eT]
    rfl
  rw [WeakScheduler.haltMass, Scheduler.haltMass]
  show (⟨μ0, (flatSched S μ0 E).toScheduler⟩ : ProbabilisticExecution sys).probOf ev eT
      * (flatSched S μ0 E).toScheduler.next ev none = _
  rw [hnext, probOf_eq_reachArrM S μ0 E ⟨ev, eT⟩]
  show reachArrM S μ0 E ⟨ev, eT⟩ * flatMass S μ0 E ⟨ev, eT⟩ none = _
  have hdiv : (∑' p : Label × PMF State,
        reachDepM S μ0 E ⟨ev, eT⟩ p.1 p.2 / reachArrM S μ0 E ⟨ev, eT⟩)
      = (∑' p : Label × PMF State, reachDepM S μ0 E ⟨ev, eT⟩ p.1 p.2)
          / reachArrM S μ0 E ⟨ev, eT⟩ := by
    simp_rw [div_eq_mul_inv]; rw [ENNReal.tsum_mul_right]
  have htop : reachArrM S μ0 E ⟨ev, eT⟩ ≠ ⊤ := by
    rw [← probOf_eq_reachArrM S μ0 E ⟨ev, eT⟩]
    exact ((ProbabilisticExecution.probOf_le_init _ _ _).trans (PMF.coe_le_one _ _)).trans_lt
      ENNReal.one_lt_top |>.ne
  show reachArrM S μ0 E ⟨ev, eT⟩
      * (1 - ∑' p : Label × PMF State,
          reachDepM S μ0 E ⟨ev, eT⟩ p.1 p.2 / reachArrM S μ0 E ⟨ev, eT⟩) = _
  rw [hdiv, key _ _ (reachDepM_sum_le S μ0 E ⟨ev, eT⟩) htop]
  rfl

/-- The `flatSched` halt-integral of a test `g` from source `μ0`, rooted at
macro-history `E`. -/
noncomputable def fHM (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label) (g : State → ENNReal) : ENNReal :=
  ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
    (flatSched S μ0 E).haltMass μ0 e * g (e.1.endState e.2)

/-- `fHM` as a `reachArrHalt`-weighted sum (via the halt-mass identity `flatSched_haltMass`). -/
private theorem fHM_reachArrHalt (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label) (g : State → ENNReal) :
    fHM S μ0 E g
      = ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          reachArrHalt S μ0 E e * g (e.1.endState e.2) := by
  unfold fHM
  exact tsum_congr (fun e => by rw [flatSched_haltMass])

/-- The macro scheduler's total mass at `E` splits as halt-now plus `τ`-emission. -/
private theorem macroTot (S : WeakScheduler (𝒟(sys^w))) (E : AlterSeq (PMF State) Label) :
    S.next E none + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω)) = 1 := by
  have hzero : ∀ (l : Label) (ω : PMF (PMF State)), l ≠ Silent.τ →
      S.next E (some (l, ω)) = 0 := fun l ω hl => by
    by_contra hne
    exact hl (S.internal_only E l ω ((PMF.mem_support_iff _ _).mpr hne))
  have h1 : (∑' o, (S.next E) o) = 1 := PMF.tsum_coe _
  rw [tsumOpt (fun o => (S.next E) o)] at h1
  rw [← h1]; congr 1
  refine ((?_ : (∑' p : Label × PMF (PMF State), (S.next E) (some p)) = _)).symm
  rw [ENNReal.tsum_prod', tsum_eq_single Silent.τ (fun l hl => by
    rw [ENNReal.tsum_eq_zero]; intro ω; exact hzero l ω hl)]

open Classical in
/-- **The nil carve split.** At an empty observed history the source
mass splits exactly into the (stall-resolvent) departures and the composite
halt. -/
private theorem reachArrHalt_nil_add (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label) (s0 : State) :
    reachArrHalt S μ0 E ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
        + genW (depMove S) S μ0 E ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
      = μ0 s0 := by
  set e0 : {e : AlterSeq State Label // e.trans.Terminates} :=
    ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ with he0
  have hnil : e0.1.trans = Stream'.Seq.nil := rfl
  have hdep : (∑' p : Label × PMF State, reachDepM S μ0 E e0 p.1 p.2)
      = genW (depMove S) S μ0 E e0 := by
    rw [genW_eq_dconfig]
    simp_rw [reachDepM]
    rw [ENNReal.tsum_comm]
    exact tsum_congr (fun c => by rw [ENNReal.tsum_mul_left, moveSum_eq_depMove])
  rw [reachArrHalt, hdep, reachArrM, if_pos hnil]
  exact tsub_add_cancel_of_le (genW_dep_nil S μ0 E e0 hnil)

open Classical in
/-- Reindex a `nil`-guarded execution sum over the source `State`: the only
terminating executions with empty transitions are `⟨s0, nil⟩`. -/
private theorem tsum_nil_reindex
    (G : {e : AlterSeq State Label // e.trans.Terminates} → ENNReal) :
    (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        (if e.1.trans = Stream'.Seq.nil then G e else 0))
      = ∑' s0 : State, G ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ := by
  have hinj : Function.Injective
      (fun s0 : State => (⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ :
        {e : AlterSeq State Label // e.trans.Terminates})) := by
    intro a b hab
    simp only [Subtype.mk.injEq, AlterSeq.mk.injEq] at hab
    exact hab.1
  have hsupp : ∀ e ∉ Set.range (fun s0 : State =>
      (⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ :
        {e : AlterSeq State Label // e.trans.Terminates})),
      (if e.1.trans = Stream'.Seq.nil then G e else 0) = 0 := by
    intro e he
    rw [if_neg]
    intro hnil
    refine he ⟨e.1.init, ?_⟩
    obtain ⟨⟨i, t⟩, hT⟩ := e
    simp only at hnil ⊢
    exact Subtype.ext (congrArg (AlterSeq.mk i) hnil.symm)
  rw [← Function.Injective.tsum_eq hinj (Function.support_subset_iff'.2 hsupp)]
  exact tsum_congr (fun s0 => if_pos rfl)

/-- **`g` factors through the peel.** The residual history after peeling a
legal first segment has the SAME end-state as the full history (the prepended
run does not move the final landing point). -/
private theorem dResidual_endState
    (e : {q : AlterSeq State Label // q.trans.Terminates})
    (seg : FlatSeg State Label) (h : segPre e seg) :
    (dResidual e seg).1.endState (dResidual e seg).2 = e.1.endState e.2 := by
  unfold dResidual
  obtain ⟨hinit, happ⟩ := h
  have hAterm : seg.run.trans.Terminates := seg.runT
  have hBterm : (e.1.trans.drop (seg.run.trans.length seg.runT)).Terminates :=
    WeakScheduler.drop_terminates e.2 _
  have hAB : (seg.run.trans.append
      (e.1.trans.drop (seg.run.trans.length seg.runT))).Terminates := by rw [happ]; exact e.2
  have hseg : (⟨e.1.init, seg.run.trans⟩ : AlterSeq State Label) = seg.run := by rw [← hinit]
  have he1 : e.1 = (⟨e.1.init, seg.run.trans.append
      (e.1.trans.drop (seg.run.trans.length seg.runT))⟩ : AlterSeq State Label) := by rw [happ]
  rw [AlterSeq.endState_congr_pub he1 e.2 hAB,
    endState_append_shift e.1.init seg.run.trans
      (e.1.trans.drop (seg.run.trans.length seg.runT)) hAterm hAB hBterm,
    AlterSeq.endState_congr_pub hseg hAterm seg.runT]

open Classical in
/-- **The front-prepend reindex.** For a fixed
first segment `seg` (nonempty run), summing `H (dResidual e seg)` over the histories
`e` that legally peel `seg` equals summing `H e'` over the residual histories `e'`
whose init is the segment's landing state. The prepend map `e' ↦ ⟨seg.run.init,
seg.run.trans ⧺ e'.trans⟩` is injective ONLY on the fiber `e'.init = seg.run.end`
(it discards the init otherwise), so the reindex runs over that fiber. -/
private theorem segPre_reindex (seg : FlatSeg State Label)
    (H : {q : AlterSeq State Label // q.trans.Terminates} → ENNReal) :
    (∑' e : {q : AlterSeq State Label // q.trans.Terminates},
        if segPre e seg then H (dResidual e seg) else 0)
      = ∑' e' : {q : AlterSeq State Label // q.trans.Terminates},
          if e'.1.init = seg.run.endState seg.runT then H e' else 0 := by
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun x => (⟨⟨seg.run.init, seg.run.trans.append x.1.1.trans⟩,
        ⟨_, Stream'.Seq.terminatedAt_append_find seg.runT (Nat.find_spec x.1.2)⟩⟩ :
        {q : AlterSeq State Label // q.trans.Terminates})) ?_ ?_ ?_
  · rintro ⟨e'a, ha⟩ ⟨e'b, hb⟩ hab
    have hia : e'a.1.init = seg.run.endState seg.runT := by
      by_contra h; exact (Function.mem_support.mp ha) (if_neg h)
    have hib : e'b.1.init = seg.run.endState seg.runT := by
      by_contra h; exact (Function.mem_support.mp hb) (if_neg h)
    have htr : seg.run.trans.append e'a.1.trans = seg.run.trans.append e'b.1.trans :=
      congrArg AlterSeq.trans (congrArg Subtype.val hab)
    have hte : e'a.1.trans = e'b.1.trans := by
      have hd := congrArg (fun s => s.drop (seg.run.trans.length seg.runT)) htr
      rwa [drop_append_length seg.run.trans e'a.1.trans seg.runT,
        drop_append_length seg.run.trans e'b.1.trans seg.runT] at hd
    apply Subtype.ext; apply Subtype.ext
    show (⟨e'a.1.init, e'a.1.trans⟩ : AlterSeq State Label) = ⟨e'b.1.init, e'b.1.trans⟩
    rw [hia, hib, hte]
  · intro e he
    have hf0 : (if segPre e seg then H (dResidual e seg) else 0) ≠ 0 := Function.mem_support.mp he
    have hsp : segPre e seg := by by_contra hne; exact hf0 (if_neg hne)
    have hH : H (dResidual e seg) ≠ 0 := by rw [if_pos hsp] at hf0; exact hf0
    obtain ⟨hinit, happ⟩ := hsp
    refine ⟨⟨dResidual e seg, ?_⟩, ?_⟩
    · have hcond : (if (dResidual e seg).1.init = seg.run.endState seg.runT
          then H (dResidual e seg) else 0) = H (dResidual e seg) := if_pos rfl
      rw [Function.mem_support]
      show (if (dResidual e seg).1.init = seg.run.endState seg.runT
          then H (dResidual e seg) else 0) ≠ 0
      rw [hcond]; exact hH
    · apply Subtype.ext
      show (⟨seg.run.init, seg.run.trans.append (dResidual e seg).1.trans⟩ :
          AlterSeq State Label) = e.1
      show (⟨seg.run.init,
          seg.run.trans.append (e.1.trans.drop (seg.run.trans.length seg.runT))⟩ :
          AlterSeq State Label) = e.1
      rw [happ, hinit]
  · rintro ⟨e', hx⟩
    have hg0 : (if e'.1.init = seg.run.endState seg.runT then H e' else 0) ≠ 0 :=
      Function.mem_support.mp hx
    have hfib : e'.1.init = seg.run.endState seg.runT := by
      by_contra hne; exact hg0 (if_neg hne)
    have hdrop : (seg.run.trans.append e'.1.trans).drop (seg.run.trans.length seg.runT)
        = e'.1.trans := drop_append_length seg.run.trans e'.1.trans seg.runT
    have hsp : segPre ⟨⟨seg.run.init, seg.run.trans.append e'.1.trans⟩,
        ⟨_, Stream'.Seq.terminatedAt_append_find seg.runT (Nat.find_spec e'.2)⟩⟩ seg :=
      ⟨rfl, by simp only [hdrop]⟩
    simp only [if_pos hfib, if_pos hsp]
    congr 1
    apply Subtype.ext
    show (⟨seg.run.endState seg.runT,
        (seg.run.trans.append e'.1.trans).drop (seg.run.trans.length seg.runT)⟩ :
        AlterSeq State Label) = e'.1
    rw [hdrop, ← hfib]

open Classical in
/-- **Nil/nonempty carve of `fHM`** (pure reindex, `tsum_nil_reindex`).
The nil part is resolved by the stall resolvent (`nilHalt_resolvent`). -/
private theorem fHM_split (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label) :
    fHM S μ0 E g
      = (∑' s0 : State,
            reachArrHalt S μ0 E ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0)
        + ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
            if e.1.trans = Stream'.Seq.nil then 0
            else reachArrHalt S μ0 E e * g (e.1.endState e.2) := by
  rw [fHM_reachArrHalt]
  have hnil : (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        if e.1.trans = Stream'.Seq.nil then reachArrHalt S μ0 E e * g (e.1.endState e.2) else 0)
      = ∑' s0 : State,
          reachArrHalt S μ0 E ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0 := by
    rw [tsum_nil_reindex (fun e => reachArrHalt S μ0 E e * g (e.1.endState e.2))]
    refine tsum_congr (fun s0 => ?_)
    rw [AlterSeq.endState_of_trans_nil (⟨s0, Stream'.Seq.nil⟩ : AlterSeq State Label) rfl
      Stream'.Seq.terminates_nil]
  rw [← hnil, ← ENNReal.tsum_add]
  exact tsum_congr (fun e => by split_ifs <;> simp)

open Classical in
/-- **Junction linearity split** through the child `fHM_split`. -/
private theorem renewal_junction_split (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label) :
    (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
        * ∑' m', ω m' * fHM S m' (macroExtend E m') g)
      = (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m' * (∑' s0 : State,
                reachArrHalt S m' (macroExtend E m')
                    ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0))
        + (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m' * (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
                if e.1.trans = Stream'.Seq.nil then 0
                else reachArrHalt S m' (macroExtend E m') e * g (e.1.endState e.2))) := by
  have hpt : ∀ ω : PMF (PMF State),
      S.next E (some (Silent.τ, ω)) * ∑' m', ω m' * fHM S m' (macroExtend E m') g
        = S.next E (some (Silent.τ, ω))
              * ∑' m', ω m' * (∑' s0 : State,
                  reachArrHalt S m' (macroExtend E m')
                      ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0)
          + S.next E (some (Silent.τ, ω))
              * ∑' m', ω m' * (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
                  if e.1.trans = Stream'.Seq.nil then 0
                  else reachArrHalt S m' (macroExtend E m') e * g (e.1.endState e.2)) := by
    intro ω
    rw [← mul_add]
    congr 1
    rw [← ENNReal.tsum_add]
    refine tsum_congr (fun m' => ?_)
    rw [← mul_add]
    congr 1
    exact fHM_split S g m' (macroExtend E m')
  rw [tsum_congr hpt, ENNReal.tsum_add]

/-- **The divided per-segment head weight** (the `segWeight`-cons factor,
`src = μ0`). Names the junction-divided head that the peel/collapse carries. -/
private noncomputable def divHead (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label) (seg : FlatSeg State Label) : ENNReal :=
  S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
    * ((innerWitness sys μ0 seg.emit).haltMass μ0 ⟨seg.run, seg.runT⟩
        / (seg.emit.bind id) (seg.run.endState seg.runT))

open Classical in
/-- **Parent nonempty-history halt-reach integral** (`boundaryHaltSum`): the
single-current-run halt reach summed over nonempty observed histories, `g`-weighted. -/
private noncomputable def bHaltSum (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label) : ENNReal :=
  ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
    if e.1.trans = Stream'.Seq.nil then 0
    else haltReach S μ0 E e * g (e.1.endState e.2)

open Classical in
/-- **Reset-departure integral** (`Σreset·g`): the fresh-restart departures
at the empty residual, summed over the peels of each nonempty observed history,
`g`-weighted. The tail factor is the RESOLVENT departure carrier
`genW (depMove)` at the empty residual (post-stall resets included), not the
single-stage `depMove`. -/
private noncomputable def resetSum (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label) : ENNReal :=
  ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
    if e.1.trans = Stream'.Seq.nil then 0
    else (∑' seg : FlatSeg State Label,
            (if segPre e seg ∧ (dResidual e seg).1.trans = Stream'.Seq.nil
              then (1 : ENNReal) else 0)
              * divHead S μ0 E seg
              * genW (fun s Ec c => depMove S s Ec c) S seg.succ (macroExtend E seg.succ)
                  (dResidual e seg))
          * g (e.1.endState e.2)

open Classical in
/-- **Single-run halt-integral collapse.** The parent's current-run halt
reach, summed over all observed histories and `g`-weighted, collapses through the
inner-witness integrate identity (`innerWitness_integrate`, valid at each `ω` by
`S.valid` under `hinv`) to the junction average of the child source-integrals. -/
private theorem parentHaltReach_collapse (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) (hinv : μ0 = E.endState hT) :
    (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        haltReach S μ0 E e * g (e.1.endState e.2))
      = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * ∑' m', ω m' * (∑' s, m' s * g s) := by
  have hunfold : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      haltReach S μ0 E e * g (e.1.endState e.2)
        = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ((innerWitness sys μ0 ω).haltMass μ0 e * g (e.1.endState e.2)) := by
    intro e
    rw [show haltReach S μ0 E e
          = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
              * (innerWitness sys μ0 ω).haltMass μ0 e from by
        rw [haltReach]
        refine tsum_congr (fun ω => ?_)
        unfold WeakScheduler.haltMass Scheduler.haltMass
        rw [mul_assoc], ← ENNReal.tsum_mul_right]
    exact tsum_congr (fun ω => by rw [mul_assoc])
  rw [tsum_congr hunfold, ENNReal.tsum_comm]
  refine tsum_congr (fun ω => ?_)
  rw [ENNReal.tsum_mul_left]
  by_cases hw : S.next E (some (Silent.τ, ω)) = 0
  · rw [hw, zero_mul, zero_mul]
  · congr 1
    have hstep : (𝒟(sys^w)).step μ0 Silent.τ ω := by
      rw [hinv]
      exact S.valid E (Nat.find hT) (E.endState hT) (Nat.find_spec hT)
        (AlterSeq.stateAt_find_eq_endState E hT) Silent.τ ω ((PMF.mem_support_iff _ _).mpr hw)
    rw [innerWitness_integrate hstep g, tsum_bind_mul ω id g]
    simp only [id_eq]

open Classical in
/-- **The total current-run halt reach** splits over the nil/nonempty
histories into `nilHalt_g` (`tsum_nil_reindex`) plus `bHaltSum`. -/
private theorem haltReach_total_eq (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label) :
    (∑' s0 : State, haltReach S μ0 E
          ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0)
        + bHaltSum S g μ0 E
      = ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          haltReach S μ0 E e * g (e.1.endState e.2) := by
  rw [bHaltSum]
  have hsplit : (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        haltReach S μ0 E e * g (e.1.endState e.2))
      = (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          if e.1.trans = Stream'.Seq.nil then haltReach S μ0 E e * g (e.1.endState e.2) else 0)
        + ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          if e.1.trans = Stream'.Seq.nil then 0 else haltReach S μ0 E e * g (e.1.endState e.2) := by
    rw [← ENNReal.tsum_add]; exact tsum_congr (fun e => by split_ifs <;> simp)
  rw [hsplit, tsum_nil_reindex (fun e => haltReach S μ0 E e * g (e.1.endState e.2))]
  congr 1
  refine tsum_congr (fun s0 => ?_)
  rw [AlterSeq.endState_of_trans_nil (⟨s0, Stream'.Seq.nil⟩ : AlterSeq State Label) rfl
    Stream'.Seq.terminates_nil]

/-- **The fresh-restart gap** (`Gap`): the junction average of the child
fresh-run (`nil`) RESOLVENT departure integrals (`genW (depMove)`). -/
private noncomputable def Gap (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (E : AlterSeq (PMF State) Label) : ENNReal :=
  ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
    * ∑' m', ω m' * (∑' s0 : State,
        genW (fun s Ec c => depMove S s Ec c) S m' (macroExtend E m')
            ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0)

/-- **Total current-run halt reach is a sub-probability** (no invariant
needed): unfold to the emissions' witness halt masses and apply the Kraft bound. -/
private theorem haltReach_tsum_le_one (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (E : AlterSeq (PMF State) Label) :
    (∑' e : {e : AlterSeq State Label // e.trans.Terminates}, haltReach S src E e) ≤ 1 := by
  have hunfold : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      haltReach S src E e
        = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * (innerWitness sys src ω).haltMass src e := by
    intro e
    rw [haltReach]
    refine tsum_congr (fun ω => ?_)
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [mul_assoc]
  rw [tsum_congr hunfold, ENNReal.tsum_comm]
  calc (∑' ω : PMF (PMF State), ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          S.next E (some (Silent.τ, ω)) * (innerWitness sys src ω).haltMass src e)
      = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
              (innerWitness sys src ω).haltMass src e :=
        tsum_congr (fun ω => ENNReal.tsum_mul_left)
    _ ≤ ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω)) * 1 := by
        gcongr with ω
        exact WeakScheduler.haltMass_tsum_le_one _ _
    _ = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω)) := by
        rw [tsum_congr (fun _ => mul_one _)]
    _ ≤ 1 := macroSome_le_one S E

open Classical in
/-- **`bHaltSum` is a sub-probability.** -/
private theorem bHaltSum_le_one (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (hg : ∀ x, g x ≤ 1) (μ0 : PMF State) (E : AlterSeq (PMF State) Label) :
    bHaltSum S g μ0 E ≤ 1 := by
  refine le_trans ?_ (haltReach_tsum_le_one S μ0 E)
  rw [bHaltSum]
  refine ENNReal.tsum_le_tsum (fun e => ?_)
  split_ifs
  · exact zero_le'
  · exact mul_le_of_le_one_right' (hg _)

open Classical in
/-- **The nil-run halt integral is a sub-probability.** -/
private theorem nilHaltReach_g_le_one (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (hg : ∀ x, g x ≤ 1) (μ0 : PMF State) (E : AlterSeq (PMF State) Label) :
    (∑' s0 : State,
        haltReach S μ0 E ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0) ≤ 1 := by
  have hinj : Function.Injective (fun s0 : State =>
      (⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ :
        {e : AlterSeq State Label // e.trans.Terminates})) :=
    fun a b h => congrArg (fun e => e.1.init) h
  calc (∑' s0 : State,
          haltReach S μ0 E ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0)
      ≤ ∑' s0 : State,
          haltReach S μ0 E ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ :=
        ENNReal.tsum_le_tsum (fun s0 => mul_le_of_le_one_right' (hg s0))
    _ ≤ ∑' e : {e : AlterSeq State Label // e.trans.Terminates}, haltReach S μ0 E e :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj (fun e => haltReach S μ0 E e)
    _ ≤ 1 := haltReach_tsum_le_one S μ0 E

open Classical in
/-- **The reset integral is dominated by the boundary halt integral**:
per peel, LEMMA A bounds the resolvent tail by the successor mass, and
`boundaryHalt_le` absorbs the boundary. -/
private theorem resetSum_le_bHaltSum (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label) :
    resetSum S g μ0 E ≤ bHaltSum S g μ0 E := by
  rw [resetSum, bHaltSum]
  refine ENNReal.tsum_le_tsum (fun e => ?_)
  split_ifs
  · exact le_rfl
  · refine mul_le_mul_right' ?_ _
    refine le_trans ?_ (boundaryHalt_le S μ0 E e)
    refine ENNReal.tsum_le_tsum (fun seg => ?_)
    by_cases hP : segPre e seg ∧ (dResidual e seg).1.trans = Stream'.Seq.nil
    · rw [if_pos hP]
      simp only [divHead]
      gcongr
      exact genW_dep_nil S seg.succ (macroExtend E seg.succ) (dResidual e seg) hP.2
    · rw [if_neg hP, zero_mul, zero_mul, zero_mul, zero_mul]

/-- **The reset integral is a sub-probability.** -/
private theorem resetSum_le_one (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (hg : ∀ x, g x ≤ 1) (μ0 : PMF State) (E : AlterSeq (PMF State) Label) :
    resetSum S g μ0 E ≤ 1 :=
  (resetSum_le_bHaltSum S g μ0 E).trans (bHaltSum_le_one S g hg μ0 E)

/-- An `append` is `nil` only if both parts are. -/
private theorem seq_append_eq_nil {α : Type} {A B : Stream'.Seq α} :
    A.append B = Stream'.Seq.nil → A = Stream'.Seq.nil ∧ B = Stream'.Seq.nil := by
  apply Stream'.Seq.recOn A
  · intro h
    rw [Stream'.Seq.nil_append] at h
    exact ⟨rfl, h⟩
  · intro x t h
    rw [Stream'.Seq.cons_append] at h
    exact absurd h (Stream'.Seq.cons_ne_nil)

/-- Dropping from `nil` yields `nil`. -/
private theorem seq_drop_nil {α : Type} (n : ℕ) :
    (Stream'.Seq.nil : Stream'.Seq α).drop n = Stream'.Seq.nil := by
  apply Stream'.Seq.ext
  intro m
  rw [Stream'.Seq.drop_get?]
  rfl

/-- **Peels of the empty history are exactly the empty runs at its state.** -/
private theorem segPre_nil_iff (s0 : State) (seg : FlatSeg State Label) :
    segPre ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ seg
      ↔ seg.run = ⟨s0, Stream'.Seq.nil⟩ := by
  constructor
  · rintro ⟨hinit, happ⟩
    have hdrop : ((⟨s0, Stream'.Seq.nil⟩ : AlterSeq State Label).trans.drop
        (seg.run.trans.length seg.runT)) = Stream'.Seq.nil := seq_drop_nil _
    rw [hdrop] at happ
    have hrun := (seq_append_eq_nil happ).1
    calc seg.run = ⟨seg.run.init, seg.run.trans⟩ := rfl
      _ = ⟨s0, Stream'.Seq.nil⟩ := by rw [hinit, hrun]
  · intro hrun
    obtain ⟨emit, succ, run, runT⟩ := seg
    simp only at hrun
    subst hrun
    exact ⟨rfl, by rw [Stream'.Seq.nil_append, seq_drop_nil]⟩

/-- **The residual of an empty-run peel of the empty history.** -/
private theorem dResidual_nil_eq (s0 : State) (seg : FlatSeg State Label)
    (h : seg.run = ⟨s0, Stream'.Seq.nil⟩) :
    dResidual ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ seg
      = ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ := by
  obtain ⟨emit, succ, run, runT⟩ := seg
  simp only at h
  subst h
  apply Subtype.ext
  show (⟨(⟨s0, Stream'.Seq.nil⟩ : AlterSeq State Label).endState runT,
      (⟨s0, Stream'.Seq.nil⟩ : AlterSeq State Label).trans.drop _⟩ : AlterSeq State Label)
    = ⟨s0, Stream'.Seq.nil⟩
  rw [AlterSeq.endState_of_trans_nil (⟨s0, Stream'.Seq.nil⟩ : AlterSeq State Label) rfl runT]
  show (⟨s0, Stream'.Seq.nil.drop _⟩ : AlterSeq State Label) = ⟨s0, Stream'.Seq.nil⟩
  rw [seq_drop_nil]

open Classical in
/-- **The nil-history stall peel, `(ω, m')`-form.** The `genW_peel` seg-sum
at an empty observed history collapses over the forced empty run to the
Bayes-coupled stall factor times a child carrier `T` at the same state. -/
private theorem nil_peel_collapse (S : WeakScheduler (𝒟(sys^w)))
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label) (s0 : State)
    (T : PMF State → AlterSeq (PMF State) Label →
      {q : AlterSeq State Label // q.trans.Terminates} → ENNReal) :
    (∑' seg : FlatSeg State Label,
        (if segPre ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ seg
            then (1 : ENNReal) else 0)
          * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
              * ((innerWitness sys μ0 seg.emit).haltMass μ0 ⟨seg.run, seg.runT⟩
                  / (seg.emit.bind id) (seg.run.endState seg.runT)))
          * T seg.succ (macroExtend E seg.succ)
              (dResidual ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ seg))
      = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * ∑' m', ω m'
              * (((innerWitness sys μ0 ω).haltMass μ0
                      ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
                    / (ω.bind id) s0)
                * T m' (macroExtend E m')
                    ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩) := by
  have hre : (∑' seg : FlatSeg State Label,
      (if segPre ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ seg
          then (1 : ENNReal) else 0)
        * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
            * ((innerWitness sys μ0 seg.emit).haltMass μ0 ⟨seg.run, seg.runT⟩
                / (seg.emit.bind id) (seg.run.endState seg.runT)))
        * T seg.succ (macroExtend E seg.succ)
            (dResidual ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ seg))
      = ∑' t : PMF (PMF State) × PMF State × {q : AlterSeq State Label // q.trans.Terminates},
          (if segPre ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
              ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩ then (1 : ENNReal) else 0)
            * (S.next E (some (Silent.τ, t.1)) * t.1 t.2.1
                * ((innerWitness sys μ0 t.1).haltMass μ0 ⟨t.2.2.1, t.2.2.2⟩
                    / (t.1.bind id) (t.2.2.1.endState t.2.2.2)))
            * T t.2.1 (macroExtend E t.2.1)
                (dResidual ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
                  ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩) :=
    Equiv.tsum_eq flatSegEquiv
      (fun t : PMF (PMF State) × PMF State × {q : AlterSeq State Label // q.trans.Terminates} =>
        (if segPre ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
            ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩ then (1 : ENNReal) else 0)
          * (S.next E (some (Silent.τ, t.1)) * t.1 t.2.1
              * ((innerWitness sys μ0 t.1).haltMass μ0 ⟨t.2.2.1, t.2.2.2⟩
                  / (t.1.bind id) (t.2.2.1.endState t.2.2.2)))
          * T t.2.1 (macroExtend E t.2.1)
              (dResidual ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
                ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩))
  rw [hre, ENNReal.tsum_prod']
  refine tsum_congr (fun ω => ?_)
  rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_left]
  refine tsum_congr (fun m' => ?_)
  rw [tsum_eq_single (⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ :
      {q : AlterSeq State Label // q.trans.Terminates}) ?_]
  · rw [if_pos ((segPre_nil_iff s0 ⟨ω, m', ⟨s0, Stream'.Seq.nil⟩,
        Stream'.Seq.terminates_nil⟩).mpr rfl)]
    rw [dResidual_nil_eq s0 _ rfl]
    rw [AlterSeq.endState_of_trans_nil (⟨s0, Stream'.Seq.nil⟩ : AlterSeq State Label) rfl
      Stream'.Seq.terminates_nil]
    ring
  · intro r hr
    rw [if_neg (fun hsp => hr (Subtype.ext ((segPre_nil_iff s0 _).mp hsp))), zero_mul, zero_mul]

/-- Dropping a terminating sequence's full length yields `nil`. -/
private theorem seq_drop_length_nil {α : Type} (s : Stream'.Seq α) (hs : s.Terminates) :
    s.drop (s.length hs) = Stream'.Seq.nil := by
  apply Stream'.Seq.ext
  intro m
  rw [Stream'.Seq.drop_get?]
  show s.get? _ = (Stream'.Seq.nil : Stream'.Seq α).get? m
  rw [show (Stream'.Seq.nil : Stream'.Seq α).get? m = none from rfl]
  have hlen : s.length hs = Nat.find hs := rfl
  exact Stream'.Seq.terminated_stable s (by omega) (Nat.find_spec hs)

/-- **Boundary peels are exactly the full-run peels.** -/
private theorem segBoundary_iff (e : {q : AlterSeq State Label // q.trans.Terminates})
    (seg : FlatSeg State Label) :
    (segPre e seg ∧ (dResidual e seg).1.trans = Stream'.Seq.nil) ↔ seg.run = e.1 := by
  constructor
  · rintro ⟨⟨hinit, happ⟩, hnil⟩
    have hd : e.1.trans.drop (seg.run.trans.length seg.runT) = Stream'.Seq.nil := hnil
    rw [hd, Stream'.Seq.append_nil] at happ
    calc seg.run = ⟨seg.run.init, seg.run.trans⟩ := rfl
      _ = ⟨e.1.init, e.1.trans⟩ := by rw [hinit, happ]
      _ = e.1 := rfl
  · intro hrun
    obtain ⟨emit, succ, run, runT⟩ := seg
    simp only at hrun
    subst hrun
    have hd : e.1.trans.drop (e.1.trans.length runT) = Stream'.Seq.nil :=
      seq_drop_length_nil e.1.trans runT
    exact ⟨⟨rfl, by rw [hd, Stream'.Seq.append_nil]⟩, hd⟩

/-- **The residual of a boundary peel** is the empty history at the parent's
end-state. -/
private theorem dResidual_boundary_eq (e : {q : AlterSeq State Label // q.trans.Terminates})
    (seg : FlatSeg State Label) (h : seg.run = e.1) :
    dResidual e seg
      = ⟨⟨e.1.endState e.2, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ := by
  obtain ⟨emit, succ, run, runT⟩ := seg
  simp only at h
  subst h
  apply Subtype.ext
  show (⟨e.1.endState runT, e.1.trans.drop (e.1.trans.length runT)⟩ : AlterSeq State Label)
    = ⟨e.1.endState e.2, Stream'.Seq.nil⟩
  rw [seq_drop_length_nil e.1.trans runT]

open Classical in
/-- **The boundary-peel collapse, `(ω, m')`-form.** The boundary seg-sum at a
history `e` collapses over the forced full run to the Bayes-coupled factor
`haltMass μ0 e / (ω.bind id) (e.end)` times a child carrier `T` at the empty
history rooted at `e.end`. -/
private theorem reset_collapse (S : WeakScheduler (𝒟(sys^w)))
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates})
    (T : PMF State → AlterSeq (PMF State) Label →
      {q : AlterSeq State Label // q.trans.Terminates} → ENNReal) :
    (∑' seg : FlatSeg State Label,
        (if segPre e seg ∧ (dResidual e seg).1.trans = Stream'.Seq.nil
            then (1 : ENNReal) else 0)
          * divHead S μ0 E seg
          * T seg.succ (macroExtend E seg.succ) (dResidual e seg))
      = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * ∑' m', ω m'
              * (((innerWitness sys μ0 ω).haltMass μ0 e / (ω.bind id) (e.1.endState e.2))
                * T m' (macroExtend E m')
                    ⟨⟨e.1.endState e.2, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩) := by
  have hre : (∑' seg : FlatSeg State Label,
      (if segPre e seg ∧ (dResidual e seg).1.trans = Stream'.Seq.nil
          then (1 : ENNReal) else 0)
        * divHead S μ0 E seg
        * T seg.succ (macroExtend E seg.succ) (dResidual e seg))
      = ∑' t : PMF (PMF State) × PMF State × {q : AlterSeq State Label // q.trans.Terminates},
          (if segPre e ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
              ∧ (dResidual e ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩).1.trans = Stream'.Seq.nil
            then (1 : ENNReal) else 0)
            * divHead S μ0 E ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
            * T t.2.1 (macroExtend E t.2.1) (dResidual e ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩) :=
    Equiv.tsum_eq flatSegEquiv
      (fun t : PMF (PMF State) × PMF State × {q : AlterSeq State Label // q.trans.Terminates} =>
        (if segPre e ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
            ∧ (dResidual e ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩).1.trans = Stream'.Seq.nil
          then (1 : ENNReal) else 0)
          * divHead S μ0 E ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
          * T t.2.1 (macroExtend E t.2.1) (dResidual e ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩))
  rw [hre, ENNReal.tsum_prod']
  refine tsum_congr (fun ω => ?_)
  rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_left]
  refine tsum_congr (fun m' => ?_)
  rw [tsum_eq_single e ?_]
  · rw [if_pos ((segBoundary_iff e ⟨ω, m', e.1, e.2⟩).mpr rfl),
      dResidual_boundary_eq e _ rfl]
    show (1 : ENNReal) * divHead S μ0 E ⟨ω, m', e.1, e.2⟩ * _ = _
    rw [divHead]
    show (1 : ENNReal) * (S.next E (some (Silent.τ, ω)) * ω m'
        * ((innerWitness sys μ0 ω).haltMass μ0 ⟨e.1, e.2⟩
            / (ω.bind id) (e.1.endState e.2))) * _ = _
    ring
  · intro r hr
    rw [if_neg (fun hP => hr (Subtype.ext ((segBoundary_iff e _).mp hP))), zero_mul, zero_mul]

/-- Dropping zero elements is the identity. -/
private theorem seq_drop_zero {α : Type} (s : Stream'.Seq α) : s.drop 0 = s := rfl

/-- **Stall peels at a general history are exactly the empty runs at its
initial state.** -/
private theorem segStall_iff (e : {q : AlterSeq State Label // q.trans.Terminates})
    (seg : FlatSeg State Label) :
    (segPre e seg ∧ seg.run.trans = Stream'.Seq.nil)
      ↔ seg.run = ⟨e.1.init, Stream'.Seq.nil⟩ := by
  constructor
  · rintro ⟨⟨hinit, _⟩, hnil⟩
    calc seg.run = ⟨seg.run.init, seg.run.trans⟩ := rfl
      _ = ⟨e.1.init, Stream'.Seq.nil⟩ := by rw [hinit, hnil]
  · intro hrun
    obtain ⟨emit, succ, run, runT⟩ := seg
    simp only at hrun
    subst hrun
    have hlen : (⟨e.1.init, Stream'.Seq.nil⟩ : AlterSeq State Label).trans.length runT = 0 :=
      Stream'.Seq.length_eq_zero.mpr rfl
    refine ⟨⟨rfl, ?_⟩, rfl⟩
    show Stream'.Seq.nil.append (e.1.trans.drop
      ((⟨e.1.init, Stream'.Seq.nil⟩ : AlterSeq State Label).trans.length runT)) = e.1.trans
    rw [hlen, seq_drop_zero, Stream'.Seq.nil_append]

/-- **The residual of a stall peel is the history itself.** -/
private theorem dResidual_stall_eq (e : {q : AlterSeq State Label // q.trans.Terminates})
    (seg : FlatSeg State Label) (h : seg.run = ⟨e.1.init, Stream'.Seq.nil⟩) :
    dResidual e seg = e := by
  obtain ⟨emit, succ, run, runT⟩ := seg
  simp only at h
  subst h
  have hlen : (⟨e.1.init, Stream'.Seq.nil⟩ : AlterSeq State Label).trans.length runT = 0 :=
    Stream'.Seq.length_eq_zero.mpr rfl
  apply Subtype.ext
  show (⟨(⟨e.1.init, Stream'.Seq.nil⟩ : AlterSeq State Label).endState runT,
      e.1.trans.drop ((⟨e.1.init, Stream'.Seq.nil⟩ : AlterSeq State Label).trans.length runT)⟩
      : AlterSeq State Label) = e.1
  rw [AlterSeq.endState_of_trans_nil (⟨e.1.init, Stream'.Seq.nil⟩ : AlterSeq State Label) rfl
    runT, hlen, seq_drop_zero]

open Classical in
/-- **The stall-peel collapse at a general history, `(ω, m')`-form.** The
empty-run stratum of the peel collapses to the Bayes-coupled stall factor at the
initial state times a child carrier `T` at the SAME history. -/
private theorem stall_peel_collapse (S : WeakScheduler (𝒟(sys^w)))
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates})
    (T : PMF State → AlterSeq (PMF State) Label →
      {q : AlterSeq State Label // q.trans.Terminates} → ENNReal) :
    (∑' seg : FlatSeg State Label,
        (if segPre e seg ∧ seg.run.trans = Stream'.Seq.nil then (1 : ENNReal) else 0)
          * divHead S μ0 E seg
          * T seg.succ (macroExtend E seg.succ) (dResidual e seg))
      = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * ∑' m', ω m'
              * (((innerWitness sys μ0 ω).haltMass μ0
                      ⟨⟨e.1.init, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
                    / (ω.bind id) e.1.init)
                * T m' (macroExtend E m') e) := by
  have hre : (∑' seg : FlatSeg State Label,
      (if segPre e seg ∧ seg.run.trans = Stream'.Seq.nil then (1 : ENNReal) else 0)
        * divHead S μ0 E seg
        * T seg.succ (macroExtend E seg.succ) (dResidual e seg))
      = ∑' t : PMF (PMF State) × PMF State × {q : AlterSeq State Label // q.trans.Terminates},
          (if segPre e ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
              ∧ (⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩ : FlatSeg State Label).run.trans
                  = Stream'.Seq.nil
            then (1 : ENNReal) else 0)
            * divHead S μ0 E ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
            * T t.2.1 (macroExtend E t.2.1) (dResidual e ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩) :=
    Equiv.tsum_eq flatSegEquiv
      (fun t : PMF (PMF State) × PMF State × {q : AlterSeq State Label // q.trans.Terminates} =>
        (if segPre e ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
            ∧ (⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩ : FlatSeg State Label).run.trans
                = Stream'.Seq.nil
          then (1 : ENNReal) else 0)
          * divHead S μ0 E ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
          * T t.2.1 (macroExtend E t.2.1) (dResidual e ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩))
  rw [hre, ENNReal.tsum_prod']
  refine tsum_congr (fun ω => ?_)
  rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_left]
  refine tsum_congr (fun m' => ?_)
  rw [tsum_eq_single (⟨⟨e.1.init, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ :
      {q : AlterSeq State Label // q.trans.Terminates}) ?_]
  · rw [if_pos ((segStall_iff e ⟨ω, m', ⟨e.1.init, Stream'.Seq.nil⟩,
        Stream'.Seq.terminates_nil⟩).mpr rfl),
      dResidual_stall_eq e _ rfl]
    show (1 : ENNReal) * divHead S μ0 E ⟨ω, m', ⟨e.1.init, Stream'.Seq.nil⟩,
        Stream'.Seq.terminates_nil⟩ * _ = _
    rw [divHead]
    show (1 : ENNReal) * (S.next E (some (Silent.τ, ω)) * ω m'
        * ((innerWitness sys μ0 ω).haltMass μ0
              ⟨⟨e.1.init, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
            / (ω.bind id) ((⟨e.1.init, Stream'.Seq.nil⟩ : AlterSeq State Label).endState
                Stream'.Seq.terminates_nil))) * _ = _
    rw [AlterSeq.endState_of_trans_nil (⟨e.1.init, Stream'.Seq.nil⟩ : AlterSeq State Label) rfl
      Stream'.Seq.terminates_nil]
    ring
  · intro r hr
    rw [if_neg (fun hP => hr (Subtype.ext ((segStall_iff e _).mp hP))), zero_mul, zero_mul]

/-- `segTrans` reconstructing `nil` forces an empty current prefix. -/
private theorem segTrans_nil_cur (segs : List (FlatSeg State Label))
    (c : Stream'.Seq (Label × State)) (h : segTrans segs c = Stream'.Seq.nil) :
    c = Stream'.Seq.nil := by
  induction segs with
  | nil => exact h
  | cons seg rest ih =>
    exact ih ((seq_append_eq_nil (show seg.run.trans.append (segTrans rest c)
      = Stream'.Seq.nil from h)).2)

open Classical in
/-- **The arrival carrier vanishes at empty histories**: every consistent
config has an empty current prefix, killed by the `curReachG` guard. -/
private theorem genW_arrG_nil (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) (h : e.1.trans = Stream'.Seq.nil) :
    genW (curReachG S) S src E e = 0 := by
  rw [genW]
  refine ENNReal.tsum_eq_zero.mpr (fun p => ?_)
  by_cases hdc : dConsistent e.1 ⟨p.1, p.2.1, p.2.2⟩
  · have hcur : p.2.1.trans = Stream'.Seq.nil :=
      segTrans_nil_cur p.1 p.2.1.trans (by rw [hdc.1, h])
    rw [show curReachG S (segSrc src p.1) (segHist E p.1) p.2 = 0 from by
      rw [curReachG, if_neg (fun hne => hne hcur)], mul_zero]
  · rw [if_neg hdc, zero_mul, zero_mul]

open Classical in
/-- **The halted-arrival carve at a nonempty history, additive form**:
`reachArrHalt + genW(dep) = genW(arrG)`. -/
private theorem rAH_add_dep (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) (hne : e.1.trans ≠ Stream'.Seq.nil) :
    reachArrHalt S μ0 E e + genW (depMove S) S μ0 E e = genW (curReachG S) S μ0 E e := by
  have hdep : (∑' p : Label × PMF State, reachDepM S μ0 E e p.1 p.2)
      = genW (depMove S) S μ0 E e := by
    rw [genW_eq_dconfig]
    simp_rw [reachDepM]
    rw [ENNReal.tsum_comm]
    exact tsum_congr (fun c => by rw [ENNReal.tsum_mul_left, moveSum_eq_depMove])
  rw [reachArrHalt, hdep, ← reachArrM_of_ne_nil S μ0 E e hne]
  refine tsub_add_cancel_of_le ?_
  rw [← hdep]
  exact reachDepM_sum_le S μ0 E e

open Classical in
/-- **The halted-arrival reach is dominated by the source at the initial
state.** -/
private theorem reachArrHalt_le_init (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) :
    reachArrHalt S μ0 E e ≤ μ0 e.1.init := by
  refine le_trans tsub_le_self ?_
  by_cases hnil : e.1.trans = Stream'.Seq.nil
  · rw [reachArrM, if_pos hnil]
  · rw [← probOf_eq_reachArrM S μ0 E e]
    exact ProbabilisticExecution.probOf_le_init _ _ _

open Classical in
/-- Group an execution-indexed sum by the initial state. -/
private theorem tsum_group_init
    (F : {q : AlterSeq State Label // q.trans.Terminates} → ENNReal) :
    (∑' e : {q : AlterSeq State Label // q.trans.Terminates}, F e)
      = ∑' t : State, ∑' e : {q : AlterSeq State Label // q.trans.Terminates},
          if e.1.init = t then F e else 0 := by
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun e => ?_)
  rw [tsum_eq_single e.1.init (fun t ht => if_neg (fun hh => ht hh.symm)), if_pos rfl]

open Classical in
/-- **The per-history additive peel identity (∗).** At a nonempty observed
history, the composite halt plus its boundary resets equals the current-run halt
plus the (stall + continuing) child halts one junction level deeper. -/
private theorem rAH_peel_identity (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) (hne : e.1.trans ≠ Stream'.Seq.nil) :
    reachArrHalt S μ0 E e
        + (∑' seg : FlatSeg State Label,
            (if segPre e seg ∧ (dResidual e seg).1.trans = Stream'.Seq.nil
              then (1 : ENNReal) else 0)
              * divHead S μ0 E seg
              * genW (fun s Ec c => depMove S s Ec c) S seg.succ (macroExtend E seg.succ)
                  (dResidual e seg))
      = haltReach S μ0 E e
        + ∑' seg : FlatSeg State Label,
            (if segPre e seg ∧ ¬ (dResidual e seg).1.trans = Stream'.Seq.nil
              then (1 : ENNReal) else 0)
              * divHead S μ0 E seg
              * reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg) := by
  have hd1 : genW (depMove S) S μ0 E e
      = depMove S μ0 E e
        + ((∑' seg : FlatSeg State Label,
              (if segPre e seg ∧ (dResidual e seg).1.trans = Stream'.Seq.nil
                then (1 : ENNReal) else 0)
                * divHead S μ0 E seg
                * genW (fun s Ec c => depMove S s Ec c) S seg.succ (macroExtend E seg.succ)
                    (dResidual e seg))
          + ∑' seg : FlatSeg State Label,
              (if segPre e seg ∧ ¬ (dResidual e seg).1.trans = Stream'.Seq.nil
                then (1 : ENNReal) else 0)
                * divHead S μ0 E seg
                * genW (fun s Ec c => depMove S s Ec c) S seg.succ (macroExtend E seg.succ)
                    (dResidual e seg)) := by
    rw [genW_peel (depMove S) S μ0 E e]
    congr 1
    rw [← ENNReal.tsum_add]
    refine tsum_congr (fun seg => ?_)
    simp only [divHead]
    by_cases hsp : segPre e seg
    · by_cases hrn : (dResidual e seg).1.trans = Stream'.Seq.nil
      · rw [if_pos hsp, if_pos ⟨hsp, hrn⟩, if_neg (fun h => h.2 hrn)]
        simp
      · rw [if_pos hsp, if_neg (fun h => hrn h.2), if_pos ⟨hsp, hrn⟩]
        simp
    · rw [if_neg hsp, if_neg (fun h => hsp h.1), if_neg (fun h => hsp h.1)]
      simp
  have hd2 : genW (curReachG S) S μ0 E e
      = curReach S μ0 E e
        + ((∑' seg : FlatSeg State Label,
              (if segPre e seg ∧ ¬ (dResidual e seg).1.trans = Stream'.Seq.nil
                then (1 : ENNReal) else 0)
                * divHead S μ0 E seg
                * reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg))
          + ∑' seg : FlatSeg State Label,
              (if segPre e seg ∧ ¬ (dResidual e seg).1.trans = Stream'.Seq.nil
                then (1 : ENNReal) else 0)
                * divHead S μ0 E seg
                * genW (fun s Ec c => depMove S s Ec c) S seg.succ (macroExtend E seg.succ)
                    (dResidual e seg)) := by
    rw [genW_peel (curReachG S) S μ0 E e]
    congr 1
    · show curReachG S μ0 E e = curReach S μ0 E e
      rw [curReachG, if_pos hne]
    rw [← ENNReal.tsum_add]
    refine tsum_congr (fun seg => ?_)
    simp only [divHead]
    by_cases hsp : segPre e seg
    · by_cases hrn : (dResidual e seg).1.trans = Stream'.Seq.nil
      · rw [if_pos hsp,
          if_neg (show ¬(segPre e seg ∧ ¬ (dResidual e seg).1.trans = Stream'.Seq.nil)
            from fun h => h.2 hrn),
          genW_arrG_nil S seg.succ (macroExtend E seg.succ) (dResidual e seg) hrn]
        simp
      · rw [if_pos hsp,
          if_pos (show segPre e seg ∧ ¬ (dResidual e seg).1.trans = Stream'.Seq.nil
            from ⟨hsp, hrn⟩),
          ← rAH_add_dep S seg.succ (macroExtend E seg.succ) (dResidual e seg) hrn]
        simp only [one_mul]
        ring
    · rw [if_neg hsp,
        if_neg (show ¬(segPre e seg ∧ ¬ (dResidual e seg).1.trans = Stream'.Seq.nil)
          from fun h => hsp h.1)]
      simp
  have hfinX : depMove S μ0 E e
      + (∑' seg : FlatSeg State Label,
          (if segPre e seg ∧ ¬ (dResidual e seg).1.trans = Stream'.Seq.nil
            then (1 : ENNReal) else 0)
            * divHead S μ0 E seg
            * genW (fun s Ec c => depMove S s Ec c) S seg.succ (macroExtend E seg.succ)
                (dResidual e seg)) ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
    · exact ne_top_of_le_ne_top ENNReal.one_ne_top
        ((depMove_le_init S μ0 E e).trans (PMF.coe_le_one _ _))
    · refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      calc (∑' seg : FlatSeg State Label,
              (if segPre e seg ∧ ¬ (dResidual e seg).1.trans = Stream'.Seq.nil
                then (1 : ENNReal) else 0)
                * divHead S μ0 E seg
                * genW (fun s Ec c => depMove S s Ec c) S seg.succ (macroExtend E seg.succ)
                    (dResidual e seg))
          ≤ genW (depMove S) S μ0 E e := by
            rw [hd1]
            exact le_add_self.trans (le_add_left le_rfl)
        _ ≤ genW (curReachG S) S μ0 E e := genDep_le_genArr S μ0 E e hne
        _ = reachArrM S μ0 E e := (reachArrM_of_ne_nil S μ0 E e hne).symm
        _ ≤ 1 := by
            rw [← probOf_eq_reachArrM S μ0 E e]
            exact (ProbabilisticExecution.probOf_le_init _ _ _).trans (PMF.coe_le_one _ _)
  have hchain : reachArrHalt S μ0 E e
      + (∑' seg : FlatSeg State Label,
          (if segPre e seg ∧ (dResidual e seg).1.trans = Stream'.Seq.nil
            then (1 : ENNReal) else 0)
            * divHead S μ0 E seg
            * genW (fun s Ec c => depMove S s Ec c) S seg.succ (macroExtend E seg.succ)
                (dResidual e seg))
      + (depMove S μ0 E e
        + (∑' seg : FlatSeg State Label,
            (if segPre e seg ∧ ¬ (dResidual e seg).1.trans = Stream'.Seq.nil
              then (1 : ENNReal) else 0)
              * divHead S μ0 E seg
              * genW (fun s Ec c => depMove S s Ec c) S seg.succ (macroExtend E seg.succ)
                  (dResidual e seg)))
      = (haltReach S μ0 E e
        + ∑' seg : FlatSeg State Label,
            (if segPre e seg ∧ ¬ (dResidual e seg).1.trans = Stream'.Seq.nil
              then (1 : ENNReal) else 0)
              * divHead S μ0 E seg
              * reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg))
      + (depMove S μ0 E e
        + (∑' seg : FlatSeg State Label,
            (if segPre e seg ∧ ¬ (dResidual e seg).1.trans = Stream'.Seq.nil
              then (1 : ENNReal) else 0)
              * divHead S μ0 E seg
              * genW (fun s Ec c => depMove S s Ec c) S seg.succ (macroExtend E seg.succ)
                  (dResidual e seg))) := by
    calc _ = reachArrHalt S μ0 E e + genW (depMove S) S μ0 E e := by rw [hd1]; ring
      _ = genW (curReachG S) S μ0 E e := rAH_add_dep S μ0 E e hne
      _ = curReach S μ0 E e + _ := hd2
      _ = depMove S μ0 E e + haltReach S μ0 E e + _ := by rw [curReach_split S μ0 E e]
      _ = _ := by ring
  exact le_antisymm
    ((ENNReal.add_le_add_iff_right hfinX).mp (le_of_eq hchain))
    ((ENNReal.add_le_add_iff_right hfinX).mp (le_of_eq hchain.symm))

open Classical in
/-- **The child nonempty-halt fiber** at landing state `t`. -/
private noncomputable def childNEfib (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (m' : PMF State) (F : AlterSeq (PMF State) Label) (t : State) : ENNReal :=
  ∑' e' : {q : AlterSeq State Label // q.trans.Terminates},
    if e'.1.init = t then
      (if e'.1.trans = Stream'.Seq.nil then 0
        else reachArrHalt S m' F e' * g (e'.1.endState e'.2))
    else 0

open Classical in
/-- The fibers exhaust the child nonempty-halt integral. -/
private theorem childNEfib_total (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (m' : PMF State) (F : AlterSeq (PMF State) Label) :
    (∑' t : State, childNEfib S g m' F t)
      = ∑' e' : {q : AlterSeq State Label // q.trans.Terminates},
          if e'.1.trans = Stream'.Seq.nil then 0
          else reachArrHalt S m' F e' * g (e'.1.endState e'.2) :=
  (tsum_group_init (fun e' =>
    if e'.1.trans = Stream'.Seq.nil then 0
    else reachArrHalt S m' F e' * g (e'.1.endState e'.2))).symm

open Classical in
/-- A fiber at a source-null landing state vanishes. -/
private theorem childNEfib_zero (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (m' : PMF State) (F : AlterSeq (PMF State) Label) (t : State) (h : m' t = 0) :
    childNEfib S g m' F t = 0 := by
  rw [childNEfib]
  refine ENNReal.tsum_eq_zero.mpr (fun e' => ?_)
  split_ifs with h1 h2
  · rfl
  · have h0 : reachArrHalt S m' F e' = 0 := by
      have hle := reachArrHalt_le_init S m' F e'
      rw [h1, h] at hle
      exact le_antisymm hle zero_le'
    rw [h0, zero_mul]
  · rfl

open Classical in
/-- **The exact junction fiber collapse.** Per emission (on the step
support) and per child, the stall-weighted child halts at the SAME history plus
the W1-collapsed nonempty-head child halts recombine EXACTLY into the child
nonempty-halt integral: the two Bayes weights sum to `(ω.bind id) t / (ω.bind
id) t`, which is `1` where it matters and `0` exactly where the child fiber
vanishes. -/
private theorem fiber_collapse (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label) (ω : PMF (PMF State)) (m' : PMF State)
    (hstep : (𝒟(sys^w)).step μ0 Silent.τ ω)
    (hm : ∀ t : State, (ω.bind id) t = 0 → m' t = 0) :
    (∑' e : {q : AlterSeq State Label // q.trans.Terminates},
        if e.1.trans = Stream'.Seq.nil then 0
        else ((innerWitness sys μ0 ω).haltMass μ0
                ⟨⟨e.1.init, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
              / (ω.bind id) e.1.init)
          * (reachArrHalt S m' (macroExtend E m') e * g (e.1.endState e.2)))
      + (∑' r : {q : AlterSeq State Label // q.trans.Terminates},
          if r.1.trans = Stream'.Seq.nil then 0
          else ((innerWitness sys μ0 ω).haltMass μ0 r / (ω.bind id) (r.1.endState r.2))
            * childNEfib S g m' (macroExtend E m') (r.1.endState r.2))
      = ∑' e' : {q : AlterSeq State Label // q.trans.Terminates},
          if e'.1.trans = Stream'.Seq.nil then 0
          else reachArrHalt S m' (macroExtend E m') e' * g (e'.1.endState e'.2) := by
  -- the stall side is the nil-`r` stratum of the same `r`-sum
  have hstall : (∑' e : {q : AlterSeq State Label // q.trans.Terminates},
      if e.1.trans = Stream'.Seq.nil then 0
      else ((innerWitness sys μ0 ω).haltMass μ0
              ⟨⟨e.1.init, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
            / (ω.bind id) e.1.init)
        * (reachArrHalt S m' (macroExtend E m') e * g (e.1.endState e.2)))
      = ∑' r : {q : AlterSeq State Label // q.trans.Terminates},
          if r.1.trans = Stream'.Seq.nil
            then ((innerWitness sys μ0 ω).haltMass μ0 r / (ω.bind id) (r.1.endState r.2))
              * childNEfib S g m' (macroExtend E m') (r.1.endState r.2)
            else 0 := by
    rw [tsum_nil_reindex (fun r =>
      ((innerWitness sys μ0 ω).haltMass μ0 r / (ω.bind id) (r.1.endState r.2))
        * childNEfib S g m' (macroExtend E m') (r.1.endState r.2))]
    rw [tsum_group_init (fun e =>
      if e.1.trans = Stream'.Seq.nil then 0
      else ((innerWitness sys μ0 ω).haltMass μ0
              ⟨⟨e.1.init, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
            / (ω.bind id) e.1.init)
        * (reachArrHalt S m' (macroExtend E m') e * g (e.1.endState e.2)))]
    refine tsum_congr (fun t => ?_)
    have hend : (⟨t, Stream'.Seq.nil⟩ : AlterSeq State Label).endState
        Stream'.Seq.terminates_nil = t :=
      AlterSeq.endState_of_trans_nil (⟨t, Stream'.Seq.nil⟩ : AlterSeq State Label) rfl
        Stream'.Seq.terminates_nil
    rw [hend, childNEfib, ← ENNReal.tsum_mul_left]
    refine tsum_congr (fun e => ?_)
    by_cases hi : e.1.init = t
    · rw [if_pos hi]
      split_ifs with h2
      · rw [mul_zero]
      · rw [hi]
    · rw [if_neg hi, if_neg hi, mul_zero]
  rw [hstall, ← ENNReal.tsum_add,
    show (∑' r : {q : AlterSeq State Label // q.trans.Terminates},
        ((if r.1.trans = Stream'.Seq.nil
            then ((innerWitness sys μ0 ω).haltMass μ0 r / (ω.bind id) (r.1.endState r.2))
              * childNEfib S g m' (macroExtend E m') (r.1.endState r.2)
            else 0)
          + (if r.1.trans = Stream'.Seq.nil then 0
              else ((innerWitness sys μ0 ω).haltMass μ0 r / (ω.bind id) (r.1.endState r.2))
                * childNEfib S g m' (macroExtend E m') (r.1.endState r.2))))
      = ∑' r : {q : AlterSeq State Label // q.trans.Terminates},
          ((innerWitness sys μ0 ω).haltMass μ0 r / (ω.bind id) (r.1.endState r.2))
            * childNEfib S g m' (macroExtend E m') (r.1.endState r.2) from
    tsum_congr (fun r => by split_ifs <;> simp), ← childNEfib_total S g m' (macroExtend E m')]
  calc (∑' r : {q : AlterSeq State Label // q.trans.Terminates},
          ((innerWitness sys μ0 ω).haltMass μ0 r / (ω.bind id) (r.1.endState r.2))
            * childNEfib S g m' (macroExtend E m') (r.1.endState r.2))
      = ∑' r : {q : AlterSeq State Label // q.trans.Terminates}, ∑' t : State,
          (if r.1.endState r.2 = t then
            (innerWitness sys μ0 ω).haltMass μ0 r
              * (((ω.bind id) t)⁻¹ * childNEfib S g m' (macroExtend E m') t)
          else 0) := by
        refine tsum_congr (fun r => ?_)
        rw [tsum_eq_single (r.1.endState r.2) (fun t ht => if_neg (fun h => ht h.symm)),
          if_pos rfl, div_eq_mul_inv, mul_assoc]
    _ = ∑' t : State,
          (((ω.bind id) t)⁻¹ * childNEfib S g m' (macroExtend E m') t) * (ω.bind id) t := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr (fun t => ?_)
        rw [innerWitness_pushforward hstep t, ← ENNReal.tsum_mul_left]
        refine tsum_congr (fun r => ?_)
        split_ifs with h
        · rw [mul_one]; ring
        · rw [mul_zero, mul_zero]
    _ = ∑' t : State, childNEfib S g m' (macroExtend E m') t := by
        refine tsum_congr (fun t => ?_)
        by_cases hb : (ω.bind id) t = 0
        · rw [hb, mul_zero, childNEfib_zero S g m' (macroExtend E m') t (hm t hb)]
        · rw [show (((ω.bind id) t)⁻¹ * childNEfib S g m' (macroExtend E m') t) * (ω.bind id) t
              = (((ω.bind id) t)⁻¹ * (ω.bind id) t)
                * childNEfib S g m' (macroExtend E m') t from by ring,
            ENNReal.inv_mul_cancel hb
              (ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one _ _)),
            one_mul]
open Classical in
/-- **The stall-junction nil-halt average** (`stallNil`): per emission `ω`
and landing state `s0`, the Bayes-coupled stall factor
`haltMass μ0 ⟨s0,nil⟩ / (ω.bind id) s0` times the junction average of the CHILD
nil-history halts at the same state, `g`-weighted. The resolvent one-step term
of the nil-halt carve. -/
private noncomputable def stallNil (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label) : ENNReal :=
  ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
    * ∑' s0 : State,
        ((innerWitness sys μ0 ω).haltMass μ0
              ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
            / (ω.bind id) s0)
          * (∑' m', ω m' * reachArrHalt S m' (macroExtend E m')
              ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩)
          * g s0

open Classical in
/-- **The nil-halt stall resolvent.** The nil-history halt carve unfolds one
macro level: halt now against the source, or stall (Bayes-coupled empty inner
run) and halt at the same state one macro level deeper. -/
private theorem nilHalt_resolvent (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) (hinv : μ0 = E.endState hT) :
    (∑' s0 : State,
        reachArrHalt S μ0 E ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0)
      = S.next E none * (∑' s, μ0 s * g s) + stallNil S g μ0 E := by
  have hpt : ∀ s0 : State,
      reachArrHalt S μ0 E ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
        = S.next E none * μ0 s0
          + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
              * ∑' m', ω m'
                  * (((innerWitness sys μ0 ω).haltMass μ0
                          ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
                        / (ω.bind id) s0)
                    * reachArrHalt S m' (macroExtend E m')
                        ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩) := by
    intro s0
    set r0 : {q : AlterSeq State Label // q.trans.Terminates} :=
      ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ with hr0
    set sf : PMF (PMF State) → ENNReal :=
      fun ω => (innerWitness sys μ0 ω).haltMass μ0 r0 / (ω.bind id) s0 with hsf
    set X := (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
        * ∑' m', ω m' * (sf ω * reachArrHalt S m' (macroExtend E m') r0)) with hX
    set Y := (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
        * ∑' m', ω m' * (sf ω * genW (depMove S) S m' (macroExtend E m') r0)) with hY
    have hP : genW (depMove S) S μ0 E r0
        = depMove S μ0 E r0 + Y := by
      rw [genW_peel (depMove S) S μ0 E r0]
      congr 1
      exact nil_peel_collapse S μ0 E s0
        (fun s Ec c => genW (depMove S) S s Ec c)
    have hbind : ∀ ω : PMF (PMF State), (∑' m', ω m' * m' s0) = (ω.bind id) s0 := by
      intro ω
      rw [PMF.bind_apply]
      exact tsum_congr (fun m' => by rw [id_eq])
    have hXY : X + Y = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
        * (sf ω * (ω.bind id) s0) := by
      rw [hX, hY, ← ENNReal.tsum_add]
      refine tsum_congr (fun ω => ?_)
      rw [← mul_add]
      congr 1
      rw [← ENNReal.tsum_add,
        show (∑' m', (ω m' * (sf ω * reachArrHalt S m' (macroExtend E m') r0)
              + ω m' * (sf ω * genW (depMove S) S m' (macroExtend E m') r0)))
            = ∑' m', sf ω * (ω m' * m' s0) from
          tsum_congr (fun m' => by
            rw [← mul_add, ← mul_add, reachArrHalt_nil_add S m' (macroExtend E m') s0]
            ring),
        ENNReal.tsum_mul_left, hbind ω]
    have hhr : haltReach S μ0 E r0
        = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * (innerWitness sys μ0 ω).haltMass μ0 r0 := by
      rw [haltReach]
      refine tsum_congr (fun ω => ?_)
      unfold WeakScheduler.haltMass Scheduler.haltMass
      rw [mul_assoc]
    have hHR : (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
        * (sf ω * (ω.bind id) s0)) = haltReach S μ0 E r0 := by
      rw [hhr]
      refine tsum_congr (fun ω => ?_)
      by_cases hw : S.next E (some (Silent.τ, ω)) = 0
      · rw [hw, zero_mul, zero_mul]
      · congr 1
        have hstep : (𝒟(sys^w)).step μ0 Silent.τ ω := by
          rw [hinv]
          exact S.valid E (Nat.find hT) (E.endState hT) (Nat.find_spec hT)
            (AlterSeq.stateAt_find_eq_endState E hT) Silent.τ ω
            ((PMF.mem_support_iff _ _).mpr hw)
        by_cases hb : (ω.bind id) s0 = 0
        · have h0 : (innerWitness sys μ0 ω).haltMass μ0 r0 = 0 := by
            have hle : (innerWitness sys μ0 ω).haltMass μ0 r0 ≤ (ω.bind id) s0 := by
              rw [innerWitness_pushforward hstep s0]
              refine le_trans (le_of_eq ?_) (ENNReal.le_tsum r0)
              rw [if_pos (AlterSeq.endState_of_trans_nil
                (⟨s0, Stream'.Seq.nil⟩ : AlterSeq State Label) rfl
                Stream'.Seq.terminates_nil), mul_one]
            rw [hb] at hle
            exact le_antisymm hle zero_le'
          rw [hsf]
          simp only [h0, ENNReal.zero_div, zero_mul]
        · have hbtop : (ω.bind id) s0 ≠ ⊤ :=
            ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one _ _)
          rw [hsf]
          exact ENNReal.div_mul_cancel hb hbtop
    have hcur : curReach S μ0 E r0
        = (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))) * μ0 s0 := by
      rw [curReach, ← ENNReal.tsum_mul_right]
      refine tsum_congr (fun ω => ?_)
      rw [ProbabilisticExecution.probOf_nil]
      rfl
    have hv : μ0 s0 = S.next E none * μ0 s0 + depMove S μ0 E r0 + haltReach S μ0 E r0 := by
      calc μ0 s0
          = (S.next E none + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))) * μ0 s0 := by
            rw [macroTot, one_mul]
        _ = S.next E none * μ0 s0 + curReach S μ0 E r0 := by rw [add_mul, hcur]
        _ = S.next E none * μ0 s0 + (depMove S μ0 E r0 + haltReach S μ0 E r0) := by
            rw [curReach_split S μ0 E r0]
        _ = S.next E none * μ0 s0 + depMove S μ0 E r0 + haltReach S μ0 E r0 := by ring
    have hfin2 : depMove S μ0 E r0 + Y ≠ ⊤ := by
      refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
      · exact ne_top_of_le_ne_top ENNReal.one_ne_top
          ((depMove_le_init S μ0 E r0).trans (PMF.coe_le_one _ _))
      · refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
        calc Y ≤ X + Y := le_add_self
          _ = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
              * (sf ω * (ω.bind id) s0) := hXY
          _ = haltReach S μ0 E r0 := hHR
          _ ≤ curReach S μ0 E r0 := by rw [curReach_split S μ0 E r0]; exact le_add_self
          _ = (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))) * μ0 s0 := hcur
          _ ≤ 1 * 1 := mul_le_mul' (macroSome_le_one S E) (PMF.coe_le_one _ _)
          _ = 1 := one_mul _
    have hchain : reachArrHalt S μ0 E r0 + (depMove S μ0 E r0 + Y)
        = (S.next E none * μ0 s0 + X) + (depMove S μ0 E r0 + Y) := by
      calc reachArrHalt S μ0 E r0 + (depMove S μ0 E r0 + Y)
          = reachArrHalt S μ0 E r0 + genW (depMove S) S μ0 E r0 := by rw [hP]
        _ = μ0 s0 := reachArrHalt_nil_add S μ0 E s0
        _ = S.next E none * μ0 s0 + depMove S μ0 E r0 + haltReach S μ0 E r0 := hv
        _ = S.next E none * μ0 s0 + depMove S μ0 E r0 + (X + Y) := by rw [hXY, hHR]
        _ = (S.next E none * μ0 s0 + X) + (depMove S μ0 E r0 + Y) := by ring
    exact le_antisymm
      ((ENNReal.add_le_add_iff_right hfin2).mp (le_of_eq hchain))
      ((ENNReal.add_le_add_iff_right hfin2).mp (le_of_eq hchain.symm))
  rw [tsum_congr (fun s0 => by rw [hpt s0, add_mul]), ENNReal.tsum_add]
  congr 1
  · rw [← ENNReal.tsum_mul_left]
    exact tsum_congr (fun s0 => by rw [mul_assoc])
  · rw [stallNil]
    rw [show (∑' s0 : State, (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * ∑' m', ω m'
              * (((innerWitness sys μ0 ω).haltMass μ0
                      ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
                    / (ω.bind id) s0)
                * reachArrHalt S m' (macroExtend E m')
                    ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩)) * g s0)
        = ∑' s0 : State, ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * (((innerWitness sys μ0 ω).haltMass μ0
                    ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
                  / (ω.bind id) s0)
                * (∑' m', ω m' * reachArrHalt S m' (macroExtend E m')
                    ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩)
                * g s0) from
      tsum_congr (fun s0 => by
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr (fun ω => ?_)
        rw [show (∑' m', ω m'
              * (((innerWitness sys μ0 ω).haltMass μ0
                      ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
                    / (ω.bind id) s0)
                  * reachArrHalt S m' (macroExtend E m')
                      ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩))
            = ((innerWitness sys μ0 ω).haltMass μ0
                  ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
                / (ω.bind id) s0)
              * ∑' m', ω m' * reachArrHalt S m' (macroExtend E m')
                  ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ from by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr (fun m' => by ring)]
        ring)]
    rw [ENNReal.tsum_comm]
    exact tsum_congr (fun ω => ENNReal.tsum_mul_left)

open Classical in
/-- **The exact nonempty-history junction identity.** The junction collapse is
exact: the nonempty-history halt-reach integral plus the resets equals the
boundary halt integral plus the emission-averaged child nonempty-history
halt-reach integral. The nil-run mass (weight `haltMass ⟨t,nil⟩/(ω.bind id) t`
per landing state) is filled precisely by the stall peels (empty-run heads),
since the witness mass runs over ALL runs: `W(ω,t) + sf(ω,t) = 1`. -/
private theorem renewal_NE_identity (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (hg : ∀ x, g x ≤ 1)
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) (hinv : μ0 = E.endState hT) :
    (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          if e.1.trans = Stream'.Seq.nil then 0
          else reachArrHalt S μ0 E e * g (e.1.endState e.2))
        + resetSum S g μ0 E
      = bHaltSum S g μ0 E
        + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m' * (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
                if e.1.trans = Stream'.Seq.nil then 0
                else reachArrHalt S m' (macroExtend E m') e * g (e.1.endState e.2)) := by
  classical
  -- Step 1 — merge via the per-history identity (∗): LHS = bHaltSum + T.
  have hmerge : (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        if e.1.trans = Stream'.Seq.nil then 0
        else reachArrHalt S μ0 E e * g (e.1.endState e.2))
      + resetSum S g μ0 E
      = bHaltSum S g μ0 E
        + ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
            if e.1.trans = Stream'.Seq.nil then 0
            else (∑' seg : FlatSeg State Label,
                (if segPre e seg ∧ ¬ (dResidual e seg).1.trans = Stream'.Seq.nil
                  then (1 : ENNReal) else 0)
                  * divHead S μ0 E seg
                  * reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg))
              * g (e.1.endState e.2) := by
    rw [resetSum, bHaltSum, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine tsum_congr (fun e => ?_)
    split_ifs with hnil
    · simp
    · rw [← add_mul, ← add_mul, rAH_peel_identity S μ0 E e hnil]
  rw [hmerge]
  congr 1
  -- Step 2 — T = JNE via the run-strata split and the fiber collapse.
  -- per-`(e, seg)` strata split (stall heads vs continuing nonempty heads)
  have hsplit : ∀ (e : {q : AlterSeq State Label // q.trans.Terminates}),
      ¬ e.1.trans = Stream'.Seq.nil →
      ∀ seg : FlatSeg State Label,
      (if segPre e seg ∧ ¬ (dResidual e seg).1.trans = Stream'.Seq.nil
          then (1 : ENNReal) else 0)
          * divHead S μ0 E seg
          * reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg)
          * g (e.1.endState e.2)
        = ((if segPre e seg ∧ seg.run.trans = Stream'.Seq.nil then (1 : ENNReal) else 0)
            * divHead S μ0 E seg
            * reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg)
            * g (e.1.endState e.2))
          + (if seg.run.trans = Stream'.Seq.nil then 0
              else divHead S μ0 E seg
                * (if segPre e seg then
                    (if (dResidual e seg).1.trans = Stream'.Seq.nil then 0
                      else reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg)
                        * g ((dResidual e seg).1.endState (dResidual e seg).2))
                  else 0)) := by
    intro e hne seg
    by_cases hsp : segPre e seg
    · by_cases hrun : seg.run.trans = Stream'.Seq.nil
      · have hres : dResidual e seg = e :=
          dResidual_stall_eq e seg ((segStall_iff e seg).mp ⟨hsp, hrun⟩)
        rw [if_pos ⟨hsp, by rw [hres]; exact hne⟩, if_pos ⟨hsp, hrun⟩, if_pos hrun]
        simp
      · by_cases hrn : (dResidual e seg).1.trans = Stream'.Seq.nil
        · rw [if_neg (fun h => h.2 hrn), if_neg (fun h => hrun h.2), if_neg hrun,
            if_pos hsp, if_pos hrn]
          simp
        · rw [if_pos ⟨hsp, hrn⟩, if_neg (fun h => hrun h.2), if_neg hrun, if_pos hsp,
            if_neg hrn, dResidual_endState e seg hsp]
          simp
          ring
    · rw [if_neg (fun h => hsp h.1), if_neg (fun h => hsp h.1), if_neg hsp]
      split_ifs <;> simp
  -- push `g` into the segment sum, apply the strata split, and separate the sums
  have hTsplit : (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        if e.1.trans = Stream'.Seq.nil then 0
        else (∑' seg : FlatSeg State Label,
            (if segPre e seg ∧ ¬ (dResidual e seg).1.trans = Stream'.Seq.nil
              then (1 : ENNReal) else 0)
              * divHead S μ0 E seg
              * reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg))
          * g (e.1.endState e.2))
      = (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          if e.1.trans = Stream'.Seq.nil then 0
          else ∑' seg : FlatSeg State Label,
            (if segPre e seg ∧ seg.run.trans = Stream'.Seq.nil then (1 : ENNReal) else 0)
              * divHead S μ0 E seg
              * reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg)
              * g (e.1.endState e.2))
        + ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
            ∑' seg : FlatSeg State Label,
              (if seg.run.trans = Stream'.Seq.nil then 0
                else divHead S μ0 E seg
                  * (if segPre e seg then
                      (if (dResidual e seg).1.trans = Stream'.Seq.nil then 0
                        else reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg)
                          * g ((dResidual e seg).1.endState (dResidual e seg).2))
                    else 0)) := by
    rw [← ENNReal.tsum_add]
    refine tsum_congr (fun e => ?_)
    by_cases hnil : e.1.trans = Stream'.Seq.nil
    · rw [if_pos hnil, if_pos hnil, zero_add]
      refine (ENNReal.tsum_eq_zero.mpr (fun seg => ?_)).symm
      by_cases hrun : seg.run.trans = Stream'.Seq.nil
      · rw [if_pos hrun]
      · rw [if_neg hrun]
        have hns : ¬ segPre e seg := by
          rintro ⟨hinit, happ⟩
          rw [hnil] at happ
          exact hrun (seq_append_eq_nil happ).1
        rw [if_neg hns, mul_zero]
    · rw [if_neg hnil, if_neg hnil, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
      exact tsum_congr (fun seg => hsplit e hnil seg)
  rw [hTsplit]
  -- stall stratum: collapse per history via `stall_peel_collapse`
  have hTstall : (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        if e.1.trans = Stream'.Seq.nil then 0
        else ∑' seg : FlatSeg State Label,
          (if segPre e seg ∧ seg.run.trans = Stream'.Seq.nil then (1 : ENNReal) else 0)
            * divHead S μ0 E seg
            * reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg)
            * g (e.1.endState e.2))
      = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * ∑' m', ω m'
              * ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
                  (if e.1.trans = Stream'.Seq.nil then 0
                    else ((innerWitness sys μ0 ω).haltMass μ0
                            ⟨⟨e.1.init, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
                          / (ω.bind id) e.1.init)
                      * (reachArrHalt S m' (macroExtend E m') e * g (e.1.endState e.2))) := by
    have hpt : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
        (if e.1.trans = Stream'.Seq.nil then 0
          else ∑' seg : FlatSeg State Label,
            (if segPre e seg ∧ seg.run.trans = Stream'.Seq.nil then (1 : ENNReal) else 0)
              * divHead S μ0 E seg
              * reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg)
              * g (e.1.endState e.2))
        = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m'
                * (if e.1.trans = Stream'.Seq.nil then 0
                    else ((innerWitness sys μ0 ω).haltMass μ0
                            ⟨⟨e.1.init, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
                          / (ω.bind id) e.1.init)
                      * (reachArrHalt S m' (macroExtend E m') e * g (e.1.endState e.2))) := by
      intro e
      split_ifs with hnil
      · simp
      · calc (∑' seg : FlatSeg State Label,
              (if segPre e seg ∧ seg.run.trans = Stream'.Seq.nil then (1 : ENNReal) else 0)
                * divHead S μ0 E seg
                * reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg)
                * g (e.1.endState e.2))
            = (∑' seg : FlatSeg State Label,
                (if segPre e seg ∧ seg.run.trans = Stream'.Seq.nil then (1 : ENNReal) else 0)
                  * divHead S μ0 E seg
                  * reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg))
                * g (e.1.endState e.2) := ENNReal.tsum_mul_right
          _ = (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
                * ∑' m', ω m'
                    * (((innerWitness sys μ0 ω).haltMass μ0
                            ⟨⟨e.1.init, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
                          / (ω.bind id) e.1.init)
                      * reachArrHalt S m' (macroExtend E m') e))
                * g (e.1.endState e.2) := by
              congr 1
              exact stall_peel_collapse S μ0 E e (fun s F r => reachArrHalt S s F r)
          _ = _ := by
              rw [← ENNReal.tsum_mul_right]
              refine tsum_congr (fun ω => ?_)
              rw [mul_assoc]
              congr 1
              rw [← ENNReal.tsum_mul_right]
              refine tsum_congr (fun m' => ?_)
              ring
    rw [tsum_congr hpt, ENNReal.tsum_comm]
    refine tsum_congr (fun ω => ?_)
    rw [ENNReal.tsum_mul_left]
    congr 1
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun m' => ?_)
    rw [ENNReal.tsum_mul_left]
  -- move stratum: reindex over the peeled head and collapse the fiber
  have hTmove : (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        ∑' seg : FlatSeg State Label,
          (if seg.run.trans = Stream'.Seq.nil then 0
            else divHead S μ0 E seg
              * (if segPre e seg then
                  (if (dResidual e seg).1.trans = Stream'.Seq.nil then 0
                    else reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg)
                      * g ((dResidual e seg).1.endState (dResidual e seg).2))
                else 0)))
      = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * ∑' m', ω m'
              * ∑' r : {q : AlterSeq State Label // q.trans.Terminates},
                  (if r.1.trans = Stream'.Seq.nil then 0
                    else ((innerWitness sys μ0 ω).haltMass μ0 r
                        / (ω.bind id) (r.1.endState r.2))
                      * childNEfib S g m' (macroExtend E m') (r.1.endState r.2)) := by
    rw [ENNReal.tsum_comm]
    have hseg : ∀ seg : FlatSeg State Label,
        (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          (if seg.run.trans = Stream'.Seq.nil then 0
            else divHead S μ0 E seg
              * (if segPre e seg then
                  (if (dResidual e seg).1.trans = Stream'.Seq.nil then 0
                    else reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg)
                      * g ((dResidual e seg).1.endState (dResidual e seg).2))
                else 0)))
        = if seg.run.trans = Stream'.Seq.nil then 0
            else divHead S μ0 E seg
              * childNEfib S g seg.succ (macroExtend E seg.succ)
                  (seg.run.endState seg.runT) := by
      intro seg
      by_cases hrun : seg.run.trans = Stream'.Seq.nil
      · rw [if_pos hrun]
        refine ENNReal.tsum_eq_zero.mpr (fun e => ?_)
        rw [if_pos hrun]
      · rw [if_neg hrun,
          show (∑' e : {q : AlterSeq State Label // q.trans.Terminates},
              (if seg.run.trans = Stream'.Seq.nil then 0
                else divHead S μ0 E seg
                  * (if segPre e seg then
                      (if (dResidual e seg).1.trans = Stream'.Seq.nil then 0
                        else reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg)
                          * g ((dResidual e seg).1.endState (dResidual e seg).2))
                    else 0)))
            = ∑' e : {q : AlterSeq State Label // q.trans.Terminates},
                divHead S μ0 E seg
                  * (if segPre e seg then
                      (if (dResidual e seg).1.trans = Stream'.Seq.nil then 0
                        else reachArrHalt S seg.succ (macroExtend E seg.succ) (dResidual e seg)
                          * g ((dResidual e seg).1.endState (dResidual e seg).2))
                    else 0) from
          tsum_congr (fun e => by rw [if_neg hrun]), ENNReal.tsum_mul_left]
        congr 1
        exact segPre_reindex seg (fun e' =>
          if e'.1.trans = Stream'.Seq.nil then 0
          else reachArrHalt S seg.succ (macroExtend E seg.succ) e' * g (e'.1.endState e'.2))
    rw [tsum_congr hseg,
      show (∑' seg : FlatSeg State Label,
          (if seg.run.trans = Stream'.Seq.nil then 0
            else divHead S μ0 E seg
              * childNEfib S g seg.succ (macroExtend E seg.succ)
                  (seg.run.endState seg.runT)))
        = ∑' t : PMF (PMF State) × PMF State × {q : AlterSeq State Label // q.trans.Terminates},
            (if t.2.2.1.trans = Stream'.Seq.nil then 0
              else divHead S μ0 E ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
                * childNEfib S g t.2.1 (macroExtend E t.2.1)
                    (t.2.2.1.endState t.2.2.2)) from
      Equiv.tsum_eq flatSegEquiv
        (fun t : PMF (PMF State) × PMF State ×
            {q : AlterSeq State Label // q.trans.Terminates} =>
          (if t.2.2.1.trans = Stream'.Seq.nil then 0
            else divHead S μ0 E ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
              * childNEfib S g t.2.1 (macroExtend E t.2.1)
                  (t.2.2.1.endState t.2.2.2))), ENNReal.tsum_prod']
    refine tsum_congr (fun ω => ?_)
    rw [ENNReal.tsum_prod',
      show (∑' m' : PMF State,
          ∑' r : {q : AlterSeq State Label // q.trans.Terminates},
            (if r.1.trans = Stream'.Seq.nil then 0
              else divHead S μ0 E ⟨ω, m', r.1, r.2⟩
                * childNEfib S g m' (macroExtend E m') (r.1.endState r.2)))
        = ∑' m' : PMF State, S.next E (some (Silent.τ, ω))
            * (ω m' * ∑' r : {q : AlterSeq State Label // q.trans.Terminates},
                (if r.1.trans = Stream'.Seq.nil then 0
                  else ((innerWitness sys μ0 ω).haltMass μ0 r
                      / (ω.bind id) (r.1.endState r.2))
                    * childNEfib S g m' (macroExtend E m') (r.1.endState r.2))) from
      tsum_congr (fun m' => by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        refine tsum_congr (fun r => ?_)
        split_ifs with h
        · simp
        · simp only [divHead]
          ring), ENNReal.tsum_mul_left]
  rw [hTstall, hTmove, ← ENNReal.tsum_add]
  refine tsum_congr (fun ω => ?_)
  by_cases hw : S.next E (some (Silent.τ, ω)) = 0
  · rw [hw, zero_mul, zero_mul, zero_mul, add_zero]
  · rw [← mul_add]
    congr 1
    have hstep : (𝒟(sys^w)).step μ0 Silent.τ ω := by
      rw [hinv]
      exact S.valid E (Nat.find hT) (E.endState hT) (Nat.find_spec hT)
        (AlterSeq.stateAt_find_eq_endState E hT) Silent.τ ω
        ((PMF.mem_support_iff _ _).mpr hw)
    rw [← ENNReal.tsum_add]
    refine tsum_congr (fun m' => ?_)
    by_cases hm0 : ω m' = 0
    · rw [hm0, zero_mul, zero_mul, zero_mul, add_zero]
    · rw [← mul_add]
      congr 1
      refine fiber_collapse S g μ0 E ω m' hstep (fun t hb => ?_)
      have hb' : (∑' m'', ω m'' * m'' t) = 0 := by
        rw [show (∑' m'', ω m'' * m'' t) = (ω.bind id) t from by
          rw [PMF.bind_apply]; exact tsum_congr (fun m'' => by rw [id_eq]), hb]
      exact (mul_eq_zero.mp (ENNReal.tsum_eq_zero.mp hb' m')).resolve_left hm0

/-- `x / c * c ≤ x` unconditionally in `ENNReal` (the W2 cancellation). -/
private theorem ennreal_div_mul_le (x c : ENNReal) : x / c * c ≤ x := by
  rcases eq_or_ne c 0 with hc | hc
  · simp [hc]
  rcases eq_or_ne c ⊤ with hc' | hc'
  · simp [hc', ENNReal.div_top]
  · rw [ENNReal.div_mul_cancel hc hc']

open Classical in
/-- **The parent nil-run halts split through the stall junction:**
`nilstall = stallNil + sfGap`, by the Bayes cancellation at each landing state
and the child K1 carve. -/
private theorem nilstall_split (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) (hinv : μ0 = E.endState hT) :
    (∑' s0 : State,
        haltReach S μ0 E ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0)
      = stallNil S g μ0 E
        + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' s0 : State,
                ((innerWitness sys μ0 ω).haltMass μ0
                      ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
                    / (ω.bind id) s0)
                  * (∑' m', ω m' * genW (depMove S) S m' (macroExtend E m')
                      ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩)
                  * g s0 := by
  have hhr : ∀ s0 : State,
      haltReach S μ0 E ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
        = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * (innerWitness sys μ0 ω).haltMass μ0
                ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ := by
    intro s0
    rw [haltReach]
    refine tsum_congr (fun ω => ?_)
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [mul_assoc]
  have hNS : (∑' s0 : State,
      haltReach S μ0 E ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0)
      = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * ∑' s0 : State,
              (innerWitness sys μ0 ω).haltMass μ0
                  ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0 := by
    rw [tsum_congr (fun s0 => by rw [hhr s0, ← ENNReal.tsum_mul_right]), ENNReal.tsum_comm]
    refine tsum_congr (fun ω => ?_)
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr (fun s0 => by rw [mul_assoc])
  rw [hNS, stallNil, ← ENNReal.tsum_add]
  refine tsum_congr (fun ω => ?_)
  by_cases hw : S.next E (some (Silent.τ, ω)) = 0
  · rw [hw, zero_mul, zero_mul, zero_mul, add_zero]
  · rw [← mul_add]
    congr 1
    have hstep : (𝒟(sys^w)).step μ0 Silent.τ ω := by
      rw [hinv]
      exact S.valid E (Nat.find hT) (E.endState hT) (Nat.find_spec hT)
        (AlterSeq.stateAt_find_eq_endState E hT) Silent.τ ω
        ((PMF.mem_support_iff _ _).mpr hw)
    rw [← ENNReal.tsum_add]
    refine tsum_congr (fun s0 => ?_)
    set r0 : {q : AlterSeq State Label // q.trans.Terminates} :=
      ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ with hr0
    have hedge : (innerWitness sys μ0 ω).haltMass μ0 r0
        = ((innerWitness sys μ0 ω).haltMass μ0 r0 / (ω.bind id) s0) * (ω.bind id) s0 := by
      by_cases hb : (ω.bind id) s0 = 0
      · have h0 : (innerWitness sys μ0 ω).haltMass μ0 r0 = 0 := by
          have hle : (innerWitness sys μ0 ω).haltMass μ0 r0 ≤ (ω.bind id) s0 := by
            rw [innerWitness_pushforward hstep s0]
            refine le_trans (le_of_eq ?_) (ENNReal.le_tsum r0)
            rw [if_pos (AlterSeq.endState_of_trans_nil
              (⟨s0, Stream'.Seq.nil⟩ : AlterSeq State Label) rfl
              Stream'.Seq.terminates_nil), mul_one]
          rw [hb] at hle
          exact le_antisymm hle zero_le'
        rw [h0, ENNReal.zero_div, zero_mul]
      · exact (ENNReal.div_mul_cancel hb
          (ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one _ _))).symm
    have hbind : (∑' m', ω m' * m' s0) = (ω.bind id) s0 := by
      rw [PMF.bind_apply]
      exact tsum_congr (fun m' => by rw [id_eq])
    calc (innerWitness sys μ0 ω).haltMass μ0 r0 * g s0
        = ((innerWitness sys μ0 ω).haltMass μ0 r0 / (ω.bind id) s0)
            * (ω.bind id) s0 * g s0 := by rw [← hedge]
      _ = ((innerWitness sys μ0 ω).haltMass μ0 r0 / (ω.bind id) s0)
            * ((∑' m', ω m' * reachArrHalt S m' (macroExtend E m') r0)
                + ∑' m', ω m' * genW (depMove S) S m' (macroExtend E m') r0) * g s0 := by
          rw [← ENNReal.tsum_add,
            tsum_congr (fun m' => by
              rw [← mul_add, reachArrHalt_nil_add S m' (macroExtend E m') s0]), hbind]
      _ = ((innerWitness sys μ0 ω).haltMass μ0 r0 / (ω.bind id) s0)
            * (∑' m', ω m' * reachArrHalt S m' (macroExtend E m') r0) * g s0
          + ((innerWitness sys μ0 ω).haltMass μ0 r0 / (ω.bind id) s0)
            * (∑' m', ω m' * genW (depMove S) S m' (macroExtend E m') r0) * g s0 := by
          ring

open Classical in
/-- **The resets plus the stall-weighted gap are absorbed by the
gap:** per landing state the two Bayes weights sum to `(ω.bind id) t / (ω.bind
id) t ≤ 1`. -/
private theorem reset_sfgap_le_gap (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) (hinv : μ0 = E.endState hT) :
    resetSum S g μ0 E
        + (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' s0 : State,
                ((innerWitness sys μ0 ω).haltMass μ0
                      ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
                    / (ω.bind id) s0)
                  * (∑' m', ω m' * genW (depMove S) S m' (macroExtend E m')
                      ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩)
                  * g s0)
      ≤ Gap S g E := by
  -- the per-`(ω, t)` child carrier
  set K : PMF (PMF State) → State → ENNReal := fun ω t =>
    (∑' m', ω m' * genW (depMove S) S m' (macroExtend E m')
        ⟨⟨t, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩) * g t with hK
  -- (b) reorganize the reset integral per `(ω, e)`
  have hreset : resetSum S g μ0 E
      = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * ∑' e : {q : AlterSeq State Label // q.trans.Terminates},
              (if e.1.trans = Stream'.Seq.nil then 0
                else ((innerWitness sys μ0 ω).haltMass μ0 e
                    / (ω.bind id) (e.1.endState e.2)) * K ω (e.1.endState e.2)) := by
    rw [resetSum]
    have hpt : ∀ e : {q : AlterSeq State Label // q.trans.Terminates},
        (if e.1.trans = Stream'.Seq.nil then 0
          else (∑' seg : FlatSeg State Label,
              (if segPre e seg ∧ (dResidual e seg).1.trans = Stream'.Seq.nil
                then (1 : ENNReal) else 0)
                * divHead S μ0 E seg
                * genW (fun s Ec c => depMove S s Ec c) S seg.succ (macroExtend E seg.succ)
                    (dResidual e seg))
              * g (e.1.endState e.2))
          = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
              * (if e.1.trans = Stream'.Seq.nil then 0
                  else ((innerWitness sys μ0 ω).haltMass μ0 e
                      / (ω.bind id) (e.1.endState e.2)) * K ω (e.1.endState e.2)) := by
      intro e
      split_ifs with hnil
      · simp
      · rw [reset_collapse S μ0 E e
            (fun s Ec c => genW (depMove S) S s Ec c), ← ENNReal.tsum_mul_right]
        refine tsum_congr (fun ω => ?_)
        rw [mul_assoc]
        congr 1
        rw [hK]
        show (∑' m', ω m'
              * (((innerWitness sys μ0 ω).haltMass μ0 e / (ω.bind id) (e.1.endState e.2))
                * genW (depMove S) S m' (macroExtend E m')
                    ⟨⟨e.1.endState e.2, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩))
            * g (e.1.endState e.2)
          = ((innerWitness sys μ0 ω).haltMass μ0 e / (ω.bind id) (e.1.endState e.2))
            * ((∑' m', ω m' * genW (depMove S) S m' (macroExtend E m')
                ⟨⟨e.1.endState e.2, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩)
              * g (e.1.endState e.2))
        rw [show (∑' m', ω m'
              * (((innerWitness sys μ0 ω).haltMass μ0 e / (ω.bind id) (e.1.endState e.2))
                * genW (depMove S) S m' (macroExtend E m')
                    ⟨⟨e.1.endState e.2, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩))
            = ((innerWitness sys μ0 ω).haltMass μ0 e / (ω.bind id) (e.1.endState e.2))
              * ∑' m', ω m' * genW (depMove S) S m' (macroExtend E m')
                  ⟨⟨e.1.endState e.2, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ from by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr (fun m' => by ring)]
        ring
    rw [tsum_congr hpt, ENNReal.tsum_comm]
    exact tsum_congr (fun ω => ENNReal.tsum_mul_left)
  rw [hreset, Gap, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum (fun ω => ?_)
  by_cases hw : S.next E (some (Silent.τ, ω)) = 0
  · rw [hw, zero_mul, zero_mul, zero_mul, add_zero]
  · rw [← mul_add]
    refine mul_le_mul_left' ?_ _
    have hstep : (𝒟(sys^w)).step μ0 Silent.τ ω := by
      rw [hinv]
      exact S.valid E (Nat.find hT) (E.endState hT) (Nat.find_spec hT)
        (AlterSeq.stateAt_find_eq_endState E hT) Silent.τ ω
        ((PMF.mem_support_iff _ _).mpr hw)
    -- the nil stratum is the `sf`-weighted gap
    have hnilstr : (∑' s0 : State,
        ((innerWitness sys μ0 ω).haltMass μ0
              ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
            / (ω.bind id) s0)
          * (∑' m', ω m' * genW (depMove S) S m' (macroExtend E m')
              ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩)
          * g s0)
        = ∑' e : {q : AlterSeq State Label // q.trans.Terminates},
            (if e.1.trans = Stream'.Seq.nil
              then ((innerWitness sys μ0 ω).haltMass μ0 e
                  / (ω.bind id) (e.1.endState e.2)) * K ω (e.1.endState e.2)
              else 0) := by
      rw [tsum_nil_reindex (fun e =>
        ((innerWitness sys μ0 ω).haltMass μ0 e
            / (ω.bind id) (e.1.endState e.2)) * K ω (e.1.endState e.2))]
      refine tsum_congr (fun s0 => ?_)
      rw [AlterSeq.endState_of_trans_nil (⟨s0, Stream'.Seq.nil⟩ : AlterSeq State Label) rfl
        Stream'.Seq.terminates_nil, hK, mul_assoc]
    rw [hnilstr, ← ENNReal.tsum_add]
    rw [show (∑' e : {q : AlterSeq State Label // q.trans.Terminates},
          ((if e.1.trans = Stream'.Seq.nil then 0
            else ((innerWitness sys μ0 ω).haltMass μ0 e
                / (ω.bind id) (e.1.endState e.2)) * K ω (e.1.endState e.2))
          + (if e.1.trans = Stream'.Seq.nil
              then ((innerWitness sys μ0 ω).haltMass μ0 e
                  / (ω.bind id) (e.1.endState e.2)) * K ω (e.1.endState e.2)
              else 0)))
        = ∑' e : {q : AlterSeq State Label // q.trans.Terminates},
            ((innerWitness sys μ0 ω).haltMass μ0 e
                / (ω.bind id) (e.1.endState e.2)) * K ω (e.1.endState e.2) from
      tsum_congr (fun e => by split_ifs <;> simp)]
    -- fiber-group over the landing state and cancel the Bayes weight
    calc (∑' e : {q : AlterSeq State Label // q.trans.Terminates},
            ((innerWitness sys μ0 ω).haltMass μ0 e
                / (ω.bind id) (e.1.endState e.2)) * K ω (e.1.endState e.2))
        = ∑' e : {q : AlterSeq State Label // q.trans.Terminates}, ∑' t : State,
            (if e.1.endState e.2 = t then
              (innerWitness sys μ0 ω).haltMass μ0 e * (((ω.bind id) t)⁻¹ * K ω t) else 0) := by
          refine tsum_congr (fun e => ?_)
          rw [tsum_eq_single (e.1.endState e.2) (fun t ht => if_neg (fun h => ht h.symm)),
            if_pos rfl, div_eq_mul_inv, mul_assoc]
      _ = ∑' t : State, (((ω.bind id) t)⁻¹ * K ω t) * (ω.bind id) t := by
          rw [ENNReal.tsum_comm]
          refine tsum_congr (fun t => ?_)
          rw [innerWitness_pushforward hstep t, ← ENNReal.tsum_mul_left]
          refine tsum_congr (fun e => ?_)
          split_ifs with h
          · rw [mul_one]; ring
          · rw [mul_zero, mul_zero]
      _ ≤ ∑' t : State, K ω t := by
          refine ENNReal.tsum_le_tsum (fun t => ?_)
          rw [show (((ω.bind id) t)⁻¹ * K ω t) * (ω.bind id) t
              = K ω t / (ω.bind id) t * (ω.bind id) t from by
            rw [div_eq_mul_inv]; ring]
          exact ennreal_div_mul_le _ _
      _ = ∑' m', ω m' * (∑' s0 : State, genW (depMove S) S m' (macroExtend E m')
            ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0) := by
          rw [hK]
          simp only
          rw [show (∑' t : State, (∑' m', ω m' * genW (depMove S) S m' (macroExtend E m')
                ⟨⟨t, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩) * g t)
              = ∑' t : State, ∑' m', ω m' * (genW (depMove S) S m' (macroExtend E m')
                ⟨⟨t, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g t) from
            tsum_congr (fun t => by
              rw [← ENNReal.tsum_mul_right]
              exact tsum_congr (fun m' => by ring)), ENNReal.tsum_comm]
          exact tsum_congr (fun m' => ENNReal.tsum_mul_left)

open Classical in
/-- **The reset/stall boundary bookkeeping.** The resets plus the parent
nil-run halts are absorbed by the stall-junction average plus the gap. -/
private theorem resetStall_le (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (hg : ∀ x, g x ≤ 1)
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) (hinv : μ0 = E.endState hT) :
    resetSum S g μ0 E
        + (∑' s0 : State,
            haltReach S μ0 E ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0)
      ≤ stallNil S g μ0 E + Gap S g E := by
  rw [nilstall_split S g μ0 E hT hinv]
  calc resetSum S g μ0 E
        + (stallNil S g μ0 E
          + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
              * ∑' s0 : State,
                  ((innerWitness sys μ0 ω).haltMass μ0
                        ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
                      / (ω.bind id) s0)
                    * (∑' m', ω m' * genW (depMove S) S m' (macroExtend E m')
                        ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩)
                    * g s0)
      = stallNil S g μ0 E
        + (resetSum S g μ0 E
          + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
              * ∑' s0 : State,
                  ((innerWitness sys μ0 ω).haltMass μ0
                        ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩
                      / (ω.bind id) s0)
                    * (∑' m', ω m' * genW (depMove S) S m' (macroExtend E m')
                        ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩)
                    * g s0) := by ring
    _ ≤ stallNil S g μ0 E + Gap S g E :=
        add_le_add le_rfl (reset_sfgap_le_gap S g μ0 E hT hinv)

open Classical in
/-- **K1 through the junction**: the child landing integral splits into the
child nil-halts plus the child resolvent departures (`Gap`). -/
private theorem junction_total_split (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label) :
    (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
        * ∑' m', ω m' * (∑' s, m' s * g s))
      = (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m' * (∑' s0 : State,
                reachArrHalt S m' (macroExtend E m')
                    ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0))
        + Gap S g E := by
  rw [Gap, ← ENNReal.tsum_add]
  refine tsum_congr (fun ω => ?_)
  rw [← mul_add]
  congr 1
  rw [← ENNReal.tsum_add]
  refine tsum_congr (fun m' => ?_)
  rw [← mul_add]
  congr 1
  rw [← ENNReal.tsum_add]
  refine tsum_congr (fun s0 => ?_)
  rw [← add_mul, reachArrHalt_nil_add S m' (macroExtend E m') s0]

open Classical in
/-- **One-step-unfold lower bound of `fHM` (the renewal `≤`).** Halting
immediately at the parent plus taking one macro step to a child `m'` and
honest-flattening from `m'` lower-bounds the parent honest flatten. Proof:
split both sides (`fHM_split`, `renewal_junction_split`, `nilHalt_resolvent`),
add the finite `resetSum + nilstall` to both sides, and chain `resetStall_le`,
`junction_total_split`, `parentHaltReach_collapse`, `haltReach_total_eq`, and
`renewal_NE_identity`. -/
private theorem renewal_step_le (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (hg : ∀ x, g x ≤ 1)
    (μ0 : PMF State) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) (hinv : μ0 = E.endState hT) :
    S.next E none * (∑' s, μ0 s * g s)
        + (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m' * fHM S m' (macroExtend E m') g)
      ≤ fHM S μ0 E g := by
  rw [fHM_split S g μ0 E, renewal_junction_split S g μ0 E,
    nilHalt_resolvent S g μ0 E hT hinv]
  have hkey : (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * ∑' m', ω m' * (∑' s0 : State,
              reachArrHalt S m' (macroExtend E m')
                  ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0))
        + (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m' * (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
                if e.1.trans = Stream'.Seq.nil then 0
                else reachArrHalt S m' (macroExtend E m') e * g (e.1.endState e.2)))
      ≤ stallNil S g μ0 E
        + ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
            if e.1.trans = Stream'.Seq.nil then 0
            else reachArrHalt S μ0 E e * g (e.1.endState e.2) := by
    set Jn := (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
        * ∑' m', ω m' * (∑' s0 : State,
            reachArrHalt S m' (macroExtend E m')
                ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0)) with hJn
    set JNE := (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
        * ∑' m', ω m' * (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
            if e.1.trans = Stream'.Seq.nil then 0
            else reachArrHalt S m' (macroExtend E m') e * g (e.1.endState e.2))) with hJNE
    set NE := (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        if e.1.trans = Stream'.Seq.nil then 0
        else reachArrHalt S μ0 E e * g (e.1.endState e.2)) with hNE
    set NS := (∑' s0 : State,
        haltReach S μ0 E ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0) with hNS
    have hfinR : resetSum S g μ0 E + NS ≠ ⊤ := by
      refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
      · exact ne_top_of_le_ne_top ENNReal.one_ne_top (resetSum_le_one S g hg μ0 E)
      · exact ne_top_of_le_ne_top ENNReal.one_ne_top (nilHaltReach_g_le_one S g hg μ0 E)
    have key : (Jn + JNE) + (resetSum S g μ0 E + NS)
        ≤ (stallNil S g μ0 E + NE) + (resetSum S g μ0 E + NS) := by
      calc (Jn + JNE) + (resetSum S g μ0 E + NS)
          ≤ (Jn + JNE) + (stallNil S g μ0 E + Gap S g E) :=
            add_le_add le_rfl (resetStall_le S g hg μ0 E hT hinv)
        _ = stallNil S g μ0 E + (Jn + Gap S g E) + JNE := by ring
        _ = stallNil S g μ0 E
              + (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
                  * ∑' m', ω m' * (∑' s, m' s * g s)) + JNE := by
            rw [← junction_total_split S g μ0 E]
        _ = stallNil S g μ0 E
              + (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
                  haltReach S μ0 E e * g (e.1.endState e.2)) + JNE := by
            rw [← parentHaltReach_collapse S g μ0 E hT hinv]
        _ = stallNil S g μ0 E + (NS + bHaltSum S g μ0 E) + JNE := by
            rw [haltReach_total_eq S g μ0 E]
        _ = stallNil S g μ0 E + NS + (bHaltSum S g μ0 E + JNE) := by ring
        _ = stallNil S g μ0 E + NS + (NE + resetSum S g μ0 E) := by
            rw [← renewal_NE_identity S g hg μ0 E hT hinv]
        _ = (stallNil S g μ0 E + NE) + (resetSum S g μ0 E + NS) := by ring
    exact (ENNReal.add_le_add_iff_right hfinR).mp key
  calc S.next E none * (∑' s, μ0 s * g s)
        + ((∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m' * (∑' s0 : State,
                reachArrHalt S m' (macroExtend E m')
                    ⟨⟨s0, Stream'.Seq.nil⟩, Stream'.Seq.terminates_nil⟩ * g s0))
          + (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
              * ∑' m', ω m' * (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
                  if e.1.trans = Stream'.Seq.nil then 0
                  else reachArrHalt S m' (macroExtend E m') e * g (e.1.endState e.2))))
      ≤ S.next E none * (∑' s, μ0 s * g s)
          + (stallNil S g μ0 E
            + ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
                if e.1.trans = Stream'.Seq.nil then 0
                else reachArrHalt S μ0 E e * g (e.1.endState e.2)) :=
        add_le_add le_rfl hkey
    _ = S.next E none * (∑' s, μ0 s * g s) + stallNil S g μ0 E
          + ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
              if e.1.trans = Stream'.Seq.nil then 0
              else reachArrHalt S μ0 E e * g (e.1.endState e.2) := by ring

open Classical in
/-- **Depth-stratified halt bound.** For any stratum family `D` obeying the
depth-0 stop identity (`Dzero`) and the one-step junction recursion (`Dsucc`),
the depth-`n` partial sum lower-bounds the honest flatten's `g`-integral
(by induction on the depth, via `renewal_step_le`). Specializes to `fHalt_ge`
(`g := 1`) and `fHalt_ge_G` (`g := [·=s]`). -/
private theorem condDepthSum_le_fHM (S : WeakScheduler (𝒟(sys^w))) (g : State → ENNReal)
    (hg : ∀ x, g x ≤ 1)
    (D : PMF State → (E : AlterSeq (PMF State) Label) → E.trans.Terminates → ℕ → ENNReal)
    (Dsucc : ∀ (μ0 : PMF State) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates)
        (k : ℕ),
      D μ0 E hT (k + 1)
        = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m' * D m' (macroExtend E m') (macroExtend_term hT m') k)
    (Dzero : ∀ (μ0 : PMF State) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates),
      μ0 = E.endState hT → D μ0 E hT 0 = S.next E none * (∑' s0, μ0 s0 * g s0))
    (n : ℕ) :
    ∀ (μ0 : PMF State) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates),
      μ0 = E.endState hT →
      (∑ k ∈ Finset.range n, D μ0 E hT k) ≤ fHM S μ0 E g := by
  induction n with
  | zero => intro μ0 E hT hinv; simp
  | succ n IH =>
    intro μ0 E hT hinv
    have hswap : (∑ k ∈ Finset.range n, D μ0 E hT (k + 1))
        = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m'
                * (∑ k ∈ Finset.range n, D m' (macroExtend E m') (macroExtend_term hT m') k) := by
      rw [Finset.sum_congr rfl (fun k _ => Dsucc μ0 E hT k),
        ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine tsum_congr (fun ω => ?_)
      rw [← Finset.mul_sum]
      congr 1
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine tsum_congr (fun m' => ?_)
      rw [← Finset.mul_sum]
    rw [Finset.sum_range_succ', Dzero μ0 E hT hinv, hswap, add_comm]
    refine le_trans (add_le_add le_rfl ?_) (renewal_step_le S g hg μ0 E hT hinv)
    refine ENNReal.tsum_le_tsum (fun ω => ?_)
    refine mul_le_mul_left' (ENNReal.tsum_le_tsum (fun m' => ?_)) _
    refine mul_le_mul_left' ?_ _
    exact IH m' (macroExtend E m') (macroExtend_term hT m')
      (macroExtend_endState hT m').symm

/-- Iterating `f_integrate_ge` at `g := 1`: the partial sum of conditional depth
totals lower-bounds the honest flatten's total halting mass. -/
private theorem fHalt_ge (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) :
    ∀ (μ0 : PMF State) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates),
      μ0 = E.endState hT →
      (∑ k ∈ Finset.range n, condDepth S μ0 k E) ≤ fHM S μ0 E (fun _ => 1) :=
  condDepthSum_le_fHM S (fun _ => 1) (fun _ => le_rfl)
    (fun μ0 E _ k => condDepth S μ0 k E)
    (fun μ0 E _ k => condDepth_succ' S μ0 k E)
    (fun μ0 E _ _ => by rw [condDepth_zero]; simp only [mul_one, PMF.tsum_coe])
    n

/-- **A.s.-halting.** Given `S` halts almost surely from `PMF.pure μ0`,
the honest flatten `flatSched` halts almost surely from `μ0`. -/
theorem f_halts (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (hhalt : (∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
        S.haltMass (PMF.pure μ0) E) = 1) :
    (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        (flatSched S μ0 ⟨μ0, Seq.nil⟩).haltMass μ0 e) = 1 := by
  have hle : (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
      (flatSched S μ0 ⟨μ0, Seq.nil⟩).haltMass μ0 e) ≤ 1 :=
    WeakScheduler.haltMass_tsum_le_one _ _
  have hHM : fHM S μ0 ⟨μ0, Seq.nil⟩ (fun _ => 1)
      = ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          (flatSched S μ0 ⟨μ0, Seq.nil⟩).haltMass μ0 e := by
    unfold fHM; exact tsum_congr (fun e => mul_one _)
  refine le_antisymm hle ?_
  rw [← macroHalted_iSup_eq_one S μ0 hhalt]
  refine iSup_le (fun n => ?_)
  rw [show (∑ k ∈ Finset.range n, ∑' s, macroHaltDepth S μ0 k s)
      = ∑ k ∈ Finset.range n, condDepth S μ0 k ⟨μ0, Seq.nil⟩ from
    Finset.sum_congr rfl (fun k _ => by rw [macroHaltDepth_total, ← condDepth_root])]
  rw [← hHM]
  exact fHalt_ge S n μ0 ⟨μ0, Seq.nil⟩ Stream'.Seq.terminates_nil
    (AlterSeq.endState_of_trans_nil ⟨μ0, Seq.nil⟩ rfl Stream'.Seq.terminates_nil).symm

open Classical in
/-- Iterating `f_integrate_step` at `g := [· = s]`: the partial sum of the
depth-`k` end-state pushforwards lower-bounds the honest flatten's `s`-integral,
along the invariant that the source is the current macro end-state. -/
private theorem fHalt_ge_G (S : WeakScheduler (𝒟(sys^w))) (s : State) (n : ℕ) :
    ∀ (μ0 : PMF State) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates),
      μ0 = E.endState hT →
      (∑ k ∈ Finset.range n, condDepthG S k E hT s)
        ≤ fHM S μ0 E (fun x => if x = s then 1 else 0) :=
  condDepthSum_le_fHM S (fun x => if x = s then 1 else 0) (fun x => by split_ifs <;> simp)
    (fun _ E hT k => condDepthG S k E hT s)
    (fun _ E hT k => condDepthG_succ' S k E hT s)
    (fun μ0 E hT hinv => by
      rw [condDepthG_zero]
      congr 1
      rw [← hinv, tsum_eq_single s (fun s' hs' => by simp [hs'])]
      simp)
    n

open Classical in
/-- **Pushforward.** The honest flatten `flatSched`'s halting end-state
pushforward is the macro mixture `Ν.bind id`. -/
theorem f_pushforward (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (Ν : PMF (PMF State))
    (hpush : ∀ m, Ν m = ∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
        S.haltMass (PMF.pure μ0) E * (if E.1.endState E.2 = m then 1 else 0))
    (s : State) :
    (Ν.bind id) s
      = ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          (flatSched S μ0 ⟨μ0, Seq.nil⟩).haltMass μ0 e
            * (if e.1.endState e.2 = s then 1 else 0) := by
  have hhalt : (∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
      S.haltMass (PMF.pure μ0) E) = 1 := by
    have h := (PMF.tsum_coe Ν).symm
    rw [tsum_congr (fun m => hpush m), ENNReal.tsum_comm,
      tsum_congr (fun E => by
        rw [ENNReal.tsum_mul_left,
          tsum_eq_single (E.1.endState E.2)
            (fun m hm => if_neg (fun heq => hm heq.symm)), if_pos rfl, mul_one])] at h
    exact h.symm
  set F : State → ENNReal :=
    fun s' => fHM S μ0 ⟨μ0, Seq.nil⟩ (fun x => if x = s' then 1 else 0) with hF
  have htotF : (∑' s', F s') = 1 := by
    simp only [hF, fHM]
    rw [ENNReal.tsum_comm,
      tsum_congr (fun e => by
        rw [ENNReal.tsum_mul_left,
          tsum_eq_single (e.1.endState e.2)
            (fun s' hs' => if_neg (fun heq => hs' heq.symm)), if_pos rfl, mul_one])]
    exact f_halts S μ0 hhalt
  have hle : ∀ s0, (Ν.bind id) s0 ≤ F s0 := by
    intro s0
    rw [macroHalt_tsum_depth S μ0 hpush s0, ENNReal.tsum_eq_iSup_nat]
    refine iSup_le (fun n => ?_)
    rw [show (∑ k ∈ Finset.range n, macroHaltDepth S μ0 k s0)
        = ∑ k ∈ Finset.range n, condDepthG S k ⟨μ0, Seq.nil⟩ Stream'.Seq.terminates_nil s0 from
      Finset.sum_congr rfl (fun k _ => (condDepthG_root S μ0 k s0).symm)]
    exact fHalt_ge_G S s0 n μ0 ⟨μ0, Seq.nil⟩ Stream'.Seq.terminates_nil
      (AlterSeq.endState_of_trans_nil ⟨μ0, Seq.nil⟩ rfl Stream'.Seq.terminates_nil).symm
  have hge : F s ≤ (Ν.bind id) s := by
    have hFsplit : (∑' s', F s') = F s + ∑' s', if s' = s then 0 else F s' :=
      ENNReal.tsum_eq_add_tsum_ite s
    have hNsplit : (∑' s', (Ν.bind id) s') = (Ν.bind id) s
        + ∑' s', if s' = s then 0 else (Ν.bind id) s' :=
      ENNReal.tsum_eq_add_tsum_ite s
    have hRle : (∑' s', if s' = s then 0 else (Ν.bind id) s')
        ≤ ∑' s', if s' = s then 0 else F s' :=
      ENNReal.tsum_le_tsum (fun s' => by split_ifs; exacts [le_refl 0, hle s'])
    have hRfin : (∑' s', if s' = s then 0 else F s') ≠ ⊤ := by
      have hb : (∑' s', if s' = s then 0 else F s') ≤ ∑' s', F s' :=
        ENNReal.tsum_le_tsum (fun s' => by split_ifs; exacts [zero_le', le_refl _])
      rw [htotF] at hb
      exact ne_top_of_le_ne_top ENNReal.one_ne_top hb
    have hle2 : F s + (∑' s', if s' = s then 0 else F s')
        ≤ (Ν.bind id) s + (∑' s', if s' = s then 0 else F s') := by
      calc F s + (∑' s', if s' = s then 0 else F s')
          = ∑' s', F s' := hFsplit.symm
        _ = 1 := htotF
        _ = ∑' s', (Ν.bind id) s' := (PMF.tsum_coe _).symm
        _ = (Ν.bind id) s + ∑' s', if s' = s then 0 else (Ν.bind id) s' := hNsplit
        _ ≤ (Ν.bind id) s + ∑' s', if s' = s then 0 else F s' :=
            add_le_add le_rfl hRle
    exact (ENNReal.add_le_add_iff_right hRfin).mp hle2
  show (Ν.bind id) s = F s
  exact le_antisymm (hle s) hge

/-- **Flattening.** An internal weak transition of `𝒟(sys^w)` out of the
Dirac macro-state `PMF.pure μ` collapses to an internal weak transition of `sys`
from `μ` to the end-state mixture. Witnessed by the honest reach-arrival
flattening scheduler `flatSched` instantiated at the macro witness of `h`:
a.s.-halting is `f_halts`, the pushforward is `f_pushforward`. -/
theorem weakTau_flatten (sys : System State Label) {μ : PMF State}
    {Ν : PMF (PMF State)} (h : weakTau (𝒟(sys^w)) (PMF.pure μ) Ν) :
    weakTau sys μ (Ν.bind id) := by
  classical
  refine ⟨flatSched h.witnessScheduler μ ⟨μ, Seq.nil⟩, ?_, ?_⟩
  · exact f_halts h.witnessScheduler μ h.witness_halts
  · exact fun s => f_pushforward h.witnessScheduler μ Ν
      (fun m => h.witness_pushforward m) s

end PLTS
