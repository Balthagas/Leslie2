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


end PLTS
