/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Simulation.WeakTauFlatten

/-!
# Attic: superseded constructions from the `weakTau_flatten` development

Self-contained studies superseded during the development of `weakTau_flatten`
(`Leslie2.Simulation.WeakTauFlatten`), kept buildable for reference. Nothing
here is used by the library.

Contents, in original order:

* the depth-truncated macro-future `macroFuture_trunc` with its classical
  weak-transition witnesses, and the halted/residual split
  (`macroHalted`/`macroResidual`/`macroSurvive`) — support for the towers;
* the opaque coherent bind tower: `oneDecision`, `TowerData`/`towerStep`,
  `towerSched` and its halting/integrate identities;
* the numerator-exposed single-layer scheduler `oneDecisionC` (branch family,
  `odNum`/`odDenom`, cancel/probOf/haltMass/integrate identities);
* the generic belief scheduler `beliefSched` over a hidden branch family
  (`bNum`/`bDenom`, cancel/probOf/haltMass/integrate identities);
* the concrete coherent bind tower `TowerDataC`/`towerSchedC` and its
  numerator exposure `twNum`/`twDenom`;
* the cylinder-measure limit theory: `cylP`, `cylP_le_one`, `cylP_root`,
  `twDenom_super_step`, `cylMono`, `cylP_super`, `cylP_prefix_le`,
  `cylP_ne_top`.

The small private helpers `tsumOpt` and `tsum_bind_mul` are duplicated
(private) from `WeakTauFlatten`. Other superseded scraps from the same
development are omitted (preserved in git history): the `macroHaltTotal`
partial-sum bridge and its root corollaries, the stall kit
(`iwHaltMass`/`iwMoveMass`/`stallPart`/`stallSum`/`stall_unfold`),
`innerWitness_halts`, `macroHalt_bind_id_eq_iSup`, and the late bound lemmas
(`genW_g_peel`, `condDepthSum_le_one`, `reachArrHalt_ne`/`_peel`,
`fHM_le_one`, `junction_avg_le_one`, `gap_le_one`).
-/

open Stream'
open scoped BigOperators

namespace PLTS

variable {State Label : Type} [Silent Label]

/-- The **depth-`n` truncated macro-future** of the composite belief scheduler
`Σ` from the macro-history `E`: run `Σ` for at most `n` internal macro-steps and,
on a forced halt (depth `0`) or a scheduler stop (`none`), collapse to the
current macro end-state. Genuinely a `PMF State`. -/
noncomputable def macroFuture_trunc {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) :
    (n : ℕ) → (E : AlterSeq (PMF State) Label) → E.trans.Terminates → PMF State
  | 0, E, hT => E.endState hT
  | n + 1, E, hT =>
      (S.next E).bind (fun o => match o with
        | none => E.endState hT
        | some (_, ω) => ω.bind (fun m' =>
            macroFuture_trunc S n (macroExtend E m') (macroExtend_term hT m')))

/-- **Finite macro-future collapse.** Each depth-`n` truncated macro-future of
`S` from a terminating macro-history `E` is an internal weak transition of `sys`
out of `E`'s macro end-state. Proven by induction on `n`: the base is
reflexivity; the step is target-convexity over the scheduler's emission
(`weakTau_mix`), collapsing one macro-step through `weakTau_of_distStep` and
gluing the sampled successor's induction hypothesis with `weakTau_trans`. -/
theorem weakTau_macroFuture_trunc {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) :
    weakTau sys (E.endState hT) (macroFuture_trunc S n E hT) := by
  induction n generalizing E hT with
  | zero => exact weakTau_refl sys (E.endState hT)
  | succ n IH =>
    -- pointwise weak-τ for each scheduler emission `o`
    have hbranch : ∀ o ∈ (S.next E).support,
        weakTau sys (E.endState hT)
          ((fun o => match o with
            | none => E.endState hT
            | some (_, ω) => ω.bind (fun m' =>
                macroFuture_trunc S n (macroExtend E m') (macroExtend_term hT m'))) o) := by
      rintro (_ | ⟨l, ω⟩) ho
      · exact weakTau_refl sys (E.endState hT)
      · -- the emission is a valid internal step out of `E`'s end-state
        have hl : l = Silent.τ := S.internal_only E l ω ho
        subst hl
        have hstep : (𝒟(sys^w)).step (E.endState hT) Silent.τ ω :=
          S.valid E (Nat.find hT) (E.endState hT) (Nat.find_spec hT)
            (AlterSeq.stateAt_find_eq_endState E hT) Silent.τ ω ho
        -- collapse the single macro-step, then continue via the IH per successor
        have hτ1 : weakTau sys (E.endState hT) (ω.bind id) := weakTau_of_distStep hstep
        have hτ2 : weakTau sys (ω.bind id)
            (ω.bind (fun m' =>
              macroFuture_trunc S n (macroExtend E m') (macroExtend_term hT m'))) := by
          refine weakTau_mix ω id
            (fun m' => macroFuture_trunc S n (macroExtend E m') (macroExtend_term hT m'))
            (fun m' _ => ?_)
          have IHm := IH (macroExtend E m') (macroExtend_term hT m')
          rw [macroExtend_endState hT m'] at IHm
          exact IHm
        exact weakTau_trans hτ1 hτ2
    -- assemble via target-convexity, rewriting the source through `bind_const`
    have key := weakTau_mix (S.next E) (fun _ => E.endState hT)
      (fun o => match o with
        | none => E.endState hT
        | some (_, ω) => ω.bind (fun m' =>
            macroFuture_trunc S n (macroExtend E m') (macroExtend_term hT m'))) hbranch
    rw [PMF.bind_const] at key
    exact key

/-- **Root corollary.** From a Dirac-free source `μ` (the nil macro-history), the
depth-`n` truncated macro-future is an internal weak transition of `sys` out of
`μ`. -/
theorem weakTau_macroFuture_trunc_root {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (μ : PMF State) :
    weakTau sys μ
      (macroFuture_trunc S n ⟨μ, Seq.nil⟩ Stream'.Seq.terminates_nil) := by
  have h := weakTau_macroFuture_trunc S n ⟨μ, Seq.nil⟩ Stream'.Seq.terminates_nil
  rwa [AlterSeq.endState_of_trans_nil (⟨μ, Seq.nil⟩ : AlterSeq (PMF State) Label) rfl
    Stream'.Seq.terminates_nil] at h


/-- Split an `ENNReal` tsum over `Option γ` into the `none` value plus the tsum
over `some`. (Private copy of the `WeakTauFlatten` helper.) -/
private theorem tsumOpt {γ : Type} (f : Option γ → ENNReal) :
    (∑' o, f o) = f none + ∑' n, f (some n) := by
  rw [← (Equiv.optionEquivSumPUnit.{0} γ).symm.tsum_eq f,
    Summable.tsum_sum ENNReal.summable ENNReal.summable, add_comm]
  congr 1
  rw [tsum_eq_single PUnit.unit (by rintro ⟨⟩ h; exact absurd rfl h)]
  rfl

/-- Integrating a test `g` against a `PMF.bind` splits as the source-weighted sum
of the branch integrals (the `∑'`-form of `∫ g d(p.bind f) = ∑ₐ p a · ∫ g d(f a)`).
(Private copy of the `WeakTauFlatten` helper.) -/
private theorem tsum_bind_mul {γ : Type} (p : PMF γ) (f : γ → PMF State)
    (g : State → ENNReal) :
    (∑' s, (p.bind f) s * g s) = ∑' a, p a * ∑' s, f a s * g s := by
  have h1 : (∑' s, (p.bind f) s * g s) = ∑' s, ∑' a, p a * f a s * g s :=
    tsum_congr fun s => by rw [PMF.bind_apply, ENNReal.tsum_mul_right]
  rw [h1, ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun s => by ring

/-- The **residual** of the depth-`n` macro-future from `E`: the mass that takes a
scheduler step at every one of the first `n` levels (never stops) and is pushed
through the depth-`n` macro end-state. A sub-distribution of
`macroFuture_trunc S n E`. -/
noncomputable def macroResidual {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) :
    (n : ℕ) → (E : AlterSeq (PMF State) Label) → E.trans.Terminates → State → ENNReal
  | 0, E, hT, s => (E.endState hT) s
  | n + 1, E, hT, s =>
      ∑' o, (S.next E) o * (match o with
        | none => 0
        | some (_, ω) => ∑' m', ω m' *
            macroResidual S n (macroExtend E m') (macroExtend_term hT m') s)

/-- The **halted-within-`n`** sub-distribution of the depth-`n` macro-future from
`E`: the mass that, within the first `n` recursion levels, hits a scheduler stop
(`none`) and collapses to the macro end-state at that moment. -/
noncomputable def macroHalted {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) :
    (n : ℕ) → (E : AlterSeq (PMF State) Label) → E.trans.Terminates → State → ENNReal
  | 0, _, _, _ => 0
  | n + 1, E, hT, s =>
      ∑' o, (S.next E) o * (match o with
        | none => (E.endState hT) s
        | some (_, ω) => ∑' m', ω m' *
            macroHalted S n (macroExtend E m') (macroExtend_term hT m') s)

/-- **Recursion-side decomposition.** The depth-`n` macro-future splits, pointwise,
into the halted-within-`n` part plus the residual. -/
theorem macroFuture_trunc_decompose {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) (s : State) :
    (macroFuture_trunc S n E hT) s
      = macroHalted S n E hT s + macroResidual S n E hT s := by
  induction n generalizing E hT with
  | zero => simp only [macroFuture_trunc, macroHalted, macroResidual, zero_add]
  | succ n IH =>
    simp only [macroHalted, macroResidual, macroFuture_trunc]
    rw [PMF.bind_apply, ← ENNReal.tsum_add]
    apply tsum_congr
    intro o
    cases o with
    | none => simp
    | some p =>
      obtain ⟨l, ω⟩ := p
      rw [← mul_add]
      refine congrArg _ ?_
      rw [PMF.bind_apply, ← ENNReal.tsum_add]
      apply tsum_congr
      intro m'
      rw [← mul_add, IH (macroExtend E m') (macroExtend_term hT m')]

/-- One-step unfolding of the halted-within-`n` sub-distribution. -/
theorem macroHalted_succ {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) (s : State) :
    macroHalted S (n + 1) E hT s
      = ∑' o, (S.next E) o * (match o with
          | none => (E.endState hT) s
          | some (_, ω) => ∑' m', ω m' *
              macroHalted S n (macroExtend E m') (macroExtend_term hT m') s) := rfl

/-- One-step unfolding of the residual sub-distribution. -/
theorem macroResidual_succ {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) (s : State) :
    macroResidual S (n + 1) E hT s
      = ∑' o, (S.next E) o * (match o with
          | none => 0
          | some (_, ω) => ∑' m', ω m' *
              macroResidual S n (macroExtend E m') (macroExtend_term hT m') s) := rfl

/-- **The halted part is monotone in the depth.** Running one more level can only
add halting mass. -/
theorem macroHalted_mono {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) (s : State) :
    macroHalted S n E hT s ≤ macroHalted S (n + 1) E hT s := by
  induction n generalizing E hT with
  | zero => simp [macroHalted]
  | succ n IH =>
    rw [macroHalted_succ, macroHalted_succ]
    refine ENNReal.tsum_le_tsum (fun o => ?_)
    cases o with
    | none => exact le_refl _
    | some p =>
      obtain ⟨l, ω⟩ := p
      refine mul_le_mul_left' (ENNReal.tsum_le_tsum (fun m' => ?_)) _
      exact mul_le_mul_left' (IH (macroExtend E m') (macroExtend_term hT m')) _

/-- **Total residual mass** surviving `n` internal macro-levels from `E`: the total
mass of the depth-`n` residual sub-distribution. Antitone in `n`; its limit is `0`
under a.s.-halting (see the stratification side). -/
noncomputable def macroSurvive {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) : ENNReal :=
  ∑' s, macroResidual S n E hT s

/-- At depth `0` nothing has stopped: the whole (unit) mass survives. -/
theorem macroSurvive_zero {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) :
    macroSurvive S 0 E hT = 1 := by
  unfold macroSurvive
  simp only [macroResidual]
  exact PMF.tsum_coe _

/-- One-step recursion of the total residual mass: survive `n+1` levels iff the
scheduler steps now and the sampled successor survives `n` more. -/
theorem macroSurvive_succ {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) :
    macroSurvive S (n + 1) E hT
      = ∑' o, (S.next E) o * (match o with
          | none => 0
          | some (_, ω) => ∑' m', ω m' *
              macroSurvive S n (macroExtend E m') (macroExtend_term hT m')) := by
  unfold macroSurvive
  simp only [macroResidual]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro o
  rw [ENNReal.tsum_mul_left]
  congr 1
  cases o with
  | none => simp
  | some p =>
    obtain ⟨l, ω⟩ := p
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro m'
    rw [ENNReal.tsum_mul_left]

/-- **Halted total + survive = 1.** The depth-`n` macro-future is a `PMF`, so its
halted-within-`n` total mass and its residual total mass `macroSurvive` partition
the unit mass. Monotone/antitone consequence: as the halted total rises to `1`
(stratification side), `macroSurvive` falls to `0`. -/
theorem macroHalted_total_add_macroSurvive {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) :
    (∑' s, macroHalted S n E hT s) + macroSurvive S n E hT = 1 := by
  unfold macroSurvive
  rw [← ENNReal.tsum_add,
    tsum_congr (fun s => (macroFuture_trunc_decompose S n E hT s).symm)]
  exact PMF.tsum_coe _
variable {sys : System State Label}

/-- **One-layer distribution integrate identity.** Integrating `g` against the
depth-`(n+1)` truncated macro-future distribution unfolds one macro level: halt
now (mass `S.next E none`, integral against the current source `E.endState hT`), or
take a macro-emission `ω` and successor `m'` and recurse at depth `n` from
`macroExtend E m'`. This is the distribution-side (`macroFuture_trunc`) analogue of
the scheduler-side target `d_integrate_step`; it is the pushforward that route-(b)'s
`oneDecision := (weakTau_macroFuture_trunc S 1 E hT).witnessScheduler` delivers. -/
theorem macroFuture_trunc_integrate_succ (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (g : State → ENNReal) :
    (∑' s, macroFuture_trunc S (n + 1) E hT s * g s)
      = S.next E none * (∑' s, (E.endState hT) s * g s)
        + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m' * (∑' s, macroFuture_trunc S n (macroExtend E m')
                (macroExtend_term hT m') s * g s) := by
  have hzero : ∀ (l : Label) (ω : PMF (PMF State)), l ≠ Silent.τ →
      S.next E (some (l, ω)) = 0 := fun l ω hl => by
    by_contra hne
    exact hl (S.internal_only E l ω ((PMF.mem_support_iff _ _).mpr hne))
  have hunfold : macroFuture_trunc S (n + 1) E hT
      = (S.next E).bind (fun o => match o with
          | none => E.endState hT
          | some (_, ω) => ω.bind (fun m' =>
              macroFuture_trunc S n (macroExtend E m') (macroExtend_term hT m'))) := rfl
  rw [hunfold, tsum_bind_mul]
  rw [tsumOpt]
  congr 1
  rw [ENNReal.tsum_prod']
  rw [tsum_eq_single Silent.τ (fun l hl => by
    rw [ENNReal.tsum_eq_zero]; intro ω; rw [hzero l ω hl, zero_mul])]
  refine tsum_congr fun ω => ?_
  rw [tsum_bind_mul]

/-- **`oneDecision` (route (b)).** The single-layer witness scheduler for the
depth-1 truncated macro-future, extracted non-constructively from the landed
`weakTau_macroFuture_trunc S 1 E hT`. No bespoke mixture construction is needed:
`weakTau`'s own `witnessScheduler` / `witness_halts` / `integrate` /
`witness_pushforward` supply every identity the one layer requires. -/
noncomputable def oneDecision (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) : WeakScheduler sys :=
  (weakTau_macroFuture_trunc S 1 E hT).witnessScheduler

/-- `oneDecision` halts almost surely from the current source `E.endState hT`. -/
theorem oneDecision_halts (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) :
    (∑' e, (oneDecision S E hT).haltMass (E.endState hT) e) = 1 :=
  (weakTau_macroFuture_trunc S 1 E hT).witness_halts

/-- **One-layer integrate identity for `oneDecision`.** Exactly `d_integrate_step`'s
shape, truncated at depth `0`: halt now (integral against the source `E.endState hT`),
or take a macro-emission `ω` and successor `m'`, whereupon the successor integral is
against the sampled `m'` itself (the depth-0 macro-future). The genuine work left for
the full recursion is to replace this `∑' s, m' s * g s` by `dHM S m' (macroExtend E m')`
via the depth tower / limit closure. -/
theorem oneDecision_integrate (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (g : State → ENNReal) :
    (∑' e, (oneDecision S E hT).haltMass (E.endState hT) e * g (e.1.endState e.2))
      = S.next E none * (∑' s, (E.endState hT) s * g s)
        + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m' * (∑' s, (macroExtend E m').endState (macroExtend_term hT m')
                s * g s) := by
  rw [oneDecision, (weakTau_macroFuture_trunc S 1 E hT).integrate g]
  exact macroFuture_trunc_integrate_succ S 0 E hT g

/-! ### The numerator-exposed single-layer scheduler `oneDecisionC`

A concrete-`next` rebuild of `oneDecision` as a **mixture-of-common-source belief
scheduler**. The single hidden index is the macro-emission `x : Option (Label ×
PMF (PMF State))` sampled from `S.next E`; each branch runs a genuine `sys`-weak
scheduler `odFam x` from the common source `E.endState hT` (the immediately-stopping
scheduler at `none`, the per-emission inner witness `innerWitness sys src ω` at
`some (_, ω)`). The belief `next e o` is the normalized numerator `odNum e o /
odDenom e`; `odDenom` is the composite path measure and is `≤ 1` (single layer, so
the total emission weight `∑' x, S.next E x = 1` — no stall leak). -/

/-- The branch scheduler family for `oneDecisionC`. -/
noncomputable def odFam (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) :
    Option (Label × PMF (PMF State)) → WeakScheduler sys
  | none => WeakScheduler.stop sys
  | some (_, ω) => innerWitness sys (E.endState hT) ω

open Classical in
/-- The per-branch path measure at an observed inner history `e` (0 off-termination). -/
noncomputable def odBranchProb (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates)
    (x : Option (Label × PMF (PMF State))) (e : AlterSeq State Label) : ENNReal :=
  if h : e.trans.Terminates then
    (⟨E.endState hT, (odFam S E hT x).toScheduler⟩ : ProbabilisticExecution sys).probOf e h
  else 0

/-- The exposed **numerator** of `oneDecisionC.next e` at emission `o`. -/
noncomputable def odNum (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates)
    (e : AlterSeq State Label) (o : Option (Label × PMF State)) : ENNReal :=
  ∑' x, S.next E x * odBranchProb S E hT x e * (odFam S E hT x).next e o

/-- The exposed **denominator** (composite path measure) of `oneDecisionC` at `e`. -/
noncomputable def odDenom (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates)
    (e : AlterSeq State Label) : ENNReal :=
  ∑' x, S.next E x * odBranchProb S E hT x e

/-- Each branch path measure is a sub-probability. -/
theorem odBranchProb_le_one (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates)
    (x : Option (Label × PMF (PMF State))) (e : AlterSeq State Label) :
    odBranchProb S E hT x e ≤ 1 := by
  classical
  unfold odBranchProb
  split
  · exact le_trans (ProbabilisticExecution.probOf_le_init _ _ _) (PMF.coe_le_one _ _)
  · exact zero_le_one

/-- The numerators over `o` sum to the denominator (each branch's `next e` is a PMF). -/
theorem odNum_tsum (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    (∑' o, odNum S E hT e o) = odDenom S E hT e := by
  unfold odNum odDenom
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun x => ?_)
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

/-- The denominator is a sub-probability (`∑' x, S.next E x = 1`, `odBranchProb ≤ 1`). -/
theorem odDenom_le_one (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    odDenom S E hT e ≤ 1 := by
  unfold odDenom
  calc (∑' x, S.next E x * odBranchProb S E hT x e)
      ≤ ∑' x, S.next E x :=
        ENNReal.tsum_le_tsum (fun x => mul_le_of_le_one_right' (odBranchProb_le_one S E hT x e))
    _ = 1 := (S.next E).tsum_coe

/-- The denominator is never `⊤` (the trivial single-layer bound; feeds later `⨆`). -/
theorem odDenom_ne_top (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    odDenom S E hT e ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (odDenom_le_one S E hT e)

open Classical in
/-- **`oneDecisionC` (numerator-exposed route (b)).** The single-macro-layer belief
scheduler with EXPLICIT `next`: the normalized mixture posterior `odNum e o / odDenom e`
over the hidden emission `x`. `valid`/`internal_only` reduce to the branch schedulers'
(each `odFam x` is a genuine `sys`-weak scheduler). -/
noncomputable def oneDecisionC (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) : WeakScheduler sys where
  next e := if h : odDenom S E hT e = 0 then PMF.pure none
    else PMF.normalize (odNum S E hT e) (by rw [odNum_tsum]; exact h)
      (by rw [odNum_tsum]; exact odDenom_ne_top S E hT e)
  valid := by
    classical
    intro e n s hterm hstate l ν hsupp
    by_cases hd : odDenom S E hT e = 0
    · rw [dif_pos hd, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
      exact absurd rfl hsupp
    · simp only [dif_neg hd, PMF.mem_support_normalize_iff] at hsupp
      have hgne : odNum S E hT e (some (l, ν)) ≠ 0 := hsupp
      rw [odNum] at hgne
      have hex := mt ENNReal.tsum_eq_zero.mpr hgne
      push Not at hex
      obtain ⟨x, hxne⟩ := hex
      have hnextne : (odFam S E hT x).next e (some (l, ν)) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hxne; exact hxne rfl
      exact (odFam S E hT x).valid e n s hterm hstate l ν ((PMF.mem_support_iff _ _).mpr hnextne)
  internal_only := by
    classical
    intro e l ν hsupp
    by_cases hd : odDenom S E hT e = 0
    · rw [dif_pos hd, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
      exact absurd rfl hsupp
    · simp only [dif_neg hd, PMF.mem_support_normalize_iff] at hsupp
      have hgne : odNum S E hT e (some (l, ν)) ≠ 0 := hsupp
      rw [odNum] at hgne
      have hex := mt ENNReal.tsum_eq_zero.mpr hgne
      push Not at hex
      obtain ⟨x, hxne⟩ := hex
      have hnextne : (odFam S E hT x).next e (some (l, ν)) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hxne; exact hxne rfl
      exact (odFam S E hT x).internal_only e l ν ((PMF.mem_support_iff _ _).mpr hnextne)

/-- **Cancellation:** `odDenom · oneDecisionC.next = odNum` (the belief-scheduler
normalization identity; the `mapWeakBeliefSched_cancel` analogue). -/
theorem oneDecisionC_cancel (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates)
    (e : AlterSeq State Label) (o : Option (Label × PMF State)) :
    odDenom S E hT e * (oneDecisionC S E hT).next e o = odNum S E hT e o := by
  classical
  by_cases hd : odDenom S E hT e = 0
  · have hnext : (oneDecisionC S E hT).next e = PMF.pure none := dif_pos hd
    rw [hnext, hd, zero_mul]
    have hall : ∀ o', odNum S E hT e o' = 0 := by
      rw [← ENNReal.tsum_eq_zero, odNum_tsum]; exact hd
    exact (hall o).symm
  · have hnext : (oneDecisionC S E hT).next e o
        = odNum S E hT e o * (odDenom S E hT e)⁻¹ := by
      have h1 : (oneDecisionC S E hT).next e
          = PMF.normalize (odNum S E hT e) (by rw [odNum_tsum]; exact hd)
            (by rw [odNum_tsum]; exact odDenom_ne_top S E hT e) := dif_neg hd
      rw [h1, PMF.normalize_apply, odNum_tsum]
    rw [hnext, ← mul_assoc, mul_comm (odDenom S E hT e) (odNum S E hT e o), mul_assoc,
      ENNReal.mul_inv_cancel hd (odDenom_ne_top S E hT e), mul_one]

/-- **Belief consistency (pointwise).** The `oneDecisionC`-path measure of a
terminating inner history `e`, from the common source `E.endState hT`, is exactly the
denominator `odDenom e`. Because the single layer carries total emission weight
`∑' x, S.next E x = 1`, the `nil` base collapses to the source with NO stall term — the
pointwise form that failed for the recursive belief scheduler `dSched`. Induction on
`e` (`List.reverseRecOn`), the append case telescoping each branch's own `probOf`. -/
theorem oneDecisionC_probOf (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates)
    (e : AlterSeq State Label) (hFin : e.trans.Terminates) :
    (⟨E.endState hT, (oneDecisionC S E hT).toScheduler⟩ : ProbabilisticExecution sys).probOf e hFin
      = odDenom S E hT e := by
  classical
  set pe : ProbabilisticExecution sys :=
    ⟨E.endState hT, (oneDecisionC S E hT).toScheduler⟩ with hpe
  change pe.probOf e hFin = odDenom S E hT e
  suffices hgen : ∀ (L : List (Label × State)) (s₀ : State)
      (hFin : (Seq.ofList L : Seq (Label × State)).Terminates),
      pe.probOf ⟨s₀, Seq.ofList L⟩ hFin = odDenom S E hT ⟨s₀, Seq.ofList L⟩ by
    have hofl : (Seq.ofList (e.trans.toList hFin) : Seq (Label × State)) = e.trans :=
      Stream'.Seq.ofList_toList e.trans hFin
    have hFin' : (Seq.ofList (e.trans.toList hFin) : Seq (Label × State)).Terminates := by
      rw [hofl]; exact hFin
    have hEeq : (⟨e.init, Seq.ofList (e.trans.toList hFin)⟩ : AlterSeq State Label) = e := by
      cases e; simp only [hofl]
    have hkey := hgen (e.trans.toList hFin) e.init hFin'
    rw [pe.probOf_congr ⟨e.init, Seq.ofList (e.trans.toList hFin)⟩ e hEeq hFin' hFin] at hkey
    rw [hkey, hEeq]
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    intro s₀ hFin
    rw [pe.probOf_congr ⟨s₀, Seq.ofList ([] : List (Label × State))⟩ ⟨s₀, Seq.nil⟩
      (by rw [Stream'.Seq.ofList_nil]) hFin Stream'.Seq.terminates_nil,
      ProbabilisticExecution.probOf_nil, Stream'.Seq.ofList_nil]
    have hbp : ∀ x, odBranchProb S E hT x ⟨s₀, Seq.nil⟩ = (E.endState hT) s₀ := by
      intro x
      unfold odBranchProb
      rw [dif_pos Stream'.Seq.terminates_nil, ProbabilisticExecution.probOf_nil,
        ProbabilisticExecution.init_eq_initState]
    change (E.endState hT) s₀ = odDenom S E hT ⟨s₀, Seq.nil⟩
    unfold odDenom
    rw [tsum_congr (fun x => by rw [hbp x]), ENNReal.tsum_mul_right, (S.next E).tsum_coe, one_mul]
  | append_singleton rest last ih =>
    intro s₀ hFin
    obtain ⟨l, s'⟩ := last
    have hsplit : (Seq.ofList (rest ++ [(l, s')]) : Seq (Label × State))
        = (Seq.ofList rest).append (Seq.cons (l, s') Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have hrest_fin : (Seq.ofList rest : Seq (Label × State)).Terminates :=
      Stream'.Seq.terminates_ofList _
    have hFinS : ((Seq.ofList rest).append (Seq.cons (l, s') Seq.nil)).Terminates := by
      rw [← hsplit]; exact hFin
    set E' : AlterSeq State Label := ⟨s₀, Seq.ofList rest⟩ with hE'
    -- per-branch: probOf(E') * (branch kernel at (l,s')) = probOf(full)
    have hbpstep : ∀ x, odBranchProb S E hT x E'
        * (∑' ν, (odFam S E hT x).next E' (some (l, ν)) * ν s')
        = odBranchProb S E hT x ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩ := by
      intro x
      unfold odBranchProb
      rw [dif_pos hrest_fin, dif_pos hFin,
        (⟨E.endState hT, (odFam S E hT x).toScheduler⟩ : ProbabilisticExecution sys).probOf_congr
          ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩
          ⟨s₀, (Seq.ofList rest).append (Seq.cons (l, s') Seq.nil)⟩ (by rw [hsplit]) hFin hFinS,
        ProbabilisticExecution.probOf_append_singleton _ s₀ (Seq.ofList rest) hrest_fin (l, s')
          hFinS, ProbabilisticExecution.kernel]
    set Mid : ENNReal := ∑' x, S.next E x * odBranchProb S E hT x E'
      * (∑' ν, (odFam S E hT x).next E' (some (l, ν)) * ν s') with hMid
    have hLHS : pe.probOf ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩ hFin = Mid := by
      rw [pe.probOf_congr ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩
          ⟨s₀, (Seq.ofList rest).append (Seq.cons (l, s') Seq.nil)⟩ (by rw [hsplit]) hFin hFinS,
        pe.probOf_append_singleton s₀ (Seq.ofList rest) hrest_fin (l, s') hFinS,
        show pe.probOf E' hrest_fin = odDenom S E hT E' from ih s₀ hrest_fin,
        ProbabilisticExecution.kernel]
      change odDenom S E hT E' * (∑' ν, (oneDecisionC S E hT).next E' (some (l, ν)) * ν s') = Mid
      have hstep2 : ∀ ν, odNum S E hT E' (some (l, ν)) * ν s'
          = ∑' x, S.next E x * odBranchProb S E hT x E'
              * (odFam S E hT x).next E' (some (l, ν)) * ν s' := by
        intro ν; unfold odNum; rw [ENNReal.tsum_mul_right]
      rw [← ENNReal.tsum_mul_left,
        tsum_congr (fun ν => by rw [← mul_assoc, oneDecisionC_cancel S E hT E' (some (l, ν))]),
        tsum_congr hstep2, ENNReal.tsum_comm, hMid]
      refine tsum_congr (fun x => ?_)
      rw [tsum_congr (fun ν => mul_assoc (S.next E x * odBranchProb S E hT x E') _ _),
        ENNReal.tsum_mul_left]
    have hRHS : odDenom S E hT ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩ = Mid := by
      unfold odDenom
      rw [hMid]
      refine tsum_congr (fun x => ?_)
      rw [← hbpstep x, ← mul_assoc]
    rw [hLHS, hRHS]

/-- Reindex a terminating-history sum supported on the `nil` fibre onto states
(local copy of `weakTau_reindex_fiber`). -/
private theorem reindexFiber {St Lb : Type}
    (fiber : St → AlterSeq St Lb) (hterm : ∀ s, (fiber s).trans.Terminates)
    (hinj : Function.Injective fiber)
    (F : {e : AlterSeq St Lb // e.trans.Terminates} → ENNReal)
    (hsupp : ∀ e : {e : AlterSeq St Lb // e.trans.Terminates},
        F e ≠ 0 → ∃ s, fiber s = e.1) :
    (∑' e, F e) = ∑' s, F ⟨fiber s, hterm s⟩ := by
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun x => (⟨fiber (x : St), hterm x⟩ : {e : AlterSeq St Lb // e.trans.Terminates}))
    ?_ ?_ ?_
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext (hinj hab)
  · intro e he
    obtain ⟨s, hs⟩ := hsupp e (Function.mem_support.mp he)
    have hes : (⟨fiber s, hterm s⟩ : {e : AlterSeq St Lb // e.trans.Terminates}) = e :=
      Subtype.ext hs
    exact ⟨⟨s, by change F ⟨fiber s, hterm s⟩ ≠ 0; rw [hes]; exact Function.mem_support.mp he⟩,
      Subtype.ext hs⟩
  · intro x; rfl

/-- **`stop`-scheduler integrate.** The immediately-stopping scheduler halts on the
`nil` histories, so its `g`-integrated halting end-state is the `g`-integral of the
source (the `none`-branch of `oneDecisionC`). -/
theorem stop_integrate {sys : System State Label} (μ : PMF State) (g : State → ENNReal) :
    (∑' e, (WeakScheduler.stop sys).haltMass μ e * g (e.1.endState e.2)) = ∑' s, μ s * g s := by
  classical
  set pe : ProbabilisticExecution sys := ⟨μ, (WeakScheduler.stop sys).toScheduler⟩ with hpe
  have hker : ∀ (e' : AlterSeq State Label) (st : Label × State), pe.kernel e' st = 0 := by
    intro e' st
    unfold ProbabilisticExecution.kernel
    have h0 : ∀ ν : PMF State, pe.scheduler.next e' (some (st.1, ν)) = 0 :=
      fun ν => PMF.pure_apply_of_ne _ _ (by simp)
    simp only [h0, zero_mul, tsum_zero]
  have hprob_nonnil : ∀ (e' : AlterSeq State Label) (h : e'.trans.Terminates),
      e'.trans ≠ Seq.nil → pe.probOf e' h = 0 := by
    rintro ⟨init', trans'⟩ h hne
    simp only at h hne ⊢
    have hnonempty : trans'.toList h ≠ [] := by
      intro hnil; apply hne
      have := Stream'.Seq.ofList_toList trans' h
      rw [hnil, Stream'.Seq.ofList_nil] at this; exact this.symm
    obtain ⟨previous, last, h_prev, h_split, _, _⟩ :=
      Stream'.Seq.exists_split_last trans' h hnonempty
    subst h_split
    rw [ProbabilisticExecution.probOf_append_singleton _ _ _ h_prev _ h, hker, mul_zero]
  have hhalt_fiber : ∀ s : State,
      (WeakScheduler.stop sys).haltMass μ ⟨⟨s, Seq.nil⟩, Stream'.Seq.terminates_nil⟩ = μ s := by
    intro s
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [← hpe, ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState,
      show (WeakScheduler.stop sys).toScheduler.next ⟨s, Seq.nil⟩ none = 1 from
        PMF.pure_apply_self none, mul_one]
  rw [reindexFiber (fun s => (⟨s, Seq.nil⟩ : AlterSeq State Label))
      (fun _ => Stream'.Seq.terminates_nil) (fun a b hab => congrArg AlterSeq.init hab)
      (fun e => (WeakScheduler.stop sys).haltMass μ e * g (e.1.endState e.2)) ?supp]
  · refine tsum_congr (fun s => ?_)
    rw [hhalt_fiber s, AlterSeq.endState_of_trans_nil _ rfl]
  case supp =>
    intro e hne
    refine ⟨e.1.init, ?_⟩
    by_contra hcontra
    apply hne
    have htrans : e.1.trans ≠ Seq.nil := by
      intro hnil; apply hcontra
      cases e with | mk e' he' => cases e' with | mk i t => simp only at hnil ⊢; rw [hnil]
    have hz : (WeakScheduler.stop sys).haltMass μ e = 0 := by
      unfold WeakScheduler.haltMass Scheduler.haltMass
      rw [← hpe, hprob_nonnil e.1 e.2 htrans, zero_mul]
    rw [hz, zero_mul]

/-- **`oneDecisionC` halting mass as a branch mixture.** The composite halting mass
factors through the hidden emission `x`: `haltMass = ∑' x, S.next E x · (branch halt
mass)`. Immediate from `oneDecisionC_probOf` (path measure `= odDenom`) and
`oneDecisionC_cancel` (`odDenom · next = odNum`). -/
theorem oneDecisionC_haltMass (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) :
    (oneDecisionC S E hT).haltMass (E.endState hT) e
      = ∑' x, S.next E x * (odFam S E hT x).haltMass (E.endState hT) e := by
  classical
  have hhalt : (oneDecisionC S E hT).haltMass (E.endState hT) e = odNum S E hT e.1 none := by
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [show (⟨E.endState hT, (oneDecisionC S E hT).toScheduler⟩
          : ProbabilisticExecution sys).probOf e.1 e.2 = odDenom S E hT e.1 from
        oneDecisionC_probOf S E hT e.1 e.2]
    exact oneDecisionC_cancel S E hT e.1 none
  rw [hhalt]
  unfold odNum
  refine tsum_congr (fun x => ?_)
  rw [mul_assoc]
  congr 1
  unfold WeakScheduler.haltMass Scheduler.haltMass odBranchProb
  rw [dif_pos e.2]

/-- **One-layer integrate identity for `oneDecisionC`.** The `g`-integrated halting
end-state of the concrete single-layer scheduler unfolds exactly one macro level —
the SAME right-hand side as the opaque `oneDecision_integrate`, so the tower/limit
tranches see identical shapes. The `none` branch integrates against the source
(`stop_integrate`); each `some (τ, ω)` branch against `ω.bind id` (`innerWitness_integrate`
then `tsum_bind_mul`), matching the depth-0 macro-future `(macroExtend E m').endState = m'`. -/
theorem oneDecisionC_integrate (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (g : State → ENNReal) :
    (∑' e, (oneDecisionC S E hT).haltMass (E.endState hT) e * g (e.1.endState e.2))
      = S.next E none * (∑' s, (E.endState hT) s * g s)
        + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m' * (∑' s, (macroExtend E m').endState (macroExtend_term hT m')
                s * g s) := by
  classical
  have hA : (∑' e, (oneDecisionC S E hT).haltMass (E.endState hT) e * g (e.1.endState e.2))
      = ∑' x, S.next E x
          * (∑' e, (odFam S E hT x).haltMass (E.endState hT) e * g (e.1.endState e.2)) := by
    have he : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
        (oneDecisionC S E hT).haltMass (E.endState hT) e * g (e.1.endState e.2)
          = ∑' x, S.next E x * (odFam S E hT x).haltMass (E.endState hT) e
              * g (e.1.endState e.2) := by
      intro e
      rw [oneDecisionC_haltMass S E hT e, ENNReal.tsum_mul_right]
    rw [tsum_congr he, ENNReal.tsum_comm]
    refine tsum_congr (fun x => ?_)
    rw [tsum_congr (fun e => mul_assoc (S.next E x) _ _), ENNReal.tsum_mul_left]
  rw [hA, tsumOpt (fun x => S.next E x
    * (∑' e, (odFam S E hT x).haltMass (E.endState hT) e * g (e.1.endState e.2)))]
  congr 1
  · congr 1
    exact stop_integrate (E.endState hT) g
  · have hzero : ∀ (l : Label) (ω : PMF (PMF State)), l ≠ Silent.τ →
        S.next E (some (l, ω)) = 0 := fun l ω hl => by
      by_contra hne
      exact hl (S.internal_only E l ω ((PMF.mem_support_iff _ _).mpr hne))
    rw [ENNReal.tsum_prod',
      tsum_eq_single Silent.τ (fun l hl => by
        rw [ENNReal.tsum_eq_zero]; intro ω; rw [hzero l ω hl, zero_mul])]
    refine tsum_congr (fun ω => ?_)
    by_cases hw : S.next E (some (Silent.τ, ω)) = 0
    · rw [hw, zero_mul, zero_mul]
    · have hstep : (𝒟(sys^w)).step (E.endState hT) Silent.τ ω :=
        S.valid E (Nat.find hT) (E.endState hT) (Nat.find_spec hT)
          (AlterSeq.stateAt_find_eq_endState E hT) Silent.τ ω ((PMF.mem_support_iff _ _).mpr hw)
      congr 1
      show (∑' e, (innerWitness sys (E.endState hT) ω).haltMass (E.endState hT) e
              * g (e.1.endState e.2))
          = ∑' m', ω m' * (∑' s, (macroExtend E m').endState (macroExtend_term hT m') s * g s)
      rw [innerWitness_integrate hstep g, tsum_bind_mul ω id g]
      simp only [id_eq]
      refine tsum_congr (fun m' => ?_)
      rw [macroExtend_endState hT m']

/-- **`oneDecisionC` integrate, macro-future form.** The same identity re-expressed
against the depth-`1` truncated macro-future distribution (`macroFuture_trunc_integrate_succ`),
matching `oneDecision.integrate` — the shape the σ\* squeeze consumes. -/
theorem oneDecisionC_integrate_trunc (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (g : State → ENNReal) :
    (∑' e, (oneDecisionC S E hT).haltMass (E.endState hT) e * g (e.1.endState e.2))
      = ∑' s, macroFuture_trunc S 1 E hT s * g s := by
  rw [oneDecisionC_integrate S E hT g]
  exact (macroFuture_trunc_integrate_succ S 0 E hT g).symm


/-- **`WeakScheduler.bind` compose-integrate law** (the v4 enabling primitive).
The weak-scheduler wrapper over the proven `Scheduler.bind_compose_integrate`:
integrating `g` against the halting end-states of `bind σ k` (from `μ_init`)
factors through `σ`'s halt states `f₁`, continuing with `k (f₁.end)` run from the
Dirac `pure (f₁.end)`. Definitionally the `Scheduler`-level law, since
`WeakScheduler.bind`/`haltMass` unfold to their `Scheduler` counterparts. -/
theorem WeakScheduler.bind_compose_integrate (σ : WeakScheduler sys)
    (k : State → WeakScheduler sys) (μ_init : PMF State) (g : State → ENNReal) :
    (∑' e, (WeakScheduler.bind σ k).haltMass μ_init e * g (e.1.endState e.2))
      = ∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
          σ.haltMass μ_init f₁ *
            ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
              (k (f₁.1.endState f₁.2)).haltMass (PMF.pure (f₁.1.endState f₁.2)) f₂
                * g (f₂.1.endState f₂.2) :=
  Scheduler.bind_compose_integrate σ.toScheduler (fun s => (k s).toScheduler) μ_init g

open Classical in
/-- The halting end-state pushforward of an a.s.-halting weak scheduler `σ` from
source `μ`, as a genuine `PMF State` (total mass `1` by the a.s.-halting hypothesis). -/
noncomputable def pushforwardPMF {sys : System State Label} (σ : WeakScheduler sys)
    (μ : PMF State) (hh : (∑' e, σ.haltMass μ e) = 1) : PMF State :=
  ⟨fun s => ∑' e, σ.haltMass μ e * (if e.1.endState e.2 = s then 1 else 0), by
    have hsum : (∑' s, ∑' e, σ.haltMass μ e * (if e.1.endState e.2 = s then 1 else 0)) = 1 := by
      rw [ENNReal.tsum_comm]
      refine (tsum_congr fun e => ?_).trans hh
      rw [ENNReal.tsum_mul_left, tsum_eq_single (e.1.endState e.2)
        (fun s hs => by rw [if_neg (fun h => hs h.symm)]), if_pos rfl, mul_one]
    have hhs := ENNReal.summable.hasSum
      (f := fun s => ∑' e, σ.haltMass μ e * (if e.1.endState e.2 = s then 1 else 0))
    rwa [hsum] at hhs⟩

open Classical in
/-- An a.s.-halting weak scheduler from source `μ` witnesses `weakTau sys μ` to its
own halting end-state pushforward. -/
theorem weakTau_of_halts {sys : System State Label} (σ : WeakScheduler sys)
    (μ : PMF State) (hh : (∑' e, σ.haltMass μ e) = 1) :
    weakTau sys μ (pushforwardPMF σ μ hh) :=
  ⟨σ, hh, fun _ => rfl⟩

/-- **Pure-source a.s.-halting corollary.** If `σ` halts a.s. from source `μ`, then it
halts a.s. from the Dirac at every `t ∈ μ.support`. (`M u := ∑'e haltMass (pure u) e ≤ 1`
averages to `1` against `μ`, forcing `M t = 1` on the support.) -/
theorem haltMass_pure_of_source {sys : System State Label} (σ : WeakScheduler sys)
    (μ : PMF State) (hh : (∑' e, σ.haltMass μ e) = 1) (t : State) (ht : t ∈ μ.support) :
    (∑' e, σ.haltMass (PMF.pure t) e) = 1 := by
  set M : State → ENNReal := fun u => ∑' e, σ.haltMass (PMF.pure u) e with hM
  have hle : ∀ u, M u ≤ 1 := fun u => WeakScheduler.haltMass_tsum_le_one σ (PMF.pure u)
  have hmix : (∑' u, μ u * M u) = 1 := by
    rw [← hh, tsum_congr (fun e => σ.haltMass_init_mix μ e), ENNReal.tsum_comm]
    exact tsum_congr fun u => by rw [hM, ENNReal.tsum_mul_left]
  have hab : ∀ u, μ u * M u ≤ μ u := fun u => mul_le_of_le_one_right' (hle u)
  have hnlt : ¬ (μ t * M t < μ t) := fun hlt => by
    have hcontra := ENNReal.tsum_lt_tsum (f := fun u => μ u * M u) (g := μ) (i := t)
      (by rw [hmix]; exact ENNReal.one_ne_top) hab hlt
    rw [hmix, μ.tsum_coe] at hcontra
    exact lt_irrefl 1 hcontra
  have heqt : μ t * M t = μ t * 1 := by rw [mul_one]; exact le_antisymm (hab t) (not_lt.mp hnlt)
  show M t = 1
  exact (ENNReal.mul_right_inj ((PMF.mem_support_iff μ t).mp ht) (μ.apply_ne_top t)).mp heqt

open Classical in
/-- **Pushforward integrate.** Integrating `g` against `σ`'s halting end-state
pushforward `PMF` equals integrating `g` against the halting end-states directly. -/
theorem pushforwardPMF_integrate {sys : System State Label} (σ : WeakScheduler sys)
    (μ : PMF State) (hh : (∑' e, σ.haltMass μ e) = 1) (g : State → ENNReal) :
    (∑' u, pushforwardPMF σ μ hh u * g u)
      = ∑' e, σ.haltMass μ e * g (e.1.endState e.2) := by
  calc (∑' u, pushforwardPMF σ μ hh u * g u)
      = ∑' u, (∑' e, σ.haltMass μ e * (if e.1.endState e.2 = u then 1 else 0)) * g u := rfl
    _ = ∑' u, ∑' e, σ.haltMass μ e * (if e.1.endState e.2 = u then 1 else 0) * g u :=
        tsum_congr (fun u => by rw [ENNReal.tsum_mul_right])
    _ = ∑' e, ∑' u, σ.haltMass μ e * (if e.1.endState e.2 = u then 1 else 0) * g u :=
        ENNReal.tsum_comm
    _ = ∑' e, σ.haltMass μ e * g (e.1.endState e.2) := by
        refine tsum_congr (fun e => ?_)
        rw [tsum_congr (fun u => by ring :
            ∀ u, σ.haltMass μ e * (if e.1.endState e.2 = u then 1 else 0) * g u
              = σ.haltMass μ e * ((if e.1.endState e.2 = u then 1 else 0) * g u)),
          ENNReal.tsum_mul_left]
        congr 1
        rw [tsum_eq_single (e.1.endState e.2)
            (fun u' hu' => by rw [if_neg (fun heq => hu' heq.symm), zero_mul]),
          if_pos rfl, one_mul]

/-- **Depth-1 truncated macro-future, pointwise.** One macro-step unfolding of
`macroFuture_trunc S 1 E hT` at a state `t`: halt now (`S.next E none`, source
`E.endState hT`) or take an emission `ω` and successor `m'` (weight `ω m'`, value
`m' t`). The pointwise companion of `macroFuture_trunc_integrate_succ`. -/
theorem macroFuture_trunc_one_apply (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (t : State) :
    macroFuture_trunc S 1 E hT t
      = S.next E none * (E.endState hT) t
        + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω)) * ∑' m', ω m' * m' t := by
  have hzero : ∀ (l : Label) (ω : PMF (PMF State)), l ≠ Silent.τ →
      S.next E (some (l, ω)) = 0 := fun l ω hl => by
    by_contra hne
    exact hl (S.internal_only E l ω ((PMF.mem_support_iff _ _).mpr hne))
  have hunfold : macroFuture_trunc S 1 E hT
      = (S.next E).bind (fun o => match o with
          | none => E.endState hT
          | some (_, ω) => ω.bind (fun m' =>
              macroFuture_trunc S 0 (macroExtend E m') (macroExtend_term hT m'))) := rfl
  rw [hunfold, PMF.bind_apply, tsumOpt]
  congr 1
  rw [ENNReal.tsum_prod']
  rw [tsum_eq_single Silent.τ (fun l hl => by
    rw [ENNReal.tsum_eq_zero]; intro ω; rw [hzero l ω hl, zero_mul])]
  refine tsum_congr fun ω => ?_
  rw [PMF.bind_apply]
  congr 1
  refine tsum_congr fun m' => ?_
  rw [show macroFuture_trunc S 0 (macroExtend E m') (macroExtend_term hT m') = m' from
    macroExtend_endState hT m']

/-! ### Layer 4d (cont.): the coherent bind tower

The depth-`n` **coherent bind tower** `towerSched S n E hT : WeakScheduler sys`: a
concrete witness for `weakTau sys (E.end) (macroFuture_trunc S n E hT)` built by
`Nat.rec` from `WeakScheduler.bind` and `oneDecision`, so that its halting-integral
identity `towerSched_integrate` COMPOSES through `bind_compose_integrate` (unlike the
opaque classical witness of `weakTau_macroFuture_trunc`). This is the v4 route the
frontier docstring at `d_integrate_step` calls for. -/

/-- Bundled payload of the depth-`n` coherent bind tower rooted at `(E, hT)`: the
scheduler together with its `g`-integrated halting identity against the depth-`n`
truncated macro-future. Bundling is forced: the successor's continuation kernel is
built from the previous level's identity (via `weakTau_mix`), so definition and proof
are mutually recursive. -/
structure TowerData {sys : System State Label} (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) where
  /-- The depth-`n` tower scheduler. -/
  sched : WeakScheduler sys
  /-- Its `g`-integrated halting end-state identity: the coherence dividend. -/
  integrate : ∀ g : State → ENNReal,
    (∑' e, sched.haltMass (E.endState hT) e * g (e.1.endState e.2))
      = ∑' s, macroFuture_trunc S n E hT s * g s

/-- **Successor step of the coherent bind tower.** Given the depth-`n` family
`prev` (over all extended macro-histories), produce the depth-`(n+1)` tower rooted at
`(E, hT)`: `WeakScheduler.bind (oneDecision S E hT) k`, where the continuation `k t`
witnesses `weakTau sys (pure t) β_t` and `β_t` is the single-layer posterior mixture
over provenance `Option (PMF (PMF State) × PMF State)`. -/
noncomputable def towerStep (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (prev : ∀ (E' : AlterSeq (PMF State) Label) (hT' : E'.trans.Terminates),
      TowerData S n E' hT')
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) :
    TowerData S (n + 1) E hT := by
  classical
  -- provenance weights: none = immediate halt, some (ω, m') = macro-emission
  let w : Option (PMF (PMF State) × PMF State) → State → ENNReal :=
    fun x t => match x with
      | none => S.next E none * (E.endState hT) t
      | some p => S.next E (some (Silent.τ, p.1)) * p.1 p.2 * p.2 t
  -- the normalizer equals the depth-1 truncated macro-future
  have hZsum : ∀ t, (∑' x, w x t) = macroFuture_trunc S 1 E hT t := by
    intro t
    rw [tsumOpt (fun x => w x t), macroFuture_trunc_one_apply]
    congr 1
    rw [ENNReal.tsum_prod']
    refine tsum_congr fun ω => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun m' => ?_
    show S.next E (some (Silent.τ, ω)) * ω m' * m' t
      = S.next E (some (Silent.τ, ω)) * (ω m' * m' t)
    rw [mul_assoc]
  have hZne : ∀ t, (∑' x, w x t) ≠ ⊤ := fun t => by
    rw [hZsum t]; exact (macroFuture_trunc S 1 E hT).apply_ne_top t
  -- posterior over provenance (junk when the normalizer vanishes)
  let q : State → PMF (Option (PMF (PMF State) × PMF State)) := fun t =>
    if h0 : (∑' x, w x t) = 0 then PMF.pure none
    else PMF.normalize (fun x => w x t) h0 (hZne t)
  -- the depth-n family halts a.s. from source `m'`
  have prevHalt' : ∀ m',
      (∑' e, (prev (macroExtend E m') (macroExtend_term hT m')).sched.haltMass m' e) = 1 := by
    intro m'
    have hsrc : (macroExtend E m').endState (macroExtend_term hT m') = m' :=
      macroExtend_endState hT m'
    have h := (prev (macroExtend E m') (macroExtend_term hT m')).integrate (fun _ => 1)
    simp only [mul_one] at h
    rw [hsrc] at h
    rw [h, (macroFuture_trunc S n (macroExtend E m') (macroExtend_term hT m')).tsum_coe]
  -- continuation targets: pure-halt (none) or the depth-n pushforward from `pure t`
  let branchTarget : State → Option (PMF (PMF State) × PMF State) → PMF State :=
    fun t x => match x with
      | none => PMF.pure t
      | some p => if ht : t ∈ (p.2).support
          then pushforwardPMF (prev (macroExtend E p.2) (macroExtend_term hT p.2)).sched
                (PMF.pure t) (haltMass_pure_of_source _ p.2 (prevHalt' p.2) t ht)
          else PMF.pure t
  -- each posterior mixture is a weak-τ continuation out of `pure t`
  have H : ∀ t, weakTau sys (PMF.pure t) ((q t).bind (branchTarget t)) := by
    intro t
    have hmix : weakTau sys ((q t).bind (fun _ => PMF.pure t)) ((q t).bind (branchTarget t)) := by
      refine weakTau_mix (q t) (fun _ => PMF.pure t) (branchTarget t) ?_
      intro x hx
      match x with
      | none => exact weakTau_refl sys (PMF.pure t)
      | some p =>
          have hwne : w (some p) t ≠ 0 := by
            by_cases h0 : (∑' x, w x t) = 0
            · rw [show q t = PMF.pure none from dif_pos h0, PMF.mem_support_iff,
                PMF.pure_apply, if_neg (Option.some_ne_none p)] at hx
              exact absurd rfl hx
            · rw [show q t = PMF.normalize (fun x => w x t) h0 (hZne t) from dif_neg h0,
                PMF.mem_support_iff, PMF.normalize_apply] at hx
              exact left_ne_zero_of_mul hx
          have ht : t ∈ (p.2).support := by
            rw [PMF.mem_support_iff]; intro hz
            exact hwne (by
              show S.next E (some (Silent.τ, p.1)) * p.1 p.2 * p.2 t = 0
              rw [hz, mul_zero])
          have hht := haltMass_pure_of_source
            (prev (macroExtend E p.2) (macroExtend_term hT p.2)).sched p.2 (prevHalt' p.2) t ht
          rw [show branchTarget t (some p)
              = pushforwardPMF (prev (macroExtend E p.2) (macroExtend_term hT p.2)).sched
                (PMF.pure t) hht from dif_pos ht]
          exact weakTau_of_halts _ (PMF.pure t) hht
    rwa [PMF.bind_const] at hmix
  exact
    { sched := WeakScheduler.bind (oneDecision S E hT) (fun t => (H t).witnessScheduler)
      integrate := fun g => by
        -- normalizer cancellation: `mft1 t · q t x = w x t`
        have hcancel : ∀ t x, macroFuture_trunc S 1 E hT t * q t x = w x t := by
          intro t x
          by_cases h0 : (∑' y, w y t) = 0
          · have hmft : macroFuture_trunc S 1 E hT t = 0 := (hZsum t).symm.trans h0
            have hwx : w x t = 0 := ENNReal.tsum_eq_zero.mp h0 x
            rw [hmft, zero_mul, hwx]
          · rw [show q t = PMF.normalize (fun y => w y t) h0 (hZne t) from dif_neg h0,
              PMF.normalize_apply, ← hZsum t, ← mul_assoc, mul_comm _ (w x t), mul_assoc,
              ENNReal.mul_inv_cancel h0 (hZne t), mul_one]
        -- expectation under a Dirac
        have hpure : ∀ (t : State), (∑' s, (PMF.pure t) s * g s) = g t := fun t => by
          rw [tsum_eq_single t (fun s hs => by rw [PMF.pure_apply, if_neg hs, zero_mul]),
            PMF.pure_apply, if_pos rfl, one_mul]
        -- per-`t` posterior collapse
        have hΦcancel : ∀ t, macroFuture_trunc S 1 E hT t
              * (∑' s, ((q t).bind (branchTarget t)) s * g s)
            = ∑' x, w x t * (∑' s, branchTarget t x s * g s) := by
          intro t
          rw [tsum_bind_mul (q t) (branchTarget t) g, ← ENNReal.tsum_mul_left]
          exact tsum_congr fun x => by rw [← mul_assoc, hcancel t x]
        -- term A (immediate-halt provenance)
        have hTermA : (∑' t, w none t * (∑' s, branchTarget t none s * g s))
            = S.next E none * (∑' s, (E.endState hT) s * g s) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun t => ?_
          show S.next E none * (E.endState hT) t * (∑' s, (PMF.pure t) s * g s)
            = S.next E none * ((E.endState hT) t * g t)
          rw [hpure t, mul_assoc]
        -- term B (macro-emission provenance)
        have hTermB : (∑' p : PMF (PMF State) × PMF State,
              ∑' t, w (some p) t * (∑' s, branchTarget t (some p) s * g s))
            = ∑' ω, S.next E (some (Silent.τ, ω)) * ∑' m', ω m'
                * (∑' s, macroFuture_trunc S n (macroExtend E m')
                    (macroExtend_term hT m') s * g s) := by
          rw [ENNReal.tsum_prod']
          refine tsum_congr fun ω => ?_
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun m' => ?_
          set σ' := (prev (macroExtend E m') (macroExtend_term hT m')).sched with hσ'
          have hbridge : (∑' t, m' t * (∑' s, branchTarget t (some (ω, m')) s * g s))
              = ∑' s, macroFuture_trunc S n (macroExtend E m')
                  (macroExtend_term hT m') s * g s := by
            have hstep : ∀ t, m' t * (∑' s, branchTarget t (some (ω, m')) s * g s)
                = m' t * (∑' e, σ'.haltMass (PMF.pure t) e * g (e.1.endState e.2)) := by
              intro t
              by_cases ht : t ∈ (m').support
              · congr 1
                rw [show branchTarget t (some (ω, m'))
                    = pushforwardPMF σ' (PMF.pure t)
                      (haltMass_pure_of_source _ m' (prevHalt' m') t ht) from dif_pos ht]
                exact pushforwardPMF_integrate _ (PMF.pure t) _ g
              · rw [PMF.mem_support_iff, not_not] at ht
                rw [ht, zero_mul, zero_mul]
            rw [tsum_congr hstep]
            have hsrc : (macroExtend E m').endState (macroExtend_term hT m') = m' :=
              macroExtend_endState hT m'
            have hint := (prev (macroExtend E m') (macroExtend_term hT m')).integrate g
            rw [hsrc, ← hσ'] at hint
            calc (∑' t, m' t * (∑' e, σ'.haltMass (PMF.pure t) e * g (e.1.endState e.2)))
                = ∑' t, ∑' e, m' t * (σ'.haltMass (PMF.pure t) e * g (e.1.endState e.2)) :=
                  tsum_congr fun t => ENNReal.tsum_mul_left.symm
              _ = ∑' e, ∑' t, m' t * (σ'.haltMass (PMF.pure t) e * g (e.1.endState e.2)) :=
                  ENNReal.tsum_comm
              _ = ∑' e, (∑' t, m' t * σ'.haltMass (PMF.pure t) e) * g (e.1.endState e.2) := by
                  refine tsum_congr fun e => ?_
                  rw [← ENNReal.tsum_mul_right]
                  exact tsum_congr fun t => by rw [mul_assoc]
              _ = ∑' e, σ'.haltMass m' e * g (e.1.endState e.2) := by
                  refine tsum_congr fun e => ?_
                  rw [← WeakScheduler.haltMass_init_mix]
              _ = ∑' s, macroFuture_trunc S n (macroExtend E m')
                    (macroExtend_term hT m') s * g s := hint
          rw [← hbridge, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun t => ?_
          show S.next E (some (Silent.τ, ω)) * ω m' * m' t
              * (∑' s, branchTarget t (some (ω, m')) s * g s)
            = S.next E (some (Silent.τ, ω))
              * (ω m' * (m' t * (∑' s, branchTarget t (some (ω, m')) s * g s)))
          ring
        -- assemble: bind_compose ↦ mft1-reweight ↦ cancel ↦ split ↦ A + B
        have h123 : (∑' e, (WeakScheduler.bind (oneDecision S E hT)
                (fun t => (H t).witnessScheduler)).haltMass (E.endState hT) e
              * g (e.1.endState e.2))
            = ∑' t, macroFuture_trunc S 1 E hT t
                * (∑' s, ((q t).bind (branchTarget t)) s * g s) := by
          rw [WeakScheduler.bind_compose_integrate]
          have hin : ∀ f₁ : {e : AlterSeq State Label // e.trans.Terminates},
              (∑' f₂, (H (f₁.1.endState f₁.2)).witnessScheduler.haltMass
                  (PMF.pure (f₁.1.endState f₁.2)) f₂ * g (f₂.1.endState f₂.2))
              = ∑' s, ((q (f₁.1.endState f₁.2)).bind
                  (branchTarget (f₁.1.endState f₁.2))) s * g s :=
            fun f₁ => (H (f₁.1.endState f₁.2)).integrate g
          simp_rw [hin]
          exact (weakTau_macroFuture_trunc S 1 E hT).integrate
            (fun t => ∑' s, ((q t).bind (branchTarget t)) s * g s)
        rw [h123, macroFuture_trunc_integrate_succ S n E hT g, tsum_congr hΦcancel,
          ENNReal.tsum_comm, tsumOpt, hTermA, hTermB] }

/-- The coherent bind tower, by `Nat.rec`. Depth `0` is the immediate-halt witness
(`weakTau_refl`); depth `n+1` is `WeakScheduler.bind (oneDecision S E hT) k` with the
posterior-mixing continuation `k`.

REMAINING (successor): `k t` is the witness of `weakTau sys (pure t) β_t`, where `β_t`
is the single-layer posterior mixture over provenance `(none | some (ω,m'))` given the
halt-state `t` of `oneDecision`: weight `S.next E none · (E.end) t` continues by
immediate halt, weight `S.next E (τ,ω) · ω m' · m' t` continues by `towerData S n
(macroExtend E m')` (its pure-`t` halting is the `t∈supp(m')` corollary of the depth-`n`
`integrate`). Normalizer `∑ = macroFuture_trunc S 1 E hT t ≤ 1` (`ne_top` trivial). The
`integrate` field then follows: `bind_compose_integrate` factors through `oneDecision`'s
halt states; `(weakTau_macroFuture_trunc S 1 E hT).integrate` reweights by
`macroFuture_trunc S 1`; the normalizer cancels the posterior denominator, leaving
`macroFuture_trunc_integrate_succ`'s two terms closed by depth-`n` `integrate`. -/
noncomputable def towerData {sys : System State Label} (S : WeakScheduler (𝒟(sys^w))) :
    (n : ℕ) → (E : AlterSeq (PMF State) Label) → (hT : E.trans.Terminates) →
      TowerData S n E hT
  | 0, E, hT =>
    { sched := (weakTau_refl sys (E.endState hT)).witnessScheduler
      integrate := fun g => by
        simpa only [macroFuture_trunc] using (weakTau_refl sys (E.endState hT)).integrate g }
  | n + 1, E, hT => towerStep S n (fun E' hT' => towerData S n E' hT') E hT
  termination_by n => n

/-- The depth-`n` coherent bind tower witnessing
`weakTau sys (E.end) (macroFuture_trunc S n E hT)`. -/
noncomputable def towerSched {sys : System State Label} (S : WeakScheduler (𝒟(sys^w)))
    (n : ℕ) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) : WeakScheduler sys :=
  (towerData S n E hT).sched

/-- **T2 — the tower realizes the truncation (pushforward/integrate).** The coherence
dividend: the tower's `g`-integrated halting end-state equals the `g`-integral of the
depth-`n` truncated macro-future. -/
theorem towerSched_integrate {sys : System State Label} (S : WeakScheduler (𝒟(sys^w)))
    (n : ℕ) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (g : State → ENNReal) :
    (∑' e, (towerSched S n E hT).haltMass (E.endState hT) e * g (e.1.endState e.2))
      = ∑' s, macroFuture_trunc S n E hT s * g s :=
  (towerData S n E hT).integrate g

/-- **T2 — the tower halts almost surely** from the current source `E.end`. The `g:=1`
specialization of `towerSched_integrate` (the truncated macro-future is a `PMF`). -/
theorem towerSched_halts {sys : System State Label} (S : WeakScheduler (𝒟(sys^w)))
    (n : ℕ) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) :
    (∑' e, (towerSched S n E hT).haltMass (E.endState hT) e) = 1 := by
  have h := towerSched_integrate S n E hT (fun _ => 1)
  simp only [mul_one] at h
  rw [h, (macroFuture_trunc S n E hT).tsum_coe]

/-! ### Generic belief scheduler over a branch family

The `oneDecisionC` pattern (a dite-normalized posterior mixture over a hidden index),
abstracted over an arbitrary index type `ι`, weight `PMF ι`, source `μ`, and branch
family `fam : ι → WeakScheduler sys`, so that the concrete continuation `contC` can
reuse the `probOf`/`haltMass`/`integrate` induction verbatim. -/

open Classical in
/-- Per-branch path measure of family member `fam x` from source `μ` (0 off-termination). -/
noncomputable def bBranchProb {ι : Type} (fam : ι → WeakScheduler sys)
    (μ : PMF State) (x : ι) (e : AlterSeq State Label) : ENNReal :=
  if h : e.trans.Terminates then
    (⟨μ, (fam x).toScheduler⟩ : ProbabilisticExecution sys).probOf e h
  else 0

/-- Exposed **numerator** of the belief scheduler at emission `o`. -/
noncomputable def bNum {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (e : AlterSeq State Label) (o : Option (Label × PMF State)) : ENNReal :=
  ∑' x, wt x * bBranchProb fam μ x e * (fam x).next e o

/-- Exposed **denominator** (composite path measure) of the belief scheduler at `e`. -/
noncomputable def bDenom {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (e : AlterSeq State Label) : ENNReal :=
  ∑' x, wt x * bBranchProb fam μ x e

theorem bBranchProb_le_one {ι : Type} (fam : ι → WeakScheduler sys)
    (μ : PMF State) (x : ι) (e : AlterSeq State Label) :
    bBranchProb fam μ x e ≤ 1 := by
  classical
  unfold bBranchProb
  split
  · exact le_trans (ProbabilisticExecution.probOf_le_init _ _ _) (PMF.coe_le_one _ _)
  · exact zero_le_one

theorem bNum_tsum {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (e : AlterSeq State Label) :
    (∑' o, bNum fam wt μ e o) = bDenom fam wt μ e := by
  unfold bNum bDenom
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun x => ?_)
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

theorem bDenom_le_one {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (e : AlterSeq State Label) :
    bDenom fam wt μ e ≤ 1 := by
  unfold bDenom
  calc (∑' x, wt x * bBranchProb fam μ x e)
      ≤ ∑' x, wt x :=
        ENNReal.tsum_le_tsum (fun x => mul_le_of_le_one_right' (bBranchProb_le_one fam μ x e))
    _ = 1 := wt.tsum_coe

theorem bDenom_ne_top {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (e : AlterSeq State Label) :
    bDenom fam wt μ e ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (bDenom_le_one fam wt μ e)

open Classical in
/-- The generic single-layer belief scheduler: normalized posterior `bNum/bDenom`. -/
noncomputable def beliefSched {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) : WeakScheduler sys where
  next e := if h : bDenom fam wt μ e = 0 then PMF.pure none
    else PMF.normalize (bNum fam wt μ e) (by rw [bNum_tsum]; exact h)
      (by rw [bNum_tsum]; exact bDenom_ne_top fam wt μ e)
  valid := by
    classical
    intro e n s hterm hstate l ν hsupp
    by_cases hd : bDenom fam wt μ e = 0
    · rw [dif_pos hd, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
      exact absurd rfl hsupp
    · simp only [dif_neg hd, PMF.mem_support_normalize_iff] at hsupp
      have hgne : bNum fam wt μ e (some (l, ν)) ≠ 0 := hsupp
      rw [bNum] at hgne
      have hex := mt ENNReal.tsum_eq_zero.mpr hgne
      push Not at hex
      obtain ⟨x, hxne⟩ := hex
      have hnextne : (fam x).next e (some (l, ν)) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hxne; exact hxne rfl
      exact (fam x).valid e n s hterm hstate l ν ((PMF.mem_support_iff _ _).mpr hnextne)
  internal_only := by
    classical
    intro e l ν hsupp
    by_cases hd : bDenom fam wt μ e = 0
    · rw [dif_pos hd, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
      exact absurd rfl hsupp
    · simp only [dif_neg hd, PMF.mem_support_normalize_iff] at hsupp
      have hgne : bNum fam wt μ e (some (l, ν)) ≠ 0 := hsupp
      rw [bNum] at hgne
      have hex := mt ENNReal.tsum_eq_zero.mpr hgne
      push Not at hex
      obtain ⟨x, hxne⟩ := hex
      have hnextne : (fam x).next e (some (l, ν)) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hxne; exact hxne rfl
      exact (fam x).internal_only e l ν ((PMF.mem_support_iff _ _).mpr hnextne)

/-- **Cancellation:** `bDenom · beliefSched.next = bNum`. -/
theorem beliefSched_cancel {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (e : AlterSeq State Label) (o : Option (Label × PMF State)) :
    bDenom fam wt μ e * (beliefSched fam wt μ).next e o = bNum fam wt μ e o := by
  classical
  by_cases hd : bDenom fam wt μ e = 0
  · have hnext : (beliefSched fam wt μ).next e = PMF.pure none := dif_pos hd
    rw [hnext, hd, zero_mul]
    have hall : ∀ o', bNum fam wt μ e o' = 0 := by
      rw [← ENNReal.tsum_eq_zero, bNum_tsum]; exact hd
    exact (hall o).symm
  · have hnext : (beliefSched fam wt μ).next e o
        = bNum fam wt μ e o * (bDenom fam wt μ e)⁻¹ := by
      have h1 : (beliefSched fam wt μ).next e
          = PMF.normalize (bNum fam wt μ e) (by rw [bNum_tsum]; exact hd)
            (by rw [bNum_tsum]; exact bDenom_ne_top fam wt μ e) := dif_neg hd
      rw [h1, PMF.normalize_apply, bNum_tsum]
    rw [hnext, ← mul_assoc, mul_comm (bDenom fam wt μ e) (bNum fam wt μ e o), mul_assoc,
      ENNReal.mul_inv_cancel hd (bDenom_ne_top fam wt μ e), mul_one]

/-- **Belief consistency (pointwise).** The `beliefSched`-path measure of a terminating
history `e` from source `μ` is exactly `bDenom e`. Induction on `e` (`List.reverseRecOn`). -/
theorem beliefSched_probOf {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (e : AlterSeq State Label) (hFin : e.trans.Terminates) :
    (⟨μ, (beliefSched fam wt μ).toScheduler⟩ : ProbabilisticExecution sys).probOf e hFin
      = bDenom fam wt μ e := by
  classical
  set pe : ProbabilisticExecution sys := ⟨μ, (beliefSched fam wt μ).toScheduler⟩ with hpe
  change pe.probOf e hFin = bDenom fam wt μ e
  suffices hgen : ∀ (L : List (Label × State)) (s₀ : State)
      (hFin : (Seq.ofList L : Seq (Label × State)).Terminates),
      pe.probOf ⟨s₀, Seq.ofList L⟩ hFin = bDenom fam wt μ ⟨s₀, Seq.ofList L⟩ by
    have hofl : (Seq.ofList (e.trans.toList hFin) : Seq (Label × State)) = e.trans :=
      Stream'.Seq.ofList_toList e.trans hFin
    have hFin' : (Seq.ofList (e.trans.toList hFin) : Seq (Label × State)).Terminates := by
      rw [hofl]; exact hFin
    have hEeq : (⟨e.init, Seq.ofList (e.trans.toList hFin)⟩ : AlterSeq State Label) = e := by
      cases e; simp only [hofl]
    have hkey := hgen (e.trans.toList hFin) e.init hFin'
    rw [pe.probOf_congr ⟨e.init, Seq.ofList (e.trans.toList hFin)⟩ e hEeq hFin' hFin] at hkey
    rw [hkey, hEeq]
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    intro s₀ hFin
    rw [pe.probOf_congr ⟨s₀, Seq.ofList ([] : List (Label × State))⟩ ⟨s₀, Seq.nil⟩
      (by rw [Stream'.Seq.ofList_nil]) hFin Stream'.Seq.terminates_nil,
      ProbabilisticExecution.probOf_nil, Stream'.Seq.ofList_nil]
    have hbp : ∀ x, bBranchProb fam μ x ⟨s₀, Seq.nil⟩ = μ s₀ := by
      intro x
      unfold bBranchProb
      rw [dif_pos Stream'.Seq.terminates_nil, ProbabilisticExecution.probOf_nil,
        ProbabilisticExecution.init_eq_initState]
    change μ s₀ = bDenom fam wt μ ⟨s₀, Seq.nil⟩
    unfold bDenom
    rw [tsum_congr (fun x => by rw [hbp x]), ENNReal.tsum_mul_right, wt.tsum_coe, one_mul]
  | append_singleton rest last ih =>
    intro s₀ hFin
    obtain ⟨l, s'⟩ := last
    have hsplit : (Seq.ofList (rest ++ [(l, s')]) : Seq (Label × State))
        = (Seq.ofList rest).append (Seq.cons (l, s') Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have hrest_fin : (Seq.ofList rest : Seq (Label × State)).Terminates :=
      Stream'.Seq.terminates_ofList _
    have hFinS : ((Seq.ofList rest).append (Seq.cons (l, s') Seq.nil)).Terminates := by
      rw [← hsplit]; exact hFin
    set E' : AlterSeq State Label := ⟨s₀, Seq.ofList rest⟩ with hE'
    have hbpstep : ∀ x, bBranchProb fam μ x E'
        * (∑' ν, (fam x).next E' (some (l, ν)) * ν s')
        = bBranchProb fam μ x ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩ := by
      intro x
      unfold bBranchProb
      rw [dif_pos hrest_fin, dif_pos hFin,
        (⟨μ, (fam x).toScheduler⟩ : ProbabilisticExecution sys).probOf_congr
          ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩
          ⟨s₀, (Seq.ofList rest).append (Seq.cons (l, s') Seq.nil)⟩ (by rw [hsplit]) hFin hFinS,
        ProbabilisticExecution.probOf_append_singleton _ s₀ (Seq.ofList rest) hrest_fin (l, s')
          hFinS, ProbabilisticExecution.kernel]
    set Mid : ENNReal := ∑' x, wt x * bBranchProb fam μ x E'
      * (∑' ν, (fam x).next E' (some (l, ν)) * ν s') with hMid
    have hLHS : pe.probOf ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩ hFin = Mid := by
      rw [pe.probOf_congr ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩
          ⟨s₀, (Seq.ofList rest).append (Seq.cons (l, s') Seq.nil)⟩ (by rw [hsplit]) hFin hFinS,
        pe.probOf_append_singleton s₀ (Seq.ofList rest) hrest_fin (l, s') hFinS,
        show pe.probOf E' hrest_fin = bDenom fam wt μ E' from ih s₀ hrest_fin,
        ProbabilisticExecution.kernel]
      change bDenom fam wt μ E' * (∑' ν, (beliefSched fam wt μ).next E' (some (l, ν)) * ν s') = Mid
      have hstep2 : ∀ ν, bNum fam wt μ E' (some (l, ν)) * ν s'
          = ∑' x, wt x * bBranchProb fam μ x E'
              * (fam x).next E' (some (l, ν)) * ν s' := by
        intro ν; unfold bNum; rw [ENNReal.tsum_mul_right]
      rw [← ENNReal.tsum_mul_left,
        tsum_congr (fun ν => by rw [← mul_assoc, beliefSched_cancel fam wt μ E' (some (l, ν))]),
        tsum_congr hstep2, ENNReal.tsum_comm, hMid]
      refine tsum_congr (fun x => ?_)
      rw [tsum_congr (fun ν => mul_assoc (wt x * bBranchProb fam μ x E') _ _),
        ENNReal.tsum_mul_left]
    have hRHS : bDenom fam wt μ ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩ = Mid := by
      unfold bDenom
      rw [hMid]
      refine tsum_congr (fun x => ?_)
      rw [← hbpstep x, ← mul_assoc]
    rw [hLHS, hRHS]

/-- **Belief halting mass as a branch mixture.** -/
theorem beliefSched_haltMass {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (e : {e : AlterSeq State Label // e.trans.Terminates}) :
    (beliefSched fam wt μ).haltMass μ e
      = ∑' x, wt x * (fam x).haltMass μ e := by
  classical
  have hhalt : (beliefSched fam wt μ).haltMass μ e = bNum fam wt μ e.1 none := by
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [show (⟨μ, (beliefSched fam wt μ).toScheduler⟩
          : ProbabilisticExecution sys).probOf e.1 e.2 = bDenom fam wt μ e.1 from
        beliefSched_probOf fam wt μ e.1 e.2]
    exact beliefSched_cancel fam wt μ e.1 none
  rw [hhalt]
  unfold bNum
  refine tsum_congr (fun x => ?_)
  rw [mul_assoc]
  congr 1
  unfold WeakScheduler.haltMass Scheduler.haltMass bBranchProb
  rw [dif_pos e.2]

/-- **Generic integrate identity.** The `g`-integrated halting end-state of `beliefSched`
factors through the hidden index: `∑' x, wt x · (branch integral)`. -/
theorem beliefSched_integrate {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (g : State → ENNReal) :
    (∑' e, (beliefSched fam wt μ).haltMass μ e * g (e.1.endState e.2))
      = ∑' x, wt x
          * (∑' e, (fam x).haltMass μ e * g (e.1.endState e.2)) := by
  classical
  have he : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      (beliefSched fam wt μ).haltMass μ e * g (e.1.endState e.2)
        = ∑' x, wt x * (fam x).haltMass μ e
            * g (e.1.endState e.2) := by
    intro e
    rw [beliefSched_haltMass fam wt μ e, ENNReal.tsum_mul_right]
  rw [tsum_congr he, ENNReal.tsum_comm]
  refine tsum_congr (fun x => ?_)
  rw [tsum_congr (fun e => mul_assoc (wt x) _ _), ENNReal.tsum_mul_left]

/-! ### The concrete coherent bind tower `TowerDataC` (numerator-exposed, route (b))

Mirrors `TowerData`/`towerStep`/`towerData`, but built from the numerator-exposed
`oneDecisionC` and a CONCRETE single-layer belief continuation `contC` (an instance of
`beliefSched`) in place of the opaque `Classical.choose` witnesses, so its `next` carries
an exposed numerator for the `⨆ n` limit. -/

/-- Bundled payload of the depth-`n` concrete tower rooted at `(E, hT)`: scheduler plus
its `g`-integrated halting identity against the depth-`n` truncated macro-future.
Identical fields to `TowerData`; kept distinct so the concrete recursion is self-contained. -/
structure TowerDataC {sys : System State Label} (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) where
  /-- The depth-`n` concrete tower scheduler. -/
  sched : WeakScheduler sys
  /-- Its `g`-integrated halting end-state identity. -/
  integrate : ∀ g : State → ENNReal,
    (∑' e, sched.haltMass (E.endState hT) e * g (e.1.endState e.2))
      = ∑' s, macroFuture_trunc S n E hT s * g s

/-- Provenance weights at halt-state `t`: `none` = immediate halt, `some (ω, m')` =
macro-emission. -/
noncomputable def ctW (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) :
    Option (PMF (PMF State) × PMF State) → State → ENNReal :=
  fun x t => match x with
    | none => S.next E none * (E.endState hT) t
    | some p => S.next E (some (Silent.τ, p.1)) * p.1 p.2 * p.2 t

/-- The provenance weights sum to the depth-1 truncated macro-future. -/
theorem ctZsum (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (t : State) :
    (∑' x, ctW S E hT x t) = macroFuture_trunc S 1 E hT t := by
  rw [tsumOpt (fun x => ctW S E hT x t), macroFuture_trunc_one_apply]
  congr 1
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun ω => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun m' => ?_
  show S.next E (some (Silent.τ, ω)) * ω m' * m' t
    = S.next E (some (Silent.τ, ω)) * (ω m' * m' t)
  rw [mul_assoc]

/-- The provenance normalizer is never `⊤`. -/
theorem ctZne (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (t : State) :
    (∑' x, ctW S E hT x t) ≠ ⊤ := by
  rw [ctZsum]; exact (macroFuture_trunc S 1 E hT).apply_ne_top t

/-- The normalized provenance posterior at halt-state `t` (junk `pure none` off support). -/
noncomputable def ctPost (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (t : State) :
    PMF (Option (PMF (PMF State) × PMF State)) :=
  if h0 : (∑' x, ctW S E hT x t) = 0 then PMF.pure none
  else PMF.normalize (fun x => ctW S E hT x t) h0 (ctZne S E hT t)

/-- Continuation branch family: immediate-halt (`stop`) or the depth-`n` tower at the
extended root `macroExtend E m'`. -/
noncomputable def ctFam (S : WeakScheduler (𝒟(sys^w))) {n : ℕ}
    (prev : ∀ (E' : AlterSeq (PMF State) Label) (hT' : E'.trans.Terminates), TowerDataC S n E' hT')
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) :
    Option (PMF (PMF State) × PMF State) → WeakScheduler sys :=
  fun x => match x with
    | none => WeakScheduler.stop sys
    | some p => (prev (macroExtend E p.2) (macroExtend_term hT p.2)).sched

/-- The depth-`n` family halts a.s. from source `m'` (the `prevHalt'` of `towerStep`). -/
theorem ctPrevHalt (S : WeakScheduler (𝒟(sys^w))) {n : ℕ}
    (prev : ∀ (E' : AlterSeq (PMF State) Label) (hT' : E'.trans.Terminates), TowerDataC S n E' hT')
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (m' : PMF State) :
    (∑' e, (prev (macroExtend E m') (macroExtend_term hT m')).sched.haltMass m' e) = 1 := by
  have hsrc : (macroExtend E m').endState (macroExtend_term hT m') = m' :=
    macroExtend_endState hT m'
  have h := (prev (macroExtend E m') (macroExtend_term hT m')).integrate (fun _ => 1)
  simp only [mul_one] at h
  rw [hsrc] at h
  rw [h, (macroFuture_trunc S n (macroExtend E m') (macroExtend_term hT m')).tsum_coe]

open Classical in
/-- Continuation targets from the Dirac `pure t`: `none` ↦ `pure t`, `some p` ↦ the
depth-`n` pushforward from `pure t` (`pure t` off `p.2`'s support). -/
noncomputable def branchTargetC (S : WeakScheduler (𝒟(sys^w))) {n : ℕ}
    (prev : ∀ (E' : AlterSeq (PMF State) Label) (hT' : E'.trans.Terminates), TowerDataC S n E' hT')
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (t : State) :
    Option (PMF (PMF State) × PMF State) → PMF State :=
  fun x => match x with
    | none => PMF.pure t
    | some p => if ht : t ∈ (p.2).support
        then pushforwardPMF (prev (macroExtend E p.2) (macroExtend_term hT p.2)).sched
              (PMF.pure t) (haltMass_pure_of_source _ p.2 (ctPrevHalt S prev E hT p.2) t ht)
        else PMF.pure t

/-- **The concrete continuation kernel.** At a halt-state `t` of `oneDecisionC`, the
single-layer belief scheduler mixing the provenance posterior `ctPost t` over the
branch family `ctFam`, run from the Dirac source `pure t`. An instance of `beliefSched`,
so its `next` carries the exposed numerator `bNum (ctFam …) (ctPost … t) (pure t)`. -/
noncomputable def contC (S : WeakScheduler (𝒟(sys^w))) {n : ℕ}
    (prev : ∀ (E' : AlterSeq (PMF State) Label) (hT' : E'.trans.Terminates), TowerDataC S n E' hT')
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (t : State) : WeakScheduler sys :=
  beliefSched (ctFam S prev E hT) (ctPost S E hT t) (PMF.pure t)

/-- **Continuation integrate (RHS-parity with the opaque `(H t).integrate`).** The
`g`-integrated halting end-state of `contC` from source `pure t` equals the `g`-integral
of the posterior mixture `(ctPost t).bind (branchTargetC t)` — the exact right-hand side
the opaque `towerStep` continuation produced, so the tower integrate proof transplants. -/
theorem contC_integrate (S : WeakScheduler (𝒟(sys^w))) {n : ℕ}
    (prev : ∀ (E' : AlterSeq (PMF State) Label) (hT' : E'.trans.Terminates), TowerDataC S n E' hT')
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (t : State) (g : State → ENNReal) :
    (∑' e, (contC S prev E hT t).haltMass (PMF.pure t) e * g (e.1.endState e.2))
      = ∑' s, ((ctPost S E hT t).bind (branchTargetC S prev E hT t)) s * g s := by
  classical
  have hc : contC S prev E hT t
      = beliefSched (ctFam S prev E hT) (ctPost S E hT t) (PMF.pure t) := rfl
  rw [hc, beliefSched_integrate (ctFam S prev E hT) (ctPost S E hT t) (PMF.pure t) g,
    tsum_bind_mul (ctPost S E hT t) (branchTargetC S prev E hT t) g]
  refine tsum_congr fun x => ?_
  cases x with
  | none =>
      congr 1
      show (∑' e, (WeakScheduler.stop sys).haltMass (PMF.pure t) e * g (e.1.endState e.2))
        = ∑' s, (PMF.pure t) s * g s
      exact stop_integrate (PMF.pure t) g
  | some p =>
      by_cases ht : t ∈ (p.2).support
      · congr 1
        rw [show branchTargetC S prev E hT t (some p)
            = pushforwardPMF (prev (macroExtend E p.2) (macroExtend_term hT p.2)).sched
              (PMF.pure t) (haltMass_pure_of_source _ p.2 (ctPrevHalt S prev E hT p.2) t ht)
            from dif_pos ht]
        exact (pushforwardPMF_integrate _ (PMF.pure t) _ g).symm
      · have hw0 : ctW S E hT (some p) t = 0 := by
          show S.next E (some (Silent.τ, p.1)) * p.1 p.2 * p.2 t = 0
          rw [PMF.mem_support_iff, not_not] at ht
          rw [ht, mul_zero]
        have hpost0 : ctPost S E hT t (some p) = 0 := by
          by_cases h0 : (∑' x, ctW S E hT x t) = 0
          · rw [ctPost, dif_pos h0, PMF.pure_apply, if_neg (Option.some_ne_none p)]
          · rw [ctPost, dif_neg h0, PMF.normalize_apply, hw0, zero_mul]
        rw [hpost0, zero_mul, zero_mul]

/-- **Successor step of the concrete tower.** Given the depth-`n` concrete family `prev`,
the depth-`(n+1)` tower rooted at `(E, hT)`: `WeakScheduler.bind (oneDecisionC S E hT) contC`.
Integrate proof transplanted from the opaque `towerStep` (RHS parity), with `contC_integrate`
for `(H t).integrate` and `oneDecisionC_integrate_trunc` for the depth-1 reweight. -/
noncomputable def towerStepC (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (prev : ∀ (E' : AlterSeq (PMF State) Label) (hT' : E'.trans.Terminates), TowerDataC S n E' hT')
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) :
    TowerDataC S (n + 1) E hT :=
  { sched := WeakScheduler.bind (oneDecisionC S E hT) (fun t => contC S prev E hT t)
    integrate := fun g => by
      classical
      have hcancel : ∀ t x, macroFuture_trunc S 1 E hT t * ctPost S E hT t x = ctW S E hT x t := by
        intro t x
        by_cases h0 : (∑' y, ctW S E hT y t) = 0
        · have hmft : macroFuture_trunc S 1 E hT t = 0 := (ctZsum S E hT t).symm.trans h0
          have hwx : ctW S E hT x t = 0 := ENNReal.tsum_eq_zero.mp h0 x
          rw [hmft, zero_mul, hwx]
        · rw [show ctPost S E hT t = PMF.normalize (fun y => ctW S E hT y t) h0 (ctZne S E hT t)
              from dif_neg h0,
            PMF.normalize_apply, ← ctZsum S E hT t, ← mul_assoc, mul_comm _ (ctW S E hT x t),
            mul_assoc, ENNReal.mul_inv_cancel h0 (ctZne S E hT t), mul_one]
      have hpure : ∀ (t : State), (∑' s, (PMF.pure t) s * g s) = g t := fun t => by
        rw [tsum_eq_single t (fun s hs => by rw [PMF.pure_apply, if_neg hs, zero_mul]),
          PMF.pure_apply, if_pos rfl, one_mul]
      have hΦcancel : ∀ t, macroFuture_trunc S 1 E hT t
            * (∑' s, ((ctPost S E hT t).bind (branchTargetC S prev E hT t)) s * g s)
          = ∑' x, ctW S E hT x t * (∑' s, branchTargetC S prev E hT t x s * g s) := by
        intro t
        rw [tsum_bind_mul (ctPost S E hT t) (branchTargetC S prev E hT t) g,
          ← ENNReal.tsum_mul_left]
        exact tsum_congr fun x => by rw [← mul_assoc, hcancel t x]
      have hTermA : (∑' t, ctW S E hT none t * (∑' s, branchTargetC S prev E hT t none s * g s))
          = S.next E none * (∑' s, (E.endState hT) s * g s) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun t => ?_
        show S.next E none * (E.endState hT) t * (∑' s, (PMF.pure t) s * g s)
          = S.next E none * ((E.endState hT) t * g t)
        rw [hpure t, mul_assoc]
      have hTermB : (∑' p : PMF (PMF State) × PMF State,
            ∑' t, ctW S E hT (some p) t * (∑' s, branchTargetC S prev E hT t (some p) s * g s))
          = ∑' ω, S.next E (some (Silent.τ, ω)) * ∑' m', ω m'
              * (∑' s, macroFuture_trunc S n (macroExtend E m')
                  (macroExtend_term hT m') s * g s) := by
        rw [ENNReal.tsum_prod']
        refine tsum_congr fun ω => ?_
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun m' => ?_
        set σ' := (prev (macroExtend E m') (macroExtend_term hT m')).sched with hσ'
        have hbridge : (∑' t, m' t * (∑' s, branchTargetC S prev E hT t (some (ω, m')) s * g s))
            = ∑' s, macroFuture_trunc S n (macroExtend E m')
                (macroExtend_term hT m') s * g s := by
          have hstep : ∀ t, m' t * (∑' s, branchTargetC S prev E hT t (some (ω, m')) s * g s)
              = m' t * (∑' e, σ'.haltMass (PMF.pure t) e * g (e.1.endState e.2)) := by
            intro t
            by_cases ht : t ∈ (m').support
            · congr 1
              rw [show branchTargetC S prev E hT t (some (ω, m'))
                  = pushforwardPMF σ' (PMF.pure t)
                    (haltMass_pure_of_source _ m' (ctPrevHalt S prev E hT m') t ht) from dif_pos ht]
              exact pushforwardPMF_integrate _ (PMF.pure t) _ g
            · rw [PMF.mem_support_iff, not_not] at ht
              rw [ht, zero_mul, zero_mul]
          rw [tsum_congr hstep]
          have hsrc : (macroExtend E m').endState (macroExtend_term hT m') = m' :=
            macroExtend_endState hT m'
          have hint := (prev (macroExtend E m') (macroExtend_term hT m')).integrate g
          rw [hsrc, ← hσ'] at hint
          calc (∑' t, m' t * (∑' e, σ'.haltMass (PMF.pure t) e * g (e.1.endState e.2)))
              = ∑' t, ∑' e, m' t * (σ'.haltMass (PMF.pure t) e * g (e.1.endState e.2)) :=
                tsum_congr fun t => ENNReal.tsum_mul_left.symm
            _ = ∑' e, ∑' t, m' t * (σ'.haltMass (PMF.pure t) e * g (e.1.endState e.2)) :=
                ENNReal.tsum_comm
            _ = ∑' e, (∑' t, m' t * σ'.haltMass (PMF.pure t) e) * g (e.1.endState e.2) := by
                refine tsum_congr fun e => ?_
                rw [← ENNReal.tsum_mul_right]
                exact tsum_congr fun t => by rw [mul_assoc]
            _ = ∑' e, σ'.haltMass m' e * g (e.1.endState e.2) := by
                refine tsum_congr fun e => ?_
                rw [← WeakScheduler.haltMass_init_mix]
            _ = ∑' s, macroFuture_trunc S n (macroExtend E m')
                  (macroExtend_term hT m') s * g s := hint
        rw [← hbridge, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun t => ?_
        show S.next E (some (Silent.τ, ω)) * ω m' * m' t
            * (∑' s, branchTargetC S prev E hT t (some (ω, m')) s * g s)
          = S.next E (some (Silent.τ, ω))
            * (ω m' * (m' t * (∑' s, branchTargetC S prev E hT t (some (ω, m')) s * g s)))
        ring
      have h123 : (∑' e, (WeakScheduler.bind (oneDecisionC S E hT)
              (fun t => contC S prev E hT t)).haltMass (E.endState hT) e
            * g (e.1.endState e.2))
          = ∑' t, macroFuture_trunc S 1 E hT t
              * (∑' s, ((ctPost S E hT t).bind (branchTargetC S prev E hT t)) s * g s) := by
        rw [WeakScheduler.bind_compose_integrate]
        have hin : ∀ f₁ : {e : AlterSeq State Label // e.trans.Terminates},
            (∑' f₂, (contC S prev E hT (f₁.1.endState f₁.2)).haltMass
                (PMF.pure (f₁.1.endState f₁.2)) f₂ * g (f₂.1.endState f₂.2))
            = ∑' s, ((ctPost S E hT (f₁.1.endState f₁.2)).bind
                (branchTargetC S prev E hT (f₁.1.endState f₁.2))) s * g s :=
          fun f₁ => contC_integrate S prev E hT (f₁.1.endState f₁.2) g
        simp_rw [hin]
        exact oneDecisionC_integrate_trunc S E hT
          (fun t => ∑' s, ((ctPost S E hT t).bind (branchTargetC S prev E hT t)) s * g s)
      rw [h123, macroFuture_trunc_integrate_succ S n E hT g, tsum_congr hΦcancel,
        ENNReal.tsum_comm, tsumOpt, hTermA, hTermB] }

/-- The concrete coherent bind tower, by `Nat.rec`. Depth `0` is the immediate-stop
witness `WeakScheduler.stop`; depth `n+1` is `towerStepC`. -/
noncomputable def towerDataC (S : WeakScheduler (𝒟(sys^w))) :
    (n : ℕ) → (E : AlterSeq (PMF State) Label) → (hT : E.trans.Terminates) →
      TowerDataC S n E hT
  | 0, E, hT =>
    { sched := WeakScheduler.stop sys
      integrate := fun g => by
        simpa only [macroFuture_trunc] using stop_integrate (E.endState hT) g }
  | n + 1, E, hT => towerStepC S n (fun E' hT' => towerDataC S n E' hT') E hT
  termination_by n => n

/-- The depth-`n` concrete tower scheduler witnessing
`weakTau sys (E.end) (macroFuture_trunc S n E hT)`, with numerator-exposed `next`. -/
noncomputable def towerSchedC (S : WeakScheduler (𝒟(sys^w)))
    (n : ℕ) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) : WeakScheduler sys :=
  (towerDataC S n E hT).sched

/-- **The concrete tower realizes the truncation.** -/
theorem towerSchedC_integrate (S : WeakScheduler (𝒟(sys^w)))
    (n : ℕ) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (g : State → ENNReal) :
    (∑' e, (towerSchedC S n E hT).haltMass (E.endState hT) e * g (e.1.endState e.2))
      = ∑' s, macroFuture_trunc S n E hT s * g s :=
  (towerDataC S n E hT).integrate g

/-- **The concrete tower halts almost surely** from `E.end`. -/
theorem towerSchedC_halts (S : WeakScheduler (𝒟(sys^w)))
    (n : ℕ) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) :
    (∑' e, (towerSchedC S n E hT).haltMass (E.endState hT) e) = 1 := by
  have h := towerSchedC_integrate S n E hT (fun _ => 1)
  simp only [mul_one] at h
  rw [h, (macroFuture_trunc S n E hT).tsum_coe]

/-! ### Numerator exposure of the concrete tower (S3)

The unnormalized weights of `towerSchedC S n E hT |>.next e`: the joint (path-measure ×
belief) mass `twNum S n E hT e o = twDenom · next e o`, where `twDenom` is the composite
path measure `probOf e`. Because each layer of the concrete tower is a genuine
belief/`bind` scheduler, `twDenom` is a bona-fide sub-probability (`≤ 1`, uniformly in `n`),
and `∑' o, twNum e o = twDenom e` (the belief `next e` is a PMF). These are the
`⨆`-ready per-history handles the σ\* limit consumes; the monotone end-state spine is the
existing `macroHalted`/`macroHalted_mono` (with `macroFuture_trunc = macroHalted +
macroResidual`), which `towerSchedC_integrate` realizes as the tower's halting pushforward. -/

open Classical in
/-- The exposed **denominator** (composite path measure `probOf e`) of `towerSchedC`'s
belief at a history `e` (0 off-termination). Uniformly `≤ 1` in `n`. -/
noncomputable def twDenom (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    ENNReal :=
  if h : e.trans.Terminates then
    (⟨E.endState hT, (towerSchedC S n E hT).toScheduler⟩ : ProbabilisticExecution sys).probOf e h
  else 0

/-- The exposed **numerator** of `towerSchedC S n E hT |>.next e` at emission `o`: the
unnormalized joint mass `twDenom · next e o`. -/
noncomputable def twNum (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label)
    (o : Option (Label × PMF State)) : ENNReal :=
  twDenom S n E hT e * (towerSchedC S n E hT).next e o

/-- The numerators over `o` sum to the denominator (`next e` is a PMF). -/
theorem twNum_tsum (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    (∑' o, twNum S n E hT e o) = twDenom S n E hT e := by
  unfold twNum
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

/-- **Uniform denominator bound.** `twDenom ≤ 1` for every depth `n` (each path measure
`probOf e ≤ init ≤ 1`): a finite bound independent of `n`, as the σ\* squeeze requires. -/
theorem twDenom_le_one (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    twDenom S n E hT e ≤ 1 := by
  classical
  unfold twDenom
  split
  · exact le_trans (ProbabilisticExecution.probOf_le_init _ _ _) (PMF.coe_le_one _ _)
  · exact zero_le_one

/-- **Monotone end-state spine** (the σ\*-pushforward target). The tower's depth-`n`
halting pushforward `macroFuture_trunc` splits as `macroHalted + macroResidual`, and the
halted-within-`n` part `macroHalted` is monotone (`macroHalted_mono`) and bounded by `1`;
its `⨆ n` is the limit distribution the σ\* witness must realize. -/
theorem macroHalted_le_one (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (s : State) :
    macroHalted S n E hT s ≤ 1 := by
  calc macroHalted S n E hT s
      ≤ macroHalted S n E hT s + macroResidual S n E hT s := le_self_add
    _ = macroFuture_trunc S n E hT s := (macroFuture_trunc_decompose S n E hT s).symm
    _ ≤ 1 := (macroFuture_trunc S n E hT).coe_le_one s

/-! ### v5 Layer 1 — the cylinder mass `cylP` (the monotone cylinder limit)

For a fixed observable history `e`, the composite path measure `twDenom S n E hT e = probOf_n(e)`
is monotone non-decreasing in the tower depth `n` (paper verdict F5a): deepening the tower
only lets the `oneDecisionC`-halt-then-continue branch realize deeper cylinders (adding reach
mass), while already-reachable cylinders keep their (`n`-independent) belief weight — the
`beliefSched_probOf` normalizers cancel pointwise, so `probOf e = bDenom e` is an *unnormalized*
config-sum. `cylP e := ⨆ n, twDenom S n E hT e` is the resulting cylinder limit. -/

/-- **Cylinder mass at history `e`** for the depth-`n` concrete tower rooted at `(E, hT)`:
the `⨆ n` of the composite path measure `twDenom S n E hT e = probOf_n(e)`. Layer 1 of the
v5 cylinder-ratio scheduler. -/
noncomputable def cylP (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    ENNReal :=
  ⨆ n, twDenom S n E hT e

/-- `cylP ≤ 1` (uniform `twDenom_le_one` under the `⨆`). -/
theorem cylP_le_one (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    cylP S E hT e ≤ 1 :=
  iSup_le (fun n => twDenom_le_one S n E hT e)

/-- **Base value (telescope root).** At the empty concrete history `⟨s₀, nil⟩` the tower path
measure is the source mass `(E.endState hT) s₀`, `n`-independent, so `cylP = (E.endState hT) s₀`. -/
theorem cylP_root (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (s₀ : State) :
    cylP S E hT ⟨s₀, Seq.nil⟩ = (E.endState hT) s₀ := by
  have hconst : ∀ n, twDenom S n E hT ⟨s₀, Seq.nil⟩ = (E.endState hT) s₀ := by
    intro n
    unfold twDenom
    rw [dif_pos Stream'.Seq.terminates_nil]
    simp only [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState]
  unfold cylP
  simp only [hconst, iSup_const]

/-- **Per-depth cylinder super-step (F5b).** At a fixed tower depth `n`, the cylinder reach
masses of the one-step extensions of `e` sum to at most the reach mass of `e`:
`∑' t, twDenom (e·t) ≤ twDenom e`. This is `probOf_append_singleton` (each extension peels one
kernel factor) followed by `kernel_tsum_le_one` (the one-step kernel mass is `≤ 1`). Independent
of the depth `n` (no monotonicity used); the `n`-dependence enters only when `⨆ n` is taken. -/
theorem twDenom_super_step (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label)
    (he : e.trans.Terminates) :
    (∑' t : Label × State, twDenom S n E hT ⟨e.init, e.trans.append (Seq.cons t Seq.nil)⟩)
      ≤ twDenom S n E hT e := by
  classical
  set pe : ProbabilisticExecution sys :=
    ⟨E.endState hT, (towerSchedC S n E hT).toScheduler⟩ with hpe
  have hbase : twDenom S n E hT e = pe.probOf e he := by
    unfold twDenom; rw [dif_pos he, ← hpe]
  have hstep : ∀ t : Label × State,
      twDenom S n E hT ⟨e.init, e.trans.append (Seq.cons t Seq.nil)⟩
        = pe.probOf e he * pe.kernel e t := by
    intro t
    have hcons : (Seq.cons t Seq.nil : Seq (Label × State)).Terminates :=
      Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
    have happ : (e.trans.append (Seq.cons t Seq.nil)).Terminates :=
      ⟨_, Stream'.Seq.terminatedAt_append_find he hcons.choose_spec⟩
    unfold twDenom
    rw [dif_pos happ, ← hpe]
    exact pe.probOf_append_singleton e.init e.trans he t happ
  rw [tsum_congr hstep, ENNReal.tsum_mul_left, hbase]
  exact mul_le_of_le_one_right' (pe.kernel_tsum_le_one e)

/-! ### F5c — `cylMono` : cylinder reach mass is monotone in tower depth -/

/-- **Source split of `probOf`.** The path measure from a general source `μ` factors as
the source mass at the start times the Dirac-`pure`-sourced path measure. Reverse induction
on the transition list (`kernel` is source-independent, so only the base init factor differs). -/
private theorem probOf_source_split (sch : Scheduler sys) (μ : PMF State)
    (s₀ : State) (L : List (Label × State)) :
    (⟨μ, sch⟩ : ProbabilisticExecution sys).probOf ⟨s₀, Seq.ofList L⟩
        (Stream'.Seq.terminates_ofList L)
      = μ s₀ * (⟨PMF.pure s₀, sch⟩ : ProbabilisticExecution sys).probOf ⟨s₀, Seq.ofList L⟩
          (Stream'.Seq.terminates_ofList L) := by
  classical
  induction L using List.reverseRecOn with
  | nil =>
    rw [(⟨μ, sch⟩ : ProbabilisticExecution sys).probOf_congr
          ⟨s₀, Seq.ofList ([] : List (Label × State))⟩ ⟨s₀, Seq.nil⟩
          (by rw [Stream'.Seq.ofList_nil]) _ Stream'.Seq.terminates_nil,
        (⟨PMF.pure s₀, sch⟩ : ProbabilisticExecution sys).probOf_congr
          ⟨s₀, Seq.ofList ([] : List (Label × State))⟩ ⟨s₀, Seq.nil⟩
          (by rw [Stream'.Seq.ofList_nil]) _ Stream'.Seq.terminates_nil,
        ProbabilisticExecution.probOf_nil, ProbabilisticExecution.probOf_nil]
    change μ s₀ = μ s₀ * (PMF.pure s₀ : PMF State) s₀
    rw [PMF.pure_apply_self, mul_one]
  | append_singleton rest last ih =>
    have hsplit : (Seq.ofList (rest ++ [last]) : Seq (Label × State))
        = (Seq.ofList rest).append (Seq.cons last Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have hrest_fin : (Seq.ofList rest : Seq (Label × State)).Terminates :=
      Stream'.Seq.terminates_ofList _
    have hFinS : ((Seq.ofList rest).append (Seq.cons last Seq.nil)).Terminates := by
      rw [← hsplit]; exact Stream'.Seq.terminates_ofList _
    rw [(⟨μ, sch⟩ : ProbabilisticExecution sys).probOf_congr
          ⟨s₀, Seq.ofList (rest ++ [last])⟩ ⟨s₀, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩
          (by rw [hsplit]) _ hFinS,
        ProbabilisticExecution.probOf_append_singleton _ s₀ (Seq.ofList rest) hrest_fin last hFinS,
        (⟨PMF.pure s₀, sch⟩ : ProbabilisticExecution sys).probOf_congr
          ⟨s₀, Seq.ofList (rest ++ [last])⟩ ⟨s₀, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩
          (by rw [hsplit]) _ hFinS,
        ProbabilisticExecution.probOf_append_singleton _ s₀ (Seq.ofList rest) hrest_fin last hFinS,
        ih,
        show (⟨μ, sch⟩ : ProbabilisticExecution sys).kernel ⟨s₀, Seq.ofList rest⟩ last
          = (⟨PMF.pure s₀, sch⟩ : ProbabilisticExecution sys).kernel ⟨s₀, Seq.ofList rest⟩ last
          from rfl, mul_assoc]

/-- Termwise `bindWeight` monotonicity from a pointwise continuation bound. -/
private theorem bindWeight_mono (σ : Scheduler sys) (k₁ k₂ : State → Scheduler sys)
    (hk : ∀ (t : State) (e' : AlterSeq State Label) (he' : e'.trans.Terminates),
      (⟨PMF.pure t, k₁ t⟩ : ProbabilisticExecution sys).probOf e' he'
        ≤ (⟨PMF.pure t, k₂ t⟩ : ProbabilisticExecution sys).probOf e' he')
    (e : AlterSeq State Label) (hT : e.trans.Terminates) (o : Option ℕ) :
    Scheduler.bindWeight σ k₁ e hT o ≤ Scheduler.bindWeight σ k₂ e hT o := by
  cases o with
  | none => exact le_rfl
  | some j =>
    by_cases hj : j < e.trans.length hT
    · show (if _hj : j < e.trans.length hT then _ else 0)
        ≤ (if _hj : j < e.trans.length hT then _ else 0)
      rw [dif_pos hj, dif_pos hj]
      exact mul_le_mul_left'
        (hk (WeakScheduler.stateAfter e j) ⟨WeakScheduler.stateAfter e j, e.trans.drop j⟩
          (WeakScheduler.drop_terminates hT j)) _
    · show (if _hj : j < e.trans.length hT then _ else 0)
        ≤ (if _hj : j < e.trans.length hT then _ else 0)
      rw [dif_neg hj, dif_neg hj]

/-- **Bind monotonicity of the Dirac path measure.** If continuation `k₁ ≤ k₂` pointwise
(on every Dirac-sourced path measure), then `bind σ k₁ ≤ bind σ k₂` on every Dirac path. -/
private theorem bind_probOf_mono (σ : Scheduler sys) (k₁ k₂ : State → Scheduler sys)
    (hk : ∀ (t : State) (e' : AlterSeq State Label) (he' : e'.trans.Terminates),
      (⟨PMF.pure t, k₁ t⟩ : ProbabilisticExecution sys).probOf e' he'
        ≤ (⟨PMF.pure t, k₂ t⟩ : ProbabilisticExecution sys).probOf e' he')
    (s₀ : State) (e : AlterSeq State Label) (he : e.trans.Terminates) :
    (⟨PMF.pure s₀, Scheduler.bind σ k₁⟩ : ProbabilisticExecution sys).probOf e he
      ≤ (⟨PMF.pure s₀, Scheduler.bind σ k₂⟩ : ProbabilisticExecution sys).probOf e he := by
  classical
  by_cases hinit : e.init = s₀
  · subst hinit
    have hofl : (Seq.ofList (e.trans.toList he) : Seq (Label × State)) = e.trans :=
      Stream'.Seq.ofList_toList e.trans he
    have hEeq : (⟨e.init, Seq.ofList (e.trans.toList he)⟩ : AlterSeq State Label) = e := by
      cases e; simp only [hofl]
    rw [← (⟨PMF.pure e.init, Scheduler.bind σ k₁⟩ : ProbabilisticExecution sys).probOf_congr
          ⟨e.init, Seq.ofList (e.trans.toList he)⟩ e hEeq
          (Stream'.Seq.terminates_ofList (e.trans.toList he)) he,
        ← (⟨PMF.pure e.init, Scheduler.bind σ k₂⟩ : ProbabilisticExecution sys).probOf_congr
          ⟨e.init, Seq.ofList (e.trans.toList he)⟩ e hEeq
          (Stream'.Seq.terminates_ofList (e.trans.toList he)) he,
        Scheduler.reach σ k₁ e.init (e.trans.toList he),
        Scheduler.reach σ k₂ e.init (e.trans.toList he)]
    exact ENNReal.tsum_le_tsum
      (fun o => bindWeight_mono σ k₁ k₂ hk ⟨e.init, Seq.ofList (e.trans.toList he)⟩
        (Stream'.Seq.terminates_ofList _) o)
  · have hz : (PMF.pure s₀ : PMF State) e.init = 0 := by rw [PMF.pure_apply, if_neg hinit]
    have h0 : ∀ k : State → Scheduler sys,
        (⟨PMF.pure s₀, Scheduler.bind σ k⟩ : ProbabilisticExecution sys).probOf e he = 0 := by
      intro k
      have hle : (⟨PMF.pure s₀, Scheduler.bind σ k⟩ : ProbabilisticExecution sys).probOf e he ≤ 0 := by
        refine le_trans (ProbabilisticExecution.probOf_le_init _ e he) ?_
        rw [ProbabilisticExecution.init_eq_initState]
        exact le_of_eq hz
      exact le_antisymm hle bot_le
    rw [h0 k₁, h0 k₂]

/-- **Continuation monotonicity** (takes the depth-`n` induction hypothesis explicitly).
The concrete continuation kernel is monotone from depth `n` to `n+1` on every Dirac path. -/
private theorem contC_probOf_mono (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (IH : ∀ (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (s₀ : State)
      (e : AlterSeq State Label) (he : e.trans.Terminates),
      (⟨PMF.pure s₀, (towerSchedC S n E hT).toScheduler⟩
          : ProbabilisticExecution sys).probOf e he
        ≤ (⟨PMF.pure s₀, (towerSchedC S (n+1) E hT).toScheduler⟩
          : ProbabilisticExecution sys).probOf e he)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (t : State)
    (e' : AlterSeq State Label) (he' : e'.trans.Terminates) :
    (⟨PMF.pure t, (contC S (fun E' hT' => towerDataC S n E' hT') E hT t).toScheduler⟩
        : ProbabilisticExecution sys).probOf e' he'
      ≤ (⟨PMF.pure t, (contC S (fun E' hT' => towerDataC S (n+1) E' hT') E hT t).toScheduler⟩
        : ProbabilisticExecution sys).probOf e' he' := by
  classical
  simp only [contC]
  rw [beliefSched_probOf (ctFam S (fun E' hT' => towerDataC S n E' hT') E hT)
        (ctPost S E hT t) (PMF.pure t) e' he',
    beliefSched_probOf (ctFam S (fun E' hT' => towerDataC S (n+1) E' hT') E hT)
      (ctPost S E hT t) (PMF.pure t) e' he']
  unfold bDenom
  refine ENNReal.tsum_le_tsum (fun x => mul_le_mul_left' ?_ _)
  cases x with
  | none => exact le_rfl
  | some p =>
    unfold bBranchProb
    rw [dif_pos he', dif_pos he']
    exact IH (macroExtend E p.2) (macroExtend_term hT p.2) t e' he'

/-- The immediate-stop path measure is a lower bound for any scheduler's path measure:
they agree on the empty history and `stop` gives `0` on every non-empty one (its kernel is `0`). -/
private theorem stop_probOf_le (sch : Scheduler sys) (μ : PMF State) (s₀ : State)
    (L : List (Label × State)) :
    (⟨μ, (WeakScheduler.stop sys).toScheduler⟩ : ProbabilisticExecution sys).probOf
        ⟨s₀, Seq.ofList L⟩ (Stream'.Seq.terminates_ofList L)
      ≤ (⟨μ, sch⟩ : ProbabilisticExecution sys).probOf
        ⟨s₀, Seq.ofList L⟩ (Stream'.Seq.terminates_ofList L) := by
  classical
  induction L using List.reverseRecOn with
  | nil =>
    rw [(⟨μ, (WeakScheduler.stop sys).toScheduler⟩ : ProbabilisticExecution sys).probOf_congr
        ⟨s₀, Seq.ofList ([] : List (Label × State))⟩ ⟨s₀, Seq.nil⟩
        (by rw [Stream'.Seq.ofList_nil]) _ Stream'.Seq.terminates_nil,
      (⟨μ, sch⟩ : ProbabilisticExecution sys).probOf_congr
        ⟨s₀, Seq.ofList ([] : List (Label × State))⟩ ⟨s₀, Seq.nil⟩
        (by rw [Stream'.Seq.ofList_nil]) _ Stream'.Seq.terminates_nil,
      ProbabilisticExecution.probOf_nil, ProbabilisticExecution.probOf_nil]
    exact le_rfl
  | append_singleton rest last _ih =>
    have hsplit : (Seq.ofList (rest ++ [last]) : Seq (Label × State))
        = (Seq.ofList rest).append (Seq.cons last Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have hrest_fin : (Seq.ofList rest : Seq (Label × State)).Terminates :=
      Stream'.Seq.terminates_ofList _
    have hFinS : ((Seq.ofList rest).append (Seq.cons last Seq.nil)).Terminates := by
      rw [← hsplit]; exact Stream'.Seq.terminates_ofList _
    have hker : (⟨μ, (WeakScheduler.stop sys).toScheduler⟩ : ProbabilisticExecution sys).kernel
        ⟨s₀, Seq.ofList rest⟩ last = 0 := by
      unfold ProbabilisticExecution.kernel
      refine ENNReal.tsum_eq_zero.mpr (fun ν => ?_)
      rw [show (⟨μ, (WeakScheduler.stop sys).toScheduler⟩
            : ProbabilisticExecution sys).scheduler.next ⟨s₀, Seq.ofList rest⟩ (some (last.1, ν))
          = (PMF.pure none : PMF (Option (Label × PMF State))) (some (last.1, ν)) from rfl,
        PMF.pure_apply_of_ne _ _ (by simp), zero_mul]
    rw [(⟨μ, (WeakScheduler.stop sys).toScheduler⟩ : ProbabilisticExecution sys).probOf_congr
        ⟨s₀, Seq.ofList (rest ++ [last])⟩ ⟨s₀, (Seq.ofList rest).append (Seq.cons last Seq.nil)⟩
        (by rw [hsplit]) _ hFinS,
      ProbabilisticExecution.probOf_append_singleton _ s₀ (Seq.ofList rest) hrest_fin last hFinS,
      hker, mul_zero]
    exact bot_le

/-- **Dirac-source cylinder monotonicity** (the induction on tower depth `n`). -/
private theorem twDenom_pure_mono (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (s₀ : State)
    (e : AlterSeq State Label) (he : e.trans.Terminates) :
    (⟨PMF.pure s₀, (towerSchedC S n E hT).toScheduler⟩
        : ProbabilisticExecution sys).probOf e he
      ≤ (⟨PMF.pure s₀, (towerSchedC S (n+1) E hT).toScheduler⟩
        : ProbabilisticExecution sys).probOf e he := by
  classical
  induction n generalizing E hT s₀ e he with
  | zero =>
    have h0 : towerSchedC S 0 E hT = WeakScheduler.stop sys := by
      show (towerDataC S 0 E hT).sched = _
      simp only [towerDataC]
    rw [h0]
    have hEeq : (⟨e.init, Seq.ofList (e.trans.toList he)⟩ : AlterSeq State Label) = e := by
      cases e; simp only [Stream'.Seq.ofList_toList _ he]
    rw [← (⟨PMF.pure s₀, (WeakScheduler.stop sys).toScheduler⟩
          : ProbabilisticExecution sys).probOf_congr ⟨e.init, Seq.ofList (e.trans.toList he)⟩ e hEeq
          (Stream'.Seq.terminates_ofList (e.trans.toList he)) he,
        ← (⟨PMF.pure s₀, (towerSchedC S 1 E hT).toScheduler⟩
          : ProbabilisticExecution sys).probOf_congr ⟨e.init, Seq.ofList (e.trans.toList he)⟩ e hEeq
          (Stream'.Seq.terminates_ofList (e.trans.toList he)) he]
    exact stop_probOf_le (towerSchedC S 1 E hT).toScheduler (PMF.pure s₀) e.init (e.trans.toList he)
  | succ n IH =>
    have hunf : ∀ (m : ℕ) (E' : AlterSeq (PMF State) Label) (hT' : E'.trans.Terminates),
        towerSchedC S (m+1) E' hT'
          = WeakScheduler.bind (oneDecisionC S E' hT')
              (fun t => contC S (fun E'' hT'' => towerDataC S m E'' hT'') E' hT' t) := by
      intro m E' hT'
      show (towerDataC S (m+1) E' hT').sched = _
      simp only [towerDataC, towerStepC]
    rw [hunf n E hT, hunf (n+1) E hT]
    exact bind_probOf_mono (oneDecisionC S E hT).toScheduler
      (fun t => (contC S (fun E'' hT'' => towerDataC S n E'' hT'') E hT t).toScheduler)
      (fun t => (contC S (fun E'' hT'' => towerDataC S (n+1) E'' hT'') E hT t).toScheduler)
      (fun t e' he' => contC_probOf_mono S n IH E hT t e' he') s₀ e he

/-- **`cylMono` — cylinder reach mass is monotone in tower depth.**
`twDenom S n E hT e ≤ twDenom S (n+1) E hT e`: deepening the tower only adds through-mass at
`e` (the belief normalizers cancel; `probOf = bDenom` is an unnormalized config sum). -/
theorem cylMono (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    twDenom S n E hT e ≤ twDenom S (n+1) E hT e := by
  classical
  unfold twDenom
  by_cases he : e.trans.Terminates
  · rw [dif_pos he, dif_pos he]
    have hEeq : (⟨e.init, Seq.ofList (e.trans.toList he)⟩ : AlterSeq State Label) = e := by
      cases e; simp only [Stream'.Seq.ofList_toList _ he]
    rw [← (⟨E.endState hT, (towerSchedC S n E hT).toScheduler⟩
          : ProbabilisticExecution sys).probOf_congr ⟨e.init, Seq.ofList (e.trans.toList he)⟩ e hEeq
          (Stream'.Seq.terminates_ofList (e.trans.toList he)) he,
        ← (⟨E.endState hT, (towerSchedC S (n+1) E hT).toScheduler⟩
          : ProbabilisticExecution sys).probOf_congr ⟨e.init, Seq.ofList (e.trans.toList he)⟩ e hEeq
          (Stream'.Seq.terminates_ofList (e.trans.toList he)) he,
        probOf_source_split (towerSchedC S n E hT).toScheduler (E.endState hT) e.init
          (e.trans.toList he),
        probOf_source_split (towerSchedC S (n+1) E hT).toScheduler (E.endState hT) e.init
          (e.trans.toList he)]
    exact mul_le_mul_left'
      (twDenom_pure_mono S n E hT e.init ⟨e.init, Seq.ofList (e.trans.toList he)⟩
        (Stream'.Seq.terminates_ofList _)) _
  · rw [dif_neg he, dif_neg he]

/-- **`cylP_super` — cylinder super-martingale step.** The cylinder limit masses of the
one-step extensions of `e` sum to at most the cylinder limit mass of `e`. The `∑'`/`⨆`
interchange (`tsum_iSup_of_monotone`, powered by `cylMono`) reduces it to the per-depth
`twDenom_super_step`. This is the key layer-1 inequality for the F5d σ\* construction. -/
theorem cylP_super (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label)
    (he : e.trans.Terminates) :
    (∑' t : Label × State, cylP S E hT ⟨e.init, e.trans.append (Seq.cons t Seq.nil)⟩)
      ≤ cylP S E hT e := by
  classical
  have hmono : ∀ t : Label × State,
      Monotone (fun n => twDenom S n E hT ⟨e.init, e.trans.append (Seq.cons t Seq.nil)⟩) :=
    fun t => monotone_nat_of_le_succ
      (fun n => cylMono S n E hT ⟨e.init, e.trans.append (Seq.cons t Seq.nil)⟩)
  calc (∑' t : Label × State, cylP S E hT ⟨e.init, e.trans.append (Seq.cons t Seq.nil)⟩)
      = ⨆ n, ∑' t : Label × State,
          twDenom S n E hT ⟨e.init, e.trans.append (Seq.cons t Seq.nil)⟩ :=
        tsum_iSup_of_monotone _ hmono
    _ ≤ ⨆ n, twDenom S n E hT e := iSup_mono (fun n => twDenom_super_step S n E hT e he)
    _ = cylP S E hT e := rfl

/-! ### F5d Layer 2 (T0) — abstract cylinder-mass helpers (scheduler-free)

`cylP_prefix_le` (single-term extraction from `cylP_super`) and `cylP_ne_top`
(from `cylP_le_one`). Both are pure `cylP`-level algebra, independent of any
scheduler — the only part of the F5d Layer-2 recipe that lands, since realizing
`cylP` as a scheduler's `probOf` (T1–T3) is blocked (see the F5d addendum). -/

/-- **Single-prefix bound.** A single one-step extension's cylinder mass is bounded
by the parent's, extracted termwise from `cylP_super` (`ENNReal.le_tsum`). -/
theorem cylP_prefix_le (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label)
    (he : e.trans.Terminates) (t : Label × State) :
    cylP S E hT ⟨e.init, e.trans.append (Seq.cons t Seq.nil)⟩ ≤ cylP S E hT e :=
  le_trans (ENNReal.le_tsum t) (cylP_super S E hT e he)

/-- `cylP` is never `⊤` (it is `≤ 1`). -/
theorem cylP_ne_top (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    cylP S E hT e ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (cylP_le_one S E hT e)


end PLTS
