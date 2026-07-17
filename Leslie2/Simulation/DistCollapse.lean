/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.DistMonad.DistTrace
import Leslie2.Weak.WeakScheduler
import Leslie2.Weak.WeakTransition

/-!
# The `𝒟`-collapse of an internal weak transition

A single internal weak transition of the distribution-monad lift `𝒟(sys)` out of a
Dirac source `PMF.pure ρ` collapses to an internal weak transition of the underlying
system `sys` out of `ρ`, with the `𝒟(sys)`-target flattened by the PMF-monad
multiplication `bind id`:

  `weakTau_dist_collapse : weakTau (𝒟(sys)) (PMF.pure ρ) Ν → weakTau sys ρ (Ν.bind id)`.

The witnessing `sys`-weak-scheduler is `Scheduler.lower` of the `𝒟(sys)`-witness
(`DistMonad/DistTraceBelief`), which un-disintegrates the trace-cone belief. Its
two `weakTau` obligations — a.s.-halting and the end-state pushforward — are the
`g = 1` and `g = [· = s]` slices of the halt-collapse identity
`ProbabilisticExecution.lower_haltMass_g_eq` (the analytic crux proven below):

  `∑' e, haltMass (lower pe') ρ e * g (endState e)
     = ∑' E, haltMass pe' (pure ρ) E * (∑' s, (endState E) s * g s)`,

which pushes each `𝒟(sys)`-history's end-*distribution* `endState E` through the
`bind id` flattening. `Scheduler.lower` is wrapped as a `WeakScheduler` via
`Scheduler.lower_internal_only`: its `some (l, μ')` emissions come only from the
underlying `𝒟(sys)`-scheduler's emissions, so an internal-only source scheduler
forces `l = τ`.
-/

open Stream'

namespace PLTS

variable {State Label : Type}

/-- Local copy of `System.map_ofList` (which is `private` in `Systems/Trace.lean`):
mapping `Prod.fst` over `Seq.ofList` equals `Seq.ofList` of the mapped list. -/
private theorem map_ofList' {S L : Type} (l : List (L × S)) :
    (Seq.ofList l).map Prod.fst = Seq.ofList (l.map Prod.fst) := by
  induction l with
  | nil => rw [Stream'.Seq.ofList_nil, Stream'.Seq.map_nil, List.map_nil, Stream'.Seq.ofList_nil]
  | cons a l ih =>
    rw [Stream'.Seq.ofList_cons, Stream'.Seq.map_cons, List.map_cons, Stream'.Seq.ofList_cons, ih]

open Classical in
/-- **Target 1 (halt factor).** The lowered scheduler's `none`-mass at a
terminating `sys`-history `e` factors through the trace-cone belief and the
underlying scheduler's `none`-mass. The `some (l, ω)` branch of the `lower`
scheduler's inner match maps into `some …`, so contributes `0` at `none`. -/
theorem ProbabilisticExecution.lower_next_none_eq
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys))
    (e : AlterSeq State Label) (h_term : e.trans.Terminates) :
    (Scheduler.lower pe').next e none
      = ∑' E : AlterSeq (PMF State) Label,
          pe'.beliefTC ((e.trans.toList h_term).map Prod.fst) (e.endState h_term) E *
            pe'.scheduler.next E none := by
  classical
  change (if h : e.trans.Terminates then
      (pe'.beliefTC ((e.trans.toList h).map Prod.fst) (e.endState h)).bind (fun E =>
        (pe'.scheduler.next E).bind (fun opt =>
          match opt with
          | none => PMF.pure none
          | some (l, ω) =>
            (pe'.distHyperKernel E l ω (e.endState h)).map (fun μ' => some (l, μ'))))
    else PMF.pure none) none = _
  rw [dif_pos h_term, PMF.bind_apply]
  refine tsum_congr (fun E => ?_)
  congr 1
  -- Inner: `((next E).bind matchfn) none = next E none`.
  rw [PMF.bind_apply]
  -- Only `opt = none` contributes; `some (l, ω)` maps into `some …`.
  refine tsum_eq_single none ?_ |>.trans ?_
  · rintro (_ | ⟨l, ω⟩) hopt
    · exact absurd rfl hopt
    · -- `((distHyperKernel …).map (some ∘ …)) none = 0`.
      rw [show (match (some (l, ω) : Option (Label × PMF (PMF State))) with
          | none => PMF.pure none
          | some (l, ω) => (pe'.distHyperKernel E l ω (e.endState h_term)).map
              (fun μ' => some (l, μ')))
          = (pe'.distHyperKernel E l ω (e.endState h_term)).map (fun μ' => some (l, μ')) from rfl]
      rw [PMF.map_apply]
      refine mul_eq_zero_of_right _ ?_
      rw [ENNReal.tsum_eq_zero]
      intro μ'
      exact if_neg (by simp)
  · -- `opt = none`: `(match none …) none = (PMF.pure none) none = 1`.
    rw [show (match (none : Option (Label × PMF (PMF State))) with
        | none => PMF.pure none
        | some (l, ω) => (pe'.distHyperKernel E l ω (e.endState h_term)).map
            (fun μ' => some (l, μ')))
        = (PMF.pure (none : Option (Label × PMF State))) from rfl]
    rw [PMF.pure_apply]
    simp

open Classical in
/-- **Target 2, per-label-list crux (the belief-cancellation).** For each label
list `labs`, the `𝒟(sys)`-side halt mass over histories with label list `labs`
equals `pe'`'s level-mass integrated against the "halt g-factor"
`hHalt labs s = ∑' E', beliefTC labs s E' · next E' none`. This is the halt
analogue of the RHS-expansion in `lower_labProb_eq_aux`'s `hLmid` block:
`beliefTC_normalize_cancel` discharges the entanglement between the outer
`∑' E` weight and the inner belief `∑' E'`. -/
theorem ProbabilisticExecution.halt_labMass_crux
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys)) (labs : List Label) :
    pe'.labMass labs
        (fun μ : PMF State => ∑' s : State, μ s *
          (∑' E' : AlterSeq (PMF State) Label,
            pe'.beliefTC labs s E' * pe'.scheduler.next E' none))
      = ∑' E : AlterSeq (PMF State) Label,
          dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
            (fun h => pe'.probOf E h.1 * pe'.scheduler.next E none) (fun _ => 0) := by
  classical
  -- Abbreviate the per-state halt factor.
  set Hfun : State → ENNReal := fun s =>
      ∑' E' : AlterSeq (PMF State) Label,
        pe'.beliefTC labs s E' * pe'.scheduler.next E' none with hHfun
  -- Step A: `labMass labs (μ ↦ ∑' s, μ s · Hfun s) = ∑' E₀, ∑' s, beliefTCw labs s E₀ · Hfun s`.
  have stepA : (pe'.labMass labs (fun μ : PMF State => ∑' s : State, μ s * Hfun s))
      = ∑' E₀ : AlterSeq (PMF State) Label, ∑' s : State,
          pe'.beliefTCw labs s E₀ * Hfun s := by
    unfold ProbabilisticExecution.labMass
    refine tsum_congr (fun E₀ => ?_)
    by_cases hc : E₀.trans.Terminates ∧ E₀.trans.map Prod.fst = Seq.ofList labs
    · rw [dif_pos hc, ← ENNReal.tsum_mul_left]
      refine tsum_congr (fun s => ?_)
      have hbw : pe'.beliefTCw labs s E₀ = pe'.probOf E₀ hc.1 * (E₀.endState hc.1) s := by
        unfold ProbabilisticExecution.beliefTCw; rw [dif_pos hc]
      rw [hbw]; ring
    · rw [dif_neg hc]
      have hz : ∀ s : State, pe'.beliefTCw labs s E₀ = 0 := by
        intro s; unfold ProbabilisticExecution.beliefTCw; rw [dif_neg hc]
      simp only [hz, zero_mul, tsum_zero]
  rw [stepA, ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_right]
  simp only [hHfun]
  -- Step B: belief-normalizer cancellation per state `b`.
  have stepB : ∀ b : State,
      (∑' i : AlterSeq (PMF State) Label, pe'.beliefTCw labs b i) *
        (∑' E' : AlterSeq (PMF State) Label,
          pe'.beliefTC labs b E' * pe'.scheduler.next E' none)
      = ∑' E' : AlterSeq (PMF State) Label,
          pe'.beliefTCw labs b E' * pe'.scheduler.next E' none := by
    intro b
    exact pe'.beliefTC_normalize_cancel labs b
      (fun E' => pe'.scheduler.next E' none)
  simp_rw [stepB]
  rw [ENNReal.tsum_comm]
  -- Now: `∑' E', (∑' s, beliefTCw labs s E') · next E' none = RHS`.
  refine tsum_congr (fun E => ?_)
  by_cases hc : E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs
  · rw [dif_pos hc]
    have hbw : ∀ s : State,
        pe'.beliefTCw labs s E = pe'.probOf E hc.1 * (E.endState hc.1) s := by
      intro s; unfold ProbabilisticExecution.beliefTCw; rw [dif_pos hc]
    simp_rw [hbw]
    -- `∑' s, probOf E · (E.endState) s · next E none`; factor `(E.endState) s` alone.
    rw [show (∑' a : State, pe'.probOf E hc.1 * (E.endState hc.1) a * pe'.scheduler.next E none)
          = ∑' a : State, (E.endState hc.1) a *
              (pe'.probOf E hc.1 * pe'.scheduler.next E none) from
        tsum_congr (fun a => by ring)]
    rw [ENNReal.tsum_mul_right, (E.endState hc.1).tsum_coe, one_mul]
  · have hz : ∀ s : State, pe'.beliefTCw labs s E = 0 := by
      intro s; unfold ProbabilisticExecution.beliefTCw; rw [dif_neg hc]
    rw [dif_neg hc]
    simp only [hz, zero_mul, tsum_zero]

open Classical in
/-- **Target 3, per-label-list crux (`g`-integrated belief-cancellation).** The
`g`-weighted generalization of `halt_labMass_crux`: `pe'`'s level-mass against the
halt g-factor times `g` collapses to the halt mass weighted by the pushforward
expectation `∑' s, (E.endState) s · g s`. Same `beliefTC_normalize_cancel`
discharge; the `g = 1` slice recovers `halt_labMass_crux`. -/
theorem ProbabilisticExecution.halt_labMass_crux_g
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys)) (labs : List Label) (g : State → ENNReal) :
    pe'.labMass labs
        (fun μ : PMF State => ∑' s : State, μ s *
          ((∑' E' : AlterSeq (PMF State) Label,
            pe'.beliefTC labs s E' * pe'.scheduler.next E' none) * g s))
      = ∑' E : AlterSeq (PMF State) Label,
          dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
            (fun h => pe'.probOf E h.1 * pe'.scheduler.next E none *
              (∑' s : State, (E.endState h.1) s * g s)) (fun _ => 0) := by
  classical
  -- Abbreviate the per-state factor `Hg s = hHalt s · g s`.
  set Hg : State → ENNReal := fun s =>
      (∑' E' : AlterSeq (PMF State) Label,
        pe'.beliefTC labs s E' * pe'.scheduler.next E' none) * g s with hHg
  -- Step A: `labMass labs (μ ↦ ∑' s, μ s · Hg s) = ∑' E₀, ∑' s, beliefTCw labs s E₀ · Hg s`.
  have stepA : (pe'.labMass labs (fun μ : PMF State => ∑' s : State, μ s * Hg s))
      = ∑' E₀ : AlterSeq (PMF State) Label, ∑' s : State,
          pe'.beliefTCw labs s E₀ * Hg s := by
    unfold ProbabilisticExecution.labMass
    refine tsum_congr (fun E₀ => ?_)
    by_cases hc : E₀.trans.Terminates ∧ E₀.trans.map Prod.fst = Seq.ofList labs
    · rw [dif_pos hc, ← ENNReal.tsum_mul_left]
      refine tsum_congr (fun s => ?_)
      have hbw : pe'.beliefTCw labs s E₀ = pe'.probOf E₀ hc.1 * (E₀.endState hc.1) s := by
        unfold ProbabilisticExecution.beliefTCw; rw [dif_pos hc]
      rw [hbw]; ring
    · rw [dif_neg hc]
      have hz : ∀ s : State, pe'.beliefTCw labs s E₀ = 0 := by
        intro s; unfold ProbabilisticExecution.beliefTCw; rw [dif_neg hc]
      simp only [hz, zero_mul, tsum_zero]
  rw [stepA, ENNReal.tsum_comm]
  -- Peel `g s` off `Hg s`: `beliefTCw · (hHalt · g s) = (beliefTCw · hHalt) · g s`... but we
  -- need the belief-cancellation on `hHalt` alone, so keep `g s` as a per-`s` right factor.
  simp only [hHg]
  -- Rework each `s`-sum: `∑' E₀, beliefTCw s E₀ · (hHalt s · g s)
  --   = (∑' E₀, beliefTCw s E₀) · hHalt s · g s`.
  rw [show (∑' s : State, ∑' E₀ : AlterSeq (PMF State) Label, pe'.beliefTCw labs s E₀ *
        ((∑' E' : AlterSeq (PMF State) Label,
          pe'.beliefTC labs s E' * pe'.scheduler.next E' none) * g s))
      = ∑' s : State,
          (∑' i : AlterSeq (PMF State) Label, pe'.beliefTCw labs s i) *
            (∑' E' : AlterSeq (PMF State) Label,
              pe'.beliefTC labs s E' * pe'.scheduler.next E' none) * g s from by
    refine tsum_congr (fun s => ?_)
    -- Pull the compound right factor `hHalt s · g s` out, then reassociate.
    rw [ENNReal.tsum_mul_right, mul_assoc]]
  -- Step B: belief-normalizer cancellation per state `s` (on the `hHalt` factor).
  have stepB : ∀ b : State,
      (∑' i : AlterSeq (PMF State) Label, pe'.beliefTCw labs b i) *
        (∑' E' : AlterSeq (PMF State) Label,
          pe'.beliefTC labs b E' * pe'.scheduler.next E' none)
      = ∑' E' : AlterSeq (PMF State) Label,
          pe'.beliefTCw labs b E' * pe'.scheduler.next E' none := by
    intro b
    exact pe'.beliefTC_normalize_cancel labs b
      (fun E' => pe'.scheduler.next E' none)
  simp_rw [stepB]
  -- Now: `∑' s, (∑' E', beliefTCw labs s E' · next E' none) · g s`; swap to `∑' E'`.
  rw [show (∑' s : State,
        (∑' E' : AlterSeq (PMF State) Label,
          pe'.beliefTCw labs s E' * pe'.scheduler.next E' none) * g s)
      = ∑' E' : AlterSeq (PMF State) Label, ∑' s : State,
          pe'.beliefTCw labs s E' * pe'.scheduler.next E' none * g s from by
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun s => ?_)
    rw [← ENNReal.tsum_mul_right]]
  refine tsum_congr (fun E => ?_)
  by_cases hc : E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs
  · rw [dif_pos hc]
    have hbw : ∀ s : State,
        pe'.beliefTCw labs s E = pe'.probOf E hc.1 * (E.endState hc.1) s := by
      intro s; unfold ProbabilisticExecution.beliefTCw; rw [dif_pos hc]
    simp_rw [hbw]
    -- `∑' s, probOf E · (endState E) s · next E none · g s
    --   = probOf E · next E none · (∑' s, (endState E) s · g s)`.
    rw [show (∑' s : State, pe'.probOf E hc.1 * (E.endState hc.1) s *
          pe'.scheduler.next E none * g s)
        = ∑' s : State, ((E.endState hc.1) s * g s) *
            (pe'.probOf E hc.1 * pe'.scheduler.next E none) from
      tsum_congr (fun s => by ring)]
    rw [ENNReal.tsum_mul_right]
    ring
  · have hz : ∀ s : State, pe'.beliefTCw labs s E = 0 := by
      intro s; unfold ProbabilisticExecution.beliefTCw; rw [dif_neg hc]
    rw [dif_neg hc]
    simp only [hz, zero_mul, tsum_zero]

open Classical in
/-- **Regroup a terminating-execution sum by label list.** Any function
`G : (e) → e.trans.Terminates → ENNReal` summed over the subtype of terminating
executions equals its double sum over `(labs, e)` with the label-list `dite`.
Each terminating `e` has a unique label list, giving a bijection. -/
theorem tsum_terminates_eq_labs_sum {S L : Type}
    (G : (e : AlterSeq S L) → e.trans.Terminates → ENNReal) :
    (∑' e : {e : AlterSeq S L // e.trans.Terminates}, G e.1 e.2)
      = ∑' labs : List L, ∑' e : AlterSeq S L,
          dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs)
            (fun h => G e h.1) (fun _ => 0) := by
  classical
  -- Combine the RHS double sum into a single sum over `List L × AlterSeq S L`.
  rw [← ENNReal.tsum_prod' (f := fun p : List L × AlterSeq S L =>
      dite (p.2.trans.Terminates ∧ Seq.map Prod.fst p.2.trans = (↑p.1 : Seq L))
        (fun h => G p.2 h.1) (fun _ => 0))]
  -- Abbreviate the RHS product summand `g`.
  set g : List L × AlterSeq S L → ENNReal := fun p =>
      dite (p.2.trans.Terminates ∧ Seq.map Prod.fst p.2.trans = (↑p.1 : Seq L))
        (fun h => G p.2 h.1) (fun _ => 0) with hg_def
  -- A nonzero `g p` forces its `dite` condition (in particular `p.2` terminates).
  have g_cond : ∀ p : List L × AlterSeq S L, g p ≠ 0 →
      p.2.trans.Terminates ∧ Seq.map Prod.fst p.2.trans = (↑p.1 : Seq L) := by
    intro p hp
    by_contra hc
    rw [hg_def] at hp; simp only at hp; rw [dif_neg hc] at hp; exact hp rfl
  -- Bijection: a nonzero product-index `(labs, e)` maps to the subtype element `⟨e, hT⟩`.
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun p : Function.support g =>
      (⟨(p : List L × AlterSeq S L).2, (g_cond p.1 p.2).1⟩
        : {e : AlterSeq S L // e.trans.Terminates})) ?hinj ?hf ?hfg
  case hinj =>
    rintro ⟨⟨labs₁, e₁⟩, hp₁⟩ ⟨⟨labs₂, e₂⟩, hp₂⟩ hij
    simp only [Subtype.mk.injEq] at hij
    -- Same `e`, so same label list (from each side's `dite` condition).
    have h1 := g_cond (labs₁, e₁) hp₁
    have h2 := g_cond (labs₂, e₂) hp₂
    have hlabs : labs₁ = labs₂ := by
      apply Stream'.Seq.ofList_injective
      rw [← h1.2, hij, h2.2]
    subst hlabs; subst hij; rfl
  case hf =>
    rintro ⟨e, hT⟩ hmem
    -- Preimage: `(labels_e, e)`.
    have hmap : e.trans.map Prod.fst = Seq.ofList ((e.trans.toList hT).map Prod.fst) := by
      rw [← map_ofList', Stream'.Seq.ofList_toList e.trans hT]
    have hcond : e.trans.Terminates ∧ Seq.map Prod.fst e.trans
        = (↑((e.trans.toList hT).map Prod.fst) : Seq L) := ⟨hT, hmap⟩
    have hg_ne : g ((e.trans.toList hT).map Prod.fst, e) ≠ 0 := by
      rw [hg_def]; simp only; rw [dif_pos hcond]
      exact (Function.mem_support.mp hmem)
    exact ⟨⟨((e.trans.toList hT).map Prod.fst, e), hg_ne⟩, rfl⟩
  case hfg =>
    rintro ⟨⟨labs, e⟩, hp⟩
    change G e (g_cond (labs, e) hp).1 = g (labs, e)
    have hcond := g_cond (labs, e) hp
    rw [hg_def]; simp only [dif_pos hcond]

open Classical in
/-- **LHS halt-labMass = `lower.labMass` against the halt g-factor.** Under the
label-list guard, the lowered halt factor `(lower pe').next e none` equals
`hHalt labs (endState e)` by `lower_next_none_eq`, packaging the per-labs LHS
halt mass as a `labMass` of the lowered witness. -/
theorem ProbabilisticExecution.lower_haltLabMass_eq
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys)) (labs : List Label) :
    (∑' e : AlterSeq State Label,
        dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs)
          (fun h => pe'.lower.probOf e h.1 * (Scheduler.lower pe').next e none) (fun _ => 0))
      = pe'.lower.labMass labs
          (fun s => ∑' E' : AlterSeq (PMF State) Label,
            pe'.beliefTC labs s E' * pe'.scheduler.next E' none) := by
  classical
  unfold ProbabilisticExecution.labMass
  refine tsum_congr (fun e => ?_)
  by_cases hc : e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs
  · rw [dif_pos hc, dif_pos hc]
    congr 1
    -- `(lower pe').next e none = ∑' E, beliefTC labs (endState e) E · next E none`.
    rw [pe'.lower_next_none_eq e hc.1]
    -- The belief label list `(e.trans.toList hc.1).map Prod.fst` equals `labs`.
    have h_labs : (e.trans.toList hc.1).map Prod.fst = labs := by
      apply Stream'.Seq.ofList_injective
      rw [← map_ofList', Stream'.Seq.ofList_toList e.trans hc.1]; exact hc.2
    rw [h_labs]
  · rw [dif_neg hc, dif_neg hc]

open Classical in
/-- **Target 2 (a.s.-halting: `lower` preserves total halting mass).** The `g = 1`
halt-collapse: summing the lowered witness's halt mass over all terminating
`sys`-executions equals `pe'`'s halt mass over all terminating `𝒟(sys)`-histories.
Route (a): regroup by label list, then per label list use
`lower_labProb_eq_aux` (belief invariant) with the halt g-factor and
`halt_labMass_crux` (belief-normalizer cancellation of the halt factor). -/
theorem ProbabilisticExecution.lower_haltMass_eq
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys)) :
    (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        Scheduler.haltMass (Scheduler.lower pe') (pe'.initState.bind id) e)
      = ∑' E : {E : AlterSeq (PMF State) Label // E.trans.Terminates},
          Scheduler.haltMass pe'.scheduler pe'.initState E := by
  classical
  -- Regroup both subtype sums by label list.
  rw [tsum_terminates_eq_labs_sum
        (fun e (h : e.trans.Terminates) =>
          Scheduler.haltMass (Scheduler.lower pe') (pe'.initState.bind id) ⟨e, h⟩),
      tsum_terminates_eq_labs_sum
        (fun E (h : E.trans.Terminates) =>
          Scheduler.haltMass pe'.scheduler pe'.initState ⟨E, h⟩)]
  refine tsum_congr (fun labs => ?_)
  -- Rewrite both inner sums via the `haltMass` definition.
  have hLHS : (∑' e : AlterSeq State Label,
      dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs)
        (fun h => Scheduler.haltMass (Scheduler.lower pe') (pe'.initState.bind id) ⟨e, h.1⟩)
        (fun _ => 0))
      = ∑' e : AlterSeq State Label,
          dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs)
            (fun h => pe'.lower.probOf e h.1 * (Scheduler.lower pe').next e none)
            (fun _ => 0) := by
    refine tsum_congr (fun e => ?_)
    by_cases hc : e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs
    · rw [dif_pos hc, dif_pos hc]; rfl
    · rw [dif_neg hc, dif_neg hc]
  have hRHS : (∑' E : AlterSeq (PMF State) Label,
      dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
        (fun h => Scheduler.haltMass pe'.scheduler pe'.initState ⟨E, h.1⟩)
        (fun _ => 0))
      = ∑' E : AlterSeq (PMF State) Label,
          dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
            (fun h => pe'.probOf E h.1 * pe'.scheduler.next E none) (fun _ => 0) := by
    refine tsum_congr (fun E => ?_)
    by_cases hc : E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs
    · rw [dif_pos hc, dif_pos hc]; rfl
    · rw [dif_neg hc, dif_neg hc]
  rw [hLHS, hRHS,
    pe'.lower_haltLabMass_eq labs,
    pe'.lower_labProb_eq_aux labs
      (fun s => ∑' E' : AlterSeq (PMF State) Label,
        pe'.beliefTC labs s E' * pe'.scheduler.next E' none),
    pe'.halt_labMass_crux labs]

open Classical in
/-- **`g`-weighted LHS halt-labMass = `lower.labMass` against `hHalt · g`.** The
`g`-version of `lower_haltLabMass_eq`: under the label-list guard the lowered
halt factor is `hHalt labs (endState e)`, and the extra `g (endState e)` weight
folds into the `labMass` g-argument. -/
theorem ProbabilisticExecution.lower_haltLabMass_g_eq
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys)) (labs : List Label) (g : State → ENNReal) :
    (∑' e : AlterSeq State Label,
        dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs)
          (fun h => pe'.lower.probOf e h.1 * (Scheduler.lower pe').next e none *
            g (e.endState h.1)) (fun _ => 0))
      = pe'.lower.labMass labs
          (fun s => (∑' E' : AlterSeq (PMF State) Label,
            pe'.beliefTC labs s E' * pe'.scheduler.next E' none) * g s) := by
  classical
  unfold ProbabilisticExecution.labMass
  refine tsum_congr (fun e => ?_)
  by_cases hc : e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs
  · rw [dif_pos hc, dif_pos hc]
    have h_labs : (e.trans.toList hc.1).map Prod.fst = labs := by
      apply Stream'.Seq.ofList_injective
      rw [← map_ofList', Stream'.Seq.ofList_toList e.trans hc.1]; exact hc.2
    rw [pe'.lower_next_none_eq e hc.1, h_labs]
    ring
  · rw [dif_neg hc, dif_neg hc]

open Classical in
/-- **Target 3 (`g`-integrated halt-collapse).** The general `g`-form: the lowered
witness's `g (endState)`-weighted halt mass equals `pe'`'s halt mass weighted by
the `bind id` pushforward expectation `∑' s, (E.endState) s · g s`. The `g = 1`
slice recovers `lower_haltMass_eq`. Route (a) with `lower_labProb_eq_aux` and the
`g`-integrated belief cancellation `halt_labMass_crux_g`. -/
theorem ProbabilisticExecution.lower_haltMass_g_eq
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys)) (g : State → ENNReal) :
    (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        Scheduler.haltMass (Scheduler.lower pe') (pe'.initState.bind id) e *
          g (e.1.endState e.2))
      = ∑' E : {E : AlterSeq (PMF State) Label // E.trans.Terminates},
          Scheduler.haltMass pe'.scheduler pe'.initState E *
            (∑' s : State, (E.1.endState E.2) s * g s) := by
  classical
  rw [tsum_terminates_eq_labs_sum
        (fun e (h : e.trans.Terminates) =>
          Scheduler.haltMass (Scheduler.lower pe') (pe'.initState.bind id) ⟨e, h⟩ *
            g (e.endState h)),
      tsum_terminates_eq_labs_sum
        (fun E (h : E.trans.Terminates) =>
          Scheduler.haltMass pe'.scheduler pe'.initState ⟨E, h⟩ *
            (∑' s : State, (E.endState h) s * g s))]
  refine tsum_congr (fun labs => ?_)
  have hLHS : (∑' e : AlterSeq State Label,
      dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs)
        (fun h => Scheduler.haltMass (Scheduler.lower pe') (pe'.initState.bind id) ⟨e, h.1⟩ *
          g (e.endState h.1))
        (fun _ => 0))
      = ∑' e : AlterSeq State Label,
          dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs)
            (fun h => pe'.lower.probOf e h.1 * (Scheduler.lower pe').next e none *
              g (e.endState h.1))
            (fun _ => 0) := by
    refine tsum_congr (fun e => ?_)
    by_cases hc : e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs
    · rw [dif_pos hc, dif_pos hc]; rfl
    · rw [dif_neg hc, dif_neg hc]
  have hRHS : (∑' E : AlterSeq (PMF State) Label,
      dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
        (fun h => Scheduler.haltMass pe'.scheduler pe'.initState ⟨E, h.1⟩ *
          (∑' s : State, (E.endState h.1) s * g s))
        (fun _ => 0))
      = ∑' E : AlterSeq (PMF State) Label,
          dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
            (fun h => pe'.probOf E h.1 * pe'.scheduler.next E none *
              (∑' s : State, (E.endState h.1) s * g s)) (fun _ => 0) := by
    refine tsum_congr (fun E => ?_)
    by_cases hc : E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs
    · rw [dif_pos hc, dif_pos hc]; rfl
    · rw [dif_neg hc, dif_neg hc]
  rw [hLHS, hRHS,
    pe'.lower_haltLabMass_g_eq labs g,
    pe'.lower_labProb_eq_aux labs
      (fun s => (∑' E' : AlterSeq (PMF State) Label,
        pe'.beliefTC labs s E' * pe'.scheduler.next E' none) * g s),
    pe'.halt_labMass_crux_g labs g]

/-! ### Wrapping `Scheduler.lower` as a `WeakScheduler` -/

open Classical in
/-- **`Scheduler.lower` is internal-only.** Given a `𝒟(sys)`-scheduler that is
internal-only, its lowering emits only internal labels. The `some (l, μ')`
emissions of `(Scheduler.lower pe').next e` are produced by the
`(distHyperKernel E l ω …).map (some (l, ·))` branch, entered only when
`(l, ω) ∈ (pe'.scheduler.next E).support` for some `𝒟(sys)`-history `E` and
posterior `ω`; the source `internal_only` then forces `l = τ`. -/
theorem Scheduler.lower_internal_only
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys))
    (h_int : ∀ (E : AlterSeq (PMF State) Label) (l : Label) (ω : PMF (PMF State)),
      some (l, ω) ∈ (pe'.scheduler.next E).support → l = Silent.τ)
    (e : AlterSeq State Label) (l : Label) (μ' : PMF State)
    (h_supp : some (l, μ') ∈ ((Scheduler.lower pe').next e).support) :
    l = Silent.τ := by
  classical
  -- Unfold `Scheduler.lower.next`; the `none` branch cannot emit `some`.
  change some (l, μ') ∈
    (if h_term : e.trans.Terminates then
      (pe'.beliefTC ((e.trans.toList h_term).map Prod.fst) (e.endState h_term)).bind (fun E =>
        (pe'.scheduler.next E).bind (fun opt =>
          match opt with
          | none         => PMF.pure none
          | some (l', ω) =>
            (pe'.distHyperKernel E l' ω (e.endState h_term)).map
              (fun μ'' => some (l', μ''))))
    else PMF.pure none).support at h_supp
  by_cases h_term : e.trans.Terminates
  · rw [dif_pos h_term, PMF.mem_support_bind_iff] at h_supp
    obtain ⟨E, _, h_supp⟩ := h_supp
    rw [PMF.mem_support_bind_iff] at h_supp
    obtain ⟨opt, hopt_sch, h_supp⟩ := h_supp
    cases opt with
    | none =>
      change some (l, μ') ∈ (PMF.pure (α := Option (Label × PMF State)) none).support at h_supp
      rw [PMF.mem_support_pure_iff] at h_supp
      exact absurd h_supp (by simp)
    | some lω =>
      obtain ⟨l', ω⟩ := lω
      -- The `some (l', ω)` branch maps `(l', ·)`; matching `some (l, μ')` forces `l = l'`.
      change some (l, μ') ∈ ((pe'.distHyperKernel E l' ω (e.endState h_term)).map
        (fun μ'' => some (l', μ''))).support at h_supp
      rw [PMF.mem_support_map_iff] at h_supp
      obtain ⟨_, _, h_eq⟩ := h_supp
      simp only [Option.some.injEq, Prod.mk.injEq] at h_eq
      obtain ⟨rfl, _⟩ := h_eq
      -- `(l', ω)` is in the source scheduler's support; apply `h_int`.
      exact h_int E l' ω hopt_sch
  · rw [dif_neg h_term] at h_supp
    change some (l, μ') ∈ (PMF.pure (α := Option (Label × PMF State)) none).support at h_supp
    rw [PMF.mem_support_pure_iff] at h_supp
    exact absurd h_supp (by simp)

/-- The **lowered weak scheduler**: `Scheduler.lower` of a `𝒟(sys)`-weak-scheduler,
carrying the `internal_only` field via `Scheduler.lower_internal_only`. Its
underlying scheduler and hence `haltMass`/`probOf` are definitionally
`Scheduler.lower`. -/
noncomputable def WeakScheduler.lower
    {sys : System State Label} [Silent Label]
    {ρ : PMF State} (σ : WeakScheduler 𝒟(sys)) :
    WeakScheduler sys where
  toScheduler := Scheduler.lower ⟨PMF.pure ρ, σ.toScheduler⟩
  internal_only :=
    Scheduler.lower_internal_only ⟨PMF.pure ρ, σ.toScheduler⟩
      (fun E l ω h => σ.internal_only E l ω h)

open Classical in
/-- **The `𝒟`-collapse of an internal weak transition.** An internal weak
transition of the distribution-monad lift `𝒟(sys)` out of a Dirac source
`PMF.pure ρ`, targeting `Ν : PMF (PMF State)`, collapses to an internal weak
transition of `sys` out of `ρ` targeting the PMF-monad flattening `Ν.bind id`.

The witnessing `sys`-weak-scheduler is `WeakScheduler.lower` of the `𝒟(sys)`
witness. Its two `weakTau` obligations are the `g = 1` and `g = [· = s]` slices
of the halt-collapse identity `ProbabilisticExecution.lower_haltMass_g_eq`, which
flattens each `𝒟(sys)`-history's end-distribution `endState E` through `bind id`. -/
theorem weakTau_dist_collapse {State Label : Type} [Silent Label] {sys : System State Label}
    {ρ : PMF State} {Ν : PMF (PMF State)}
    (h : weakTau (𝒟(sys)) (PMF.pure ρ) Ν) : weakTau sys ρ (Ν.bind id) := by
  classical
  -- The `𝒟(sys)`-witness and its packaged execution.
  set σ : WeakScheduler 𝒟(sys) := h.witnessScheduler with hσ
  set pe' : ProbabilisticExecution 𝒟(sys) := ⟨PMF.pure ρ, σ.toScheduler⟩ with hpe'
  -- The lowered `sys`-weak-scheduler.
  set wσ : WeakScheduler sys := WeakScheduler.lower (ρ := ρ) σ with hwσ
  -- `pe'.initState.bind id = ρ` (both `defeq`); the lowered halt-mass reads through it.
  have hbindρ : pe'.initState.bind id = ρ := PMF.pure_bind ρ id
  -- `wσ.haltMass ρ e = Scheduler.haltMass (Scheduler.lower pe') (pe'.initState.bind id) e`.
  have hhm : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      wσ.haltMass ρ e
        = Scheduler.haltMass (Scheduler.lower pe') (pe'.initState.bind id) e := by
    intro e
    rw [hbindρ]
    rfl
  -- Facts about the witness.
  have hσhalts : (∑' E, σ.haltMass (PMF.pure ρ) E) = 1 := h.witness_halts
  have hσpush : ∀ σ' : PMF State, Ν σ'
      = ∑' E, σ.haltMass (PMF.pure ρ) E * (if E.1.endState E.2 = σ' then (1:ENNReal) else 0) :=
    h.witness_pushforward
  -- `σ.haltMass (PMF.pure ρ) E = Scheduler.haltMass pe'.scheduler pe'.initState E` (defeq).
  have hσhm : ∀ E : {E : AlterSeq (PMF State) Label // E.trans.Terminates},
      σ.haltMass (PMF.pure ρ) E = Scheduler.haltMass pe'.scheduler pe'.initState E := fun _ => rfl
  refine ⟨wσ, ?_, ?_⟩
  · -- a.s.-halting: the `g = 1` slice.
    have key := pe'.lower_haltMass_g_eq (fun _ => 1)
    simp only [mul_one] at key
    -- each `E.endState`'s `tsum_coe = 1`.
    rw [show (∑' E : {E : AlterSeq (PMF State) Label // E.trans.Terminates},
          Scheduler.haltMass pe'.scheduler pe'.initState E *
            (∑' s : State, (E.1.endState E.2) s))
        = ∑' E : {E : AlterSeq (PMF State) Label // E.trans.Terminates},
            Scheduler.haltMass pe'.scheduler pe'.initState E from
      tsum_congr (fun E => by rw [(E.1.endState E.2).tsum_coe, mul_one])] at key
    calc (∑' e, wσ.haltMass ρ e)
        = ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
            Scheduler.haltMass (Scheduler.lower pe') (pe'.initState.bind id) e :=
          tsum_congr (fun e => hhm e)
      _ = ∑' E : {E : AlterSeq (PMF State) Label // E.trans.Terminates},
            Scheduler.haltMass pe'.scheduler pe'.initState E := key
      _ = 1 := by simp only [← hσhm]; exact hσhalts
  · -- pushforward: the `g = [· = s]` slice.
    intro s
    have key := pe'.lower_haltMass_g_eq (fun s' => if s' = s then (1:ENNReal) else 0)
    -- RHS of `key`: `∑' E, haltMass pe' E * (endState E) s`.
    rw [show (∑' E : {E : AlterSeq (PMF State) Label // E.trans.Terminates},
          Scheduler.haltMass pe'.scheduler pe'.initState E *
            (∑' s' : State, (E.1.endState E.2) s' * (if s' = s then (1:ENNReal) else 0)))
        = ∑' E : {E : AlterSeq (PMF State) Label // E.trans.Terminates},
            Scheduler.haltMass pe'.scheduler pe'.initState E * (E.1.endState E.2) s from
      tsum_congr (fun E => by
        congr 1
        rw [tsum_eq_single s (fun s' hs' => by rw [if_neg hs', mul_zero]), if_pos rfl,
          mul_one])] at key
    -- LHS of the goal: `(Ν.bind id) s = ∑' σ', Ν σ' * σ' s`.
    rw [PMF.bind_apply]
    change (∑' σ', Ν σ' * id σ' s) = _
    simp only [id_eq]
    -- Substitute `witness_pushforward`, swap sums, match `key`.
    rw [show (∑' σ', Ν σ' * σ' s)
        = ∑' σ', (∑' E, σ.haltMass (PMF.pure ρ) E *
            (if E.1.endState E.2 = σ' then (1:ENNReal) else 0)) * σ' s from
      tsum_congr (fun σ' => by rw [hσpush σ'])]
    rw [show (∑' σ', (∑' E, σ.haltMass (PMF.pure ρ) E *
            (if E.1.endState E.2 = σ' then (1:ENNReal) else 0)) * σ' s)
        = ∑' σ', ∑' E, σ.haltMass (PMF.pure ρ) E *
            (if E.1.endState E.2 = σ' then (1:ENNReal) else 0) * σ' s from
      tsum_congr (fun σ' => by rw [ENNReal.tsum_mul_right])]
    rw [ENNReal.tsum_comm]
    rw [show (∑' E, ∑' σ', σ.haltMass (PMF.pure ρ) E *
            (if E.1.endState E.2 = σ' then (1:ENNReal) else 0) * σ' s)
        = ∑' E, σ.haltMass (PMF.pure ρ) E * (E.1.endState E.2) s from by
      refine tsum_congr (fun E => ?_)
      rw [tsum_congr (fun σ' => by ring :
          ∀ σ', σ.haltMass (PMF.pure ρ) E *
              (if E.1.endState E.2 = σ' then (1:ENNReal) else 0) * σ' s
            = σ.haltMass (PMF.pure ρ) E *
              ((if E.1.endState E.2 = σ' then (1:ENNReal) else 0) * σ' s)),
        ENNReal.tsum_mul_left]
      congr 1
      rw [tsum_eq_single (E.1.endState E.2)
          (fun σ' hσ' => by rw [if_neg (fun heq => hσ' heq.symm), zero_mul]),
        if_pos rfl, one_mul]]
    -- Now match `key`: LHS goal via `hσhm`, RHS goal via `hhm`, then `key`.
    rw [tsum_congr (fun E => by rw [hσhm E] :
        ∀ E, σ.haltMass (PMF.pure ρ) E * (E.1.endState E.2) s
          = Scheduler.haltMass pe'.scheduler pe'.initState E * (E.1.endState E.2) s)]
    rw [← key]
    exact tsum_congr (fun e => by rw [hhm e])

end PLTS
