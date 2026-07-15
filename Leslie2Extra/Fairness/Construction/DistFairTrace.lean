/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2Extra.Fairness.Construction.DistFair

/-!
# Trace-distribution correctness of the reconstructed scheduler

The reconstructed resolved scheduler `lowerSched F s` (`Construction/DistFair.lean`) realises the
same trace distribution as the abstract resolved-history scheduler `s` on `𝒟f(sys, F)`:

  `lowerSched_traceProbR` : for every trace `τ`,
    `(⟨δ_{sys.init}, lowerSched F s⟩).traceProbR τ = (⟨δ_{𝒟f.init}, s⟩).traceProbR τ`.

## Strategy

Both trace probabilities are expressed as *reach-masses of lowering-chain configurations*, then
equated using the fact that the chain keeps the two runs label-synchronised:

* `lowerReachProb_trace_eq` — **the invariant**: on every reachable config, `sys.trace e = 𝒟f.trace
  de` (both runs carry the same label at every step); likewise `reachProb_isTight_iff` for tightness
* `traceProbR_eq_reachDe` — the abstract probability `(⟨δ, s⟩).traceProbR tr` equals the reach-mass
  of configs whose `de`-run is tight with trace `tr`.
* `traceProbR_eq_reachE` — the concrete probability `(⟨δ, lowerSched F s⟩).traceProbR tr` equals the
  reach-mass of configs whose `e`-run is tight with trace `tr`.

Since the two config families coincide on reachable configs (invariant), the two reach-masses are
equal, hence the two trace probabilities are equal.
-/

open Stream'

namespace PLTS

variable {State Label : Type} [Silent Label]

/-! ### `trace`/`IsTight` depend only on the label sequence -/

/-- `trace` factors as "map to labels, then filter out `τ`" (local copy of the private
`System.trace_eq_filter_map`). -/
theorem trace_eq_filter_mapFst {S L : Type} [Silent L] (ls : System S L) (e : AlterSeq S L) :
    ls.trace e = (e.trans.map Prod.fst).filter (fun l => ¬ (l = Silent.τ)) := by
  unfold System.trace
  rw [Stream'.Seq.filter_map Prod.fst (fun l => ¬ (l = Silent.τ))]
  rfl

/-- The label sequence of `r.toExec` is the label sequence recorded by `r`. -/
theorem toExec_map_fst {S L : Type} (r : ResolvedExec S L) :
    (r.toExec).trans.map Prod.fst = r.trans.map (fun p => p.1.1) := by
  apply Stream'.Seq.ext; intro n
  simp only [ResolvedExec.toExec, Stream'.Seq.map_get?, Option.map_map]
  rfl

/-- `System.trace` depends only on the label sequence: equal label sequences (over possibly
different state types) give equal traces. -/
theorem trace_eq_of_map_fst {S S' L : Type} [Silent L] (ls : System S L) (ls' : System S' L)
    (e : AlterSeq S L) (e' : AlterSeq S' L) (h : e.trans.map Prod.fst = e'.trans.map Prod.fst) :
    ls.trace e = ls'.trace e' := by
  rw [trace_eq_filter_mapFst, trace_eq_filter_mapFst, h]

/-- `IsTight` depends only on the label sequence. -/
theorem isTight_iff_of_map_fst {S S' L : Type} [Silent L] (ls : System S L) (ls' : System S' L)
    (e : AlterSeq S L) (e' : AlterSeq S' L) (h : e.trans.map Prod.fst = e'.trans.map Prod.fst) :
    ls.IsTight e ↔ ls'.IsTight e' := by
  have hget : ∀ n, (e.trans.get? n).map Prod.fst = (e'.trans.get? n).map Prod.fst := by
    intro n; have hh := congrArg (fun s => s.get? n) h
    simpa only [Stream'.Seq.map_get?] using hh
  have hterm : ∀ n, e.trans.TerminatedAt n ↔ e'.trans.TerminatedAt n := by
    intro n
    have hn := hget n
    unfold Stream'.Seq.TerminatedAt
    constructor <;> intro ht
    · have : (e'.trans.get? n).map Prod.fst = none := by rw [← hn, ht]; rfl
      exact Option.map_eq_none_iff.mp this
    · have : (e.trans.get? n).map Prod.fst = none := by rw [hn, ht]; rfl
      exact Option.map_eq_none_iff.mp this
  unfold System.IsTight
  rw [hterm 0]
  apply or_congr_right
  constructor
  · rintro ⟨n, l, s, hs, ht1, hl⟩
    have hml : (e'.trans.get? n).map Prod.fst = some l := by rw [← hget n, hs]; rfl
    obtain ⟨p, hp, hpl⟩ := Option.map_eq_some_iff.mp hml
    exact ⟨n, l, p.2, by rw [hp]; exact congrArg some (Prod.ext hpl rfl),
      (hterm (n + 1)).mp ht1, hl⟩
  · rintro ⟨n, l, s', hs', ht1, hl⟩
    have hml : (e.trans.get? n).map Prod.fst = some l := by rw [hget n, hs']; rfl
    obtain ⟨p, hp, hpl⟩ := Option.map_eq_some_iff.mp hml
    exact ⟨n, l, p.2, by rw [hp]; exact congrArg some (Prod.ext hpl rfl),
      (hterm (n + 1)).mpr ht1, hl⟩

/-! ### The trace-sync invariant of the lowering chain -/

variable {sys : System State Label}

/-- **Label-sync invariant.** On every reachable config the concrete and abstract runs carry the
same recorded labels. Proved by induction on the instruction count: each `LowerStep` appends the
*same* label `l` to both `e` and `de`. -/
theorem reachAfter_labels_eq (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (n : ℕ) (c : LowerConfig sys) (hne : LowerReachAfter F s n c ≠ 0) :
    c.e.trans.map (fun p => p.1.1) = c.de.trans.map (fun p => p.1.1) := by
  classical
  induction n generalizing c with
  | zero =>
    rw [LowerReachAfter_zero] at hne
    by_cases hc : c.de = ⟨PMF.pure sys.init, Seq.nil⟩ ∧ c.e = ⟨sys.init, Seq.nil⟩
    · rw [hc.1, hc.2]; simp only [Stream'.Seq.map_nil]
    · rw [if_neg hc] at hne; exact absurd rfl hne
  | succ k ih =>
    rw [LowerReachAfter_succ] at hne
    obtain ⟨c₀, hc₀⟩ := tsum_ne_zero_exists hne
    have hreach₀ : LowerReachAfter F s k c₀ ≠ 0 := fun h => hc₀ (by rw [h, zero_mul])
    have hstep : LowerStep F s c₀ c ≠ 0 := fun h => hc₀ (by rw [h, mul_zero])
    have hlab₀ : c₀.e.trans.map (fun p => p.1.1) = c₀.de.trans.map (fun p => p.1.1) := ih c₀ hreach₀
    revert hstep
    unfold LowerStep
    cases hh : c₀.h with
    | none => intro hstep; exact absurd rfl hstep
    | some lω =>
      obtain ⟨l₀, ω₀⟩ := lω
      simp only
      set μ' : PMF State := lastMuOf c.e with hμ'
      by_cases hif : c.de.init = c₀.de.init ∧ c.e.init = c₀.e.init ∧
          c.de.trans = c₀.de.trans.append (Seq.cons ((l₀, ω₀), lastStateOf c.de) Seq.nil) ∧
          c.e.trans = c₀.e.trans.append (Seq.cons ((l₀, μ'), lastStateOf c.e) Seq.nil)
      · rw [if_pos hif]
        intro _
        obtain ⟨_, _, hde_trans, he_trans⟩ := hif
        rw [he_trans, hde_trans]
        simp only [Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil, hlab₀]
      · rw [if_neg hif]; intro hstep; exact absurd rfl hstep

/-- Label-sync at the reach-*probability* level: any config with nonzero reach-probability is
label-synced. -/
theorem reachProb_labels_eq (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (c : LowerConfig sys) (hne : LowerReachProb F s c ≠ 0) :
    c.e.trans.map (fun p => p.1.1) = c.de.trans.map (fun p => p.1.1) := by
  obtain ⟨n, hn⟩ := tsum_ne_zero_exists hne
  exact reachAfter_labels_eq F s n c hn

/-- **The invariant.** On every reachable config, the concrete `sys`-trace of `e` equals the
abstract `𝒟f`-trace of `de`. -/
theorem lowerReachProb_trace_eq (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (c : LowerConfig sys) (hne : LowerReachProb F s c ≠ 0) :
    sys.trace c.e.toExec = (sys.distF F).trace c.de.toExec := by
  refine trace_eq_of_map_fst sys (sys.distF F) c.e.toExec c.de.toExec ?_
  rw [toExec_map_fst, toExec_map_fst]
  exact reachProb_labels_eq F s c hne

/-- Tightness-sync: on every reachable config, `e` is tight iff `de` is. -/
theorem reachProb_isTight_iff (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (c : LowerConfig sys) (hne : LowerReachProb F s c ≠ 0) :
    sys.IsTight c.e.toExec ↔ (sys.distF F).IsTight c.de.toExec := by
  refine isTight_iff_of_map_fst sys (sys.distF F) c.e.toExec c.de.toExec ?_
  rw [toExec_map_fst, toExec_map_fst]
  exact reachProb_labels_eq F s c hne

/-! ### Flow-conservation of the lowering chain

The concrete probability `(⟨δ, lowerSched F s⟩).traceProbR tr` is computed by relating the resolved
path-measure `probOfR` to the chain's arrival-mass `lowerMe F s r` at a concrete history `r`
(`∑' de h, LowerReachProb ⟨de, r, h⟩`). The key facts are flow-conservation identities:

* `lowerStep_tsum_eq_one` — one instruction out of a *reachable* pending config conserves mass
  exactly (it is a genuine probability kernel there);
* `lowerMe_eq_lowerDenom` — arrival mass = the scheduler denominator (pending mass telescopes into
  departures via step-conservation);
* `lowerMe_append` — arrival mass at a one-step extension of `r` is `μ q · lowerArrStep …`;
* `probOfR_eq_lowerMe` — the resolved path-measure equals the arrival mass (cons-end induction). -/

/-- Any outcome `x` of a **sampled** concrete transition `μ' ∈ (tKernel F β l ω qₚ).support` lies in
the support of the flattened belief-successor `ω.bind id`. Both branches of `tKernel` pick `μ'`
from a `hyperStep`-kernel `p qₚ` with `ω.bind id = β.bind (fun s => (p s).bind id)`, and
`qₚ ∈ β.support`, so any `x ∈ μ'.support` reaches `ω.bind id`. -/
theorem tKernel_mem_bind (F : Fairness sys) (β : PMF State) (l : Label) (ω : PMF (PMF State))
    (qₚ : State) (hq : qₚ ∈ β.support) (hstep : (sys.distF F).step β l ω)
    (μ' : PMF State) (hμ' : μ' ∈ (tKernel F β l ω qₚ).support)
    (x : State) (hx : x ∈ μ'.support) :
    x ∈ (ω.bind id).support := by
  classical
  unfold tKernel at hμ'
  by_cases hf : F.dist.fair β l ω
  · rw [dif_pos hf] at hμ'
    set p := hf.2.choose with hp
    have hbind : ω.bind id = β.bind (fun s => (p s).bind id) := hf.2.choose_spec.2
    rw [hbind, PMF.mem_support_bind_iff]
    exact ⟨qₚ, hq, by rw [PMF.mem_support_bind_iff]; exact ⟨μ', hμ', hx⟩⟩
  · rw [dif_neg hf, dif_pos hstep] at hμ'
    set p := hstep.1.choose with hp
    have hbind : ω.bind id = β.bind (fun s => (p s).bind id) := hstep.1.choose_spec.2
    rw [hbind, PMF.mem_support_bind_iff]
    exact ⟨qₚ, hq, by rw [PMF.mem_support_bind_iff]; exact ⟨μ', hμ', hx⟩⟩

/-- **Step-conservation.** Out of a reachable pending config `c₀` (`Coupled`, with a valid emission
`(l, ω)`) the lowering chain conserves mass *exactly*: `∑' c', LowerStep … c₀ c' = 1`. This sharpens
`lowerStep_tsum_le_one`: the only inequality there was `(ω.bind id) q / (ω.bind id) q ≤ 1`, which is
an *equality* for `q ∈ μ'.support` because `μ'.support ⊆ (ω.bind id).support` (`tOutcome_mem_bind`)
forces `(ω.bind id) q ≠ 0`. -/
theorem lowerStep_tsum_eq_one (F : Fairness sys) (sch : ResolvedScheduler (sys.distF F))
    (c₀ : LowerConfig sys) (hcoup : Coupled c₀)
    (l : Label) (ω : PMF (PMF State)) (hh : c₀.h = some (l, ω))
    (hstep : (sys.distF F).step (lastStateOf c₀.de) l ω) :
    ∑' c', LowerStep F sch c₀ c' = 1 := by
  classical
  set β := lastStateOf c₀.de with hβ
  set qₚ := lastStateOf c₀.e with hqₚ
  set De : PMF State → ResolvedExec (PMF State) Label :=
    fun dq => ⟨c₀.de.init, c₀.de.trans.append (Seq.cons ((l, ω), dq) Seq.nil)⟩ with hDe
  set Ec : PMF State → State → ResolvedExec State Label :=
    fun μ q => ⟨c₀.e.init, c₀.e.trans.append (Seq.cons ((l, μ), q) Seq.nil)⟩ with hEc
  set φ : PMF State × PMF State × State × Option (Label × PMF (PMF State)) → LowerConfig sys :=
    fun p => ⟨De p.2.1, Ec p.1 p.2.2.1, p.2.2.2⟩ with hφ
  have hde : c₀.de.trans.Terminates := hcoup.1
  have he : c₀.e.trans.Terminates := hcoup.2.1
  have hDelast : ∀ dq, lastStateOf (De dq) = dq := fun dq =>
    lastStateOf_append_singleton ⟨c₀.de.init, c₀.de.trans⟩ hde (l, ω) dq
  have hEclast : ∀ μ q, lastStateOf (Ec μ q) = q := fun μ q =>
    lastStateOf_append_singleton ⟨c₀.e.init, c₀.e.trans⟩ he (l, μ) q
  have hEcmu : ∀ μ q, lastMuOf (Ec μ q) = μ := fun μ q =>
    lastMuOf_append_singleton ⟨c₀.e.init, c₀.e.trans⟩ he l μ q
  have hφinj : Function.Injective φ := by
    rintro ⟨μ₁, dq₁, q₁, h₁⟩ ⟨μ₂, dq₂, q₂, h₂⟩ heq
    have hdq' := congrArg (fun c => lastStateOf c.de) heq
    have hq' := congrArg (fun c => lastStateOf c.e) heq
    have hmu' := congrArg (fun c => lastMuOf c.e) heq
    have hhh := congrArg LowerConfig.h heq
    simp only [hφ, hDelast, hEclast, hEcmu] at hdq' hq' hmu' hhh
    subst hdq'; subst hq'; subst hmu'; subst hhh; rfl
  have hval : ∀ p : PMF State × PMF State × State × Option (Label × PMF (PMF State)),
      LowerStep F sch c₀ (φ p)
        = (tKernel F β l ω qₚ) p.1 * p.1 p.2.2.1 * ω p.2.1
            * (p.2.1 p.2.2.1 / (ω.bind id) p.2.2.1) * sch.next (De p.2.1) p.2.2.2 := by
    rintro ⟨μ, dq, q, h'⟩
    change LowerStep F sch c₀ ⟨De dq, Ec μ q, h'⟩ = _
    unfold LowerStep
    rw [hh]
    simp only [hDelast, hEclast, hEcmu]
    rw [if_pos ⟨rfl, rfl, rfl, rfl⟩]
  set g : PMF State × PMF State × State × Option (Label × PMF (PMF State)) → ENNReal :=
    fun p => (tKernel F β l ω qₚ) p.1 * p.1 p.2.2.1 * ω p.2.1
      * (p.2.1 p.2.2.1 / (ω.bind id) p.2.2.1) * sch.next (De p.2.1) p.2.2.2 with hg
  have hreindex : ∑' c', LowerStep F sch c₀ c' = ∑' p, g p := by
    refine tsum_eq_tsum_of_ne_zero_bij (i := fun p : Function.support g => φ p.1)
      ?inj ?supp ?val
    · rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hab
      exact Subtype.ext (hφinj hab)
    · intro c' hc'
      have hne : LowerStep F sch c₀ c' ≠ 0 := hc'
      have hshape : c' = φ (lastMuOf c'.e, lastStateOf c'.de, lastStateOf c'.e, c'.h) := by
        revert hne
        unfold LowerStep
        rw [hh]
        simp only
        by_cases hif : c'.de.init = c₀.de.init ∧ c'.e.init = c₀.e.init ∧
            c'.de.trans = c₀.de.trans.append (Seq.cons ((l, ω), lastStateOf c'.de) Seq.nil) ∧
            c'.e.trans =
              c₀.e.trans.append (Seq.cons ((l, lastMuOf c'.e), lastStateOf c'.e) Seq.nil)
        · intro _
          obtain ⟨hdinit, heinit, hdt, het⟩ := hif
          have hde_eq : c'.de = De (lastStateOf c'.de) := by
            rw [hDe]; exact alterSeq_ext hdinit hdt
          have he_eq : c'.e = Ec (lastMuOf c'.e) (lastStateOf c'.e) := by
            rw [hEc]; exact alterSeq_ext heinit het
          change c' = ⟨De (lastStateOf c'.de), Ec (lastMuOf c'.e) (lastStateOf c'.e), c'.h⟩
          rw [← hde_eq, ← he_eq]
        · rw [if_neg hif]; intro h0; exact absurd rfl h0
      refine ⟨⟨(lastMuOf c'.e, lastStateOf c'.de, lastStateOf c'.e, c'.h), ?_⟩, hshape.symm⟩
      rw [Function.mem_support]
      have heq : g (lastMuOf c'.e, lastStateOf c'.de, lastStateOf c'.e, c'.h)
          = LowerStep F sch c₀ c' := by
        rw [show g (lastMuOf c'.e, lastStateOf c'.de, lastStateOf c'.e, c'.h)
          = LowerStep F sch c₀ (φ (lastMuOf c'.e, lastStateOf c'.de, lastStateOf c'.e, c'.h)) from
          (hval _).symm, ← hshape]
      rw [heq]; exact hne
    · rintro ⟨p, hp⟩; exact hval p
  rw [hreindex, hg]
  simp only []
  have hbind : ∀ q : State, ∑' dq : PMF State, ω dq * dq q = (ω.bind id) q := fun q => by
    simp only [PMF.bind_apply, id_eq]
  -- The belief fibre is exactly `1` for outcomes `q` a sampled `μ` can reach (`tKernel_mem_bind`).
  have hfibre : ∀ (μ : PMF State), μ ∈ (tKernel F β l ω qₚ).support → ∀ q ∈ μ.support,
      ∑' dq : PMF State, ω dq * (dq q / (ω.bind id) q) = 1 := by
    intro μ hμ q hq
    have h2 : ∑' dq : PMF State, ω dq * (dq q / (ω.bind id) q)
        = (ω.bind id) q * ((ω.bind id) q)⁻¹ := by
      calc ∑' dq : PMF State, ω dq * (dq q / (ω.bind id) q)
          = ∑' dq : PMF State, (ω dq * dq q) * ((ω.bind id) q)⁻¹ := by
            refine tsum_congr fun dq => ?_; rw [div_eq_mul_inv]; ring
        _ = (∑' dq : PMF State, ω dq * dq q) * ((ω.bind id) q)⁻¹ := ENNReal.tsum_mul_right
        _ = (ω.bind id) q * ((ω.bind id) q)⁻¹ := by rw [hbind]
    rw [h2]
    have hne0 : (ω.bind id) q ≠ 0 := by
      have := tKernel_mem_bind F β l ω qₚ hcoup.2.2 hstep μ hμ q hq
      rwa [PMF.mem_support_iff] at this
    exact ENNReal.mul_inv_cancel hne0 (PMF.apply_ne_top (ω.bind id) q)
  calc ∑' p : PMF State × PMF State × State × Option (Label × PMF (PMF State)),
          (tKernel F β l ω qₚ) p.1 * p.1 p.2.2.1 * ω p.2.1
            * (p.2.1 p.2.2.1 / (ω.bind id) p.2.2.1) * sch.next (De p.2.1) p.2.2.2
      = ∑' (μ : PMF State) (dq : PMF State) (q : State),
          (tKernel F β l ω qₚ) μ * μ q * ω dq * (dq q / (ω.bind id) q) := by
        rw [ENNReal.tsum_prod']
        refine tsum_congr fun μ => ?_
        rw [ENNReal.tsum_prod']
        refine tsum_congr fun dq => ?_
        rw [ENNReal.tsum_prod']
        refine tsum_congr fun q => ?_
        simp only [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
    _ = ∑' (μ : PMF State) (q : State) (dq : PMF State),
          (tKernel F β l ω qₚ) μ * μ q * ω dq * (dq q / (ω.bind id) q) := by
        refine tsum_congr fun μ => ?_; exact ENNReal.tsum_comm
    _ = ∑' (μ : PMF State) (q : State), (tKernel F β l ω qₚ) μ * μ q := by
        refine tsum_congr fun μ => tsum_congr fun q => ?_
        rcases eq_or_ne ((tKernel F β l ω qₚ) μ * μ q) 0 with h0 | h0
        · rcases mul_eq_zero.mp h0 with h1 | h1
          · simp only [h1, zero_mul, tsum_zero]
          · simp only [h1, mul_zero, zero_mul, tsum_zero]
        · rw [mul_ne_zero_iff] at h0
          have hμ : μ ∈ (tKernel F β l ω qₚ).support := (PMF.mem_support_iff _ _).mpr h0.1
          have hq : q ∈ μ.support := (PMF.mem_support_iff _ _).mpr h0.2
          calc ∑' dq : PMF State, (tKernel F β l ω qₚ) μ * μ q * ω dq * (dq q / (ω.bind id) q)
              = (tKernel F β l ω qₚ) μ * μ q * ∑' dq : PMF State,
                  ω dq * (dq q / (ω.bind id) q) := by
                rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun dq => by ring
            _ = (tKernel F β l ω qₚ) μ * μ q * 1 := by rw [hfibre μ hμ q hq]
            _ = (tKernel F β l ω qₚ) μ * μ q := mul_one _
    _ = ∑' μ : PMF State, (tKernel F β l ω qₚ) μ := by
        refine tsum_congr fun μ => ?_
        rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
    _ = 1 := PMF.tsum_coe _

/-- The chain's **arrival-mass** at a concrete history `r`: the reach-mass, marginalised over the
abstract run `de` and the pending emission `h`, of all configs whose concrete run is `r`. -/
noncomputable def lowerMe (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (r : ResolvedExec State Label) : ENNReal :=
  ∑' (de : ResolvedExec (PMF State) Label) (h : Option (Label × PMF (PMF State))),
    LowerReachProb F s ⟨de, r, h⟩

/-- **Level-peel.** For a config whose level-`0` mass vanishes (in particular any config whose
concrete run is a nonempty append), the reach-prob is the one-instruction convolution of the
predecessor reach-probs with `LowerStep`. Shifting `∑' n` by one (level `0` drops out). -/
theorem LowerReachProb_peel (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (c : LowerConfig sys) (h0 : LowerReachAfter F s 0 c = 0) :
    LowerReachProb F s c = ∑' c₀, LowerReachProb F s c₀ * LowerStep F s c₀ c := by
  classical
  unfold LowerReachProb
  have hshift : ∑' n, LowerReachAfter F s n c = ∑' n, LowerReachAfter F s (n + 1) c := by
    rw [tsum_eq_zero_add' ENNReal.summable, h0, zero_add]
  rw [hshift]
  simp_rw [LowerReachAfter_succ]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun c₀ => ENNReal.tsum_mul_right

/-- Appending one transition to `t` never yields a sequence that terminates at `0` (the appended
head is present at some early position). -/
theorem append_singleton_not_terminatedAt_zero {S L : Type} (t : Seq (L × S)) (x : L × S) :
    ¬ (t.append (Seq.cons x Seq.nil)).TerminatedAt 0 := by
  classical
  rw [Stream'.Seq.TerminatedAt]
  by_cases hr : t = Seq.nil
  · rw [hr, Stream'.Seq.nil_append, Stream'.Seq.get?_cons_zero]; simp
  · obtain ⟨y, hy⟩ : ∃ y, t.get? 0 = some y := by
      rcases hg : t.get? 0 with _ | y
      · exact absurd (Stream'.Seq.ext (fun n => by
          rw [Stream'.Seq.get?_nil]
          exact Stream'.Seq.terminated_stable t (Nat.zero_le n) hg)) hr
      · exact ⟨y, rfl⟩
    rw [Stream'.Seq.get?_append_before_length (k := 0)
      (by rw [Stream'.Seq.TerminatedAt, hy]; simp), hy]
    simp

/-- The level-`0` mass of any config whose concrete run is a nonempty append is `0` (its concrete
run does not terminate at `0`, so `L2` rules the level out). -/
theorem reachAfter_zero_of_append (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (de : ResolvedExec (PMF State) Label) (r : ResolvedExec State Label)
    (x : (Label × PMF State) × State) (h : Option (Label × PMF (PMF State))) :
    LowerReachAfter F s 0 ⟨de, ⟨r.init, r.trans.append (Seq.cons x Seq.nil)⟩, h⟩ = 0 := by
  classical
  by_contra hne
  have := (reachAfter_length F s 0
    ⟨de, ⟨r.init, r.trans.append (Seq.cons x Seq.nil)⟩, h⟩ hne).1
  exact append_singleton_not_terminatedAt_zero r.trans x this

/-- A sequence whose one-transition extension terminates itself terminates. -/
theorem terminates_of_append_singleton {S L : Type} (t : Seq (L × S)) (x : L × S)
    (h : (t.append (Seq.cons x Seq.nil)).Terminates) : t.Terminates := by
  classical
  by_contra hns
  have heq : t.append (Seq.cons x Seq.nil) = t := by
    apply Stream'.Seq.ext; intro m
    rw [Stream'.Seq.get?_append_before_length]; intro ht; exact hns ⟨m, ht⟩
  rw [heq] at h; exact hns h

/-- **Departure reindexing.** Out of `c₀` (`Coupled`), the flat sum of `LowerStep` over the
successors parameterised by `(x, de', q', h')` — the departures whose concrete run extends `c₀.e` —
is the total `LowerStep`-sum. The last transition `(x, q')` is recovered from the extended run, so
the parameterisation is an injective bijection onto the nonzero successors. -/
theorem lowerStep_flat_eq (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (c₀ : LowerConfig sys) (hcoup : Coupled c₀) :
    (∑' (p : (Label × PMF State) × ResolvedExec (PMF State) Label × State ×
          Option (Label × PMF (PMF State))),
        LowerStep F s c₀
          ⟨p.2.1, ⟨c₀.e.init, c₀.e.trans.append (Seq.cons (p.1, p.2.2.1) Seq.nil)⟩, p.2.2.2⟩)
      = ∑' c', LowerStep F s c₀ c' := by
  classical
  cases hh : c₀.h with
  | none =>
    have hz : ∀ c', LowerStep F s c₀ c' = 0 := by intro c'; unfold LowerStep; rw [hh]
    simp only [hz, tsum_zero]
  | some lω =>
    obtain ⟨l, ω⟩ := lω
    have he : c₀.e.trans.Terminates := hcoup.2.1
    set φ : (Label × PMF State) × ResolvedExec (PMF State) Label × State ×
          Option (Label × PMF (PMF State)) → LowerConfig sys :=
      fun p => ⟨p.2.1, ⟨c₀.e.init, c₀.e.trans.append (Seq.cons (p.1, p.2.2.1) Seq.nil)⟩, p.2.2.2⟩
      with hφ
    symm
    refine tsum_eq_tsum_of_ne_zero_bij
      (i := fun p : Function.support (fun p => LowerStep F s c₀ (φ p)) => φ p.1) ?inj ?supp ?val
    · rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hab
      refine Subtype.ext ?_
      obtain ⟨x₁, de₁, q₁, h₁⟩ := p₁
      obtain ⟨x₂, de₂, q₂, h₂⟩ := p₂
      simp only [hφ] at hab
      have hde := congrArg LowerConfig.de hab
      have he' := congrArg (fun c => c.e.trans) hab
      have hhh := congrArg LowerConfig.h hab
      simp only at hde he' hhh
      have hxq : (x₁, q₁) = (x₂, q₂) :=
        Stream'.Seq.append_singleton_inj_right c₀.e.trans c₀.e.trans he he _ _ he'
      have hx : x₁ = x₂ := congrArg Prod.fst hxq
      have hq : q₁ = q₂ := congrArg Prod.snd hxq
      subst hde; subst hhh; subst hx; subst hq; rfl
    · intro c' hc'
      have hne : LowerStep F s c₀ c' ≠ 0 := hc'
      have hshape : c' = φ ((l, lastMuOf c'.e), c'.de, lastStateOf c'.e, c'.h) := by
        revert hne
        unfold LowerStep
        rw [hh]
        simp only
        by_cases hif : c'.de.init = c₀.de.init ∧ c'.e.init = c₀.e.init ∧
            c'.de.trans = c₀.de.trans.append (Seq.cons ((l, ω), lastStateOf c'.de) Seq.nil) ∧
            c'.e.trans =
              c₀.e.trans.append (Seq.cons ((l, lastMuOf c'.e), lastStateOf c'.e) Seq.nil)
        · intro _
          obtain ⟨_, heinit, _, het⟩ := hif
          have hee : c'.e =
              ⟨c₀.e.init,
                c₀.e.trans.append (Seq.cons ((l, lastMuOf c'.e), lastStateOf c'.e) Seq.nil)⟩ :=
            alterSeq_ext heinit het
          change c' = ⟨c'.de, ⟨c₀.e.init,
            c₀.e.trans.append (Seq.cons ((l, lastMuOf c'.e), lastStateOf c'.e) Seq.nil)⟩, c'.h⟩
          rw [← hee]
        · rw [if_neg hif]; intro h0; exact absurd rfl h0
      refine ⟨⟨((l, lastMuOf c'.e), c'.de, lastStateOf c'.e, c'.h), ?_⟩, hshape.symm⟩
      rw [Function.mem_support]
      change LowerStep F s c₀ (φ ((l, lastMuOf c'.e), c'.de, lastStateOf c'.e, c'.h)) ≠ 0
      rw [← hshape]; exact hne
    · rintro ⟨p, hp⟩; rfl

/-- A reachable pending config is `Coupled` and its recorded emission `(l, ω)` is a valid
`𝒟f`-step out of `lastStateOf de` (scheduler validity at the belief run's end). -/
theorem reachProb_pending_step (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (c₀ : LowerConfig sys) (hne : LowerReachProb F s c₀ ≠ 0)
    (l : Label) (ω : PMF (PMF State)) (hh : c₀.h = some (l, ω)) :
    Coupled c₀ ∧ (sys.distF F).step (lastStateOf c₀.de) l ω := by
  classical
  unfold LowerReachProb at hne
  obtain ⟨N, hN⟩ := tsum_ne_zero_exists hne
  have hcoup : Coupled c₀ := reachAfter_coupled F s N c₀ hN
  refine ⟨hcoup, ?_⟩
  have hnext : s.next c₀.de c₀.h ≠ 0 := reachAfter_next_ne_zero F s N c₀ hN
  rw [hh] at hnext
  have hmem : some (l, ω) ∈ (s.next c₀.de).support := (PMF.mem_support_iff _ _).mpr hnext
  have hde_term : c₀.de.trans.Terminates := hcoup.1
  have hde_state : c₀.de.stateAt (Nat.find hde_term) = some (lastStateOf c₀.de) := by
    have := AlterSeq.stateAt_find_eq_endState c₀.de hde_term
    rw [this]; congr 1; unfold lastStateOf; rw [dif_pos hde_term]
  exact s.valid c₀.de (Nat.find hde_term) (lastStateOf c₀.de) (Nat.find_spec hde_term)
    hde_state l ω hmem

/-- **Pending = departures.** The pending reach-mass at `r` (configs `⟨de, r, some lω⟩`, still to
emit) equals the total step-departure mass at `r`. Each departure config's reach-prob is peeled into
its predecessors, the sum is swapped to run over predecessors first, and step-conservation
(`lowerStep_tsum_eq_one`) collapses the inner departure-sum to `1` exactly on the reachable pending
predecessors `⟨de, r, some lω⟩` (nonzero only there). -/
theorem lowerMe_pending_eq_dep (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (r : ResolvedExec State Label) :
    (∑' (de : ResolvedExec (PMF State) Label) (lω : Label × PMF (PMF State)),
        LowerReachProb F s ⟨de, r, some lω⟩)
      = ∑' x, lowerArrStep F s r x := by
  classical
  -- departures: flatten, peel, swap.
  have hdep : (∑' x, lowerArrStep F s r x)
      = ∑' c₀, LowerReachProb F s c₀ *
          (∑' (p : (Label × PMF State) × ResolvedExec (PMF State) Label × State ×
                Option (Label × PMF (PMF State))),
              LowerStep F s c₀
                ⟨p.2.1, ⟨r.init, r.trans.append (Seq.cons (p.1, p.2.2.1) Seq.nil)⟩, p.2.2.2⟩) := by
    have hflat : (∑' x, lowerArrStep F s r x)
        = ∑' (p : (Label × PMF State) × ResolvedExec (PMF State) Label × State ×
              Option (Label × PMF (PMF State))),
            LowerReachProb F s
              ⟨p.2.1, ⟨r.init, r.trans.append (Seq.cons (p.1, p.2.2.1) Seq.nil)⟩, p.2.2.2⟩ := by
      unfold lowerArrStep
      rw [ENNReal.tsum_prod' (f := fun p : (Label × PMF State) × ResolvedExec (PMF State) Label ×
            State × Option (Label × PMF (PMF State)) =>
          LowerReachProb F s
            ⟨p.2.1, ⟨r.init, r.trans.append (Seq.cons (p.1, p.2.2.1) Seq.nil)⟩, p.2.2.2⟩)]
      refine tsum_congr fun x => ?_
      rw [ENNReal.tsum_prod']
      refine tsum_congr fun de => ?_
      rw [ENNReal.tsum_prod']
    rw [hflat]
    have hpeel : ∀ p : (Label × PMF State) × ResolvedExec (PMF State) Label × State ×
          Option (Label × PMF (PMF State)),
        LowerReachProb F s
            ⟨p.2.1, ⟨r.init, r.trans.append (Seq.cons (p.1, p.2.2.1) Seq.nil)⟩, p.2.2.2⟩
          = ∑' c₀, LowerReachProb F s c₀ * LowerStep F s c₀
              ⟨p.2.1, ⟨r.init, r.trans.append (Seq.cons (p.1, p.2.2.1) Seq.nil)⟩, p.2.2.2⟩ :=
      fun p => LowerReachProb_peel F s _
        (reachAfter_zero_of_append F s p.2.1 r (p.1, p.2.2.1) p.2.2.2)
    simp_rw [hpeel]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun c₀ => by rw [← ENNReal.tsum_mul_left]
  rw [hdep]
  -- reindex the predecessor sum onto the pending configs.
  rw [← ENNReal.tsum_prod'
    (f := fun p : ResolvedExec (PMF State) Label × (Label × PMF (PMF State)) =>
      LowerReachProb F s ⟨p.1, r, some p.2⟩)]
  symm
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun p : Function.support (fun p : ResolvedExec (PMF State) Label ×
        (Label × PMF (PMF State)) => LowerReachProb F s ⟨p.1, r, some p.2⟩) =>
      (⟨p.1.1, r, some p.1.2⟩ : LowerConfig sys)) ?inj ?supp ?val
  · rintro ⟨⟨de₁, lω₁⟩, h₁⟩ ⟨⟨de₂, lω₂⟩, h₂⟩ hab
    simp only [LowerConfig.mk.injEq] at hab
    obtain ⟨hde, -, hlω⟩ := hab
    exact Subtype.ext (Prod.ext hde (Option.some.inj hlω))
  · intro c₀ hc₀
    rw [Function.mem_support] at hc₀
    have hrp : LowerReachProb F s c₀ ≠ 0 := fun h => hc₀ (by rw [h, zero_mul])
    have hJ : (∑' p : (Label × PMF State) × ResolvedExec (PMF State) Label × State ×
          Option (Label × PMF (PMF State)), LowerStep F s c₀
        ⟨p.2.1, ⟨r.init, r.trans.append (Seq.cons (p.1, p.2.2.1) Seq.nil)⟩, p.2.2.2⟩) ≠ 0 :=
      fun h => hc₀ (by rw [h, mul_zero])
    obtain ⟨p, hp⟩ := tsum_ne_zero_exists hJ
    obtain ⟨l, ω, hh⟩ : ∃ l ω, c₀.h = some (l, ω) := by
      rcases hhc : c₀.h with _ | ⟨l, ω⟩
      · exfalso; revert hp; unfold LowerStep; rw [hhc]; intro hp; exact hp rfl
      · exact ⟨l, ω, rfl⟩
    have hcoup : Coupled c₀ := (reachProb_pending_step F s c₀ hrp l ω hh).1
    have her : c₀.e = r := by
      revert hp
      unfold LowerStep
      rw [hh]
      simp only
      set μ' : PMF State := lastMuOf (⟨r.init, r.trans.append (Seq.cons (p.1, p.2.2.1) Seq.nil)⟩ :
        ResolvedExec State Label) with hμ'
      by_cases hif : p.2.1.init = c₀.de.init ∧ r.init = c₀.e.init ∧
          p.2.1.trans = c₀.de.trans.append (Seq.cons ((l, ω), lastStateOf p.2.1) Seq.nil) ∧
          r.trans.append (Seq.cons (p.1, p.2.2.1) Seq.nil) =
            c₀.e.trans.append (Seq.cons ((l, μ'),
              lastStateOf (⟨r.init, r.trans.append (Seq.cons (p.1, p.2.2.1) Seq.nil)⟩ :
                ResolvedExec State Label)) Seq.nil)
      · intro _
        obtain ⟨_, heinit, _, het⟩ := hif
        have hrterm : r.trans.Terminates :=
          terminates_of_append_singleton r.trans (p.1, p.2.2.1) (het ▸
            (⟨Nat.find hcoup.2.1 + 1, Stream'.Seq.terminatedAt_append_find hcoup.2.1
              (show (Seq.cons ((l, μ'), _) Seq.nil).TerminatedAt 1 from rfl)⟩))
        have htr : c₀.e.trans = r.trans :=
          (Stream'.Seq.append_singleton_inj_left r.trans c₀.e.trans hrterm hcoup.2.1 _ _ het).symm
        exact alterSeq_ext heinit.symm htr
      · rw [if_neg hif]; intro h0; exact absurd rfl h0
    refine ⟨⟨(c₀.de, (l, ω)), ?_⟩, ?_⟩
    · rw [Function.mem_support]
      change LowerReachProb F s ⟨c₀.de, r, some (l, ω)⟩ ≠ 0
      rw [← her, ← hh]; exact hrp
    · change (⟨c₀.de, r, some (l, ω)⟩ : LowerConfig sys) = c₀
      rw [← her, ← hh]
  · rintro ⟨⟨de, l, ω⟩, hne⟩
    rw [Function.mem_support] at hne
    have hrp : LowerReachProb F s ⟨de, r, some (l, ω)⟩ ≠ 0 := hne
    obtain ⟨hcoup, hstep⟩ := reachProb_pending_step F s ⟨de, r, some (l, ω)⟩ hrp l ω rfl
    have hJeq : (∑' p : (Label × PMF State) × ResolvedExec (PMF State) Label × State ×
          Option (Label × PMF (PMF State)), LowerStep F s ⟨de, r, some (l, ω)⟩
          ⟨p.2.1, ⟨r.init, r.trans.append (Seq.cons (p.1, p.2.2.1) Seq.nil)⟩, p.2.2.2⟩)
        = ∑' c', LowerStep F s ⟨de, r, some (l, ω)⟩ c' :=
      lowerStep_flat_eq F s ⟨de, r, some (l, ω)⟩ hcoup
    dsimp only
    rw [hJeq, lowerStep_tsum_eq_one F s ⟨de, r, some (l, ω)⟩ hcoup l ω rfl hstep, mul_one]

/-- **Flow (A): arrival = denominator.** The chain's total arrival-mass at `r` equals the
scheduler denominator `lowerDenom` at `r`. Splitting both by the halt/step dichotomy, the halt parts
agree and the pending-vs-departure parts agree by `lowerMe_pending_eq_dep`. -/
theorem lowerMe_eq_lowerDenom (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (r : ResolvedExec State Label) : lowerMe F s r = lowerDenom F s r := by
  classical
  have hMe : lowerMe F s r = lowerArrHalt F s r
      + ∑' (de : ResolvedExec (PMF State) Label) (lω : Label × PMF (PMF State)),
          LowerReachProb F s ⟨de, r, some lω⟩ := by
    unfold lowerMe lowerArrHalt
    have hinner : ∀ de, (∑' h, LowerReachProb F s ⟨de, r, h⟩)
        = LowerReachProb F s ⟨de, r, none⟩
          + ∑' lω, LowerReachProb F s ⟨de, r, some lω⟩ := fun de =>
      lower_tsum_option (fun h => LowerReachProb F s ⟨de, r, h⟩)
    simp_rw [hinner]
    rw [ENNReal.tsum_add]
  have hDenom : lowerDenom F s r = lowerArrHalt F s r + ∑' x, lowerArrStep F s r x := by
    unfold lowerDenom
    rw [lower_tsum_option (lowerNumer F s r)]
    rfl
  rw [hMe, hDenom, lowerMe_pending_eq_dep F s r]

/-- **Append inner sum.** Out of a reachable pending config `c₀` whose recorded emission is
`(l, ω)`, the mass appended by one instruction onto the concrete extension `((l, μ), q)` — recording
the **sampled** transition `μ` — is `tKernel(…)(μ) · μ q`. Summing the `h'`-draw (a `PMF`, `= 1`)
and reindexing the `de'`-draw by its last belief `dq`, the Bayes normaliser cancels
(`∑' dq, ω dq · dq q /(ω.bind id) q = 1` when `μ ∈ tKernel.support` and `q ∈ μ.support`; otherwise
the leading `tKernel(…)(μ) · μ q` is `0`). -/
theorem lowerStep_append_inner (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (c₀ : LowerConfig sys) (hcoup : Coupled c₀)
    (l : Label) (ω : PMF (PMF State)) (hh : c₀.h = some (l, ω))
    (hstep : (sys.distF F).step (lastStateOf c₀.de) l ω) (μ : PMF State) (q : State) :
    (∑' (de' : ResolvedExec (PMF State) Label) (h' : Option (Label × PMF (PMF State))),
        LowerStep F s c₀
          ⟨de', ⟨c₀.e.init, c₀.e.trans.append (Seq.cons ((l, μ), q) Seq.nil)⟩, h'⟩)
      = (tKernel F (lastStateOf c₀.de) l ω (lastStateOf c₀.e)) μ * μ q := by
  classical
  set K : ENNReal := (tKernel F (lastStateOf c₀.de) l ω (lastStateOf c₀.e)) μ with hK
  have hde : c₀.de.trans.Terminates := hcoup.1
  have he : c₀.e.trans.Terminates := hcoup.2.1
  set E : ResolvedExec State Label :=
    ⟨c₀.e.init, c₀.e.trans.append (Seq.cons ((l, μ), q) Seq.nil)⟩ with hE
  have hElast : lastStateOf E = q :=
    lastStateOf_append_singleton ⟨c₀.e.init, c₀.e.trans⟩ he (l, μ) q
  have hEmu : lastMuOf E = μ :=
    lastMuOf_append_singleton ⟨c₀.e.init, c₀.e.trans⟩ he l μ q
  set De : PMF State → ResolvedExec (PMF State) Label :=
    fun dq => ⟨c₀.de.init, c₀.de.trans.append (Seq.cons ((l, ω), dq) Seq.nil)⟩ with hDe
  have hDelast : ∀ dq, lastStateOf (De dq) = dq := fun dq =>
    lastStateOf_append_singleton ⟨c₀.de.init, c₀.de.trans⟩ hde (l, ω) dq
  have hval : ∀ (de' : ResolvedExec (PMF State) Label) (h' : Option (Label × PMF (PMF State))),
      LowerStep F s c₀ ⟨de', E, h'⟩
        = (if de'.init = c₀.de.init ∧
             de'.trans = c₀.de.trans.append (Seq.cons ((l, ω), lastStateOf de') Seq.nil)
           then K * μ q * ω (lastStateOf de') *
             (lastStateOf de' q / (ω.bind id) q) * s.next de' h'
           else 0) := by
    intro de' h'
    unfold LowerStep
    rw [hh]
    simp only [hElast, hEmu]
    by_cases hif : de'.init = c₀.de.init ∧ E.init = c₀.e.init ∧
        de'.trans = c₀.de.trans.append (Seq.cons ((l, ω), lastStateOf de') Seq.nil) ∧
        E.trans = c₀.e.trans.append (Seq.cons ((l, μ), q) Seq.nil)
    · rw [if_pos hif, if_pos ⟨hif.1, hif.2.2.1⟩]
    · rw [if_neg hif, if_neg]
      rintro ⟨h1, h2⟩; exact hif ⟨h1, rfl, h2, rfl⟩
  have hsum_h : ∀ de', (∑' h', LowerStep F s c₀ ⟨de', E, h'⟩)
      = (if de'.init = c₀.de.init ∧
           de'.trans = c₀.de.trans.append (Seq.cons ((l, ω), lastStateOf de') Seq.nil)
         then K * μ q * ω (lastStateOf de') * (lastStateOf de' q / (ω.bind id) q)
         else 0) := by
    intro de'
    simp_rw [hval de']
    by_cases hif : de'.init = c₀.de.init ∧
        de'.trans = c₀.de.trans.append (Seq.cons ((l, ω), lastStateOf de') Seq.nil)
    · simp_rw [if_pos hif]
      rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
    · simp_rw [if_neg hif, tsum_zero]
  simp_rw [hsum_h]
  have hreindex : (∑' de' : ResolvedExec (PMF State) Label,
        (if de'.init = c₀.de.init ∧
           de'.trans = c₀.de.trans.append (Seq.cons ((l, ω), lastStateOf de') Seq.nil)
         then K * μ q * ω (lastStateOf de') * (lastStateOf de' q / (ω.bind id) q)
         else 0))
      = ∑' dq : PMF State, K * μ q * ω dq * (dq q / (ω.bind id) q) := by
    refine tsum_eq_tsum_of_ne_zero_bij (i := fun dq : Function.support
        (fun dq : PMF State => K * μ q * ω dq * (dq q / (ω.bind id) q)) => De dq.1) ?inj ?supp ?val
    · rintro ⟨dq₁, h₁⟩ ⟨dq₂, h₂⟩ hab
      refine Subtype.ext ?_
      have := congrArg lastStateOf hab
      rw [hDelast, hDelast] at this; exact this
    · intro de' hde'
      rw [Function.mem_support] at hde'
      by_cases hif : de'.init = c₀.de.init ∧
          de'.trans = c₀.de.trans.append (Seq.cons ((l, ω), lastStateOf de') Seq.nil)
      · refine ⟨⟨lastStateOf de', ?_⟩, ?_⟩
        · rw [Function.mem_support]; rwa [if_pos hif] at hde'
        · change De (lastStateOf de') = de'
          rw [hDe]
          obtain ⟨di, dt⟩ := de'
          simp only at hif ⊢
          obtain ⟨h1, h2⟩ := hif
          rw [← h1, ← h2]
      · rw [if_neg hif] at hde'; exact absurd rfl hde'
    · rintro ⟨dq, hdq⟩
      rw [if_pos ⟨rfl, by rw [hDelast]⟩, hDelast]
  rw [hreindex]
  by_cases hKμ : K * μ q = 0
  · rw [hKμ]; simp only [zero_mul, tsum_zero]
  · obtain ⟨hK0, hμ0⟩ := mul_ne_zero_iff.mp hKμ
    have hμmem : μ ∈ (tKernel F (lastStateOf c₀.de) l ω (lastStateOf c₀.e)).support :=
      (PMF.mem_support_iff _ _).mpr hK0
    have hqμ : q ∈ μ.support := (PMF.mem_support_iff _ _).mpr hμ0
    have hne0 : (ω.bind id) q ≠ 0 := by
      have := tKernel_mem_bind F (lastStateOf c₀.de) l ω (lastStateOf c₀.e) hcoup.2.2 hstep μ
        hμmem q hqμ
      rwa [PMF.mem_support_iff] at this
    have hstep1 : (∑' dq : PMF State, K * μ q * ω dq * (dq q / (ω.bind id) q))
        = K * μ q * ∑' dq : PMF State, ω dq * (dq q / (ω.bind id) q) := by
      rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun dq => by ring
    rw [hstep1]
    have hfib : (∑' dq : PMF State, ω dq * (dq q / (ω.bind id) q)) = 1 := by
      have h2 : ∑' dq : PMF State, ω dq * (dq q / (ω.bind id) q)
          = (ω.bind id) q * ((ω.bind id) q)⁻¹ := by
        calc ∑' dq : PMF State, ω dq * (dq q / (ω.bind id) q)
            = ∑' dq : PMF State, (ω dq * dq q) * ((ω.bind id) q)⁻¹ := by
              refine tsum_congr fun dq => ?_; rw [div_eq_mul_inv]; ring
          _ = (∑' dq : PMF State, ω dq * dq q) * ((ω.bind id) q)⁻¹ := ENNReal.tsum_mul_right
          _ = (ω.bind id) q * ((ω.bind id) q)⁻¹ := by
                rw [show (∑' dq : PMF State, ω dq * dq q) = (ω.bind id) q by
                  simp only [PMF.bind_apply, id_eq]]
      rw [h2]; exact ENNReal.mul_inv_cancel hne0 (PMF.apply_ne_top (ω.bind id) q)
    rw [hfib, mul_one]

/-- **Append match.** Any nonzero one-instruction weight from `c₀` onto a concrete extension
`(l, μ) q` of `r` forces `c₀` to be the reachable pending predecessor `⟨_, r, some (l, ω)⟩` (append
injectivity + scheduler validity). The recorded `μ` is the sampled transition, so it is no longer
pinned to a fixed value. -/
theorem lowerStep_append_match (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (r : ResolvedExec State Label) (l : Label) (μ : PMF State)
    (c₀ : LowerConfig sys) (hrp : LowerReachProb F s c₀ ≠ 0) (q : State)
    (de' : ResolvedExec (PMF State) Label) (h' : Option (Label × PMF (PMF State)))
    (hne : LowerStep F s c₀ ⟨de', ⟨r.init,
      r.trans.append (Seq.cons ((l, μ), q) Seq.nil)⟩, h'⟩ ≠ 0) :
    ∃ ω, c₀.h = some (l, ω) ∧ c₀.e = r ∧
      Coupled c₀ ∧ (sys.distF F).step (lastStateOf c₀.de) l ω := by
  classical
  set E : ResolvedExec State Label :=
    ⟨r.init, r.trans.append (Seq.cons ((l, μ), q) Seq.nil)⟩ with hE
  obtain ⟨l₀, ωω, hh⟩ : ∃ l₀ ωω, c₀.h = some (l₀, ωω) := by
    rcases hhc : c₀.h with _ | ⟨l₀, ωω⟩
    · exfalso; revert hne; unfold LowerStep; rw [hhc]; intro hne; exact hne rfl
    · exact ⟨l₀, ωω, rfl⟩
  obtain ⟨hcoup, hstepF⟩ := reachProb_pending_step F s c₀ hrp l₀ ωω hh
  revert hne
  unfold LowerStep
  rw [hh]
  simp only
  set μ'₀ : PMF State := lastMuOf E with hμ'₀
  by_cases hif : de'.init = c₀.de.init ∧ E.init = c₀.e.init ∧
      de'.trans = c₀.de.trans.append (Seq.cons ((l₀, ωω), lastStateOf de') Seq.nil) ∧
      E.trans = c₀.e.trans.append (Seq.cons ((l₀, μ'₀), lastStateOf E) Seq.nil)
  · intro _
    obtain ⟨_, heinit, _, het⟩ := hif
    have happ : r.trans.append (Seq.cons ((l, μ), q) Seq.nil)
        = c₀.e.trans.append (Seq.cons ((l₀, μ'₀), lastStateOf E) Seq.nil) := het
    have hRHSterm : (c₀.e.trans.append (Seq.cons ((l₀, μ'₀), lastStateOf E) Seq.nil)).Terminates :=
      ⟨Nat.find hcoup.2.1 + 1, Stream'.Seq.terminatedAt_append_find hcoup.2.1
        (show (Seq.cons ((l₀, μ'₀), lastStateOf E) Seq.nil).TerminatedAt 1 from rfl)⟩
    have hLHSterm : (r.trans.append (Seq.cons ((l, μ), q) Seq.nil)).Terminates := happ ▸ hRHSterm
    have hrterm : r.trans.Terminates :=
      terminates_of_append_singleton r.trans ((l, μ), q) hLHSterm
    have hlast :=
      Stream'.Seq.append_singleton_inj_right r.trans c₀.e.trans hrterm hcoup.2.1 _ _ happ
    have htrans :=
      Stream'.Seq.append_singleton_inj_left r.trans c₀.e.trans hrterm hcoup.2.1 _ _ happ
    rw [Prod.mk.injEq, Prod.mk.injEq] at hlast
    obtain ⟨⟨hl, _⟩, _⟩ := hlast
    have her : c₀.e = r := alterSeq_ext heinit.symm htrans.symm
    refine ⟨ωω, ?_, her, hcoup, ?_⟩
    · rw [hl]
    · rw [hl]; exact hstepF
  · rw [if_neg hif]; intro h0; exact absurd rfl h0

/-- **Append expand.** The arrival-mass at a one-step extension of `r` is the one-instruction
convolution of predecessor reach-probs with `LowerStep` onto that extension (`peel` each summand,
then swap the `(de, h)`-marginals inside the predecessor sum). -/
theorem lowerMe_append_expand (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (r : ResolvedExec State Label) (l : Label) (μ : PMF State) (q : State) :
    lowerMe F s ⟨r.init, r.trans.append (Seq.cons ((l, μ), q) Seq.nil)⟩
      = ∑' c₀, LowerReachProb F s c₀ *
          (∑' (de' : ResolvedExec (PMF State) Label) (h' : Option (Label × PMF (PMF State))),
            LowerStep F s c₀
              ⟨de', ⟨r.init, r.trans.append (Seq.cons ((l, μ), q) Seq.nil)⟩, h'⟩) := by
  classical
  unfold lowerMe
  have hpeel : ∀ (de : ResolvedExec (PMF State) Label) (h : Option (Label × PMF (PMF State))),
      LowerReachProb F s ⟨de, ⟨r.init, r.trans.append (Seq.cons ((l, μ), q) Seq.nil)⟩, h⟩
        = ∑' c₀, LowerReachProb F s c₀ * LowerStep F s c₀
            ⟨de, ⟨r.init, r.trans.append (Seq.cons ((l, μ), q) Seq.nil)⟩, h⟩ :=
    fun de h => LowerReachProb_peel F s _ (reachAfter_zero_of_append F s de r ((l, μ), q) h)
  simp_rw [hpeel]
  rw [show (∑' (de : ResolvedExec (PMF State) Label) (h : Option (Label × PMF (PMF State)))
      (c₀ : LowerConfig sys), LowerReachProb F s c₀ * LowerStep F s c₀
        ⟨de, ⟨r.init, r.trans.append (Seq.cons ((l, μ), q) Seq.nil)⟩, h⟩)
      = ∑' (p : ResolvedExec (PMF State) Label × Option (Label × PMF (PMF State)))
          (c₀ : LowerConfig sys), LowerReachProb F s c₀ * LowerStep F s c₀
            ⟨p.1, ⟨r.init, r.trans.append (Seq.cons ((l, μ), q) Seq.nil)⟩, p.2⟩ by
    rw [ENNReal.tsum_prod']]
  rw [ENNReal.tsum_comm (f := fun (p : ResolvedExec (PMF State) Label ×
      Option (Label × PMF (PMF State))) (c₀ : LowerConfig sys) =>
    LowerReachProb F s c₀ * LowerStep F s c₀
      ⟨p.1, ⟨r.init, r.trans.append (Seq.cons ((l, μ), q) Seq.nil)⟩, p.2⟩)]
  refine tsum_congr fun c₀ => ?_
  rw [ENNReal.tsum_prod' (f := fun p : ResolvedExec (PMF State) Label ×
      Option (Label × PMF (PMF State)) =>
    LowerReachProb F s c₀ * LowerStep F s c₀
      ⟨p.1, ⟨r.init, r.trans.append (Seq.cons ((l, μ), q) Seq.nil)⟩, p.2⟩)]
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun de' => ?_
  rw [← ENNReal.tsum_mul_left]

/-- **Append ratio (per predecessor).** Out of a reachable `c₀`, the one-instruction append-mass
onto extension `(l, μ) q` scales with `μ q`: it is `μ q` times the total append-mass summed over the
sampled next state (either all zero, or `c₀` qualifies and each append-mass is `μ q'` by
`lowerStep_append_inner`, whose sum over `q'` is `1`). -/
theorem lowerMe_append_inner_ratio (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (r : ResolvedExec State Label) (l : Label) (μ : PMF State)
    (c₀ : LowerConfig sys) (hrp : LowerReachProb F s c₀ ≠ 0) (q : State) :
    (∑' (de' : ResolvedExec (PMF State) Label) (h' : Option (Label × PMF (PMF State))),
        LowerStep F s c₀ ⟨de', ⟨r.init, r.trans.append (Seq.cons ((l, μ), q) Seq.nil)⟩, h'⟩)
      = μ q * (∑' (q' : State) (de' : ResolvedExec (PMF State) Label)
          (h' : Option (Label × PMF (PMF State))),
        LowerStep F s c₀ ⟨de', ⟨r.init, r.trans.append (Seq.cons ((l, μ), q') Seq.nil)⟩, h'⟩) := by
  classical
  set Inner : State → ENNReal := fun qq =>
    ∑' (de' : ResolvedExec (PMF State) Label) (h' : Option (Label × PMF (PMF State))),
      LowerStep F s c₀ ⟨de', ⟨r.init, r.trans.append (Seq.cons ((l, μ), qq) Seq.nil)⟩, h'⟩
    with hInner
  change Inner q = μ q * ∑' q', Inner q'
  by_cases hex : ∃ q₀, Inner q₀ ≠ 0
  · obtain ⟨q₀, hq₀⟩ := hex
    obtain ⟨de', hde'⟩ := tsum_ne_zero_exists hq₀
    obtain ⟨h', hh'⟩ := tsum_ne_zero_exists hde'
    obtain ⟨ω, hhω, her, hcoup, hstep⟩ :=
      lowerStep_append_match F s r l μ c₀ hrp q₀ de' h' hh'
    set K : ENNReal := (tKernel F (lastStateOf c₀.de) l ω (lastStateOf c₀.e)) μ with hK
    have hInnerEq : ∀ qq, Inner qq = K * μ qq := by
      intro qq
      rw [hInner]
      simp only
      rw [← her]
      exact lowerStep_append_inner F s c₀ hcoup l ω hhω hstep μ qq
    rw [hInnerEq q]
    have hsum1 : (∑' q', Inner q') = K := by
      simp_rw [hInnerEq]
      rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
    rw [hsum1]; ring
  · push Not at hex
    have hall : ∀ qq, Inner qq = 0 := hex
    rw [hall q]
    have : (∑' q', Inner q') = 0 := by simp_rw [hall]; exact tsum_zero
    rw [this, mul_zero]

/-- **Flow (B): arrival at a one-step extension.** The chain's arrival-mass at `r` extended by one
concrete step `((l, μ), q)` is `μ q` times the step-arrival `lowerArrStep F s r (l, μ)`. The
per-predecessor ratio (`lowerMe_append_inner_ratio`) pulls out `μ q`; the remaining factor is the
step-arrival (`lowerArrStep = ∑' q', lowerMe (r ++ ((l, μ), q'))`, re-expanded). -/
theorem lowerMe_append (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (r : ResolvedExec State Label) (l : Label) (μ : PMF State) (q : State) :
    lowerMe F s ⟨r.init, r.trans.append (Seq.cons ((l, μ), q) Seq.nil)⟩
      = μ q * lowerArrStep F s r (l, μ) := by
  classical
  rw [lowerMe_append_expand F s r l μ q]
  have hterm : ∀ c₀, LowerReachProb F s c₀ *
        (∑' (de' : ResolvedExec (PMF State) Label) (h' : Option (Label × PMF (PMF State))),
          LowerStep F s c₀ ⟨de', ⟨r.init, r.trans.append (Seq.cons ((l, μ), q) Seq.nil)⟩, h'⟩)
      = μ q * (LowerReachProb F s c₀ *
          (∑' (q' : State) (de' : ResolvedExec (PMF State) Label)
            (h' : Option (Label × PMF (PMF State))),
          LowerStep F s c₀
            ⟨de', ⟨r.init, r.trans.append (Seq.cons ((l, μ), q') Seq.nil)⟩, h'⟩)) := by
    intro c₀
    by_cases hrp : LowerReachProb F s c₀ = 0
    · simp [hrp]
    · rw [lowerMe_append_inner_ratio F s r l μ c₀ hrp q]; ring
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left]
  congr 1
  have hArr : lowerArrStep F s r (l, μ)
      = ∑' (q' : State), lowerMe F s ⟨r.init, r.trans.append (Seq.cons ((l, μ), q') Seq.nil)⟩ := by
    unfold lowerArrStep lowerMe
    rw [ENNReal.tsum_comm]
  rw [hArr]
  simp_rw [lowerMe_append_expand]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun c₀ => ?_
  rw [← ENNReal.tsum_mul_left]

/-- The arrival-mass at the start `⟨sys.init, nil⟩` is `1`: only the level-`0` start config
contributes, and its mass is `∑' h, s.next ⟨δ_init, nil⟩ h = 1` (a `PMF`). -/
theorem lowerMe_nil (F : Fairness sys) (s : ResolvedScheduler (sys.distF F)) :
    lowerMe F s ⟨sys.init, Seq.nil⟩ = 1 := by
  classical
  unfold lowerMe
  have hnilterm : (⟨sys.init, Seq.nil⟩ : ResolvedExec State Label).trans.Terminates :=
    Stream'.Seq.terminates_nil
  have hcollapse : ∀ (de : ResolvedExec (PMF State) Label)
      (h : Option (Label × PMF (PMF State))),
      LowerReachProb F s ⟨de, ⟨sys.init, Seq.nil⟩, h⟩
        = LowerReachAfter F s 0 ⟨de, ⟨sys.init, Seq.nil⟩, h⟩ := by
    intro de h
    rw [LowerReachProb_collapse F s ⟨de, ⟨sys.init, Seq.nil⟩, h⟩ hnilterm]
    congr 1
    exact Nat.eq_zero_of_le_zero (Nat.find_le (Stream'.Seq.terminatedAt_nil))
  simp_rw [hcollapse, LowerReachAfter_zero, and_true]
  rw [tsum_eq_single (⟨PMF.pure sys.init, Seq.nil⟩ : ResolvedExec (PMF State) Label) ?_]
  · simp only [if_true]
    exact PMF.tsum_coe _
  · intro de hde
    simp only [if_neg hde, tsum_zero]

/-- The arrival-mass at any *other* nil history `⟨i, nil⟩` (with `i ≠ sys.init`) is `0`: the chain
starts only from `sys.init`. -/
theorem lowerMe_nil_ne (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (i : State) (hi : i ≠ sys.init) : lowerMe F s ⟨i, Seq.nil⟩ = 0 := by
  classical
  unfold lowerMe
  rw [ENNReal.tsum_eq_zero]
  intro de
  rw [ENNReal.tsum_eq_zero]
  intro h
  have hnilterm : (⟨i, Seq.nil⟩ : ResolvedExec State Label).trans.Terminates :=
    Stream'.Seq.terminates_nil
  rw [LowerReachProb_collapse F s ⟨de, ⟨i, Seq.nil⟩, h⟩ hnilterm]
  rw [show Nat.find (hnilterm) = 0 from
    Nat.eq_zero_of_le_zero (Nat.find_le (Stream'.Seq.terminatedAt_nil))]
  rw [LowerReachAfter_zero, if_neg]
  rintro ⟨-, he⟩
  exact hi (congrArg AlterSeq.init he)

/-- The scheduler's step-emission at `e` is the step-arrival ratio when `e` is reachable
(`lowerDenom e ≠ 0`): `lowerNext e (some (l, μ)) = lowerArrStep e (l, μ) / lowerDenom e`. -/
theorem lowerNext_some_of_ne_zero (F : Fairness sys) (sch : ResolvedScheduler (sys.distF F))
    (e : ResolvedExec State Label) (l : Label) (μ : PMF State) (hd : lowerDenom F sch e ≠ 0) :
    lowerNext F sch e (some (l, μ)) = lowerArrStep F sch e (l, μ) / lowerDenom F sch e := by
  classical
  unfold lowerNext
  rw [dif_neg hd]
  rfl

/-- The step-arrival at any single `(l, μ)` is bounded by the denominator (it is one summand of the
total step arrival, itself `≤ lowerDenom`). -/
theorem lowerArrStep_le_lowerDenom (F : Fairness sys) (sch : ResolvedScheduler (sys.distF F))
    (e : ResolvedExec State Label) (x : Label × PMF State) :
    lowerArrStep F sch e x ≤ lowerDenom F sch e := by
  classical
  have hsplit : lowerDenom F sch e = lowerArrHalt F sch e + ∑' x, lowerArrStep F sch e x := by
    unfold lowerDenom
    rw [lower_tsum_option (lowerNumer F sch e)]
    rfl
  rw [hsplit]
  calc lowerArrStep F sch e x ≤ ∑' x, lowerArrStep F sch e x := ENNReal.le_tsum x
    _ ≤ lowerArrHalt F sch e + ∑' x, lowerArrStep F sch e x := le_add_self

/-- **Core: path-measure = arrival-mass.** The resolved path-measure of the concrete execution
`lowerSched F s` at any terminating history `r` equals the chain's arrival-mass at `r`. Cons-end
length induction: the base is `lowerMe_nil`/`lowerMe_nil_ne`; the step peels the last transition
(`probOfR_append_singleton`), applies the IH to the prefix, rewrites `lowerMe = lowerDenom` (Flow A)
and `lowerMe (r ++ step) = μ q · lowerArrStep` (Flow B), then cancels `lowerDenom / lowerDenom` on
reachable prefix (both sides vanish on unreachable prefixes). -/
theorem probOfR_eq_lowerMe (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (r : ResolvedExec State Label) (hterm : r.trans.Terminates) :
    (⟨PMF.pure sys.init, lowerSched F s⟩ : ResolvedProbabilisticExecution sys).probOfR r hterm
      = lowerMe F s r := by
  classical
  set pe : ResolvedProbabilisticExecution sys := ⟨PMF.pure sys.init, lowerSched F s⟩ with hpe
  suffices H : ∀ n (r : ResolvedExec State Label) (hterm : r.trans.Terminates),
      (r.trans.toList hterm).length = n → pe.probOfR r hterm = lowerMe F s r from H _ r hterm rfl
  intro n
  induction n with
  | zero =>
    intro r hterm hlen
    have htoList : r.trans.toList hterm = [] := List.length_eq_zero_iff.mp hlen
    obtain ⟨i, t⟩ := r
    have h_nil : t = Seq.nil := by
      have hh := Stream'.Seq.ofList_toList t hterm
      rw [htoList, Stream'.Seq.ofList_nil] at hh
      exact hh.symm
    subst h_nil
    rw [pe.probOfR_nil i]
    by_cases hi : i = sys.init
    · subst hi
      change (PMF.pure sys.init) sys.init = _
      rw [PMF.pure_apply, if_pos rfl]
      exact (lowerMe_nil F s).symm
    · change (PMF.pure sys.init) i = _
      rw [PMF.pure_apply, if_neg hi]
      exact (lowerMe_nil_ne F s i hi).symm
  | succ k ih =>
    intro r hterm hlen
    have hne : r.trans.toList hterm ≠ [] := by
      intro hnil; rw [hnil, List.length_nil] at hlen; exact Nat.succ_ne_zero k hlen.symm
    obtain ⟨prev, last, hprev, hsplit, hprevlist, -⟩ :=
      Stream'.Seq.exists_split_last r.trans hterm hne
    have happ : (prev.append (Seq.cons last Seq.nil)).Terminates := hsplit ▸ hterm
    have hr_eq : r = ⟨r.init, prev.append (Seq.cons last Seq.nil)⟩ := by
      obtain ⟨ri, rt⟩ := r; exact congrArg (AlterSeq.mk ri) hsplit
    have hlen_prev : (prev.toList hprev).length = k := by
      have h1 : (prev.toList hprev).length = (r.trans.toList hterm).length - 1 := by
        rw [hprevlist, List.length_dropLast]
      omega
    obtain ⟨⟨l, μ⟩, q⟩ := last
    rw [pe.probOfR_congr r ⟨r.init, prev.append (Seq.cons ((l, μ), q) Seq.nil)⟩ hr_eq hterm happ,
      pe.probOfR_append_singleton r.init prev hprev ((l, μ), q) happ]
    rw [ih ⟨r.init, prev⟩ hprev hlen_prev]
    have hrk : pe.rkernel ⟨r.init, prev⟩ ((l, μ), q)
        = lowerNext F s ⟨r.init, prev⟩ (some (l, μ)) * μ q := rfl
    rw [hrk]
    rw [lowerMe_eq_lowerDenom F s ⟨r.init, prev⟩]
    rw [hr_eq,
      show (⟨r.init, prev.append (Seq.cons ((l, μ), q) Seq.nil)⟩ : ResolvedExec State Label)
        = ⟨(⟨r.init, prev⟩ : ResolvedExec State Label).init,
            (⟨r.init, prev⟩ : ResolvedExec State Label).trans.append
              (Seq.cons ((l, μ), q) Seq.nil)⟩ from rfl,
      lowerMe_append F s ⟨r.init, prev⟩ l μ q]
    set E₀ : ResolvedExec State Label := ⟨r.init, prev⟩ with hE₀
    by_cases hd : lowerDenom F s E₀ = 0
    · rw [hd, zero_mul]
      have hle := lowerArrStep_le_lowerDenom F s E₀ (l, μ)
      rw [hd] at hle
      rw [nonpos_iff_eq_zero.mp hle, mul_zero]
    · rw [lowerNext_some_of_ne_zero F s E₀ l μ hd, ENNReal.div_eq_inv_mul,
        show lowerDenom F s E₀ * ((lowerDenom F s E₀)⁻¹ * lowerArrStep F s E₀ (l, μ) * μ q)
          = (lowerDenom F s E₀ * (lowerDenom F s E₀)⁻¹) * (lowerArrStep F s E₀ (l, μ) * μ q)
          by ring,
        ENNReal.mul_inv_cancel hd (lowerDenom_ne_top F s E₀), one_mul]
      ring

/-- A tight resolved execution terminates: `IsTight` already carries a `TerminatedAt` witness, which
transfers from the plain image `r.toExec` back to the resolved history `r`. -/
theorem terminates_of_isTight {r : ResolvedExec State Label} (h : sys.IsTight r.toExec) :
    r.trans.Terminates := by
  classical
  have hiff : ∀ n, r.toExec.trans.TerminatedAt n ↔ r.trans.TerminatedAt n := by
    intro n
    unfold Stream'.Seq.TerminatedAt
    unfold ResolvedExec.toExec
    simp only [Stream'.Seq.map_get?, Option.map_eq_none_iff]
  unfold System.IsTight at h
  rcases h with h0 | ⟨n, _, _, _, hn1, _⟩
  · exact ⟨0, (hiff 0).mp h0⟩
  · exact ⟨n + 1, (hiff (n + 1)).mp hn1⟩

/-! ### The abstract equation, via the belief-tracking invariant

`traceProbR_eq_reachE` (concrete) is proved. The abstract `traceProbR_eq_reachDe` reduces — by the
same flatten/reindex used for the concrete equation — to the **abstract core**
`lowerMde_eq_probOfR`: `∑' e h, LowerReachProb ⟨D,e,h⟩ = pe.probOfR D`, i.e. the chain's
abstract-run
marginal reproduces the original abstract execution `pe = ⟨δ_{δ_init}, s⟩`. That in turn follows
from
the **belief-tracking invariant** `abstractArr_eq`:
`abstractArr D qₚ = pe.probOfR D · (lastStateOf D) qₚ` — conditioned on the abstract run `D`, the
concrete endpoint is distributed as the running belief `lastStateOf D`. This is TRUE precisely
because
`μ'` is sampled from `tKernel` (it was false for the old deterministic `tOutcome`): the averaging
over
the concrete endpoint uses the GLOBAL witness identity `tKernel_bind_avg`. -/

/-- **Belief-tracking arrival mass.** The chain's reach-mass of configs whose abstract run is `D`
and
whose concrete run ends at `qₚ`, marginalised over the concrete run `e` (grouped by its endpoint)
and
the pending emission `h`. -/
noncomputable def abstractArr (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (D : ResolvedExec (PMF State) Label) (qₚ : State) : ENNReal := by
  classical
  exact ∑' (e : ResolvedExec State Label) (h : Option (Label × PMF (PMF State))),
    if lastStateOf e = qₚ then LowerReachProb F s ⟨D, e, h⟩ else 0

/-- **Pending-emission factoring (one instruction).** The pending emission `h` enters `LowerStep`
only through the final `s.next c'.de c'.h` factor (the if-condition and all other factors are
`h`-free), so it factors out. Proof: `unfold LowerStep`; in the `some (l,ω)` branch the `h`-free
prefix `P` gives `LowerStep c₀ ⟨D,e,h⟩ = P · s.next D h`, and `∑' h', LowerStep c₀ ⟨D,e,h'⟩ = P`
(`s.next D` is a `PMF`, `∑ = 1`, `ENNReal.tsum_mul_left`); the `none` branch is `0`. -/
theorem lowerStep_pending_factor (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (c₀ : LowerConfig sys) (D : ResolvedExec (PMF State) Label) (e : ResolvedExec State Label)
    (h : Option (Label × PMF (PMF State))) :
    LowerStep F s c₀ ⟨D, e, h⟩
      = (∑' h', LowerStep F s c₀ ⟨D, e, h'⟩) * s.next D h := by
  classical
  cases hh : c₀.h with
  | none =>
    have hz : ∀ h' : Option (Label × PMF (PMF State)),
        LowerStep F s c₀ ⟨D, e, h'⟩ = 0 := by
      intro h'; unfold LowerStep; rw [hh]
    rw [hz h]; simp_rw [hz]; simp only [tsum_zero, zero_mul]
  | some lω =>
    obtain ⟨l, ω⟩ := lω
    -- The if-condition and the factor `P` are `h`-free; only `s.next D h` depends on `h`.
    set P : ENNReal := (tKernel F (lastStateOf c₀.de) l ω (lastStateOf c₀.e)) (lastMuOf e)
        * (lastMuOf e) (lastStateOf e) * ω (lastStateOf D)
        * ((lastStateOf D) (lastStateOf e) / (ω.bind id) (lastStateOf e)) with hP
    have hval : ∀ h' : Option (Label × PMF (PMF State)),
        LowerStep F s c₀ ⟨D, e, h'⟩
          = (if D.init = c₀.de.init ∧ e.init = c₀.e.init ∧
               D.trans = c₀.de.trans.append (Seq.cons ((l, ω), lastStateOf D) Seq.nil) ∧
               e.trans = c₀.e.trans.append (Seq.cons ((l, lastMuOf e), lastStateOf e) Seq.nil)
             then P * s.next D h' else 0) := by
      intro h'
      rw [hP]
      unfold LowerStep
      rw [hh]
    rw [hval h]
    by_cases hif : D.init = c₀.de.init ∧ e.init = c₀.e.init ∧
        D.trans = c₀.de.trans.append (Seq.cons ((l, ω), lastStateOf D) Seq.nil) ∧
        e.trans = c₀.e.trans.append (Seq.cons ((l, lastMuOf e), lastStateOf e) Seq.nil)
    · rw [if_pos hif]
      have hsum : (∑' h', LowerStep F s c₀ ⟨D, e, h'⟩) = P := by
        simp_rw [hval, if_pos hif]
        rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
      rw [hsum, mul_assoc]
    · rw [if_neg hif]
      have hsum : (∑' h', LowerStep F s c₀ ⟨D, e, h'⟩) = 0 := by
        simp_rw [hval, if_neg hif]; exact tsum_zero
      rw [hsum, zero_mul]

/-- **Pending-emission factoring (reach-prob).** Lifts `lowerStep_pending_factor` through the level
recursion: prove `LowerReachAfter n ⟨D,e,h⟩ = (∑' h', LowerReachAfter n ⟨D,e,h'⟩) · s.next D h` by
induction on `n` — base: `LowerReachAfter 0 ⟨D,e,h⟩ = (if D = δ_init-run ∧ e = init-run then
s.next D h else 0)`, and `∑' h'` of it is the same `if … then 1 else 0`; step: convolve, pull the
`h`-factor out of each `LowerStep` via `lowerStep_pending_factor`, then `ENNReal.tsum_mul_right` /
`∑' h' s.next = 1` — then sum over `n` (`ENNReal.tsum_mul_right`, swap `∑ n`/`∑ h'`). -/
theorem lowerReachProb_pending_factor (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (D : ResolvedExec (PMF State) Label) (e : ResolvedExec State Label)
    (h : Option (Label × PMF (PMF State))) :
    LowerReachProb F s ⟨D, e, h⟩
      = (∑' h', LowerReachProb F s ⟨D, e, h'⟩) * s.next D h := by
  classical
  -- Per-level version, by induction on `n`.
  have hlevel : ∀ (n : ℕ),
      LowerReachAfter F s n ⟨D, e, h⟩
        = (∑' h', LowerReachAfter F s n ⟨D, e, h'⟩) * s.next D h := by
    intro n
    induction n with
    | zero =>
      rw [LowerReachAfter_zero]
      simp only []
      by_cases hc : D = ⟨PMF.pure sys.init, Seq.nil⟩ ∧ e = ⟨sys.init, Seq.nil⟩
      · rw [if_pos hc]
        have hsum : (∑' h', LowerReachAfter F s 0 ⟨D, e, h'⟩)
            = ∑' h', s.next ⟨PMF.pure sys.init, Seq.nil⟩ h' := by
          refine tsum_congr fun h' => ?_
          rw [LowerReachAfter_zero, if_pos hc]
        rw [hsum, PMF.tsum_coe, one_mul, hc.1]
      · rw [if_neg hc]
        have hsum : (∑' h', LowerReachAfter F s 0 ⟨D, e, h'⟩) = 0 := by
          refine ENNReal.tsum_eq_zero.mpr fun h' => ?_
          rw [LowerReachAfter_zero, if_neg hc]
        rw [hsum, zero_mul]
    | succ k _ =>
      rw [LowerReachAfter_succ]
      -- Pull `s.next D h` out of each summand via `lowerStep_pending_factor`.
      have hfac : ∀ c₀, LowerReachAfter F s k c₀ * LowerStep F s c₀ ⟨D, e, h⟩
          = (LowerReachAfter F s k c₀ * (∑' h', LowerStep F s c₀ ⟨D, e, h'⟩)) * s.next D h := by
        intro c₀
        rw [lowerStep_pending_factor F s c₀ D e h, mul_assoc]
      simp_rw [hfac]
      rw [ENNReal.tsum_mul_right]
      congr 1
      simp_rw [LowerReachAfter_succ]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun c₀ => ?_
      rw [← ENNReal.tsum_mul_left]
  unfold LowerReachProb
  simp_rw [hlevel]
  rw [ENNReal.tsum_mul_right]
  congr 1
  rw [ENNReal.tsum_comm]

/-- **Kernel belief-average = flattened successor** (the GLOBAL witness identity). Averaging the
sampled concrete transition over the belief `β` reproduces the flattened next-belief:
`∑' qₚ, β qₚ · (tKernel F β l ω qₚ).bind id x = (ω.bind id) x`. Proof mirrors `tKernel_mem_bind`:
the
LHS is `(β.bind (fun qₚ => (tKernel F β l ω qₚ).bind id)) x`; case `F.dist.fair β l ω`, whose
witness
`p = hf.2.choose` (resp. the step witness `hstep.1.choose`) satisfies `hf.2.choose_spec.2` (resp.
`hstep.1.choose_spec.2`): `ω.bind id = β.bind (fun s => (p s).bind id)`, and `tKernel … qₚ = p qₚ`
on
`β.support` — so use `PMF.bind_apply` and rewrite by the witness identity. -/
theorem tKernel_bind_avg (F : Fairness sys) (β : PMF State) (l : Label) (ω : PMF (PMF State))
    (hstep : (sys.distF F).step β l ω) (x : State) :
    (∑' qₚ : State, β qₚ * ((tKernel F β l ω qₚ).bind id) x) = (ω.bind id) x := by
  classical
  -- The LHS is `(β.bind (fun qₚ => (tKernel F β l ω qₚ).bind id)) x`.
  have hLHS : (∑' qₚ : State, β qₚ * ((tKernel F β l ω qₚ).bind id) x)
      = (β.bind (fun qₚ => (tKernel F β l ω qₚ).bind id)) x := by
    rw [PMF.bind_apply]
  rw [hLHS]
  -- On each branch `tKernel F β l ω = p`, and `ω.bind id = β.bind (fun s => (p s).bind id)`.
  by_cases hf : F.dist.fair β l ω
  · have hbind : ω.bind id = β.bind (fun s => (hf.2.choose s).bind id) := hf.2.choose_spec.2
    rw [hbind]
    have hk : (fun qₚ => (tKernel F β l ω qₚ).bind id) = (fun s => (hf.2.choose s).bind id) := by
      funext qₚ
      congr 1
      unfold tKernel
      rw [dif_pos hf]
    rw [hk]
  · have hbind : ω.bind id = β.bind (fun s => (hstep.1.choose s).bind id) := hstep.1.choose_spec.2
    rw [hbind]
    have hk : (fun qₚ => (tKernel F β l ω qₚ).bind id)
        = (fun s => (hstep.1.choose s).bind id) := by
      funext qₚ
      congr 1
      unfold tKernel
      rw [dif_neg hf, dif_pos hstep]
    rw [hk]

/-- Higher levels never reach a config whose abstract run is nil: each instruction appends to `de`,
so `de.trans = nil` forces level `0`. (Every `LowerStep c₀ ⟨⟨i,nil⟩,e,h⟩ = 0`: the if-condition
demands `nil = c₀.de.trans.append (Seq.cons _ nil)`, impossible.) -/
theorem reachAfter_succ_de_nil (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (n : ℕ) (i : PMF State) (e : ResolvedExec State Label)
    (h : Option (Label × PMF (PMF State))) :
    LowerReachAfter F s (n + 1) ⟨⟨i, Seq.nil⟩, e, h⟩ = 0 := by
  classical
  rw [LowerReachAfter_succ]
  refine ENNReal.tsum_eq_zero.mpr fun c₀ => ?_
  -- Every `LowerStep c₀ ⟨⟨i,nil⟩,e,h⟩ = 0`: the de-append can't be `nil`.
  have hz : LowerStep F s c₀ ⟨⟨i, Seq.nil⟩, e, h⟩ = 0 := by
    unfold LowerStep
    cases hh : c₀.h with
    | none => rfl
    | some lω =>
      obtain ⟨l, ω⟩ := lω
      simp only
      rw [if_neg]
      rintro ⟨-, -, hde, -⟩
      -- `hde : Seq.nil = c₀.de.trans.append (Seq.cons _ Seq.nil)`
      exact append_singleton_not_terminatedAt_zero c₀.de.trans _
        (hde ▸ (Stream'.Seq.terminatedAt_nil (n := 0)))
  rw [hz, mul_zero]

/-- The level-`0` mass of a config whose abstract run is a nonempty append is `0` (its `de` is not
the
start's `nil`). De-side analogue of `reachAfter_zero_of_append`; needed to `LowerReachProb_peel` in
the step of `abstractArr_eq`. -/
theorem reachAfter_zero_of_de_append (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (i : PMF State) (t : Seq ((Label × PMF (PMF State)) × PMF State))
    (x : (Label × PMF (PMF State)) × PMF State)
    (e : ResolvedExec State Label) (h : Option (Label × PMF (PMF State))) :
    LowerReachAfter F s 0 ⟨⟨i, t.append (Seq.cons x Seq.nil)⟩, e, h⟩ = 0 := by
  classical
  rw [LowerReachAfter_zero, if_neg]
  rintro ⟨hde, -⟩
  -- `hde : ⟨i, t.append (cons x nil)⟩ = ⟨δ_init, nil⟩`, so `t.append (cons x nil) = nil`.
  have htr : t.append (Seq.cons x Seq.nil) = Seq.nil := congrArg AlterSeq.trans hde
  refine append_singleton_not_terminatedAt_zero t x ?_
  rw [htr]; exact Stream'.Seq.terminatedAt_nil

/-- **Belief-tracking invariant.** The chain's abstract-run marginal reproduces `pe`, with the
concrete endpoint distributed as the running belief:
`abstractArr D qₚ = pe.probOfR D · (last D) qₚ`.
Length induction on `D` (mirror `probOfR_eq_lowerMe`: `suffices ∀ n D hterm,
(D.trans.toList hterm).length = n → …`).

* **Base** (`D = ⟨i, nil⟩`): `reachAfter_succ_de_nil` collapses `LowerReachProb ⟨⟨i,nil⟩,e,h⟩` to
  `LowerReachAfter 0` (the start config only), so
  `abstractArr ⟨i,nil⟩ qₚ = [i = δ_init]·[qₚ = init]`;
  the RHS is `pe.probOfR ⟨i,nil⟩ · (lastStateOf ⟨i,nil⟩) qₚ = pe.initState i · i qₚ`, and
  `pe.initState = PMF.pure (δ_init)` so `pe.initState i = [i = δ_init]`, with `i qₚ = [qₚ = init]`
  when
  `i = δ_init` (`lastStateOf ⟨i,nil⟩ = i` via `lastStateOf_nil`).
* **Step** (`D = D₀ · ((l,ω),dq)`, `dq = lastStateOf D`): `Stream'.Seq.exists_split_last`; for each
  `⟨e',h⟩` with `last e' = qₚ`, `LowerReachProb_peel` (`reachAfter_zero_of_de_append`) and swap the
  `c₀`-sum outermost. Only `c₀ = ⟨D₀, e₀, some (l,ω)⟩` contributes (de-append match), with
  `e' = e₀·((l,μ),qₚ)` — reindex the concrete extension by the sampled `μ` (`q = qₚ` forced by
  `last e' = qₚ`); the `LowerStep` weight is
  `tKernel(β,l,ω,last e₀)(μ)·μ qₚ·ω dq·(dq qₚ/(ω.bind id)qₚ)·s.next (D₀·((l,ω),dq)) h`. Sum `μ`
  (`∑' μ, tKernel(…)(μ)·μ qₚ = (tKernel(β,l,ω,last e₀).bind id) qₚ`) and `h` (`∑ s.next = 1`); group
  `e₀` by `last e₀ = qₚ₀` and factor the pending `some (l,ω)` (`lowerReachProb_pending_factor`) to
  `s.next D₀ (some (l,ω)) · abstractArr D₀ qₚ₀`. IH gives
  `abstractArr D₀ qₚ₀ = pe.probOfR D₀ · β qₚ₀`
  (`β = lastStateOf D₀`); then `∑' qₚ₀, β qₚ₀ · (tKernel(β,l,ω,qₚ₀).bind id) qₚ = (ω.bind id) qₚ`
  (`tKernel_bind_avg`). So the whole thing is
  `ω dq·(dq qₚ/(ω.bind id)qₚ)·s.next D₀ (some (l,ω))·pe.probOfR D₀·(ω.bind id)qₚ`. Cancel
  `(dq qₚ/(ω.bind id)qₚ)·(ω.bind id)qₚ = dq qₚ` (`ENNReal.div_mul_cancel`; case `(ω.bind id)qₚ = 0`:
  then `ω dq ≠ 0 ⇒ dq qₚ = 0`, both sides `0`). Reassemble with `probOfR_append_singleton` and
  `pe.rkernel D₀ ((l,ω),dq) = s.next D₀ (some (l,ω)) · ω dq` (`rfl`) into
  `pe.probOfR (D₀·((l,ω),dq)) · dq qₚ`. -/
theorem abstractArr_eq (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (D : ResolvedExec (PMF State) Label) (hterm : D.trans.Terminates) (qₚ : State) :
    abstractArr F s D qₚ
      = (⟨PMF.pure (sys.distF F).init, s⟩ :
          ResolvedProbabilisticExecution (sys.distF F)).probOfR D hterm
        * (lastStateOf D) qₚ := by
  classical
  set pe : ResolvedProbabilisticExecution (sys.distF F) :=
    ⟨PMF.pure (sys.distF F).init, s⟩ with hpe
  suffices H : ∀ n (D : ResolvedExec (PMF State) Label) (hterm : D.trans.Terminates)
      (qₚ : State), (D.trans.toList hterm).length = n →
      abstractArr F s D qₚ = pe.probOfR D hterm * (lastStateOf D) qₚ from H _ D hterm qₚ rfl
  clear qₚ
  intro n
  induction n with
  | zero =>
    intro D hterm qₚ hlen
    -- `D = ⟨i, nil⟩`.
    have htoList : D.trans.toList hterm = [] := List.length_eq_zero_iff.mp hlen
    obtain ⟨i, t⟩ := D
    have h_nil : t = Seq.nil := by
      have hh := Stream'.Seq.ofList_toList t hterm
      rw [htoList, Stream'.Seq.ofList_nil] at hh
      exact hh.symm
    subst h_nil
    rw [pe.probOfR_nil i, lastStateOf_nil i]
    -- `pe.initState = PMF.pure (sys.distF F).init = PMF.pure (PMF.pure sys.init)`.
    have hinit : pe.initState = PMF.pure (PMF.pure sys.init) := rfl
    rw [hinit]
    -- On `⟨i,nil⟩`, only level 0 contributes; the start config forces `i = δ ∧ e = ⟨init,nil⟩`.
    have hcollapse : ∀ (e : ResolvedExec State Label) (h : Option (Label × PMF (PMF State))),
        LowerReachProb F s ⟨⟨i, Seq.nil⟩, e, h⟩
          = LowerReachAfter F s 0 ⟨⟨i, Seq.nil⟩, e, h⟩ := by
      intro e h
      unfold LowerReachProb
      rw [tsum_eq_zero_add' ENNReal.summable]
      have hz : (∑' n, LowerReachAfter F s (n + 1) ⟨⟨i, Seq.nil⟩, e, h⟩) = 0 := by
        refine ENNReal.tsum_eq_zero.mpr fun n => ?_
        exact reachAfter_succ_de_nil F s n i e h
      rw [hz, add_zero]
    unfold abstractArr
    simp_rw [hcollapse, LowerReachAfter_zero]
    -- Evaluate `PMF.pure (PMF.pure sys.init) i` by cases on `i = PMF.pure sys.init`.
    rw [PMF.pure_apply]
    by_cases hi : i = PMF.pure sys.init
    · subst hi
      rw [if_pos rfl, one_mul]
      -- Only `e = ⟨sys.init, nil⟩` contributes; then `∑' h, s.next = 1`, and cond `sys.init = qₚ`.
      rw [tsum_eq_single (⟨sys.init, Seq.nil⟩ : ResolvedExec State Label) ?_]
      · simp_rw [lastStateOf_nil sys.init]
        by_cases hq : sys.init = qₚ
        · simp_rw [if_pos hq, and_self, if_true]
          rw [PMF.tsum_coe, ← hq, PMF.pure_apply, if_pos rfl]
        · simp_rw [if_neg hq]
          rw [tsum_zero, PMF.pure_apply, if_neg (fun h => hq h.symm)]
      · intro e he
        refine (ENNReal.tsum_eq_zero.mpr fun h => ?_)
        have hinner : (if (⟨PMF.pure sys.init, Seq.nil⟩ : ResolvedExec (PMF State) Label)
              = ⟨PMF.pure sys.init, Seq.nil⟩ ∧ e = ⟨sys.init, Seq.nil⟩
            then s.next ⟨PMF.pure sys.init, Seq.nil⟩ h else 0) = 0 := by
          rw [if_neg]
          rintro ⟨-, he'⟩
          exact he he'
        rw [hinner, ite_self]
    · rw [if_neg hi, zero_mul]
      refine (ENNReal.tsum_eq_zero.mpr fun e => ?_)
      refine (ENNReal.tsum_eq_zero.mpr fun h => ?_)
      have hinner : (if (⟨i, Seq.nil⟩ : ResolvedExec (PMF State) Label)
            = ⟨PMF.pure sys.init, Seq.nil⟩ ∧ e = ⟨sys.init, Seq.nil⟩
          then s.next ⟨PMF.pure sys.init, Seq.nil⟩ h else 0) = 0 := by
        rw [if_neg]
        rintro ⟨hii, -⟩
        exact hi (congrArg AlterSeq.init hii)
      rw [hinner, ite_self]
  | succ k ih =>
    intro D hterm qₚ hlen
    -- Split the last abstract transition: `D = D₀ ++ ((l,ω),dq)`, `D₀ = ⟨D.init, prev⟩`.
    have hne : D.trans.toList hterm ≠ [] := by
      intro hnil; rw [hnil, List.length_nil] at hlen; exact Nat.succ_ne_zero k hlen.symm
    obtain ⟨prev, last, hprev, hsplit, hprevlist, -⟩ :=
      Stream'.Seq.exists_split_last D.trans hterm hne
    have happ : (prev.append (Seq.cons last Seq.nil)).Terminates := hsplit ▸ hterm
    have hD_eq : D = ⟨D.init, prev.append (Seq.cons last Seq.nil)⟩ := by
      obtain ⟨di, dt⟩ := D; exact congrArg (AlterSeq.mk di) hsplit
    have hlen_prev : (prev.toList hprev).length = k := by
      have h1 : (prev.toList hprev).length = (D.trans.toList hterm).length - 1 := by
        rw [hprevlist, List.length_dropLast]
      omega
    obtain ⟨⟨l, ω⟩, dq⟩ := last
    set D₀ : ResolvedExec (PMF State) Label := ⟨D.init, prev⟩ with hD₀
    have hDlast : lastStateOf D = dq := by
      rw [hD_eq]
      exact lastStateOf_append_singleton D₀ hprev (l, ω) dq
    rw [hDlast]
    -- `pe.probOfR D = pe.probOfR D₀ * (s.next D₀ (some (l,ω)) * ω dq)`.
    have hprobD : pe.probOfR D hterm
        = pe.probOfR D₀ hprev * (s.next D₀ (some (l, ω)) * ω dq) := by
      rw [pe.probOfR_congr D ⟨D.init, prev.append (Seq.cons ((l, ω), dq) Seq.nil)⟩ hD_eq hterm happ]
      exact pe.probOfR_append_singleton D.init prev hprev ((l, ω), dq) happ
    rw [hprobD]
    -- Goal: `abstractArr D qₚ = pe.probOfR D₀ hprev * (s.next D₀ (some (l,ω)) * ω dq) * dq qₚ`.
    -- Peel each `LowerReachProb ⟨D,e,h⟩` (`D` is a nonempty de-append), swap `c₀` outermost.
    have hAbstract1 : abstractArr F s D qₚ
        = ∑' c₀, LowerReachProb F s c₀ *
            (∑' (e : ResolvedExec State Label),
              if lastStateOf e = qₚ then
                (∑' h : Option (Label × PMF (PMF State)), LowerStep F s c₀ ⟨D, e, h⟩) else 0) := by
      unfold abstractArr
      -- Peel: `LowerReachProb ⟨D,e,h⟩ = ∑' c₀, LowerReachProb c₀ * LowerStep c₀ ⟨D,e,h⟩`.
      have hpeel : ∀ (e : ResolvedExec State Label) (h : Option (Label × PMF (PMF State))),
          LowerReachProb F s ⟨D, e, h⟩
            = ∑' c₀, LowerReachProb F s c₀ * LowerStep F s c₀ ⟨D, e, h⟩ := by
        intro e h
        refine LowerReachProb_peel F s ⟨D, e, h⟩ ?_
        rw [hD_eq]
        exact reachAfter_zero_of_de_append F s D.init prev ((l, ω), dq) e h
      simp_rw [hpeel]
      -- Push the `if` through the `∑' c₀`, i.e.
      -- `(if p then ∑ c₀, f c₀ else 0) = ∑ c₀, if p then f c₀ else 0`.
      have hpush : ∀ (e : ResolvedExec State Label) (h : Option (Label × PMF (PMF State))),
          (if lastStateOf e = qₚ then
              (∑' c₀, LowerReachProb F s c₀ * LowerStep F s c₀ ⟨D, e, h⟩) else 0)
            = ∑' c₀, (if lastStateOf e = qₚ then
                LowerReachProb F s c₀ * LowerStep F s c₀ ⟨D, e, h⟩ else 0) := by
        intro e h
        by_cases hq : lastStateOf e = qₚ
        · simp_rw [if_pos hq]
        · simp_rw [if_neg hq, tsum_zero]
      simp_rw [hpush]
      -- Goal LHS `∑' e h c₀ → ∑' e c₀ h` (swap inner two under `e`).
      have hswap : ∀ e : ResolvedExec State Label,
          (∑' (h : Option (Label × PMF (PMF State))) (c₀ : LowerConfig sys),
              if lastStateOf e = qₚ then LowerReachProb F s c₀ * LowerStep F s c₀ ⟨D, e, h⟩ else 0)
            = ∑' (c₀ : LowerConfig sys) (h : Option (Label × PMF (PMF State))),
              if lastStateOf e = qₚ then LowerReachProb F s c₀ * LowerStep F s c₀ ⟨D, e, h⟩
                else 0 :=
        fun e => ENNReal.tsum_comm
      simp_rw [hswap]
      -- `∑' e c₀ h → ∑' c₀ e h`.
      rw [ENNReal.tsum_comm (f := fun (e : ResolvedExec State Label) (c₀ : LowerConfig sys) =>
        ∑' h : Option (Label × PMF (PMF State)),
          if lastStateOf e = qₚ then LowerReachProb F s c₀ * LowerStep F s c₀ ⟨D, e, h⟩ else 0)]
      -- `∑' c₀ e h, ...`; regroup on the RHS.
      refine tsum_congr fun c₀ => ?_
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun e => ?_
      by_cases hq : lastStateOf e = qₚ
      · simp_rw [if_pos hq]
        rw [ENNReal.tsum_mul_left]
      · simp_rw [if_neg hq, tsum_zero, mul_zero]
    rw [hAbstract1]
    -- Abbreviations.
    set β : PMF State := lastStateOf D₀ with hβ
    -- Inner sum over `e` for a *reachable pending* `c₀ = ⟨D₀, e₀, some (l,ω)⟩`.
    -- For a general `c₀`, the inner sum is
    -- `∑' μ, tKernel(β,l,ω,last c₀.e)(μ)·μ qₚ·ω dq·(dq qₚ/(ω.bind id)qₚ)`
    -- when `c₀.de = D₀` and `c₀.h = some (l,ω)`, else `0` on reachable `c₀`.
    have hInnerReach : ∀ c₀ : LowerConfig sys, LowerReachProb F s c₀ ≠ 0 →
        (∑' (e : ResolvedExec State Label),
            if lastStateOf e = qₚ then
              (∑' h : Option (Label × PMF (PMF State)), LowerStep F s c₀ ⟨D, e, h⟩) else 0)
          = (if c₀.de = D₀ ∧ c₀.h = some (l, ω) then
              (tKernel F β l ω (lastStateOf c₀.e)).bind id qₚ * ω dq
                * (dq qₚ / (ω.bind id) qₚ)
             else 0) := by
      intro c₀ hrp
      have hcoup : Coupled c₀ := by
        obtain ⟨N, hN⟩ := tsum_ne_zero_exists hrp
        exact reachAfter_coupled F s N c₀ hN
      have hce_term : c₀.e.trans.Terminates := hcoup.2.1
      -- The inner `∑' h, LowerStep c₀ ⟨D,e,h⟩` collapses the pending draw:
      -- `= if cond then P e else 0`.
      -- We compute it by unfolding `LowerStep` and summing `s.next D h = 1`.
      have hsum_h : ∀ e : ResolvedExec State Label,
          (∑' h : Option (Label × PMF (PMF State)), LowerStep F s c₀ ⟨D, e, h⟩)
            = (match c₀.h with
               | none => 0
               | some (l₀, ω₀) =>
                 if D.init = c₀.de.init ∧ e.init = c₀.e.init ∧
                    D.trans = c₀.de.trans.append (Seq.cons ((l₀, ω₀), lastStateOf D) Seq.nil) ∧
                    e.trans = c₀.e.trans.append (Seq.cons ((l₀, lastMuOf e), lastStateOf e) Seq.nil)
                 then (tKernel F (lastStateOf c₀.de) l₀ ω₀ (lastStateOf c₀.e)) (lastMuOf e)
                       * (lastMuOf e) (lastStateOf e) * ω₀ (lastStateOf D)
                       * ((lastStateOf D) (lastStateOf e) / (ω₀.bind id) (lastStateOf e))
                 else 0) := by
        intro e
        cases hh : c₀.h with
        | none =>
          simp only
          refine ENNReal.tsum_eq_zero.mpr fun h => ?_
          unfold LowerStep; rw [hh]
        | some lω =>
          obtain ⟨l₀, ω₀⟩ := lω
          simp only
          have hval : ∀ h : Option (Label × PMF (PMF State)),
              LowerStep F s c₀ ⟨D, e, h⟩
                = (if D.init = c₀.de.init ∧ e.init = c₀.e.init ∧
                     D.trans = c₀.de.trans.append (Seq.cons ((l₀, ω₀), lastStateOf D) Seq.nil) ∧
                     e.trans =
                       c₀.e.trans.append (Seq.cons ((l₀, lastMuOf e), lastStateOf e) Seq.nil)
                   then (tKernel F (lastStateOf c₀.de) l₀ ω₀ (lastStateOf c₀.e)) (lastMuOf e)
                         * (lastMuOf e) (lastStateOf e) * ω₀ (lastStateOf D)
                         * ((lastStateOf D) (lastStateOf e) / (ω₀.bind id) (lastStateOf e))
                         * s.next D h
                   else 0) := by
            intro h
            unfold LowerStep; rw [hh]
          simp_rw [hval]
          by_cases hif : D.init = c₀.de.init ∧ e.init = c₀.e.init ∧
              D.trans = c₀.de.trans.append (Seq.cons ((l₀, ω₀), lastStateOf D) Seq.nil) ∧
              e.trans = c₀.e.trans.append (Seq.cons ((l₀, lastMuOf e), lastStateOf e) Seq.nil)
          · simp_rw [if_pos hif]
            rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
          · simp_rw [if_neg hif, tsum_zero]
      simp_rw [hsum_h]
      cases hh : c₀.h with
      | none =>
        simp only []
        rw [if_neg (by rintro ⟨-, hcon⟩; exact absurd hcon (by simp))]
        simp only [ite_self, tsum_zero]
      | some lω =>
        obtain ⟨l₀, ω₀⟩ := lω
        simp only []
        by_cases hmatch : c₀.de = D₀ ∧ l₀ = l ∧ ω₀ = ω
        · obtain ⟨hcde, hl0, hω0⟩ := hmatch
          subst hl0; subst hω0
          rw [if_pos ⟨hcde, rfl⟩]
          -- The de-conjunct of the inner condition is always true; reindex `e` by `(μ, q)`.
          have hde_init : D.init = c₀.de.init := by rw [hcde]
          have hde_tr :
              D.trans = c₀.de.trans.append (Seq.cons ((l₀, ω₀), lastStateOf D) Seq.nil) := by
            rw [hcde, hDlast]; exact hsplit
          -- Reindex `e ↦ ⟨c₀.e.init, c₀.e.trans ++ ((l₀,μ),q)⟩`.
          set Ec : PMF State → State → ResolvedExec State Label :=
            fun μ q => ⟨c₀.e.init, c₀.e.trans.append (Seq.cons ((l₀, μ), q) Seq.nil)⟩ with hEc
          have hEclast : ∀ μ q, lastStateOf (Ec μ q) = q := fun μ q =>
            lastStateOf_append_singleton ⟨c₀.e.init, c₀.e.trans⟩ hce_term (l₀, μ) q
          have hEcmu : ∀ μ q, lastMuOf (Ec μ q) = μ := fun μ q =>
            lastMuOf_append_singleton ⟨c₀.e.init, c₀.e.trans⟩ hce_term l₀ μ q
          -- Rewrite the inner summand: for each `e`, the term is `Val (lastMuOf e) (lastStateOf e)`
          -- exactly when `e = Ec (lastMuOf e) (lastStateOf e)` (i.e. `e` is a one-step extension).
          set Val : PMF State → State → ENNReal := fun μ q =>
            (if q = qₚ then
              (tKernel F (lastStateOf c₀.de) l₀ ω₀ (lastStateOf c₀.e)) μ * μ q * ω₀ dq
                * (dq q / (ω₀.bind id) q)
             else 0) with hVal
          -- LHS is a reindex of `∑' μ q, Val μ q` onto the extensions of `c₀.e`.
          have hLHS : (∑' e : ResolvedExec State Label,
                if lastStateOf e = qₚ then
                  (if D.init = c₀.de.init ∧ e.init = c₀.e.init ∧
                      D.trans = c₀.de.trans.append (Seq.cons ((l₀, ω₀), lastStateOf D) Seq.nil) ∧
                      e.trans =
                        c₀.e.trans.append (Seq.cons ((l₀, lastMuOf e), lastStateOf e) Seq.nil)
                    then (tKernel F (lastStateOf c₀.de) l₀ ω₀ (lastStateOf c₀.e)) (lastMuOf e)
                          * (lastMuOf e) (lastStateOf e) * ω₀ (lastStateOf D)
                          * ((lastStateOf D) (lastStateOf e) / (ω₀.bind id) (lastStateOf e))
                    else 0)
                else 0)
              = ∑' (μ : PMF State) (q : State), Val μ q := by
            rw [← ENNReal.tsum_prod' (f := fun p : PMF State × State => Val p.1 p.2)]
            refine tsum_eq_tsum_of_ne_zero_bij
              (i := fun p : Function.support (fun p : PMF State × State => Val p.1 p.2) =>
                Ec p.1.1 p.1.2) ?inj ?supp ?val
            · rintro ⟨⟨μ₁, q₁⟩, hp₁⟩ ⟨⟨μ₂, q₂⟩, hp₂⟩ hab
              have hq := congrArg lastStateOf hab
              have hμ := congrArg lastMuOf hab
              rw [hEclast, hEclast] at hq
              rw [hEcmu, hEcmu] at hμ
              exact Subtype.ext (Prod.ext hμ hq)
            · intro e he
              rw [Function.mem_support] at he
              -- Nonzero ⇒ inner condition held ⇒ `e = Ec (lastMuOf e) (lastStateOf e)`.
              have hcond : lastStateOf e = qₚ ∧
                  (e.init = c₀.e.init ∧
                    e.trans =
                      c₀.e.trans.append (Seq.cons ((l₀, lastMuOf e), lastStateOf e) Seq.nil)) := by
                by_contra hcon
                apply he
                by_cases hq : lastStateOf e = qₚ
                · rw [if_pos hq] at *
                  by_cases hin : e.init = c₀.e.init ∧
                      e.trans =
                        c₀.e.trans.append (Seq.cons ((l₀, lastMuOf e), lastStateOf e) Seq.nil)
                  · exact absurd ⟨hq, hin⟩ hcon
                  · rw [if_neg (fun hc => hin ⟨hc.2.1, hc.2.2.2⟩)]
                · rw [if_neg hq]
              obtain ⟨hq, hein, hetr⟩ := hcond
              have heEc : e = Ec (lastMuOf e) (lastStateOf e) := by
                rw [hEc]; exact alterSeq_ext hein hetr
              refine ⟨⟨(lastMuOf e, lastStateOf e), ?_⟩, ?_⟩
              · rw [Function.mem_support, hVal]
                simp only
                rw [if_pos hq, ← hDlast]
                rw [if_pos hq] at he
                rw [if_pos ⟨hde_init, hein, hde_tr, hetr⟩] at he
                exact he
              · exact heEc.symm
            · rintro ⟨⟨μ, q⟩, hp⟩
              -- `f (Ec μ q) = Val μ q`.
              change (if lastStateOf (Ec μ q) = qₚ then
                  (if D.init = c₀.de.init ∧ (Ec μ q).init = c₀.e.init ∧
                      D.trans = c₀.de.trans.append (Seq.cons ((l₀, ω₀), lastStateOf D) Seq.nil) ∧
                      (Ec μ q).trans =
                        c₀.e.trans.append
                          (Seq.cons ((l₀, lastMuOf (Ec μ q)), lastStateOf (Ec μ q)) Seq.nil)
                    then (tKernel F (lastStateOf c₀.de) l₀ ω₀ (lastStateOf c₀.e))
                          (lastMuOf (Ec μ q))
                          * (lastMuOf (Ec μ q)) (lastStateOf (Ec μ q)) * ω₀ (lastStateOf D)
                          * ((lastStateOf D) (lastStateOf (Ec μ q))
                              / (ω₀.bind id) (lastStateOf (Ec μ q)))
                    else 0)
                  else 0) = Val μ q
              rw [hEclast, hEcmu, hVal]
              simp only
              by_cases hq : q = qₚ
              · rw [if_pos hq, if_pos hq, if_pos ⟨hde_init, rfl, hde_tr, rfl⟩, hDlast]
              · rw [if_neg hq, if_neg hq]
          rw [hLHS, hVal]
          simp only []
          -- Collapse `q = qₚ` and sum over `μ`.
          have hqcollapse : (∑' (μ : PMF State) (q : State),
                if q = qₚ then
                  (tKernel F (lastStateOf c₀.de) l₀ ω₀ (lastStateOf c₀.e)) μ * μ q * ω₀ dq
                    * (dq q / (ω₀.bind id) q)
                else 0)
              = ∑' μ : PMF State,
                (tKernel F (lastStateOf c₀.de) l₀ ω₀ (lastStateOf c₀.e)) μ * μ qₚ * ω₀ dq
                  * (dq qₚ / (ω₀.bind id) qₚ) := by
            refine tsum_congr fun μ => ?_
            rw [tsum_eq_single qₚ ?_, if_pos rfl]
            · intro q hq; rw [if_neg hq]
          rw [hqcollapse]
          -- `∑' μ, tKernel(...)(μ) * μ qₚ = (tKernel(...).bind id) qₚ`.
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right,
            show (∑' μ : PMF State,
                (tKernel F (lastStateOf c₀.de) l₀ ω₀ (lastStateOf c₀.e)) μ * μ qₚ)
              = (tKernel F (lastStateOf c₀.de) l₀ ω₀ (lastStateOf c₀.e)).bind id qₚ by
              simp only [PMF.bind_apply, id_eq]]
          rw [hβ, hcde]
        · rw [if_neg (by
            rintro ⟨hcde, hcon⟩
            rw [Option.some.injEq, Prod.mk.injEq] at hcon
            exact hmatch ⟨hcde, hcon.1, hcon.2⟩)]
          -- Every inner `if` fails (append-injectivity forces the match); LHS = 0.
          refine ENNReal.tsum_eq_zero.mpr fun e => ?_
          rw [ite_eq_right_iff.mpr fun _ => ?_]
          rw [if_neg]
          rintro ⟨hdinit, hee, hdtr, hetr⟩
          apply hmatch
          -- `D.trans = c₀.de.trans ++ ((l₀,ω₀),last D)` and `hsplit` ⇒ `c₀.de.trans = prev`,
          -- `(l₀,ω₀)=(l,ω)`.
          have hDterm2 : c₀.de.trans.Terminates := hcoup.1
          have happ2 : D.trans = prev.append (Seq.cons ((l, ω), dq) Seq.nil) := hsplit
          rw [hdtr, hDlast] at happ2
          have hlast := Stream'.Seq.append_singleton_inj_right c₀.de.trans prev hDterm2 hprev
            _ _ happ2
          have htr := Stream'.Seq.append_singleton_inj_left c₀.de.trans prev hDterm2 hprev
            _ _ happ2
          rw [Prod.mk.injEq, Prod.mk.injEq] at hlast
          obtain ⟨⟨hll, hωω⟩, -⟩ := hlast
          exact ⟨alterSeq_ext hdinit.symm htr, hll, hωω⟩
    -- Rewrite each summand (handling `LowerReachProb c₀ = 0` separately).
    have hSummand : ∀ c₀ : LowerConfig sys,
        LowerReachProb F s c₀ *
          (∑' (e : ResolvedExec State Label),
            if lastStateOf e = qₚ then
              (∑' h : Option (Label × PMF (PMF State)), LowerStep F s c₀ ⟨D, e, h⟩) else 0)
          = LowerReachProb F s c₀ *
              (if c₀.de = D₀ ∧ c₀.h = some (l, ω) then
                (tKernel F β l ω (lastStateOf c₀.e)).bind id qₚ * ω dq
                  * (dq qₚ / (ω.bind id) qₚ)
               else 0) := by
      intro c₀
      by_cases hrp : LowerReachProb F s c₀ = 0
      · rw [hrp, zero_mul, zero_mul]
      · rw [hInnerReach c₀ hrp]
    simp_rw [hSummand]
    -- Reindex the `c₀`-sum onto `e₀` via `e₀ ↦ ⟨D₀, e₀, some (l,ω)⟩` (only these are nonzero).
    have hReindex : (∑' c₀ : LowerConfig sys, LowerReachProb F s c₀ *
          (if c₀.de = D₀ ∧ c₀.h = some (l, ω) then
            (tKernel F β l ω (lastStateOf c₀.e)).bind id qₚ * ω dq
              * (dq qₚ / (ω.bind id) qₚ)
           else 0))
        = ∑' e₀ : ResolvedExec State Label, LowerReachProb F s ⟨D₀, e₀, some (l, ω)⟩ *
            ((tKernel F β l ω (lastStateOf e₀)).bind id qₚ * ω dq * (dq qₚ / (ω.bind id) qₚ)) := by
      refine tsum_eq_tsum_of_ne_zero_bij
        (i := fun e₀ : Function.support (fun e₀ : ResolvedExec State Label =>
            LowerReachProb F s ⟨D₀, e₀, some (l, ω)⟩ *
              ((tKernel F β l ω (lastStateOf e₀)).bind id qₚ * ω dq
                * (dq qₚ / (ω.bind id) qₚ))) =>
          (⟨D₀, e₀.1, some (l, ω)⟩ : LowerConfig sys)) ?rinj ?rsupp ?rval
      · rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ hab
        simp only [LowerConfig.mk.injEq] at hab
        exact Subtype.ext hab.2.1
      · intro c₀ hc₀
        rw [Function.mem_support] at hc₀
        -- Nonzero ⇒ the `if` fired ⇒ `c₀ = ⟨D₀, c₀.e, some (l,ω)⟩`.
        have hif : c₀.de = D₀ ∧ c₀.h = some (l, ω) := by
          by_contra hcon
          rw [if_neg hcon, mul_zero] at hc₀
          exact hc₀ rfl
        refine ⟨⟨c₀.e, ?_⟩, ?_⟩
        · rw [Function.mem_support]
          rw [if_pos hif] at hc₀
          rw [← hif.1, ← hif.2]
          exact hc₀
        · obtain ⟨cd, ce, ch⟩ := c₀
          simp only at hif ⊢
          rw [hif.1, hif.2]
      · rintro ⟨e₀, he₀⟩
        rw [if_pos ⟨rfl, rfl⟩]
    rw [hReindex]
    by_cases hstep : (sys.distF F).step β l ω
    · -- Factor `s.next D₀ (some (l,ω))` out of each `LowerReachProb`, group `e₀` by its endpoint.
      have hfac : ∀ e₀ : ResolvedExec State Label,
          LowerReachProb F s ⟨D₀, e₀, some (l, ω)⟩ *
            ((tKernel F β l ω (lastStateOf e₀)).bind id qₚ * ω dq * (dq qₚ / (ω.bind id) qₚ))
          = (∑' h' : Option (Label × PMF (PMF State)), LowerReachProb F s ⟨D₀, e₀, h'⟩) *
              (s.next D₀ (some (l, ω)) * ω dq * (dq qₚ / (ω.bind id) qₚ)
                * (tKernel F β l ω (lastStateOf e₀)).bind id qₚ) := by
        intro e₀
        rw [lowerReachProb_pending_factor F s D₀ e₀ (some (l, ω))]
        ring
      simp_rw [hfac]
      -- Group `e₀` by `lastStateOf e₀ = qₚ₀` using `abstractArr D₀` and the IH.
      set C : State → ENNReal := fun qₚ₀ =>
        s.next D₀ (some (l, ω)) * ω dq * (dq qₚ / (ω.bind id) qₚ)
          * (tKernel F β l ω qₚ₀).bind id qₚ with hC
      have hgroup : (∑' e₀ : ResolvedExec State Label,
            (∑' h' : Option (Label × PMF (PMF State)), LowerReachProb F s ⟨D₀, e₀, h'⟩)
              * C (lastStateOf e₀))
          = ∑' qₚ₀ : State, abstractArr F s D₀ qₚ₀ * C qₚ₀ := by
        -- Expand `abstractArr D₀ qₚ₀` on the RHS and collapse the `qₚ₀`-indicator.
        symm
        have hexp : ∀ qₚ₀ : State, abstractArr F s D₀ qₚ₀ * C qₚ₀
            = ∑' (e : ResolvedExec State Label) (h : Option (Label × PMF (PMF State))),
              (if lastStateOf e = qₚ₀ then LowerReachProb F s ⟨D₀, e, h⟩ else 0) * C qₚ₀ := by
          intro qₚ₀
          rw [abstractArr, ← ENNReal.tsum_mul_right]
          refine tsum_congr fun e => ?_
          rw [← ENNReal.tsum_mul_right]
        simp_rw [hexp]
        -- `∑' qₚ₀ e h, … → ∑' e h qₚ₀, …`.
        rw [ENNReal.tsum_comm (f := fun (qₚ₀ : State) (e : ResolvedExec State Label) =>
          ∑' h : Option (Label × PMF (PMF State)),
            (if lastStateOf e = qₚ₀ then LowerReachProb F s ⟨D₀, e, h⟩ else 0) * C qₚ₀)]
        refine tsum_congr fun e => ?_
        rw [ENNReal.tsum_comm (f := fun (qₚ₀ : State) (h : Option (Label × PMF (PMF State))) =>
          (if lastStateOf e = qₚ₀ then LowerReachProb F s ⟨D₀, e, h⟩ else 0) * C qₚ₀)]
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun h => ?_
        simp_rw [ite_mul, zero_mul, eq_comm (a := lastStateOf e)]
        rw [tsum_ite_eq (lastStateOf e) (fun qₚ₀ => LowerReachProb F s ⟨D₀, e, h⟩ * C qₚ₀)]
      rw [hgroup]
      -- Apply the IH to `abstractArr D₀ qₚ₀`, pull constants, then `tKernel_bind_avg`.
      simp_rw [fun qₚ₀ => ih D₀ hprev qₚ₀ hlen_prev]
      simp_rw [hC]
      -- `pe.probOfR D₀ * β qₚ₀ * (s.next... * ω dq * ... * (tKernel β l ω qₚ₀).bind id qₚ)`.
      rw [show (∑' qₚ₀ : State,
            pe.probOfR D₀ hprev * β qₚ₀ *
              (s.next D₀ (some (l, ω)) * ω dq * (dq qₚ / (ω.bind id) qₚ)
                * (tKernel F β l ω qₚ₀).bind id qₚ))
          = pe.probOfR D₀ hprev * (s.next D₀ (some (l, ω)) * ω dq * (dq qₚ / (ω.bind id) qₚ))
              * ∑' qₚ₀ : State, β qₚ₀ * (tKernel F β l ω qₚ₀).bind id qₚ from ?_]
      · rw [tKernel_bind_avg F β l ω hstep qₚ]
        -- Cancel `ω dq · (dq qₚ / (ω.bind id) qₚ) · (ω.bind id) qₚ = ω dq · dq qₚ`.
        have hcancel : ω dq * ((dq qₚ / (ω.bind id) qₚ) * (ω.bind id) qₚ) = ω dq * dq qₚ := by
          by_cases hb0 : (ω.bind id) qₚ = 0
          · rw [hb0, mul_zero, mul_zero]
            -- `ω dq = 0` or `dq qₚ = 0`: if `ω dq ≠ 0` then `dq qₚ ≤ (ω.bind id) qₚ = 0`.
            by_cases hωdq : ω dq = 0
            · rw [hωdq, zero_mul]
            · -- `(ω.bind id) qₚ = ∑' ν, ω ν * ν qₚ = 0` ⇒ `ω dq * dq qₚ = 0` ⇒ `dq qₚ = 0`.
              have hbindeq : (ω.bind id) qₚ = ∑' ν : PMF State, ω ν * ν qₚ := by
                simp only [PMF.bind_apply, id_eq]
              rw [hbindeq] at hb0
              have hterm0 : ω dq * dq qₚ = 0 :=
                le_antisymm (hb0 ▸ ENNReal.le_tsum dq) bot_le
              have hdq0 : dq qₚ = 0 := by
                rcases mul_eq_zero.mp hterm0 with h | h
                · exact absurd h hωdq
                · exact h
              rw [hdq0, mul_zero]
          · rw [div_eq_mul_inv, mul_assoc,
              ENNReal.inv_mul_cancel hb0 (PMF.apply_ne_top (ω.bind id) qₚ), mul_one]
        rw [mul_assoc (pe.probOfR D₀ hprev),
          show (s.next D₀ (some (l, ω)) * ω dq * (dq qₚ / (ω.bind id) qₚ)) * (ω.bind id) qₚ
            = s.next D₀ (some (l, ω))
                * (ω dq * ((dq qₚ / (ω.bind id) qₚ) * (ω.bind id) qₚ)) by ring,
          hcancel]
        ring
      · rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun qₚ₀ => ?_
        ring
    · -- `¬ step`: every pending witness is unreachable ⇒ LHS = 0;
      --   `s.next D₀ (some (l,ω)) = 0` ⇒ RHS = 0.
      have hnext0 : s.next D₀ (some (l, ω)) = 0 := by
        by_contra hnz
        have hmem : some (l, ω) ∈ (s.next D₀).support := (PMF.mem_support_iff _ _).mpr hnz
        have hde_state : D₀.stateAt (Nat.find hprev) = some (lastStateOf D₀) := by
          have := AlterSeq.stateAt_find_eq_endState D₀ hprev
          rw [this]; congr 1; unfold lastStateOf; rw [dif_pos hprev]
        have hvalid := s.valid D₀ (Nat.find hprev) (lastStateOf D₀) (Nat.find_spec hprev)
          hde_state l ω hmem
        exact hstep hvalid
      have hLHS0 : (∑' e₀ : ResolvedExec State Label, LowerReachProb F s ⟨D₀, e₀, some (l, ω)⟩ *
            ((tKernel F β l ω (lastStateOf e₀)).bind id qₚ * ω dq * (dq qₚ / (ω.bind id) qₚ)))
              = 0 := by
        refine ENNReal.tsum_eq_zero.mpr fun e₀ => ?_
        by_cases hrp : LowerReachProb F s ⟨D₀, e₀, some (l, ω)⟩ = 0
        · rw [hrp, zero_mul]
        · exfalso
          have := (reachProb_pending_step F s ⟨D₀, e₀, some (l, ω)⟩ hrp l ω rfl).2
          exact hstep this
      rw [hLHS0, hnext0]
      ring

/-- **Core (abstract): path-measure = de-marginal arrival mass.** Sum `abstractArr_eq` over the
concrete endpoint `qₚ`: `∑' qₚ, pe.probOfR D · (lastStateOf D) qₚ = pe.probOfR D` (`lastStateOf D`
is
a `PMF`, `PMF.tsum_coe`, `ENNReal.tsum_mul_left`), while `∑' qₚ, abstractArr D qₚ =
∑' e h, LowerReachProb ⟨D,e,h⟩` (swap the `qₚ`-sum inside; `if last e = qₚ` selects `qₚ = last e`,
`tsum_ite_eq`). -/
theorem lowerMde_eq_probOfR (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (D : ResolvedExec (PMF State) Label) (hterm : D.trans.Terminates) :
    (∑' (e : ResolvedExec State Label) (h : Option (Label × PMF (PMF State))),
        LowerReachProb F s ⟨D, e, h⟩)
      = (⟨PMF.pure (sys.distF F).init, s⟩ :
          ResolvedProbabilisticExecution (sys.distF F)).probOfR D hterm := by
  classical
  set pe : ResolvedProbabilisticExecution (sys.distF F) :=
    ⟨PMF.pure (sys.distF F).init, s⟩ with hpe
  -- Sum `abstractArr_eq` over the concrete endpoint `qₚ`.
  have hRHS : (∑' qₚ : State, abstractArr F s D qₚ)
      = pe.probOfR D hterm := by
    simp_rw [abstractArr_eq F s D hterm]
    rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  rw [← hRHS]
  -- LHS: `∑' qₚ, abstractArr D qₚ = ∑' e h, LowerReachProb ⟨D,e,h⟩`.
  unfold abstractArr
  -- Move the `qₚ`-sum innermost, then collapse the indicator (`tsum_ite_eq`).
  rw [ENNReal.tsum_comm (α := State)]
  refine tsum_congr fun e => ?_
  rw [ENNReal.tsum_comm (α := State)]
  refine tsum_congr fun h => ?_
  simp_rw [eq_comm (a := lastStateOf e)]
  rw [tsum_ite_eq (lastStateOf e) (fun _ => LowerReachProb F s ⟨D, e, h⟩)]

/-- **Equation (abstract).** The probability that `s` produces trace `tr` equals the reach-mass of
configs whose abstract run `de` is a tight execution with trace `tr`. Proof: mirror
`traceProbR_eq_reachE` — `unfold traceProbR`, rewrite each `pe.probOfR D` by `lowerMde_eq_probOfR`
(so `pe.probOfR D = ∑' e h, LowerReachProb ⟨D,e,h⟩`), flatten `∑' D (e,h)` to a product and reindex
`(D, e, h) ↦ ⟨D, e, h⟩` onto `{c // (distF).trace c.de.toExec = tr ∧ (distF).IsTight c.de.toExec}`
(`IsTight ⇒ Terminates` via `terminates_of_isTight`, so the subtypes coincide). -/
theorem traceProbR_eq_reachDe (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (tr : Seq Label) :
    (⟨PMF.pure (sys.distF F).init, s⟩ :
        ResolvedProbabilisticExecution (sys.distF F)).traceProbR tr
      = ∑' c : {c : LowerConfig sys //
          (sys.distF F).trace c.de.toExec = tr ∧ (sys.distF F).IsTight c.de.toExec},
        LowerReachProb F s c.1 := by
  classical
  unfold ResolvedProbabilisticExecution.traceProbR
  -- Rewrite each resolved path-measure as the de-marginal arrival-mass (`abstract Core`).
  have hrw : ∀ D : {D : ResolvedExec (PMF State) Label //
      D.trans.Terminates ∧ (sys.distF F).trace D.toExec = tr ∧ (sys.distF F).IsTight D.toExec},
      (⟨PMF.pure (sys.distF F).init, s⟩ :
        ResolvedProbabilisticExecution (sys.distF F)).probOfR D.1 D.2.1
        = ∑' (e : ResolvedExec State Label) (h : Option (Label × PMF (PMF State))),
          LowerReachProb F s ⟨D.1, e, h⟩ := by
    intro D
    rw [lowerMde_eq_probOfR F s D.1 D.2.1]
  simp_rw [hrw]
  -- Flatten `∑' D, ∑' e h` to a product, then reindex `(D, e, h) ↦ ⟨D, e, h⟩` onto the configs
  -- whose abstract run is tight with trace `tr` (`IsTight ⇒ Terminates`, so the subtypes coincide).
  rw [show (∑' (D : {D : ResolvedExec (PMF State) Label //
        D.trans.Terminates ∧ (sys.distF F).trace D.toExec = tr ∧ (sys.distF F).IsTight D.toExec})
        (e : ResolvedExec State Label) (h : Option (Label × PMF (PMF State))),
        LowerReachProb F s ⟨D.1, e, h⟩)
      = ∑' (p : {D : ResolvedExec (PMF State) Label //
          D.trans.Terminates ∧ (sys.distF F).trace D.toExec = tr ∧ (sys.distF F).IsTight D.toExec} ×
          ResolvedExec State Label × Option (Label × PMF (PMF State))),
        LowerReachProb F s ⟨p.1.1, p.2.1, p.2.2⟩ by
    rw [ENNReal.tsum_prod']
    refine tsum_congr fun D => ?_
    rw [ENNReal.tsum_prod']]
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun c : Function.support (fun c : {c : LowerConfig sys //
        (sys.distF F).trace c.de.toExec = tr ∧ (sys.distF F).IsTight c.de.toExec} =>
      LowerReachProb F s c.1) =>
      (⟨⟨c.1.1.de, terminates_of_isTight c.1.2.2, c.1.2.1, c.1.2.2⟩,
        c.1.1.e, c.1.1.h⟩ : {D : ResolvedExec (PMF State) Label //
          D.trans.Terminates ∧ (sys.distF F).trace D.toExec = tr ∧ (sys.distF F).IsTight D.toExec} ×
        ResolvedExec State Label × Option (Label × PMF (PMF State)))) ?inj ?supp ?val
  · rintro ⟨⟨c₁, hc₁⟩, hne₁⟩ ⟨⟨c₂, hc₂⟩, hne₂⟩ hab
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hab
    obtain ⟨hde, he, hh⟩ := hab
    refine Subtype.ext (Subtype.ext ?_)
    obtain ⟨d1, e1, h1⟩ := c₁
    obtain ⟨d2, e2, h2⟩ := c₂
    simp only at hde he hh
    subst hde; subst he; subst hh; rfl
  · intro p hp
    rw [Function.mem_support] at hp
    refine ⟨⟨⟨⟨p.1.1, p.2.1, p.2.2⟩, p.1.2.2.1, p.1.2.2.2⟩, hp⟩, ?_⟩
    obtain ⟨D, e, h⟩ := p
    obtain ⟨DD, hD1, hD2, hD3⟩ := D
    rfl
  · rintro ⟨⟨c, hc⟩, hne⟩
    rfl

/-- **Equation (concrete).** The probability that `lowerSched F s` produces trace `tr` equals the
reach-mass of configs whose concrete run `e` is a tight execution with trace `tr`. -/
theorem traceProbR_eq_reachE (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (tr : Seq Label) :
    (⟨PMF.pure sys.init, lowerSched F s⟩ : ResolvedProbabilisticExecution sys).traceProbR tr
      = ∑' c : {c : LowerConfig sys // sys.trace c.e.toExec = tr ∧ sys.IsTight c.e.toExec},
        LowerReachProb F s c.1 := by
  classical
  unfold ResolvedProbabilisticExecution.traceProbR
  -- Rewrite each resolved path-measure as the chain's arrival-mass (`Core`).
  have hrw : ∀ r : {r : ResolvedExec State Label //
      r.trans.Terminates ∧ sys.trace r.toExec = tr ∧ sys.IsTight r.toExec},
      (⟨PMF.pure sys.init, lowerSched F s⟩ :
        ResolvedProbabilisticExecution sys).probOfR r.1 r.2.1
        = ∑' (de : ResolvedExec (PMF State) Label) (h : Option (Label × PMF (PMF State))),
          LowerReachProb F s ⟨de, r.1, h⟩ := by
    intro r
    rw [probOfR_eq_lowerMe F s r.1 r.2.1]; rfl
  simp_rw [hrw]
  -- Flatten `∑' r, ∑' de h` to a product, then reindex `(r, de, h) ↦ ⟨de, r, h⟩` onto the configs
  -- whose concrete run is tight with trace `tr` (`IsTight ⇒ Terminates`, so the subtypes coincide).
  rw [show (∑' (r : {r : ResolvedExec State Label //
        r.trans.Terminates ∧ sys.trace r.toExec = tr ∧ sys.IsTight r.toExec})
        (de : ResolvedExec (PMF State) Label) (h : Option (Label × PMF (PMF State))),
        LowerReachProb F s ⟨de, r.1, h⟩)
      = ∑' (p : {r : ResolvedExec State Label //
          r.trans.Terminates ∧ sys.trace r.toExec = tr ∧ sys.IsTight r.toExec} ×
          ResolvedExec (PMF State) Label × Option (Label × PMF (PMF State))),
        LowerReachProb F s ⟨p.2.1, p.1.1, p.2.2⟩ by
    rw [ENNReal.tsum_prod']
    refine tsum_congr fun r => ?_
    rw [ENNReal.tsum_prod']]
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun c : Function.support (fun c : {c : LowerConfig sys //
        sys.trace c.e.toExec = tr ∧ sys.IsTight c.e.toExec} => LowerReachProb F s c.1) =>
      (⟨⟨c.1.1.e, terminates_of_isTight c.1.2.2, c.1.2.1, c.1.2.2⟩,
        c.1.1.de, c.1.1.h⟩ : {r : ResolvedExec State Label //
          r.trans.Terminates ∧ sys.trace r.toExec = tr ∧ sys.IsTight r.toExec} ×
        ResolvedExec (PMF State) Label × Option (Label × PMF (PMF State)))) ?inj ?supp ?val
  · rintro ⟨⟨c₁, hc₁⟩, hne₁⟩ ⟨⟨c₂, hc₂⟩, hne₂⟩ hab
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hab
    obtain ⟨he, hde, hh⟩ := hab
    refine Subtype.ext (Subtype.ext ?_)
    obtain ⟨d1, e1, h1⟩ := c₁
    obtain ⟨d2, e2, h2⟩ := c₂
    simp only at he hde hh
    subst he; subst hde; subst hh; rfl
  · intro p hp
    rw [Function.mem_support] at hp
    refine ⟨⟨⟨⟨p.2.1, p.1.1, p.2.2⟩, p.1.2.2.1, p.1.2.2.2⟩, hp⟩, ?_⟩
    obtain ⟨r, de, h⟩ := p
    obtain ⟨rr, hr1, hr2, hr3⟩ := r
    rfl
  · rintro ⟨⟨c, hc⟩, hne⟩
    rfl

/-- The two reach-masses coincide: on reachable configs the abstract-side and concrete-side tight
trace conditions agree (`lowerReachProb_trace_eq` + `reachProb_isTight_iff`). -/
theorem reachDe_eq_reachE (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (tr : Seq Label) :
    (∑' c : {c : LowerConfig sys //
        (sys.distF F).trace c.de.toExec = tr ∧ (sys.distF F).IsTight c.de.toExec},
      LowerReachProb F s c.1)
      = ∑' c : {c : LowerConfig sys // sys.trace c.e.toExec = tr ∧ sys.IsTight c.e.toExec},
        LowerReachProb F s c.1 := by
  classical
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun x : {x : {c : LowerConfig sys //
          sys.trace c.e.toExec = tr ∧ sys.IsTight c.e.toExec} // LowerReachProb F s x.1 ≠ 0} =>
      (⟨x.1.1, (lowerReachProb_trace_eq F s x.1.1 x.2).symm.trans x.1.2.1,
          (reachProb_isTight_iff F s x.1.1 x.2).mp x.1.2.2⟩ :
        {c : LowerConfig sys //
          (sys.distF F).trace c.de.toExec = tr ∧ (sys.distF F).IsTight c.de.toExec}))
    ?_ ?_ ?_
  · rintro ⟨⟨c₁, h₁⟩, hne₁⟩ ⟨⟨c₂, h₂⟩, hne₂⟩ hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext (Subtype.ext hab)
  · rintro ⟨c, hde⟩ hne
    rw [Function.mem_support] at hne
    exact ⟨⟨⟨c, (lowerReachProb_trace_eq F s c hne).trans hde.1,
        (reachProb_isTight_iff F s c hne).mpr hde.2⟩, hne⟩, Subtype.ext rfl⟩
  · rintro ⟨⟨c, h⟩, hne⟩; rfl

/-- **Trace-distribution correctness.** The resolved execution driven by the reconstructed scheduler
`lowerSched F s` realises the same trace distribution as the abstract scheduler `s` on
`𝒟f(sys, F)`. -/
theorem lowerSched_traceProbR (F : Fairness sys)
    (s : ResolvedScheduler (sys.distF F)) (τ : Seq Label) :
    (⟨PMF.pure sys.init, lowerSched F s⟩ : ResolvedProbabilisticExecution sys).traceProbR τ
      = (⟨PMF.pure (sys.distF F).init, s⟩ :
          ResolvedProbabilisticExecution (sys.distF F)).traceProbR τ := by
  rw [traceProbR_eq_reachE, traceProbR_eq_reachDe, reachDe_eq_reachE]

end PLTS
