/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Construction.EndState

/-!
# Trace-distribution transfer along a functional simulation

A *functional, label-preserving simulation* `f : X → Y` between two labelled
systems — `f` maps the initial state to the initial state, lifts every step
`s -[l]→ μ` to `f s -[l]→ μ.map f`, and the two systems agree on internal labels
— preserves the set of achievable trace distributions:

  `achievableTraceDists sys_X ⊆ achievableTraceDists sys_Y`.

This `achievableTraceDists_map` is the deterministic special case of strong
probabilistic simulation soundness (where the abstract successor is a *function*
of the concrete one, i.e. the coupling is the graph of `f`). It is **not**
specific to any particular simulation and is reused to prove the "subset" (easy)
directions of the `𝒟`- and `·^w`-constructions, and to project the coupled
product in `Simulation/Trace.lean`.

The witnessing `sys_Y`-execution is the pushforward of the `sys_X`-execution
along `f`, whose scheduler is recovered by a posterior over the `f`-fibres of
abstract histories (a marginalisation/disintegration).
-/

open Stream'

namespace PLTS

-- The canonical-`τ` instance `[Silent L]` is threaded as a section variable but
-- is unused by the pure `AlterSeq.map` infrastructure / kernel lemmas below;
-- silence the over-inclusion linter for both sections in this file.
set_option linter.unusedSectionVars false

/-! ### Generic `AlterSeq.map` infrastructure (for `achievableTraceDists_map`)

The pushforward of an execution along `f : X → Y` keeps the *labels* untouched, so
the label list `trans.map Prod.fst` is preserved, and `stateAt`/`endState` commute
with `f`. -/

section MapInfra

variable {X Y L : Type} [Silent L]

/-- The length of `(ofList rest).append (cons x nil)` is `rest.length + 1`. -/
theorem Stream'.Seq.append_singleton_length' {γ : Type} (rest : List γ) (x : γ) :
    ((Seq.ofList rest).append (Seq.cons x Seq.nil) : Seq γ).length' = rest.length + 1 := by
  have hcons : (Seq.cons x Seq.nil : Seq γ).Terminates :=
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
  have hfin : ((Seq.ofList rest).append (Seq.cons x Seq.nil) : Seq γ).Terminates :=
    ⟨_, Stream'.Seq.terminatedAt_append_find (Stream'.Seq.terminates_ofList rest)
      (show (Seq.cons x Seq.nil).TerminatedAt 1 from rfl)⟩
  rw [Stream'.Seq.length'_of_terminates hfin]
  have h_eq := Stream'.Seq.length_toList ((Seq.ofList rest).append (Seq.cons x Seq.nil)) hfin
  rw [Stream'.Seq.toList_append (Seq.ofList rest) (Seq.cons x Seq.nil)
    (Stream'.Seq.terminates_ofList rest) hcons hfin,
    Stream'.Seq.toList_ofList, List.length_append, Stream'.Seq.toList_cons,
    Stream'.Seq.toList_nil] at h_eq
  rw [← h_eq]; simp

/-- `AlterSeq.map` preserves the label list (only states are touched). -/
private theorem AlterSeq.mapFib_labs (f : X → Y) (e : AlterSeq X L) :
    (e.map f).trans.map Prod.fst = e.trans.map Prod.fst := by
  change (e.trans.map (fun lq => (lq.1, f lq.2))).map Prod.fst = _
  rw [← Stream'.Seq.map_comp]; rfl

/-- `stateAt` commutes with `AlterSeq.map`. -/
private theorem AlterSeq.mapFib_stateAt (f : X → Y) (e : AlterSeq X L) (n : ℕ) :
    (e.map f).stateAt n = (e.stateAt n).map f := by
  cases n with
  | zero => rfl
  | succ k =>
    change ((e.trans.map (fun lq => (lq.1, f lq.2))).get? k).map Prod.snd
      = ((e.trans.get? k).map Prod.snd).map f
    rw [Stream'.Seq.map_get?]
    cases e.trans.get? k with
    | none => rfl
    | some lq => rfl

/-- `AlterSeq.map` preserves the `length'` of the transition sequence. -/
private theorem AlterSeq.mapFib_length (f : X → Y) (e : AlterSeq X L) :
    (e.map f).trans.length' = e.trans.length' := by
  change (e.trans.map (fun lq => (lq.1, f lq.2))).length' = _
  rw [Stream'.Seq.length'_map]

/-- `get? n` agrees on labels under `AlterSeq.map` (only states are altered). -/
private theorem AlterSeq.mapFib_get?_fst (f : X → Y) (e : AlterSeq X L) (n : ℕ) :
    ((e.map f).trans.get? n).map Prod.fst = (e.trans.get? n).map Prod.fst := by
  change ((e.trans.map (fun lq => (lq.1, f lq.2))).get? n).map Prod.fst = _
  rw [Stream'.Seq.map_get?]
  cases e.trans.get? n with
  | none => rfl
  | some lq => rfl

/-- `TerminatedAt n` is preserved under `AlterSeq.map`. -/
private theorem AlterSeq.mapFib_terminatedAt (f : X → Y) (e : AlterSeq X L) (n : ℕ) :
    (e.map f).trans.TerminatedAt n ↔ e.trans.TerminatedAt n := by
  change ((e.trans.map (fun lq => (lq.1, f lq.2))).get? n) = none ↔ e.trans.get? n = none
  rw [Stream'.Seq.map_get?]
  cases e.trans.get? n with
  | none => simp
  | some lq => simp

/-- **Functional pushforward preserves traces** (traces only see labels, and the
internal/external classification is canonical — the silent label `τ`). -/
private theorem AlterSeq.trace_map {sys_X : System X L} {sys_Y : System Y L}
    (f : X → Y) (e : AlterSeq X L) :
    sys_Y.trace (e.map f) = sys_X.trace e := by
  classical
  unfold System.trace
  change ((e.trans.map (fun lq : L × X => (lq.1, f lq.2))).filter
      (fun p => ¬ (p.1 = Silent.τ))).map Prod.fst
    = (e.trans.filter (fun p => ¬ (p.1 = Silent.τ))).map Prod.fst
  rw [Stream'.Seq.filter_map (fun lq : L × X => (lq.1, f lq.2))
      (fun p : L × Y => ¬ (p.1 = Silent.τ)) e.trans]
  have hpred : (fun p : L × Y => ¬ (p.1 = Silent.τ)) ∘ (fun lq : L × X => (lq.1, f lq.2))
      = (fun p : L × X => ¬ (p.1 = Silent.τ)) := by
    funext p; rfl
  rw [hpred, ← Stream'.Seq.map_comp,
    show (Prod.fst : L × Y → L) ∘ (fun lq : L × X => (lq.1, f lq.2))
      = (Prod.fst : L × X → L) from rfl]

/-- **Functional pushforward preserves tightness** (tightness only sees labels,
and the internal/external classification is canonical — the silent label `τ`). -/
private theorem AlterSeq.isTight_map {sys_X : System X L} {sys_Y : System Y L}
    (f : X → Y) (e : AlterSeq X L) :
    sys_Y.IsTight (e.map f) ↔ sys_X.IsTight e := by
  classical
  unfold System.IsTight
  constructor
  · rintro (h0 | ⟨n, l, s, hget_n, hterm_n1, hnint⟩)
    · left; exact (AlterSeq.mapFib_terminatedAt f e 0).mp h0
    · right
      have hl : (e.trans.get? n).map Prod.fst = some l := by
        rw [← AlterSeq.mapFib_get?_fst f e n, hget_n]; rfl
      obtain ⟨⟨l', x'⟩, hx, hl'⟩ : ∃ p : L × X, e.trans.get? n = some p ∧ p.1 = l := by
        cases hc : e.trans.get? n with
        | none => rw [hc] at hl; simp at hl
        | some p => rw [hc] at hl; exact ⟨p, rfl, by simpa using hl⟩
      simp only at hl'
      subst hl'
      exact ⟨n, l', x', hx, (AlterSeq.mapFib_terminatedAt f e (n + 1)).mp hterm_n1,
        hnint⟩
  · rintro (h0 | ⟨n, l, s, hget_n, hterm_n1, hnint⟩)
    · left; exact (AlterSeq.mapFib_terminatedAt f e 0).mpr h0
    · right
      have hmapget : (e.map f).trans.get? n = some (l, f s) := by
        change (e.trans.map (fun lq : L × X => (lq.1, f lq.2))).get? n = _
        rw [Stream'.Seq.map_get?, hget_n]; rfl
      exact ⟨n, l, f s, hmapget, (AlterSeq.mapFib_terminatedAt f e (n + 1)).mpr hterm_n1,
        hnint⟩

/-- Two terminating executions mapping (via `f`) to the same `Y`-execution have
equal-length transition lists. -/
private theorem AlterSeq.fibre_len_eq (f : X → Y) (E_Y : AlterSeq Y L)
    (E1 E2 : AlterSeq X L) (h1 : E1.trans.Terminates) (h2 : E2.trans.Terminates)
    (hm1 : E1.map f = E_Y) (hm2 : E2.map f = E_Y) :
    (E1.trans.toList h1).length = (E2.trans.toList h2).length := by
  have hl1 : E1.trans.length' = E_Y.trans.length' := by rw [← AlterSeq.mapFib_length f E1, hm1]
  have hl2 : E2.trans.length' = E_Y.trans.length' := by rw [← AlterSeq.mapFib_length f E2, hm2]
  rw [Stream'.Seq.length'_of_terminates h1] at hl1
  rw [Stream'.Seq.length'_of_terminates h2] at hl2
  have heq : (E1.trans.length h1 : ℕ∞) = (E2.trans.length h2 : ℕ∞) := by rw [hl1, hl2]
  rw [Stream'.Seq.length_toList E1.trans h1, Stream'.Seq.length_toList E2.trans h2,
    (by exact_mod_cast heq : E1.trans.length h1 = E2.trans.length h2)]

/-- `(μ.map f) y'` is the total `μ`-mass on the `f`-fibre of `y'`. -/
private theorem AlterSeq.map_apply_fibre (f : X → Y) (μ : PMF X) (y' : Y) :
    (μ.map f) y' = ∑' x' : {x // f x = y'}, μ x'.1 := by
  classical
  rw [PMF.map_apply, show (∑' x' : {x // f x = y'}, μ x'.1)
      = ∑' x : X, ({x | f x = y'}.indicator (fun x => μ x)) x
      from tsum_subtype {x | f x = y'} (fun x => μ x)]
  refine tsum_congr (fun x => ?_)
  by_cases hc : f x = y'
  · rw [if_pos hc.symm, Set.indicator_of_mem (show x ∈ {x | f x = y'} from hc)]
  · rw [if_neg (fun h => hc h.symm), Set.indicator_of_notMem (show x ∉ {x | f x = y'} from hc)]

end MapInfra

/-! ### The marginal scheduler for `achievableTraceDists_map`

Given a concrete execution `pe_X` of `sys_X`, we build a single `sys_Y`-scheduler
realising the pushforward distribution. On a `Y`-history `E_Y` the scheduler emits
the (normalised) **belief-weighted pushforward** of the `pe_X`-emissions over the
`f`-fibre `{E_X // E_X.map f = E_Y}` of histories. The total fibre mass `W E_Y`
collapses to the `pe_Y`-path-measure (`hprob`), and traces/tightness are
`f`-invariant, giving the trace-distribution transfer. -/

section MapConstruction

variable {X Y L : Type} [Silent L] {sys_X : System X L} {sys_Y : System Y L}

/-- The pushforward map on scheduler emissions: keep the label, push the
distribution forward along `f`. -/
noncomputable def mapEmit (f : X → Y) : Option (L × PMF X) → Option (L × PMF Y) :=
  Option.map (fun lμ => (lμ.1, lμ.2.map f))

/-- **Mapped-kernel collapse.** For a fixed `X`-prefix `E_X`, summing the
pushforward emission weight against the `Y`-successor mass `ν y'` recovers the
total `pe_X`-kernel mass over the `f`-fibre of `y'` (via `map_apply`, fibre
collapse and a kernel unfold). -/
theorem mappedKernel_eq (pe_X : ProbabilisticExecution sys_X) (f : X → Y)
    (E_X : AlterSeq X L) (l : L) (y' : Y) :
    (∑' ν : PMF Y,
        ((pe_X.scheduler.next E_X).map (mapEmit f)) (some (l, ν)) * ν y')
      = ∑' x' : {x // f x = y'}, pe_X.kernel E_X (l, x'.1) := by
  classical
  simp only [mapEmit, PMF.map_apply]
  rw [tsum_congr (fun ν => ENNReal.tsum_mul_right.symm), ENNReal.tsum_comm]
  rw [← Function.Injective.tsum_eq (g := fun μ : PMF X => some (l, μ))
      (fun a b hab => by simpa using hab) ?supp]
  case supp =>
    intro o ho
    rw [Function.mem_support] at ho
    by_contra hcon
    apply ho
    refine ENNReal.tsum_eq_zero.mpr (fun ν => ?_)
    by_cases hc : some (l, ν) = Option.map (fun lμ : L × PMF X => (lμ.1, lμ.2.map f)) o
    · exfalso; apply hcon
      cases o with
      | none => simp at hc
      | some lμ =>
        obtain ⟨l', μ⟩ := lμ
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
        exact ⟨μ, by rw [hc.1]⟩
    · rw [if_neg hc, zero_mul]
  refine Eq.trans (tsum_congr (fun μ => ?perMu))
    (by rw [ENNReal.tsum_comm]; exact tsum_congr (fun x' => by rw [ProbabilisticExecution.kernel]) :
      (∑' (μ : PMF X) (x' : {x // f x = y'}),
          pe_X.scheduler.next E_X (some (l, μ)) * μ x'.1)
        = ∑' x' : {x // f x = y'}, pe_X.kernel E_X (l, x'.1))
  case perMu =>
    rw [tsum_eq_single (μ.map f) (fun ν hν => by
      rw [if_neg (by
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, not_and]
        exact fun _ => hν), zero_mul])]
    rw [show Option.map (fun lμ : L × PMF X => (lμ.1, lμ.2.map f)) (some (l, μ))
        = some (l, μ.map f) from rfl, if_pos rfl]
    rw [AlterSeq.map_apply_fibre f μ y', ENNReal.tsum_mul_left]

open Classical in
/-- **Fibre Kraft bound.** The total `pe_X`-mass over the `f`-fibre of a
`Y`-history `E_Y` is `≤ 1`: all fibre members are equal-length terminating
executions, hence prefix-incomparable, so the antichain Kraft bound applies. -/
theorem W_le_one (pe_X : ProbabilisticExecution sys_X) (f : X → Y)
    (E_Y : AlterSeq Y L) :
    (∑' E_X : AlterSeq X L,
      dite (E_X.trans.Terminates ∧ E_X.map f = E_Y)
        (fun h => pe_X.probOf E_X h.1) (fun _ => 0)) ≤ 1 := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le (fun s => ?_)
  set s' : Finset (AlterSeq X L) :=
    s.filter (fun E_X => E_X.trans.Terminates ∧ E_X.map f = E_Y) with hs'
  have hsum_eq : (∑ E_X ∈ s, dite (E_X.trans.Terminates ∧ E_X.map f = E_Y)
        (fun h => pe_X.probOf E_X h.1) (fun _ => 0))
      = ∑ E_X ∈ s', dite (E_X.trans.Terminates ∧ E_X.map f = E_Y)
        (fun h => pe_X.probOf E_X h.1) (fun _ => 0) := by
    rw [hs', Finset.sum_filter]
    refine Finset.sum_congr rfl (fun E_X _ => ?_)
    by_cases hc : E_X.trans.Terminates ∧ E_X.map f = E_Y
    · rw [if_pos hc]
    · rw [if_neg hc, dif_neg hc]
  rw [hsum_eq]
  have hterm : ∀ E_X ∈ s', E_X.trans.Terminates := by
    intro E_X hE; rw [hs', Finset.mem_filter] at hE; exact hE.2.1
  have hmap : ∀ E_X ∈ s', E_X.map f = E_Y := by
    intro E_X hE; rw [hs', Finset.mem_filter] at hE; exact hE.2.2
  rw [show (∑ E_X ∈ s', dite (E_X.trans.Terminates ∧ E_X.map f = E_Y)
          (fun h => pe_X.probOf E_X h.1) (fun _ => 0))
      = ∑ E_X ∈ s'.attach, pe_X.probOf E_X.1 (hterm E_X.1 E_X.2) from by
    rw [← Finset.sum_attach s' (fun E_X => dite (E_X.trans.Terminates ∧ E_X.map f = E_Y)
        (fun h => pe_X.probOf E_X h.1) (fun _ => 0))]
    refine Finset.sum_congr rfl (fun E_X _ => ?_)
    rw [dif_pos ⟨hterm E_X.1 E_X.2, hmap E_X.1 E_X.2⟩]]
  refine ProbabilisticExecution.probOf_antichain pe_X s' hterm ?_
  intro e he e' he' hinit hpre
  have hlen := AlterSeq.fibre_len_eq f E_Y e e' (hterm e he) (hterm e' he')
    (hmap e he) (hmap e' he')
  have htl : e.trans.toList (hterm e he) = e'.trans.toList (hterm e' he') :=
    hpre.eq_of_length hlen
  have htrans : e.trans = e'.trans := by
    rw [← Stream'.Seq.ofList_toList e.trans (hterm e he),
      ← Stream'.Seq.ofList_toList e'.trans (hterm e' he'), htl]
  cases e; cases e'; simp only at hinit htrans; rw [hinit, htrans]

open Classical in
-- split-last bijection on `f`-fibres of histories (a `tsum_eq_tsum_of_ne_zero_bij`)
/-- **Split-last fibre reindex.** The `pe_X`-mass over the `f`-fibre of an
appended `Y`-history `⟨y₀, (ofList rest) ++ [(l, y')]⟩` reindexes as a sum over a
prefix in the `f`-fibre of `⟨y₀, ofList rest⟩` paired with a fibre point
`x' : {x // f x = y'}` of the appended `Y`-state. -/
theorem fibre_append_reindex (pe_X : ProbabilisticExecution sys_X) (f : X → Y)
    (y₀ : Y) (rest : List (L × Y)) (l : L) (y' : Y) :
    (∑' E_X : AlterSeq X L,
        dite (E_X.trans.Terminates ∧ E_X.map f
            = ⟨y₀, (Seq.ofList rest).append (Seq.cons (l, y') Seq.nil)⟩)
          (fun h => pe_X.probOf E_X h.1) (fun _ => 0))
      = ∑' (p : AlterSeq X L × {x : X // f x = y'}),
          dite (p.1.trans.Terminates ∧ p.1.map f = ⟨y₀, Seq.ofList rest⟩)
            (fun h => pe_X.probOf
              ⟨p.1.init, p.1.trans.append (Seq.cons (l, p.2.1) Seq.nil)⟩
              ⟨_, Stream'.Seq.terminatedAt_append_find h.1
                  (show (Seq.cons (l, p.2.1) Seq.nil).TerminatedAt 1 from rfl)⟩)
            (fun _ => 0) := by
  classical
  refine (tsum_eq_tsum_of_ne_zero_bij
    (i := fun x =>
      (⟨x.1.1.init, x.1.1.trans.append (Seq.cons (l, x.1.2.1) Seq.nil)⟩ : AlterSeq X L))
    ?hinj ?hf ?hfg)
  case hinj =>
    rintro ⟨⟨E1, ⟨a1, ha1⟩⟩, hE1⟩ ⟨⟨E2, ⟨a2, ha2⟩⟩, hE2⟩ hab
    rw [Function.mem_support] at hE1 hE2
    have hT1 : E1.trans.Terminates := by by_contra hc; exact hE1 (dif_neg (fun h => hc h.1))
    have hT2 : E2.trans.Terminates := by by_contra hc; exact hE2 (dif_neg (fun h => hc h.1))
    simp only at hab
    have hinit : E1.init = E2.init := congr_arg (·.init) hab
    have htrans : E1.trans.append (Seq.cons (l, a1) Seq.nil)
        = E2.trans.append (Seq.cons (l, a2) Seq.nil) := congr_arg (·.trans) hab
    have hE12 : E1.trans = E2.trans :=
      Stream'.Seq.append_singleton_inj_left _ _ hT1 hT2 _ _ htrans
    have ha12 : a1 = a2 := by
      have he1 := AlterSeq.endState_append_singleton E1 hT1 l a1
      have he2 := AlterSeq.endState_append_singleton E2 hT2 l a2
      have heq := AlterSeq.endState_congr_pub hab
        ⟨_, Stream'.Seq.terminatedAt_append_find hT1
          (show (Seq.cons (l, a1) Seq.nil).TerminatedAt 1 from rfl)⟩
        ⟨_, Stream'.Seq.terminatedAt_append_find hT2
          (show (Seq.cons (l, a2) Seq.nil).TerminatedAt 1 from rfl)⟩
      rw [he1, he2] at heq; exact heq
    have hEE : E1 = E2 := by
      cases E1; cases E2; simp only at hinit hE12; subst hinit; subst hE12; rfl
    subst hEE; subst ha12; rfl
  case hf =>
    intro E hE
    rw [Function.mem_support] at hE
    have hc : E.trans.Terminates ∧ E.map f
        = ⟨y₀, (Seq.ofList rest).append (Seq.cons (l, y') Seq.nil)⟩ := by
      by_contra hcon; exact hE (dif_neg hcon)
    obtain ⟨hT, hmap⟩ := hc
    have htrans_proj : E.trans.map (fun lq => (lq.1, f lq.2))
        = (Seq.ofList rest).append (Seq.cons (l, y') Seq.nil) := congr_arg (·.trans) hmap
    have hne : E.trans.toList hT ≠ [] := by
      intro hnil
      have hlen : E.trans.length' = 0 := by
        rw [Stream'.Seq.length'_of_terminates hT]
        have := Stream'.Seq.length_toList E.trans hT
        rw [hnil, List.length_nil] at this; simp [← this]
      have hmaplen : (E.trans.map (fun lq : L × X => (lq.1, f lq.2))).length' = 0 := by
        rw [Stream'.Seq.length'_map]; exact hlen
      rw [htrans_proj, Stream'.Seq.append_singleton_length'] at hmaplen
      exact absurd (by exact_mod_cast hmaplen : rest.length + 1 = 0) (Nat.succ_ne_zero _)
    obtain ⟨previous, lastp, h_prev, h_split, _, _⟩ :=
      Stream'.Seq.exists_split_last E.trans hT hne
    rw [h_split, Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil]
      at htrans_proj
    have hpm : (previous.map (fun lq : L × X => (lq.1, f lq.2))).Terminates :=
      Stream'.Seq.terminates_map_iff.mpr h_prev
    have hprevmap : previous.map (fun lq : L × X => (lq.1, f lq.2)) = Seq.ofList rest :=
      Stream'.Seq.append_singleton_inj_left _ _ hpm (Stream'.Seq.terminates_ofList rest) _ _
        htrans_proj
    have hpm_min : ∀ k < rest.length,
        ¬ (previous.map (fun lq : L × X => (lq.1, f lq.2))).TerminatedAt k := by
      intro k hk hterm
      rw [hprevmap, show (Seq.ofList rest).TerminatedAt k ↔ (Seq.ofList rest).get? k = none from
        Iff.rfl, Stream'.Seq.ofList_get?] at hterm
      exact absurd hterm (by rw [List.getElem?_eq_getElem hk]; exact Option.some_ne_none _)
    have hpm_done : (previous.map
        (fun lq : L × X => (lq.1, f lq.2))).TerminatedAt rest.length := by
      rw [hprevmap]; exact Stream'.Seq.terminatedAt_ofList rest
    have hrmin : ∀ k < rest.length, ¬ (Seq.ofList rest : Seq (L × Y)).TerminatedAt k := by
      intro k hk hterm
      rw [show (Seq.ofList rest).TerminatedAt k ↔ (Seq.ofList rest).get? k = none from Iff.rfl,
        Stream'.Seq.ofList_get?] at hterm
      exact absurd hterm (by rw [List.getElem?_eq_getElem hk]; exact Option.some_ne_none _)
    have hbound : (lastp.1, f lastp.2) = (l, y') := by
      have h_lhs := Stream'.Seq.get?_append_after_length
        (s' := Seq.cons (lastp.1, f lastp.2) Seq.nil) hpm_min hpm_done 0
      have h_rhs := Stream'.Seq.get?_append_after_length
        (s' := Seq.cons (l, y') Seq.nil) hrmin (Stream'.Seq.terminatedAt_ofList rest) 0
      rw [Stream'.Seq.get?_cons_zero] at h_lhs h_rhs
      rw [htrans_proj] at h_lhs
      rw [h_rhs] at h_lhs
      exact (Option.some.inj h_lhs).symm
    obtain ⟨hl', hsc'⟩ := Prod.mk.injEq .. ▸ hbound
    have hlasteq : lastp = (l, lastp.2) := by
      obtain ⟨ll, sc⟩ := lastp; simp only at hl' ⊢; rw [hl']
    have hprobE : pe_X.probOf E hT ≠ 0 := by
      intro h0; exact hE (by rw [dif_pos ⟨hT, hmap⟩, h0])
    have hprevproj : (⟨E.init, previous⟩ : AlterSeq X L).map f = ⟨y₀, Seq.ofList rest⟩ := by
      have hinitY : f E.init = y₀ := congr_arg (·.init) hmap
      change (⟨f E.init, previous.map (fun lq => (lq.1, f lq.2))⟩ : AlterSeq Y L)
        = ⟨y₀, Seq.ofList rest⟩
      rw [hprevmap, hinitY]
    have hsupp_ne : dite ((⟨E.init, previous⟩ : AlterSeq X L).trans.Terminates
          ∧ (⟨E.init, previous⟩ : AlterSeq X L).map f = ⟨y₀, Seq.ofList rest⟩)
        (fun h => pe_X.probOf
          ⟨(⟨E.init, previous⟩ : AlterSeq X L).init,
            (⟨E.init, previous⟩ : AlterSeq X L).trans.append (Seq.cons (l, lastp.2) Seq.nil)⟩
          ⟨_, Stream'.Seq.terminatedAt_append_find h.1
              (show (Seq.cons (l, lastp.2) Seq.nil).TerminatedAt 1 from rfl)⟩)
        (fun _ => 0) ≠ 0 := by
      rw [dif_pos ⟨h_prev, hprevproj⟩]
      have hEeq : (⟨(⟨E.init, previous⟩ : AlterSeq X L).init,
            previous.append (Seq.cons (l, lastp.2) Seq.nil)⟩ : AlterSeq X L) = E := by
        cases E; simp only at h_split ⊢; rw [h_split, hlasteq]
      rw [pe_X.probOf_congr _ E hEeq _ hT]; exact hprobE
    refine ⟨⟨(⟨E.init, previous⟩, ⟨lastp.2, hsc'⟩), hsupp_ne⟩, ?_⟩
    change (⟨(⟨E.init, previous⟩ : AlterSeq X L).init,
        previous.append (Seq.cons (l, lastp.2) Seq.nil)⟩ : AlterSeq X L) = E
    cases E; simp only at h_split ⊢; rw [h_split, hlasteq]
  case hfg =>
    rintro ⟨⟨E1, ⟨a1, ha1⟩⟩, hmem⟩
    rw [Function.mem_support] at hmem
    have hg : E1.trans.Terminates ∧ E1.map f = ⟨y₀, Seq.ofList rest⟩ := by
      by_contra hc; exact hmem (dif_neg hc)
    change dite _ _ _ = dite _ _ _
    have hcondF :
        (⟨E1.init, E1.trans.append (Seq.cons (l, a1) Seq.nil)⟩ : AlterSeq X L).trans.Terminates
          ∧ (⟨E1.init, E1.trans.append (Seq.cons (l, a1) Seq.nil)⟩ : AlterSeq X L).map f
            = ⟨y₀, (Seq.ofList rest).append (Seq.cons (l, y') Seq.nil)⟩ :=
      ⟨⟨_, Stream'.Seq.terminatedAt_append_find hg.1
          (show (Seq.cons (l, a1) Seq.nil).TerminatedAt 1 from rfl)⟩,
        by rw [AlterSeq.map_append_singleton f E1 l a1, hg.2, ha1]⟩
    rw [dif_pos hcondF, dif_pos hg]

open Classical in
/-- Total `pe_X`-mass over the `f`-fibre of `E_Y`. -/
noncomputable def mapWeight (f : X → Y) (pe_X : ProbabilisticExecution sys_X)
    (E_Y : AlterSeq Y L) : ENNReal :=
  ∑' E_X : AlterSeq X L,
    dite (E_X.trans.Terminates ∧ E_X.map f = E_Y) (fun h => pe_X.probOf E_X h.1) (fun _ => 0)

open Classical in
/-- Belief numerator (fibre-weighted pushforward of emissions). -/
noncomputable def mapBeliefNum (f : X → Y) (pe_X : ProbabilisticExecution sys_X)
    (E_Y : AlterSeq Y L) (o : Option (L × PMF Y)) : ENNReal :=
  ∑' E_X : AlterSeq X L,
    (dite (E_X.trans.Terminates ∧ E_X.map f = E_Y) (fun h => pe_X.probOf E_X h.1) (fun _ => 0))
      * ((pe_X.scheduler.next E_X).map (mapEmit f)) o

/-- `∑' o, mapBeliefNum … o = mapWeight …` (the pushforward emission PMF sums to 1). -/
private theorem mapBeliefNum_tsum (f : X → Y) (pe_X : ProbabilisticExecution sys_X)
    (E_Y : AlterSeq Y L) :
    (∑' o, mapBeliefNum f pe_X E_Y o) = mapWeight f pe_X E_Y := by
  classical
  simp only [mapBeliefNum, mapWeight]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun E_X => ?_)
  rw [ENNReal.tsum_mul_left, ((pe_X.scheduler.next E_X).map (mapEmit f)).tsum_coe, mul_one]

/-- `mapWeight` never equals `⊤` (it is bounded by `1` via the Kraft antichain bound). -/
private theorem mapWeight_ne_top (f : X → Y) (pe_X : ProbabilisticExecution sys_X)
    (E_Y : AlterSeq Y L) : mapWeight f pe_X E_Y ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (W_le_one pe_X f E_Y)

/-- The marginal (belief) scheduler on `sys_Y`: on a `Y`-history `E_Y` it emits the
`mapWeight`-normalised belief-weighted pushforward `mapBeliefNum` of the `pe_X`
emissions over the `f`-fibre of `E_Y` (or stops if the fibre has zero mass). -/
noncomputable def mapBeliefSched (f : X → Y)
    (h_step : ∀ s l μ, sys_X.step s l μ → sys_Y.step (f s) l (μ.map f))
    (pe_X : ProbabilisticExecution sys_X) : Scheduler sys_Y :=
  { next := fun E_Y => if hW0 : mapWeight f pe_X E_Y = 0 then PMF.pure none
      else PMF.normalize (mapBeliefNum f pe_X E_Y) (by rw [mapBeliefNum_tsum]; exact hW0)
        (by rw [mapBeliefNum_tsum]; exact mapWeight_ne_top f pe_X E_Y)
    valid := by
      classical
      intro E_Y n s hterm hstate l ν hsupp
      by_cases hW0 : mapWeight f pe_X E_Y = 0
      · rw [dif_pos hW0, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
        exact absurd rfl hsupp
      · simp only [dif_neg hW0, PMF.mem_support_normalize_iff] at hsupp
        -- `hsupp : mapBeliefNum … (some (l, ν)) ≠ 0`; extract a fibre witness `E_X`.
        have hgne : (∑' E_X : AlterSeq X L,
            (dite (E_X.trans.Terminates ∧ E_X.map f = E_Y)
                (fun h => pe_X.probOf E_X h.1) (fun _ => 0))
              * ((pe_X.scheduler.next E_X).map (mapEmit f)) (some (l, ν))) ≠ 0 := hsupp
        have hex := mt ENNReal.tsum_eq_zero.mpr hgne
        push Not at hex
        obtain ⟨E_X, hEX⟩ := hex
        have hguard : E_X.trans.Terminates ∧ E_X.map f = E_Y := by
          by_contra hc
          rw [dif_neg hc, zero_mul] at hEX; exact hEX rfl
        have hmapne : ((pe_X.scheduler.next E_X).map (mapEmit f)) (some (l, ν)) ≠ 0 := by
          intro h0; rw [h0, mul_zero] at hEX; exact hEX rfl
        obtain ⟨μ, hμne, hνeq⟩ :
            ∃ μ : PMF X, pe_X.scheduler.next E_X (some (l, μ)) ≠ 0 ∧ ν = μ.map f := by
          rw [mapEmit, PMF.map_apply] at hmapne
          have hex2 := mt ENNReal.tsum_eq_zero.mpr hmapne
          push Not at hex2
          obtain ⟨o, ho⟩ := hex2
          by_cases hc : some (l, ν) = Option.map (fun lμ : L × PMF X => (lμ.1, lμ.2.map f)) o
          · cases o with
            | none => simp at hc
            | some lμ =>
              obtain ⟨l', μ⟩ := lμ
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
              obtain ⟨rfl, rfl⟩ := hc
              exact ⟨μ, fun h0 => by rw [h0] at ho; simp at ho, rfl⟩
          · rw [if_neg hc] at ho; exact absurd rfl ho
        -- the current `X`-state at `n` maps to `s`.
        have hstateX : (E_X.stateAt n).map f = some s := by
          rw [← AlterSeq.mapFib_stateAt f E_X n, hguard.2, hstate]
        obtain ⟨x, hxn, hfx⟩ : ∃ x : X, E_X.stateAt n = some x ∧ f x = s := by
          cases hc : E_X.stateAt n with
          | none => rw [hc] at hstateX; simp at hstateX
          | some x => rw [hc] at hstateX; exact ⟨x, rfl, by simpa using hstateX⟩
        have htermX : E_X.trans.TerminatedAt n :=
          (AlterSeq.mapFib_terminatedAt f E_X n).mp (hguard.2 ▸ hterm)
        have hstepX : sys_X.step x l μ :=
          pe_X.scheduler.valid E_X n x htermX hxn l μ ((PMF.mem_support_iff _ _).mpr hμne)
        have hres := h_step x l μ hstepX
        rw [hfx, ← hνeq] at hres
        exact hres }

/-- The pushforward probabilistic execution (Dirac init + belief scheduler). -/
noncomputable def mapBeliefExec (f : X → Y)
    (h_step : ∀ s l μ, sys_X.step s l μ → sys_Y.step (f s) l (μ.map f))
    (pe_X : ProbabilisticExecution sys_X) : ProbabilisticExecution sys_Y :=
  ⟨PMF.pure sys_Y.init, mapBeliefSched f h_step pe_X⟩

@[simp] theorem mapBeliefExec_initState (f : X → Y)
    (h_step : ∀ s l μ, sys_X.step s l μ → sys_Y.step (f s) l (μ.map f))
    (pe_X : ProbabilisticExecution sys_X) :
    (mapBeliefExec f h_step pe_X).initState = PMF.pure sys_Y.init := rfl

/-- **Cancellation:** `mapWeight · belief-scheduler-emission = mapBeliefNum`. -/
theorem mapWeight_mul_next (f : X → Y)
    (h_step : ∀ s l μ, sys_X.step s l μ → sys_Y.step (f s) l (μ.map f))
    (pe_X : ProbabilisticExecution sys_X) (E_Y : AlterSeq Y L) (o : Option (L × PMF Y)) :
    mapWeight f pe_X E_Y * (mapBeliefSched f h_step pe_X).next E_Y o
      = mapBeliefNum f pe_X E_Y o := by
  classical
  by_cases hW0 : mapWeight f pe_X E_Y = 0
  · have hnext : (mapBeliefSched f h_step pe_X).next E_Y = PMF.pure none := by
      simp only [mapBeliefSched]; exact dif_pos hW0
    rw [hnext, hW0, zero_mul]
    have hall : ∀ o', mapBeliefNum f pe_X E_Y o' = 0 := by
      rw [← ENNReal.tsum_eq_zero, mapBeliefNum_tsum]; exact hW0
    exact (hall o).symm
  · have hnext : (mapBeliefSched f h_step pe_X).next E_Y o
        = mapBeliefNum f pe_X E_Y o * (mapWeight f pe_X E_Y)⁻¹ := by
      have h1 : (mapBeliefSched f h_step pe_X).next E_Y
          = PMF.normalize (mapBeliefNum f pe_X E_Y) (by rw [mapBeliefNum_tsum]; exact hW0)
            (by rw [mapBeliefNum_tsum]; exact mapWeight_ne_top f pe_X E_Y) := by
        simp only [mapBeliefSched]; exact dif_neg hW0
      rw [h1, PMF.normalize_apply, mapBeliefNum_tsum]
    rw [hnext, ← mul_assoc, mul_comm (mapWeight f pe_X E_Y) (mapBeliefNum f pe_X E_Y o),
      mul_assoc, ENNReal.mul_inv_cancel hW0 (mapWeight_ne_top f pe_X E_Y), mul_one]

/-- **Path-measure identity.** The `mapBeliefExec`-probability of a terminating
`Y`-history `E_Y` collapses to the total `f`-fibre mass `mapWeight … E_Y`. Proven
by cons-end (`reverseRecOn`) induction on the label list, using the cancellation
`mapWeight_mul_next`, the mapped-kernel collapse and the split-last fibre reindex. -/
theorem mapBeliefExec_probOf (f : X → Y)
    (h_step : ∀ s l μ, sys_X.step s l μ → sys_Y.step (f s) l (μ.map f))
    (pe_X : ProbabilisticExecution sys_X) (h_init : f sys_X.init = sys_Y.init)
    (h_init_X : pe_X.initState = PMF.pure sys_X.init)
    (E_Y : AlterSeq Y L) (hFin : E_Y.trans.Terminates) :
    (mapBeliefExec f h_step pe_X).probOf E_Y hFin = mapWeight f pe_X E_Y := by
  classical
  -- Rebind the pushforward pieces to the short names used in the path-measure proof.
  set gnum : AlterSeq Y L → AlterSeq X L → ENNReal := fun E_Y E_X =>
    dite (E_X.trans.Terminates ∧ E_X.map f = E_Y) (fun h => pe_X.probOf E_X h.1) (fun _ => 0)
    with hgnum
  set g : AlterSeq Y L → Option (L × PMF Y) → ENNReal := fun E_Y o =>
    ∑' E_X : AlterSeq X L, gnum E_Y E_X * ((pe_X.scheduler.next E_X).map (mapEmit f)) o with hg
  set W : AlterSeq Y L → ENNReal := fun E_Y => ∑' E_X : AlterSeq X L, gnum E_Y E_X with hW
  set σ_Y : Scheduler sys_Y := mapBeliefSched f h_step pe_X with hσ
  set pe_Y : ProbabilisticExecution sys_Y := mapBeliefExec f h_step pe_X with hpe_Y
  -- **Cancellation:** `W E_Y * σ_Y.next E_Y o = g E_Y o` (from `mapWeight_mul_next`).
  have hcancel : ∀ E_Y o, W E_Y * σ_Y.next E_Y o = g E_Y o :=
    fun E_Y o => mapWeight_mul_next f h_step pe_X E_Y o
  change pe_Y.probOf E_Y hFin = W E_Y
  suffices hgen : ∀ (LY : List (L × Y)) (y₀ : Y)
      (hFin : (Seq.ofList LY : Seq (L × Y)).Terminates),
      pe_Y.probOf ⟨y₀, Seq.ofList LY⟩ hFin = W ⟨y₀, Seq.ofList LY⟩ by
    have hofl : (Seq.ofList (E_Y.trans.toList hFin) : Seq (L × Y)) = E_Y.trans :=
      Stream'.Seq.ofList_toList E_Y.trans hFin
    have hFin' : (Seq.ofList (E_Y.trans.toList hFin) : Seq (L × Y)).Terminates := by
      rw [hofl]; exact hFin
    have hEeq : (⟨E_Y.init, Seq.ofList (E_Y.trans.toList hFin)⟩ : AlterSeq Y L) = E_Y := by
      cases E_Y; simp only [hofl]
    have hkey := hgen (E_Y.trans.toList hFin) E_Y.init hFin'
    rw [pe_Y.probOf_congr ⟨E_Y.init, Seq.ofList (E_Y.trans.toList hFin)⟩ E_Y hEeq hFin' hFin]
      at hkey
    rw [hkey, hEeq]
  intro LY
  induction LY using List.reverseRecOn with
  | nil =>
    intro y₀ hFin
    rw [pe_Y.probOf_congr ⟨y₀, Seq.ofList ([] : List (L × Y))⟩ ⟨y₀, Seq.nil⟩
      (by rw [Stream'.Seq.ofList_nil]) hFin Stream'.Seq.terminates_nil,
      ProbabilisticExecution.probOf_nil]
    change (PMF.pure sys_Y.init) y₀
      = ∑' E_X : AlterSeq X L, gnum ⟨y₀, Seq.ofList ([] : List (L × Y))⟩ E_X
    -- `W ⟨y₀, nil⟩ = ∑' E_X (E_X.map f = ⟨y₀,nil⟩), probOf = (pure sys_Y.init) y₀`.
    rw [tsum_congr (fun E_X => by rw [hgnum]), Stream'.Seq.ofList_nil]
    rw [← Function.Injective.tsum_eq (g := fun x : {x : X // f x = y₀} =>
        (⟨x.1, Seq.nil⟩ : AlterSeq X L))
        (fun a b hab => by
          have := congr_arg (·.init) hab; simp only at this; exact Subtype.ext this)
        (f := fun E_X : AlterSeq X L =>
          dite (E_X.trans.Terminates ∧ E_X.map f = (⟨y₀, Seq.nil⟩ : AlterSeq Y L))
            (fun h => pe_X.probOf E_X h.1) (fun _ => 0)) ?suppNil]
    · rw [show (PMF.pure sys_Y.init) y₀
          = ((PMF.pure sys_X.init).map f) y₀ from by rw [PMF.pure_map, h_init],
        AlterSeq.map_apply_fibre f (PMF.pure sys_X.init) y₀]
      refine tsum_congr (fun x => ?_)
      rw [dif_pos ⟨Stream'.Seq.terminates_nil, by
        change (⟨f x.1, Stream'.Seq.map _ Seq.nil⟩ : AlterSeq Y L) = ⟨y₀, Seq.nil⟩
        rw [Stream'.Seq.map_nil, x.2]⟩,
        ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState, h_init_X]
    case suppNil =>
      intro E_X hE
      rw [Function.mem_support] at hE
      have hc : E_X.trans.Terminates ∧ E_X.map f = (⟨y₀, Seq.nil⟩ : AlterSeq Y L) := by
        by_contra hcon; exact hE (dif_neg hcon)
      obtain ⟨hT, hmap⟩ := hc
      have hinit : f E_X.init = y₀ := congr_arg (·.init) hmap
      have htrans : E_X.trans.map (fun lq => (lq.1, f lq.2)) = Seq.nil := congr_arg (·.trans) hmap
      have hEtrans : E_X.trans = Seq.nil := by
        have hlen := congr_arg Stream'.Seq.length' htrans
        rw [Stream'.Seq.length'_map, Stream'.Seq.length'_nil] at hlen
        exact (Stream'.Seq.length'_eq_zero_iff_nil E_X.trans).mp hlen
      refine ⟨⟨E_X.init, hinit⟩, ?_⟩
      obtain ⟨ei, et⟩ := E_X; simp only at hEtrans ⊢; rw [hEtrans]
  | append_singleton rest last ih =>
    intro y₀ hFin
    obtain ⟨l, y'⟩ := last
    have hsplit : (Seq.ofList (rest ++ [(l, y')]) : Seq (L × Y))
        = (Seq.ofList rest).append (Seq.cons (l, y') Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have hrest_fin : (Seq.ofList rest : Seq (L × Y)).Terminates :=
      Stream'.Seq.terminates_ofList _
    have hFinS : ((Seq.ofList rest).append (Seq.cons (l, y') Seq.nil)).Terminates := by
      rw [← hsplit]; exact hFin
    set E_Y' : AlterSeq Y L := ⟨y₀, Seq.ofList rest⟩ with hE_Y'
    -- The common middle expression.
    set Mid : ENNReal := ∑' E_X' : AlterSeq X L,
      gnum E_Y' E_X' * ∑' x' : {x : X // f x = y'}, pe_X.kernel E_X' (l, x'.1) with hMid
    -- **LHS = Mid.**
    have hLHS : pe_Y.probOf ⟨y₀, Seq.ofList (rest ++ [(l, y')])⟩ hFin = Mid := by
      rw [pe_Y.probOf_congr ⟨y₀, Seq.ofList (rest ++ [(l, y')])⟩
          ⟨y₀, (Seq.ofList rest).append (Seq.cons (l, y') Seq.nil)⟩ (by rw [hsplit]) hFin hFinS,
        pe_Y.probOf_append_singleton y₀ (Seq.ofList rest) hrest_fin (l, y') hFinS,
        show pe_Y.probOf E_Y' hrest_fin = W E_Y' from ih y₀ hrest_fin]
      -- `W E_Y' * kernel_Y = ∑' ν, g E_Y' (some(l,ν)) * ν y'`.
      rw [ProbabilisticExecution.kernel]
      change W E_Y' * (∑' ν, σ_Y.next E_Y' (some (l, ν)) * ν y') = Mid
      rw [← ENNReal.tsum_mul_left]
      rw [tsum_congr (fun ν => by rw [← mul_assoc, hcancel E_Y' (some (l, ν))])]
      -- `g E_Y' (some(l,ν)) = ∑' E_X', gnum E_Y' E_X' * mappedNext E_X' (some(l,ν))`.
      rw [tsum_congr (fun ν => by rw [hg]), hMid]
      -- swap and factor: push `* ν y'` inside, swap `ν`/`E_X'`, then factor `gnum`.
      rw [tsum_congr (fun ν => ENNReal.tsum_mul_right.symm), ENNReal.tsum_comm]
      refine tsum_congr (fun E_X' => ?_)
      rw [tsum_congr (fun ν => mul_assoc _ _ _), ENNReal.tsum_mul_left,
        mappedKernel_eq pe_X f E_X' l y']
    -- **RHS = Mid.**
    have hRHS : W ⟨y₀, Seq.ofList (rest ++ [(l, y')])⟩ = Mid := by
      rw [hW]
      change (∑' E_X, gnum ⟨y₀, Seq.ofList (rest ++ [(l, y')])⟩ E_X) = Mid
      rw [tsum_congr (fun E_X => by rw [hgnum]), hsplit]
      rw [fibre_append_reindex pe_X f y₀ rest l y', ENNReal.tsum_prod']
      rw [hMid]
      refine tsum_congr (fun E_X' => ?_)
      simp only
      by_cases hc : E_X'.trans.Terminates ∧ E_X'.map f = ⟨y₀, Seq.ofList rest⟩
      · rw [tsum_congr (fun x' => dif_pos hc)]
        rw [tsum_congr (fun x' : {x : X // f x = y'} =>
            ProbabilisticExecution.probOf_append_singleton pe_X E_X'.init
              E_X'.trans hc.1 (l, x'.1) _), ENNReal.tsum_mul_left]
        rw [show gnum E_Y' E_X' = pe_X.probOf E_X' hc.1 from by rw [hgnum]; exact dif_pos hc]
      · rw [tsum_congr (fun x' => dif_neg hc), tsum_zero]
        rw [show gnum E_Y' E_X' = 0 from by rw [hgnum]; exact dif_neg hc, zero_mul]
    rw [hLHS, hRHS]

/-- **Trace transfer along the pushforward.** The `sys_Y`-trace distribution of
`mapBeliefExec … pe_X` equals the `sys_X`-trace distribution of `pe_X`: traces and
tightness are `f`-invariant, and the path-measure collapses to the fibre mass
(`mapBeliefExec_probOf`), so the tight-`X` executions biject onto the (tight-`Y`,
fibre) product support. -/
theorem mapBeliefExec_traceProb (f : X → Y)
    (h_step : ∀ s l μ, sys_X.step s l μ → sys_Y.step (f s) l (μ.map f))
    (pe_X : ProbabilisticExecution sys_X) (h_init : f sys_X.init = sys_Y.init)
    (h_init_X : pe_X.initState = PMF.pure sys_X.init) (τ : Seq L) :
    sys_Y.traceProb (mapBeliefExec f h_step pe_X) τ = sys_X.traceProb pe_X τ := by
  classical
  set gnum : AlterSeq Y L → AlterSeq X L → ENNReal := fun E_Y E_X =>
    dite (E_X.trans.Terminates ∧ E_X.map f = E_Y) (fun h => pe_X.probOf E_X h.1) (fun _ => 0)
    with hgnum
  set W : AlterSeq Y L → ENNReal := fun E_Y => ∑' E_X : AlterSeq X L, gnum E_Y E_X with hW
  set pe_Y : ProbabilisticExecution sys_Y := mapBeliefExec f h_step pe_X with hpe_Y
  have hprob : ∀ (E_Y : AlterSeq Y L) (hFin : E_Y.trans.Terminates),
      pe_Y.probOf E_Y hFin = W E_Y :=
    fun E_Y hFin => mapBeliefExec_probOf f h_step pe_X h_init h_init_X E_Y hFin
  -- Unfold both `traceProb`s; substitute `hprob`; biject `f`-fibres of tight execs.
  unfold System.traceProb
  -- LHS: substitute `hprob`, then combine tight-`Y` sum and fibre sum into a product.
  refine Eq.trans (tsum_congr (fun E_Y => hprob E_Y.1 E_Y.2.1)) ?_
  refine Eq.trans
    (show (∑' E_Y : {e : AlterSeq Y L //
            e.trans.Terminates ∧ sys_Y.trace e = τ ∧ sys_Y.IsTight e}, W E_Y.1)
        = ∑' p : {e : AlterSeq Y L //
              e.trans.Terminates ∧ sys_Y.trace e = τ ∧ sys_Y.IsTight e} × AlterSeq X L,
            gnum p.1.1 p.2 from by
      rw [ENNReal.tsum_prod']) ?_
  -- biject the tight-`X` execs onto the (tight-`Y`, fibre) product support.
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun x : {x : {e : AlterSeq X L //
          e.trans.Terminates ∧ sys_X.trace e = τ ∧ sys_X.IsTight e} //
          pe_X.probOf x.1 x.2.1 ≠ 0} =>
      (⟨⟨x.1.1.map f,
          ⟨(AlterSeq.map_trans_terminates_iff f x.1.1).mpr x.1.2.1,
            by rw [AlterSeq.trace_map f x.1.1]; exact x.1.2.2.1,
            (AlterSeq.isTight_map f x.1.1).mpr x.1.2.2.2⟩⟩,
          x.1.1⟩ :
        {e : AlterSeq Y L // e.trans.Terminates ∧ sys_Y.trace e = τ ∧ sys_Y.IsTight e}
          × AlterSeq X L))
    ?tinj ?tf ?tfg
  case tinj =>
    rintro ⟨⟨E1, hE1⟩, hne1⟩ ⟨⟨E2, hE2⟩, hne2⟩ hab
    simp only [Prod.mk.injEq] at hab
    exact Subtype.ext (Subtype.ext hab.2)
  case tf =>
    intro p hp
    rw [Function.mem_support] at hp
    simp only [hgnum] at hp
    -- `gnum p.1.1 p.2 ≠ 0` forces the fibre guard, hence `p.2` is a tight-X τ-exec.
    have hc : p.2.trans.Terminates ∧ p.2.map f = p.1.1 := by
      by_contra hcon; rw [dif_neg hcon] at hp; exact hp rfl
    have hpe : pe_X.probOf p.2 hc.1 ≠ 0 := by
      intro h0; rw [dif_pos hc, h0] at hp; exact hp rfl
    have hXtight : p.2.trans.Terminates ∧ sys_X.trace p.2 = τ ∧ sys_X.IsTight p.2 := by
      refine ⟨hc.1, ?_, ?_⟩
      · rw [← AlterSeq.trace_map f p.2, hc.2]; exact p.1.2.2.1
      · rw [← AlterSeq.isTight_map f p.2, hc.2]; exact p.1.2.2.2
    refine ⟨⟨⟨p.2, hXtight⟩, ?_⟩, ?_⟩
    · change pe_X.probOf p.2 hXtight.1 ≠ 0; exact hpe
    · -- the image pair equals `p` (the `Y`-component is forced by `p.2.map f = p.1.1`).
      exact Prod.ext (Subtype.ext (by simp only; rw [hc.2])) rfl
  case tfg =>
    rintro ⟨⟨E_X, hX⟩, hne⟩
    change gnum (E_X.map f) E_X = pe_X.probOf E_X hX.1
    simp only [hgnum]
    rw [dif_pos (show E_X.trans.Terminates ∧ True from ⟨hX.1, trivial⟩)]

/-- **Functional simulation preserves achievable trace distributions.** If
`f : X → Y` maps the initial state to the initial state, lifts every `sys_X` step
`s -[l]→ μ` to a `sys_Y` step `f s -[l]→ μ.map f`, and the two systems agree on
internal labels, then every trace distribution achievable by `sys_X` is
achievable by `sys_Y`.

This is the marginalisation crux: the `sys_Y`-execution witnessing membership is
the pushforward of the `sys_X`-execution along `f`, whose scheduler is recovered
by a posterior over the `f`-fibres of abstract histories.

The proof builds a marginal scheduler via a posterior over `f`-fibres and a
`reverseRecOn` path-measure identity (hence the raised heartbeat budget for the
heavy nested `tsum` reindexings). -/
theorem achievableTraceDists_map {X Y L : Type} [Silent L]
    {sys_X : System X L} {sys_Y : System Y L} (f : X → Y)
    (h_init : f sys_X.init = sys_Y.init)
    (h_step : ∀ s l μ, sys_X.step s l μ → sys_Y.step (f s) l (μ.map f)) :
    achievableTraceDists sys_X ⊆ achievableTraceDists sys_Y := by
  rintro D ⟨pe_X, h_init_X, h_trace_X⟩
  exact ⟨mapBeliefExec f h_step pe_X, mapBeliefExec_initState f h_step pe_X,
    fun τ => by rw [mapBeliefExec_traceProb f h_step pe_X h_init h_init_X τ]; exact h_trace_X τ⟩

end MapConstruction

end PLTS
