/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.WeakClosure.Trace

/-!
# Abstract-side fidelity of the unfolding algorithm

The probability of the `sys^w`-trajectory `e` under `ws` equals the probability of
reaching an unfolding-algorithm configuration whose abstract execution `we` is `e` —
counted **without double-counting**: only at the *entry* configurations
`c.we = e ∧ c.e'.trans = nil` (the freshly-committed / reset points, hit exactly once
per run that reaches `we = e`).
-/

open Stream'

namespace PLTS

variable {State Label : Type} [Silent Label] {sys : System State Label}

open Classical in
/-- **Segment pushforward.** Summing the witness `schedOf sys y l μ`'s halting runs that
end at a fixed state `x` recovers `μ x` — i.e. the concrete unfolding of one weak step
`(l, μ)` reproduces the abstract end-state distribution `μ`. (This is `Realises` clause (b)
for `schedOf`, available because `sys^w.step y l μ` makes `schedOf` a genuine witness.) -/
theorem seg_pushforward {y : State} {l : Label} {μ : PMF State}
    (h : sys^w.step y l μ) (x : State) :
    (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        (schedOf sys y l μ).haltMass (PMF.pure y) e *
          (if WeakScheduler.stateAfter e.1 (e.1.trans.length e.2) = x then 1 else 0)) = μ x :=
  ((schedOf_realises h).2.1 x).symm

/-! ### Structural helpers for the entry-configuration sum -/

omit [Silent Label] in
/-- Appending a nonempty (`cons`) segment never produces the empty sequence. -/
theorem append_cons_ne_nil {α : Type} (s : Seq α) (a : α) (t : Seq α) :
    s.append (Seq.cons a t) ≠ Seq.nil := by
  apply Stream'.Seq.recOn s
  · rw [Stream'.Seq.nil_append]; exact Stream'.Seq.cons_ne_nil
  · intro x s'; rw [Stream'.Seq.cons_append]; exact Stream'.Seq.cons_ne_nil

/-- A nonzero guarded weight `if P then a else 0` forces its guard `P` (local copy of
the `private` `of_ite_ne_zero` in `ExpandTrace`). -/
private theorem of_ite_ne_zero {P : Prop} [Decidable P] {a : ENNReal}
    (h : (if P then a else 0) ≠ 0) : P := by
  by_contra hP; rw [if_neg hP] at h; exact h rfl

/-- A nonzero guarded weight `if P then a else 0` has nonzero branch `a` (local copy of the
`private` `ne_zero_of_ite_ne_zero` in `ExpandTrace`). -/
private theorem ne_zero_of_ite_ne_zero {P : Prop} [Decidable P] {a : ENNReal}
    (h : (if P then a else 0) ≠ 0) : a ≠ 0 := by
  intro ha; rw [ha, ite_self] at h; exact h rfl

open Classical in
/-- The committed abstract execution always starts at `sys.init`. (`we` is `⟨init, nil⟩`
at the start and only ever grows by appending, never changing its `init`.) -/
private theorem reachAfter_we_init (ws : Scheduler sys^w) :
    ∀ (n : ℕ) (c : Config sys), reachAfter ws n c ≠ 0 → c.we.init = sys.init := by
  intro n
  induction n with
  | zero =>
    intro c hreach
    by_cases hcond : (c.we = (⟨sys.init, Seq.nil⟩ : AlterSeq State Label) ∧
        c.e = ⟨sys.init, Seq.nil⟩ ∧ c.e' = ⟨sys.init, Seq.nil⟩ ∧
        (∀ p, c.wt = some p → c.s = schedOf sys sys.init p.1 p.2) ∧
        (c.wt = none → c.s = Scheduler.halt sys))
    · rw [hcond.1]
    · simp only [reachAfter] at hreach; rw [if_neg hcond] at hreach; exact absurd rfl hreach
  | succ n ih =>
    intro c hreach
    rw [reachAfter] at hreach
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, reachAfter ws n c₀ * step ws c₀ c ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hreach (ENNReal.tsum_eq_zero.mpr hcon)
    rw [mul_ne_zero_iff] at hc₀
    obtain ⟨hreach₀, hstep⟩ := hc₀
    have hinit₀ := ih c₀ hreach₀
    obtain ⟨we₀, e₀, wt₀, s₀, e'₀, t₀⟩ := c₀
    cases wt₀ with
    | none => simp only [step] at hstep; exact absurd rfl hstep
    | some wtp =>
      obtain ⟨lw, μw⟩ := wtp
      cases t₀ with
      | none =>
        simp only [step] at hstep
        rw [(of_ite_ne_zero hstep).2.1]; exact hinit₀
      | some tp =>
        obtain ⟨l', μ'⟩ := tp
        simp only [step] at hstep
        rw [(of_ite_ne_zero hstep).1]; exact hinit₀

/-- The committed abstract execution of any reachable configuration starts at `sys.init`. -/
private theorem reachProb_we_init (ws : Scheduler sys^w) (c : Config sys)
    (h : reachProb ws c ≠ 0) : c.we.init = sys.init := by
  rw [reachProb] at h
  obtain ⟨n, hn⟩ : ∃ n, reachAfter ws n c ≠ 0 := by
    by_contra hcon; push Not at hcon; exact h (ENNReal.tsum_eq_zero.mpr hcon)
  exact reachAfter_we_init ws n c hn

open Classical in
/-- **No instruction lands on a "fresh entry of the empty execution".** A `step` into a
configuration whose committed `we` and current segment `e'` are both empty has weight `0`:
the inner instruction grows `e'` (to a `cons`), the outer instruction grows `we`, so
neither can produce `we.trans = nil ∧ e'.trans = nil`. -/
private theorem step_eq_zero_of_target_nil (ws : Scheduler sys^w) (c₀ c : Config sys)
    (hwe : c.we.trans = Seq.nil) (he' : c.e'.trans = Seq.nil) :
    step ws c₀ c = 0 := by
  obtain ⟨we₀, e₀, wt₀, s₀, e'₀, t₀⟩ := c₀
  cases wt₀ with
  | none => simp only [step]
  | some wtp =>
    obtain ⟨lw, μw⟩ := wtp
    cases t₀ with
    | none =>
      simp only [step]
      rw [if_neg]
      rintro ⟨_, hcwe, _, _, _⟩
      have heq := congrArg AlterSeq.trans hcwe
      rw [hwe] at heq
      exact append_cons_ne_nil _ _ _ heq.symm
    | some tp =>
      obtain ⟨l', μ'⟩ := tp
      simp only [step]
      rw [if_neg]
      rintro ⟨_, _, _, _, _, htrans⟩
      rw [he'] at htrans
      exact append_cons_ne_nil _ _ _ htrans.symm

open Classical in
/-- For a "fresh entry of the empty execution", the reaching probability collapses to the
start weight `reachAfter 0`: such a configuration is never produced by any instruction
(`step_eq_zero_of_target_nil`), so only the `n = 0` term survives in `reachProb`. -/
theorem reachProb_eq_reachAfter_zero (ws : Scheduler sys^w) (c : Config sys)
    (hwe : c.we.trans = Seq.nil) (he' : c.e'.trans = Seq.nil) :
    reachProb ws c = reachAfter ws 0 c := by
  rw [reachProb]
  refine tsum_eq_single 0 (fun n hn => ?_)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [reachAfter]
  refine ENNReal.tsum_eq_zero.mpr (fun c₀ => ?_)
  rw [step_eq_zero_of_target_nil ws c₀ c hwe he', mul_zero]

open Classical in
/-- The canonical **entry configuration** for the OUTER step from a predecessor that commits a
weak step into `we = weN`, with concrete prefix `e = eN`, reset state `y = last(eN)`, indexed by
the entry's free next-draws `(wt, t)`. Its initial-reset-point special case
(`weN = eN = ⟨init, nil⟩`, `y = init`) is `baseCfg` below; its `step`-weight from the predecessor
marginalises over `(wt, t)` to `1`. -/
noncomputable def entryCfg (sys : System State Label)
    (weN eN : AlterSeq State Label) (y : State)
    (wt t : Option (Label × PMF State)) : Config sys where
  we := weN
  e := eN
  wt := wt
  s := match wt with
       | none => Scheduler.halt sys
       | some p => schedOf sys y p.1 p.2
  e' := ⟨y, Seq.nil⟩
  t := t

open Classical in
/-- **Shared entry-draw reindexing.** For any weight `F` supported only on configurations of the
canonical entry shape (committed `we = W`, concrete prefix `e = E`, reset segment `e' = ⟨y, nil⟩`,
witness `s` pinned by `wt`), summing `F` over *all* configurations equals summing it over the free
draws `(wt, t)` via `entryCfg`. This is the common core of the four `(wt, t) ↦ entryCfg` reindexings
(`base_sum`, `base_entry_e_marg`, `step_entry_e_marg`, `entryStep_collapse`): injectivity from
`entryCfg`'s `(wt, t)` dependence, surjectivity by rebuilding any supported `c` as
`entryCfg W E y c.wt c.t`. -/
theorem entry_draw_reindex (F : Config sys → ENNReal)
    (W E : AlterSeq State Label) (y : State)
    (hpin : ∀ c, F c ≠ 0 → c.we = W ∧ c.e = E ∧ c.e' = ⟨y, Seq.nil⟩ ∧
        (∀ p, c.wt = some p → c.s = schedOf sys y p.1 p.2) ∧
        (c.wt = none → c.s = Scheduler.halt sys)) :
    (∑' c : Config sys, F c)
      = ∑' pr : Option (Label × PMF State) × Option (Label × PMF State),
          F (entryCfg sys W E y pr.1 pr.2) := by
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun pr => entryCfg sys W E y pr.1.1 pr.1.2) ?_ ?_ ?_
  · rintro ⟨⟨wa, ta⟩, _⟩ ⟨⟨wb, tb⟩, _⟩ hab
    exact Subtype.ext (Prod.ext (congrArg Config.wt hab) (congrArg Config.t hab))
  · intro c hc
    have hcne := Function.mem_support.mp hc
    obtain ⟨hwe, he, he', hsome, hnone⟩ := hpin c hcne
    have heq : entryCfg sys W E y c.wt c.t = c := by
      have hs : (match c.wt with
          | none => Scheduler.halt sys
          | some p => schedOf sys y p.1 p.2) = c.s := by
        rcases hw : c.wt with _ | p
        · exact (hnone hw).symm
        · exact (hsome p hw).symm
      obtain ⟨we, e, wt, s, e', t⟩ := c
      simp only at hwe he he' hs ⊢
      simp only [entryCfg, hwe, he, he', ← hs]
    exact ⟨⟨(c.wt, c.t), by
      change F (entryCfg sys W E y c.wt c.t) ≠ 0; rw [heq]; exact hcne⟩, heq⟩
  · intro pr; rfl

open Classical in
/-- The canonical **start configuration** for the draws `(wt, t)`: the initial-reset-point
special case of `entryCfg` (committed/segment executions all reset to `⟨sys.init, nil⟩`, witness
`s` pinned by `wt`). These are exactly the support of `reachAfter 0`, indexed by the free draws
`(wt, t)`. -/
private noncomputable def baseCfg (sys : System State Label)
    (wt t : Option (Label × PMF State)) : Config sys :=
  entryCfg sys ⟨sys.init, Seq.nil⟩ ⟨sys.init, Seq.nil⟩ sys.init wt t

open Classical in
/-- Summing the start weight `reachAfter 0` over the free first inner draw `t` (for a
fixed first weak draw `wt`) recovers the outer draw probability `ws.next ⟨init, nil⟩ wt`
(the inner draws of `s` — real `t` or halt — normalise to `1`). -/
private theorem baseCfg_inner_sum (ws : Scheduler sys^w) (wt : Option (Label × PMF State)) :
    (∑' t, reachAfter ws 0 (baseCfg sys wt t)) = ws.next ⟨sys.init, Seq.nil⟩ wt := by
  cases wt with
  | none =>
    have hval : ∀ t, reachAfter ws 0 (baseCfg sys none t)
        = ws.next ⟨sys.init, Seq.nil⟩ none * (if t = none then 1 else 0) := by
      intro t
      have hcond : (baseCfg sys none t).we = (⟨sys.init, Seq.nil⟩ : AlterSeq State Label) ∧
          (baseCfg sys none t).e = ⟨sys.init, Seq.nil⟩ ∧
          (baseCfg sys none t).e' = ⟨sys.init, Seq.nil⟩ ∧
          (∀ p, (baseCfg sys none t).wt = some p →
            (baseCfg sys none t).s = schedOf sys sys.init p.1 p.2) ∧
          ((baseCfg sys none t).wt = none → (baseCfg sys none t).s = Scheduler.halt sys) :=
        ⟨rfl, rfl, rfl, fun p hp => absurd hp (by simp [baseCfg, entryCfg]), fun _ => rfl⟩
      rw [reachAfter, if_pos hcond]; rfl
    simp only [hval, ENNReal.tsum_mul_left]
    rw [tsum_eq_single none (fun b hb => by rw [if_neg hb]), if_pos rfl, mul_one]
  | some p =>
    have hval : ∀ t, reachAfter ws 0 (baseCfg sys (some p) t)
        = ws.next ⟨sys.init, Seq.nil⟩ (some p)
          * (schedOf sys sys.init p.1 p.2).next ⟨sys.init, Seq.nil⟩ t := by
      intro t
      have hcond : (baseCfg sys (some p) t).we = (⟨sys.init, Seq.nil⟩ : AlterSeq State Label) ∧
          (baseCfg sys (some p) t).e = ⟨sys.init, Seq.nil⟩ ∧
          (baseCfg sys (some p) t).e' = ⟨sys.init, Seq.nil⟩ ∧
          (∀ p', (baseCfg sys (some p) t).wt = some p' →
            (baseCfg sys (some p) t).s = schedOf sys sys.init p'.1 p'.2) ∧
          ((baseCfg sys (some p) t).wt = none →
            (baseCfg sys (some p) t).s = Scheduler.halt sys) := by
        refine ⟨rfl, rfl, rfl, fun p' hp' => ?_,
          fun hp' => absurd hp' (by simp [baseCfg, entryCfg])⟩
        simp only [baseCfg, entryCfg] at hp' ⊢; rw [Option.some.inj hp']
      rw [reachAfter, if_pos hcond]; rfl
    simp only [hval, ENNReal.tsum_mul_left]
    rw [PMF.tsum_coe, mul_one]

open Classical in
/-- **The base entry-sum is `1`** (PLAN, base case RHS). The entries for the empty
weak-step list collapse to the `reachAfter 0` start configurations, indexed bijectively by
the free draws `(wt, t)` via `baseCfg`; the sum then factors through PMF normalisation. -/
theorem base_sum (ws : Scheduler sys^w) :
    (∑' c : {c : Config sys // c.we = ⟨sys.init, Seq.nil⟩ ∧ c.e'.trans = Seq.nil},
        reachProb ws c.1) = 1 := by
  have hcongr : (∑' c : {c : Config sys // c.we = ⟨sys.init, Seq.nil⟩ ∧ c.e'.trans = Seq.nil},
        reachProb ws c.1)
      = ∑' c : {c : Config sys // c.we = ⟨sys.init, Seq.nil⟩ ∧ c.e'.trans = Seq.nil},
          reachAfter ws 0 c.1 :=
    tsum_congr (fun c => reachProb_eq_reachAfter_zero ws c.1 (by rw [c.2.1]) c.2.2)
  rw [hcongr]
  have hbij : (∑' c : {c : Config sys // c.we = ⟨sys.init, Seq.nil⟩ ∧ c.e'.trans = Seq.nil},
        reachAfter ws 0 c.1)
      = ∑' pr : Option (Label × PMF State) × Option (Label × PMF State),
          reachAfter ws 0 (baseCfg sys pr.1 pr.2) :=
    (tsum_subtype_eq_of_support_subset (s := {c : Config sys |
        c.we = ⟨sys.init, Seq.nil⟩ ∧ c.e'.trans = Seq.nil}) (by
      intro c hc
      have hcne := Function.mem_support.mp hc
      simp only [reachAfter] at hcne
      obtain ⟨hwe, _, he', -, -⟩ := of_ite_ne_zero hcne
      exact ⟨hwe, congrArg AlterSeq.trans he'⟩)).trans
      (entry_draw_reindex (reachAfter ws 0) ⟨sys.init, Seq.nil⟩ ⟨sys.init, Seq.nil⟩ sys.init (by
      intro c hcne
      simp only [reachAfter] at hcne
      obtain ⟨hwe, he, he', hsome, hnone⟩ := of_ite_ne_zero hcne
      exact ⟨hwe, he, he', hsome, hnone⟩))
  rw [hbij, ENNReal.tsum_prod']
  simp only [baseCfg_inner_sum]
  exact (ws.next ⟨sys.init, Seq.nil⟩).tsum_coe

open Classical in
/-- **Fixpoint / one-unfolding equation for `reachProb`.** Splitting the instruction-count
sum at `n = 0` exposes the start weight plus one application of the transition kernel `step`:
`reachProb c = reachAfter 0 c + ∑' c₀, reachProb c₀ · step c₀ c`. (The `n ≥ 1` tail is
`∑' n, ∑' c₀, reachAfter n c₀ · step c₀ c`; commuting the sums and pulling out `step` rebuilds
`reachProb c₀`.) This is the entry point for the step-case decomposition. -/
theorem reachProb_fixpoint (ws : Scheduler sys^w) (c : Config sys) :
    reachProb ws c = reachAfter ws 0 c + ∑' c₀, reachProb ws c₀ * step ws c₀ c := by
  rw [reachProb, tsum_eq_zero_add' ENNReal.summable]
  congr 1
  rw [show (∑' b, reachAfter ws (b + 1) c)
        = ∑' b, ∑' c₀, reachAfter ws b c₀ * step ws c₀ c from
      tsum_congr (fun b => by rw [reachAfter]),
    ENNReal.tsum_comm]
  refine tsum_congr (fun c₀ => ?_)
  rw [reachProb, ENNReal.tsum_mul_right]

/-! ### Helpers for the inner-loop recursion (A1) -/

omit [Silent Label] in
/-- If a family `f` factors pointwise as `f i = A * p i` against a PMF `p`, then the
constant `A` is recovered as `∑' i, f i` (the `p`-marginal normalises to `1`), so
`f i = (∑' i, f i) * p i`. -/
private theorem tsum_eq_factor {ι : Type*} (p : PMF ι) (A : ENNReal)
    (f : ι → ENNReal) (hf : ∀ i, f i = A * p i) (i : ι) :
    f i = (∑' j, f j) * p i := by
  have hsum : (∑' j, f j) = A := by
    simp only [hf]; rw [ENNReal.tsum_mul_left, p.tsum_coe, mul_one]
  rw [hsum, hf i]

omit [Silent Label] in
/-- If `s.append s'` terminates then so does its prefix `s` (an infinite `s` would make the
append infinite, since `get?` agrees with `s` before `s` terminates). -/
theorem terminates_of_append_terminates {α : Type} {s s' : Seq α}
    (h : (s.append s').Terminates) : s.Terminates := by
  by_contra hs
  rw [Stream'.Seq.not_terminates_iff] at hs
  obtain ⟨N, hN⟩ := h
  have hnt : ¬ s.TerminatedAt N := by
    intro hT
    have hsN := hs N
    rw [Stream'.Seq.TerminatedAt] at hT
    rw [hT] at hsN
    simp at hsN
  have hagree := Stream'.Seq.get?_append_before_length (s := s) (s' := s') hnt
  rw [Stream'.Seq.TerminatedAt, hagree] at hN
  exact hnt hN

omit [Silent Label] in
/-- `lastOf` of an execution extended by one transition `(l, s)` is `s`. -/
theorem lastOf_append_singleton (e : AlterSeq State Label) (h : e.trans.Terminates)
    (l : Label) (s : State) :
    lastOf (⟨e.init, e.trans.append (Seq.cons (l, s) Seq.nil)⟩ : AlterSeq State Label) = s := by
  unfold lastOf
  rw [dif_pos ⟨_, Stream'.Seq.terminatedAt_append_find h
    (show (Seq.cons (l, s) Seq.nil).TerminatedAt 1 from rfl)⟩]
  exact AlterSeq.endState_append_singleton e h l s

open Classical in
/-- **Step weight into an entry-config factors through the inner draw `t`.** For an entry
config `c'` (`c'.e'.trans = nil`, active weak step `c'.wt = some p`), the `step` weight into
`{c' with t := t}` is `(t-marginal) * c'.s.next c'.e' t`: the inner draw appears only as the
`s.next` factor (INNER can't land on `e'.trans = nil`; OUTER's `match` selects the `s.next`
branch). -/
private theorem step_entryT_factor (ws : Scheduler sys^w) (c' : Config sys)
    (he' : c'.e'.trans = Seq.nil) (p : Label × PMF State) (hwt : c'.wt = some p)
    (c₀ : Config sys) (t : Option (Label × PMF State)) :
    step ws c₀ {c' with t := t}
      = (∑' t', step ws c₀ {c' with t := t'}) * c'.s.next c'.e' t := by
  have hex : ∃ A, ∀ t, step ws c₀ {c' with t := t} = A * c'.s.next c'.e' t := by
    obtain ⟨we₀, e₀, wt₀, s₀, e'₀, t₀⟩ := c₀
    cases wt₀ with
    | none => exact ⟨0, fun t => by simp only [step]; rw [zero_mul]⟩
    | some wtp =>
      obtain ⟨lw, μw⟩ := wtp
      cases t₀ with
      | some tp =>
        obtain ⟨l', μ'⟩ := tp
        refine ⟨0, fun t => ?_⟩
        rw [zero_mul]
        simp only [step]
        rw [if_neg]
        rintro ⟨-, -, -, -, -, htr⟩
        rw [he'] at htr
        exact append_cons_ne_nil _ _ _ htr.symm
      | none =>
        by_cases hg : c'.e = (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label) ∧
            c'.we = (⟨we₀.init, we₀.trans.append (Seq.cons
              (lw, lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label))
              Seq.nil)⟩ : AlterSeq State Label) ∧
            c'.e' = (⟨lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label),
              Seq.nil⟩ : AlterSeq State Label) ∧
            (∀ q, c'.wt = some q → c'.s = schedOf sys
              (lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label)) q.1 q.2) ∧
            (c'.wt = none → c'.s = Scheduler.halt sys)
        · refine ⟨ws.next (⟨we₀.init, we₀.trans.append (Seq.cons
              (lw, lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label))
              Seq.nil)⟩ : AlterSeq State Label) (some p), fun t => ?_⟩
          simp only [step]
          rw [if_pos hg]
          simp only [hwt]
        · exact ⟨0, fun t => by simp only [step]; rw [if_neg hg, zero_mul]⟩
  obtain ⟨A, hA⟩ := hex
  exact tsum_eq_factor (c'.s.next c'.e') A _ hA t

open Classical in
/-- **(A1base) Entry-config inner-draw factorisation.** For an entry config `c'`
(`c'.e'.trans = nil`, active weak step `c'.wt = some p`), `reachProb` of `{c' with t := t}`
factors as the `t`-marginal predraw times the inner draw `c'.s.next c'.e' t`. -/
private theorem seg_entry_factor (ws : Scheduler sys^w) (c' : Config sys)
    (he' : c'.e'.trans = Seq.nil) (p : Label × PMF State) (hwt : c'.wt = some p)
    (t : Option (Label × PMF State)) :
    reachProb ws {c' with t := t}
      = (∑' t', reachProb ws {c' with t := t'}) * c'.s.next c'.e' t := by
  have hex : ∀ n, ∃ A, ∀ t, reachAfter ws n {c' with t := t} = A * c'.s.next c'.e' t := by
    intro n
    cases n with
    | zero =>
      by_cases hg : c'.we = (⟨sys.init, Seq.nil⟩ : AlterSeq State Label) ∧
          c'.e = (⟨sys.init, Seq.nil⟩ : AlterSeq State Label) ∧
          c'.e' = (⟨sys.init, Seq.nil⟩ : AlterSeq State Label) ∧
          (∀ q, c'.wt = some q → c'.s = schedOf sys sys.init q.1 q.2) ∧
          (c'.wt = none → c'.s = Scheduler.halt sys)
      · refine ⟨ws.next ⟨sys.init, Seq.nil⟩ (some p), fun t => ?_⟩
        simp only [reachAfter]
        rw [if_pos hg]
        simp only [hwt]
      · exact ⟨0, fun t => by simp only [reachAfter]; rw [if_neg hg, zero_mul]⟩
    | succ m =>
      refine ⟨∑' c₀, reachAfter ws m c₀ * (∑' t', step ws c₀ {c' with t := t'}), fun t => ?_⟩
      rw [reachAfter]
      rw [show (∑' c₀, reachAfter ws m c₀ * step ws c₀ {c' with t := t})
            = ∑' c₀, (reachAfter ws m c₀ * (∑' t', step ws c₀ {c' with t := t'}))
                * c'.s.next c'.e' t from
          tsum_congr (fun c₀ => by rw [step_entryT_factor ws c' he' p hwt c₀ t, ← mul_assoc])]
      rw [ENNReal.tsum_mul_right]
  have R_after : ∀ n t, reachAfter ws n {c' with t := t}
      = (∑' t', reachAfter ws n {c' with t := t'}) * c'.s.next c'.e' t := by
    intro n t
    obtain ⟨A, hA⟩ := hex n
    exact tsum_eq_factor (c'.s.next c'.e') A _ hA t
  rw [reachProb, tsum_congr (fun n => R_after n t), ENNReal.tsum_mul_right]
  congr 1
  rw [ENNReal.tsum_comm]
  exact tsum_congr (fun t' => by rw [reachProb])

open Classical in
/-- **(A1) Inner-loop recursion.** For `c` with an active weak step `c.wt = some (l, μ)`,
segment `c.e'` starting at `lastOf c.e` and ending wherever (`c.e'.trans = ofList L`),
`reachProb c` factors as the entry predraw (the `t`-marginal at the reset point
`e' = ⟨lastOf c.e, nil⟩`) times the witness `probOf` of the segment times the final inner
draw `c.s.next c.e' c.t`. Proved by reverse induction on the segment, peeling INNER steps. -/
theorem seg_inner_recursion (ws : Scheduler sys^w) (l : Label) (μ : PMF State)
    (L : List (Label × State)) :
    ∀ (c : Config sys) (hfin : c.e'.trans.Terminates),
      c.wt = some (l, μ) → c.e'.init = lastOf c.e → c.e'.trans = Seq.ofList L →
      reachProb ws c
        = (∑' t, reachProb ws {c with e' := ⟨lastOf c.e, Seq.nil⟩, t := t})
          * (⟨PMF.pure (lastOf c.e), c.s⟩ : ProbabilisticExecution sys).probOf c.e' hfin
          * c.s.next c.e' c.t := by
  induction L using List.reverseRecOn with
  | nil =>
    intro c hfin hwt hinit hL
    have he' : c.e'.trans = Seq.nil := by rw [hL, Stream'.Seq.ofList_nil]
    have hce' : c.e' = (⟨lastOf c.e, Seq.nil⟩ : AlterSeq State Label) := by
      rw [← hinit, ← he']
    have hprob : (⟨PMF.pure (lastOf c.e), c.s⟩ : ProbabilisticExecution sys).probOf c.e' hfin
        = 1 := by
      rw [ProbabilisticExecution.probOf_congr _ c.e' ⟨lastOf c.e, Seq.nil⟩ hce' hfin
          Stream'.Seq.terminates_nil, ProbabilisticExecution.probOf_nil]
      change (PMF.pure (lastOf c.e)) (lastOf c.e) = 1
      exact PMF.pure_apply_self _
    rw [hprob, mul_one]
    have hkey := seg_entry_factor ws c he' (l, μ) hwt c.t
    rw [show ({c with t := c.t} : Config sys) = c from rfl] at hkey
    rw [hkey]
    congr 1
    exact tsum_congr (fun t => by rw [← hce'])
  | append_singleton sq last ih =>
    intro c hfin hwt hinit hL
    obtain ⟨l', s'⟩ := last
    have hofl : (Seq.ofList (sq ++ [(l', s')]) : Seq (Label × State))
        = (Seq.ofList sq).append (Seq.cons (l', s') Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have hetrans : c.e'.trans = (Seq.ofList sq).append (Seq.cons (l', s') Seq.nil) := by
      rw [hL, hofl]
    have hsqfin : (Seq.ofList sq : Seq (Label × State)).Terminates :=
      Stream'.Seq.terminates_ofList sq
    have hlast : lastOf c.e' = s' := by
      have hce'eq : c.e'
          = (⟨c.e'.init, (Seq.ofList sq).append (Seq.cons (l', s') Seq.nil)⟩
            : AlterSeq State Label) := by rw [← hetrans]
      rw [hce'eq]; exact lastOf_append_singleton ⟨c.e'.init, Seq.ofList sq⟩ hsqfin l' s'
    -- The peeled predecessor (one fewer inner step), parametrised by the inner draw `μ'`.
    set cMinus : PMF State → Config sys :=
      fun μ' => {c with e' := ⟨c.e'.init, Seq.ofList sq⟩, t := some (l', μ')} with hcMinus
    -- `step` from `cMinus μ'` into `c` (the INNER instruction that grew the last transition).
    have hstepMinus : ∀ μ', step ws (cMinus μ') c = μ' s' * c.s.next c.e' c.t := by
      intro μ'
      simp only [hcMinus, step, hwt]
      rw [if_pos ⟨trivial, trivial, trivial, trivial, trivial, by rw [hlast]; exact hetrans⟩,
        hlast]
    rw [reachProb_fixpoint]
    have h0 : reachAfter ws 0 c = 0 := by
      rw [reachAfter, if_neg]
      rintro ⟨-, -, hce'eq, -, -⟩
      have hnil : c.e'.trans = Seq.nil := by rw [hce'eq]
      rw [hetrans] at hnil
      exact append_cons_ne_nil _ _ _ hnil
    rw [h0, zero_add]
    -- **Reindex** the predecessor sum by the inner draw `μ'`.
    rw [show (∑' c₀, reachProb ws c₀ * step ws c₀ c)
          = ∑' μ', reachProb ws (cMinus μ') * (μ' s' * c.s.next c.e' c.t) from ?_]
    · -- **Apply IH** to each `cMinus μ'`, then collapse the kernel sum into `probOf c.e'`.
      have hIH : ∀ μ', reachProb ws (cMinus μ')
          = (∑' t, reachProb ws {c with e' := ⟨lastOf c.e, Seq.nil⟩, t := t})
            * (⟨PMF.pure (lastOf c.e), c.s⟩ : ProbabilisticExecution sys).probOf
                ⟨c.e'.init, Seq.ofList sq⟩ hsqfin
            * c.s.next ⟨c.e'.init, Seq.ofList sq⟩ (some (l', μ')) := by
        intro μ'
        rw [ih (cMinus μ') hsqfin hwt hinit rfl]
      rw [tsum_congr (fun μ' => by rw [hIH μ'])]
      -- Pull out the constants and collapse `∑' μ', s.next … (some (l', μ')) * μ' s' = kernel`.
      rw [show (∑' μ', (∑' t, reachProb ws {c with e' := ⟨lastOf c.e, Seq.nil⟩, t := t})
              * (⟨PMF.pure (lastOf c.e), c.s⟩ : ProbabilisticExecution sys).probOf
                  ⟨c.e'.init, Seq.ofList sq⟩ hsqfin
              * c.s.next ⟨c.e'.init, Seq.ofList sq⟩ (some (l', μ'))
              * (μ' s' * c.s.next c.e' c.t))
            = ((∑' t, reachProb ws {c with e' := ⟨lastOf c.e, Seq.nil⟩, t := t})
                * (⟨PMF.pure (lastOf c.e), c.s⟩ : ProbabilisticExecution sys).probOf
                    ⟨c.e'.init, Seq.ofList sq⟩ hsqfin
                * c.s.next c.e' c.t)
              * ∑' μ', c.s.next ⟨c.e'.init, Seq.ofList sq⟩ (some (l', μ')) * μ' s' from by
          rw [← ENNReal.tsum_mul_left]; exact tsum_congr (fun μ' => by ring)]
      -- The remaining `μ'`-sum is the one-step kernel; fold it into `probOf c.e'`.
      rw [show (∑' μ', c.s.next ⟨c.e'.init, Seq.ofList sq⟩ (some (l', μ')) * μ' s')
            = (⟨PMF.pure (lastOf c.e), c.s⟩ : ProbabilisticExecution sys).kernel
                ⟨c.e'.init, Seq.ofList sq⟩ (l', s') from rfl]
      rw [show (⟨PMF.pure (lastOf c.e), c.s⟩ : ProbabilisticExecution sys).probOf c.e' hfin
            = (⟨PMF.pure (lastOf c.e), c.s⟩ : ProbabilisticExecution sys).probOf
                  ⟨c.e'.init, Seq.ofList sq⟩ hsqfin
              * (⟨PMF.pure (lastOf c.e), c.s⟩ : ProbabilisticExecution sys).kernel
                  ⟨c.e'.init, Seq.ofList sq⟩ (l', s') from ?_]
      · ring
      · rw [ProbabilisticExecution.probOf_congr _ c.e'
            ⟨c.e'.init, (Seq.ofList sq).append (Seq.cons (l', s') Seq.nil)⟩ (by rw [← hetrans]) hfin
            (by rw [← hetrans]; exact hfin),
          ProbabilisticExecution.probOf_append_singleton _ c.e'.init (Seq.ofList sq) hsqfin
            (l', s') (by rw [← hetrans]; exact hfin)]
    · -- **The reindex bijection** `c₀ ↦ μ'` on the support of `c₀ ↦ reachProb c₀ * step c₀ c`.
      refine tsum_eq_tsum_of_ne_zero_bij (i := fun x => cMinus x.1) ?_ ?_ ?_
      · intro a b hab
        have ht := congrArg Config.t hab
        simp only [hcMinus] at ht
        exact Subtype.ext (Prod.mk.inj (Option.some.inj ht)).2
      · intro c₀ hc₀
        have hstep : step ws c₀ c ≠ 0 := by
          intro h
          exact (Function.mem_support.mp hc₀) (by rw [h, mul_zero])
        obtain ⟨we₀, e₀, wt₀, s₀, e'₀, t₀⟩ := c₀
        cases wt₀ with
        | none => simp only [step] at hstep; exact absurd rfl hstep
        | some wtp =>
          obtain ⟨lw, μw⟩ := wtp
          cases t₀ with
          | none =>
            exfalso
            simp only [step] at hstep
            obtain ⟨-, -, hce'eq, -, -⟩ := of_ite_ne_zero hstep
            have hnil : c.e'.trans = Seq.nil := by rw [hce'eq]
            rw [hetrans] at hnil
            exact append_cons_ne_nil _ _ _ hnil
          | some tp =>
            obtain ⟨l'', μ''⟩ := tp
            simp only [step] at hstep
            obtain ⟨hwe, he, hcwt, hcs, he'i, he't⟩ := of_ite_ne_zero hstep
            rw [hlast] at he't
            have he't' : e'₀.trans.append (Seq.cons (l'', s') Seq.nil)
                = (Seq.ofList sq).append (Seq.cons (l', s') Seq.nil) := by
              rw [← he't, hetrans]
            have he'₀fin : e'₀.trans.Terminates :=
              terminates_of_append_terminates (he't ▸ hfin)
            have hsqeq : e'₀.trans = Seq.ofList sq :=
              Stream'.Seq.append_singleton_inj_left _ _ he'₀fin hsqfin _ _ he't'
            have hlleq : (l'', s') = (l', s') :=
              Stream'.Seq.append_singleton_inj_right _ _ he'₀fin hsqfin _ _ he't'
            have hl'' : l'' = l' := congrArg Prod.fst hlleq
            have hc₀eq : cMinus μ''
                = (⟨we₀, e₀, some (lw, μw), s₀, e'₀, some (l'', μ'')⟩ : Config sys) := by
              simp only [hcMinus]
              show (⟨c.we, c.e, c.wt, c.s, ⟨c.e'.init, Seq.ofList sq⟩, some (l', μ'')⟩
                  : Config sys)
                = ⟨we₀, e₀, some (lw, μw), s₀, e'₀, some (l'', μ'')⟩
              rw [hwe, he, hcwt, hcs, hl'']
              congr 1
              rw [he'i, ← hsqeq]
            refine ⟨⟨μ'', ?_⟩, hc₀eq⟩
            rw [Function.mem_support, ← hstepMinus μ'', hc₀eq]
            exact Function.mem_support.mp hc₀
      · rintro ⟨μ', -⟩
        change reachProb ws (cMinus μ') * step ws (cMinus μ') c
          = reachProb ws (cMinus μ') * (μ' s' * c.s.next c.e' c.t)
        rw [hstepMinus μ']

open Classical in
/-- Summing the OUTER `step` weight from a right-shaped predecessor into the canonical
`entryCfg` over the free first inner draw `t` (for a fixed outer draw `wt`) recovers the outer
draw probability `ws.next weN wt`. The analogue of `baseCfg_inner_sum` for the `step` kernel. -/
theorem entryCfg_step_inner (ws : Scheduler sys^w)
    (we₀ e₀ e'₀ : AlterSeq State Label) (lw : Label) (μw : PMF State) (s₀ : Scheduler sys)
    (wt : Option (Label × PMF State)) :
    let eN : AlterSeq State Label := ⟨e₀.init, e₀.trans.append e'₀.trans⟩
    let weN : AlterSeq State Label :=
      ⟨we₀.init, we₀.trans.append (Seq.cons (lw, lastOf eN) Seq.nil)⟩
    (∑' t, step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩
        (entryCfg sys weN eN (lastOf eN) wt t)) = ws.next weN wt := by
  intro eN weN
  cases wt with
  | none =>
    have hval : ∀ t, step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩
        (entryCfg sys weN eN (lastOf eN) none t)
        = ws.next weN none * (if t = none then 1 else 0) := by
      intro t
      simp only [step]
      rw [if_pos ?_]
      · rfl
      · exact ⟨rfl, rfl, rfl, fun p hp => absurd hp (by simp [entryCfg]), fun _ => rfl⟩
    simp only [hval, ENNReal.tsum_mul_left]
    rw [tsum_eq_single none (fun b hb => by rw [if_neg hb]), if_pos rfl, mul_one]
  | some p =>
    have hval : ∀ t, step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩
        (entryCfg sys weN eN (lastOf eN) (some p) t)
        = ws.next weN (some p)
          * (schedOf sys (lastOf eN) p.1 p.2).next ⟨lastOf eN, Seq.nil⟩ t := by
      intro t
      simp only [step]
      rw [if_pos ?_]
      · rfl
      · refine ⟨rfl, rfl, rfl, fun p' hp' => ?_, fun hp' => absurd hp' (by simp [entryCfg])⟩
        simp only [entryCfg] at hp' ⊢; rw [Option.some.inj hp']
    simp only [hval, ENNReal.tsum_mul_left]
    rw [PMF.tsum_coe, mul_one]

open Classical in
/-- **(A2-step) Entry-step marginal.** Marginalising the inner draw `t` of the `step` weight from
`c₀` into the canonical entry config at `(⟨init, ofList L'⟩, E)` equals the total entry-`L'` step
mass (over entries sharing `E`) times the outer draw `ws.next ⟨init, ofList L'⟩ (some (l, μ))`. -/
private theorem step_entry_e_marg (ws : Scheduler sys^w) (L' : List (Label × State))
    (l : Label) (μ : PMF State) (E : AlterSeq State Label) (c₀ : Config sys) :
    (∑' t, step ws c₀ (entryCfg sys ⟨sys.init, Seq.ofList L'⟩ E (lastOf E) (some (l, μ)) t))
      = (∑' c' : {c' : Config sys //
            c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = E},
          step ws c₀ c'.1)
        * ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) := by
  obtain ⟨we₀, e₀, wt₀, s₀, e'₀, t₀⟩ := c₀
  cases wt₀ with
  | none => simp only [step, tsum_zero, zero_mul]
  | some wtp =>
    obtain ⟨lw, μw⟩ := wtp
    cases t₀ with
    | some tp =>
      obtain ⟨l', μ'⟩ := tp
      rw [show (∑' t, step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, some (l', μ')⟩
              (entryCfg sys ⟨sys.init, Seq.ofList L'⟩ E (lastOf E) (some (l, μ)) t)) = 0 from
          ENNReal.tsum_eq_zero.mpr (fun t => by
            simp only [step]; rw [if_neg]; rintro ⟨-, -, -, -, -, htr⟩
            exact append_cons_ne_nil _ _ _ htr.symm),
        show (∑' c' : {c' : Config sys //
              c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = E},
              step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, some (l', μ')⟩ c'.1) = 0 from
          ENNReal.tsum_eq_zero.mpr (fun c' => by
            simp only [step]; rw [if_neg]; rintro ⟨-, -, -, -, -, htr⟩
            rw [c'.2.2.1] at htr
            exact append_cons_ne_nil _ _ _ htr.symm),
        zero_mul]
    | none =>
      by_cases hg : (⟨we₀.init, we₀.trans.append (Seq.cons
            (lw, lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label))
            Seq.nil)⟩ : AlterSeq State Label) = ⟨sys.init, Seq.ofList L'⟩ ∧
          (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label) = E
      · have hLHS : (∑' t, step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩
              (entryCfg sys ⟨sys.init, Seq.ofList L'⟩ E (lastOf E) (some (l, μ)) t))
            = ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) := by
          rw [tsum_congr (fun t => by rw [← hg.1, ← hg.2]), ← hg.1]
          exact entryCfg_step_inner ws we₀ e₀ e'₀ lw μw s₀ (some (l, μ))
        rw [hLHS,
          show (∑' c' : {c' : Config sys //
                c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = E},
                step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩ c'.1) = 1 from ?_, one_mul]
        rw [show (∑' c' : {c' : Config sys //
                c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = E},
                step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩ c'.1)
              = ∑' pr : Option (Label × PMF State) × Option (Label × PMF State),
                  step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩
                    (entryCfg sys ⟨we₀.init, we₀.trans.append (Seq.cons (lw,
                        lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label))
                        Seq.nil)⟩ ⟨e₀.init, e₀.trans.append e'₀.trans⟩
                      (lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label))
                      pr.1 pr.2) from ?_]
        · rw [ENNReal.tsum_prod',
            tsum_congr (fun wt => entryCfg_step_inner ws we₀ e₀ e'₀ lw μw s₀ wt)]
          exact (ws.next _).tsum_coe
        · exact (tsum_subtype_eq_of_support_subset (s := {c : Config sys |
              c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil ∧ c.e = E}) (by
            intro c hc
            have hcne : step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩ c ≠ 0 := hc
            simp only [step] at hcne
            obtain ⟨he, hwe2, he', -, -⟩ := of_ite_ne_zero hcne
            exact ⟨hg.1 ▸ hwe2, congrArg AlterSeq.trans he', hg.2 ▸ he⟩)).trans
            (entry_draw_reindex (step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩)
              ⟨we₀.init, we₀.trans.append (Seq.cons (lw,
                  lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label))
                  Seq.nil)⟩ ⟨e₀.init, e₀.trans.append e'₀.trans⟩
                (lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label)) (by
            intro c hcne
            simp only [step] at hcne
            obtain ⟨he, hwe2, he', hsome, hnone⟩ := of_ite_ne_zero hcne
            exact ⟨hwe2, he, he', hsome, hnone⟩))
      · rw [show (∑' t, step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩
                (entryCfg sys ⟨sys.init, Seq.ofList L'⟩ E (lastOf E) (some (l, μ)) t)) = 0 from
            ENNReal.tsum_eq_zero.mpr (fun t => by
              simp only [step, entryCfg]; rw [if_neg]; rintro ⟨he, hwe2, -, -, -⟩
              exact hg ⟨hwe2.symm, he.symm⟩),
          show (∑' c' : {c' : Config sys //
                c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = E},
                step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩ c'.1) = 0 from
            ENNReal.tsum_eq_zero.mpr (fun c' => by
              simp only [step]; rw [if_neg]; rintro ⟨he, hwe2, -, -, -⟩
              exact hg ⟨hwe2.symm.trans c'.2.1, he.symm.trans c'.2.2.2⟩),
          zero_mul]

omit [Silent Label] in
/-- `lastOf ⟨y, nil⟩ = y`. -/
private theorem lastOf_nil (y : State) :
    lastOf (⟨y, Seq.nil⟩ : AlterSeq State Label) = y := by
  unfold lastOf
  rw [dif_pos Stream'.Seq.terminates_nil]
  exact AlterSeq.endState_of_trans_nil _ rfl _

open Classical in
/-- **(A2-base) Entry-base marginal.** The `reachAfter 0` analogue of `step_entry_e_marg`:
marginalising the inner draw `t` of the start weight of the canonical entry config at
`(⟨init, ofList L'⟩, E)` equals the total entry-`L'` start mass (over entries sharing `E`) times
`ws.next ⟨init, ofList L'⟩ (some (l, μ))`. Nonzero only at the start (`L' = []`, `E = ⟨init, nil⟩`),
where it reduces to `baseCfg`/`base_sum`. -/
private theorem base_entry_e_marg (ws : Scheduler sys^w) (L' : List (Label × State))
    (l : Label) (μ : PMF State) (E : AlterSeq State Label) :
    (∑' t, reachAfter ws 0 (entryCfg sys ⟨sys.init, Seq.ofList L'⟩ E (lastOf E) (some (l, μ)) t))
      = (∑' c' : {c' : Config sys //
            c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = E},
          reachAfter ws 0 c'.1)
        * ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) := by
  by_cases hg : (⟨sys.init, Seq.ofList L'⟩ : AlterSeq State Label) = ⟨sys.init, Seq.nil⟩ ∧
      E = (⟨sys.init, Seq.nil⟩ : AlterSeq State Label)
  · have hbase_eq : ∀ t, entryCfg sys ⟨sys.init, Seq.ofList L'⟩ E (lastOf E) (some (l, μ)) t
        = baseCfg sys (some (l, μ)) t := by
      intro t; rw [hg.1, hg.2, lastOf_nil]; rfl
    rw [tsum_congr (fun t => by rw [hbase_eq t]), baseCfg_inner_sum,
      show (∑' c' : {c' : Config sys //
            c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = E},
            reachAfter ws 0 c'.1) = 1 from ?_, one_mul, hg.1]
    rw [show (∑' c' : {c' : Config sys //
            c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = E},
            reachAfter ws 0 c'.1)
          = ∑' pr : Option (Label × PMF State) × Option (Label × PMF State),
              reachAfter ws 0 (baseCfg sys pr.1 pr.2) from ?_]
    · rw [ENNReal.tsum_prod']
      simp only [baseCfg_inner_sum]
      exact (ws.next ⟨sys.init, Seq.nil⟩).tsum_coe
    · exact (tsum_subtype_eq_of_support_subset (s := {c : Config sys |
          c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil ∧ c.e = E}) (by
        intro c hc
        have hcne := Function.mem_support.mp hc
        simp only [reachAfter] at hcne
        obtain ⟨hwe, he, he', -, -⟩ := of_ite_ne_zero hcne
        exact ⟨hwe.trans hg.1.symm, congrArg AlterSeq.trans he', he.trans hg.2.symm⟩)).trans
        (entry_draw_reindex (reachAfter ws 0) ⟨sys.init, Seq.nil⟩ ⟨sys.init, Seq.nil⟩ sys.init (by
        intro c hcne
        simp only [reachAfter] at hcne
        obtain ⟨hwe, he, he', hsome, hnone⟩ := of_ite_ne_zero hcne
        exact ⟨hwe, he, he', hsome, hnone⟩))
  · rw [show (∑' t, reachAfter ws 0
            (entryCfg sys ⟨sys.init, Seq.ofList L'⟩ E (lastOf E) (some (l, μ)) t)) = 0 from
        ENNReal.tsum_eq_zero.mpr (fun t => by
          simp only [reachAfter]; rw [if_neg]; rintro ⟨hwe2, he2, -, -, -⟩
          exact hg ⟨hwe2, he2⟩),
      show (∑' c' : {c' : Config sys //
            c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = E},
            reachAfter ws 0 c'.1) = 0 from
        ENNReal.tsum_eq_zero.mpr (fun c' => by
          simp only [reachAfter]; rw [if_neg]; rintro ⟨hwe2, he2, -, -, -⟩
          exact hg ⟨c'.2.1.symm.trans hwe2, c'.2.2.2.symm.trans he2⟩),
      zero_mul]

open Classical in
/-- **(A2) Entry-draw factorisation.** Marginalising the inner draw `t` of the entry config
`{c with e' := reset, t}` (active step `c.wt = some (l, μ)`, committed `c.we = ⟨init, ofList L'⟩`)
recovers the entry-`L'` predecessor mass (over all entries sharing `c.e`) times the probability
`ws` assigns at `⟨init, ofList L'⟩` to drawing `(l, μ)`. The outer first-weak-draw
marginalisation. -/
theorem seg_entry_draw (ws : Scheduler sys^w)
    (L' : List (Label × State)) (l : Label) (μ : PMF State) (c : Config sys)
    (hwe : c.we = ⟨sys.init, Seq.ofList L'⟩) (hwt : c.wt = some (l, μ))
    (hs : c.s = schedOf sys (lastOf c.e) l μ) :
    (∑' t, reachProb ws {c with e' := ⟨lastOf c.e, Seq.nil⟩, t := t})
      = (∑' c' : {c' : Config sys //
            c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = c.e},
          reachProb ws c'.1)
        * ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) := by
  have hRA : ∀ (m : ℕ) (d : Config sys),
      reachAfter ws (m + 1) d = ∑' c₀, reachAfter ws m c₀ * step ws c₀ d := fun _ _ => rfl
  have hRP : ∀ d : Config sys, reachProb ws d = ∑' n, reachAfter ws n d := fun _ => rfl
  have hentAt : ∀ t, ({c with e' := ⟨lastOf c.e, Seq.nil⟩, t := t} : Config sys)
      = entryCfg sys ⟨sys.init, Seq.ofList L'⟩ c.e (lastOf c.e) (some (l, μ)) t := by
    intro t; rw [hwe, hwt, hs]; rfl
  have hlevel : ∀ n, (∑' t, reachAfter ws n {c with e' := ⟨lastOf c.e, Seq.nil⟩, t := t})
      = (∑' c' : {c' : Config sys //
          c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = c.e},
        reachAfter ws n c'.1) * ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) := by
    intro n
    rw [tsum_congr (fun t => by rw [hentAt t])]
    cases n with
    | zero => exact base_entry_e_marg ws L' l μ c.e
    | succ m =>
      rw [tsum_congr (fun t => hRA m _), ENNReal.tsum_comm,
        tsum_congr (fun c₀ => by
          rw [ENNReal.tsum_mul_left, step_entry_e_marg ws L' l μ c.e c₀, ← mul_assoc]),
        ENNReal.tsum_mul_right]
      congr 1
      rw [tsum_congr (fun c' : {c' : Config sys //
          c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = c.e} =>
            hRA m c'.1), ENNReal.tsum_comm]
      exact tsum_congr (fun c₀ => (ENNReal.tsum_mul_left).symm)
  calc (∑' t, reachProb ws {c with e' := ⟨lastOf c.e, Seq.nil⟩, t := t})
      = ∑' t, ∑' n, reachAfter ws n {c with e' := ⟨lastOf c.e, Seq.nil⟩, t := t} :=
        tsum_congr (fun t => hRP _)
    _ = ∑' n, ∑' t, reachAfter ws n {c with e' := ⟨lastOf c.e, Seq.nil⟩, t := t} :=
        ENNReal.tsum_comm
    _ = ∑' n, (∑' c' : {c' : Config sys //
            c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = c.e},
          reachAfter ws n c'.1) * ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) :=
        tsum_congr hlevel
    _ = (∑' n, ∑' c' : {c' : Config sys //
            c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = c.e},
          reachAfter ws n c'.1) * ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) :=
        ENNReal.tsum_mul_right
    _ = (∑' c' : {c' : Config sys //
            c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = c.e},
          ∑' n, reachAfter ws n c'.1) * ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) := by
        rw [ENNReal.tsum_comm]
    _ = (∑' c' : {c' : Config sys //
            c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = c.e},
          reachProb ws c'.1) * ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) := by
        rw [tsum_congr (fun c' : {c' : Config sys //
          c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = c.e} =>
            (hRP c'.1).symm)]

open Classical in
/-- **Sub-step 3: inner-loop + predecessor decomposition** (`reachProb_seg`). For a
configuration `c` whose inner segment `c.e'` is *completed* (`c.t = none`) with an active weak
step `c.wt = some (l, μ)` committed from `c.we = ⟨sys.init, ofList L'⟩`, the reaching probability
factors as the total reach over entry-configs-for-`L'` sharing `c`'s committed concrete prefix
`c.e`, times the probability `ws` assigns to drawing `(l, μ)`, times the witness scheduler's
`haltMass` on the completed segment `c.e'`. Assembled from the inner-loop recursion (A1,
`seg_inner_recursion`) and the entry-draw factorisation (A2, `seg_entry_draw`). -/
theorem reachProb_seg (ws : Scheduler sys^w)
    (L' : List (Label × State)) (l : Label) (μ : PMF State) (c : Config sys)
    (he'fin : c.e'.trans.Terminates)
    (hwe : c.we = ⟨sys.init, Seq.ofList L'⟩)
    (hwt : c.wt = some (l, μ)) (ht : c.t = none)
    (hs : c.s = schedOf sys (lastOf c.e) l μ)
    (hinit : c.e'.init = lastOf c.e) :
    reachProb ws c
      = (∑' c' : {c' : Config sys //
            c'.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c'.e'.trans = Seq.nil ∧ c'.e = c.e},
          reachProb ws c'.1)
        * ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ))
        * (schedOf sys (lastOf c.e) l μ).haltMass (PMF.pure (lastOf c.e)) ⟨c.e', he'fin⟩ := by
  rw [seg_inner_recursion ws l μ (c.e'.trans.toList he'fin) c he'fin hwt hinit
      (Stream'.Seq.ofList_toList c.e'.trans he'fin).symm,
    ht, seg_entry_draw ws L' l μ c hwe hwt hs, hs]
  simp only [Scheduler.haltMass]
  ring

open Classical in
/-- **Sub-step 2: the entry-step marginal.** Summing the OUTER `step` weight from a fixed
predecessor `c₀` over all entry configurations for `L = L' ++ [(l, x)]` yields `1` exactly when
`c₀` is "right-shaped" — committed `we = ⟨init, ofList L'⟩`, halted inner loop (`t = none`),
active weak step `wt = some (l, ·)`, and concrete segment ending at `x` — and `0` otherwise. The
free next-draws `(c.wt, c.t)` of the entry marginalise out by PMF normalisation (same idea as
`baseCfg_inner_sum`/`base_sum`, but at reset state `last(eN)` and committed `weN`). -/
private theorem entryStep_collapse (ws : Scheduler sys^w)
    (L' : List (Label × State)) (l : Label) (x : State) (c₀ : Config sys) :
    (∑' c : {c : Config sys //
        c.we = ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ ∧ c.e'.trans = Seq.nil}, step ws c₀ c.1)
      = if (∃ μ, c₀.wt = some (l, μ)) ∧ c₀.t = none ∧
           c₀.we = ⟨sys.init, Seq.ofList L'⟩ ∧
           lastOf ⟨c₀.e.init, c₀.e.trans.append c₀.e'.trans⟩ = x
        then 1 else 0 := by
  have hofL : (Seq.ofList (L' ++ [(l, x)]) : Seq (Label × State))
      = (Seq.ofList L').append (Seq.cons (l, x) Seq.nil) := by
    rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
  obtain ⟨we₀, e₀, wt₀, s₀, e'₀, t₀⟩ := c₀
  cases wt₀ with
  | none =>
    rw [if_neg (by rintro ⟨⟨μ, hμ⟩, -⟩; simp at hμ)]
    exact ENNReal.tsum_eq_zero.mpr (fun c => by simp only [step])
  | some wtp =>
    obtain ⟨lw, μw⟩ := wtp
    cases t₀ with
    | some tp =>
      obtain ⟨l', μ'⟩ := tp
      rw [if_neg (by rintro ⟨-, ht, -⟩; simp at ht)]
      refine ENNReal.tsum_eq_zero.mpr (fun c => ?_)
      simp only [step]
      rw [if_neg ?_]
      rintro ⟨-, -, -, -, -, htr⟩
      rw [c.2.2] at htr
      exact append_cons_ne_nil _ _ _ htr.symm
    | none =>
      by_cases hcond : lw = l ∧ we₀ = (⟨sys.init, Seq.ofList L'⟩ : AlterSeq State Label) ∧
          lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label) = x
      · -- **value 1**: the entry-step weights marginalise to `1` over the free draws.
        rw [if_pos ⟨⟨μw, by rw [hcond.1]⟩, rfl, hcond.2.1, hcond.2.2⟩]
        have hweN : (⟨we₀.init, we₀.trans.append (Seq.cons (lw,
              lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label))
              Seq.nil)⟩ : AlterSeq State Label)
            = ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ := by
          obtain ⟨hlw, hwe0, hlast⟩ := hcond
          rw [hwe0, hlw, hlast, hofL]
        have hbij : (∑' c : {c : Config sys //
              c.we = ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ ∧ c.e'.trans = Seq.nil},
              step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩ c.1)
            = ∑' pr : Option (Label × PMF State) × Option (Label × PMF State),
                step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩
                  (entryCfg sys ⟨we₀.init, we₀.trans.append (Seq.cons (lw,
                      lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label))
                      Seq.nil)⟩
                    ⟨e₀.init, e₀.trans.append e'₀.trans⟩
                    (lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label))
                    pr.1 pr.2) :=
          (tsum_subtype_eq_of_support_subset (s := {c : Config sys |
              c.we = ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ ∧ c.e'.trans = Seq.nil}) (by
            intro c hc
            have hcne : step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩ c ≠ 0 := hc
            simp only [step] at hcne
            obtain ⟨_, hwe2, he', -, -⟩ := of_ite_ne_zero hcne
            exact ⟨hweN ▸ hwe2, congrArg AlterSeq.trans he'⟩)).trans
            (entry_draw_reindex (step ws ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩)
              ⟨we₀.init, we₀.trans.append (Seq.cons (lw,
                  lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label))
                  Seq.nil)⟩ ⟨e₀.init, e₀.trans.append e'₀.trans⟩
                (lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label)) (by
            intro c hcne
            simp only [step] at hcne
            obtain ⟨he, hwe2, he', hsome, hnone⟩ := of_ite_ne_zero hcne
            exact ⟨hwe2, he, he', hsome, hnone⟩))
        rw [hbij, ENNReal.tsum_prod',
          tsum_congr (fun wt => entryCfg_step_inner ws we₀ e₀ e'₀ lw μw s₀ wt), hweN]
        exact (ws.next _).tsum_coe
      · -- **value 0**: no entry for `L` is produced, so the OUTER guard always fails.
        rw [if_neg (by
          rintro ⟨⟨μ, hμ⟩, -, hwe0, hlast⟩
          exact hcond ⟨congrArg Prod.fst (Option.some.inj hμ), hwe0, hlast⟩)]
        refine ENNReal.tsum_eq_zero.mpr (fun c => ?_)
        simp only [step]
        rw [if_neg ?_]
        rintro ⟨-, hwe, -, -, -⟩
        have hwwe : (⟨we₀.init, we₀.trans.append (Seq.cons (lw,
              lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label))
              Seq.nil)⟩ : AlterSeq State Label)
            = ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ := hwe ▸ c.2.1
        have hinit2 : we₀.init = sys.init := congrArg AlterSeq.init hwwe
        have htrans2 : we₀.trans.append (Seq.cons (lw,
            lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label)) Seq.nil)
            = Seq.ofList (L' ++ [(l, x)]) := congrArg AlterSeq.trans hwwe
        have happ_term : (we₀.trans.append (Seq.cons (lw, lastOf
          (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label)) Seq.nil)).Terminates := by
          rw [htrans2]; exact Stream'.Seq.terminates_ofList _
        have hwt2 : we₀.trans.Terminates := terminates_of_append_terminates happ_term
        have hL'term : (Seq.ofList L' : Seq (Label × State)).Terminates :=
          Stream'.Seq.terminates_ofList _
        rw [hofL] at htrans2
        have hlweq : (lw, lastOf (⟨e₀.init, e₀.trans.append e'₀.trans⟩ : AlterSeq State Label))
            = (l, x) :=
          Stream'.Seq.append_singleton_inj_right _ _ hwt2 hL'term _ _ htrans2
        have hwetrans : we₀.trans = Seq.ofList L' :=
          Stream'.Seq.append_singleton_inj_left _ _ hwt2 hL'term _ _ htrans2
        have hwe₀eq : we₀ = (⟨sys.init, Seq.ofList L'⟩ : AlterSeq State Label) := by
          rw [← hinit2, ← hwetrans]
        exact hcond ⟨congrArg Prod.fst hlweq, hwe₀eq, congrArg Prod.snd hlweq⟩

open Classical in
/-- **Fiber partition of the entry-`L'` sum by the concrete prefix `e`.** Summing the
entry-`L'` reach restricted to a fixed `c.e = E` over all `E` recovers the full entry-`L'`
sum (each entry has a unique `e`). The `∑' E, predSum E = E L'` step of sub-step 4. -/
theorem predSum_partition (ws : Scheduler sys^w) (L' : List (Label × State)) :
    (∑' E : AlterSeq State Label,
        ∑' c : {c : Config sys //
            c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil ∧ c.e = E},
          reachProb ws c.1)
      = ∑' c : {c : Config sys // c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil},
          reachProb ws c.1 := by
  rw [← ENNReal.tsum_sigma (fun E (c : {c : Config sys //
      c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil ∧ c.e = E}) => reachProb ws c.1)]
  exact Equiv.tsum_eq
    (({ toFun := fun p => ⟨p.2.1, p.2.2.1, p.2.2.2.1⟩
        invFun := fun c => ⟨c.1.e, c.1, c.2.1, c.2.2, rfl⟩
        left_inv := fun p => by obtain ⟨E, c, hwe, he', he⟩ := p; subst he; rfl
        right_inv := fun c => rfl } :
      (Σ E : AlterSeq State Label, {c : Config sys //
          c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil ∧ c.e = E})
        ≃ {c : Config sys // c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil}))
    (fun c => reachProb ws c.1)

/-! ### Supporting pieces for `rs_pushed` -/

omit [Silent Label] in
/-- `lastOf` of a terminating execution is its `endState` (the junk branch never fires). -/
theorem lastOf_eq_endState (e : AlterSeq State Label) (h : e.trans.Terminates) :
    lastOf e = e.endState h := by
  unfold lastOf; rw [dif_pos h]

omit [Silent Label] in
/-- **Piece 3: endState of a concatenation.** If `seg` starts at `lastOf E`, the end-state of
`E` followed by `seg` is `lastOf seg`. (Both executions finite; via `toList`/`getLast?` of the
append.) -/
theorem lastOf_append_eq (E seg : AlterSeq State Label)
    (hE : E.trans.Terminates) (hseg : seg.trans.Terminates) (hinit : seg.init = lastOf E) :
    lastOf (⟨E.init, E.trans.append seg.trans⟩ : AlterSeq State Label) = lastOf seg := by
  have happ : (E.trans.append seg.trans).Terminates :=
    ⟨Nat.find hE + Nat.find hseg, Stream'.Seq.terminatedAt_append_find hE (Nat.find_spec hseg)⟩
  rw [lastOf_eq_endState _ happ, lastOf_eq_endState seg hseg,
    AlterSeq.endState_eq_getLast?, AlterSeq.endState_eq_getLast?,
    Stream'.Seq.toList_append E.trans seg.trans hE hseg happ]
  by_cases hnil : seg.trans.toList hseg = []
  · rw [hnil, List.append_nil, List.getLast?_nil, Option.elim,
      ← AlterSeq.endState_eq_getLast? E hE, ← lastOf_eq_endState E hE]
    exact hinit.symm
  · rw [List.getLast?_append_of_ne_nil _ hnil]
    obtain ⟨p, hp⟩ : ∃ p, (seg.trans.toList hseg).getLast? = some p := by
      cases hgl : (seg.trans.toList hseg).getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hgl) hnil
      | some p => exact ⟨p, rfl⟩
    rw [hp]; rfl

open Classical in
/-- **Piece 1: reachability invariant** (read off `reachAfter_Inv`). A reachable configuration has
finite committed/segment executions, its segment starts at `lastOf c.e`, and its witness `s` is the
canonical `schedOf` of the active weak step. -/
theorem reachProb_inv (ws : Scheduler sys^w) (c : Config sys) (h : reachProb ws c ≠ 0) :
    c.e.trans.Terminates ∧ c.e'.trans.Terminates ∧ c.e'.init = lastOf c.e ∧
      ∀ l₀ μ₀, c.wt = some (l₀, μ₀) → c.s = schedOf sys (lastOf c.e) l₀ μ₀ := by
  rw [reachProb] at h
  obtain ⟨n, hn⟩ : ∃ n, reachAfter ws n c ≠ 0 := by
    by_contra hcon; push Not at hcon; exact h (ENNReal.tsum_eq_zero.mpr hcon)
  have hInv := reachAfter_Inv ws n c hn
  exact ⟨hInv.e_fin, hInv.e'_fin, hInv.e'_init, fun l₀ μ₀ hwt => (hInv.seg l₀ μ₀ hwt).2.1⟩

open Classical in
/-- **Piece 2 (induction): finiteness + endpoint invariant.** The committed abstract execution `we`
is finite and ends at the same state as the committed concrete execution `e`. Each commit appends
`(lw, lastOf eN)` to `we` and sets `e := eN`, so both end at `lastOf eN`. -/
private theorem reachAfter_we_endpoint (ws : Scheduler sys^w) :
    ∀ (n : ℕ) (c : Config sys), reachAfter ws n c ≠ 0 →
      c.we.trans.Terminates ∧ lastOf c.we = lastOf c.e := by
  intro n
  induction n with
  | zero =>
    intro c hreach
    by_cases hcond : (c.we = (⟨sys.init, Seq.nil⟩ : AlterSeq State Label) ∧
        c.e = ⟨sys.init, Seq.nil⟩ ∧ c.e' = ⟨sys.init, Seq.nil⟩ ∧
        (∀ p, c.wt = some p → c.s = schedOf sys sys.init p.1 p.2) ∧
        (c.wt = none → c.s = Scheduler.halt sys))
    · refine ⟨?_, ?_⟩
      · rw [hcond.1]; exact Stream'.Seq.terminates_nil
      · rw [hcond.1, hcond.2.1]
    · simp only [reachAfter] at hreach; rw [if_neg hcond] at hreach; exact absurd rfl hreach
  | succ n ih =>
    intro c hreach
    rw [reachAfter] at hreach
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, reachAfter ws n c₀ * step ws c₀ c ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hreach (ENNReal.tsum_eq_zero.mpr hcon)
    rw [mul_ne_zero_iff] at hc₀
    obtain ⟨hreach₀, hstep⟩ := hc₀
    obtain ⟨hwefin₀, hlast₀⟩ := ih c₀ hreach₀
    obtain ⟨we₀, e₀, wt₀, s₀, e'₀, t₀⟩ := c₀
    cases wt₀ with
    | none => simp only [step] at hstep; exact absurd rfl hstep
    | some wtp =>
      obtain ⟨lw, μw⟩ := wtp
      cases t₀ with
      | some tp =>
        obtain ⟨l', μ'⟩ := tp
        simp only [step] at hstep
        obtain ⟨hcwe, hce, -, -, -, -⟩ := of_ite_ne_zero hstep
        exact ⟨by rw [hcwe]; exact hwefin₀, by rw [hcwe, hce]; exact hlast₀⟩
      | none =>
        simp only [step] at hstep
        set eN : AlterSeq State Label := ⟨e₀.init, e₀.trans.append e'₀.trans⟩ with heN
        obtain ⟨hce, hcwe, -, -, -⟩ := of_ite_ne_zero hstep
        refine ⟨?_, ?_⟩
        · rw [hcwe]
          exact ⟨_, Stream'.Seq.terminatedAt_append_find hwefin₀
            (show (Seq.cons (lw, lastOf eN) Seq.nil).TerminatedAt 1 from rfl)⟩
        · rw [hcwe, hce]
          exact lastOf_append_singleton ⟨we₀.init, we₀.trans⟩ hwefin₀ lw (lastOf eN)

/-- **Piece 2: endpoint invariant.** A reachable configuration's committed abstract and concrete
executions end at the same state. -/
theorem reachProb_endpoint (ws : Scheduler sys^w) (c : Config sys)
    (h : reachProb ws c ≠ 0) : lastOf c.we = lastOf c.e := by
  rw [reachProb] at h
  obtain ⟨n, hn⟩ : ∃ n, reachAfter ws n c ≠ 0 := by
    by_contra hcon; push Not at hcon; exact h (ENNReal.tsum_eq_zero.mpr hcon)
  exact (reachAfter_we_endpoint ws n c hn).2

/-- The **canonical entry-`L'` predecessor configuration** for the triple `(E, μ, seg)`: committed
`we = ⟨init, ofList L'⟩`, concrete prefix `e = E`, active weak step `wt = some (l, μ)` with witness
`schedOf sys (lastOf E) l μ`, completed inner segment `e' = seg`, inner loop halted (`t = none`).
Every right-shaped `c₀` summed in `rs_pushed`'s LHS is of this form. -/
noncomputable def canonCfg (sys : System State Label) (L' : List (Label × State))
    (l : Label) (E : AlterSeq State Label) (μ : PMF State) (seg : AlterSeq State Label) :
    Config sys where
  we := ⟨sys.init, Seq.ofList L'⟩
  e := E
  wt := some (l, μ)
  s := schedOf sys (lastOf E) l μ
  e' := seg
  t := none

open Classical in
/-- **Piece 4: substitution.** `reachProb` of the canonical predecessor `canonCfg E μ seg` factors,
unconditionally, as the entry-`L'` predecessor mass over `E`, times `ws.next … (l, μ)`, times the
witness `haltMass` of `seg`. When `seg.init = lastOf E` this is `reachProb_seg`; otherwise both
sides vanish (`reachProb` by piece 1, `haltMass` by `probOf_le_init`). -/
private theorem reachProb_canonCfg (ws : Scheduler sys^w) (L' : List (Label × State))
    (l : Label) (E : AlterSeq State Label) (μ : PMF State) (seg : AlterSeq State Label)
    (h : seg.trans.Terminates) :
    reachProb ws (canonCfg sys L' l E μ seg)
      = (∑' c : {c : Config sys //
            c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil ∧ c.e = E},
          reachProb ws c.1)
        * ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ))
        * (schedOf sys (lastOf E) l μ).haltMass (PMF.pure (lastOf E)) ⟨seg, h⟩ := by
  by_cases hinit : seg.init = lastOf E
  · exact reachProb_seg ws L' l μ (canonCfg sys L' l E μ seg) h rfl rfl rfl rfl hinit
  · have hRP : reachProb ws (canonCfg sys L' l E μ seg) = 0 := by
      by_contra hne
      exact hinit (reachProb_inv ws (canonCfg sys L' l E μ seg) hne).2.2.1
    have hhalt : (schedOf sys (lastOf E) l μ).haltMass (PMF.pure (lastOf E)) ⟨seg, h⟩ = 0 := by
      unfold Scheduler.haltMass
      have hz : (⟨PMF.pure (lastOf E), schedOf sys (lastOf E) l μ⟩
          : ProbabilisticExecution sys).probOf seg h = 0 := by
        refine nonpos_iff_eq_zero.mp
          (le_trans (ProbabilisticExecution.probOf_le_init _ seg h) (le_of_eq ?_))
        change (PMF.pure (lastOf E)) seg.init = 0
        rw [PMF.pure_apply, if_neg hinit]
      rw [hz, zero_mul]
    rw [hRP, hhalt, mul_zero]

open Classical in
/-- **Piece 5a: collapse the segment sum** at a fixed `(E, μ)`. Substitute piece 4 pointwise, pull
out the constants, and collapse `∑' seg, haltMass · [endpoint = x]` to `μ x` via `seg_pushforward`
(valid because `ws.valid` + piece 2 give `sys^w.step (lastOf E) l μ` whenever the prefactor is
nonzero; otherwise the prefactor is `0`). -/
private theorem seg_collapse (ws : Scheduler sys^w) (L' : List (Label × State))
    (l : Label) (x : State) (E : AlterSeq State Label) (μ : PMF State) :
    (∑' seg : {seg : AlterSeq State Label // seg.trans.Terminates},
        if WeakScheduler.stateAfter seg.1 (seg.1.trans.length seg.2) = x
          then reachProb ws (canonCfg sys L' l E μ seg.1) else 0)
      = (∑' c : {c : Config sys //
            c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil ∧ c.e = E},
          reachProb ws c.1)
        * (ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) * μ x) := by
  set P := (∑' c : {c : Config sys //
      c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil ∧ c.e = E}, reachProb ws c.1) with hP
  have hsum : ∀ seg : {seg : AlterSeq State Label // seg.trans.Terminates},
      (if WeakScheduler.stateAfter seg.1 (seg.1.trans.length seg.2) = x
          then reachProb ws (canonCfg sys L' l E μ seg.1) else 0)
        = (P * ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)))
          * ((schedOf sys (lastOf E) l μ).haltMass (PMF.pure (lastOf E)) seg
            * (if WeakScheduler.stateAfter seg.1 (seg.1.trans.length seg.2) = x then 1
              else 0)) := by
    intro seg
    rw [reachProb_canonCfg ws L' l E μ seg.1 seg.2]
    by_cases hc : WeakScheduler.stateAfter seg.1 (seg.1.trans.length seg.2) = x
    · rw [if_pos hc, if_pos hc, mul_one]
    · rw [if_neg hc, if_neg hc, mul_zero, mul_zero]
  rw [tsum_congr hsum, ENNReal.tsum_mul_left]
  by_cases hstep : sys^w.step (lastOf E) l μ
  · rw [seg_pushforward hstep x]; ring
  · have hPnext : P * ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) = 0 := by
      by_contra hne
      obtain ⟨hP0, hnext0⟩ := mul_ne_zero_iff.mp hne
      apply hstep
      have hfinL : (Seq.ofList L' : Seq (Label × State)).Terminates :=
        Stream'.Seq.terminates_ofList L'
      have hstate : (⟨sys.init, Seq.ofList L'⟩ : AlterSeq State Label).stateAt (Nat.find hfinL)
          = some (lastOf (⟨sys.init, Seq.ofList L'⟩ : AlterSeq State Label)) := by
        rw [lastOf_eq_endState _ hfinL]; exact AlterSeq.stateAt_find_eq_endState _ hfinL
      have hweak : sys^w.step (lastOf (⟨sys.init, Seq.ofList L'⟩ : AlterSeq State Label)) l μ :=
        ws.valid ⟨sys.init, Seq.ofList L'⟩ (Nat.find hfinL)
          (lastOf ⟨sys.init, Seq.ofList L'⟩) (Nat.find_spec hfinL) hstate l μ
          (PMF.mem_support_iff _ _ |>.mpr hnext0)
      have hlastEq : lastOf (⟨sys.init, Seq.ofList L'⟩ : AlterSeq State Label) = lastOf E := by
        obtain ⟨c', hc'⟩ : ∃ c' : {c : Config sys //
            c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil ∧ c.e = E},
            reachProb ws c'.1 ≠ 0 := by
          by_contra hcon; push Not at hcon; exact hP0 (ENNReal.tsum_eq_zero.mpr hcon)
        have hend := reachProb_endpoint ws c'.1 hc'
        rw [c'.2.1, c'.2.2.2] at hend; exact hend
      rwa [hlastEq] at hweak
    rw [hPnext, zero_mul, ← mul_assoc, hPnext, zero_mul]

open Classical in
/-- **Piece 5b: reindex the LHS.** The right-shaped predecessor sum is reindexed bijectively onto
triples `(E, μ, seg)` (any nonzero, guard-true `c₀` equals `canonCfg c₀.e μ c₀.e'` by pieces 1+2),
turning the guard `lastOf (E ⌢ seg) = x` into the `stateAfter`-endpoint guard of `seg`. -/
private theorem lhs_reindex (ws : Scheduler sys^w) (L' : List (Label × State))
    (l : Label) (x : State) :
    (∑' c₀ : Config sys, if (∃ μ, c₀.wt = some (l, μ)) ∧ c₀.t = none ∧
        c₀.we = ⟨sys.init, Seq.ofList L'⟩ ∧
        lastOf ⟨c₀.e.init, c₀.e.trans.append c₀.e'.trans⟩ = x
      then reachProb ws c₀ else 0)
      = ∑' t : AlterSeq State Label × PMF State ×
          {seg : AlterSeq State Label // seg.trans.Terminates},
          if WeakScheduler.stateAfter t.2.2.1 (t.2.2.1.trans.length t.2.2.2) = x
            then reachProb ws (canonCfg sys L' l t.1 t.2.1 t.2.2.1) else 0 := by
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun t => canonCfg sys L' l t.1.1 t.1.2.1 t.1.2.2.1) ?_ ?_ ?_
  · intro a b hab
    have hE : a.1.1 = b.1.1 := congrArg Config.e hab
    have hwt : some (l, a.1.2.1) = some (l, b.1.2.1) := congrArg Config.wt hab
    have hseg : a.1.2.2.1 = b.1.2.2.1 := congrArg Config.e' hab
    have hμ : a.1.2.1 = b.1.2.1 := (Prod.mk.inj (Option.some.inj hwt)).2
    exact Subtype.ext (Prod.ext hE (Prod.ext hμ (Subtype.ext hseg)))
  · intro c₀ hc₀
    have hfne : (if (∃ μ, c₀.wt = some (l, μ)) ∧ c₀.t = none ∧
        c₀.we = ⟨sys.init, Seq.ofList L'⟩ ∧
        lastOf ⟨c₀.e.init, c₀.e.trans.append c₀.e'.trans⟩ = x
      then reachProb ws c₀ else 0) ≠ 0 := hc₀
    obtain ⟨⟨μ₀, hμ₀⟩, ht₀, hwe₀, hlast₀⟩ := of_ite_ne_zero hfne
    have hrp : reachProb ws c₀ ≠ 0 := ne_zero_of_ite_ne_zero hfne
    obtain ⟨hEfin, hfin, he'init, hsched⟩ := reachProb_inv ws c₀ hrp
    have hs₀ := hsched l μ₀ hμ₀
    have heq : canonCfg sys L' l c₀.e μ₀ c₀.e' = c₀ := by
      obtain ⟨we, e, wt, s, e', t⟩ := c₀
      simp only at hwe₀ ht₀ hμ₀ hs₀
      simp only [canonCfg, hwe₀, ht₀, hμ₀, hs₀]
    have hcond : WeakScheduler.stateAfter c₀.e' (c₀.e'.trans.length hfin) = x := by
      rw [WeakScheduler.stateAfter_length_eq_endState, ← lastOf_eq_endState c₀.e' hfin,
        ← lastOf_append_eq c₀.e c₀.e' hEfin hfin he'init]
      exact hlast₀
    have hmem : (if WeakScheduler.stateAfter c₀.e' (c₀.e'.trans.length hfin) = x
        then reachProb ws (canonCfg sys L' l c₀.e μ₀ c₀.e') else 0) ≠ 0 := by
      rw [if_pos hcond, heq]; exact hrp
    exact ⟨⟨(c₀.e, μ₀, ⟨c₀.e', hfin⟩), hmem⟩, heq⟩
  · rintro ⟨⟨E, μ, seg⟩, ht⟩
    have hcond : WeakScheduler.stateAfter seg.1 (seg.1.trans.length seg.2) = x := of_ite_ne_zero ht
    have hrp : reachProb ws (canonCfg sys L' l E μ seg.1) ≠ 0 := ne_zero_of_ite_ne_zero ht
    obtain ⟨hEfin, -, hsinit, -⟩ := reachProb_inv ws (canonCfg sys L' l E μ seg.1) hrp
    rw [if_pos hcond, if_pos]
    refine ⟨⟨μ, rfl⟩, rfl, rfl, ?_⟩
    change lastOf ⟨E.init, E.trans.append seg.1.trans⟩ = x
    rw [lastOf_append_eq E seg.1 hEfin seg.2 hsinit, lastOf_eq_endState seg.1 seg.2,
      ← WeakScheduler.stateAfter_length_eq_endState]
    exact hcond

open Classical in
/-- **Sub-step 4: reindex + segment pushforward.** Reindexes the right-shaped predecessor sum by
the triple `(E := c₀.e, μ, segment := c₀.e')` (`lhs_reindex`), then collapses each per-`(E, μ)`
segment sum (`seg_collapse`): `reachProb_canonCfg` factors `reachProb` into the entry-`L'`
predecessor mass `×` `ws.next (l, μ)` `×` the witness `haltMass`, and `seg_pushforward`
(`∑ haltMass = μ x`) collapses `∑' seg` to `μ x`, yielding the per-`(E, μ)` product form below.

The supporting invariants (each a `private` lemma above) are `reachProb_inv` (reachability
invariant, read off `reachAfter_Inv`), `reachProb_endpoint` (endpoint invariant
`lastOf we = lastOf e`, which supplies `sys^w.step (lastOf E) l μ` via `ws.valid` so
`seg_pushforward` applies), and `lastOf_append_eq` (endState of a concatenation). -/
private theorem rs_pushed (ws : Scheduler sys^w)
    (L' : List (Label × State)) (l : Label) (x : State) :
    (∑' c₀ : Config sys, if (∃ μ, c₀.wt = some (l, μ)) ∧ c₀.t = none ∧
        c₀.we = ⟨sys.init, Seq.ofList L'⟩ ∧
        lastOf ⟨c₀.e.init, c₀.e.trans.append c₀.e'.trans⟩ = x
      then reachProb ws c₀ else 0)
      = ∑' E : AlterSeq State Label, ∑' μ : PMF State,
          (∑' c : {c : Config sys //
              c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil ∧ c.e = E},
            reachProb ws c.1)
            * (ws.next ⟨sys.init, Seq.ofList L'⟩ (some (l, μ)) * μ x) := by
  rw [lhs_reindex ws L' l x, ENNReal.tsum_prod']
  refine tsum_congr (fun E => ?_)
  rw [ENNReal.tsum_prod']
  exact tsum_congr (fun μ => seg_collapse ws L' l x E μ)

open Classical in
/-- **Step decomposition of the entry-configuration sum** (PLAN items 1–4). The total
`reachProb` over entries for the extended weak-step list `L' ++ [(l, x)]` factors as the
total over entries for `L'` times the one-step `sys^w`-kernel `pe'.kernel eP (l, x)`.

This is the combinatorial crux: an entry `c` for `L' ++ [(l, x)]` is produced by the OUTER
`step` from a `c₀` with committed `we = eP := ⟨sys.init, ofList L'⟩`, halted inner loop
(`c₀.t = none`), active weak step `c₀.wt = some (l, μ)`, and segment ending at `x`. Marginalising
the entry's free next-draws gives `1`; decomposing `reachProb c₀` into the entry-for-`L'`
reach (weighted `ws.next eP (some (l, μ))`) times `haltMass (schedOf … l μ) (·) c₀.e'`; then
`seg_pushforward` collapses the segment sum to `μ x`; finally summing `μ` against
`ws.next eP (some (l, μ))` rebuilds `pe'.kernel eP (l, x)`.

The proof, matching the sub-steps in the body:
1. Each entry `c` for `L` has non-`nil` committed `we` (`ofList (L' ++ [(l, x)]) ≠ nil`), so
   `reachAfter 0 c = 0` and `reachProb_fixpoint` + Tonelli give
   `E L = ∑' c₀, reachProb c₀ · (∑' c (entry-L), step c₀ c)`.
2. `entryStep_collapse` reduces the inner entry-marginal `∑' c (entry-L), step c₀ c` to the
   right-shape indicator: `1` exactly when `c₀.we = ⟨init, ofList L'⟩`, `c₀.wt = some (l, ·)`,
   `c₀.t = none`, and `lastOf (c₀.e ⌢ c₀.e') = x`; `0` otherwise (PMF normalisation over the
   entry's free draws, the OUTER branch forced by `c.e'.trans = nil`).
3–4. `rs_pushed` reindexes by `(E, μ, seg)` and collapses (via `reachProb_seg` / `seg_pushforward`)
   to the per-`(E, μ)` product; `predSum_partition` rebuilds `E L'`, and the residual `μ`-sum is
   `pe'.kernel ⟨init, ofList L'⟩ (l, x)` by definition of `ProbabilisticExecution.kernel`. -/
theorem reachProb_we_step (ws : Scheduler sys^w)
    (L' : List (Label × State)) (l : Label) (x : State) :
    (∑' c : {c : Config sys //
        c.we = ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ ∧ c.e'.trans = Seq.nil}, reachProb ws c.1)
      = (∑' c : {c : Config sys //
            c.we = ⟨sys.init, Seq.ofList L'⟩ ∧ c.e'.trans = Seq.nil}, reachProb ws c.1)
        * (⟨PMF.pure sys.init, ws⟩ : ProbabilisticExecution sys^w).kernel
            ⟨sys.init, Seq.ofList L'⟩ (l, x) := by
  -- The committed execution of an entry for `L = L' ++ [(l, x)]` is nonempty.
  have hofL : (Seq.ofList (L' ++ [(l, x)]) : Seq (Label × State))
      = (Seq.ofList L').append (Seq.cons (l, x) Seq.nil) := by
    rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
  have hofL_ne : (Seq.ofList (L' ++ [(l, x)]) : Seq (Label × State)) ≠ Seq.nil := by
    rw [hofL]; exact append_cons_ne_nil _ _ _
  -- **Sub-step 1.** `reachAfter 0 = 0` on each entry, then `reachProb_fixpoint` + Tonelli.
  have step1 : (∑' c : {c : Config sys //
        c.we = ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ ∧ c.e'.trans = Seq.nil}, reachProb ws c.1)
      = ∑' c₀ : Config sys, reachProb ws c₀ *
          (∑' c : {c : Config sys // c.we = ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ ∧
              c.e'.trans = Seq.nil}, step ws c₀ c.1) := by
    have hrw : ∀ c : {c : Config sys // c.we = ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ ∧
          c.e'.trans = Seq.nil}, reachProb ws c.1 = ∑' c₀, reachProb ws c₀ * step ws c₀ c.1 := by
      intro c
      rw [reachProb_fixpoint]
      have h0 : reachAfter ws 0 c.1 = 0 := by
        rw [reachAfter, if_neg]
        rintro ⟨hwe, -, -, -, -⟩
        rw [c.2.1] at hwe
        exact hofL_ne (congrArg AlterSeq.trans hwe)
      rw [h0, zero_add]
    rw [tsum_congr hrw, ENNReal.tsum_comm]
    exact tsum_congr (fun c₀ => ENNReal.tsum_mul_left)
  rw [step1]
  -- **Sub-step 2.** Collapse the inner entry-marginal to the right-shape indicator, turning
  -- the sum into a sum over the right-shaped predecessors `c₀`.
  have hcollapse : ∀ c₀ : Config sys,
      reachProb ws c₀ * (∑' c : {c : Config sys //
          c.we = ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩ ∧ c.e'.trans = Seq.nil}, step ws c₀ c.1)
        = (if (∃ μ, c₀.wt = some (l, μ)) ∧ c₀.t = none ∧
              c₀.we = ⟨sys.init, Seq.ofList L'⟩ ∧
              lastOf ⟨c₀.e.init, c₀.e.trans.append c₀.e'.trans⟩ = x
            then reachProb ws c₀ else 0) := by
    intro c₀
    rw [entryStep_collapse ws L' l x c₀]
    by_cases h : (∃ μ, c₀.wt = some (l, μ)) ∧ c₀.t = none ∧
        c₀.we = ⟨sys.init, Seq.ofList L'⟩ ∧
        lastOf ⟨c₀.e.init, c₀.e.trans.append c₀.e'.trans⟩ = x
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [tsum_congr hcollapse]
  -- **Sub-step 4.** `rs_pushed` (reindex + `reachProb_seg` + `seg_pushforward`) gives the
  -- per-`(E, μ)` product form; Fubini factors it, `predSum_partition` rebuilds `E L'`, and the
  -- remaining `μ`-sum is exactly the one-step kernel by definition.
  rw [rs_pushed ws L' l x, tsum_congr (fun _ => ENNReal.tsum_mul_left),
    ENNReal.tsum_mul_right, predSum_partition ws L']
  congr 1

open Classical in
/-- The list-indexed core of `probOf_eq_reachProb_we`: the claim for executions of the
canonical form `⟨sys.init, ofList L⟩`. Proved by reverse (cons-end) induction on `L`. -/
theorem aux (ws : Scheduler sys^w) (L : List (Label × State)) :
    (⟨PMF.pure sys.init, ws⟩ : ProbabilisticExecution sys^w).probOf
        ⟨sys.init, Seq.ofList L⟩ (Stream'.Seq.terminates_ofList L)
      = ∑' c : {c : Config sys // c.we = ⟨sys.init, Seq.ofList L⟩ ∧ c.e'.trans = Seq.nil},
          reachProb ws c.1 := by
  induction L using List.reverseRecOn with
  | nil =>
    have hLHS : (⟨PMF.pure sys.init, ws⟩ : ProbabilisticExecution sys^w).probOf
        ⟨sys.init, Seq.ofList ([] : List (Label × State))⟩
        (Stream'.Seq.terminates_ofList []) = 1 := by
      rw [ProbabilisticExecution.probOf_congr _ ⟨sys.init, Seq.ofList []⟩ ⟨sys.init, Seq.nil⟩
          (by rw [Stream'.Seq.ofList_nil]) (Stream'.Seq.terminates_ofList [])
          Stream'.Seq.terminates_nil,
        ProbabilisticExecution.probOf_nil]
      exact PMF.pure_apply_self sys.init
    rw [hLHS]
    symm
    rw [show (Seq.ofList ([] : List (Label × State)) : Seq (Label × State)) = Seq.nil from
      Stream'.Seq.ofList_nil]
    exact base_sum ws
  | append_singleton L' last ih =>
    obtain ⟨l, x⟩ := last
    -- LHS factorises by the cons-end recursion of `probOf`.
    have hofl : (Seq.ofList (L' ++ [(l, x)]) : Seq (Label × State))
        = (Seq.ofList L').append (Seq.cons (l, x) Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have hterm_app : ((Seq.ofList L').append (Seq.cons (l, x) Seq.nil)).Terminates := by
      rw [← hofl]; exact Stream'.Seq.terminates_ofList _
    rw [ProbabilisticExecution.probOf_congr _ ⟨sys.init, Seq.ofList (L' ++ [(l, x)])⟩
        ⟨sys.init, (Seq.ofList L').append (Seq.cons (l, x) Seq.nil)⟩ (by rw [hofl])
        (Stream'.Seq.terminates_ofList _) hterm_app,
      ProbabilisticExecution.probOf_append_singleton _ sys.init (Seq.ofList L')
        (Stream'.Seq.terminates_ofList _) (l, x) hterm_app, ih,
      reachProb_we_step ws L' l x]

/-- **Abstract-side fidelity.** The probability of the `sys^w`-trajectory `e` under `ws`
equals the total `reachProb` over *entry* configurations with abstract execution `e`
(`c.we = e`) at a reset point (`c.e'.trans = nil`).

PROOF PLAN (induction on `e`'s weak-step list `L`, with `e = ⟨sys.init, ofList L⟩`; if
`e.init ≠ sys.init` both sides are `0` since `we` always starts at `sys.init` and `pe'.init`
is `pure sys.init`). Write `E L` for the RHS at `e = ⟨sys.init, ofList L⟩`.

* **Base `L = []`**: `pe'.probOf ⟨sys.init, nil⟩ = pe'.init sys.init = (pure sys.init) sys.init = 1`
  (`probOf_nil`/`PMF.pure_apply_self`). RHS: the entry configs with `we = e' = ⟨sys.init,nil⟩`
  are exactly the `reachAfter 0` (start) configs — they cannot be reached at `n ≥ 1` (every
  `step` grows `we`/`e`/`e'`), so `reachProb = reachAfter 0` there, summing to `1`
  (`∑_{wt} ws.next ⟨init,nil⟩ wt · ∑_t … = 1`).

* **Step `L = L' ++ [(l, x)]`** (let `eP := ⟨sys.init, ofList L'⟩`):
  1. `E L = ∑_{entry c for L} reachProb c`. Each entry `c` is produced by the OUTER `step`
     from a `c₀` with `c₀.we = eP`, `c₀.t = none`, `c₀.wt = some (l, _)`, and
     `lastOf (c₀.e ⌢ c₀.e') = x`. Summing the OUTER `step c₀ c` over the entry's free
     next-draws (`c.wt`, `c.t`) gives `1` (PMF normalisation, incl. the halt case
     `c.wt = none`), so `E L = ∑_{c₀ : that shape} reachProb c₀`.
  2. `reachProb c₀ = [reach the entry-for-L' config with wt = (l, μ)] · haltMass (schedOf … l μ)
     (pure (lastOf eP-concrete)) c₀.e'` — the entry-for-L' reach contributes
     `ws.next eP (some (l, μ))` (and the first-`t` draw + inner draws telescope into the
     segment's `probOf`, and `probOf · next-none = haltMass`).
  3. `∑_{c₀ : segment ends at x} haltMass (schedOf … l μ) (·) c₀.e' = μ x` by `seg_pushforward`.
  4. Hence `E L = E L' · ∑_μ ws.next eP (some (l, μ)) · μ x = E L' · pe'.kernel eP (l, x)`.
  5. `pe'.probOf ⟨sys.init, ofList L⟩ = pe'.probOf eP · pe'.kernel eP (l, x)`
     (`probOf_append_singleton`). With the IH `E L' = pe'.probOf eP`, done. -/
theorem probOf_eq_reachProb_we (ws : Scheduler sys^w)
    (e : AlterSeq State Label) (h : e.trans.Terminates) :
    (⟨PMF.pure sys.init, ws⟩ : ProbabilisticExecution sys^w).probOf e h
      = ∑' c : {c : Config sys // c.we = e ∧ c.e'.trans = Seq.nil}, reachProb ws c.1 := by
  by_cases hinit : e.init = sys.init
  · -- `e = ⟨sys.init, ofList L⟩` for `L = e.trans.toList h`; reduce to `aux`.
    obtain ⟨ei, et⟩ := e
    subst hinit
    set L := et.toList h with hLdef
    have hL : et = Seq.ofList L := (Stream'.Seq.ofList_toList et h).symm
    rw [ProbabilisticExecution.probOf_congr _ ⟨sys.init, et⟩ ⟨sys.init, Seq.ofList L⟩
        (by rw [hL]) h (Stream'.Seq.terminates_ofList L), aux ws L, hL]
  · -- `e.init ≠ sys.init`: both sides vanish.
    rw [ProbabilisticExecution.probOf_init_factor ws (PMF.pure sys.init) e h,
      PMF.pure_apply_of_ne _ _ hinit, zero_mul]
    symm
    refine ENNReal.tsum_eq_zero.mpr (fun c => ?_)
    by_contra hne
    have hwi := reachProb_we_init ws c.1 hne
    rw [c.2.1] at hwi
    exact hinit hwi

end PLTS
