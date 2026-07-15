/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.DistMonad.DistTraceKernel

/-!
# The trace-cone belief and the lower witness execution

Second stage of `dist_traceProb_eq` (`DistMonad/DistTrace.lean`): the trace-cone belief
(`beliefTCw`, `beliefTC`), the level-mass `labMass`, and the *lowered* witness scheduler/execution
(`Scheduler.lower`, `ProbabilisticExecution.lower`) that invert the `𝒟`-lift. The level-mass
recursion and the trace-probability equality built on top live in `DistTrace.lean`.
-/

open Stream'

namespace PLTS

variable {α β State State_C State_A Label : Type}

/-! ### The trace-cone belief and the witness execution -/

/-- Unnormalized weight of the trace-cone belief: mass on `𝒟(sys)`-histories `E`
whose **full label sequence** equals `labs`, weighted by the current-state mass
`(E.endState) s`. Conditioning on the full label list (internal labels included),
rather than the external trace, keeps the normalizer finite (a level sum, see
`beliefTCw_tsum_ne_top`) and makes the trace-cone invariant step uniform. -/
noncomputable def ProbabilisticExecution.beliefTCw
    {sys : System State Label}
    (pe' : ProbabilisticExecution 𝒟(sys))
    (labs : List Label) (s : State) (E : AlterSeq (PMF State) Label) : ENNReal :=
  open Classical in
  if h : E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs then
    pe'.probOf E h.1 * (E.endState h.1) s
  else 0

open Classical in
/-- **Append-singleton reindex** for `probOf` over label-list-constrained
`𝒟(sys)`-histories: summing `probOf` over `E` with label list `labs ++ [l]`
equals summing `probOf E' · kernel E' (l, μ)` over `(E', μ)` with `E'` having label
list `labs`, via the bijection `E = ⟨E'.init, E'.trans.append (cons (l,μ) nil)⟩`
and `probOf_append_singleton`. -/
theorem ProbabilisticExecution.tsum_probOf_labels_append
    {sys : System State Label}
    (pe' : ProbabilisticExecution 𝒟(sys))
    (labs : List Label) (l : Label) :
    (∑' E : AlterSeq (PMF State) Label,
        dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList (labs ++ [l]))
          (fun h => pe'.probOf E h.1) (fun _ => 0))
    = ∑' (E' : AlterSeq (PMF State) Label) (μ : PMF State),
        dite (E'.trans.Terminates ∧ E'.trans.map Prod.fst = Seq.ofList labs)
          (fun h => pe'.probOf E' h.1 * pe'.kernel E' (l, μ)) (fun _ => 0) := by
  classical
  rw [← ENNReal.tsum_prod' (f := fun p : AlterSeq (PMF State) Label × PMF State =>
      dite (p.1.trans.Terminates ∧ Seq.map Prod.fst p.1.trans = (↑labs : Seq Label))
        (fun h => pe'.probOf p.1 h.1 * pe'.kernel p.1 (l, p.2)) (fun _ => 0))]
  -- Abbreviate the two summands.
  set f : AlterSeq (PMF State) Label → ENNReal := fun E =>
      dite (E.trans.Terminates ∧ Seq.map Prod.fst E.trans = (↑(labs ++ [l]) : Seq Label))
        (fun h => pe'.probOf E h.1) (fun _ => 0) with hf_def
  set g : AlterSeq (PMF State) Label × PMF State → ENNReal := fun p =>
      dite (p.1.trans.Terminates ∧ Seq.map Prod.fst p.1.trans = (↑labs : Seq Label))
        (fun h => pe'.probOf p.1 h.1 * pe'.kernel p.1 (l, p.2)) (fun _ => 0) with hg_def
  -- Helper: membership in `support g` forces the then-branch condition.
  have g_supp_cond : ∀ p : AlterSeq (PMF State) Label × PMF State, g p ≠ 0 →
      p.1.trans.Terminates ∧ Seq.map Prod.fst p.1.trans = (↑labs : Seq Label) := by
    intro p hp
    by_contra hcond
    rw [hg_def] at hp
    simp only at hp
    rw [dif_neg hcond] at hp
    exact hp rfl
  -- Helper: membership in `support f` forces the then-branch condition.
  have f_supp_cond : ∀ E : AlterSeq (PMF State) Label, f E ≠ 0 →
      E.trans.Terminates ∧ Seq.map Prod.fst E.trans = (↑(labs ++ [l]) : Seq Label) := by
    intro E hE
    by_contra hcond
    rw [hf_def] at hE
    simp only at hE
    rw [dif_neg hcond] at hE
    exact hE rfl
  -- The forward bijection `(E', μ) ↦ ⟨E'.init, E'.trans.append (cons (l,μ) nil)⟩`.
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun x => (⟨(x.1).1.init,
        (x.1).1.trans.append (Seq.cons (l, (x.1).2) Seq.nil)⟩ : AlterSeq (PMF State) Label))
    ?hinj ?hf ?hfg
  case hinj =>
    rintro x y hxy
    have hx := g_supp_cond x.1 x.2
    have hy := g_supp_cond y.1 y.2
    -- Extract trans-equation from `i x = i y`.
    have h_trans := congrArg AlterSeq.trans hxy
    have h_init := congrArg AlterSeq.init hxy
    simp only at h_trans h_init
    -- `append_singleton_inj_right` ⇒ last elements equal ⇒ `μ`'s equal.
    have h_last := Stream'.Seq.append_singleton_inj_right
      (x.1).1.trans (y.1).1.trans hx.1 hy.1 _ _ h_trans
    have hμ : (x.1).2 = (y.1).2 := (Prod.mk.inj h_last).2
    -- `append_singleton_inj_left` ⇒ trans prefixes equal.
    have h_prev := Stream'.Seq.append_singleton_inj_left
      (x.1).1.trans (y.1).1.trans hx.1 hy.1 _ _ h_trans
    -- Reassemble.
    refine Subtype.ext (Prod.ext ?_ hμ)
    exact congrArg₂ AlterSeq.mk h_init h_prev
  case hf =>
    intro E hE_mem
    have hE := f_supp_cond E hE_mem
    -- `E.trans` is nonempty: `map Prod.fst E.trans = ↑(labs ++ [l])` is nonempty.
    have h_ne : E.trans.toList hE.1 ≠ [] := by
      intro hnil
      have h_map_nil : E.trans.map Prod.fst = Stream'.Seq.nil := by
        have : E.trans = Stream'.Seq.nil := by
          rw [← Stream'.Seq.ofList_toList E.trans hE.1, hnil, Stream'.Seq.ofList_nil]
        rw [this, Stream'.Seq.map_nil]
      rw [hE.2] at h_map_nil
      -- `↑(labs ++ [l]) = nil`, but `labs ++ [l]` has positive length.
      have h_len := congrArg Stream'.Seq.length' h_map_nil
      rw [Stream'.Seq.length'_nil,
        Stream'.Seq.length'_of_terminates (Stream'.Seq.terminates_ofList _),
        ← Stream'.Seq.length_toList _ (Stream'.Seq.terminates_ofList _),
        Stream'.Seq.toList_ofList] at h_len
      simp only [List.length_append, List.length_singleton, Nat.cast_eq_zero] at h_len
      omega
    -- Split `E.trans = prev.append (cons last nil)`.
    obtain ⟨prev, last, h_prev_term, h_split, _, _⟩ :=
      Stream'.Seq.exists_split_last E.trans hE.1 h_ne
    -- Substitute the split into the map-equation.
    have h_trans_map := hE.2
    rw [h_split, Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil] at h_trans_map
    -- `↑(labs ++ [l]) = (↑labs).append (cons l nil)`.
    rw [show (↑(labs ++ [l]) : Seq Label)
        = (↑labs : Seq Label).append (Seq.cons l Seq.nil) by
        rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]]
      at h_trans_map
    -- Cancel the appended singleton.
    have h_prev_map_term : (prev.map Prod.fst).Terminates :=
      Stream'.Seq.terminates_map_iff.mpr h_prev_term
    have h_prev_map : prev.map Prod.fst = (↑labs : Seq Label) :=
      Stream'.Seq.append_singleton_inj_left _ _ h_prev_map_term
        (Stream'.Seq.terminates_ofList _) _ _ h_trans_map
    have h_last : last.1 = l :=
      Stream'.Seq.append_singleton_inj_right _ _ h_prev_map_term
        (Stream'.Seq.terminates_ofList _) _ _ h_trans_map
    -- The preimage `(⟨E.init, prev⟩, last.2)` lies in `support g`.
    have hg_pos : g (⟨E.init, prev⟩, last.2) ≠ 0 := by
      rw [hg_def]; simp only
      rw [dif_pos ⟨h_prev_term, h_prev_map⟩]
      -- This value equals `pe'.probOf E ≠ 0` via `probOf_append_singleton`.
      have h_app_term : (prev.append (Seq.cons (l, last.2) Seq.nil)).Terminates := by
        rw [show (Seq.cons (l, last.2) Seq.nil) = Seq.cons last Seq.nil by
          rw [← h_last]]
        exact h_split ▸ hE.1
      have h_factor := ProbabilisticExecution.probOf_append_singleton pe'
        E.init prev h_prev_term (l, last.2) h_app_term
      -- `⟨E.init, prev.append (cons (l, last.2) nil)⟩ = E` so its probOf is `pe'.probOf E`.
      have h_reassemble : (⟨E.init, prev.append (Seq.cons (l, last.2) Seq.nil)⟩
          : AlterSeq (PMF State) Label) = E := by
        refine congrArg₂ AlterSeq.mk rfl ?_
        rw [show (Seq.cons (l, last.2) Seq.nil) = Seq.cons last Seq.nil by rw [← h_last]]
        exact h_split.symm
      have h_probOf_E : pe'.probOf E hE.1 ≠ 0 := by
        have h_mem := Function.mem_support.mp hE_mem
        rwa [dif_pos hE] at h_mem
      intro hzero
      apply h_probOf_E
      -- `pe'.probOf E = (factored product) = 0`. Transport the termination proof.
      have key : ∀ (A : AlterSeq (PMF State) Label) (hA : A.trans.Terminates),
          A = E → pe'.probOf A hA = pe'.probOf E hE.1 := by
        rintro A hA rfl; rfl
      rw [← key _ h_app_term h_reassemble, h_factor, hzero]
    -- Conclude: `E` is in the range of `i`.
    refine ⟨⟨(⟨E.init, prev⟩, last.2), hg_pos⟩, ?_⟩
    simp only
    refine congrArg₂ AlterSeq.mk rfl ?_
    rw [show (Seq.cons (l, last.2) Seq.nil) = Seq.cons last Seq.nil by rw [← h_last]]
    exact h_split.symm
  case hfg =>
    rintro x
    set E' := (x.1).1 with hE'_def
    set μ := (x.1).2 with hμ_def
    have hx := g_supp_cond x.1 x.2
    -- `hx.1 : E'.trans.Terminates`, `hx.2 : E'.trans.map Prod.fst = ↑labs`.
    -- The RHS `g ↑x` is in its then-branch.
    have h_g : g x.1 = pe'.probOf E' hx.1 * pe'.kernel E' (l, μ) := by
      rw [hg_def]; simp only; rw [dif_pos hx]
    -- Termination of the appended trans.
    have h_app_term : (E'.trans.append (Seq.cons (l, μ) Seq.nil)).Terminates :=
      ⟨_, Stream'.Seq.terminatedAt_append_find hx.1
        (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil).choose_spec⟩
    -- The map of the appended trans is `↑(labs ++ [l])`.
    have h_map : Seq.map Prod.fst (E'.trans.append (Seq.cons (l, μ) Seq.nil))
        = (↑(labs ++ [l]) : Seq Label) := by
      rw [Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil, hx.2,
        Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    -- The LHS `f (i x)` is in its then-branch.
    have h_f : f (⟨E'.init, E'.trans.append (Seq.cons (l, μ) Seq.nil)⟩
        : AlterSeq (PMF State) Label)
        = pe'.probOf ⟨E'.init, E'.trans.append (Seq.cons (l, μ) Seq.nil)⟩ h_app_term := by
      rw [hf_def]; simp only; rw [dif_pos ⟨h_app_term, h_map⟩]
    change f (⟨E'.init, E'.trans.append (Seq.cons (l, μ) Seq.nil)⟩
        : AlterSeq (PMF State) Label) = g x.1
    rw [h_f, h_g]
    -- Factor via `probOf_append_singleton`. Note `⟨E'.init, E'.trans⟩ = E'`.
    rw [ProbabilisticExecution.probOf_append_singleton pe' E'.init E'.trans hx.1 (l, μ)
      h_app_term]

open Classical in
/-- The **`g`-integrated level mass**: total `probOf`-weight of terminating
histories with label list `labs`, each weighted by `g` of its end-state. The
trace-cone invariant is most naturally proven for this `g`-indexed quantity
(the `g = 1` slice recovers the bare level sum). -/
noncomputable def ProbabilisticExecution.labMass {S : Type} {Sys : System S Label}
    (pe : ProbabilisticExecution Sys) (labs : List Label) (g : S → ENNReal) : ENNReal :=
  ∑' e : AlterSeq S Label,
    dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs)
      (fun h => pe.probOf e h.1 * g (e.endState h.1)) (fun _ => 0)

open Classical in
/-- **Base of the level-mass recursion.** Histories with empty label list are the
`⟨s₀, nil⟩`, with `probOf = initState s₀` and `endState = s₀`. -/
theorem ProbabilisticExecution.labMass_nil {S : Type} {Sys : System S Label}
    (pe : ProbabilisticExecution Sys) (g : S → ENNReal) :
    pe.labMass [] g = ∑' s₀ : S, pe.initState s₀ * g s₀ := by
  classical
  unfold ProbabilisticExecution.labMass
  -- The summand over `AlterSeq S Label`.
  set f : AlterSeq S Label → ENNReal := fun e =>
      dite (e.trans.Terminates ∧ Seq.map Prod.fst e.trans = (↑([] : List Label) : Seq Label))
        (fun h => pe.probOf e h.1 * g (e.endState h.1)) (fun _ => 0) with hf_def
  set rhs : S → ENNReal := fun s₀ => pe.initState s₀ * g s₀ with hrhs_def
  -- Membership in `support f` forces `e.trans = nil`.
  have f_supp_cond : ∀ e : AlterSeq S Label, f e ≠ 0 →
      e.trans.Terminates ∧ Seq.map Prod.fst e.trans = (↑([] : List Label) : Seq Label) := by
    intro e he
    by_contra hcond
    rw [hf_def] at he; simp only at he
    rw [dif_neg hcond] at he
    exact he rfl
  -- A then-branch condition forces `e.trans = nil`.
  have trans_nil : ∀ e : AlterSeq S Label,
      e.trans.Terminates ∧ Seq.map Prod.fst e.trans = (↑([] : List Label) : Seq Label) →
      e.trans = Seq.nil := by
    intro e h
    have h0 : Stream'.Seq.length' e.trans = 0 := by
      rw [← Stream'.Seq.length'_map (f := Prod.fst), h.2, Stream'.Seq.ofList_nil,
        Stream'.Seq.length'_nil]
    exact (Stream'.Seq.length'_eq_zero_iff_nil e.trans).mp h0
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun s₀ => (⟨(s₀ : S), Seq.nil⟩ : AlterSeq S Label)) ?hinj ?hf ?hfg
  case hinj =>
    rintro a b hab
    have h_init := congrArg AlterSeq.init hab
    simp only at h_init
    exact Subtype.ext h_init
  case hf =>
    intro e he_mem
    have he := f_supp_cond e (Function.mem_support.mp he_mem)
    have h_nil : e.trans = Seq.nil := trans_nil e he
    -- `e = ⟨e.init, nil⟩`.
    have h_reassemble : (⟨e.init, Seq.nil⟩ : AlterSeq S Label) = e :=
      congrArg₂ AlterSeq.mk rfl h_nil.symm
    -- `f e = pe.initState e.init * g e.init`, so `e.init ∈ support rhs`.
    have hf_pos : rhs e.init ≠ 0 := by
      rw [hrhs_def]; simp only
      intro hzero
      apply Function.mem_support.mp he_mem
      change f e = 0
      rw [hf_def]; simp only; rw [dif_pos he]
      -- Transport `probOf` and `endState` through `h_reassemble`.
      have h_prob : pe.probOf e he.1 = pe.initState e.init := by
        have key : ∀ (A : AlterSeq S Label) (hA : A.trans.Terminates),
            A = (⟨e.init, Seq.nil⟩ : AlterSeq S Label) →
            pe.probOf A hA = pe.probOf (⟨e.init, Seq.nil⟩ : AlterSeq S Label)
              Stream'.Seq.terminates_nil := by
          rintro A hA rfl; rfl
        rw [key e he.1 h_reassemble.symm, ProbabilisticExecution.probOf_nil,
          ProbabilisticExecution.init_eq_initState]
      have h_end : e.endState he.1 = e.init :=
        AlterSeq.endState_of_trans_nil e h_nil he.1
      rw [h_prob, h_end]; exact hzero
    refine ⟨⟨e.init, hf_pos⟩, ?_⟩
    simp only
    exact h_reassemble
  case hfg =>
    rintro x
    set s₀ := (x : S) with hs₀_def
    -- `i x = ⟨s₀, nil⟩`; its matching condition holds.
    have h_cond : (⟨s₀, Seq.nil⟩ : AlterSeq S Label).trans.Terminates ∧
        Seq.map Prod.fst (⟨s₀, Seq.nil⟩ : AlterSeq S Label).trans
          = (↑([] : List Label) : Seq Label) := by
      refine ⟨Stream'.Seq.terminates_nil, ?_⟩
      simp only [Stream'.Seq.map_nil, Stream'.Seq.ofList_nil]
    change f (⟨s₀, Seq.nil⟩ : AlterSeq S Label) = rhs s₀
    rw [hf_def]; simp only; rw [dif_pos h_cond]
    rw [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState,
      AlterSeq.endState_of_trans_nil _ rfl h_cond.1]

open Classical in
/-- Base case of the level sum: the histories with empty label list are exactly
the `⟨μ₀, nil⟩`, whose `probOf` is `initState μ₀`, summing to
`∑' μ₀, initState μ₀ = 1`. The `g = 1` slice of `labMass_nil`. -/
theorem ProbabilisticExecution.tsum_probOf_labels_nil
    {sys : System State Label}
    (pe' : ProbabilisticExecution 𝒟(sys)) :
    (∑' E : AlterSeq (PMF State) Label,
        dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList ([] : List Label))
          (fun h => pe'.probOf E h.1) (fun _ => 0)) = 1 := by
  have h := pe'.labMass_nil (fun _ => (1 : ENNReal))
  simpa only [ProbabilisticExecution.labMass, mul_one, PMF.tsum_coe] using h

/-- The summed one-step kernel is `≤ 1` (the scheduler emits a sub-probability). -/
theorem ProbabilisticExecution.tsum_kernel_le_one
    {sys : System State Label}
    (pe' : ProbabilisticExecution 𝒟(sys))
    (E : AlterSeq (PMF State) Label) (l : Label) :
    (∑' μ : PMF State, pe'.kernel E (l, μ)) ≤ 1 := by
  calc (∑' μ : PMF State, pe'.kernel E (l, μ))
      = ∑' (μ : PMF State) (ω : PMF (PMF State)),
          pe'.scheduler.next E (some (l, ω)) * ω μ := rfl
    _ = ∑' (ω : PMF (PMF State)) (μ : PMF State),
          pe'.scheduler.next E (some (l, ω)) * ω μ := ENNReal.tsum_comm
    _ = ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) := by
        refine tsum_congr fun ω => ?_
        rw [ENNReal.tsum_mul_left, ω.tsum_coe, mul_one]
    _ ≤ ∑' opt, pe'.scheduler.next E opt :=
        ENNReal.tsum_comp_le_tsum_of_injective (f := fun ω : PMF (PMF State) => some (l, ω))
          (fun _ _ h => (Prod.mk.inj (Option.some.inj h)).2) _
    _ = 1 := (pe'.scheduler.next E).tsum_coe

open Classical in
/-- **Level sum `≤ 1`**: the total `probOf`-mass of `𝒟(sys)`-histories with a fixed
label list is `≤ 1`. Induction on the label list via `tsum_probOf_labels_append`,
`tsum_probOf_labels_nil`, and `tsum_kernel_le_one`. -/
theorem ProbabilisticExecution.probOf_labels_tsum_le_one
    {sys : System State Label}
    (pe' : ProbabilisticExecution 𝒟(sys)) (labs : List Label) :
    (∑' E : AlterSeq (PMF State) Label,
        dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
          (fun h => pe'.probOf E h.1) (fun _ => 0)) ≤ 1 := by
  classical
  induction labs using List.reverseRecOn with
  | nil => exact le_of_eq pe'.tsum_probOf_labels_nil
  | append_singleton labs l ih =>
      rw [pe'.tsum_probOf_labels_append labs l]
      refine le_trans (ENNReal.tsum_le_tsum (fun E' => ?_)) ih
      by_cases hP : E'.trans.Terminates ∧ E'.trans.map Prod.fst = Seq.ofList labs
      · simp only [dif_pos hP]
        rw [ENNReal.tsum_mul_left]
        exact mul_le_of_le_one_right' (pe'.tsum_kernel_le_one E' l)
      · simp only [dif_neg hP, tsum_zero, le_refl]

/-- The trace-cone normalizer is finite (`≤ 1`): the `E` with label list `labs`
all have length `labs.length`, contributing a level-`probOf` sum bounded by
`probOf_labels_tsum_le_one`. -/
theorem ProbabilisticExecution.beliefTCw_tsum_ne_top
    {sys : System State Label}
    (pe' : ProbabilisticExecution 𝒟(sys))
    (labs : List Label) (s : State) :
    (∑' E : AlterSeq (PMF State) Label, pe'.beliefTCw labs s E) ≠ ⊤ := by
  classical
  have hle : (∑' E : AlterSeq (PMF State) Label, pe'.beliefTCw labs s E) ≤ 1 := by
    refine le_trans (ENNReal.tsum_le_tsum (fun E => ?_)) (pe'.probOf_labels_tsum_le_one labs)
    unfold ProbabilisticExecution.beliefTCw
    by_cases hP : E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs
    · simp only [dif_pos hP]
      exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
    · simp only [dif_neg hP, le_refl]
  exact (lt_of_le_of_lt hle ENNReal.one_lt_top).ne

/-- **Trace-cone belief.** Posterior over `𝒟(sys)`-histories with full label
sequence `labs`, weighted by the current-state mass `(E.endState) s`; conditions
only on the labels `labs` and the current state `s` (not the intermediate
states of the `sys`-history). -/
noncomputable def ProbabilisticExecution.beliefTC
    {sys : System State Label}
    (pe' : ProbabilisticExecution 𝒟(sys))
    (labs : List Label) (s : State) : PMF (AlterSeq (PMF State) Label) :=
  open Classical in
  if h0 : (∑' E, pe'.beliefTCw labs s E) ≠ 0 then
    PMF.normalize (pe'.beliefTCw labs s) h0 (pe'.beliefTCw_tsum_ne_top labs s)
  else
    PMF.pure ⟨PMF.pure s, Seq.nil⟩

/-- Every `E` in `beliefTC`'s support terminates and has `s` in its end-state's
support — exactly what the witness scheduler needs for validity (via
`distHyperKernel_step`). This is *immediate* from the weight `(E.endState) s`,
with no recursive support argument. -/
theorem ProbabilisticExecution.beliefTC_support
    {sys : System State Label}
    (pe' : ProbabilisticExecution 𝒟(sys))
    (labs : List Label) (s : State) {E : AlterSeq (PMF State) Label}
    (hE : E ∈ (pe'.beliefTC labs s).support) :
    ∃ hT : E.trans.Terminates, s ∈ (E.endState hT).support := by
  classical
  unfold ProbabilisticExecution.beliefTC at hE
  split_ifs at hE with h0
  · rw [PMF.mem_support_normalize_iff] at hE
    unfold ProbabilisticExecution.beliefTCw at hE
    split_ifs at hE with h
    · refine ⟨h.1, ?_⟩
      rw [PMF.mem_support_iff]
      intro h_zero
      rw [h_zero, mul_zero] at hE
      exact hE rfl
    · exact absurd rfl hE
  · rw [PMF.mem_support_pure_iff] at hE
    subst hE
    refine ⟨Stream'.Seq.terminates_nil, ?_⟩
    rw [show (⟨PMF.pure s, Seq.nil⟩ : AlterSeq (PMF State) Label).endState
          Stream'.Seq.terminates_nil = PMF.pure s from
        AlterSeq.endState_of_trans_nil _ rfl _]
    rw [PMF.support_pure]
    exact Set.mem_singleton s

/-- The witness **scheduler**. At a (terminating) `sys`-history `e`, sample a
`𝒟(sys)`-history `E` from the trace-cone belief `beliefTC e.labels (e.endState)`
(`e.labels` = the full label list of `e`), draw `(l, ω) ∼ pe'.scheduler.next E`,
and emit `(l, μ')` with `μ' ∼ distHyperKernel E l ω (e.endState)`. Validity:
`beliefTC_support` supplies `e.endState ∈ E.endState.support`, and
`distHyperKernel_step` then yields a valid `sys`-step. -/
noncomputable def Scheduler.lower
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys)) :
    Scheduler sys where
  next e :=
    open Classical in
    if h_term : e.trans.Terminates then
      (pe'.beliefTC ((e.trans.toList h_term).map Prod.fst) (e.endState h_term)).bind (fun E =>
        (pe'.scheduler.next E).bind (fun opt =>
          match opt with
          | none         => PMF.pure none
          | some (l, ω)  =>
            (pe'.distHyperKernel E l ω (e.endState h_term)).map
              (fun μ' => some (l, μ'))))
    else
      PMF.pure none
  valid := by
    classical
    intro e n s e_term_n e_stateAt_eq l μ h_supp
    have h_term : e.trans.Terminates := ⟨n, e_term_n⟩
    have h_find_le : Nat.find h_term ≤ n := Nat.find_le e_term_n
    have h_n_le : n ≤ Nat.find h_term := by
      by_contra h_lt
      push Not at h_lt
      rcases n with _ | k
      · exact absurd h_lt (Nat.not_lt_zero _)
      · have hk_ge : Nat.find h_term ≤ k := Nat.lt_succ_iff.mp h_lt
        have h_term_k : e.trans.TerminatedAt k :=
          Stream'.Seq.terminated_stable e.trans hk_ge (Nat.find_spec h_term)
        have h_state_none : e.stateAt (k + 1) = none := by
          change (e.trans.get? k).map Prod.snd = none
          rw [show e.trans.get? k = none from h_term_k]
          rfl
        rw [h_state_none] at e_stateAt_eq
        exact Option.some_ne_none s e_stateAt_eq.symm
    have h_n_eq : n = Nat.find h_term := le_antisymm h_n_le h_find_le
    have h_s_eq : s = e.endState h_term := by
      have h := AlterSeq.stateAt_find_eq_endState e h_term
      rw [← h_n_eq] at h
      rw [h] at e_stateAt_eq
      exact (Option.some.inj e_stateAt_eq).symm
    subst h_s_eq
    change some (l, μ) ∈
      (open Classical in
        if h_term' : e.trans.Terminates then
          (pe'.beliefTC ((e.trans.toList h_term').map Prod.fst) (e.endState h_term')).bind (fun E =>
            (pe'.scheduler.next E).bind (fun opt =>
              match opt with
              | none => PMF.pure none
              | some (l', ω) =>
                (pe'.distHyperKernel E l' ω (e.endState h_term')).map
                  (fun μ' => some (l', μ'))))
        else PMF.pure none).support at h_supp
    rw [dif_pos h_term] at h_supp
    rw [PMF.mem_support_bind_iff] at h_supp
    obtain ⟨E, hE_belief, h_supp⟩ := h_supp
    rw [PMF.mem_support_bind_iff] at h_supp
    obtain ⟨opt, hopt_sch, h_supp⟩ := h_supp
    obtain ⟨hE_term, h_endState⟩ :=
      pe'.beliefTC_support ((e.trans.toList h_term).map Prod.fst) (e.endState h_term) hE_belief
    cases opt with
    | none =>
      change some (l, μ) ∈ (PMF.pure (α := Option (Label × PMF State)) none).support at h_supp
      rw [PMF.support_pure, Set.mem_singleton_iff] at h_supp
      exact absurd h_supp (by simp)
    | some lω =>
      obtain ⟨l', ω⟩ := lω
      change some (l, μ) ∈ ((pe'.distHyperKernel E l' ω (e.endState h_term)).map
        (fun μ' => some (l', μ'))).support at h_supp
      rw [PMF.mem_support_map_iff] at h_supp
      obtain ⟨μ', h_μ'_kernel, h_eq⟩ := h_supp
      simp only [Option.some.injEq, Prod.mk.injEq] at h_eq
      obtain ⟨rfl, rfl⟩ := h_eq
      exact pe'.distHyperKernel_step hE_term hopt_sch h_endState h_μ'_kernel

/-- The corrected witness **execution**: initial distribution `initState.bind id`
(a Dirac on `sys.init` under the `achievableTraceDists` requirement), with
scheduler `Scheduler.lower`. -/
noncomputable def ProbabilisticExecution.lower
    {sys : System State Label} [Silent Label]
    (pe' : ProbabilisticExecution 𝒟(sys)) :
    ProbabilisticExecution sys where
  initState := pe'.initState.bind id
  scheduler := Scheduler.lower pe'

end PLTS
