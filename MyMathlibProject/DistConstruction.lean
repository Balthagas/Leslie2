/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.WeakStep

/-!
# Distribution-monad construction

Lift a labelled PLTS `sys` to a new labelled PLTS whose state space is
`PMF State` (the free PMF on `State`) and whose steps are exactly the
`hyperStep`s of `sys`. The construction is denoted `𝒟(sys)`, and it is
designed to leave the set of achievable trace distributions invariant.
-/

open Stream'

namespace PLTS

variable {α β State State_C State_A Label : Type}

/-! ## The distribution-monad construction

Lift a labelled PLTS `sys` to a new labelled PLTS whose state space is
`PMF State` (the free PMF on `State`) and whose steps are exactly the
`hyperStep`s of `sys`. -/

/-- The **distribution-monad construction** on a labelled PLTS.

Given `sys : LabelledSystem State Label`, lift the state space to `PMF State`.
The lifted system has:

* `init := PMF.pure sys.init` — a Dirac on the original initial state;
* `step μ l ω := hyperStep sys μ l (ω.bind id)` — a transition from
  the pre-distribution `μ` at label `l` to a `PMF (PMF State)` outcome `ω`
  is valid iff the flattened destination `ω.bind id : PMF State` is reachable
  from `μ` via a `hyperStep`;
* `internal := sys.internal` — the label classification is inherited.

The PMF wrapper on the post-state slot of `System.step` is "absorbed" by
flattening with `bind id`; the lifted step thus identifies any two
post-state-of-post-state distributions that agree after one bind, which is
the natural identification under the PMF-monad multiplication
`μ : PMF (PMF α) ↦ μ.bind id : PMF α`. -/
noncomputable def LabelledSystem.dist (sys : LabelledSystem State Label) :
    LabelledSystem (PMF State) Label where
  init := PMF.pure sys.init
  step μ l ω := hyperStep sys μ l (ω.bind id)
  internal := sys.internal

/-- `𝒟(sys)` is sugar for `LabelledSystem.dist sys`, the distribution-monad
construction lifting `sys` to a labelled system over `PMF State`. -/
scoped notation:max "𝒟(" sys ")" => LabelledSystem.dist sys

/-! ### The distribution-monad construction preserves trace distributions

Both directions are non-trivial: lifting a `pe` over `sys` to `𝒟(sys)`
requires reshaping `pe`'s scheduler signature to operate on histories over
`PMF State` (with Dirac-state lifts of each transition), while the reverse
direction requires flattening genuine `PMF (PMF State)`-randomness from
`𝒟(sys)` back into `pe`-on-`sys`. The superset direction is deferred. -/

/-- Lift a `State`-execution to a `PMF State`-execution by Dirac-wrapping
every state. Preserves labels. This is the map `g` that embeds finite
`sys`-executions into `𝒟(sys)`-executions, used to transport a
probabilistic execution of `sys` to one of `𝒟(sys)` of the same trace
distribution. -/
noncomputable def AlterSeq.dirac (e : AlterSeq State Label) :
    AlterSeq (PMF State) Label where
  init := PMF.pure e.init
  trans := e.trans.map (fun lq => (lq.1, PMF.pure lq.2))

/-- Lift a `sys`-scheduler to a `𝒟(sys)`-scheduler. On a history `E` that
arises from a `sys`-execution `e` via `e.dirac`, run the underlying
scheduler on `e` and push each emitted step `(l, μ)` to
`(l, μ.map PMF.pure) : Label × PMF (PMF State)`. On any other history
(non-Dirac somewhere), terminate immediately.

The fallback branch is never reached when this scheduler is plugged into
the `dirac`-lifted initial distribution: by induction, every reachable
history stays in the image of `AlterSeq.dirac`. -/
noncomputable def Scheduler.dist {sys : LabelledSystem State Label}
    (sch : Scheduler sys.toSystem) : Scheduler 𝒟(sys).toSystem where
  next E :=
    open Classical in
    if h : ∃ e : AlterSeq State Label, e.dirac = E then
      (sch.next h.choose).map
        (Option.map (fun lμ => (lμ.1, lμ.2.map PMF.pure)))
    else
      PMF.pure none
  valid := by
    intro e n s e_finite e_final l μ
    split_ifs with hImg
    · -- `hImg : ∃ e', e'.dirac = e`: history is in the image of `dirac`.
      intro hsupp
      -- Decompose the support of the lifted PMF: there is an `(l', μ')` with
      -- `some (l', μ') ∈ (sch.next e₀).support` and `(l', μ'.map PMF.pure) = (l, μ)`.
      rw [PMF.mem_support_map_iff] at hsupp
      obtain ⟨opt, hopt_supp, hopt_eq⟩ := hsupp
      cases opt with
      | none => simp at hopt_eq
      | some lμ' =>
        obtain ⟨l', μ'⟩ := lμ'
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hopt_eq
        obtain ⟨hl_eq, hμ_eq⟩ := hopt_eq
        -- `hl_eq : l' = l`, `hμ_eq : μ'.map PMF.pure = μ`.
        set e₀ := hImg.choose with he₀_def
        have he_eq : e₀.dirac = e := hImg.choose_spec
        -- Transport `e.trans.TerminatedAt n` to `e₀.trans.TerminatedAt n`.
        have he₀_finite : e₀.trans.TerminatedAt n := by
          rw [← he_eq] at e_finite
          change (e₀.trans.map (fun lq => (lq.1, PMF.pure lq.2))).TerminatedAt n at e_finite
          rwa [Stream'.Seq.terminatedAt_map_iff] at e_finite
        -- Transport `e.stateAt n = some s` to `e₀.stateAt n = some s₀` with `s = PMF.pure s₀`.
        obtain ⟨s₀, he₀_final, hs_eq⟩ :
            ∃ s₀, e₀.stateAt n = some s₀ ∧ s = PMF.pure s₀ := by
          rw [← he_eq] at e_final
          cases n with
          | zero =>
            change some (PMF.pure e₀.init) = some s at e_final
            exact ⟨e₀.init, rfl, (Option.some.inj e_final).symm⟩
          | succ k =>
            change ((e₀.dirac).trans.get? k).map Prod.snd = some s at e_final
            change ((e₀.trans.map (fun lq => (lq.1, PMF.pure lq.2))).get? k).map Prod.snd
              = some s at e_final
            rw [Stream'.Seq.map_get?] at e_final
            -- `e_final : ((e₀.trans.get? k).map (...)).map Prod.snd = some s`
            obtain ⟨lq', hlq'_get, hlq'_eq⟩ := Option.map_eq_some_iff.mp e_final
            obtain ⟨lq, hlq_get, rfl⟩ := Option.map_eq_some_iff.mp hlq'_get
            refine ⟨lq.2, ?_, hlq'_eq.symm⟩
            change (e₀.trans.get? k).map Prod.snd = some lq.2
            rw [hlq_get]; rfl
        -- Apply `sch.valid` at `e₀` for the `sys`-side step `(l', μ')`.
        have h_step' : sys.step s₀ l' μ' :=
          sch.valid e₀ n s₀ he₀_finite he₀_final l' μ' hopt_supp
        -- Rewrite to the original `l` via `hl_eq`.
        rw [hl_eq] at h_step'
        -- Conclude: `𝒟(sys).step s l μ = hyperStep sys s l (μ.bind id)`
        -- reduces via `s = PMF.pure s₀`, `μ = μ'.map PMF.pure`, and
        -- `(μ'.map PMF.pure).bind id = μ'`.
        change hyperStep sys s l (μ.bind id)
        rw [← hμ_eq, hs_eq, PMF.bind_map]
        change hyperStep sys (PMF.pure s₀) l (μ'.bind PMF.pure)
        rw [PMF.bind_pure]
        exact hyperStep_pure_of_step h_step'
    · intro h
      simp only [PMF.support_pure, Set.mem_singleton_iff, reduceCtorEq] at h

/-- Lift a probabilistic execution of `sys` to one of `𝒟(sys)`: the
initial distribution is pushed forward by `PMF.pure`, and the scheduler
is the Dirac-lift of `pe.scheduler`. -/
noncomputable def ProbabilisticExecution.dist {sys : LabelledSystem State Label}
    (pe : ProbabilisticExecution sys.toSystem) :
    ProbabilisticExecution 𝒟(sys).toSystem where
  initState := pe.initState.map PMF.pure
  scheduler := pe.scheduler.dist

/-- `AlterSeq.dirac` preserves termination: an execution is finite iff
its Dirac-lift is. -/
@[simp] theorem AlterSeq.dirac_trans_terminates_iff (e : AlterSeq State Label) :
    e.dirac.trans.Terminates ↔ e.trans.Terminates := by
  change (e.trans.map (fun lq => (lq.1, PMF.pure lq.2))).Terminates ↔ _
  exact Stream'.Seq.terminates_map_iff

/-- `PMF.pure` is injective: two Diracs are equal only on equal points. -/
theorem PMF.pure_injective : Function.Injective (@PMF.pure State) := by
  intro a b h
  by_contra hne
  have h_app : (PMF.pure a) a = (PMF.pure b) a := by rw [h]
  rw [PMF.pure_apply_self, PMF.pure_apply, if_neg hne] at h_app
  exact one_ne_zero h_app

/-- `AlterSeq.dirac` is injective: the Dirac-lift uniquely determines its
preimage. -/
theorem AlterSeq.dirac_injective :
    Function.Injective (@AlterSeq.dirac State Label) := by
  rintro ⟨i₁, t₁⟩ ⟨i₂, t₂⟩ h
  have h_init : PMF.pure i₁ = PMF.pure i₂ := congr_arg AlterSeq.init h
  have h_trans :
      t₁.map (fun lq : Label × State => (lq.1, PMF.pure lq.2))
      = t₂.map (fun lq : Label × State => (lq.1, PMF.pure lq.2)) :=
    congr_arg AlterSeq.trans h
  obtain rfl := PMF.pure_injective h_init
  congr 1
  apply Stream'.Seq.ext
  intro n
  have hn :
      (Stream'.Seq.map (fun lq : Label × State => (lq.1, PMF.pure lq.2)) t₁).get? n
      = (Stream'.Seq.map (fun lq : Label × State => (lq.1, PMF.pure lq.2)) t₂).get? n := by
    rw [h_trans]
  rw [Stream'.Seq.map_get?, Stream'.Seq.map_get?] at hn
  cases h1 : t₁.get? n with
  | none =>
    cases h2 : t₂.get? n with
    | none => rfl
    | some lq2 => rw [h1, h2] at hn; simp at hn
  | some lq1 =>
    cases h2 : t₂.get? n with
    | none => rw [h1, h2] at hn; simp at hn
    | some lq2 =>
      rw [h1, h2] at hn
      obtain ⟨l1, s1⟩ := lq1
      obtain ⟨l2, s2⟩ := lq2
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, h_pure⟩ := hn
      obtain rfl := PMF.pure_injective h_pure
      rfl

/-- Unfolding of the lifted scheduler on a Dirac-lifted history. By
injectivity of `dirac`, the `Classical.choose` inside `Scheduler.dist`'s
`then` branch is the original `e`. -/
theorem Scheduler.dist_next_dirac {sys : LabelledSystem State Label}
    (sch : Scheduler sys.toSystem) (e : AlterSeq State Label) :
    sch.dist.next e.dirac
      = (sch.next e).map (Option.map (fun lν => (lν.1, lν.2.map PMF.pure))) := by
  change (open Classical in
    if h : ∃ e', e'.dirac = e.dirac then
      (sch.next h.choose).map (Option.map (fun lμ => (lμ.1, lμ.2.map PMF.pure)))
    else PMF.pure none) = _
  classical
  rw [dif_pos ⟨e, rfl⟩]
  congr 2
  exact AlterSeq.dirac_injective (⟨e, rfl⟩ : ∃ e', e'.dirac = e.dirac).choose_spec

/-- **Kernel of the lifted execution at a Dirac-lifted history, applied to a
Dirac post-state.** Reduces to the underlying `sys`-kernel. -/
theorem ProbabilisticExecution.dist_kernel_dirac_pure
    {sys : LabelledSystem State Label} (pe : ProbabilisticExecution sys.toSystem)
    (e : AlterSeq State Label) (l : Label) (s' : State) :
    pe.dist.kernel e.dirac (l, PMF.pure s') = pe.kernel e (l, s') := by
  -- Helper: `PMF.map PMF.pure` is injective (since `PMF.pure` is).
  have h_map_inj : Function.Injective (@PMF.map State (PMF State) PMF.pure) := by
    intro p q h
    ext a
    have h1 : (p.map PMF.pure) (PMF.pure a) = (q.map PMF.pure) (PMF.pure a) := by rw [h]
    rw [PMF.map_apply, PMF.map_apply] at h1
    rw [tsum_eq_single a (fun b hb =>
      if_neg (fun heq => hb (PMF.pure_injective heq).symm))] at h1
    rw [tsum_eq_single a (fun b hb =>
      if_neg (fun heq => hb (PMF.pure_injective heq).symm))] at h1
    rw [if_pos rfl, if_pos rfl] at h1
    exact h1
  -- Unfold both kernels and expose the lifted scheduler.
  change (∑' ω, pe.scheduler.dist.next e.dirac (some (l, ω)) * ω (PMF.pure s'))
       = ∑' ν, pe.scheduler.next e (some (l, ν)) * ν s'
  -- Rewrite the lifted scheduler on a Dirac history via `Scheduler.dist_next_dirac`.
  simp_rw [Scheduler.dist_next_dirac pe.scheduler e]
  -- Reindex the outer sum (over `ω : PMF (PMF State)`) along the injection
  -- `ν ↦ ν.map PMF.pure`; the summand's support lies in this range.
  rw [← h_map_inj.tsum_eq (f := fun ω =>
    ((pe.scheduler.next e).map (Option.map (fun lν => (lν.1, lν.2.map PMF.pure))))
      (some (l, ω)) * ω (PMF.pure s'))]
  · -- After reindexing: simplify the summand pointwise to
    -- `pe.scheduler.next e (some (l, ν)) * ν s'`.
    congr 1
    ext ν
    -- Factor 1: `((sch.next e).map _) (some (l, ν.map PMF.pure)) = sch.next e (some (l, ν))`.
    rw [PMF.map_apply]
    rw [tsum_eq_single (some (l, ν)) (fun opt hopt => by
      cases opt with
      | none => simp
      | some lν' =>
        obtain ⟨l', ν'⟩ := lν'
        simp only [Option.map_some]
        by_cases h : some (l, ν.map PMF.pure) = some (l', ν'.map PMF.pure)
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, hν⟩ := h
          have hν' : ν' = ν := (h_map_inj hν).symm
          subst hν'
          exact absurd rfl hopt
        · rw [if_neg h])]
    rw [if_pos (by simp)]
    -- Factor 2: `(ν.map PMF.pure) (PMF.pure s') = ν s'` via `PMF.pure` injectivity.
    rw [PMF.map_apply]
    rw [tsum_eq_single s' (fun s'' hs'' =>
      if_neg (fun h => hs'' (PMF.pure_injective h).symm))]
    rw [if_pos rfl]
  · -- Support condition: any `ω` with non-zero summand is in the image of `PMF.map PMF.pure`.
    classical
    intro ω hω
    simp only [Function.mem_support, ne_eq] at hω
    -- From `hω`, the first factor of the product is non-zero.
    have hfac : ((pe.scheduler.next e).map
        (Option.map (fun lν : Label × PMF State => (lν.1, lν.2.map PMF.pure))))
        (some (l, ω)) ≠ 0 := fun h => hω (by rw [h, zero_mul])
    -- Some witness opt has non-zero contribution to the map_apply sum.
    rw [PMF.map_apply] at hfac
    have hne1 := mt ENNReal.tsum_eq_zero.mpr hfac
    push Not at hne1
    obtain ⟨opt, hopt⟩ := hne1
    cases opt with
    | none => simp at hopt
    | some lν =>
      obtain ⟨l', ν'⟩ := lν
      simp only [Option.map_some] at hopt
      by_cases heq : some (l, ω) = some (l', ν'.map PMF.pure)
      · simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨_, hω_eq⟩ := heq
        exact ⟨ν', hω_eq.symm⟩
      · rw [if_neg heq] at hopt; exact absurd rfl hopt

/-- **Kernel of the lifted execution at a Dirac-lifted history, applied to a
non-Dirac post-state.** Vanishes: the lifted scheduler only emits Dirac
post-states. -/
theorem ProbabilisticExecution.dist_kernel_dirac_of_not_pure
    {sys : LabelledSystem State Label} (pe : ProbabilisticExecution sys.toSystem)
    (e : AlterSeq State Label) (l : Label) (μ_succ : PMF State)
    (h : ∀ s, μ_succ ≠ PMF.pure s) :
    pe.dist.kernel e.dirac (l, μ_succ) = 0 := by
  unfold ProbabilisticExecution.kernel
  apply ENNReal.tsum_eq_zero.mpr
  intro ω
  change (pe.scheduler.dist.next e.dirac) (some (l, ω)) * ω μ_succ = 0
  rw [Scheduler.dist_next_dirac]
  by_cases hω : ∃ ν : PMF State, ω = PMF.map PMF.pure ν
  · obtain ⟨ν, rfl⟩ := hω
    have h_zero : (PMF.map PMF.pure ν) μ_succ = 0 := by
      rw [PMF.map_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro s
      rw [if_neg (h s)]
    rw [h_zero, mul_zero]
  · have h_zero :
        (PMF.map (Option.map fun lv : Label × PMF State => (lv.1, PMF.map PMF.pure lv.2))
            (pe.scheduler.next e)) (some (l, ω)) = 0 := by
      rw [PMF.map_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro x
      rcases x with _ | ⟨l', ν⟩
      · simp
      · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
        rw [if_neg]
        rintro ⟨rfl, rfl⟩
        exact hω ⟨ν, rfl⟩
    rw [h_zero, zero_mul]

/-- The Dirac-lift commutes with appending a single transition: if we extend
a `sys`-execution `e` by `(l, s')`, the resulting Dirac-lift has the same
shape as extending `e.dirac` by `(l, PMF.pure s')`. -/
theorem AlterSeq.dirac_append_singleton
    (e : AlterSeq State Label) (l : Label) (s' : State) :
    (⟨e.init, e.trans.append (Stream'.Seq.cons (l, s') Stream'.Seq.nil)⟩
      : AlterSeq State Label).dirac
    = ⟨e.dirac.init, e.dirac.trans.append
        (Stream'.Seq.cons (l, PMF.pure s') Stream'.Seq.nil)⟩ := by
  change (⟨PMF.pure e.init,
          (e.trans.append (Stream'.Seq.cons (l, s') Stream'.Seq.nil)).map _⟩
        : AlterSeq (PMF State) Label) =
      ⟨PMF.pure e.init,
       (e.trans.map _).append (Stream'.Seq.cons (l, PMF.pure s') Stream'.Seq.nil)⟩
  congr 1
  rw [Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil]

/-- **Unified probability of a lifted execution.** The lifted probabilistic
execution `pe.dist` assigns to a finite `𝒟(sys)`-execution `E` the
`pe`-probability of its (unique, by injectivity of `dirac`) `sys`-preimage
when `E` is the Dirac-lift of some `sys`-execution, and `0` otherwise.

Proved by strong induction on the length of `E.trans.toList hFin`. In the
base case `E.trans` is empty and `probOf` reduces to the initial mass:
`(pe.initState.map PMF.pure) E.init` is non-zero iff `E.init = PMF.pure s₀`
for some `s₀`, equivalently iff `E` is in the image of `dirac`. In the
inductive case `probOf` factors as the truncated `probOf` times the kernel
at the last step; the kernel is non-zero iff the last post-state is a
Dirac (in which case it equals the underlying `sys` kernel), so the
conjunction "all states are Diracs" propagates exactly. -/
theorem ProbabilisticExecution.dist_probOf
    {sys : LabelledSystem State Label}
    (pe : ProbabilisticExecution sys.toSystem)
    (E : AlterSeq (PMF State) Label) (hFin : E.trans.Terminates) :
    pe.dist.probOf E hFin =
      open Classical in
      if h : ∃ e : AlterSeq State Label, e.dirac = E
      then pe.probOf h.choose
        ((AlterSeq.dirac_trans_terminates_iff _).mp (h.choose_spec.symm ▸ hFin))
      else 0 := by
  classical
  -- Strong induction on the length of `E.trans.toList hFin`.
  generalize hn : (E.trans.toList hFin).length = n
  induction n generalizing E hFin with
  | zero =>
    -- `(E.trans.toList hFin).length = 0` ⇒ `E.trans = Seq.nil`.
    have h_trans_nil : E.trans = Stream'.Seq.nil := by
      apply Stream'.Seq.length_eq_zero.mp
      rw [← Stream'.Seq.length_toList E.trans hFin, hn]
    -- Destructure E so we can substitute the trans-nil.
    obtain ⟨μ_init, sq⟩ := E
    change sq = Stream'.Seq.nil at h_trans_nil
    subst h_trans_nil
    -- LHS: pe.dist.probOf ⟨μ_init, Seq.nil⟩ _ = pe.dist.init μ_init.
    rw [show pe.dist.probOf ⟨μ_init, Stream'.Seq.nil⟩ hFin = pe.dist.init μ_init from
        ProbabilisticExecution.probOf_nil pe.dist μ_init]
    change (pe.initState.map PMF.pure) μ_init = _
    -- Case-split on whether `μ_init` is a Dirac.
    by_cases hex_s : ∃ s : State, PMF.pure s = μ_init
    · -- Positive: `μ_init = PMF.pure s₀`. The Dirac-lift witness is `⟨s₀, Seq.nil⟩`.
      obtain ⟨s₀, hs₀⟩ := hex_s
      have hex_e : ∃ e : AlterSeq State Label,
          e.dirac = (⟨μ_init, Stream'.Seq.nil⟩ : AlterSeq (PMF State) Label) := by
        refine ⟨⟨s₀, Stream'.Seq.nil⟩, ?_⟩
        change (⟨PMF.pure s₀, Stream'.Seq.map _ Stream'.Seq.nil⟩ : AlterSeq (PMF State) Label)
            = ⟨μ_init, Stream'.Seq.nil⟩
        rw [Stream'.Seq.map_nil, hs₀]
      rw [dif_pos hex_e]
      -- Reduce to a universally-quantified claim to dodge the dependent termination arg.
      suffices key : ∀ (e : AlterSeq State Label)
          (_ : e.dirac = (⟨μ_init, Stream'.Seq.nil⟩ : AlterSeq (PMF State) Label))
          (h_term : e.trans.Terminates),
          pe.probOf e h_term = (pe.initState.map PMF.pure) μ_init by
        exact (key hex_e.choose hex_e.choose_spec _).symm
      intro e he h_term
      obtain ⟨ei, et⟩ := e
      have h_init : PMF.pure ei = μ_init := congr_arg AlterSeq.init he
      have h_trans_map :
          Stream'.Seq.map (fun lq : Label × State => (lq.1, PMF.pure lq.2)) et
          = Stream'.Seq.nil :=
        congr_arg AlterSeq.trans he
      have h_et : et = Stream'.Seq.nil := by
        have hlen : et.length' = 0 := by
          have h := congr_arg Stream'.Seq.length' h_trans_map
          rw [Stream'.Seq.length'_map, Stream'.Seq.length'_nil] at h
          exact h
        exact (Stream'.Seq.length'_eq_zero_iff_nil et).mp hlen
      subst h_et
      rw [ProbabilisticExecution.probOf_nil]
      -- Need: pe.init ei = (pe.initState.map PMF.pure) μ_init
      rw [← h_init, PMF.map_apply]
      rw [tsum_eq_single ei (fun s' hs' => by
        rw [if_neg (fun h => hs' (PMF.pure_injective h).symm)])]
      rw [if_pos rfl]
      rfl
    · -- Negative: `μ_init` is not a Dirac. Both sides are `0`.
      have hex_e_neg : ¬ ∃ e : AlterSeq State Label,
          e.dirac = (⟨μ_init, Stream'.Seq.nil⟩ : AlterSeq (PMF State) Label) := by
        rintro ⟨e, he⟩
        apply hex_s
        refine ⟨e.init, ?_⟩
        have := congr_arg AlterSeq.init he
        change PMF.pure e.init = μ_init at this
        exact this
      rw [dif_neg hex_e_neg]
      -- LHS: (pe.initState.map PMF.pure) μ_init = 0.
      rw [PMF.map_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro s
      exact if_neg (fun h => hex_s ⟨s, h.symm⟩)
  | succ k ih =>
    -- Destructure `E = ⟨μ_init, sq⟩` upfront to avoid dependency issues later.
    obtain ⟨μ_init, sq⟩ := E
    -- (1) Decompose `sq.toList hFin = rest ++ [(l, μ_succ)]`.
    have hL_ne : sq.toList hFin ≠ [] := by
      intro hL; rw [hL] at hn; simp at hn
    obtain ⟨rest, l, μ_succ, hL_eq⟩ :
        ∃ (rest : List (Label × PMF State)) (l : Label) (μ_succ : PMF State),
          sq.toList hFin = rest ++ [(l, μ_succ)] := by
      refine ⟨(sq.toList hFin).dropLast,
              ((sq.toList hFin).getLast hL_ne).1,
              ((sq.toList hFin).getLast hL_ne).2, ?_⟩
      conv_lhs => rw [← List.dropLast_append_getLast hL_ne]
    have hrest_len : rest.length = k := by
      have h := congr_arg List.length hL_eq
      rw [List.length_append, List.length_singleton] at h
      -- `h : (sq.toList hFin).length = rest.length + 1`
      -- `hn : ({ init := μ_init, trans := sq }.trans.toList hFin).length = k + 1`
      have hn' : (sq.toList hFin).length = k + 1 := hn
      omega
    -- (2) Reconstruct sq via `ofList_toList` and `ofList_append`.
    have h_sq : sq = (Stream'.Seq.ofList rest).append
                    (Stream'.Seq.cons (l, μ_succ) Stream'.Seq.nil) := by
      conv_lhs => rw [← Stream'.Seq.ofList_toList sq hFin]
      rw [hL_eq, Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    -- (3) Truncated execution.
    have hrest_fin : (Stream'.Seq.ofList rest).Terminates := Stream'.Seq.terminates_ofList rest
    have hE_trunc_len :
        ((⟨μ_init, Stream'.Seq.ofList rest⟩ : AlterSeq (PMF State) Label).trans.toList
          hrest_fin).length = k := by
      change ((Stream'.Seq.ofList rest).toList _).length = k
      rw [Stream'.Seq.toList_ofList]
      exact hrest_len
    -- (4) Apply IH at the truncated execution.
    have ih_trunc := ih ⟨μ_init, Stream'.Seq.ofList rest⟩ hrest_fin hE_trunc_len
    -- (5) Apply `probOf_append_singleton` to the LHS.
    subst h_sq
    rw [ProbabilisticExecution.probOf_append_singleton pe.dist μ_init
        (Stream'.Seq.ofList rest) hrest_fin (l, μ_succ) hFin]
    rw [ih_trunc]
    -- (6) Manual case analysis on the two dites + Dirac-ness of `μ_succ`.
    by_cases h_trunc : ∃ e_t : AlterSeq State Label,
        e_t.dirac = (⟨μ_init, Stream'.Seq.ofList rest⟩ : AlterSeq (PMF State) Label)
    · rw [dif_pos h_trunc]
      -- Stabilize the witness via `set` to dodge dependent-rewrite motive issues.
      set e_t := h_trunc.choose with he_t_def
      have he_t_spec : e_t.dirac
          = (⟨μ_init, Stream'.Seq.ofList rest⟩ : AlterSeq (PMF State) Label) :=
        h_trunc.choose_spec
      by_cases h_dirac : ∃ s' : State, PMF.pure s' = μ_succ
      · -- Truncated in image AND `μ_succ = PMF.pure s'`.
        obtain ⟨s', hs'⟩ := h_dirac
        have h_full :
            ∃ e : AlterSeq State Label,
              e.dirac = (⟨μ_init, (Stream'.Seq.ofList rest).append
                (Stream'.Seq.cons (l, μ_succ) Stream'.Seq.nil)⟩
                : AlterSeq (PMF State) Label) := by
          refine ⟨⟨e_t.init,
            e_t.trans.append (Stream'.Seq.cons (l, s') Stream'.Seq.nil)⟩, ?_⟩
          rw [AlterSeq.dirac_append_singleton e_t l s']
          have h_init : e_t.dirac.init = μ_init := by rw [he_t_spec]
          have h_trans : e_t.dirac.trans = Stream'.Seq.ofList rest := by rw [he_t_spec]
          rw [h_init, h_trans, ← hs']
        rw [dif_pos h_full]
        -- Kernel rewrite via `he_t_spec.symm` is now safe.
        have h_kernel_eq :
            pe.dist.kernel
              (⟨μ_init, Stream'.Seq.ofList rest⟩ : AlterSeq (PMF State) Label)
              (l, μ_succ) = pe.kernel e_t (l, s') := by
          rw [← he_t_spec, ← hs']
          exact pe.dist_kernel_dirac_pure e_t l s'
        rw [h_kernel_eq]
        -- Goal: pe.probOf e_t ... * pe.kernel e_t (l, s') = pe.probOf h_full.choose ...
        -- This is `probOf_append_singleton` plus `dirac` injectivity on the witness.
        -- Reduce to a universally-quantified claim to dodge the dependent termination arg.
        suffices key : ∀ (e_full : AlterSeq State Label)
            (_ : e_full.dirac = (⟨μ_init, (Stream'.Seq.ofList rest).append
              (Stream'.Seq.cons (l, μ_succ) Stream'.Seq.nil)⟩
              : AlterSeq (PMF State) Label))
            (h_full_fin : e_full.trans.Terminates),
            pe.probOf e_t ((AlterSeq.dirac_trans_terminates_iff _).mp
              (he_t_spec.symm ▸ hrest_fin)) * pe.kernel e_t (l, s')
            = pe.probOf e_full h_full_fin by
          exact key h_full.choose h_full.choose_spec _
        intro e_full he_full h_full_fin
        -- By injectivity of dirac, e_full = ⟨e_t.init, e_t.trans.append (cons (l, s') nil)⟩.
        have h_eq : e_full = ⟨e_t.init,
            e_t.trans.append (Stream'.Seq.cons (l, s') Stream'.Seq.nil)⟩ := by
          apply AlterSeq.dirac_injective
          rw [he_full, AlterSeq.dirac_append_singleton e_t l s']
          have h_init : e_t.dirac.init = μ_init := by rw [he_t_spec]
          have h_trans : e_t.dirac.trans = Stream'.Seq.ofList rest := by rw [he_t_spec]
          rw [h_init, h_trans, ← hs']
        subst h_eq
        -- Now apply probOf_append_singleton to factor the RHS.
        rw [ProbabilisticExecution.probOf_append_singleton pe e_t.init e_t.trans
            ((AlterSeq.dirac_trans_terminates_iff _).mp (he_t_spec.symm ▸ hrest_fin))
            (l, s') h_full_fin]
      · -- Truncated in image but `μ_succ` is NOT a Dirac.
        push Not at h_dirac
        have h_not_pure : ∀ s, μ_succ ≠ PMF.pure s :=
          fun s h => h_dirac s h.symm
        have h_kernel_zero :
            pe.dist.kernel
              (⟨μ_init, Stream'.Seq.ofList rest⟩ : AlterSeq (PMF State) Label)
              (l, μ_succ) = 0 := by
          rw [← he_t_spec]
          exact pe.dist_kernel_dirac_of_not_pure e_t l μ_succ h_not_pure
        rw [h_kernel_zero, mul_zero]
        have h_not_full : ¬ ∃ e : AlterSeq State Label,
            e.dirac = (⟨μ_init, (Stream'.Seq.ofList rest).append
              (Stream'.Seq.cons (l, μ_succ) Stream'.Seq.nil)⟩
              : AlterSeq (PMF State) Label) := by
          rintro ⟨e, he⟩
          -- `e.dirac.trans` is `e.trans.map (fun lq => (lq.1, PMF.pure lq.2))`.
          -- Its last transition's μ-component must be a Dirac, but the goal's
          -- last is `μ_succ` which isn't. Contradicts.
          have h_trans : e.trans.map (fun lq => (lq.1, PMF.pure lq.2))
              = (Stream'.Seq.ofList rest).append
                (Stream'.Seq.cons (l, μ_succ) Stream'.Seq.nil) := by
            have := congr_arg AlterSeq.trans he
            simpa [AlterSeq.dirac] using this
          -- Get the index `rest.length` of both sides.
          have h_idx := congr_arg (fun s => s.get? rest.length) h_trans
          -- LHS: `(e.trans.map f).get? rest.length = (e.trans.get? rest.length).map f`.
          rw [Stream'.Seq.map_get?] at h_idx
          -- RHS: index `rest.length` in `append` lands at position 0 of the cons-tail.
          have h_min : ∀ k < rest.length,
              ¬ (Stream'.Seq.ofList rest).TerminatedAt k := by
            intro k hk hterm
            -- `(↑rest).TerminatedAt k` means `(↑rest).get? k = none`, i.e. `rest[k]? = none`,
            -- which contradicts `k < rest.length`.
            rw [show (Stream'.Seq.ofList rest).TerminatedAt k
                  ↔ (Stream'.Seq.ofList rest).get? k = none from Iff.rfl] at hterm
            rw [Stream'.Seq.ofList_get?] at hterm
            exact absurd hterm (by
              rw [List.getElem?_eq_getElem hk]; exact Option.some_ne_none _)
          have h_done : (Stream'.Seq.ofList rest).TerminatedAt rest.length :=
            Stream'.Seq.terminatedAt_ofList rest
          have h_rhs : ((Stream'.Seq.ofList rest).append
              (Stream'.Seq.cons (l, μ_succ) Stream'.Seq.nil)).get? rest.length
              = some (l, μ_succ) := by
            have := Stream'.Seq.get?_append_after_length (s' :=
              Stream'.Seq.cons (l, μ_succ) Stream'.Seq.nil) h_min h_done 0
            rw [Nat.add_zero] at this
            rw [this, Stream'.Seq.get?_cons_zero]
          rw [h_rhs] at h_idx
          -- `h_idx : (e.trans.get? rest.length).map (fun lq => (lq.1, PMF.pure lq.2))
          --           = some (l, μ_succ)`.
          rcases h_e : e.trans.get? rest.length with _ | ⟨l_e, s_e⟩
          · rw [h_e] at h_idx; simp at h_idx
          · rw [h_e] at h_idx
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h_idx
            exact h_not_pure s_e h_idx.2.symm
        rw [dif_neg h_not_full]
    · -- Truncated NOT in image: LHS = 0. Full E also NOT in image.
      rw [dif_neg h_trunc, zero_mul]
      have h_not_full : ¬ ∃ e : AlterSeq State Label,
          e.dirac = (⟨μ_init, (Stream'.Seq.ofList rest).append
            (Stream'.Seq.cons (l, μ_succ) Stream'.Seq.nil)⟩
            : AlterSeq (PMF State) Label) := by
        rintro ⟨e, he⟩
        -- If `e.dirac` matches the full execution, split `e.trans` as
        -- `previous.append (cons last nil)`. Then `(⟨e.init, previous⟩).dirac`
        -- matches the truncated execution, contradicting `h_trunc`.
        have h_init : PMF.pure e.init = μ_init := congr_arg AlterSeq.init he
        have h_trans_map :
            e.trans.map (fun lq : Label × State => (lq.1, PMF.pure lq.2))
            = (Stream'.Seq.ofList rest).append
                (Stream'.Seq.cons (l, μ_succ) Stream'.Seq.nil) :=
          congr_arg AlterSeq.trans he
        -- `e.trans` terminates because its Dirac-lift does (=RHS sequence).
        have h_e_dirac_term : e.dirac.trans.Terminates := by
          have h_dt : e.dirac.trans = (Stream'.Seq.ofList rest).append
              (Stream'.Seq.cons (l, μ_succ) Stream'.Seq.nil) :=
            congr_arg AlterSeq.trans he
          rw [h_dt]; exact hFin
        have h_e_term : e.trans.Terminates :=
          (AlterSeq.dirac_trans_terminates_iff e).mp h_e_dirac_term
        -- `e.trans.toList` is non-empty: its mapped version has length `rest.length + 1`.
        have h_e_toList_ne : e.trans.toList h_e_term ≠ [] := by
          intro hempty
          -- From `hempty`, `e.trans.length' = 0`, hence `(e.trans.map _).length' = 0`,
          -- hence the RHS `((↑rest).append (cons (l,μ_succ) nil)).length' = 0`.
          -- But the RHS toList has length `rest.length + 1 > 0`.
          have h_len_e : e.trans.length' = 0 := by
            rw [Stream'.Seq.length'_of_terminates h_e_term]
            have := Stream'.Seq.length_toList e.trans h_e_term
            rw [hempty, List.length_nil] at this
            -- `this : 0 = e.trans.length h_e_term`
            simp [← this]
          have h_len_map : (e.trans.map
              (fun lq : Label × State => (lq.1, PMF.pure lq.2))).length' = 0 := by
            rw [Stream'.Seq.length'_map]; exact h_len_e
          rw [h_trans_map] at h_len_map
          have h_rhs_pos :
              ((Stream'.Seq.ofList rest).append
                (Stream'.Seq.cons (l, μ_succ) Stream'.Seq.nil)).length' = rest.length + 1 := by
            rw [Stream'.Seq.length'_of_terminates hFin]
            have h_eq := Stream'.Seq.length_toList
              ((Stream'.Seq.ofList rest).append
                (Stream'.Seq.cons (l, μ_succ) Stream'.Seq.nil)) hFin
            rw [hL_eq, List.length_append, List.length_singleton] at h_eq
            rw [← h_eq]; push_cast; ring
          rw [h_rhs_pos] at h_len_map
          -- `h_len_map : ((rest.length + 1 : ℕ) : ℕ∞) = 0`. Contradiction.
          have : (rest.length + 1 : ℕ) = 0 := by exact_mod_cast h_len_map
          exact Nat.succ_ne_zero _ this
        -- Split `e.trans` as `previous.append (cons last nil)`.
        obtain ⟨previous, last, h_prev_term, h_split, _, _⟩ :=
          Stream'.Seq.exists_split_last e.trans h_e_term h_e_toList_ne
        -- Substitute the split into `h_trans_map`.
        rw [h_split, Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil]
          at h_trans_map
        -- Apply `append_singleton_inj_left` to derive `previous.map = ofList rest`.
        have h_prev_map_term :
            (previous.map (fun lq : Label × State => (lq.1, PMF.pure lq.2))).Terminates :=
          Stream'.Seq.terminates_map_iff.mpr h_prev_term
        have h_prev_map_eq :
            previous.map (fun lq : Label × State => (lq.1, PMF.pure lq.2))
            = Stream'.Seq.ofList rest :=
          Stream'.Seq.append_singleton_inj_left _ _ h_prev_map_term hrest_fin _ _ h_trans_map
        -- Witness for `h_trunc`: `⟨e.init, previous⟩`.
        apply h_trunc
        refine ⟨⟨e.init, previous⟩, ?_⟩
        change (⟨PMF.pure e.init,
            previous.map (fun lq : Label × State => (lq.1, PMF.pure lq.2))⟩
            : AlterSeq (PMF State) Label) = ⟨μ_init, Stream'.Seq.ofList rest⟩
        rw [h_init, h_prev_map_eq]
      rw [dif_neg h_not_full]

/-- The Dirac-lift preserves the trace: external/internal labels of an
execution are unchanged when lifting to `𝒟(sys)`, since `𝒟(sys).internal
= sys.internal` and `dirac` preserves all labels.

This is the central reason why the trace-probability transfer works: both
sides of the `(filter ∘ map)` definition of `trace` see the same label
sequence on `e` and on `e.dirac`. -/
theorem AlterSeq.dirac_trace (sys : LabelledSystem State Label)
    (e : AlterSeq State Label) :
    𝒟(sys).trace e.dirac = sys.trace e := by
  -- Unfold both traces. `𝒟(sys).internal = sys.internal` definitionally, and
  -- `e.dirac.trans = e.trans.map g` where `g lq = (lq.1, PMF.pure lq.2)`.
  -- The predicate `(¬ sys.internal ·.1)` factors through `g` (since `g`
  -- preserves the label component), so we can interchange `filter` and `map`
  -- via `Seq.filter_map`, then reduce `(_.map g).map Prod.fst` to `_.map Prod.fst`.
  unfold LabelledSystem.trace
  change ((e.trans.map (fun lq => (lq.1, PMF.pure lq.2))).filter
        (fun p => ¬ sys.internal p.1)).map Prod.fst = _
  rw [Seq.filter_map (fun lq : Label × State => (lq.1, PMF.pure lq.2))
        (fun p : Label × PMF State => ¬ sys.internal p.1)]
  rw [← Seq.map_comp]
  rfl

/-- The Dirac-lift preserves trace-tightness. Tightness is a statement about
the labels of the last transition (whether it exists and whether it is
external), which `dirac` preserves verbatim — internal is inherited from
`sys` to `𝒟(sys)`, and `dirac` only changes the state component of each
transition. -/
theorem AlterSeq.dirac_isTight_iff (sys : LabelledSystem State Label)
    (e : AlterSeq State Label) :
    𝒟(sys).IsTight e.dirac ↔ sys.IsTight e := by
  unfold LabelledSystem.IsTight
  constructor
  · rintro (h_term_0 | ⟨n, l, μ, h_get, h_term_succ, h_not_int⟩)
    · left
      change (e.trans.map (fun lq => (lq.1, PMF.pure lq.2))).TerminatedAt 0 at h_term_0
      rwa [Stream'.Seq.terminatedAt_map_iff] at h_term_0
    · right
      change (e.trans.map (fun lq => (lq.1, PMF.pure lq.2))).get? n = some (l, μ) at h_get
      rw [Stream'.Seq.map_get?] at h_get
      obtain ⟨⟨l', s⟩, h_e_get, h_eq⟩ := Option.map_eq_some_iff.mp h_get
      simp only [Prod.mk.injEq] at h_eq
      obtain ⟨rfl, _⟩ := h_eq
      refine ⟨n, l', s, h_e_get, ?_, h_not_int⟩
      change (e.trans.map (fun lq => (lq.1, PMF.pure lq.2))).TerminatedAt (n + 1) at h_term_succ
      rwa [Stream'.Seq.terminatedAt_map_iff] at h_term_succ
  · rintro (h_term_0 | ⟨n, l, s, h_get, h_term_succ, h_not_int⟩)
    · left
      change (e.trans.map (fun lq => (lq.1, PMF.pure lq.2))).TerminatedAt 0
      rwa [Stream'.Seq.terminatedAt_map_iff]
    · right
      refine ⟨n, l, PMF.pure s, ?_, ?_, h_not_int⟩
      · change (e.trans.map (fun lq => (lq.1, PMF.pure lq.2))).get? n = some (l, PMF.pure s)
        rw [Stream'.Seq.map_get?, h_get]; rfl
      · change (e.trans.map (fun lq => (lq.1, PMF.pure lq.2))).TerminatedAt (n + 1)
        rwa [Stream'.Seq.terminatedAt_map_iff]

/-- **Subset direction of `dist_traceProb_eq`.** Given a probabilistic
execution `pe` of `sys`, its Dirac-lift `pe.dist` is a probabilistic
execution of `𝒟(sys)` achieving the same trace distribution. -/
theorem dist_traceProb_subset (sys : LabelledSystem State Label) :
    achievableTraceDists sys ⊆ achievableTraceDists 𝒟(sys) := by
  classical
  intro D hD
  obtain ⟨pe, h_pe⟩ := hD
  refine ⟨pe.dist, fun τ => ?_⟩
  rw [← h_pe τ]
  -- Goal: 𝒟(sys).traceProb pe.dist τ = sys.traceProb pe τ
  unfold LabelledSystem.traceProb
  -- Use `tsum_eq_tsum_of_ne_zero_bij` with the injection
  -- `e ↦ ⟨e.1.dirac, ...⟩` from the RHS subtype into the LHS subtype.
  set RHSSubtype : Type := {e : AlterSeq State Label //
      e.trans.Terminates ∧ sys.trace e = τ ∧ sys.IsTight e} with hRHS
  set LHSSubtype : Type := {E : AlterSeq (PMF State) Label //
      E.trans.Terminates ∧ 𝒟(sys).trace E = τ ∧ 𝒟(sys).IsTight E} with hLHS
  set g : RHSSubtype → ENNReal := fun e => pe.probOf e.1 e.2.1 with hg
  set f : LHSSubtype → ENNReal := fun E => pe.dist.probOf E.1 E.2.1 with hf
  change (∑' E : LHSSubtype, f E) = ∑' e : RHSSubtype, g e
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun e : Function.support g =>
      (⟨e.1.1.dirac,
        (AlterSeq.dirac_trans_terminates_iff e.1.1).mpr e.1.2.1,
        (AlterSeq.dirac_trace sys e.1.1).trans e.1.2.2.1,
        (AlterSeq.dirac_isTight_iff sys e.1.1).mpr e.1.2.2.2⟩ : LHSSubtype))
    ?_ ?_ ?_
  · -- Injectivity.
    rintro ⟨⟨e₁, h₁⟩, hsupp₁⟩ ⟨⟨e₂, h₂⟩, hsupp₂⟩ h_eq
    have h_dirac : e₁.dirac = e₂.dirac := congr_arg Subtype.val h_eq
    have : e₁ = e₂ := AlterSeq.dirac_injective h_dirac
    subst this
    rfl
  · -- Support of LHS lies in range of `i`: any `E` with non-zero
    -- `pe.dist.probOf E _` must be in the image of `dirac`, and the
    -- preimage satisfies the RHS conditions.
    rintro ⟨E, hE_fin, hE_trace, hE_tight⟩ hE_ne
    simp only [Function.mem_support, ne_eq, hf] at hE_ne
    -- Use `dist_probOf`: if `E` is not in the dirac image, value is 0.
    rw [ProbabilisticExecution.dist_probOf] at hE_ne
    by_cases h_im : ∃ e : AlterSeq State Label, e.dirac = E
    · -- E = e.dirac for some e; the preimage is the corresponding RHS element.
      rw [dif_pos h_im] at hE_ne
      obtain ⟨e, he⟩ := h_im
      -- The conditions on `e` follow from those on `E` and the helper lemmas.
      have he_fin : e.trans.Terminates :=
        (AlterSeq.dirac_trans_terminates_iff e).mp (he.symm ▸ hE_fin)
      have he_trace : sys.trace e = τ := by
        rw [← AlterSeq.dirac_trace sys e, he]; exact hE_trace
      have he_tight : sys.IsTight e :=
        (AlterSeq.dirac_isTight_iff sys e).mp (he.symm ▸ hE_tight)
      refine ⟨⟨⟨e, he_fin, he_trace, he_tight⟩, ?_⟩, ?_⟩
      · -- e is in the support: pe.probOf e _ ≠ 0.
        simp only [Function.mem_support, ne_eq]
        -- From hE_ne in the `then` branch.
        intro h_zero
        apply hE_ne
        -- pe.probOf h_im.choose _ = pe.probOf e _ because dirac is injective.
        have h_choose : (⟨e, he⟩ : ∃ e' : AlterSeq State Label, e'.dirac = E).choose = e :=
          AlterSeq.dirac_injective
            ((⟨e, he⟩ : ∃ e' : AlterSeq State Label, e'.dirac = E).choose_spec.trans he.symm)
        -- Rewrite the choose to `e`.
        convert h_zero using 2
      · -- Match: `i` of preimage equals `E`.
        exact Subtype.ext he
    · rw [dif_neg h_im] at hE_ne
      exact absurd rfl hE_ne
  · -- Values match: `f (i x) = g x`, where `f` is LHS sum and `g` is RHS sum.
    rintro ⟨⟨e, he_fin, he_trace, he_tight⟩, hsupp⟩
    -- Goal: pe.dist.probOf e.dirac _ = pe.probOf e _.
    simp only [hf, hg]
    rw [ProbabilisticExecution.dist_probOf]
    have h_im : ∃ e' : AlterSeq State Label, e'.dirac = e.dirac := ⟨e, rfl⟩
    rw [dif_pos h_im]
    -- `h_im.choose` is `e` by injectivity.
    have h_choose : h_im.choose = e :=
      AlterSeq.dirac_injective h_im.choose_spec
    congr 1

/-- **Superset direction of `dist_traceProb_eq`** (deferred). -/
theorem dist_traceProb_superset (sys : LabelledSystem State Label) :
    achievableTraceDists 𝒟(sys) ⊆ achievableTraceDists sys := by
  sorry

/-- **Distribution-monad construction preserves trace distributions.** -/
theorem dist_traceProb_eq (sys : LabelledSystem State Label) :
    achievableTraceDists sys = achievableTraceDists 𝒟(sys) :=
  Set.Subset.antisymm
    (dist_traceProb_subset sys)
    (dist_traceProb_superset sys)

end PLTS
