/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.PmfUtils
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
noncomputable abbrev AlterSeq.dirac (e : AlterSeq State Label) :
    AlterSeq (PMF State) Label :=
  e.map PMF.pure

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
        set e₀ := hImg.choose
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
theorem AlterSeq.dirac_trans_terminates_iff (e : AlterSeq State Label) :
    e.dirac.trans.Terminates ↔ e.trans.Terminates :=
  AlterSeq.map_trans_terminates_iff PMF.pure e

/-- `AlterSeq.dirac` is injective: the Dirac-lift uniquely determines its
preimage. -/
theorem AlterSeq.dirac_injective :
    Function.Injective (@AlterSeq.dirac State Label) :=
  AlterSeq.map_injective PMF.pure_injective

/-- Unfolding of the lifted scheduler on a Dirac-lifted history. By
injectivity of `dirac`, the `Classical.choose` inside `Scheduler.dist`'s
`then` branch is the original `e`. -/
@[simp] theorem Scheduler.dist_next_dirac {sys : LabelledSystem State Label}
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
  have h_map_inj : Function.Injective (@PMF.map State (PMF State) PMF.pure) :=
    PMF.map_injective PMF.pure_injective
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
        (Stream'.Seq.cons (l, PMF.pure s') Stream'.Seq.nil)⟩ :=
  AlterSeq.map_append_singleton PMF.pure e l s'

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
      set e_t := h_trunc.choose
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
            simpa [AlterSeq.dirac, AlterSeq.map] using this
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

/-- **Probability is preserved by the Dirac-lift.** Specialization of
`dist_probOf` to the Dirac case: the lifted execution `pe.dist` assigns
to `e.dirac` the same probability that `pe` assigns to `e`. -/
theorem ProbabilisticExecution.dist_probOf_dirac
    {sys : LabelledSystem State Label} (pe : ProbabilisticExecution sys.toSystem)
    (e : AlterSeq State Label) (h_fin : e.trans.Terminates) :
    pe.dist.probOf e.dirac ((AlterSeq.dirac_trans_terminates_iff e).mpr h_fin)
      = pe.probOf e h_fin := by
  have h_im : ∃ e' : AlterSeq State Label, e'.dirac = e.dirac := ⟨e, rfl⟩
  have : h_im.choose = e := AlterSeq.dirac_injective h_im.choose_spec
  rw [dist_probOf, dif_pos h_im]
  congr 1

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
  intro D ⟨pe, h_init, h_pe⟩
  refine ⟨pe.dist, ?_, fun τ => ?_⟩
  · -- The Dirac-lift `pe.dist` also starts at `𝒟(sys)`'s initial state.
    have hD : (𝒟(sys)).toSystem.init = PMF.pure sys.toSystem.init := rfl
    change pe.dist.initState = PMF.pure 𝒟(sys).toSystem.init
    rw [hD, show pe.dist.initState = pe.initState.map PMF.pure from rfl, h_init,
      PMF.pure_map]
  rw [← h_pe τ]
  unfold LabelledSystem.traceProb
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun e => ⟨e.1.1.dirac,
      (AlterSeq.dirac_trans_terminates_iff e.1.1).mpr e.1.2.1,
      (AlterSeq.dirac_trace sys e.1.1).trans e.1.2.2.1,
      (AlterSeq.dirac_isTight_iff sys e.1.1).mpr e.1.2.2.2⟩)
    (fun _ _ h => Subtype.ext (Subtype.ext
      (AlterSeq.dirac_injective (congr_arg Subtype.val h))))
    ?_
    (fun ⟨⟨e, he_fin, _, _⟩, _⟩ => pe.dist_probOf_dirac e he_fin)
  rintro ⟨E, hE_fin, hE_trace, hE_tight⟩ hE_ne
  change pe.dist.probOf E hE_fin ≠ 0 at hE_ne
  rw [ProbabilisticExecution.dist_probOf] at hE_ne
  split_ifs at hE_ne with h_im
  · set e := h_im.choose
    have he : e.dirac = E := h_im.choose_spec
    rw [← he] at hE_fin hE_trace hE_tight
    exact ⟨⟨⟨e, (AlterSeq.dirac_trans_terminates_iff e).mp hE_fin,
      (AlterSeq.dirac_trace sys e) ▸ hE_trace,
      (AlterSeq.dirac_isTight_iff sys e).mp hE_tight⟩, hE_ne⟩,
      Subtype.ext he⟩
  · exact absurd rfl hE_ne

/-! ### Inverting the lift: from `𝒟(sys)`-execution back to `sys`-execution

The superset direction converts a `𝒟(sys)`-probabilistic execution `pe'` into a
`sys`-probabilistic execution with the same trace distribution.

A `𝒟(sys)`-transition `μ -[l]→ ω` is a `hyperStep sys μ l (ω.bind id)`, which
decomposes — via a witness `p : State → PMF (PMF State)` — into per-state
`sys`-steps: for `s ∈ μ.support`, every `μ' ∈ (p s).support` satisfies
`sys.step s l μ'` (no internal stutter). `distHyperKernel` selects such a `p`.

The `sys`-witness `ProbabilisticExecution.lower` runs the decomposition: at
`sys`-state `s` it samples a `𝒟(sys)`-history `E` from the **trace-cone belief**
`beliefTC` (conditioned only on the current trace and on `s`), draws
`(l, ω) ∼ pe'.scheduler.next E`, and steps by `distHyperKernel E l ω s`. Trace
preservation rests on the invariant `ρ_σ = (Ω_σ).bind id`, preserved one step at
a time by `hyperStep_marginal_decomp` (see `lower_traceProb_eq`).

A naive witness conditioning on the *full* `sys`-history instead of the
trace-cone fails: it over-conditions on intermediate states and does not
preserve trace distributions. -/

/-- The per-state hyperStep kernel of `pe'.scheduler.next E` at emission
`(l, ω)`. When `(l, ω)` lies in the support of `pe'.scheduler.next E` and
`E` terminates, `pe'.scheduler.valid` yields
`hyperStep sys (E.endState) l (ω.bind id)`; we classically choose a per-state
successor kernel from this witness. Outside that case the value is irrelevant
(downstream uses are multiplied by zero). -/
noncomputable def ProbabilisticExecution.distHyperKernel
    {sys : LabelledSystem State Label}
    (_pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (E : AlterSeq (PMF State) Label) (l : Label) (ω : PMF (PMF State)) :
    State → PMF (PMF State) :=
  open Classical in
  if h : ∃ hE : E.trans.Terminates,
      hyperStep sys (E.endState hE) l (ω.bind id) then
    (h.choose_spec).kernel
  else
    fun _ => PMF.pure (ω.bind id)

/-- **Validity of `distHyperKernel`.** At an emission `(l, ω)` in the
support of `pe'.scheduler.next E` (with `E` finite), every distribution
in `(distHyperKernel pe' E l ω s).support` for `s ∈ (E.endState hE).support`
is a valid `sys.step` post-distribution from `s`. This is the per-state
`hyperStep.kernel_step` repackaged for the constructed scheduler's
validity proof. -/
theorem ProbabilisticExecution.distHyperKernel_step
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    {E : AlterSeq (PMF State) Label} (hE : E.trans.Terminates)
    {l : Label} {ω : PMF (PMF State)}
    (h_supp : some (l, ω) ∈ (pe'.scheduler.next E).support)
    {s : State} (h_s : s ∈ (E.endState hE).support)
    {μ : PMF State}
    (h_μ : μ ∈ (pe'.distHyperKernel E l ω s).support) :
    sys.step s l μ := by
  classical
  -- Invoke `pe'.scheduler.valid` at canonical termination position to extract
  -- `𝒟(sys).step (E.endState hE) l ω = hyperStep sys (E.endState hE) l (ω.bind id)`.
  have h_hyper : hyperStep sys (E.endState hE) l (ω.bind id) := by
    have := pe'.scheduler.valid E (Nat.find hE) (E.endState hE)
      (Nat.find_spec hE) (AlterSeq.stateAt_find_eq_endState E hE) l ω h_supp
    -- `this : 𝒟(sys).toSystem.step (E.endState hE) l ω`
    -- By definition `𝒟(sys).step = fun μ l ω => hyperStep sys μ l (ω.bind id)`.
    exact this
  -- The existential in `distHyperKernel` holds; the value is `h_hyper'.kernel`
  -- for some classically chosen `h_hyper'`. The kernel_step lemma applies.
  have hex : ∃ hE' : E.trans.Terminates,
      hyperStep sys (E.endState hE') l (ω.bind id) := ⟨hE, h_hyper⟩
  have h_def : pe'.distHyperKernel E l ω = hex.choose_spec.kernel := by
    unfold ProbabilisticExecution.distHyperKernel
    rw [dif_pos hex]
  rw [h_def] at h_μ
  -- Now `h_μ : μ ∈ (hex.choose_spec.kernel s).support`. Need `s ∈ μ_pre.support`
  -- where `μ_pre = E.endState hex.choose`. Since `hex.choose` and `hE` are both
  -- proofs of `E.trans.Terminates`, they're propositionally equal (Prop).
  have h_choose : hex.choose = hE := Subsingleton.elim _ _
  -- Apply `hyperStep.kernel_step`.
  have h_kstep := hex.choose_spec.kernel_step
  -- `h_kstep : ∀ s' ∈ (E.endState hex.choose).support, ∀ μ' ∈ (kernel s').support,
  --              sys.step s' l μ'`
  rw [h_choose] at h_kstep
  exact h_kstep s h_s μ h_μ

/-- **Hyperstep marginal decomposition.** For a 𝒟(sys)-scheduler emission
`(l, ω)` at a terminating history `E`, the post-state marginal of `ω`
decomposes as the state-wise mixture of the per-state hyperStep-kernel
bind:
```
(ω.bind id) q = ∑' s, (E.endState hE) s · ((distHyperKernel E l ω s).bind id) q
```
This is the `μ_post = μ_pre.bind (fun s => (p s).bind id)` conjunct of the
hyperStep witness, restated in terms of `distHyperKernel`. It is the bridge
identity behind the one-step trace-cone invariant (`lower_traceProb_eq`).

Proof outline: from `pe'.scheduler.valid` extract a hyperStep witness for
`hyperStep sys (E.endState hE) l (ω.bind id)`. The witness's
`post_eq_bind` conjunct gives the equality. Reconcile the
classically-chosen `distHyperKernel` with the scheduler-extracted kernel
via `Subsingleton.elim` on `Terminates` proofs (as in
`distHyperKernel_step`). -/
private theorem ProbabilisticExecution.hyperStep_marginal_decomp
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    {E : AlterSeq (PMF State) Label} (hE : E.trans.Terminates)
    {l : Label} {ω : PMF (PMF State)}
    (h_supp : some (l, ω) ∈ (pe'.scheduler.next E).support)
    (q : State) :
    (ω.bind id) q
      = ∑' s : State, (E.endState hE) s *
          ((pe'.distHyperKernel E l ω s).bind id) q := by
  classical
  -- Extract hyperStep witness from `pe'.scheduler.valid`.
  have h_hyper : hyperStep sys (E.endState hE) l (ω.bind id) := by
    have := pe'.scheduler.valid E (Nat.find hE) (E.endState hE)
      (Nat.find_spec hE) (AlterSeq.stateAt_find_eq_endState E hE) l ω h_supp
    change hyperStep sys (E.endState hE) l (ω.bind id) at this
    exact this
  -- The existential in `distHyperKernel` holds; expose the classical kernel.
  have hex : ∃ hE' : E.trans.Terminates,
      hyperStep sys (E.endState hE') l (ω.bind id) := ⟨hE, h_hyper⟩
  have h_def : pe'.distHyperKernel E l ω = hex.choose_spec.kernel := by
    unfold ProbabilisticExecution.distHyperKernel
    rw [dif_pos hex]
  -- post_eq_bind: `(ω.bind id) = (E.endState hex.choose).bind (fun s => (kernel s).bind id)`.
  have h_post := hex.choose_spec.post_eq_bind
  have h_choose : hex.choose = hE := Subsingleton.elim _ _
  -- Evaluate at q.
  conv_lhs => rw [h_post]
  rw [PMF.bind_apply]
  -- Goal: `∑' s, (E.endState hex.choose) s * ((kernel s).bind id) q
  --     = ∑' s, (E.endState hE) s * ((distHyperKernel E l ω s).bind id) q`.
  apply tsum_congr
  intro s
  rw [h_choose, h_def]

/-! ### The trace-cone belief and the witness execution -/

/-- Unnormalized weight of the trace-cone belief: mass on `𝒟(sys)`-histories `E`
whose **full label sequence** equals `labs`, weighted by the current-state mass
`(E.endState) s`. Conditioning on the full label list (internal labels included),
rather than the external trace, keeps the normalizer finite (a level sum, see
`beliefTCw_tsum_ne_top`) and makes the trace-cone invariant step uniform. -/
noncomputable def ProbabilisticExecution.beliefTCw
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
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
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
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
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem) :
    (∑' E : AlterSeq (PMF State) Label,
        dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList ([] : List Label))
          (fun h => pe'.probOf E h.1) (fun _ => 0)) = 1 := by
  have h := pe'.labMass_nil (fun _ => (1 : ENNReal))
  simpa only [ProbabilisticExecution.labMass, mul_one, PMF.tsum_coe] using h

/-- The summed one-step kernel is `≤ 1` (the scheduler emits a sub-probability). -/
theorem ProbabilisticExecution.tsum_kernel_le_one
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
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
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem) (labs : List Label) :
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
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
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
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
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
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
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
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem) :
    Scheduler sys.toSystem where
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
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem) :
    ProbabilisticExecution sys.toSystem where
  initState := pe'.initState.bind id
  scheduler := Scheduler.lower pe'

open Classical in
/-- **Append-singleton step of the level-mass recursion** (the `g`-weighted,
generic-system generalisation of `tsum_probOf_labels_append`). Reindex by the
bijection `e = ⟨e'.init, e'.trans.append (cons (l,s') nil)⟩`, using
`endState_append_singleton` (`e.endState = s'`) and `probOf_append_singleton`. -/
theorem ProbabilisticExecution.labMass_append {S : Type} {Sys : System S Label}
    (pe : ProbabilisticExecution Sys) (labs : List Label) (l : Label) (g : S → ENNReal) :
    pe.labMass (labs ++ [l]) g
      = ∑' (e' : AlterSeq S Label) (s' : S),
          dite (e'.trans.Terminates ∧ e'.trans.map Prod.fst = Seq.ofList labs)
            (fun h => pe.probOf e' h.1 * pe.kernel e' (l, s') * g s') (fun _ => 0) := by
  classical
  unfold ProbabilisticExecution.labMass
  rw [← ENNReal.tsum_prod' (f := fun p : AlterSeq S Label × S =>
      dite (p.1.trans.Terminates ∧ Seq.map Prod.fst p.1.trans = (↑labs : Seq Label))
        (fun h => pe.probOf p.1 h.1 * pe.kernel p.1 (l, p.2) * g p.2) (fun _ => 0))]
  -- Abbreviate the two summands.
  set f : AlterSeq S Label → ENNReal := fun e =>
      dite (e.trans.Terminates ∧ Seq.map Prod.fst e.trans = (↑(labs ++ [l]) : Seq Label))
        (fun h => pe.probOf e h.1 * g (e.endState h.1)) (fun _ => 0) with hf_def
  set gg : AlterSeq S Label × S → ENNReal := fun p =>
      dite (p.1.trans.Terminates ∧ Seq.map Prod.fst p.1.trans = (↑labs : Seq Label))
        (fun h => pe.probOf p.1 h.1 * pe.kernel p.1 (l, p.2) * g p.2) (fun _ => 0) with hgg_def
  -- Helper: membership in `support gg` forces the then-branch condition.
  have g_supp_cond : ∀ p : AlterSeq S Label × S, gg p ≠ 0 →
      p.1.trans.Terminates ∧ Seq.map Prod.fst p.1.trans = (↑labs : Seq Label) := by
    intro p hp
    by_contra hcond
    rw [hgg_def] at hp
    simp only at hp
    rw [dif_neg hcond] at hp
    exact hp rfl
  -- Helper: membership in `support f` forces the then-branch condition.
  have f_supp_cond : ∀ e : AlterSeq S Label, f e ≠ 0 →
      e.trans.Terminates ∧ Seq.map Prod.fst e.trans = (↑(labs ++ [l]) : Seq Label) := by
    intro e he
    by_contra hcond
    rw [hf_def] at he
    simp only at he
    rw [dif_neg hcond] at he
    exact he rfl
  -- The forward bijection `(e', s') ↦ ⟨e'.init, e'.trans.append (cons (l,s') nil)⟩`.
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun x => (⟨(x.1).1.init,
        (x.1).1.trans.append (Seq.cons (l, (x.1).2) Seq.nil)⟩ : AlterSeq S Label))
    ?hinj ?hf ?hfg
  case hinj =>
    rintro x y hxy
    have hx := g_supp_cond x.1 x.2
    have hy := g_supp_cond y.1 y.2
    have h_trans := congrArg AlterSeq.trans hxy
    have h_init := congrArg AlterSeq.init hxy
    simp only at h_trans h_init
    have h_last := Stream'.Seq.append_singleton_inj_right
      (x.1).1.trans (y.1).1.trans hx.1 hy.1 _ _ h_trans
    have hs' : (x.1).2 = (y.1).2 := (Prod.mk.inj h_last).2
    have h_prev := Stream'.Seq.append_singleton_inj_left
      (x.1).1.trans (y.1).1.trans hx.1 hy.1 _ _ h_trans
    refine Subtype.ext (Prod.ext ?_ hs')
    exact congrArg₂ AlterSeq.mk h_init h_prev
  case hf =>
    intro e he_mem
    have he := f_supp_cond e (Function.mem_support.mp he_mem)
    -- `e.trans` is nonempty.
    have h_ne : e.trans.toList he.1 ≠ [] := by
      intro hnil
      have h_map_nil : e.trans.map Prod.fst = Stream'.Seq.nil := by
        have : e.trans = Stream'.Seq.nil := by
          rw [← Stream'.Seq.ofList_toList e.trans he.1, hnil, Stream'.Seq.ofList_nil]
        rw [this, Stream'.Seq.map_nil]
      rw [he.2] at h_map_nil
      have h_len := congrArg Stream'.Seq.length' h_map_nil
      rw [Stream'.Seq.length'_nil,
        Stream'.Seq.length'_of_terminates (Stream'.Seq.terminates_ofList _),
        ← Stream'.Seq.length_toList _ (Stream'.Seq.terminates_ofList _),
        Stream'.Seq.toList_ofList] at h_len
      simp only [List.length_append, List.length_singleton, Nat.cast_eq_zero] at h_len
      omega
    -- Split `e.trans = prev.append (cons last nil)`.
    obtain ⟨prev, last, h_prev_term, h_split, _, _⟩ :=
      Stream'.Seq.exists_split_last e.trans he.1 h_ne
    have h_trans_map := he.2
    rw [h_split, Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil] at h_trans_map
    rw [show (↑(labs ++ [l]) : Seq Label)
        = (↑labs : Seq Label).append (Seq.cons l Seq.nil) by
        rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]]
      at h_trans_map
    have h_prev_map_term : (prev.map Prod.fst).Terminates :=
      Stream'.Seq.terminates_map_iff.mpr h_prev_term
    have h_prev_map : prev.map Prod.fst = (↑labs : Seq Label) :=
      Stream'.Seq.append_singleton_inj_left _ _ h_prev_map_term
        (Stream'.Seq.terminates_ofList _) _ _ h_trans_map
    have h_last : last.1 = l :=
      Stream'.Seq.append_singleton_inj_right _ _ h_prev_map_term
        (Stream'.Seq.terminates_ofList _) _ _ h_trans_map
    -- The reassembled history equals `e`.
    have h_app_term : (prev.append (Seq.cons (l, last.2) Seq.nil)).Terminates := by
      rw [show (Seq.cons (l, last.2) Seq.nil) = Seq.cons last Seq.nil by
        rw [← h_last]]
      exact h_split ▸ he.1
    have h_reassemble : (⟨e.init, prev.append (Seq.cons (l, last.2) Seq.nil)⟩
        : AlterSeq S Label) = e := by
      refine congrArg₂ AlterSeq.mk rfl ?_
      rw [show (Seq.cons (l, last.2) Seq.nil) = Seq.cons last Seq.nil by rw [← h_last]]
      exact h_split.symm
    -- The preimage `(⟨e.init, prev⟩, last.2)` lies in `support gg`.
    have hg_pos : gg (⟨e.init, prev⟩, last.2) ≠ 0 := by
      rw [hgg_def]; simp only
      rw [dif_pos ⟨h_prev_term, h_prev_map⟩]
      have h_factor := ProbabilisticExecution.probOf_append_singleton pe
        e.init prev h_prev_term (l, last.2) h_app_term
      have h_probOf_e : pe.probOf e he.1 ≠ 0 := by
        have h_mem := Function.mem_support.mp he_mem
        change f e ≠ 0 at h_mem
        rw [hf_def] at h_mem; simp only at h_mem
        rw [dif_pos he] at h_mem
        exact fun hz => h_mem (by rw [hz, zero_mul])
      -- end-state of the reassembled history is `last.2`.
      have h_end_app : (⟨e.init, prev.append (Seq.cons (l, last.2) Seq.nil)⟩
          : AlterSeq S Label).endState h_app_term = last.2 := by
        have key := AlterSeq.endState_append_singleton
          (⟨e.init, prev⟩ : AlterSeq S Label) h_prev_term l last.2
        -- Both `endState` calls agree by proof irrelevance of the `Terminates` arg.
        exact key
      have h_g_e : g (e.endState he.1) = g last.2 := by
        have key : ∀ (A : AlterSeq S Label) (hA : A.trans.Terminates),
            A = (⟨e.init, prev.append (Seq.cons (l, last.2) Seq.nil)⟩ : AlterSeq S Label) →
            g (A.endState hA)
              = g ((⟨e.init, prev.append (Seq.cons (l, last.2) Seq.nil)⟩
                  : AlterSeq S Label).endState h_app_term) := by
          rintro A hA rfl; rfl
        rw [key e he.1 h_reassemble.symm, h_end_app]
      intro hzero
      apply h_probOf_e
      -- `pe.probOf e * g (e.endState) = (factored) * g last.2 = 0`.
      have key : ∀ (A : AlterSeq S Label) (hA : A.trans.Terminates),
          A = e → pe.probOf A hA = pe.probOf e he.1 := by
        rintro A hA rfl; rfl
      have h_eq : pe.probOf e he.1 * g (e.endState he.1)
          = (pe.probOf ⟨e.init, prev⟩ h_prev_term * pe.kernel ⟨e.init, prev⟩ (l, last.2))
            * g last.2 := by
        rw [h_g_e, ← key _ h_app_term h_reassemble, h_factor]
      have h_prod_zero : pe.probOf e he.1 * g (e.endState he.1) = 0 := by
        rw [h_eq, hzero]
      -- `g (e.endState) ≠ 0` since the `gg`-value is nonzero only if `g last.2 ≠ 0`...
      -- Actually we use that the f-membership product is nonzero.
      have h_f_ne : pe.probOf e he.1 * g (e.endState he.1) ≠ 0 := by
        have h_mem := Function.mem_support.mp he_mem
        change f e ≠ 0 at h_mem
        rw [hf_def] at h_mem; simp only at h_mem
        rwa [dif_pos he] at h_mem
      exact absurd h_prod_zero h_f_ne
    refine ⟨⟨(⟨e.init, prev⟩, last.2), hg_pos⟩, ?_⟩
    simp only
    exact h_reassemble
  case hfg =>
    rintro x
    set e' := (x.1).1 with he'_def
    set s' := (x.1).2 with hs'_def
    have hx := g_supp_cond x.1 x.2
    -- The RHS `gg ↑x` is in its then-branch.
    have h_gg : gg x.1 = pe.probOf e' hx.1 * pe.kernel e' (l, s') * g s' := by
      rw [hgg_def]; simp only; rw [dif_pos hx]
    -- Termination of the appended trans.
    have h_app_term : (e'.trans.append (Seq.cons (l, s') Seq.nil)).Terminates :=
      ⟨_, Stream'.Seq.terminatedAt_append_find hx.1
        (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil).choose_spec⟩
    -- The map of the appended trans is `↑(labs ++ [l])`.
    have h_map : Seq.map Prod.fst (e'.trans.append (Seq.cons (l, s') Seq.nil))
        = (↑(labs ++ [l]) : Seq Label) := by
      rw [Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil, hx.2,
        Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    -- The LHS `f (i x)` is in its then-branch.
    have h_f : f (⟨e'.init, e'.trans.append (Seq.cons (l, s') Seq.nil)⟩
        : AlterSeq S Label)
        = pe.probOf ⟨e'.init, e'.trans.append (Seq.cons (l, s') Seq.nil)⟩ h_app_term
          * g ((⟨e'.init, e'.trans.append (Seq.cons (l, s') Seq.nil)⟩
              : AlterSeq S Label).endState h_app_term) := by
      rw [hf_def]; simp only; rw [dif_pos ⟨h_app_term, h_map⟩]
    -- end-state of the appended history is `s'`.
    have h_end : (⟨e'.init, e'.trans.append (Seq.cons (l, s') Seq.nil)⟩
        : AlterSeq S Label).endState h_app_term = s' := by
      have key := AlterSeq.endState_append_singleton
        (⟨e'.init, e'.trans⟩ : AlterSeq S Label) hx.1 l s'
      -- `⟨e'.init, e'.trans⟩ = e'` definitionally; proof irrelevance on the `Terminates`
      -- argument makes the two `endState` calls equal.
      exact key
    change f (⟨e'.init, e'.trans.append (Seq.cons (l, s') Seq.nil)⟩
        : AlterSeq S Label) = gg x.1
    rw [h_f, h_gg, h_end]
    -- Factor via `probOf_append_singleton`.
    rw [ProbabilisticExecution.probOf_append_singleton pe e'.init e'.trans hx.1 (l, s')
      h_app_term]

open Classical in
/-- **Level-mass recursion**, kernel form: factor the appended-step sum so the
one-step kernel's `g`-expectation sits inside the level-`labs` `dite`. The form
used by both sides of the trace-cone induction. -/
theorem ProbabilisticExecution.labMass_step {S : Type} {Sys : System S Label}
    (pe : ProbabilisticExecution Sys) (labs : List Label) (l : Label) (g : S → ENNReal) :
    pe.labMass (labs ++ [l]) g
      = ∑' e' : AlterSeq S Label,
          dite (e'.trans.Terminates ∧ e'.trans.map Prod.fst = Seq.ofList labs)
            (fun h => pe.probOf e' h.1 * ∑' s' : S, pe.kernel e' (l, s') * g s')
            (fun _ => 0) := by
  classical
  rw [pe.labMass_append labs l g]
  refine tsum_congr (fun e' => ?_)
  by_cases hc : e'.trans.Terminates ∧ e'.trans.map Prod.fst = Seq.ofList labs
  · rw [dif_pos hc, ← ENNReal.tsum_mul_left]
    refine tsum_congr (fun s' => ?_)
    rw [dif_pos hc]; ring
  · rw [dif_neg hc]
    simp only [dif_neg hc, tsum_zero]

open Classical in
/-- **Lowered one-step kernel, integrated against `g`.** For a `sys`-history `e`
with label list `labs` and end-state `s`, the lowered kernel's `g`-expectation
factors through the trace-cone belief and the per-state hyper-kernel `bind id`. -/
theorem ProbabilisticExecution.lower_kernel_g_sum
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (labs : List Label) (l : Label) (g : State → ENNReal)
    (e : AlterSeq State Label) (h_term : e.trans.Terminates)
    (h_labs : (e.trans.toList h_term).map Prod.fst = labs)
    (s : State) (h_end : e.endState h_term = s) :
    (∑' s' : State, pe'.lower.kernel e (l, s') * g s')
      = ∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
          ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
            (∑' q : State, ((pe'.distHyperKernel E l ω s).bind id) q * g q) := by
  classical
  have key : ∀ ν : PMF State, pe'.lower.scheduler.next e (some (l, ν))
      = ∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
          (∑' ω : PMF (PMF State),
            pe'.scheduler.next E (some (l, ω)) * pe'.distHyperKernel E l ω s ν) := by
    intro ν
    change (if h : e.trans.Terminates then
        (pe'.beliefTC ((e.trans.toList h).map Prod.fst) (e.endState h)).bind (fun E =>
          (pe'.scheduler.next E).bind (fun opt =>
            match opt with
            | none => PMF.pure none
            | some (l, ω) =>
              (pe'.distHyperKernel E l ω (e.endState h)).map (fun μ' => some (l, μ'))))
      else PMF.pure none) (some (l, ν)) = _
    rw [dif_pos h_term, h_labs, h_end]
    rw [PMF.bind_apply]
    refine tsum_congr (fun E => ?_)
    congr 1
    rw [PMF.bind_apply]
    refine tsum_eq_tsum_of_ne_zero_bij
      (i := fun ω : Function.support (fun ω : PMF (PMF State) =>
        pe'.scheduler.next E (some (l, ω)) * pe'.distHyperKernel E l ω s ν) =>
        (some (l, (ω : PMF (PMF State))) : Option (Label × PMF (PMF State)))) ?hinj ?hf ?hfg
    case hinj =>
      rintro x y hxy
      exact Subtype.ext (Prod.mk.inj (Option.some.inj hxy)).2
    case hf =>
      intro opt hopt
      rw [Function.mem_support] at hopt
      rcases opt with _ | ⟨l₀, ω⟩
      · simp only [PMF.pure_apply_of_ne _ _ (by simp : (some (l, ν)) ≠ none), mul_zero,
          ne_eq, not_true_eq_false] at hopt
      · -- The map factor forces `l₀ = l`; produce the range witness.
        have hmap : (PMF.map (fun μ' => some (l₀, μ'))
            (pe'.distHyperKernel E l₀ ω s)) (some (l, ν)) ≠ 0 := right_ne_zero_of_mul hopt
        rw [PMF.map_apply] at hmap
        have hl : l₀ = l := by
          by_contra hne
          apply hmap
          rw [ENNReal.tsum_eq_zero]
          intro a
          exact if_neg (fun ha => hne (Prod.mk.inj (Option.some.inj ha)).1.symm)
        subst hl
        -- The map factor at `(some (l₀, ν))` evaluates to `dhk E l₀ ω s ν`.
        have hmap_eval : (PMF.map (fun μ' => some (l₀, μ'))
            (pe'.distHyperKernel E l₀ ω s)) (some (l₀, ν)) = pe'.distHyperKernel E l₀ ω s ν := by
          rw [PMF.map_apply]
          simp only [Option.some.injEq, Prod.mk.injEq, true_and, @eq_comm _ ν]
          exact tsum_ite_eq ν _
        rw [hmap_eval] at hopt
        exact ⟨⟨ω, hopt⟩, rfl⟩
    case hfg =>
      rintro ⟨ω, hω⟩
      simp only
      congr 1
      rw [PMF.map_apply]
      simp only [Option.some.injEq, Prod.mk.injEq, true_and, @eq_comm _ ν]
      exact tsum_ite_eq ν _
  -- The `bind id` push-forward abbreviation `C ν = ∑' q, ν q * g q`.
  set C : PMF State → ENNReal := fun ν => ∑' q : State, ν q * g q with hC_def
  -- Common normal form for the RHS.
  have hRHS : (∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
        ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
          (∑' q : State, ((pe'.distHyperKernel E l ω s).bind id) q * g q))
      = ∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
          ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
            (∑' ν : PMF State, pe'.distHyperKernel E l ω s ν * C ν) := by
    refine tsum_congr (fun E => ?_)
    congr 1
    refine tsum_congr (fun ω => ?_)
    congr 1
    -- `∑' q, (∑' ν, dhk ν * ν q) * g q = ∑' ν, dhk ν * C ν`.
    simp only [hC_def, PMF.bind_apply, id_eq]
    rw [show (∑' q : State, (∑' ν : PMF State, pe'.distHyperKernel E l ω s ν * ν q) * g q)
        = ∑' q : State, ∑' ν : PMF State, pe'.distHyperKernel E l ω s ν * (ν q * g q) from
      tsum_congr (fun q => by rw [← ENNReal.tsum_mul_right]; exact tsum_congr (fun ν => by ring))]
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun ν => ?_)
    rw [ENNReal.tsum_mul_left]
  -- The "push `* g s'` in, swap, pull weight out" reorganization, reused twice.
  have reorg : ∀ K : PMF State → ENNReal,
      (∑' s' : State, (∑' ν : PMF State, K ν * ν s') * g s')
        = ∑' ν : PMF State, K ν * C ν := by
    intro K
    rw [show (∑' s' : State, (∑' ν : PMF State, K ν * ν s') * g s')
        = ∑' s' : State, ∑' ν : PMF State, K ν * (ν s' * g s') from
      tsum_congr (fun s' => by rw [← ENNReal.tsum_mul_right]; exact tsum_congr (fun ν => by ring))]
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun ν => ?_)
    rw [hC_def, ENNReal.tsum_mul_left]
  rw [hRHS]
  -- Rewrite the LHS kernel and the lowered `next` via `key`, then reorganize.
  simp only [ProbabilisticExecution.kernel]
  rw [show (∑' s' : State,
        (∑' ν : PMF State, pe'.lower.scheduler.next e (some (l, ν)) * ν s') * g s')
      = ∑' ν : PMF State, pe'.lower.scheduler.next e (some (l, ν)) * C ν from reorg _]
  simp only [key]
  -- Reorganize `∑' ν, (∑' E, bel E * ∑' ω, next * dhk ν) * C ν` to the common form.
  rw [show (∑' ν : PMF State,
        (∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
          ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
            pe'.distHyperKernel E l ω s ν) * C ν)
      = ∑' E : AlterSeq (PMF State) Label, ∑' ν : PMF State,
          (pe'.beliefTC labs s E *
            ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
              pe'.distHyperKernel E l ω s ν) * C ν from by
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun ν => ?_)
    rw [← ENNReal.tsum_mul_right]]
  refine tsum_congr (fun E => ?_)
  -- Pull `beliefTC E` out of the `ν`-sum on the left.
  rw [show (∑' ν : PMF State,
        (pe'.beliefTC labs s E *
          ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
            pe'.distHyperKernel E l ω s ν) * C ν)
      = pe'.beliefTC labs s E * ∑' ν : PMF State,
          (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
            pe'.distHyperKernel E l ω s ν) * C ν from by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr (fun ν => by ring)]
  congr 1
  -- Now `∑' ν, (∑' ω, next * dhk ν) * C ν = ∑' ω, next * ∑' ν, dhk ν * C ν`.
  rw [show (∑' ν : PMF State,
        (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
          pe'.distHyperKernel E l ω s ν) * C ν)
      = ∑' ν : PMF State, ∑' ω : PMF (PMF State),
          pe'.scheduler.next E (some (l, ω)) * (pe'.distHyperKernel E l ω s ν * C ν) from
    tsum_congr (fun ν => by rw [← ENNReal.tsum_mul_right]; exact tsum_congr (fun ω => by ring))]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun ω => ?_)
  rw [ENNReal.tsum_mul_left]

/-- **Trace-cone belief normaliser cancellation.** Multiplying the (possibly
unnormalised) `beliefTC`-expectation by the normaliser recovers the unnormalised
`beliefTCw`-weighted sum; covers the `Z = 0` fallback too. -/
theorem ProbabilisticExecution.beliefTC_normalize_cancel
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (labs : List Label) (s : State) (w : AlterSeq (PMF State) Label → ENNReal) :
    (∑' E, pe'.beliefTCw labs s E) * (∑' E, pe'.beliefTC labs s E * w E)
      = ∑' E, pe'.beliefTCw labs s E * w E := by
  classical
  by_cases hZ : (∑' E, pe'.beliefTCw labs s E) = 0
  · rw [hZ, zero_mul]
    have hz : ∀ E, pe'.beliefTCw labs s E = 0 := ENNReal.tsum_eq_zero.mp hZ
    exact (ENNReal.tsum_eq_zero.mpr (fun E => by rw [hz E, zero_mul])).symm
  · have hZtop : (∑' E, pe'.beliefTCw labs s E) ≠ ⊤ := pe'.beliefTCw_tsum_ne_top labs s
    have hbel : ∀ E, pe'.beliefTC labs s E
        = pe'.beliefTCw labs s E * (∑' E', pe'.beliefTCw labs s E')⁻¹ := by
      intro E
      unfold ProbabilisticExecution.beliefTC
      rw [dif_pos hZ, PMF.normalize_apply]
    rw [show (∑' E, pe'.beliefTC labs s E * w E)
          = ∑' E, (pe'.beliefTCw labs s E * (∑' E', pe'.beliefTCw labs s E')⁻¹) * w E from
        tsum_congr (fun E => by rw [hbel E]),
      ← ENNReal.tsum_mul_left]
    refine tsum_congr (fun E => ?_)
    rw [show (∑' E', pe'.beliefTCw labs s E') *
          (pe'.beliefTCw labs s E * (∑' E', pe'.beliefTCw labs s E')⁻¹ * w E)
          = ((∑' E', pe'.beliefTCw labs s E') * (∑' E', pe'.beliefTCw labs s E')⁻¹) *
            (pe'.beliefTCw labs s E * w E) by ring,
      ENNReal.mul_inv_cancel hZ hZtop, one_mul]

open Classical in
/-- **Trace-cone invariant (`g`-indexed).** The headline identity `ρ = Ω.bind id`:
the lowered witness's `g`-integrated level mass equals `pe'`'s level mass
integrated against the `bind id` push-forward `μ ↦ ∑' s, μ s · g s`. Proven by
induction on `labs`: the base is `labMass_nil` + `initState.bind id`; the step
chains `labMass_append`, `lower_kernel_g_sum`, the IH, `beliefTC_normalize_cancel`
and `hyperStep_marginal_decomp` (the dhk→ω collapse). -/
theorem ProbabilisticExecution.lower_labProb_eq_aux
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem) (labs : List Label)
    (g : State → ENNReal) :
    pe'.lower.labMass labs g
      = pe'.labMass labs (fun μ : PMF State => ∑' s : State, μ s * g s) := by
  classical
  revert g
  induction labs using List.reverseRecOn with
  | nil =>
      intro g
      rw [pe'.lower.labMass_nil g, pe'.labMass_nil (fun μ : PMF State => ∑' s, μ s * g s)]
      have hinit : pe'.lower.initState = pe'.initState.bind id := rfl
      rw [hinit]
      simp_rw [PMF.bind_apply, id_eq]
      simp_rw [← ENNReal.tsum_mul_right]
      rw [ENNReal.tsum_comm]
      refine tsum_congr (fun a => ?_)
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr (fun s₀ => by ring)
  | append_singleton labs l ih =>
      intro g
      have hL : pe'.lower.labMass (labs ++ [l]) g
          = pe'.lower.labMass labs (fun s => ∑' E : AlterSeq (PMF State) Label,
              pe'.beliefTC labs s E * (∑' ω : PMF (PMF State),
                pe'.scheduler.next E (some (l, ω)) *
                  (∑' q : State, ((pe'.distHyperKernel E l ω s).bind id) q * g q))) := by
        rw [pe'.lower.labMass_step labs l g]
        unfold ProbabilisticExecution.labMass
        refine tsum_congr (fun e' => ?_)
        by_cases hc : e'.trans.Terminates ∧ e'.trans.map Prod.fst = Seq.ofList labs
        · rw [dif_pos hc, dif_pos hc]; congr 1
          have map_ofList : ∀ (L : List (Label × State)),
              (Seq.ofList L).map Prod.fst = Seq.ofList (L.map Prod.fst) := by
            intro L; induction L with
            | nil => simp [Stream'.Seq.ofList_nil, Stream'.Seq.map_nil]
            | cons a L ihL => rw [Stream'.Seq.ofList_cons, Stream'.Seq.map_cons, ihL,
                List.map_cons, Stream'.Seq.ofList_cons]
          have h_labs : (e'.trans.toList hc.1).map Prod.fst = labs := by
            apply Stream'.Seq.ofList_injective
            rw [← map_ofList, Stream'.Seq.ofList_toList e'.trans hc.1]; exact hc.2
          rw [pe'.lower_kernel_g_sum labs l g e' hc.1 h_labs (e'.endState hc.1) rfl]
        · rw [dif_neg hc, dif_neg hc]
      rw [hL, ih (fun s => ∑' E : AlterSeq (PMF State) Label,
            pe'.beliefTC labs s E * (∑' ω : PMF (PMF State),
              pe'.scheduler.next E (some (l, ω)) *
                (∑' q : State, ((pe'.distHyperKernel E l ω s).bind id) q * g q)))]
      have hR : pe'.labMass (labs ++ [l]) (fun μ : PMF State => ∑' s, μ s * g s)
          = ∑' E : AlterSeq (PMF State) Label,
              dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
                (fun h => pe'.probOf E h.1 * (∑' ω : PMF (PMF State),
                  pe'.scheduler.next E (some (l, ω)) *
                    (∑' s : State, ((ω.bind id) s) * g s))) (fun _ => 0) := by
        rw [pe'.labMass_step labs l (fun μ : PMF State => ∑' s, μ s * g s)]
        refine tsum_congr (fun E => ?_)
        by_cases hc : E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs
        · rw [dif_pos hc, dif_pos hc]; congr 1
          simp only [ProbabilisticExecution.kernel]
          simp_rw [← ENNReal.tsum_mul_right]
          rw [ENNReal.tsum_comm]
          refine tsum_congr (fun μ => ?_)
          rw [← ENNReal.tsum_mul_left]
          simp_rw [mul_assoc]
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
          congr 1
          simp_rw [PMF.bind_apply, id_eq]
          simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
          rw [ENNReal.tsum_comm]
          refine tsum_congr (fun a => ?_)
          refine tsum_congr (fun s => ?_)
          ring
        · rw [dif_neg hc, dif_neg hc]
      have hLmid : (pe'.labMass labs (fun μ : PMF State => ∑' s : State,
            μ s * (∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
              (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                (∑' q : State, ((pe'.distHyperKernel E l ω s).bind id) q * g q)))))
          = ∑' E : AlterSeq (PMF State) Label,
              dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
                (fun h => pe'.probOf E h.1 * (∑' ω : PMF (PMF State),
                  pe'.scheduler.next E (some (l, ω)) *
                    (∑' s : State, ((ω.bind id) s) * g s))) (fun _ => 0) := by
        -- Abbreviate the per-state inner factor `H s`.
        set Hfun : State → ENNReal := fun s =>
            ∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs s E *
              (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                (∑' q : State, ((pe'.distHyperKernel E l ω s).bind id) q * g q)) with hHfun
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
        -- Apply the normalizer cancellation per state `b`.
        have stepB : ∀ b : State,
            (∑' i : AlterSeq (PMF State) Label, pe'.beliefTCw labs b i) *
              (∑' E : AlterSeq (PMF State) Label, pe'.beliefTC labs b E *
                (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                  (∑' q : State, ((pe'.distHyperKernel E l ω b).bind id) q * g q)))
            = ∑' E : AlterSeq (PMF State) Label, pe'.beliefTCw labs b E *
                (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                  (∑' q : State, ((pe'.distHyperKernel E l ω b).bind id) q * g q)) := by
          intro b
          exact pe'.beliefTC_normalize_cancel labs b
            (fun E => ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
              (∑' q : State, ((pe'.distHyperKernel E l ω b).bind id) q * g q))
        simp_rw [stepB]
        rw [ENNReal.tsum_comm]
        -- The marginal collapse: per terminating `E`, integrating the per-state
        -- hyper-kernel against the end-state distribution recovers `ω.bind id`.
        have decomp_g : ∀ (E : AlterSeq (PMF State) Label) (hE : E.trans.Terminates),
            (∑' s : State, (E.endState hE) s *
              (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                (∑' q : State, ((pe'.distHyperKernel E l ω s).bind id) q * g q)))
            = ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                (∑' s : State, ((ω.bind id) s) * g s) := by
          intro E hE
          -- Push `(E.endState hE) s` into the ω-sum, swap `s ↔ ω`, pull `next` out.
          have hpush : ∀ s : State, (E.endState hE) s *
              (∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                (∑' q : State, ((pe'.distHyperKernel E l ω s).bind id) q * g q))
              = ∑' ω : PMF (PMF State), pe'.scheduler.next E (some (l, ω)) *
                  ((E.endState hE) s * (∑' q : State,
                    ((pe'.distHyperKernel E l ω s).bind id) q * g q)) := by
            intro s
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr (fun ω => ?_)
            ring
          rw [tsum_congr hpush, ENNReal.tsum_comm]
          refine tsum_congr (fun ω => ?_)
          rw [ENNReal.tsum_mul_left]
          by_cases hω : pe'.scheduler.next E (some (l, ω)) = 0
          · simp [hω]
          · congr 1
            have h_supp : some (l, ω) ∈ (pe'.scheduler.next E).support :=
              (PMF.mem_support_iff _ _).mpr hω
            symm
            simp_rw [hyperStep_marginal_decomp pe' hE h_supp]
            simp_rw [← ENNReal.tsum_mul_right]
            rw [ENNReal.tsum_comm]
            refine tsum_congr (fun s => ?_)
            rw [← ENNReal.tsum_mul_left]
            exact tsum_congr (fun s' => by ring)
        refine tsum_congr (fun E => ?_)
        by_cases hc : E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs
        · rw [dif_pos hc]
          have hbw : ∀ s : State,
              pe'.beliefTCw labs s E = pe'.probOf E hc.1 * (E.endState hc.1) s := by
            intro s; unfold ProbabilisticExecution.beliefTCw; rw [dif_pos hc]
          simp_rw [hbw]
          rw [← decomp_g E hc.1]
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr (fun s => ?_)
          ring
        · have hz : ∀ s : State, pe'.beliefTCw labs s E = 0 := by
            intro s; unfold ProbabilisticExecution.beliefTCw; rw [dif_neg hc]
          rw [dif_neg hc]
          simp only [hz, zero_mul, tsum_zero]
      rw [hLmid, hR]

open Classical in
/-- **Trace-cone invariant (`g = 1` slice).** For each label list `labs`, the
`lower`-witness assigns the same total `probOf`-mass to `sys`-executions with
label list `labs` as `pe'` assigns to `𝒟(sys)`-histories with label list `labs`.
The `g = 1` instance of `lower_labProb_eq_aux`. -/
theorem ProbabilisticExecution.lower_labProb_eq
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem) (labs : List Label) :
    (∑' e : AlterSeq State Label,
        dite (e.trans.Terminates ∧ e.trans.map Prod.fst = Seq.ofList labs)
          (fun h => pe'.lower.probOf e h.1) (fun _ => 0))
    = ∑' E : AlterSeq (PMF State) Label,
        dite (E.trans.Terminates ∧ E.trans.map Prod.fst = Seq.ofList labs)
          (fun h => pe'.probOf E h.1) (fun _ => 0) := by
  classical
  have h := pe'.lower_labProb_eq_aux labs (fun _ => 1)
  simpa only [ProbabilisticExecution.labMass, mul_one, PMF.tsum_coe] using h

/-- **Trace preservation for the witness.** For each trace `τ`,
`sys.traceProb pe'.lower τ = 𝒟(sys).traceProb pe' τ`. Regroup both `traceProb`s by
label list (`traceProb_eq_labProb_sum`); since `sys` and `𝒟(sys)` share `internal`,
the label-list condition coincides, and per label list the two masses agree by the
trace-cone invariant `lower_labProb_eq`. -/
theorem ProbabilisticExecution.lower_traceProb_eq
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem) (τ : Seq Label) :
    sys.traceProb pe'.lower τ = 𝒟(sys).traceProb pe' τ := by
  classical
  rw [LabelledSystem.traceProb_eq_labProb_sum sys pe'.lower τ,
      LabelledSystem.traceProb_eq_labProb_sum 𝒟(sys) pe' τ]
  refine tsum_congr fun labs => ?_
  by_cases h : sys.traceTightLabs τ labs
  · have h' : (𝒟(sys)).traceTightLabs τ labs := h
    rw [if_pos h, if_pos h', pe'.lower_labProb_eq labs]
  · have h' : ¬ (𝒟(sys)).traceTightLabs τ labs := h
    rw [if_neg h, if_neg h']

/-- **Superset direction.** Every achievable trace distribution of `𝒟(sys)` is
achievable by `sys`, witnessed by `pe'.lower` (the trace-cone construction). -/
theorem dist_traceProb_superset (sys : LabelledSystem State Label) :
    achievableTraceDists 𝒟(sys) ⊆ achievableTraceDists sys := by
  rintro D ⟨pe', h_init, h_pe'⟩
  refine ⟨pe'.lower, ?_, fun τ => ?_⟩
  · have hD : (𝒟(sys)).toSystem.init = PMF.pure sys.toSystem.init := rfl
    change pe'.lower.initState = PMF.pure sys.toSystem.init
    rw [show pe'.lower.initState = pe'.initState.bind id from rfl, h_init, hD,
      PMF.pure_bind, id_eq]
  · rw [pe'.lower_traceProb_eq τ, h_pe' τ]

/-- **Distribution-monad construction preserves trace distributions.** -/
theorem dist_traceProb_eq (sys : LabelledSystem State Label) :
    achievableTraceDists sys = achievableTraceDists 𝒟(sys) :=
  Set.Subset.antisymm
    (dist_traceProb_subset sys)
    (dist_traceProb_superset sys)

end PLTS
