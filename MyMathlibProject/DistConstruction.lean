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
  intro D ⟨pe, h_pe⟩
  refine ⟨pe.dist, fun τ => ?_⟩
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

The superset direction needs to convert a `𝒟(sys)`-probabilistic execution
`pe'` into a `sys`-probabilistic execution of the same trace distribution.

**Construction (coupling).** Jointly sample a `𝒟(sys)`-trajectory
`E := μ_0 -[l_1]→ μ_1 → …` from `pe'` and a `sys`-trajectory
`e := s_0 -[l_1]→ s_1 → …` with the same labels and `s_i ∈ μ_i.support` at
every step:

* `μ_0 ∼ pe'.initState`, `s_0 ∼ μ_0`;
* at step `i`: `(l, ω) ∼ pe'.scheduler.next E_i`; the `hyperStep` witness
  for `hyperStep sys μ_i l (ω.bind id)` exposes a per-state kernel
  `p_ω : State → PMF (PMF State)`; sample `μ' ∼ p_ω(s_i)`, `s_{i+1} ∼ μ'`,
  and independently `μ_{i+1} ∼ ω` on the `𝒟(sys)`-side.

Under the no-stutter `hyperStep`, every `μ' ∈ p_ω(s_i).support` satisfies
`sys.step s_i l μ'` directly (no internal-stutter case-split), so the
constructed `sys`-scheduler is valid by appeal to `hyperStep.kernel_step`.

**Trace preservation.** Labels are produced only by `pe'.scheduler`, hence
the marginal distribution of the label-sequence under the joint coupling
coincides with `pe'`'s. The hyperStep kernel only randomises post-states,
not labels. Trace probabilities therefore transfer.

**The `sys`-scheduler is the disintegration** of the joint distribution
along its `sys`-marginal: at history `e`, the next emission is sampled
from the conditional law of `(l, μ')` given `e`. We encode this via a
*belief state* `belief pe' e` — the posterior over `𝒟(sys)`-histories
compatible with `e`. -/

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

/-- Fallback PMF used when the belief posterior has zero marginal mass at the
observed `sys`-history. We pick the **Dirac lift** `PMF.pure e.dirac`. This
trivially satisfies `belief_support_compat` because `e.dirac` has the same
label sequence as `e` and Dirac-lifts each state. Downstream consumers
(`belief_bayes_inversion`) multiply this branch by zero — the degenerate
case corresponds to `e` with zero `ofDist`-probability. -/
noncomputable def beliefDefault (e : AlterSeq State Label) :
    PMF (AlterSeq (PMF State) Label) :=
  PMF.pure e.dirac

/-- **Base belief**: posterior distribution over `𝒟(sys)`-histories with empty
transition list (so `E = ⟨μ_0, Seq.nil⟩`) given that the observed initial
`sys`-state is `s₀`. The Bayesian weight is `pe'.initState μ_0 * μ_0 s₀`,
normalised. If the total mass is zero the fallback `beliefDefault` is used. -/
noncomputable def ProbabilisticExecution.beliefBase
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem) (s₀ : State) :
    PMF (AlterSeq (PMF State) Label) :=
  open Classical in
  if h0 : (∑' init : PMF State, pe'.initState init * init s₀) ≠ 0 then
    have h_top : (∑' init : PMF State, pe'.initState init * init s₀) ≠ ⊤ := by
      apply ne_of_lt
      calc (∑' init : PMF State, pe'.initState init * init s₀)
          ≤ ∑' init : PMF State, pe'.initState init := by
            apply ENNReal.tsum_le_tsum
            intro init
            exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
        _ = 1 := pe'.initState.tsum_coe
        _ < ⊤ := ENNReal.one_lt_top
    (PMF.normalize (fun init => pe'.initState init * init s₀) h0 h_top).map
      (fun init => ⟨init, Seq.nil⟩)
  else
    beliefDefault ⟨s₀, Seq.nil⟩

/-- **Step conditional**: given a `𝒟(sys)`-history `E_pre` and an observed
`sys`-step `(l, s')`, sample `(ω, μ_new) : PMF (PMF State) × PMF State` from
the conditional law
`pe'.scheduler.next E_pre (some (l, ω)) * ω μ_new * μ_new s'`,
normalised. The returned PMF places its mass on `E_post = ⟨E_pre.init,
E_pre.trans ++ [(l, μ_new)]⟩`.

This is the per-step Bayesian update for the joint sampling
`(l, ω) ∼ pe'.scheduler.next E_pre; μ_new ∼ ω; s' ∼ μ_new` — i.e. the
sys-side next state is sampled *from the just-drawn 𝒟-side post-PMF-state*.
The factor `μ_new s'` forces `s' ∈ μ_new.support`, which is exactly the
compatibility property `belief_support_compat` needs.

On zero-mass conditional events the fallback is the Dirac extension
`⟨E_pre.init, E_pre.trans ++ [(l, PMF.pure s')]⟩`. -/
noncomputable def ProbabilisticExecution.beliefStepCond
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (E_pre : AlterSeq (PMF State) Label) (l : Label) (s' : State) :
    PMF (AlterSeq (PMF State) Label) :=
  open Classical in
  let w : PMF (PMF State) × PMF State → ENNReal := fun p =>
    pe'.scheduler.next E_pre (some (l, p.1)) * p.1 p.2 * p.2 s'
  if h0 : (∑' p : PMF (PMF State) × PMF State, w p) ≠ 0 then
    have h_top : (∑' p, w p) ≠ ⊤ := by
      apply ne_of_lt
      have h_bound : (∑' p : PMF (PMF State) × PMF State, w p) ≤ 1 := by
        rw [ENNReal.tsum_prod']
        have h_inner : ∀ ω : PMF (PMF State),
            (∑' μ_new : PMF State, w (ω, μ_new))
            ≤ pe'.scheduler.next E_pre (some (l, ω)) := by
          intro ω
          calc (∑' μ_new : PMF State,
              pe'.scheduler.next E_pre (some (l, ω)) * ω μ_new * μ_new s')
              ≤ ∑' μ_new : PMF State,
                    pe'.scheduler.next E_pre (some (l, ω)) * ω μ_new := by
                apply ENNReal.tsum_le_tsum
                intro μ_new
                exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
            _ = pe'.scheduler.next E_pre (some (l, ω)) * ∑' μ_new, ω μ_new := by
                rw [ENNReal.tsum_mul_left]
            _ = pe'.scheduler.next E_pre (some (l, ω)) * 1 := by rw [ω.tsum_coe]
            _ = pe'.scheduler.next E_pre (some (l, ω)) := by ring
        calc (∑' ω : PMF (PMF State), ∑' μ_new : PMF State, w (ω, μ_new))
            ≤ ∑' ω : PMF (PMF State), pe'.scheduler.next E_pre (some (l, ω)) :=
              ENNReal.tsum_le_tsum h_inner
          _ ≤ ∑' (lω : Label × PMF (PMF State)),
                pe'.scheduler.next E_pre (some lω) := by
              exact ENNReal.tsum_comp_le_tsum_of_injective
                (f := fun ω => (l, ω))
                (fun _ _ h => (Prod.mk.inj h).2) _
          _ ≤ ∑' opt, pe'.scheduler.next E_pre opt := by
              exact ENNReal.tsum_comp_le_tsum_of_injective
                (f := some) (fun _ _ h => Option.some.inj h) _
          _ = 1 := (pe'.scheduler.next E_pre).tsum_coe
      exact lt_of_le_of_lt h_bound ENNReal.one_lt_top
    (PMF.normalize w h0 h_top).map (fun p =>
      ⟨E_pre.init, E_pre.trans.append (Seq.cons (l, p.2) Seq.nil)⟩)
  else
    PMF.pure ⟨E_pre.init, E_pre.trans.append (Seq.cons (l, PMF.pure s') Seq.nil)⟩

/-- **Recursive belief over a path**: build the posterior over `𝒟(sys)`-histories
along the `sys`-execution `⟨s₀, Seq.ofList rest⟩` by sequential Bayesian
filtering. The base case (`rest = []`) is `beliefBase pe' s₀`. The inductive
step at `(l, s')` performs the full smoothing update in two stages:

1. **Reweight** the prior `ih` by the per-`E_pre` marginal likelihood
   `zEpre(E_pre) := ∑' ω, scheduler.next E_pre (some (l, ω)) * (ω.bind id)(s')`
   — the marginal probability of observing sys-state `s'` at the next step
   given 𝒟-history `E_pre` and label `l`. Renormalise (or fall back to
   `beliefDefault` if the total is zero).

2. **Bind** the reweighted prior with `beliefStepCond`. The per-`E_pre`
   normalisation inside `beliefStepCond` exactly cancels the `zEpre`
   reweighting, yielding the global Bayesian posterior of the joint
   `(l, ω) ∼ pe'.scheduler; μ_new ∼ ω; s' ∼ μ_new`.

Without the reweighting, the bind would give the forward generative
distribution rather than the smoothing posterior — incorrect when different
`E_pre`'s have different marginal likelihoods. -/
noncomputable def ProbabilisticExecution.beliefRec
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem) (s₀ : State) :
    List (Label × State) → PMF (AlterSeq (PMF State) Label) :=
  fun rest =>
    rest.reverseRecOn
      (motive := fun _ => PMF (AlterSeq (PMF State) Label))
      (pe'.beliefBase s₀)
      (fun rest_prev last ih =>
        let l := last.1
        let s' := last.2
        -- Per-`E_pre` marginal likelihood of observing `(l, s')`.
        let zEpre : AlterSeq (PMF State) Label → ENNReal := fun E_pre =>
          ∑' ω : PMF (PMF State),
            pe'.scheduler.next E_pre (some (l, ω)) *
            ∑' μ_new : PMF State, ω μ_new * μ_new s'
        let reweighted : AlterSeq (PMF State) Label → ENNReal := fun E_pre =>
          ih E_pre * zEpre E_pre
        have h_zEpre_le_one : ∀ E_pre, zEpre E_pre ≤ 1 := fun E_pre => by
          change (∑' ω : PMF (PMF State),
              pe'.scheduler.next E_pre (some (l, ω)) *
              ∑' μ_new : PMF State, ω μ_new * μ_new s') ≤ 1
          calc (∑' ω : PMF (PMF State),
                pe'.scheduler.next E_pre (some (l, ω)) *
                ∑' μ_new : PMF State, ω μ_new * μ_new s')
              ≤ ∑' ω : PMF (PMF State),
                  pe'.scheduler.next E_pre (some (l, ω)) := by
                apply ENNReal.tsum_le_tsum
                intro ω
                refine mul_le_of_le_one_right' ?_
                calc (∑' μ_new : PMF State, ω μ_new * μ_new s')
                    ≤ ∑' μ_new : PMF State, ω μ_new := by
                      apply ENNReal.tsum_le_tsum
                      intro μ_new
                      exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
                  _ = 1 := ω.tsum_coe
            _ ≤ ∑' lω : Label × PMF (PMF State),
                  pe'.scheduler.next E_pre (some lω) := by
                exact ENNReal.tsum_comp_le_tsum_of_injective
                  (f := fun ω => (l, ω))
                  (fun _ _ h => (Prod.mk.inj h).2) _
            _ ≤ ∑' opt, pe'.scheduler.next E_pre opt := by
                exact ENNReal.tsum_comp_le_tsum_of_injective
                  (f := some) (fun _ _ h => Option.some.inj h) _
            _ = 1 := (pe'.scheduler.next E_pre).tsum_coe
        open Classical in
        if h0 : (∑' E_pre, reweighted E_pre) ≠ 0 then
          have h_top : (∑' E_pre, reweighted E_pre) ≠ ⊤ := by
            apply ne_of_lt
            calc (∑' E_pre, reweighted E_pre)
                ≤ ∑' E_pre, ih E_pre := by
                  apply ENNReal.tsum_le_tsum
                  intro E_pre
                  exact mul_le_of_le_one_right' (h_zEpre_le_one E_pre)
              _ = 1 := ih.tsum_coe
              _ < ⊤ := ENNReal.one_lt_top
          (PMF.normalize reweighted h0 h_top).bind (fun E_pre =>
            pe'.beliefStepCond E_pre l s')
        else
          beliefDefault ⟨s₀, Seq.ofList (rest_prev ++ [last])⟩)

/-- **Belief state**: posterior distribution over `𝒟(sys)`-histories
compatible with the observed `sys`-history `e`, i.e. the conditional law of
the `𝒟(sys)`-prefix given the `sys`-prefix in the joint sampling

  `μ_0 ∼ pe'.initState; s_0 ∼ μ_0;
   (l_{i+1}, ω) ∼ pe'.scheduler.next E_i; μ_{i+1} ∼ ω; s_{i+1} ∼ μ_{i+1}.`

The crucial choice is **`s_{i+1} ∼ μ_{i+1}` directly** — i.e., the sys-side
state at each step is sampled from the just-drawn 𝒟-side post-PMF-state.
This enforces `s_i ∈ μ_i.support` inductively, giving `belief_support_compat`
and the `e.endState ∈ E.endState.support` hypothesis that `Scheduler.ofDist`
needs to apply `distHyperKernel_step`.

Defined by sequential Bayesian conditioning along the (reverse-list)
decomposition of `e.trans`: the base case is the posterior `μ_0 ∼ pe'.initState`
conditioned on `μ_0 e.init > 0`; each subsequent step `(l, s')` reweights
by the marginal likelihood `∑ω scheduler.next E_pre (some (l, ω)) * (ω.bind id)(s')`
and samples the next PMF-state from the per-step conditional. On a
`sys`-history with zero marginal mass the posterior is undefined and we
fall back to `beliefDefault`. -/
noncomputable def ProbabilisticExecution.belief
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem) :
    AlterSeq State Label → PMF (AlterSeq (PMF State) Label) :=
  fun e =>
    open Classical in
    if hT : e.trans.Terminates then
      pe'.beliefRec e.init (e.trans.toList hT)
    else
      beliefDefault e

/-- **Recursive support compatibility.** The list-indexed version of
`belief_support_compat`: every `𝒟(sys)`-history in the support of
`beliefRec pe' s₀ rest` shares the label sequence of `Seq.ofList rest`,
contains `s₀` in its initial support, and is state-compatible at every
position. The endState conjunct says the canonical "last state" of `rest`
(equivalently, `endState ⟨s₀, Seq.ofList rest⟩`) lies in the support of
the belief's endState. -/
private theorem ProbabilisticExecution.beliefRec_support_compat
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (s₀ : State) (rest : List (Label × State))
    {E : AlterSeq (PMF State) Label}
    (hE : E ∈ (pe'.beliefRec s₀ rest).support) :
    ∃ hE_term : E.trans.Terminates,
      s₀ ∈ E.init.support ∧
      E.trans.map (fun lμ : Label × PMF State => lμ.1)
        = (Seq.ofList rest).map (fun ls : Label × State => ls.1) ∧
      (⟨s₀, Seq.ofList rest⟩ : AlterSeq State Label).endState
          (Stream'.Seq.terminates_ofList rest) ∈ (E.endState hE_term).support ∧
      (∀ n l μ s, E.trans.get? n = some (l, μ) →
          (Seq.ofList rest).get? n = some (l, s) → s ∈ μ.support) := by
  classical
  -- Generalize over `E, hE` so the IH covers every `E`.
  revert E
  induction rest using List.reverseRecOn with
  | nil =>
    intro E hE
    -- `beliefRec _ s₀ [] = beliefBase pe' s₀`.
    have h_unfold : pe'.beliefRec s₀ [] = pe'.beliefBase s₀ := by
      unfold ProbabilisticExecution.beliefRec
      rw [List.reverseRecOn_nil]
    rw [h_unfold] at hE
    unfold ProbabilisticExecution.beliefBase at hE
    split_ifs at hE with h0
    · -- Non-degenerate base case.
      rw [PMF.mem_support_map_iff] at hE
      obtain ⟨μ₀, hμ₀_supp, hE_eq⟩ := hE
      rw [PMF.mem_support_normalize_iff] at hμ₀_supp
      -- `hμ₀_supp : pe'.initState μ₀ * μ₀ s₀ ≠ 0`.
      have h_μ₀_s₀ : μ₀ s₀ ≠ 0 := fun h => hμ₀_supp (by rw [h, mul_zero])
      subst hE_eq
      refine ⟨Stream'.Seq.terminates_nil, ?_, ?_, ?_, ?_⟩
      · exact (PMF.mem_support_iff _ _).mpr h_μ₀_s₀
      · simp [Stream'.Seq.map_nil]
      · -- endState ⟨s₀, nil⟩ = s₀, endState ⟨μ₀, nil⟩ = μ₀.
        rw [AlterSeq.endState_of_trans_nil _ rfl,
            AlterSeq.endState_of_trans_nil _ rfl]
        exact (PMF.mem_support_iff _ _).mpr h_μ₀_s₀
      · intro n l μ s hn_E _
        -- `E.trans = nil`, so `E.trans.get? n = none`. Contradiction.
        simp at hn_E
    · -- Degenerate base case: E = ⟨s₀, nil⟩.dirac = ⟨PMF.pure s₀, nil⟩.
      change E ∈ (beliefDefault (⟨s₀, Seq.nil⟩ : AlterSeq State Label)).support at hE
      unfold beliefDefault at hE
      rw [PMF.mem_support_pure_iff] at hE
      subst hE
      refine ⟨Stream'.Seq.terminates_nil, ?_, ?_, ?_, ?_⟩
      · change s₀ ∈ (PMF.pure s₀).support
        rw [PMF.mem_support_pure_iff]
      · change (Stream'.Seq.map _ Seq.nil) = _
        simp [Stream'.Seq.map_nil]
      · rw [AlterSeq.endState_of_trans_nil _ rfl,
            AlterSeq.endState_of_trans_nil _ rfl]
        change s₀ ∈ (PMF.pure s₀).support
        rw [PMF.mem_support_pure_iff]
      · intro n l μ s hn_E _
        change (Stream'.Seq.map _ Seq.nil).get? n = some _ at hn_E
        simp at hn_E
  | append_singleton rest_prev last ih =>
    intro E hE
    -- Unfold `beliefRec` at the concatenation.
    have h_unfold : pe'.beliefRec s₀ (rest_prev ++ [last]) =
        (let l := last.1
         let s' := last.2
         let ih_pmf := pe'.beliefRec s₀ rest_prev
         let zEpre : AlterSeq (PMF State) Label → ENNReal := fun E_pre =>
           ∑' ω : PMF (PMF State),
             pe'.scheduler.next E_pre (some (l, ω)) *
             ∑' μ_new : PMF State, ω μ_new * μ_new s'
         let reweighted : AlterSeq (PMF State) Label → ENNReal := fun E_pre =>
           ih_pmf E_pre * zEpre E_pre
         open Classical in
         if h0 : (∑' E_pre, reweighted E_pre) ≠ 0 then
           have h_top : (∑' E_pre, reweighted E_pre) ≠ ⊤ := by
             apply ne_of_lt
             calc (∑' E_pre, reweighted E_pre)
                 ≤ ∑' E_pre, ih_pmf E_pre := by
                   apply ENNReal.tsum_le_tsum
                   intro E_pre
                   refine mul_le_of_le_one_right' ?_
                   change (∑' ω : PMF (PMF State),
                       pe'.scheduler.next E_pre (some (l, ω)) *
                       ∑' μ_new : PMF State, ω μ_new * μ_new s') ≤ 1
                   calc (∑' ω : PMF (PMF State),
                         pe'.scheduler.next E_pre (some (l, ω)) *
                         ∑' μ_new : PMF State, ω μ_new * μ_new s')
                       ≤ ∑' ω : PMF (PMF State),
                           pe'.scheduler.next E_pre (some (l, ω)) := by
                         apply ENNReal.tsum_le_tsum
                         intro ω
                         refine mul_le_of_le_one_right' ?_
                         calc (∑' μ_new : PMF State, ω μ_new * μ_new s')
                             ≤ ∑' μ_new : PMF State, ω μ_new := by
                               apply ENNReal.tsum_le_tsum
                               intro μ_new
                               exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
                           _ = 1 := ω.tsum_coe
                     _ ≤ ∑' lω : Label × PMF (PMF State),
                           pe'.scheduler.next E_pre (some lω) := by
                         exact ENNReal.tsum_comp_le_tsum_of_injective
                           (f := fun ω => (l, ω))
                           (fun _ _ h => (Prod.mk.inj h).2) _
                     _ ≤ ∑' opt, pe'.scheduler.next E_pre opt := by
                         exact ENNReal.tsum_comp_le_tsum_of_injective
                           (f := some) (fun _ _ h => Option.some.inj h) _
                     _ = 1 := (pe'.scheduler.next E_pre).tsum_coe
               _ = 1 := ih_pmf.tsum_coe
               _ < ⊤ := ENNReal.one_lt_top
           (PMF.normalize reweighted h0 h_top).bind (fun E_pre =>
             pe'.beliefStepCond E_pre l s')
         else
           beliefDefault ⟨s₀, Seq.ofList (rest_prev ++ [last])⟩) := by
      unfold ProbabilisticExecution.beliefRec
      rw [List.reverseRecOn_concat]
    rw [h_unfold] at hE
    -- Now `hE` is in the unfolded form. Set up names.
    set l := last.1 with hl_def
    set s' := last.2 with hs'_def
    have h_prev_term : (Stream'.Seq.ofList rest_prev).Terminates :=
      Stream'.Seq.terminates_ofList _
    simp only at hE
    -- Split on the if-condition.
    split_ifs at hE with h0
    · -- Non-degenerate: `belief = (normalize reweighted ..).bind beliefStepCond _ l s'`.
      rw [PMF.mem_support_bind_iff] at hE
      obtain ⟨E_pre, hE_pre_supp, hE_step⟩ := hE
      rw [PMF.mem_support_normalize_iff] at hE_pre_supp
      -- `hE_pre_supp : ih_pmf E_pre * zEpre E_pre ≠ 0`.
      have h_ih_ne : pe'.beliefRec s₀ rest_prev E_pre ≠ 0 := by
        intro h
        apply hE_pre_supp
        rw [h, zero_mul]
      -- Apply IH (on E_pre, *not* on E).
      obtain ⟨hEpre_term, h_init_pre, h_lab_pre, h_end_pre, h_compat_pre⟩ :=
        ih (E := E_pre) ((PMF.mem_support_iff _ _).mpr h_ih_ne)
      -- Now decompose hE_step using beliefStepCond.
      unfold ProbabilisticExecution.beliefStepCond at hE_step
      simp only at hE_step
      split_ifs at hE_step with h_step
      · -- Non-degenerate step: E comes from (normalize w).map.
        rw [PMF.mem_support_map_iff] at hE_step
        obtain ⟨⟨ω, μ_new⟩, h_w_supp, hE_eq⟩ := hE_step
        rw [PMF.mem_support_normalize_iff] at h_w_supp
        -- `h_w_supp : pe'.scheduler.next E_pre (some (l, ω)) * ω μ_new * μ_new s' ≠ 0`
        have h_μ_new_s' : μ_new s' ≠ 0 := fun h => h_w_supp (by
          change pe'.scheduler.next E_pre (some (l, ω)) * ω μ_new * μ_new s' = 0
          rw [h, mul_zero])
        -- Note: we don't subst — instead we use hE_eq directly via rw.
        -- E = ⟨E_pre.init, E_pre.trans.append (cons (l, μ_new) nil)⟩.
        have hE_term : E.trans.Terminates := by
          rw [← hE_eq]
          exact ⟨Nat.find hEpre_term + 1, Stream'.Seq.terminatedAt_append_find hEpre_term
            (show (Seq.cons (l, μ_new) Seq.nil).TerminatedAt 1 from rfl)⟩
        refine ⟨hE_term, ?_, ?_, ?_, ?_⟩
        · -- init compat: s₀ ∈ E_pre.init.support (from IH); E.init = E_pre.init via hE_eq.
          rw [← hE_eq]
          exact h_init_pre
        · -- Labels: append a single (l, _) on both sides.
          rw [← hE_eq]
          change Stream'.Seq.map (fun lμ : Label × PMF State => lμ.1)
              (E_pre.trans.append (Seq.cons (l, μ_new) Seq.nil))
            = Stream'.Seq.map (fun ls : Label × State => ls.1)
                (Stream'.Seq.ofList (rest_prev ++ [last]))
          rw [Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil,
              Stream'.Seq.ofList_append, Stream'.Seq.map_append,
              show (Stream'.Seq.ofList [last] : Seq (Label × State))
                = Seq.cons last Seq.nil from by
                rw [Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil],
              Stream'.Seq.map_cons, Stream'.Seq.map_nil, h_lab_pre]
        · -- endState compat.
          -- Show that `E.endState hE_term = μ_new` after rewriting via hE_eq.
          have h_E_end :
              E.endState hE_term = μ_new := by
            -- Use congruence over hE_eq.
            have h_aux : ∀ (E' : AlterSeq (PMF State) Label) (h' : E'.trans.Terminates)
                (h_eq : E' = ⟨E_pre.init,
                    E_pre.trans.append (Seq.cons (l, μ_new) Seq.nil)⟩),
                E'.endState h' = μ_new := by
              intro E' h' h_eq
              subst h_eq
              exact AlterSeq.endState_append_singleton E_pre hEpre_term l μ_new
            exact h_aux E hE_term hE_eq.symm
          rw [h_E_end]
          -- LHS endState of ⟨s₀, ofList (rest_prev ++ [last])⟩ = last.2 = s'.
          have h_seq_eq : Stream'.Seq.ofList (rest_prev ++ [last])
              = (Stream'.Seq.ofList rest_prev).append (Seq.cons last Seq.nil) := by
            rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons,
                Stream'.Seq.ofList_nil]
          have h_prev_term : (Stream'.Seq.ofList rest_prev).Terminates :=
              Stream'.Seq.terminates_ofList _
          have h_LHS_eq : (⟨s₀, Stream'.Seq.ofList (rest_prev ++ [last])⟩
              : AlterSeq State Label).endState
              (Stream'.Seq.terminates_ofList _) = s' := by
            have h_aux : ∀ (e' : AlterSeq State Label) (h' : e'.trans.Terminates)
                (h_eq : e' = ⟨s₀, (Stream'.Seq.ofList rest_prev).append
                    (Seq.cons last Seq.nil)⟩),
                e'.endState h' = last.2 := by
              intro e' h' h_eq
              subst h_eq
              exact AlterSeq.endState_append_singleton
                (⟨s₀, Stream'.Seq.ofList rest_prev⟩ : AlterSeq State Label)
                h_prev_term last.1 last.2
            apply h_aux
            congr
          rw [h_LHS_eq]
          exact (PMF.mem_support_iff _ _).mpr h_μ_new_s'
        · -- get? compat at every position.
          intro n l₀ μ s₂ hn_E hn_e
          -- Rewrite hn_E via hE_eq.
          have hn_E' : (E_pre.trans.append (Seq.cons (l, μ_new) Seq.nil)).get? n
              = some (l₀, μ) := by
            rw [← hE_eq] at *
            exact hn_E
          -- And hn_e via the rest_prev ++ [last] split.
          have hn_e' : ((Stream'.Seq.ofList rest_prev).append
              (Seq.cons last Seq.nil)).get? n = some (l₀, s₂) := by
            rw [← show Stream'.Seq.ofList (rest_prev ++ [last])
                  = (Stream'.Seq.ofList rest_prev).append (Seq.cons last Seq.nil)
                from by rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons,
                            Stream'.Seq.ofList_nil]]
            exact hn_e
          -- Now case split on n: < length rest_prev (use IH) or = length (singleton).
          by_cases h_n_term : (Stream'.Seq.ofList rest_prev).TerminatedAt n
          · -- n is past rest_prev. The get?'s come from the appended singleton.
            have h_E_pre_term_n : E_pre.trans.TerminatedAt n := by
              rw [← Stream'.Seq.terminatedAt_map_iff (f := fun lμ : Label × PMF State => lμ.1),
                  h_lab_pre,
                  Stream'.Seq.terminatedAt_map_iff (f := fun ls : Label × State => ls.1)]
              exact h_n_term
            -- We need: n - (something) = 0, i.e., n equals the "start" of the
            -- appended chunk. Both `E_pre.trans` and `Seq.ofList rest_prev` get
            -- terminated *at the same index* (their `Nat.find`s match) because
            -- labels match. So at the smallest such index, we read the singleton.
            -- Cleanest path: compute the get? values of both sides at `n` by
            -- showing that the appended chunk's `get?` aligns at this `n`.
            -- We rely on the following: there exists `k`, the first position of
            -- termination of `ofList rest_prev`; for `n ≥ k`, both
            -- `(ofList rest_prev).append (cons last nil)).get? n` and
            -- `(E_pre.trans.append (cons (l, μ_new) nil)).get? n` are determined.
            -- Use the following observation: from `hn_e'`, n equals the "0th
            -- position of [last]" relative to rest_prev. Combined with
            -- `h_E_pre_term_n`, n is similarly placed for E_pre.
            -- Approach: show l₀ = l = last.1 and s₂ = last.2 = s' and μ = μ_new.
            -- (a) Show l₀ = l and s₂ = s'.
            have h_e_last : last = (l₀, s₂) := by
              -- Use `Stream'.Seq.get?_append_after_length` if available, else
              -- inline. Easier: just look at the position n vs rest_prev.length.
              -- We have `terminatedAt_ofList rest_prev rest_prev.length` and
              -- the `Seq.cons last Seq.nil` after.
              -- We know there is a smallest m with `(ofList rest_prev).TerminatedAt m`.
              -- Use h_n_term and find a witness.
              -- A more direct path: peel off the cons via destructuring.
              have h_eq2 : ((Stream'.Seq.ofList rest_prev).append
                  (Seq.cons last Seq.nil)).get? n =
                  (Seq.cons last Seq.nil).get?
                    (n - Nat.find ⟨n, h_n_term⟩) := by
                -- Use get?_append_find with k := n - Nat.find ⟨n, h_n_term⟩.
                -- The named lemma takes `h : s.Terminates`. Use h_prev_term.
                -- Actually, get?_append_find says:
                --   (s.append s').get? (Nat.find h + k) = s'.get? k.
                -- So at index `n`, with k = n - Nat.find ⟨n, h_n_term⟩.
                -- We need Nat.find h_prev_term ≤ n. We have h_n_term, so
                -- Nat.find h_prev_term ≤ n via Nat.find_min'.
                have h_find_le : Nat.find h_prev_term ≤ n := Nat.find_le h_n_term
                have h_k_eq : n = Nat.find h_prev_term + (n - Nat.find h_prev_term) := by
                  omega
                conv_lhs => rw [h_k_eq]
                exact Stream'.Seq.get?_append_find h_prev_term _ _
              rw [h_eq2] at hn_e'
              -- hn_e' : (Seq.cons last Seq.nil).get? _ = some (l₀, s₂).
              -- Either get? 0 = some last, or get? (k+1) = none.
              rcases hk : n - Nat.find ⟨n, h_n_term⟩ with - | m
              · rw [hk] at hn_e'
                simp only [Seq.get?_cons_zero, Option.some.injEq] at hn_e'
                exact hn_e'
              · rw [hk] at hn_e'
                rcases m with - | m'
                · simp [Stream'.Seq.get?_cons_succ, Stream'.Seq.get?_nil] at hn_e'
                · simp [Stream'.Seq.get?_cons_succ, Stream'.Seq.get?_nil] at hn_e'
            obtain ⟨hl₀_eq, hs₂_eq⟩ : last.1 = l₀ ∧ last.2 = s₂ := by
              constructor
              · rw [h_e_last]
              · rw [h_e_last]
            -- (b) Show E.trans.get? n = some (l, μ_new) hence μ = μ_new.
            have h_eq3 : (E_pre.trans.append (Seq.cons (l, μ_new) Seq.nil)).get? n
                = (Seq.cons (l, μ_new) Seq.nil).get?
                  (n - Nat.find hEpre_term) := by
              have h_find_le : Nat.find hEpre_term ≤ n := Nat.find_le h_E_pre_term_n
              have h_k_eq : n = Nat.find hEpre_term + (n - Nat.find hEpre_term) := by
                omega
              conv_lhs => rw [h_k_eq]
              exact Stream'.Seq.get?_append_find hEpre_term _ _
            rw [h_eq3] at hn_E'
            -- Conclude μ = μ_new and l₀ = l.
            -- We need to show: n - Nat.find hEpre_term = 0.
            -- Show n - Nat.find h_prev_term = 0 first (from `h_e_last` we got some).
            have h_E_pre_find_n :
                Nat.find hEpre_term = Nat.find h_prev_term := by
              -- Labels match, so terminatedAt positions match.
              apply le_antisymm
              · apply Nat.find_le
                rw [← Stream'.Seq.terminatedAt_map_iff (f := fun lμ : Label × PMF State => lμ.1),
                    h_lab_pre,
                    Stream'.Seq.terminatedAt_map_iff (f := fun ls : Label × State => ls.1)]
                exact Nat.find_spec h_prev_term
              · apply Nat.find_le
                rw [← Stream'.Seq.terminatedAt_map_iff (f := fun ls : Label × State => ls.1),
                    ← h_lab_pre,
                    Stream'.Seq.terminatedAt_map_iff (f := fun lμ : Label × PMF State => lμ.1)]
                exact Nat.find_spec hEpre_term
            -- Now from h_e_last we know (Seq.cons last nil).get? (n - find h_prev_term)
            -- = some (l₀, s₂). For this to be `some _`, the index must be 0.
            have h_idx_zero : n - Nat.find h_prev_term = 0 := by
              -- Use existing `h_e_last` proof which already established the
              -- subtraction equals 0 (via rcases). Re-derive directly:
              -- The (Seq.cons last Seq.nil).get? at (n - find h_prev_term)
              -- must be `some (l₀, s₂)` (we already have hn_e' after rewriting).
              have h_eq2 : ((Stream'.Seq.ofList rest_prev).append
                  (Seq.cons last Seq.nil)).get? n =
                  (Seq.cons last Seq.nil).get?
                    (n - Nat.find h_prev_term) := by
                have h_find_le : Nat.find h_prev_term ≤ n := Nat.find_le h_n_term
                have h_k_eq : n = Nat.find h_prev_term + (n - Nat.find h_prev_term) := by
                  omega
                conv_lhs => rw [h_k_eq]
                exact Stream'.Seq.get?_append_find h_prev_term _ _
              rw [h_eq2] at hn_e'
              rcases hk : n - Nat.find h_prev_term with - | m
              · rfl
              · exfalso
                rw [hk] at hn_e'
                rcases m with - | m'
                · simp [Stream'.Seq.get?_cons_succ, Stream'.Seq.get?_nil] at hn_e'
                · simp [Stream'.Seq.get?_cons_succ, Stream'.Seq.get?_nil] at hn_e'
            have h_idx_zero_E : n - Nat.find hEpre_term = 0 := by
              rw [h_E_pre_find_n]; exact h_idx_zero
            rw [h_idx_zero_E] at hn_E'
            simp only [Seq.get?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hn_E'
            obtain ⟨_, hμ_eq⟩ := hn_E'
            rw [← hμ_eq, ← hs₂_eq]
            exact (PMF.mem_support_iff _ _).mpr h_μ_new_s'
          · -- n < length rest_prev: both get?'s come from prev.
            have h_E_pre_not_term : ¬ E_pre.trans.TerminatedAt n := by
              intro h
              apply h_n_term
              rw [← Stream'.Seq.terminatedAt_map_iff (f := fun ls : Label × State => ls.1),
                  ← h_lab_pre,
                  Stream'.Seq.terminatedAt_map_iff (f := fun lμ : Label × PMF State => lμ.1)]
              exact h
            have h_E_get : (E_pre.trans.append (Seq.cons (l, μ_new) Seq.nil)).get? n
                = E_pre.trans.get? n :=
              Stream'.Seq.get?_append_before_length h_E_pre_not_term
            rw [h_E_get] at hn_E'
            have h_e_get : ((Stream'.Seq.ofList rest_prev).append
                (Seq.cons last Seq.nil)).get? n = (Stream'.Seq.ofList rest_prev).get? n :=
              Stream'.Seq.get?_append_before_length h_n_term
            rw [h_e_get] at hn_e'
            exact h_compat_pre n l₀ μ s₂ hn_E' hn_e'
      · -- Degenerate sub-step: should be unreachable.
        -- `h_step : ¬ tsum w ≠ 0`, so `tsum w = 0`.
        push Not at h_step
        -- Inside beliefStepCond `else` branch: E = pure (single-step extension).
        exfalso
        have h_zEpre_ne : (∑' ω : PMF (PMF State),
            pe'.scheduler.next E_pre (some (l, ω)) *
            ∑' μ_new : PMF State, ω μ_new * μ_new s') ≠ 0 := by
          intro h
          apply hE_pre_supp
          rw [h, mul_zero]
        apply h_zEpre_ne
        -- Now identify the two `tsum`s.
        have h_swap : (∑' (p : PMF (PMF State) × PMF State),
              pe'.scheduler.next E_pre (some (l, p.1)) * p.1 p.2 * p.2 s')
            = ∑' ω : PMF (PMF State),
                pe'.scheduler.next E_pre (some (l, ω)) *
                ∑' μ_new : PMF State, ω μ_new * μ_new s' := by
          rw [ENNReal.tsum_prod']
          congr 1; funext ω
          rw [← ENNReal.tsum_mul_left]
          congr 1; funext μ_new
          ring
        rw [← h_swap]
        exact h_step
    · -- Degenerate top-level: E = (⟨s₀, ofList (rest_prev ++ [last])⟩).dirac.
      change E ∈ (beliefDefault ⟨s₀, Stream'.Seq.ofList (rest_prev ++ [last])⟩).support at hE
      unfold beliefDefault at hE
      rw [PMF.mem_support_pure_iff] at hE
      subst hE
      -- E = ⟨s₀, ofList (rest_prev ++ [last])⟩.dirac.
      set e_full : AlterSeq State Label :=
        ⟨s₀, Stream'.Seq.ofList (rest_prev ++ [last])⟩ with he_full_def
      have he_full_term : e_full.trans.Terminates :=
        Stream'.Seq.terminates_ofList _
      have h_dirac_term : (e_full.dirac).trans.Terminates := by
        change (e_full.trans.map _).Terminates
        exact Stream'.Seq.terminates_map_iff.mpr he_full_term
      refine ⟨h_dirac_term, ?_, ?_, ?_, ?_⟩
      · change s₀ ∈ (PMF.pure s₀).support
        rw [PMF.mem_support_pure_iff]
      · -- labels: dirac.trans.map (·.1) = e_full.trans.map (·.1).
        change Stream'.Seq.map (fun lμ : Label × PMF State => lμ.1)
            (e_full.trans.map (fun lq => (lq.1, PMF.pure lq.2)))
          = Stream'.Seq.map (fun ls : Label × State => ls.1) e_full.trans
        ext n
        rw [Stream'.Seq.map_get?, Stream'.Seq.map_get?, Stream'.Seq.map_get?]
        cases h : e_full.trans.get? n with
        | none => simp
        | some lq => simp
      · -- endState compat.
        -- e_full.dirac.endState = PMF.pure (e_full.endState).
        -- need e_full.endState ∈ (PMF.pure (e_full.endState)).support.
        -- For this we need a small fact: dirac.endState = pure of endState.
        -- We'll show this via stateAt equality, but the cleanest path is to
        -- use that `dirac = map PMF.pure` and propagate.
        -- Actually we can just appeal to the fact that the LHS state matches.
        -- Let's compute directly using stateAt_find_eq_endState.
        have h_eq : e_full.dirac.endState h_dirac_term
            = PMF.pure (e_full.endState he_full_term) := by
          -- Show via stateAt: e_full.dirac = e_full.map PMF.pure,
          -- and stateAt of map = (stateAt).map PMF.pure.
          -- Use that endState = (stateAt (Nat.find _)).get _ on both.
          -- Key: For any `e : AlterSeq State Label` (with `Terminates`),
          -- (e.map f).endState _ = f (e.endState _) (since map preserves
          -- termination and stateAt structures).
          -- We prove this as an inline auxiliary.
          have h_aux : ∀ (e : AlterSeq State Label) (h : e.trans.Terminates)
              (h_dir : (e.map PMF.pure).trans.Terminates),
              (e.map PMF.pure).endState h_dir = PMF.pure (e.endState h) := by
            intro e h h_dir
            -- The find positions agree because labels of `map` are unchanged.
            have h_find_eq : Nat.find h_dir = Nat.find h := by
              apply le_antisymm
              · apply Nat.find_le
                change ((e.trans.map _).get? (Nat.find h)) = none
                rw [Stream'.Seq.map_get?]
                have h_spec := Nat.find_spec h
                change e.trans.get? (Nat.find h) = none at h_spec
                rw [h_spec]; rfl
              · apply Nat.find_le
                have h_spec := Nat.find_spec h_dir
                change (e.trans.map _).get? (Nat.find h_dir) = none at h_spec
                rw [Stream'.Seq.map_get?] at h_spec
                change e.trans.get? (Nat.find h_dir) = none
                rcases h_get : e.trans.get? (Nat.find h_dir) with - | val
                · rfl
                · rw [h_get] at h_spec; simp at h_spec
            -- Now use the equality of find values and the structure of stateAt.
            have h_stateAt_dir := AlterSeq.stateAt_find_eq_endState (e.map PMF.pure) h_dir
            have h_stateAt_e := AlterSeq.stateAt_find_eq_endState e h
            -- Compute (e.map PMF.pure).stateAt (Nat.find h) = some (PMF.pure (e.endState h)).
            have h_stateAt_map :
                (e.map PMF.pure).stateAt (Nat.find h_dir)
                  = some (PMF.pure (e.endState h)) := by
              rw [h_find_eq]
              rcases hf : Nat.find h with - | k
              · -- stateAt 0 = some init.
                change some ((e.map PMF.pure).init) = some (PMF.pure (e.endState h))
                rw [show e.endState h = e.init from by
                  rw [hf] at h_stateAt_e
                  exact (Option.some.inj h_stateAt_e).symm]
                rfl
              · -- stateAt (k+1) = (get? k).map snd.
                change ((e.trans.map _).get? k).map Prod.snd
                  = some (PMF.pure (e.endState h))
                rw [Stream'.Seq.map_get?]
                rw [hf] at h_stateAt_e
                change (e.trans.get? k).map Prod.snd = some (e.endState h) at h_stateAt_e
                rcases hk : e.trans.get? k with - | lq
                · rw [hk] at h_stateAt_e; simp at h_stateAt_e
                · rw [hk] at h_stateAt_e
                  simp at h_stateAt_e
                  simp [← h_stateAt_e]
            rw [h_stateAt_map] at h_stateAt_dir
            exact (Option.some.inj h_stateAt_dir).symm
          exact h_aux e_full he_full_term h_dirac_term
        rw [h_eq]
        change e_full.endState he_full_term
          ∈ (PMF.pure (e_full.endState he_full_term)).support
        rw [PMF.mem_support_pure_iff]
      · -- get? compat at every position for dirac.
        intro n l₀ μ s₂ hn_E hn_e
        change (Stream'.Seq.map (fun lq : Label × State => (lq.1, PMF.pure lq.2))
            e_full.trans).get? n = some (l₀, μ) at hn_E
        rw [Stream'.Seq.map_get?] at hn_E
        change e_full.trans.get? n = some (l₀, s₂) at hn_e
        rw [hn_e] at hn_E
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hn_E
        obtain ⟨_, h_μ_eq⟩ := hn_E
        rw [← h_μ_eq]
        rw [PMF.mem_support_pure_iff]

/-- **Support compatibility.** Every `𝒟(sys)`-history `E` in the support of
`belief pe' e` (for a finite `e`) is itself finite, has the same label
sequence and the same length as `e`, contains `e.init` in `E.init.support`,
and satisfies `s_i ∈ μ_i.support` at every position. In particular
`e.endState ∈ (E.endState _).support`. -/
theorem ProbabilisticExecution.belief_support_compat
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    {e : AlterSeq State Label} (he : e.trans.Terminates)
    {E : AlterSeq (PMF State) Label}
    (hE : E ∈ (pe'.belief e).support) :
    ∃ hE_term : E.trans.Terminates,
      e.init ∈ E.init.support ∧
      E.trans.map (fun lμ : Label × PMF State => lμ.1)
        = e.trans.map (fun ls : Label × State => ls.1) ∧
      e.endState he ∈ (E.endState hE_term).support ∧
      (∀ n l μ s, E.trans.get? n = some (l, μ) → e.trans.get? n = some (l, s) →
          s ∈ μ.support) := by
  classical
  -- Unfold `belief pe' e` to `beliefRec pe' e.init (e.trans.toList he)`.
  change E ∈ (open Classical in
    if hT : e.trans.Terminates then
      pe'.beliefRec e.init (e.trans.toList hT)
    else
      beliefDefault e).support at hE
  rw [dif_pos he] at hE
  obtain ⟨hE_term, h_init, h_lab, h_end, h_compat⟩ :=
    pe'.beliefRec_support_compat e.init (e.trans.toList he) hE
  -- `Seq.ofList (e.trans.toList he) = e.trans`.
  have h_eq : Stream'.Seq.ofList (e.trans.toList he) = e.trans :=
    Stream'.Seq.ofList_toList e.trans he
  refine ⟨hE_term, h_init, ?_, ?_, ?_⟩
  · rw [h_lab, h_eq]
  · -- endState ⟨e.init, ofList (toList _)⟩ = endState e (via h_eq).
    have h_struct :
        (⟨e.init, Stream'.Seq.ofList (e.trans.toList he)⟩ : AlterSeq State Label) = e := by
      cases e with
      | mk init trans =>
        simp only [h_eq]
    -- Rewrite via `h_struct` in the conclusion, using subst on the inner alterSeq.
    -- Since `e.endState he` and the LHS endState both eq via dependent rewrite,
    -- transport `h_end` along `h_struct`.
    have : ∀ (e' : AlterSeq State Label) (h' : e'.trans.Terminates)
              (h'' : e.trans.Terminates) (heq : e' = e),
              e'.endState h' = e.endState h'' := by
      intro e' h' h'' heq
      subst heq
      rfl
    rw [this _ _ he h_struct] at h_end
    exact h_end
  · intro n l μ s hn_E hn_e
    apply h_compat n l μ s hn_E
    rw [h_eq]; exact hn_e

/-- **Belief fibre preserves traces.** For any `E` in the support of
`pe'.belief e`, the `𝒟(sys)`-trace of `E` equals the `sys`-trace of `e`.

Follows from `belief_support_compat`: the equal label sequences (witnessed
by `E.trans.map (·.1) = e.trans.map (·.1)`) determine the same trace,
since `𝒟(sys).internal = sys.internal` and `trace = (map ·.1) ∘ (filter
(¬internal ·.1))`. -/
theorem ProbabilisticExecution.belief_trace_eq
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    {e : AlterSeq State Label} (he : e.trans.Terminates)
    {E : AlterSeq (PMF State) Label}
    (hE : E ∈ (pe'.belief e).support) :
    𝒟(sys).trace E = sys.trace e := by
  obtain ⟨_, _, h_lab, _, _⟩ := pe'.belief_support_compat he hE
  -- Both traces equal `(_.trans.map ·.1).filter (¬sys.internal)` via `filter_map`,
  -- then become equal via `h_lab`.
  unfold LabelledSystem.trace
  change (E.trans.filter (fun p => ¬ sys.internal p.1)).map (fun lμ => lμ.1)
     = (e.trans.filter (fun p => ¬ sys.internal p.1)).map (fun ls => ls.1)
  rw [show (fun p : Label × PMF State => ¬ sys.internal p.1)
        = (fun l : Label => ¬ sys.internal l) ∘ (fun lμ : Label × PMF State => lμ.1)
        from rfl,
      ← Stream'.Seq.filter_map (fun lμ : Label × PMF State => lμ.1)
        (fun l => ¬ sys.internal l) E.trans,
      show (fun p : Label × State => ¬ sys.internal p.1)
        = (fun l : Label => ¬ sys.internal l) ∘ (fun ls : Label × State => ls.1)
        from rfl,
      ← Stream'.Seq.filter_map (fun ls : Label × State => ls.1)
        (fun l => ¬ sys.internal l) e.trans,
      h_lab]

/-- **Belief fibre preserves tightness.** For any `E` in the support of
`pe'.belief e`, `𝒟(sys).IsTight E ↔ sys.IsTight e`.

Follows from `belief_support_compat`: tightness depends only on the label
sequence and the position of `e.trans`'s last entry, both of which transfer
via the label-equality conjunct (`E.trans.map (·.1) = e.trans.map (·.1)`). -/
theorem ProbabilisticExecution.belief_isTight_iff
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    {e : AlterSeq State Label} (he : e.trans.Terminates)
    {E : AlterSeq (PMF State) Label}
    (hE : E ∈ (pe'.belief e).support) :
    𝒟(sys).IsTight E ↔ sys.IsTight e := by
  obtain ⟨_, _, h_lab, _, _⟩ := pe'.belief_support_compat he hE
  -- Both `TerminatedAt n` and the label at each position depend only on
  -- `_.trans.map (·.1)` (after `Stream'.Seq.terminatedAt_map_iff` and `map_get?`).
  unfold LabelledSystem.IsTight
  -- Helper: `_.trans.TerminatedAt k ↔ _.trans.map (·.1).TerminatedAt k`.
  have h_term_iff : ∀ k, E.trans.TerminatedAt k ↔ e.trans.TerminatedAt k := by
    intro k
    rw [← Stream'.Seq.terminatedAt_map_iff (f := fun lμ : Label × PMF State => lμ.1)
          (s := E.trans),
        ← Stream'.Seq.terminatedAt_map_iff (f := fun ls : Label × State => ls.1)
          (s := e.trans),
        h_lab]
  -- Helper for the existential: `E.trans.get? n = some (l, μ) ↔
  -- e.trans.get? n = some (l, _)` at the label level.
  -- Use `_.trans.map (·.1).get? n = some l` as the common bridge.
  have h_lab_get : ∀ n l,
      (∃ μ, E.trans.get? n = some (l, μ)) ↔ (∃ s, e.trans.get? n = some (l, s)) := by
    intro n l
    have h_bridge : (E.trans.map (fun lμ : Label × PMF State => lμ.1)).get? n
        = (e.trans.map (fun ls : Label × State => ls.1)).get? n := by
      rw [h_lab]
    rw [Stream'.Seq.map_get?, Stream'.Seq.map_get?] at h_bridge
    constructor
    · rintro ⟨μ, hμ⟩
      rw [hμ] at h_bridge
      rcases hs : e.trans.get? n with - | ⟨l', s⟩
      · rw [hs] at h_bridge; simp at h_bridge
      · rw [hs] at h_bridge
        simp only [Option.map_some, Option.some.injEq] at h_bridge
        -- `h_bridge : l = l'`. Goal post-rcases: `∃ s, some (l', s) = some (l, s)`.
        exact ⟨s, by rw [h_bridge]⟩
    · rintro ⟨s, hs⟩
      rw [hs] at h_bridge
      rcases hE_g : E.trans.get? n with - | ⟨l', μ⟩
      · rw [hE_g] at h_bridge; simp at h_bridge
      · rw [hE_g] at h_bridge
        simp only [Option.map_some, Option.some.injEq] at h_bridge
        -- `h_bridge : l' = l`. Goal post-rcases: `∃ μ, some (l', μ) = some (l, μ)`.
        exact ⟨μ, by rw [h_bridge]⟩
  constructor
  · rintro (h0 | ⟨n, l, μ, h_get, h_succ, h_ext⟩)
    · left; exact (h_term_iff 0).mp h0
    · right
      obtain ⟨s, hs⟩ := (h_lab_get n l).mp ⟨μ, h_get⟩
      exact ⟨n, l, s, hs, (h_term_iff (n + 1)).mp h_succ, h_ext⟩
  · rintro (h0 | ⟨n, l, s, h_get, h_succ, h_ext⟩)
    · left; exact (h_term_iff 0).mpr h0
    · right
      obtain ⟨μ, hμ⟩ := (h_lab_get n l).mpr ⟨s, h_get⟩
      exact ⟨n, l, μ, hμ, (h_term_iff (n + 1)).mpr h_succ, h_ext⟩

/-- The constructed `sys`-scheduler from a `𝒟(sys)`-probabilistic execution.
At history `e`: if `e` terminates, sample a belief `𝒟(sys)`-history `E`,
sample `(l, ω) ∼ pe'.scheduler.next E`, then sample `μ' ∼ p_ω(e.endState)`
via `distHyperKernel`, and emit `(l, μ')`. The `none` branch and the
non-terminating-`e` branch both pass through to `PMF.pure none`.

Validity follows from `belief_support_compat` (which gives `e.endState`
membership in `E.endState.support` and `E`'s termination) and
`distHyperKernel_step` (which gives `sys.step` from the kernel sample). -/
noncomputable def Scheduler.ofDist
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem) :
    Scheduler sys.toSystem where
  next e :=
    open Classical in
    if h_term : e.trans.Terminates then
      (pe'.belief e).bind (fun E =>
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
    -- Termination of `e.trans`.
    have h_term : e.trans.Terminates := ⟨n, e_term_n⟩
    -- Identify `s = e.endState h_term`: from `stateAt n = some s` and
    -- `TerminatedAt n`, conclude `n = Nat.find h_term`.
    have h_find_le : Nat.find h_term ≤ n := Nat.find_le e_term_n
    -- For m > Nat.find h_term, stateAt m = none (because get? at m-1 is none).
    have h_n_le : n ≤ Nat.find h_term := by
      by_contra h_lt
      push Not at h_lt
      -- n > Nat.find h_term, so n ≥ 1. Write n = k+1 with k ≥ Nat.find h_term.
      rcases n with _ | k
      · exact absurd h_lt (Nat.not_lt_zero _)
      · -- `TerminatedAt (Nat.find h_term)` and Nat.find h_term ≤ k.
        have hk_ge : Nat.find h_term ≤ k := Nat.lt_succ_iff.mp h_lt
        have h_term_k : e.trans.TerminatedAt k :=
          Stream'.Seq.terminated_stable e.trans hk_ge (Nat.find_spec h_term)
        -- `stateAt (k+1) = (get? k).map snd = none`.
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
    -- Unfold the next via if_pos.
    change some (l, μ) ∈
      (open Classical in
        if h_term' : e.trans.Terminates then
          (pe'.belief e).bind (fun E =>
            (pe'.scheduler.next E).bind (fun opt =>
              match opt with
              | none => PMF.pure none
              | some (l', ω) =>
                (pe'.distHyperKernel E l' ω (e.endState h_term')).map
                  (fun μ' => some (l', μ'))))
        else PMF.pure none).support at h_supp
    rw [dif_pos h_term] at h_supp
    -- Decompose the nested binds.
    rw [PMF.mem_support_bind_iff] at h_supp
    obtain ⟨E, hE_belief, h_supp⟩ := h_supp
    rw [PMF.mem_support_bind_iff] at h_supp
    obtain ⟨opt, hopt_sch, h_supp⟩ := h_supp
    -- Apply belief_support_compat.
    obtain ⟨hE_term, _h_init, _h_lab, h_endState, _h_compat⟩ :=
      pe'.belief_support_compat h_term hE_belief
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
      -- Now apply distHyperKernel_step.
      exact pe'.distHyperKernel_step hE_term hopt_sch h_endState h_μ'_kernel

/-- The constructed `sys`-probabilistic execution: initial distribution is
the `bind id` flattening of `pe'.initState : PMF (PMF State)`, and the
scheduler is `Scheduler.ofDist pe'`. -/
noncomputable def ProbabilisticExecution.ofDist
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem) :
    ProbabilisticExecution sys.toSystem where
  initState := pe'.initState.bind id
  scheduler := Scheduler.ofDist pe'

/-- Helper: `Seq.map f s = Seq.nil ↔ s = Seq.nil`. -/
private lemma seq_map_eq_nil_iff {α β : Type} (f : α → β) (s : Seq α) :
    s.map f = Seq.nil ↔ s = Seq.nil := by
  constructor
  · intro h
    apply Stream'.Seq.ext
    intro n
    have h_get : (s.map f).get? n = none := by rw [h]; rfl
    rw [Stream'.Seq.map_get?] at h_get
    cases hs : s.get? n
    · rfl
    · rw [hs] at h_get; exact absurd h_get (by simp [Option.map_some])
  · intro h; rw [h]; exact Stream'.Seq.map_nil _

/-- **Belief vanishes for non-nil prefix when target trans is nil.** If
`e.trans ≠ Seq.nil`, then `pe'.belief e ⟨μ_0, Seq.nil⟩ = 0`.

Follows from `belief_support_compat`: support membership implies the label
sequence `e.trans.map fst` equals `Seq.nil.map fst = Seq.nil`, forcing
`e.trans = Seq.nil`. -/
private theorem ProbabilisticExecution.belief_at_nil_eq_zero_of_trans_ne_nil
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    {e : AlterSeq State Label} (he : e.trans.Terminates) (μ_0 : PMF State)
    (h_ne : e.trans ≠ Seq.nil) :
    pe'.belief e ⟨μ_0, Seq.nil⟩ = 0 := by
  classical
  by_contra h
  have h' : ⟨μ_0, Seq.nil⟩ ∈ (pe'.belief e).support :=
    (PMF.mem_support_iff _ _).mpr h
  obtain ⟨_, _, h_lab, _, _⟩ := pe'.belief_support_compat he h'
  -- `h_lab` gives `(⟨μ_0, nil⟩.trans).map fst = e.trans.map fst`, so
  -- `Seq.nil = e.trans.map fst`, hence `e.trans = nil`.
  change (Seq.nil : Seq (Label × PMF State)).map _
       = e.trans.map _ at h_lab
  rw [Stream'.Seq.map_nil] at h_lab
  exact h_ne ((seq_map_eq_nil_iff _ _).mp h_lab.symm)

/-- **Bayes inversion, base case (nil trans).** For `E.trans = Seq.nil`, the
disintegration identity reduces to:
  `pe'.initState μ_0 =
    ∑' (e : {e // e.trans.Terminates}), pe'.ofDist.probOf e.1 e.2 * pe'.belief e.1 ⟨μ_0, nil⟩`.

The sum collapses to `s_0 : State` (those `e` with `e.trans = nil`), and each
term simplifies to `pe'.initState μ_0 * μ_0 s_0` via `PMF.normalize_apply`,
summing to `pe'.initState μ_0` by `μ_0.tsum_coe`. -/
private theorem ProbabilisticExecution.belief_bayes_inversion_nil
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem) (μ_0 : PMF State) :
    pe'.probOf ⟨μ_0, Seq.nil⟩ Stream'.Seq.terminates_nil =
      ∑' (e : {e : AlterSeq State Label // e.trans.Terminates}),
        pe'.ofDist.probOf e.1 e.2 * pe'.belief e.1 ⟨μ_0, Seq.nil⟩ := by
  classical
  -- LHS simplifies via `probOf_nil`.
  rw [ProbabilisticExecution.probOf_nil]
  -- Reduce RHS subtype sum to a sum over `State` (via the bijection `s_0 ↦ ⟨⟨s_0, nil⟩, _⟩`).
  -- For `e.1.trans ≠ nil`, `pe'.belief e.1 ⟨μ_0, nil⟩ = 0` (label-length mismatch).
  have h_rhs_eq :
      (∑' (e : {e : AlterSeq State Label // e.trans.Terminates}),
        pe'.ofDist.probOf e.1 e.2 * pe'.belief e.1 ⟨μ_0, Seq.nil⟩) =
      ∑' (s_0 : State),
        pe'.ofDist.probOf ⟨s_0, Seq.nil⟩ Stream'.Seq.terminates_nil *
        pe'.belief ⟨s_0, Seq.nil⟩ ⟨μ_0, Seq.nil⟩ := by
    -- The map `s_0 ↦ ⟨⟨s_0, nil⟩, terminates_nil⟩` injects `State` into the
    -- subtype; off its image, terms are zero by `belief_eq_zero_of_length_ne`.
    refine tsum_eq_tsum_of_ne_zero_bij
      (i := fun (s_0 : { s_0 : State // pe'.ofDist.probOf ⟨s_0, Seq.nil⟩
          Stream'.Seq.terminates_nil * pe'.belief ⟨s_0, Seq.nil⟩
            ⟨μ_0, Seq.nil⟩ ≠ 0 }) =>
        (⟨⟨s_0.1, Seq.nil⟩, Stream'.Seq.terminates_nil⟩ :
          { e : AlterSeq State Label // e.trans.Terminates }))
      ?_ ?_ ?_
    · -- Injectivity.
      intro a b h
      apply Subtype.ext
      have := (Subtype.ext_iff.mp h)
      -- this : (⟨a.1, nil⟩ : AlterSeq State Label) = ⟨b.1, nil⟩
      injection this
    · -- Image covers nonzero support.
      intro e he_ne
      classical
      -- `he_ne : e ∈ Function.support (fun e => ...)` i.e. summand ≠ 0.
      -- For e.1.trans ≠ nil, the belief factor is zero.
      have h_trans_nil : e.1.trans = Seq.nil := by
        by_contra h_ne_nil
        apply he_ne
        change pe'.ofDist.probOf e.1 e.2 * pe'.belief e.1 ⟨μ_0, Seq.nil⟩ = 0
        rw [pe'.belief_at_nil_eq_zero_of_trans_ne_nil e.2 μ_0 h_ne_nil, mul_zero]
      -- Now e.1 = ⟨e.1.init, Seq.nil⟩.
      have h_e1 : e.1 = ⟨e.1.init, Seq.nil⟩ := by
        rcases h_e : e.1 with ⟨i, t⟩
        rw [h_e] at h_trans_nil
        simp only at h_trans_nil
        subst h_trans_nil
        simp only
      -- Build the witness `s_0 = e.1.init`.
      refine ⟨⟨e.1.init, ?_⟩, ?_⟩
      · -- Nonzero condition transports.
        intro h_eq
        apply he_ne
        change pe'.ofDist.probOf e.1 e.2 * pe'.belief e.1 ⟨μ_0, Seq.nil⟩ = 0
        -- Use h_e1 via congr to handle the dependent proof term.
        have h_pof : pe'.ofDist.probOf e.1 e.2
            = pe'.ofDist.probOf ⟨e.1.init, Seq.nil⟩ Stream'.Seq.terminates_nil := by
          congr 1
        rw [h_pof]
        have h_b : pe'.belief e.1 = pe'.belief ⟨e.1.init, Seq.nil⟩ := by
          congr 1
        rw [h_b]
        exact h_eq
      · apply Subtype.ext
        change (⟨e.1.init, Seq.nil⟩ : AlterSeq State Label) = e.1
        exact h_e1.symm
    · -- Values match on the bijection's image.
      intro s_0
      rfl
  rw [h_rhs_eq]
  -- Now: pe'.initState μ_0 = ∑' s_0, (pe'.initState.bind id) s_0 * belief ⟨s_0, nil⟩ ⟨μ_0, nil⟩.
  -- Use `pe'.ofDist.probOf ⟨s_0, nil⟩ = pe'.initState.bind id s_0` (from probOf_nil on ofDist).
  -- And `belief ⟨s_0, nil⟩ ⟨μ_0, nil⟩ = beliefBase s_0 ⟨μ_0, nil⟩` (belief def at nil).
  -- The product is `pe'.initState μ_0 * μ_0 s_0` (after cancelling the marginal
  -- in the non-degenerate case; the degenerate case multiplies by zero).
  have h_summand : ∀ s_0 : State,
      pe'.ofDist.probOf ⟨s_0, Seq.nil⟩ Stream'.Seq.terminates_nil *
        pe'.belief ⟨s_0, Seq.nil⟩ ⟨μ_0, Seq.nil⟩ = pe'.initState μ_0 * μ_0 s_0 := by
    intro s_0
    -- LHS first factor: pe'.ofDist.probOf ⟨s_0, nil⟩ _ = pe'.ofDist.init s_0
    --                 = pe'.ofDist.initState s_0 = (pe'.initState.bind id) s_0
    --                 = ∑' init, pe'.initState init * init s_0.
    rw [ProbabilisticExecution.probOf_nil]
    -- Unfold pe'.ofDist.init.
    change (pe'.ofDist.initState : PMF State) s_0 *
        pe'.belief ⟨s_0, Seq.nil⟩ ⟨μ_0, Seq.nil⟩ = pe'.initState μ_0 * μ_0 s_0
    change (pe'.initState.bind id) s_0 *
        pe'.belief ⟨s_0, Seq.nil⟩ ⟨μ_0, Seq.nil⟩ = pe'.initState μ_0 * μ_0 s_0
    rw [PMF.bind_apply]
    -- The first factor is now `∑' init, pe'.initState init * id init s_0`.
    simp only [id]
    show (∑' init, pe'.initState init * init s_0) *
        pe'.belief ⟨s_0, Seq.nil⟩ ⟨μ_0, Seq.nil⟩ = pe'.initState μ_0 * μ_0 s_0
    -- LHS second factor: belief ⟨s_0, nil⟩ ⟨μ_0, nil⟩ = beliefBase s_0 ⟨μ_0, nil⟩.
    have h_belief :
        pe'.belief ⟨s_0, Seq.nil⟩ ⟨μ_0, Seq.nil⟩ = pe'.beliefBase s_0 ⟨μ_0, Seq.nil⟩ := by
      change (open Classical in
        if hT : (⟨s_0, Seq.nil⟩ : AlterSeq State Label).trans.Terminates then
          pe'.beliefRec s_0 ((⟨s_0, Seq.nil⟩ : AlterSeq State Label).trans.toList hT)
        else
          beliefDefault ⟨s_0, Seq.nil⟩) ⟨μ_0, Seq.nil⟩ = _
      rw [dif_pos Stream'.Seq.terminates_nil]
      -- Reduce trans.toList nil = [].
      have : (⟨s_0, Seq.nil⟩ : AlterSeq State Label).trans.toList Stream'.Seq.terminates_nil
            = ([] : List (Label × State)) := Stream'.Seq.toList_nil
      rw [this]
      -- beliefRec _ [] = beliefBase via reverseRecOn at nil.
      simp [ProbabilisticExecution.beliefRec, List.reverseRecOn]
    rw [h_belief]
    -- Set Z := ∑' init, pe'.initState init * init s_0.
    set Z : ENNReal := ∑' init : PMF State, pe'.initState init * init s_0 with hZ_def
    -- Case-split on whether Z = 0 (degenerate vs non-degenerate).
    by_cases hZ : Z = 0
    · -- Degenerate case: Z = 0; first factor is 0.
      rw [hZ, zero_mul]
      -- And Z = 0 forces pe'.initState μ_0 * μ_0 s_0 = 0.
      have h_zero : pe'.initState μ_0 * μ_0 s_0 = 0 := by
        have h_tsum_zero : (∑' init : PMF State, pe'.initState init * init s_0) = 0 := hZ
        exact (ENNReal.tsum_eq_zero.mp h_tsum_zero) μ_0
      rw [h_zero]
    · -- Non-degenerate case: Z ≠ 0. Unfold beliefBase via dif_pos.
      have h_top : Z ≠ ⊤ := by
        apply ne_of_lt
        calc Z ≤ ∑' init : PMF State, pe'.initState init := by
              apply ENNReal.tsum_le_tsum
              intro init
              exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
          _ = 1 := pe'.initState.tsum_coe
          _ < ⊤ := ENNReal.one_lt_top
      have h_bb : pe'.beliefBase s_0 ⟨μ_0, Seq.nil⟩
          = (PMF.normalize (fun init => pe'.initState init * init s_0) hZ h_top).map
              (fun init => (⟨init, Seq.nil⟩ : AlterSeq (PMF State) Label)) ⟨μ_0, Seq.nil⟩ := by
        change (open Classical in
          if h0 : (∑' init : PMF State, pe'.initState init * init s_0) ≠ 0 then
            have h_top : (∑' init : PMF State, pe'.initState init * init s_0) ≠ ⊤ := by
              apply ne_of_lt
              calc (∑' init : PMF State, pe'.initState init * init s_0)
                  ≤ ∑' init : PMF State, pe'.initState init := by
                    apply ENNReal.tsum_le_tsum
                    intro init
                    exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
                _ = 1 := pe'.initState.tsum_coe
                _ < ⊤ := ENNReal.one_lt_top
            (PMF.normalize (fun init => pe'.initState init * init s_0) h0 h_top).map
              (fun init => ⟨init, Seq.nil⟩)
          else
            beliefDefault ⟨s_0, Seq.nil⟩) ⟨μ_0, Seq.nil⟩ = _
        rw [dif_pos hZ]
      rw [h_bb]
      -- map_apply: ∑' init, [⟨μ_0, nil⟩ = ⟨init, nil⟩] * normalize ... init.
      rw [PMF.map_apply]
      -- Reduce indicator at unique nonzero point.
      have h_tsum :
          (∑' init : PMF State,
              if (⟨μ_0, Seq.nil⟩ : AlterSeq (PMF State) Label) = ⟨init, Seq.nil⟩
                then PMF.normalize (fun init => pe'.initState init * init s_0) hZ h_top init
                else 0)
            = PMF.normalize (fun init => pe'.initState init * init s_0) hZ h_top μ_0 := by
        rw [tsum_eq_single μ_0]
        · simp
        · intro b hb_ne
          have h_neq : (⟨μ_0, Seq.nil⟩ : AlterSeq (PMF State) Label) ≠ ⟨b, Seq.nil⟩ := by
            intro h
            apply hb_ne
            injection h with h_init _
            exact h_init.symm
          rw [if_neg h_neq]
      rw [h_tsum, PMF.normalize_apply]
      -- Now: Z * (w μ_0 * Z⁻¹) = pe'.initState μ_0 * μ_0 s_0.
      change Z * (pe'.initState μ_0 * μ_0 s_0 * (∑' x, pe'.initState x * x s_0)⁻¹)
          = pe'.initState μ_0 * μ_0 s_0
      rw [show (∑' x : PMF State, pe'.initState x * x s_0) = Z from rfl]
      rw [← mul_assoc, mul_comm Z _, mul_assoc]
      rw [ENNReal.mul_inv_cancel hZ h_top, mul_one]
  rw [tsum_congr h_summand, ENNReal.tsum_mul_left, μ_0.tsum_coe, mul_one]
  rfl

/-- **Per-`e'_pre` marginal of next sys-state `q_new` at label `l`**, under the
user's joint sampling `p`. Equivalent to `p_sys(e'_pre ∙ (l, q_new)) / p_sys(e'_pre)`
in the non-degenerate case. Concretely: averaged over `belief e'_pre`, the
scheduler-emission/ω-bind probability of producing `q_new` from the current
sys-history. -/
private noncomputable def ProbabilisticExecution.Z_global
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (e'_pre : AlterSeq State Label) (l : Label) (q_new : State) : ENNReal :=
  ∑' (E : AlterSeq (PMF State) Label),
    pe'.belief e'_pre E *
    ∑' (ω : PMF (PMF State)),
      pe'.scheduler.next E (some (l, ω)) * (ω.bind id) q_new

/-- **H1 — RHS vanishes when `Z_global = 0`.** In the degenerate corner where the
joint sampling assigns zero probability to producing `q_new` at label `l` from
the prior `belief e'_pre`, the RHS of `belief_factor_step` is identically zero.
Either the `belief` factor is itself zero, or every term in the bind-sum
constituting `pe'.kernel · μ_new q_new` is forced to zero by the per-`E`
analysis of `Z_global = 0`. -/
private lemma ProbabilisticExecution.belief_factor_step_rhs_zero_of_Z_global_zero
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (μ_0 : PMF State) (rest_prev : List (Label × PMF State))
    (l : Label) (μ_new : PMF State) (q_new : State)
    (e'_pre : AlterSeq State Label)
    (hZ : pe'.Z_global e'_pre l q_new = 0) :
    pe'.belief e'_pre ⟨μ_0, Seq.ofList rest_prev⟩ *
        pe'.kernel ⟨μ_0, Seq.ofList rest_prev⟩ (l, μ_new) *
        μ_new q_new
      = 0 := by
  classical
  set E := (⟨μ_0, Seq.ofList rest_prev⟩ : AlterSeq (PMF State) Label) with hE_def
  by_cases h_belief : pe'.belief e'_pre E = 0
  · rw [h_belief, zero_mul, zero_mul]
  -- belief ≠ 0; derive that the per-E inner sum in Z_global is zero.
  have h_perE : pe'.belief e'_pre E *
        (∑' (ω : PMF (PMF State)),
          pe'.scheduler.next E (some (l, ω)) * (ω.bind id) q_new) = 0 := by
    have hZ' : (∑' (E' : AlterSeq (PMF State) Label),
        pe'.belief e'_pre E' *
          ∑' (ω : PMF (PMF State)),
            pe'.scheduler.next E' (some (l, ω)) * (ω.bind id) q_new) = 0 := hZ
    exact ENNReal.tsum_eq_zero.mp hZ' E
  have h_inner_zero :
      (∑' (ω : PMF (PMF State)),
          pe'.scheduler.next E (some (l, ω)) * (ω.bind id) q_new) = 0 := by
    rcases mul_eq_zero.mp h_perE with h | h
    · exact absurd h h_belief
    · exact h
  -- For each ω: per-term is zero.
  have h_perω : ∀ ω : PMF (PMF State),
      pe'.scheduler.next E (some (l, ω)) * (ω.bind id) q_new = 0 :=
    fun ω => ENNReal.tsum_eq_zero.mp h_inner_zero ω
  -- Goal: belief * kernel * μ_new q_new = 0; suffices kernel * μ_new q_new = 0.
  suffices h_k : pe'.kernel E (l, μ_new) * μ_new q_new = 0 by
    rw [mul_assoc, h_k, mul_zero]
  -- Expand `pe'.kernel` and pull `μ_new q_new` inside.
  unfold ProbabilisticExecution.kernel
  rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_eq_zero]
  intro ω
  -- For ω: scheduler.next E (some (l, ω)) * ω μ_new * μ_new q_new = 0.
  by_cases h_sch : pe'.scheduler.next E (some (l, ω)) = 0
  · rw [h_sch, zero_mul, zero_mul]
  -- scheduler.next ≠ 0; from h_perω, (ω.bind id) q_new = 0.
  have h_bind_zero : (ω.bind id) q_new = 0 := by
    rcases mul_eq_zero.mp (h_perω ω) with h | h
    · exact absurd h h_sch
    · exact h
  -- (ω.bind id) q_new = ∑' μ', ω μ' * μ' q_new = 0; in particular ω μ_new * μ_new q_new = 0.
  have h_bind_apply : (ω.bind id) q_new = ∑' μ', ω μ' * μ' q_new := by
    rw [PMF.bind_apply]; rfl
  rw [h_bind_apply] at h_bind_zero
  have h_at_μnew : ω μ_new * μ_new q_new = 0 :=
    ENNReal.tsum_eq_zero.mp h_bind_zero μ_new
  rw [mul_assoc, h_at_μnew, mul_zero]

/-- **H2 — `beliefStepCond` at unmatched `E_pre'` gives zero mass on the target
extended PMF-history.** The output of `beliefStepCond E_pre' l q_new` is
supported on PMF-histories of shape `⟨E_pre'.init, E_pre'.trans ++ [(l, _)]⟩`.
For this to match `⟨μ_0, (ofList rest_prev) ++ [(l, μ_new)]⟩` we'd need
`E_pre'.init = μ_0` AND `E_pre'.trans = ofList rest_prev` (by
`append_singleton_inj_left`), i.e. `E_pre' = ⟨μ_0, ofList rest_prev⟩`. -/
private lemma ProbabilisticExecution.belief_factor_step_bind_collapse
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (μ_0 : PMF State) (rest_prev : List (Label × PMF State))
    (l : Label) (μ_new : PMF State) (q_new : State)
    (E_pre' : AlterSeq (PMF State) Label)
    (h_ne : E_pre' ≠ ⟨μ_0, Seq.ofList rest_prev⟩) :
    (pe'.beliefStepCond E_pre' l q_new)
        ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩
      = 0 := by
  classical
  -- Helper: distinguish two `AlterSeq`s producing distinct extended histories.
  have h_mismatch : ∀ μ : PMF State,
      (⟨E_pre'.init, E_pre'.trans.append (Seq.cons (l, μ) Seq.nil)⟩
        : AlterSeq (PMF State) Label) ≠
      ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ := by
    intro μ h_eq
    -- Extract init equality and trans equality from h_eq.
    have h_init : E_pre'.init = μ_0 := congr_arg AlterSeq.init h_eq
    have h_trans :
        E_pre'.trans.append (Seq.cons (l, μ) Seq.nil)
        = (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil) :=
      congr_arg AlterSeq.trans h_eq
    -- Need: E_pre'.trans terminates. Hmm — actually we may not have that. But the
    -- LHS is `E_pre'.trans.append (cons (l, μ) nil)` — and the RHS is finite. Since
    -- equality of two sequences gives equal `Terminates` (both refer to the same
    -- sequence), we can extract `E_pre'.trans.Terminates` from termination of RHS.
    have h_RHS_term : ((Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)).Terminates :=
      ⟨_, Stream'.Seq.terminatedAt_append_find (Stream'.Seq.terminates_ofList _)
        (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil).choose_spec⟩
    have h_LHS_term : (E_pre'.trans.append (Seq.cons (l, μ) Seq.nil)).Terminates := by
      rw [h_trans]; exact h_RHS_term
    -- Both prefixes terminate.
    have h_Epre'_term : E_pre'.trans.Terminates := by
      obtain ⟨n, h_n⟩ := h_LHS_term
      -- TerminatedAt at some position; map injection back.
      -- Actually simpler: every appended-to-finite is finite means the prefix is finite.
      -- Stream'.Seq has a lemma `terminates_of_append_left` perhaps.
      -- Direct: use Nat.find h_LHS_term as bound.
      refine ⟨n, ?_⟩
      -- If E_pre'.trans does not terminate at n, then the append at n is some value
      -- coming from E_pre'.trans at index n. But h_n says append at n is none.
      -- Use Stream'.Seq.get?_append_before_length contrapositive:
      -- if append.get? n = none, then either E_pre'.trans.get? n = none, OR
      -- E_pre'.trans is finite and we're past it. Either way E_pre'.trans terminates somewhere.
      by_contra h_not_term
      -- TerminatedAt is `get? n = none`; ¬TerminatedAt means `get? n ≠ none`.
      have h_pre_get : E_pre'.trans.get? n ≠ none := h_not_term
      have h_app_get : (E_pre'.trans.append (Seq.cons (l, μ) Seq.nil)).get? n
          = E_pre'.trans.get? n :=
        Stream'.Seq.get?_append_before_length h_not_term
      have h_n_get : (E_pre'.trans.append (Seq.cons (l, μ) Seq.nil)).get? n = none := h_n
      rw [h_app_get] at h_n_get
      exact h_pre_get h_n_get
    have h_prev_term : (Seq.ofList rest_prev).Terminates :=
      Stream'.Seq.terminates_ofList _
    have h_trans_eq : E_pre'.trans = Seq.ofList rest_prev :=
      Stream'.Seq.append_singleton_inj_left _ _
        h_Epre'_term h_prev_term _ _ h_trans
    -- So E_pre' = ⟨μ_0, ofList rest_prev⟩.
    apply h_ne
    cases E_pre' with
    | mk i t =>
      simp only at h_init h_trans_eq
      subst h_init
      subst h_trans_eq
      rfl
  -- Unfold `beliefStepCond`.
  unfold ProbabilisticExecution.beliefStepCond
  simp only
  split_ifs with h_step
  · -- Then-branch: `(normalize w).map (fun p => ⟨E_pre'.init, ... ++ [(l, p.2)]⟩)` at target.
    rw [PMF.map_apply]
    -- Goal: ∑' p, if (target) = ⟨E_pre'.init, ... ++ [(l, p.2)]⟩ then (normalize w) p else 0 = 0.
    apply ENNReal.tsum_eq_zero.mpr
    intro p
    have h_neq : ((⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩
        : AlterSeq (PMF State) Label) ≠
        ⟨E_pre'.init, E_pre'.trans.append (Seq.cons (l, p.2) Seq.nil)⟩) :=
      fun h => (h_mismatch p.2 h.symm)
    rw [if_neg h_neq]
  · -- Else-branch: PMF.pure at structural extension; the target equals it iff
    -- equality of the alterSeqs, which is excluded by h_mismatch on μ = PMF.pure q_new.
    rw [PMF.pure_apply]
    have h_neq : ((⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩
        : AlterSeq (PMF State) Label) ≠
        ⟨E_pre'.init, E_pre'.trans.append (Seq.cons (l, PMF.pure q_new) Seq.nil)⟩) :=
      fun h => (h_mismatch (PMF.pure q_new) h.symm)
    rw [if_neg h_neq]

/-- **H3 — `beliefStepCond` mass at the matched `E_pre'`, times its local
normalizer `zEpre`, equals `pe'.kernel · μ_new q_new`.** This is the heart of
the Bayes cancellation: the per-`E_pre` denominator inside `beliefStepCond`
cancels the `zEpre` reweighting from the outer `beliefRec` step. When
`zEpre = 0`, the kernel-times-marginal product is also zero (analogous to H1). -/
private lemma ProbabilisticExecution.belief_factor_step_inner
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (μ_0 : PMF State) (rest_prev : List (Label × PMF State))
    (l : Label) (μ_new : PMF State) (q_new : State) :
    (pe'.beliefStepCond ⟨μ_0, Seq.ofList rest_prev⟩ l q_new)
        ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ *
      (∑' ω : PMF (PMF State),
        pe'.scheduler.next ⟨μ_0, Seq.ofList rest_prev⟩ (some (l, ω)) *
        ∑' μ' : PMF State, ω μ' * μ' q_new)
    = pe'.kernel ⟨μ_0, Seq.ofList rest_prev⟩ (l, μ_new) * μ_new q_new := by
  classical
  set E_pre := (⟨μ_0, Seq.ofList rest_prev⟩ : AlterSeq (PMF State) Label) with hE_pre_def
  -- The right tsum is exactly `tsum w` for the joint weight `w` in beliefStepCond.
  set w : PMF (PMF State) × PMF State → ENNReal := fun p =>
    pe'.scheduler.next E_pre (some (l, p.1)) * p.1 p.2 * p.2 q_new with hw_def
  have h_tsum_w_eq : (∑' p : PMF (PMF State) × PMF State, w p)
      = ∑' ω : PMF (PMF State),
          pe'.scheduler.next E_pre (some (l, ω)) *
          ∑' μ' : PMF State, ω μ' * μ' q_new := by
    rw [ENNReal.tsum_prod']
    apply tsum_congr
    intro ω
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro μ'
    ring
  by_cases hZ : (∑' ω : PMF (PMF State),
        pe'.scheduler.next E_pre (some (l, ω)) *
        ∑' μ' : PMF State, ω μ' * μ' q_new) = 0
  · -- zEpre = 0: kernel · μ_new q_new = 0 (same argument as H1, on E_pre).
    rw [hZ, mul_zero]
    -- Show pe'.kernel E_pre (l, μ_new) * μ_new q_new = 0.
    have h_perω : ∀ ω : PMF (PMF State),
        pe'.scheduler.next E_pre (some (l, ω)) *
          ∑' μ' : PMF State, ω μ' * μ' q_new = 0 :=
      fun ω => ENNReal.tsum_eq_zero.mp hZ ω
    symm
    unfold ProbabilisticExecution.kernel
    rw [← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_eq_zero]
    intro ω
    by_cases h_sch : pe'.scheduler.next E_pre (some (l, ω)) = 0
    · rw [h_sch, zero_mul, zero_mul]
    have h_inner : (∑' μ' : PMF State, ω μ' * μ' q_new) = 0 := by
      rcases mul_eq_zero.mp (h_perω ω) with h | h
      · exact absurd h h_sch
      · exact h
    have h_at_μnew : ω μ_new * μ_new q_new = 0 :=
      ENNReal.tsum_eq_zero.mp h_inner μ_new
    rw [mul_assoc, h_at_μnew, mul_zero]
  · -- zEpre ≠ 0: beliefStepCond goes through `normalize w` then-branch.
    -- Establish the tsum_w hypotheses.
    have h_tsum_w_ne : (∑' p : PMF (PMF State) × PMF State, w p) ≠ 0 := by
      rw [h_tsum_w_eq]; exact hZ
    have h_tsum_w_top : (∑' p : PMF (PMF State) × PMF State, w p) ≠ ⊤ := by
      apply ne_of_lt
      calc (∑' p : PMF (PMF State) × PMF State, w p)
          ≤ 1 := by
            rw [ENNReal.tsum_prod']
            calc (∑' ω : PMF (PMF State), ∑' μ' : PMF State, w (ω, μ'))
                ≤ ∑' ω : PMF (PMF State),
                      pe'.scheduler.next E_pre (some (l, ω)) := by
                  apply ENNReal.tsum_le_tsum
                  intro ω
                  calc (∑' μ' : PMF State,
                        pe'.scheduler.next E_pre (some (l, ω)) * ω μ' * μ' q_new)
                      ≤ ∑' μ' : PMF State,
                            pe'.scheduler.next E_pre (some (l, ω)) * ω μ' := by
                        apply ENNReal.tsum_le_tsum
                        intro μ'
                        exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
                    _ = pe'.scheduler.next E_pre (some (l, ω)) *
                          ∑' μ' : PMF State, ω μ' := by
                        rw [ENNReal.tsum_mul_left]
                    _ = pe'.scheduler.next E_pre (some (l, ω)) * 1 := by rw [ω.tsum_coe]
                    _ = pe'.scheduler.next E_pre (some (l, ω)) := by ring
              _ ≤ ∑' (lω : Label × PMF (PMF State)),
                    pe'.scheduler.next E_pre (some lω) := by
                  exact ENNReal.tsum_comp_le_tsum_of_injective
                    (f := fun ω => (l, ω))
                    (fun _ _ h => (Prod.mk.inj h).2) _
              _ ≤ ∑' opt, pe'.scheduler.next E_pre opt := by
                  exact ENNReal.tsum_comp_le_tsum_of_injective
                    (f := some) (fun _ _ h => Option.some.inj h) _
              _ = 1 := (pe'.scheduler.next E_pre).tsum_coe
        _ < ⊤ := ENNReal.one_lt_top
    -- Unfold beliefStepCond.
    have h_step :
        (pe'.beliefStepCond E_pre l q_new)
          ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩
        = ((PMF.normalize w h_tsum_w_ne h_tsum_w_top).map (fun p =>
            (⟨E_pre.init, E_pre.trans.append (Seq.cons (l, p.2) Seq.nil)⟩
              : AlterSeq (PMF State) Label)))
            ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ := by
      change (open Classical in
        if h0 : (∑' p : PMF (PMF State) × PMF State, w p) ≠ 0 then
          (PMF.normalize w h0 (by
            apply ne_of_lt; exact lt_of_le_of_lt
              (by rw [ENNReal.tsum_prod']
                  calc (∑' ω : PMF (PMF State), ∑' μ' : PMF State, w (ω, μ'))
                      ≤ ∑' ω : PMF (PMF State),
                            pe'.scheduler.next E_pre (some (l, ω)) := by
                        apply ENNReal.tsum_le_tsum
                        intro ω
                        calc (∑' μ' : PMF State,
                              pe'.scheduler.next E_pre (some (l, ω)) * ω μ' * μ' q_new)
                            ≤ ∑' μ' : PMF State,
                                  pe'.scheduler.next E_pre (some (l, ω)) * ω μ' := by
                              apply ENNReal.tsum_le_tsum
                              intro μ'
                              exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
                          _ = pe'.scheduler.next E_pre (some (l, ω)) *
                                ∑' μ' : PMF State, ω μ' := by rw [ENNReal.tsum_mul_left]
                          _ = pe'.scheduler.next E_pre (some (l, ω)) * 1 := by rw [ω.tsum_coe]
                          _ = pe'.scheduler.next E_pre (some (l, ω)) := by ring
                    _ ≤ ∑' (lω : Label × PMF (PMF State)),
                          pe'.scheduler.next E_pre (some lω) := by
                        exact ENNReal.tsum_comp_le_tsum_of_injective
                          (f := fun ω => (l, ω))
                          (fun _ _ h => (Prod.mk.inj h).2) _
                    _ ≤ ∑' opt, pe'.scheduler.next E_pre opt := by
                        exact ENNReal.tsum_comp_le_tsum_of_injective
                          (f := some) (fun _ _ h => Option.some.inj h) _
                    _ = 1 := (pe'.scheduler.next E_pre).tsum_coe)
              ENNReal.one_lt_top)).map (fun p =>
            (⟨E_pre.init, E_pre.trans.append (Seq.cons (l, p.2) Seq.nil)⟩
              : AlterSeq (PMF State) Label))
        else
          PMF.pure ⟨E_pre.init, E_pre.trans.append (Seq.cons (l, PMF.pure q_new) Seq.nil)⟩)
        ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ = _
      rw [dif_pos h_tsum_w_ne]
    rw [h_step]
    rw [PMF.map_apply]
    -- Now goal: (∑' p, if target = ⟨μ_0, ... ++ [(l, p.2)]⟩ then normalize_w p
    -- else 0) · tsum_w = kernel · μ_new q_new.
    -- Show the if-condition is equivalent to p.2 = μ_new (under append_singleton_inj_right).
    have h_iff : ∀ p : PMF (PMF State) × PMF State,
        ((⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩
          : AlterSeq (PMF State) Label) =
          ⟨E_pre.init, E_pre.trans.append (Seq.cons (l, p.2) Seq.nil)⟩) ↔ p.2 = μ_new := by
      intro p
      constructor
      · intro h_eq
        -- E_pre.init = μ_0; E_pre.trans = ofList rest_prev.
        -- Extract trans-equality and use append_singleton_inj_right.
        have h_trans : (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)
            = E_pre.trans.append (Seq.cons (l, p.2) Seq.nil) :=
          congr_arg AlterSeq.trans h_eq
        have h_prev_term : (Seq.ofList rest_prev).Terminates :=
          Stream'.Seq.terminates_ofList _
        have h_pair_eq : (l, μ_new) = (l, p.2) :=
          Stream'.Seq.append_singleton_inj_right _ _
            h_prev_term h_prev_term _ _ h_trans
        exact (Prod.mk.inj h_pair_eq).2.symm
      · intro h_p2
        -- p.2 = μ_new: rebuild the equality.
        rw [h_p2]
    -- Rewrite using h_iff and reduce sum.
    rw [show
      (∑' p : PMF (PMF State) × PMF State,
          if (⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩
              : AlterSeq (PMF State) Label) =
              ⟨E_pre.init, E_pre.trans.append (Seq.cons (l, p.2) Seq.nil)⟩ then
            (PMF.normalize w h_tsum_w_ne h_tsum_w_top) p
          else 0)
      = ∑' p : PMF (PMF State) × PMF State,
          if p.2 = μ_new then (PMF.normalize w h_tsum_w_ne h_tsum_w_top) p else 0 from by
      apply tsum_congr
      intro p
      by_cases h_p2 : p.2 = μ_new
      · rw [if_pos ((h_iff p).mpr h_p2), if_pos h_p2]
      · rw [if_neg (fun h => h_p2 ((h_iff p).mp h)), if_neg h_p2]]
    -- Now reduce to a single sum over ω.
    rw [ENNReal.tsum_prod']
    rw [show
      (∑' (ω : PMF (PMF State)) (μ' : PMF State),
          if (ω, μ').2 = μ_new then (PMF.normalize w h_tsum_w_ne h_tsum_w_top) (ω, μ') else 0)
      = ∑' ω : PMF (PMF State), (PMF.normalize w h_tsum_w_ne h_tsum_w_top) (ω, μ_new) from by
      apply tsum_congr
      intro ω
      rw [tsum_eq_single μ_new]
      · simp
      · intro μ' h_ne
        rw [if_neg h_ne]]
    -- Now: (∑' ω, normalize w (ω, μ_new)) · tsum_w = kernel · μ_new q_new.
    -- Apply PMF.normalize_apply.
    rw [show (∑' ω : PMF (PMF State), (PMF.normalize w h_tsum_w_ne h_tsum_w_top) (ω, μ_new))
      = ∑' ω : PMF (PMF State), w (ω, μ_new) * (∑' p, w p)⁻¹ from by
      apply tsum_congr
      intro ω
      exact PMF.normalize_apply h_tsum_w_ne h_tsum_w_top _]
    rw [ENNReal.tsum_mul_right]
    -- Goal: (∑' ω, w (ω, μ_new)) · tsum_w⁻¹ · tsum_w_RHS_form = pe'.kernel · μ_new q_new.
    -- Use h_tsum_w_eq to identify the RHS form as the actual tsum_w.
    rw [← h_tsum_w_eq]
    rw [mul_assoc]
    rw [ENNReal.inv_mul_cancel h_tsum_w_ne h_tsum_w_top, mul_one]
    -- Goal: ∑' ω, w (ω, μ_new) = pe'.kernel · μ_new q_new.
    unfold ProbabilisticExecution.kernel
    -- pe'.kernel E_pre (l, μ_new) = ∑' μ', sched.next E_pre (some (l, μ')) * μ' μ_new.
    rw [← ENNReal.tsum_mul_right]

/-- **Sub-lemma 1 — Belief factorization at cons-end (multiplicative form).**

```
belief (e'_pre ∙ (l, q_new)) (E_pre ∙ (l, μ_new)) · Z_global(e'_pre, l, q_new)
  = belief e'_pre E_pre · pe'.kernel E_pre (l, μ_new) · μ_new q_new
```

**Why multiplicative**: the quotient form `LHS = RHS / Z_global` fails in the
degenerate corner where `Z_global = 0` and `E_full` happens to equal the Dirac
lift of the extended sys-history — there `LHS = 1` but quotient gives `0/0 = 0`.
The multiplicative form handles this universally: when `Z_global = 0`, the LHS
becomes `belief · 0 = 0`, and on the RHS either `belief e'_pre E_pre = 0` or
`μ_new q_new = 0` (forced by `Z_global = 0` together with `pe'.kernel > 0`).

Non-degenerate case: standard unfolding `belief` → `beliefRec` →
`List.reverseRecOn` cons-end step, then `PMF.bind_apply` + `PMF.normalize_apply`
+ `PMF.map_apply` on the `(reweighted-normalize).bind beliefStepCond` structure.
The `zEpre(E_pre)` factor between the reweighted prior and `beliefStepCond`'s
denominator cancels exactly. -/
private theorem ProbabilisticExecution.belief_factor_step
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (μ_0 : PMF State) (rest_prev : List (Label × PMF State))
    (l : Label) (μ_new : PMF State) (q_new : State)
    (e'_pre : AlterSeq State Label) (h_e'_pre_term : e'_pre.trans.Terminates) :
    pe'.belief ⟨e'_pre.init, e'_pre.trans.append (Seq.cons (l, q_new) Seq.nil)⟩
        ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ *
      pe'.Z_global e'_pre l q_new
    = pe'.belief e'_pre ⟨μ_0, Seq.ofList rest_prev⟩ *
      pe'.kernel ⟨μ_0, Seq.ofList rest_prev⟩ (l, μ_new) *
      μ_new q_new := by
  classical
  -- Case split on Z_global = 0.
  by_cases hZ : pe'.Z_global e'_pre l q_new = 0
  · -- Degenerate corner: LHS = ? * 0 = 0; RHS = 0 by H1.
    rw [hZ, mul_zero]
    exact (ProbabilisticExecution.belief_factor_step_rhs_zero_of_Z_global_zero
      pe' μ_0 rest_prev l μ_new q_new e'_pre hZ).symm
  · -- Non-degenerate case: Z_global ≠ 0.
    -- Step 1: Termination of the extended sys-history.
    have h_singleton_term : (Seq.cons (l, q_new) Seq.nil : Seq (Label × State)).Terminates :=
      Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
    have h_ext_term : (e'_pre.trans.append (Seq.cons (l, q_new) Seq.nil)).Terminates :=
      ⟨_, Stream'.Seq.terminatedAt_append_find h_e'_pre_term h_singleton_term.choose_spec⟩
    -- Step 2: Unfold `belief` on LHS to `beliefRec`.
    have h_belief_LHS :
        pe'.belief ⟨e'_pre.init, e'_pre.trans.append (Seq.cons (l, q_new) Seq.nil)⟩
            ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩
        = (pe'.beliefRec e'_pre.init
            ((e'_pre.trans.append (Seq.cons (l, q_new) Seq.nil)).toList h_ext_term))
            ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ := by
      change (open Classical in
        if hT : (e'_pre.trans.append (Seq.cons (l, q_new) Seq.nil)).Terminates then
          pe'.beliefRec e'_pre.init
            ((e'_pre.trans.append (Seq.cons (l, q_new) Seq.nil)).toList hT)
        else
          beliefDefault _) _ = _
      rw [dif_pos h_ext_term]
    rw [h_belief_LHS]
    -- Step 3: toList of the append = e'_pre.trans.toList ++ [(l, q_new)].
    have h_singleton_toList :
        (Seq.cons (l, q_new) Seq.nil : Seq (Label × State)).toList h_singleton_term
          = [(l, q_new)] := by
      rw [Stream'.Seq.toList_cons h_singleton_term]
      congr 1
      exact Stream'.Seq.toList_nil
    have h_toList_eq :
        (e'_pre.trans.append (Seq.cons (l, q_new) Seq.nil)).toList h_ext_term
          = e'_pre.trans.toList h_e'_pre_term ++ [(l, q_new)] := by
      rw [Stream'.Seq.toList_append e'_pre.trans (Seq.cons (l, q_new) Seq.nil)
        h_e'_pre_term h_singleton_term h_ext_term]
      rw [h_singleton_toList]
    rw [h_toList_eq]
    -- Step 4: Unfold `beliefRec` at the concatenation. Use `List.reverseRecOn_concat`.
    set rest_internal := e'_pre.trans.toList h_e'_pre_term with h_rest_int_def
    -- Define the components used in the cons-end step.
    set ih_pmf := pe'.beliefRec e'_pre.init rest_internal with h_ih_def
    -- The per-E_pre marginal-likelihood weight.
    set zEpre : AlterSeq (PMF State) Label → ENNReal := fun E_pre =>
      ∑' ω : PMF (PMF State),
        pe'.scheduler.next E_pre (some (l, ω)) *
        ∑' μ' : PMF State, ω μ' * μ' q_new with h_zEpre_def
    set reweighted : AlterSeq (PMF State) Label → ENNReal :=
      fun E_pre => ih_pmf E_pre * zEpre E_pre with h_reweighted_def
    -- Recognize: tsum reweighted = Z_global e'_pre l q_new.
    have h_ih_eq_belief : ih_pmf = pe'.belief e'_pre := by
      -- belief e'_pre = beliefRec e'_pre.init (e'_pre.trans.toList h_e'_pre_term)
      change pe'.beliefRec e'_pre.init rest_internal = pe'.belief e'_pre
      change _ = (open Classical in
        if hT : e'_pre.trans.Terminates then
          pe'.beliefRec e'_pre.init (e'_pre.trans.toList hT)
        else
          beliefDefault e'_pre)
      rw [dif_pos h_e'_pre_term]
    have h_tsum_eq_Z : (∑' E_pre, reweighted E_pre) = pe'.Z_global e'_pre l q_new := by
      change (∑' E_pre, ih_pmf E_pre * zEpre E_pre) = _
      rw [h_ih_eq_belief]
      -- pe'.Z_global e'_pre l q_new = ∑' E, belief e'_pre E *
      --   ∑' ω, sched.next E (some (l,ω)) * (ω.bind id) q_new
      -- = ∑' E, belief e'_pre E * zEpre E.
      change _ = ∑' E_pre, pe'.belief e'_pre E_pre *
          ∑' ω : PMF (PMF State),
            pe'.scheduler.next E_pre (some (l, ω)) * (ω.bind id) q_new
      apply tsum_congr
      intro E_pre
      congr 1
    -- Z_global ≠ 0 → tsum reweighted ≠ 0.
    have h0 : (∑' E_pre, reweighted E_pre) ≠ 0 := by
      rw [h_tsum_eq_Z]; exact hZ
    -- We need to identify beliefRec at (rest_internal ++ [(l, q_new)]).
    -- The strategy mirrors beliefRec_support_compat (line 1097+): introduce the
    -- huge `let`-based unfolding equality.
    have h_zEpre_le_one : ∀ E_pre, zEpre E_pre ≤ 1 := fun E_pre => by
      change (∑' ω : PMF (PMF State),
          pe'.scheduler.next E_pre (some (l, ω)) *
          ∑' μ' : PMF State, ω μ' * μ' q_new) ≤ 1
      calc (∑' ω : PMF (PMF State),
            pe'.scheduler.next E_pre (some (l, ω)) *
            ∑' μ' : PMF State, ω μ' * μ' q_new)
          ≤ ∑' ω : PMF (PMF State),
                pe'.scheduler.next E_pre (some (l, ω)) := by
            apply ENNReal.tsum_le_tsum
            intro ω
            refine mul_le_of_le_one_right' ?_
            calc (∑' μ' : PMF State, ω μ' * μ' q_new)
                ≤ ∑' μ' : PMF State, ω μ' := by
                  apply ENNReal.tsum_le_tsum
                  intro μ'
                  exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
              _ = 1 := ω.tsum_coe
        _ ≤ ∑' lω : Label × PMF (PMF State),
              pe'.scheduler.next E_pre (some lω) := by
            exact ENNReal.tsum_comp_le_tsum_of_injective
              (f := fun ω => (l, ω))
              (fun _ _ h => (Prod.mk.inj h).2) _
        _ ≤ ∑' opt, pe'.scheduler.next E_pre opt := by
            exact ENNReal.tsum_comp_le_tsum_of_injective
              (f := some) (fun _ _ h => Option.some.inj h) _
        _ = 1 := (pe'.scheduler.next E_pre).tsum_coe
    have h_top : (∑' E_pre, reweighted E_pre) ≠ ⊤ := by
      apply ne_of_lt
      calc (∑' E_pre, reweighted E_pre)
          ≤ ∑' E_pre, ih_pmf E_pre := by
            apply ENNReal.tsum_le_tsum
            intro E_pre
            exact mul_le_of_le_one_right' (h_zEpre_le_one E_pre)
        _ = 1 := ih_pmf.tsum_coe
        _ < ⊤ := ENNReal.one_lt_top
    -- Now we identify beliefRec via the unfold.
    have h_unfold :
        pe'.beliefRec e'_pre.init (rest_internal ++ [(l, q_new)])
        = ((PMF.normalize reweighted h0 h_top).bind
            (fun E_pre => pe'.beliefStepCond E_pre l q_new)) := by
      -- Mirror the unfold-pattern from beliefRec_support_compat.
      have h_full : pe'.beliefRec e'_pre.init (rest_internal ++ [(l, q_new)]) =
          (let l' := ((l, q_new) : Label × State).1
           let s' := ((l, q_new) : Label × State).2
           let ih_pmf' := pe'.beliefRec e'_pre.init rest_internal
           let zEpre' : AlterSeq (PMF State) Label → ENNReal := fun E_pre =>
             ∑' ω : PMF (PMF State),
               pe'.scheduler.next E_pre (some (l', ω)) *
               ∑' μ_new : PMF State, ω μ_new * μ_new s'
           let reweighted' : AlterSeq (PMF State) Label → ENNReal := fun E_pre =>
             ih_pmf' E_pre * zEpre' E_pre
           open Classical in
           if h0' : (∑' E_pre, reweighted' E_pre) ≠ 0 then
             have h_top' : (∑' E_pre, reweighted' E_pre) ≠ ⊤ := by
               apply ne_of_lt
               calc (∑' E_pre, reweighted' E_pre)
                   ≤ ∑' E_pre, ih_pmf' E_pre := by
                     apply ENNReal.tsum_le_tsum
                     intro E_pre
                     refine mul_le_of_le_one_right' ?_
                     change (∑' ω : PMF (PMF State),
                         pe'.scheduler.next E_pre (some (l', ω)) *
                         ∑' μ_new : PMF State, ω μ_new * μ_new s') ≤ 1
                     calc (∑' ω : PMF (PMF State),
                           pe'.scheduler.next E_pre (some (l', ω)) *
                           ∑' μ_new : PMF State, ω μ_new * μ_new s')
                         ≤ ∑' ω : PMF (PMF State),
                             pe'.scheduler.next E_pre (some (l', ω)) := by
                           apply ENNReal.tsum_le_tsum
                           intro ω
                           refine mul_le_of_le_one_right' ?_
                           calc (∑' μ_new : PMF State, ω μ_new * μ_new s')
                               ≤ ∑' μ_new : PMF State, ω μ_new := by
                                 apply ENNReal.tsum_le_tsum
                                 intro μ_new
                                 exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
                             _ = 1 := ω.tsum_coe
                       _ ≤ ∑' lω : Label × PMF (PMF State),
                             pe'.scheduler.next E_pre (some lω) := by
                           exact ENNReal.tsum_comp_le_tsum_of_injective
                             (f := fun ω => (l', ω))
                             (fun _ _ h => (Prod.mk.inj h).2) _
                       _ ≤ ∑' opt, pe'.scheduler.next E_pre opt := by
                           exact ENNReal.tsum_comp_le_tsum_of_injective
                             (f := some) (fun _ _ h => Option.some.inj h) _
                       _ = 1 := (pe'.scheduler.next E_pre).tsum_coe
                 _ = 1 := ih_pmf'.tsum_coe
                 _ < ⊤ := ENNReal.one_lt_top
             (PMF.normalize reweighted' h0' h_top').bind (fun E_pre =>
               pe'.beliefStepCond E_pre l' s')
           else
             beliefDefault ⟨e'_pre.init, Seq.ofList (rest_internal ++ [(l, q_new)])⟩) := by
        unfold ProbabilisticExecution.beliefRec
        rw [List.reverseRecOn_concat]
      rw [h_full]
      simp only
      rw [dif_pos h0]
    rw [h_unfold]
    -- Now compute the mass at the target.
    rw [PMF.bind_apply]
    -- Goal: ∑' E_pre, normalize_reweighted E_pre · beliefStepCond E_pre l q_new (target) = ...
    -- Use H2 to collapse the sum to E_pre = ⟨μ_0, ofList rest_prev⟩.
    have h_collapse :
        (∑' E_pre, (PMF.normalize reweighted h0 h_top) E_pre *
            (pe'.beliefStepCond E_pre l q_new)
              ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩)
        = (PMF.normalize reweighted h0 h_top) ⟨μ_0, Seq.ofList rest_prev⟩ *
            (pe'.beliefStepCond ⟨μ_0, Seq.ofList rest_prev⟩ l q_new)
              ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ := by
      apply tsum_eq_single
      intro E_pre' h_ne
      rw [pe'.belief_factor_step_bind_collapse μ_0 rest_prev l μ_new q_new E_pre' h_ne,
          mul_zero]
    rw [h_collapse]
    -- Step: multiply by Z_global = tsum reweighted; recognize normalize_apply pattern.
    rw [← h_tsum_eq_Z]
    -- Goal: (normalize r) ⟨μ_0,_⟩ · beliefStepCond _ target · tsum_r = RHS.
    rw [PMF.normalize_apply h0 h_top]
    -- Goal: r ⟨μ_0,_⟩ · (tsum r)⁻¹ · beliefStepCond _ target · tsum_r = RHS.
    -- Identify r ⟨μ_0,_⟩ as belief e'_pre · zEpre and split.
    change reweighted ⟨μ_0, Seq.ofList rest_prev⟩ * (∑' E, reweighted E)⁻¹ *
      (pe'.beliefStepCond ⟨μ_0, Seq.ofList rest_prev⟩ l q_new)
        ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ *
      (∑' E_pre, reweighted E_pre) = _
    -- Reassociate so that the two tsum factors meet and cancel.
    have h_inv_cancel : (∑' E, reweighted E)⁻¹ * (∑' E_pre, reweighted E_pre) = 1 :=
      ENNReal.inv_mul_cancel h0 h_top
    calc reweighted ⟨μ_0, Seq.ofList rest_prev⟩ * (∑' E, reweighted E)⁻¹ *
            (pe'.beliefStepCond ⟨μ_0, Seq.ofList rest_prev⟩ l q_new)
              ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ *
          (∑' E_pre, reweighted E_pre)
        = reweighted ⟨μ_0, Seq.ofList rest_prev⟩ *
            ((∑' E, reweighted E)⁻¹ * (∑' E_pre, reweighted E_pre)) *
            (pe'.beliefStepCond ⟨μ_0, Seq.ofList rest_prev⟩ l q_new)
              ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ := by
            ring
      _ = reweighted ⟨μ_0, Seq.ofList rest_prev⟩ *
            (pe'.beliefStepCond ⟨μ_0, Seq.ofList rest_prev⟩ l q_new)
              ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ := by
            rw [h_inv_cancel, mul_one]
      _ = ih_pmf ⟨μ_0, Seq.ofList rest_prev⟩ * zEpre ⟨μ_0, Seq.ofList rest_prev⟩ *
            (pe'.beliefStepCond ⟨μ_0, Seq.ofList rest_prev⟩ l q_new)
              ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ := rfl
      _ = ih_pmf ⟨μ_0, Seq.ofList rest_prev⟩ *
            ((pe'.beliefStepCond ⟨μ_0, Seq.ofList rest_prev⟩ l q_new)
              ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ *
            zEpre ⟨μ_0, Seq.ofList rest_prev⟩) := by ring
      _ = ih_pmf ⟨μ_0, Seq.ofList rest_prev⟩ *
            (pe'.kernel ⟨μ_0, Seq.ofList rest_prev⟩ (l, μ_new) * μ_new q_new) := by
            rw [pe'.belief_factor_step_inner μ_0 rest_prev l μ_new q_new]
      _ = pe'.belief e'_pre ⟨μ_0, Seq.ofList rest_prev⟩ *
            pe'.kernel ⟨μ_0, Seq.ofList rest_prev⟩ (l, μ_new) * μ_new q_new := by
            rw [h_ih_eq_belief]; ring


/-- **Helper: `ofDist.kernel` vanishes where `Z_global` does.**

When the user's joint predicts probability 0 for the next sys-state `q_new`
(i.e. `Z_global e'_pre l q_new = 0`), the constructed `ofDist` scheduler's
kernel also gives 0. This is the consistency property that makes the
construction's degenerate cases harmless in `belief_bayes_inversion_step`'s
sum.

Proof sketch: `Z_global = ∑'_E belief e'_pre E · ZZ(E, l, q_new) = 0` forces
`ZZ(E, l, q_new) = 0` for every `E` with `belief e'_pre E ≠ 0`. The
hyperStep marginal identity expands
`ZZ(E, l, q_new) = ∑_s E.endState(s) · (distHyperKernel _ _ _ s).bind id (q_new)`.
By `belief_support_compat`, `e'_pre.endState ∈ E.endState.support`, so the
`s = e'_pre.endState` summand is forced to 0, giving
`(distHyperKernel … e'_pre.endState).bind id (q_new) = 0`. Summing over
`(E, ω)` in `ofDist.kernel`'s definition then yields 0. -/
private theorem ProbabilisticExecution.ofDist_kernel_eq_zero_of_Z_global_eq_zero
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (e'_pre : AlterSeq State Label) (h_e'_pre_term : e'_pre.trans.Terminates)
    (l : Label) (q_new : State)
    (hZ : pe'.Z_global e'_pre l q_new = 0) :
    pe'.ofDist.kernel e'_pre (l, q_new) = 0 := by
  classical
  -- From hZ, every per-E summand is zero.
  have h_perE : ∀ E : AlterSeq (PMF State) Label,
      pe'.belief e'_pre E *
        (∑' (ω : PMF (PMF State)),
          pe'.scheduler.next E (some (l, ω)) * (ω.bind id) q_new) = 0 := by
    intro E
    have : (∑' (E : AlterSeq (PMF State) Label),
        pe'.belief e'_pre E *
          ∑' (ω : PMF (PMF State)),
            pe'.scheduler.next E (some (l, ω)) * (ω.bind id) q_new) = 0 := hZ
    exact ENNReal.tsum_eq_zero.mp this E
  -- Unfold `ofDist.kernel` and `Scheduler.ofDist.next` at `e'_pre`.
  unfold ProbabilisticExecution.kernel
  -- Goal: ∑' μ', pe'.ofDist.scheduler.next e'_pre (some (l, μ')) * μ' q_new = 0
  rw [ENNReal.tsum_eq_zero]
  intro μ'
  -- Reduce `pe'.ofDist.scheduler.next` via the `dif_pos`.
  change pe'.ofDist.scheduler.next e'_pre (some (l, μ')) * μ' q_new = 0
  have h_sch_eq : pe'.ofDist.scheduler.next e'_pre (some (l, μ'))
      = ((pe'.belief e'_pre).bind (fun E =>
          (pe'.scheduler.next E).bind (fun opt =>
            match opt with
            | none => PMF.pure none
            | some (l', ω) =>
                (pe'.distHyperKernel E l' ω (e'_pre.endState h_e'_pre_term)).map
                  (fun μ'' => some (l', μ''))))) (some (l, μ')) := by
    change (open Classical in
      if h_term : e'_pre.trans.Terminates then
        (pe'.belief e'_pre).bind (fun E =>
          (pe'.scheduler.next E).bind (fun opt =>
            match opt with
            | none => PMF.pure none
            | some (l', ω) =>
                (pe'.distHyperKernel E l' ω (e'_pre.endState h_term)).map
                  (fun μ'' => some (l', μ''))))
      else
        PMF.pure none) (some (l, μ')) = _
    rw [dif_pos h_e'_pre_term]
  rw [h_sch_eq]
  rw [PMF.bind_apply]
  -- Goal: (∑' E, belief e'_pre E *
  --  ((scheduler.next E).bind (fun opt => ...)) (some (l, μ'))) * μ' q_new = 0
  -- Push μ' q_new in.
  rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_eq_zero]
  intro E
  -- Goal: belief e'_pre E * (bind result evaluated) * μ' q_new = 0
  by_cases h_belief : pe'.belief e'_pre E = 0
  · rw [h_belief, zero_mul, zero_mul]
  -- belief ≠ 0, so per-E inner sum is 0.
  have h_inner_zero :
      (∑' (ω : PMF (PMF State)),
          pe'.scheduler.next E (some (l, ω)) * (ω.bind id) q_new) = 0 := by
    have := h_perE E
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h_belief
    · exact h
  have h_perω : ∀ ω : PMF (PMF State),
      pe'.scheduler.next E (some (l, ω)) * (ω.bind id) q_new = 0 :=
    fun ω => ENNReal.tsum_eq_zero.mp h_inner_zero ω
  -- belief_support_compat gives hE_term and e'_pre.endState ∈ E.endState support.
  have h_belief_supp : E ∈ (pe'.belief e'_pre).support :=
    (PMF.mem_support_iff _ _).mpr h_belief
  obtain ⟨hE_term, _h_init, _h_lab, h_end, _h_compat⟩ :=
    pe'.belief_support_compat h_e'_pre_term h_belief_supp
  -- Unfold inner bind at some (l, μ').
  rw [PMF.bind_apply]
  -- Goal: (belief * (∑'opt, sched_E opt * match_PMF_at(some(l,μ')))) * μ' q_new = 0.
  -- belief ≠ 0; multiply through.
  rw [mul_assoc, mul_eq_zero]; right
  rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_eq_zero]
  intro opt
  cases opt with
  | none =>
    change pe'.scheduler.next E none *
        (PMF.pure (α := Option (Label × PMF State)) none) (some (l, μ')) * μ' q_new = 0
    simp [PMF.pure_apply]
  | some lω =>
    obtain ⟨l', ω⟩ := lω
    by_cases h_lab_eq : l' = l
    · rw [h_lab_eq]
      -- map at some (l, μ') reduces to distHyperKernel _ μ'.
      have h_map_eval :
          ((pe'.distHyperKernel E l ω (e'_pre.endState h_e'_pre_term)).map
            (fun μ'' => some (l, μ''))) (some (l, μ'))
          = pe'.distHyperKernel E l ω (e'_pre.endState h_e'_pre_term) μ' := by
        rw [PMF.map_apply]
        rw [tsum_eq_single μ']
        · simp
        · intro μ'' h_ne
          have h_neq : (some (l, μ') : Option (Label × PMF State)) ≠ some (l, μ'') := by
            intro h; apply h_ne; injection h with h1; exact ((Prod.mk.inj h1).2).symm
          rw [if_neg h_neq]
      change pe'.scheduler.next E (some (l, ω)) *
          ((pe'.distHyperKernel E l ω (e'_pre.endState h_e'_pre_term)).map
            (fun μ'' => some (l, μ''))) (some (l, μ')) * μ' q_new = 0
      rw [h_map_eval]
      -- Goal: scheduler.next E (some (l, ω)) * distHyperKernel _ μ' * μ' q_new = 0.
      by_cases h_sch : pe'.scheduler.next E (some (l, ω)) = 0
      · rw [h_sch, zero_mul, zero_mul]
      -- scheduler.next ≠ 0; from h_perω, (ω.bind id) q_new = 0.
      have h_omega_bind_zero : (ω.bind id) q_new = 0 := by
        rcases mul_eq_zero.mp (h_perω ω) with h | h
        · exact absurd h h_sch
        · exact h
      -- hyperStep at E.
      have h_supp_sch : some (l, ω) ∈ (pe'.scheduler.next E).support :=
        (PMF.mem_support_iff _ _).mpr h_sch
      have h_hyper : hyperStep sys (E.endState hE_term) l (ω.bind id) := by
        have := pe'.scheduler.valid E (Nat.find hE_term) (E.endState hE_term)
          (Nat.find_spec hE_term) (AlterSeq.stateAt_find_eq_endState E hE_term) l ω h_supp_sch
        change hyperStep sys (E.endState hE_term) l (ω.bind id) at this
        exact this
      -- distHyperKernel = hex.choose_spec.kernel.
      have hex : ∃ hE' : E.trans.Terminates,
          hyperStep sys (E.endState hE') l (ω.bind id) := ⟨hE_term, h_hyper⟩
      have h_def : pe'.distHyperKernel E l ω = hex.choose_spec.kernel := by
        unfold ProbabilisticExecution.distHyperKernel
        rw [dif_pos hex]
      rw [h_def]
      -- Use post_eq_bind: ω.bind id = E.endState.bind (kernel.bind id).
      have h_post := hex.choose_spec.post_eq_bind
      have h_choose_eq : hex.choose = hE_term := Subsingleton.elim _ _
      have h_bind_q : (ω.bind id) q_new
          = ∑' s, (E.endState hex.choose) s * ((hex.choose_spec.kernel s).bind id) q_new := by
        conv_lhs => rw [h_post]
        rw [PMF.bind_apply]
      rw [h_bind_q] at h_omega_bind_zero
      have h_term_s :
        ∀ s, (E.endState hex.choose) s * ((hex.choose_spec.kernel s).bind id) q_new = 0 :=
        fun s => ENNReal.tsum_eq_zero.mp h_omega_bind_zero s
      have h_at_e := h_term_s (e'_pre.endState h_e'_pre_term)
      have h_E_end_ne : (E.endState hex.choose) (e'_pre.endState h_e'_pre_term) ≠ 0 := by
        rw [h_choose_eq]
        exact (PMF.mem_support_iff _ _).mp h_end
      have h_kernel_bind_q :
          ((hex.choose_spec.kernel (e'_pre.endState h_e'_pre_term)).bind id) q_new = 0 := by
        rcases mul_eq_zero.mp h_at_e with h | h
        · exact absurd h h_E_end_ne
        · exact h
      have h_bind_q' : ((hex.choose_spec.kernel (e'_pre.endState h_e'_pre_term)).bind id) q_new
          = ∑' ν, hex.choose_spec.kernel (e'_pre.endState h_e'_pre_term) ν * ν q_new := by
        rw [PMF.bind_apply]
        rfl
      rw [h_bind_q'] at h_kernel_bind_q
      have h_zero : hex.choose_spec.kernel (e'_pre.endState h_e'_pre_term) μ' * μ' q_new = 0 :=
        ENNReal.tsum_eq_zero.mp h_kernel_bind_q μ'
      rw [mul_assoc, h_zero, mul_zero]
    · -- l' ≠ l: map at (some (l, μ')) is 0.
      have h_map_eval :
          ((pe'.distHyperKernel E l' ω (e'_pre.endState h_e'_pre_term)).map
            (fun μ'' => some (l', μ''))) (some (l, μ')) = 0 := by
        rw [PMF.map_apply]
        rw [ENNReal.tsum_eq_zero]
        intro μ''
        have h_neq : (some (l, μ') : Option (Label × PMF State)) ≠ some (l', μ'') := by
          intro h; apply h_lab_eq; injection h with h1; exact ((Prod.mk.inj h1).1).symm
        rw [if_neg h_neq]
      change pe'.scheduler.next E (some (l', ω)) *
          ((pe'.distHyperKernel E l' ω (e'_pre.endState h_e'_pre_term)).map
            (fun μ'' => some (l', μ''))) (some (l, μ')) * μ' q_new = 0
      rw [h_map_eval, mul_zero, zero_mul]

/-- **Sub-lemma 2 — `ofDist.probOf` factorization at cons-end.** Direct from
`ProbabilisticExecution.probOf_append_singleton`. -/
private theorem ProbabilisticExecution.ofDist_probOf_factor_step
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (e'_pre : AlterSeq State Label) (h_e'_pre_term : e'_pre.trans.Terminates)
    (l : Label) (q_new : State)
    (h_app : (e'_pre.trans.append (Seq.cons (l, q_new) Seq.nil)).Terminates) :
    pe'.ofDist.probOf
        ⟨e'_pre.init, e'_pre.trans.append (Seq.cons (l, q_new) Seq.nil)⟩ h_app
    = pe'.ofDist.probOf e'_pre h_e'_pre_term *
      pe'.ofDist.kernel e'_pre (l, q_new) := by
  -- Direct application of `probOf_append_singleton` on `pe'.ofDist`.
  cases e'_pre with
  | mk init trans =>
    exact pe'.ofDist.probOf_append_singleton init trans
      h_e'_pre_term (l, q_new) h_app

/-- **Sub-lemma 3 — Reindexing.** The RHS sum over all terminating sys-histories
`e'` reindexes as a double sum over `(e'_pre : terminating, q_new : State)`,
where `e' = e'_pre ∙ (l, q_new)`. Uses `tsum_eq_tsum_of_ne_zero_bij` and
`belief_support_compat`'s label-equality conjunct to discard `e'` whose label
sequence does not match `rest_prev ++ [l]`. -/
private theorem ProbabilisticExecution.bayes_inversion_step_reindex
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (μ_0 : PMF State) (rest_prev : List (Label × PMF State))
    (l : Label) (μ_new : PMF State) :
    (∑' (e : {e : AlterSeq State Label // e.trans.Terminates}),
        pe'.ofDist.probOf e.1 e.2 *
          pe'.belief e.1
            ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩)
    = ∑' (e'_pre : {e : AlterSeq State Label // e.trans.Terminates}) (q_new : State),
        pe'.ofDist.probOf
          ⟨e'_pre.1.init, e'_pre.1.trans.append (Seq.cons (l, q_new) Seq.nil)⟩
          ⟨_, Stream'.Seq.terminatedAt_append_find e'_pre.2
            (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil).choose_spec⟩ *
        pe'.belief
          ⟨e'_pre.1.init, e'_pre.1.trans.append (Seq.cons (l, q_new) Seq.nil)⟩
          ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ := by
  classical
  -- Combine the double sum on the RHS into a sigma form via `ENNReal.tsum_prod'`.
  rw [show
      (∑' (e'_pre : {e : AlterSeq State Label // e.trans.Terminates}) (q_new : State),
          pe'.ofDist.probOf
            ⟨e'_pre.1.init, e'_pre.1.trans.append (Seq.cons (l, q_new) Seq.nil)⟩
            ⟨_, Stream'.Seq.terminatedAt_append_find e'_pre.2
              (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil).choose_spec⟩ *
          pe'.belief
            ⟨e'_pre.1.init, e'_pre.1.trans.append (Seq.cons (l, q_new) Seq.nil)⟩
            ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩)
      = ∑' (p : {e : AlterSeq State Label // e.trans.Terminates} × State),
          pe'.ofDist.probOf
            ⟨p.1.1.init, p.1.1.trans.append (Seq.cons (l, p.2) Seq.nil)⟩
            ⟨_, Stream'.Seq.terminatedAt_append_find p.1.2
              (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil).choose_spec⟩ *
          pe'.belief
            ⟨p.1.1.init, p.1.1.trans.append (Seq.cons (l, p.2) Seq.nil)⟩
            ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩
      from (ENNReal.tsum_prod' (f := fun (p :
            {e : AlterSeq State Label // e.trans.Terminates} × State) =>
          pe'.ofDist.probOf
            ⟨p.1.1.init, p.1.1.trans.append (Seq.cons (l, p.2) Seq.nil)⟩
            ⟨_, Stream'.Seq.terminatedAt_append_find p.1.2
              (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil).choose_spec⟩ *
          pe'.belief
            ⟨p.1.1.init, p.1.1.trans.append (Seq.cons (l, p.2) Seq.nil)⟩
            ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩)).symm]
  -- Bijection: (e'_pre, q_new) ↔ e := ⟨e'_pre.1.init, e'_pre.1.trans ++ [(l, q_new)]⟩.
  -- Helper: turn a pair into the corresponding extended history (subtype value).
  let rhs_pair : {e : AlterSeq State Label // e.trans.Terminates} × State →
      {e : AlterSeq State Label // e.trans.Terminates} :=
    fun p => ⟨⟨p.1.1.init, p.1.1.trans.append (Seq.cons (l, p.2) Seq.nil)⟩,
              ⟨_, Stream'.Seq.terminatedAt_append_find p.1.2
                (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil).choose_spec⟩⟩
  -- Per-pair summand for the RHS sigma tsum.
  let rhs_summand : {e : AlterSeq State Label // e.trans.Terminates} × State → ENNReal :=
    fun p => pe'.ofDist.probOf (rhs_pair p).1 (rhs_pair p).2 *
          pe'.belief (rhs_pair p).1
            ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩
  change _ = ∑' p, rhs_summand p
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun (p : {p : {e : AlterSeq State Label // e.trans.Terminates} × State //
        rhs_summand p ≠ 0}) =>
      rhs_pair p.1)
    ?_ ?_ ?_
  · -- Injectivity.
    rintro ⟨⟨⟨e'_pre1, h_t1⟩, q1⟩, _⟩ ⟨⟨⟨e'_pre2, h_t2⟩, q2⟩, _⟩ h_eq
    have h_E : (⟨e'_pre1.init, e'_pre1.trans.append (Seq.cons (l, q1) Seq.nil)⟩
        : AlterSeq State Label)
        = ⟨e'_pre2.init, e'_pre2.trans.append (Seq.cons (l, q2) Seq.nil)⟩ :=
      Subtype.ext_iff.mp h_eq
    have h_init : e'_pre1.init = e'_pre2.init := by
      have := congr_arg AlterSeq.init h_E
      exact this
    have h_trans_app : e'_pre1.trans.append (Seq.cons (l, q1) Seq.nil) =
        e'_pre2.trans.append (Seq.cons (l, q2) Seq.nil) := by
      have := congr_arg AlterSeq.trans h_E
      exact this
    have h_trans : e'_pre1.trans = e'_pre2.trans :=
      Stream'.Seq.append_singleton_inj_left e'_pre1.trans e'_pre2.trans
        h_t1 h_t2 _ _ h_trans_app
    have h_lq : (l, q1) = (l, q2) :=
      Stream'.Seq.append_singleton_inj_right e'_pre1.trans e'_pre2.trans
        h_t1 h_t2 _ _ h_trans_app
    have h_q : q1 = q2 := (Prod.mk.inj h_lq).2
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change e'_pre1 = e'_pre2
      cases e'_pre1; cases e'_pre2
      simp_all
    · exact h_q
  · -- Surjectivity.
    rintro ⟨e, h_e_term⟩ h_ne
    -- h_ne: ofDist.probOf e * belief e _ ≠ 0.
    -- So belief e _ ≠ 0 and hence e is in the support → label match.
    have h_belief_ne : pe'.belief e
        ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ ≠ 0 := by
      intro h
      apply h_ne
      change pe'.ofDist.probOf e h_e_term *
          pe'.belief e ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩
        = 0
      rw [h, mul_zero]
    -- Apply belief_support_compat: ⟨μ_0, ...⟩ ∈ belief e .support.
    -- Wait: belief e produces a PMF over E's, so we need to swap.
    -- Actually `belief e E` is the value of the PMF `belief e` at `E`.
    -- belief_support_compat takes hE : E ∈ (belief e).support.
    -- ⟨μ_0, ofList rest_prev ++ [(l, μ_new)]⟩ ∈ (belief e).support.
    have h_E_supp : (⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩
        : AlterSeq (PMF State) Label) ∈ (pe'.belief e).support :=
      (PMF.mem_support_iff _ _).mpr h_belief_ne
    obtain ⟨_, _, h_lab, _, _⟩ := pe'.belief_support_compat h_e_term h_E_supp
    -- h_lab: E.trans.map fst = e.trans.map fst, with
    --   E.trans = (ofList rest_prev).append (cons (l, μ_new) nil).
    -- So e.trans.map fst = (ofList rest_prev).map fst ++ [l] (modulo seq isomorphism).
    -- In particular, e.trans is non-nil (has length ≥ 1 + rest_prev.length).
    have h_e_trans_nonempty : e.trans.toList h_e_term ≠ [] := by
      intro h_empty
      -- If empty, then map empty = empty, but RHS of h_lab is nonempty.
      have h_E_term : ((Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)).Terminates :=
        ⟨_, Stream'.Seq.terminatedAt_append_find (Stream'.Seq.terminates_ofList _)
          (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil).choose_spec⟩
      -- Length match via labels (use h_lab).
      have h_e_eq : e.trans = Seq.nil := by
        have h := Stream'.Seq.ofList_toList e.trans h_e_term
        rw [h_empty] at h
        rw [← h, Stream'.Seq.ofList_nil]
      -- Then e.trans.map fst = nil but the RHS has length ≥ 1.
      rw [h_e_eq] at h_lab
      change Stream'.Seq.map _ ((Seq.ofList rest_prev).append _) = Seq.map _ Seq.nil at h_lab
      rw [Stream'.Seq.map_nil] at h_lab
      -- The LHS is non-nil. Get a contradiction via length.
      have h_len : ((Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)).map
          (fun lμ : Label × PMF State => lμ.1) ≠ Seq.nil := by
        intro h_nil
        have h_E_get0 : (((Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)).map
            (fun lμ : Label × PMF State => lμ.1)).get? rest_prev.length = none := by
          rw [h_nil]; rfl
        rw [Stream'.Seq.map_get?] at h_E_get0
        have h_app_get : ((Seq.ofList rest_prev).append
            (Seq.cons (l, μ_new) Seq.nil)).get? rest_prev.length = some (l, μ_new) := by
          have h_find : Nat.find (Stream'.Seq.terminates_ofList rest_prev)
              = rest_prev.length := by
            -- The first termination index of `ofList rest_prev` is its length.
            apply le_antisymm
            · apply Nat.find_le
              -- TerminatedAt rest_prev.length: get? at length is none.
              change (Seq.ofList rest_prev).get? rest_prev.length = none
              rw [Stream'.Seq.ofList_get?]; simp
            · -- All k < length are not terminated.
              by_contra h_lt
              push Not at h_lt
              have h_term_lt := Nat.find_spec (Stream'.Seq.terminates_ofList rest_prev)
              -- Nat.find ≤ length - 1, so let n := Nat.find.
              set n := Nat.find (Stream'.Seq.terminates_ofList rest_prev) with hn
              have h_n_lt : n < rest_prev.length := h_lt
              -- TerminatedAt n means get? n = none, but ofList.get? n = (some _) for n < length.
              have h_get_n : (Seq.ofList rest_prev).get? n = none := h_term_lt
              rw [Stream'.Seq.ofList_get?] at h_get_n
              simp [] at h_get_n
              omega
          have := Stream'.Seq.get?_append_find (Stream'.Seq.terminates_ofList rest_prev)
            (Seq.cons (l, μ_new) Seq.nil) 0
          rw [h_find] at this
          simp only [add_zero, Seq.get?_cons_zero] at this
          convert this using 2
        rw [h_app_get] at h_E_get0
        simp at h_E_get0
      exact h_len h_lab
    -- Now use exists_split_last to peel off last (l, q_new).
    obtain ⟨previous, last, h_prev_term, h_e_trans_eq, _, _⟩ :=
      Stream'.Seq.exists_split_last e.trans h_e_term h_e_trans_nonempty
    -- last must equal (l, q_new) for some q_new — verify via label compatibility.
    -- We have h_lab : E.trans.map fst = e.trans.map fst.
    -- E.trans ends with (l, μ_new), so labels end with l, so last.1 = l.
    have h_last_label : last.1 = l := by
      have h_e_trans : e.trans = previous.append (Seq.cons last Seq.nil) := h_e_trans_eq
      rw [h_e_trans] at h_lab
      -- (ofList rest_prev ++ [(l,μ_new)]).map fst = (previous ++ [last]).map fst.
      rw [Stream'.Seq.map_append, Stream'.Seq.map_append,
          Stream'.Seq.map_cons, Stream'.Seq.map_nil,
          Stream'.Seq.map_cons, Stream'.Seq.map_nil] at h_lab
      -- Right-cancel: l = last.1.
      exact (Stream'.Seq.append_singleton_inj_right _ _
        (Stream'.Seq.terminates_map_iff.mpr
          (Stream'.Seq.terminates_ofList rest_prev))
        (Stream'.Seq.terminates_map_iff.mpr h_prev_term)
        _ _ h_lab).symm
    -- Set q_new := last.2. Build the witness for surjectivity.
    -- Note: e = ⟨e.init, previous ++ [(l, last.2)]⟩ via h_e_trans_eq and h_last_label.
    have h_last_eq : last = (l, last.2) := by rw [← h_last_label]
    have h_e_eq : (⟨e.init, previous.append (Seq.cons (l, last.2) Seq.nil)⟩
        : AlterSeq State Label) = e := by
      rw [← h_last_eq, ← h_e_trans_eq]
    -- The candidate pair: e'_pre = ⟨e.init, previous⟩, q_new = last.2.
    -- Verify the non-zero condition.
    have h_ne_summand : rhs_summand
        (⟨⟨e.init, previous⟩, h_prev_term⟩, last.2) ≠ 0 := by
      change pe'.ofDist.probOf
          ⟨e.init, previous.append (Seq.cons (l, last.2) Seq.nil)⟩ _ *
        pe'.belief
          ⟨e.init, previous.append (Seq.cons (l, last.2) Seq.nil)⟩
          ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ ≠ 0
      -- Use h_e_eq to transport the LHS to e's shape.
      intro h_zero
      apply h_ne
      change pe'.ofDist.probOf e h_e_term *
          pe'.belief e ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩
        = 0
      have h_pof : pe'.ofDist.probOf
          ⟨e.init, previous.append (Seq.cons (l, last.2) Seq.nil)⟩ (h_e_eq ▸ h_e_term)
          = pe'.ofDist.probOf e h_e_term := by congr 1
      have h_bel : pe'.belief
          ⟨e.init, previous.append (Seq.cons (l, last.2) Seq.nil)⟩
          = pe'.belief e := by congr 1
      rw [h_pof, h_bel] at h_zero
      exact h_zero
    refine ⟨⟨(⟨⟨e.init, previous⟩, h_prev_term⟩, last.2), h_ne_summand⟩, ?_⟩
    -- The constructed subtype element equals ⟨e, h_e_term⟩.
    apply Subtype.ext
    change (⟨⟨e.init, previous.append (Seq.cons (l, last.2) Seq.nil)⟩, _⟩
        : {e : AlterSeq State Label // e.trans.Terminates}).1 = e
    exact h_e_eq
  · -- Compatibility.
    rintro ⟨⟨⟨e'_pre, h_t⟩, q_new⟩, _⟩
    rfl

/-- **Hyperstep marginal decomposition.** For a 𝒟(sys)-scheduler emission
`(l, ω)` at a terminating history `E`, the post-state marginal of `ω`
decomposes as the state-wise mixture of the per-state hyperStep-kernel
bind:
```
(ω.bind id) q = ∑' s, (E.endState hE) s · ((distHyperKernel E l ω s).bind id) q
```
This is the `μ_post = μ_pre.bind (fun s => (p s).bind id)` conjunct of the
hyperStep witness, restated in terms of `distHyperKernel`. The bridge
identity needed to relate `ofDist.kernel` and `Z_global` in the crux.

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

/-- **`ofDist.kernel` explicit expansion.** Unfolds `Scheduler.ofDist.next`'s
nested binds to express `ofDist.kernel` as a double tsum:
```
ofDist.kernel e'_pre (l, q) =
  ∑' E, belief e'_pre E *
    ∑' ω, scheduler.next E (some (l, ω)) *
      (distHyperKernel E l ω (e'_pre.endState)).bind id q
```
Compare to the definition of `Z_global`, which has `(ω.bind id) q` instead
of `(distHyperKernel ... e'_pre.endState).bind id q`. The two differ by
the choice of `s` in `hyperStep_marginal_decomp`: `Z_global` averages over
`s ∈ E.endState.support`, while `ofDist.kernel` evaluates at the specific
`s = e'_pre.endState`. This asymmetry is the source of the
`Φ` non-pointwise-1 phenomenon in the crux. -/
private theorem ProbabilisticExecution.ofDist_kernel_expand
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (e'_pre : AlterSeq State Label) (h_e'_pre_term : e'_pre.trans.Terminates)
    (l : Label) (q : State) :
    pe'.ofDist.kernel e'_pre (l, q) =
      ∑' E : AlterSeq (PMF State) Label,
        pe'.belief e'_pre E *
        ∑' ω : PMF (PMF State),
          pe'.scheduler.next E (some (l, ω)) *
          ((pe'.distHyperKernel E l ω (e'_pre.endState h_e'_pre_term)).bind id) q := by
  classical
  -- Unfold `ofDist.kernel` to the μ-tsum.
  unfold ProbabilisticExecution.kernel
  -- Step 1: Rewrite each `ofDist.scheduler.next e'_pre (some (l, μ'))` via dif_pos.
  have h_sch_eq : ∀ μ' : PMF State,
      pe'.ofDist.scheduler.next e'_pre (some (l, μ'))
        = ((pe'.belief e'_pre).bind (fun E =>
            (pe'.scheduler.next E).bind (fun opt =>
              match opt with
              | none => PMF.pure none
              | some (l', ω) =>
                  (pe'.distHyperKernel E l' ω (e'_pre.endState h_e'_pre_term)).map
                    (fun μ'' => some (l', μ''))))) (some (l, μ')) := by
    intro μ'
    change (open Classical in
      if h_term : e'_pre.trans.Terminates then
        (pe'.belief e'_pre).bind (fun E =>
          (pe'.scheduler.next E).bind (fun opt =>
            match opt with
            | none => PMF.pure none
            | some (l', ω) =>
                (pe'.distHyperKernel E l' ω (e'_pre.endState h_term)).map
                  (fun μ'' => some (l', μ''))))
      else
        PMF.pure none) (some (l, μ')) = _
    rw [dif_pos h_e'_pre_term]
  -- Helper: map evaluation at `some (l, μ')`.
  have h_map_l : ∀ (E : AlterSeq (PMF State) Label) (ω : PMF (PMF State)) (μ' : PMF State),
      ((pe'.distHyperKernel E l ω (e'_pre.endState h_e'_pre_term)).map
        (fun μ'' => (some (l, μ'') : Option (Label × PMF State))))
        (some (l, μ'))
      = pe'.distHyperKernel E l ω (e'_pre.endState h_e'_pre_term) μ' := by
    intro E ω μ'
    rw [PMF.map_apply]
    rw [tsum_eq_single μ']
    · simp
    · intro μ'' h_ne
      have h_neq : (some (l, μ') : Option (Label × PMF State)) ≠ some (l, μ'') := by
        intro h; apply h_ne; injection h with h1
        exact ((Prod.mk.inj h1).2).symm
      rw [if_neg h_neq]
  have h_map_ne : ∀ (E : AlterSeq (PMF State) Label)
      (l' : Label) (h_lab : l' ≠ l) (ω : PMF (PMF State)) (μ' : PMF State),
      ((pe'.distHyperKernel E l' ω (e'_pre.endState h_e'_pre_term)).map
        (fun μ'' => (some (l', μ'') : Option (Label × PMF State))))
        (some (l, μ'))
      = 0 := by
    intro E l' h_lab ω μ'
    rw [PMF.map_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro μ''
    have h_neq : (some (l, μ') : Option (Label × PMF State)) ≠ some (l', μ'') := by
      intro h; apply h_lab; injection h with h1
      exact ((Prod.mk.inj h1).1).symm
    rw [if_neg h_neq]
  -- Step 2: For each (E, μ'), inner bind picks out the `some (l, ω)` branch.
  have h_inner_eval : ∀ (E : AlterSeq (PMF State) Label) (μ' : PMF State),
      ((pe'.scheduler.next E).bind (fun opt =>
        match opt with
        | none => PMF.pure none
        | some (l', ω) =>
            (pe'.distHyperKernel E l' ω (e'_pre.endState h_e'_pre_term)).map
              (fun μ'' => some (l', μ'')))) (some (l, μ'))
      = ∑' ω : PMF (PMF State),
          pe'.scheduler.next E (some (l, ω)) *
          pe'.distHyperKernel E l ω (e'_pre.endState h_e'_pre_term) μ' := by
    intro E μ'
    rw [PMF.bind_apply]
    -- ∑' opt, sched_E opt * (match opt with …) at (some (l, μ')).
    -- Equivalently: reindex tsum to be over PMF (PMF State) via opt = some (l, ω);
    -- all other `opt` contribute zero.
    refine tsum_eq_tsum_of_ne_zero_bij
      (i := fun p => some (l, p.1)) ?_ ?_ ?_
    · -- Injectivity.
      rintro ⟨ω₁, h1⟩ ⟨ω₂, h2⟩ h_eq
      simp only at h_eq
      apply Subtype.ext
      exact (Prod.mk.inj (Option.some.inj h_eq)).2
    · -- Coverage: every nonzero opt is of the form `some (l, ω)`.
      rintro opt h_opt_ne
      -- h_opt_ne is membership in support; unfold.
      have h_opt_ne' :
          (pe'.scheduler.next E) opt *
            (match opt with
              | none => (PMF.pure none : PMF (Option (Label × PMF State)))
              | some (l', ω) =>
                  (pe'.distHyperKernel E l' ω (e'_pre.endState h_e'_pre_term)).map
                    (fun μ'' => some (l', μ''))) (some (l, μ')) ≠ 0 := h_opt_ne
      have h_match_ne :
          (match opt with
            | none => (PMF.pure none : PMF (Option (Label × PMF State)))
            | some (l', ω) =>
                (pe'.distHyperKernel E l' ω (e'_pre.endState h_e'_pre_term)).map
                  (fun μ'' => some (l', μ''))) (some (l, μ')) ≠ 0 := by
        intro h0
        apply h_opt_ne'
        rw [h0, mul_zero]
      cases opt with
      | none =>
        exfalso
        apply h_match_ne
        change (PMF.pure (α := Option (Label × PMF State)) none) (some (l, μ')) = 0
        rw [PMF.pure_apply]
        have h_neq : (some (l, μ') : Option (Label × PMF State)) ≠ none := by
          intro h; exact (Option.some_ne_none _ h)
        rw [if_neg h_neq]
      | some lω =>
        obtain ⟨l', ω⟩ := lω
        by_cases h_lab : l' = l
        · cases h_lab
          refine ⟨⟨ω, ?_⟩, rfl⟩
          -- Need: ω is in support of the ω-sum (nonzero contribution).
          intro h_zero
          simp only at h_zero
          apply h_opt_ne'
          change (pe'.scheduler.next E) (some (l, ω)) *
            ((pe'.distHyperKernel E l ω (e'_pre.endState h_e'_pre_term)).map
              (fun μ'' => (some (l, μ'') : Option (Label × PMF State))))
              (some (l, μ')) = 0
          rw [h_map_l E ω μ', h_zero]
        · exfalso
          apply h_match_ne
          change ((pe'.distHyperKernel E l' ω (e'_pre.endState h_e'_pre_term)).map
            (fun μ'' => (some (l', μ'') : Option (Label × PMF State))))
            (some (l, μ')) = 0
          exact h_map_ne E l' h_lab ω μ'
    · -- The summand equality.
      rintro ⟨ω, _⟩
      simp only
      show (pe'.scheduler.next E) (some (l, ω)) *
          ((pe'.distHyperKernel E l ω (e'_pre.endState h_e'_pre_term)).map
            (fun μ'' => (some (l, μ'') : Option (Label × PMF State))))
            (some (l, μ'))
        = (pe'.scheduler.next E) (some (l, ω)) *
            (pe'.distHyperKernel E l ω (e'_pre.endState h_e'_pre_term)) μ'
      rw [h_map_l E ω μ']
  -- Step 3: Combine. Substitute h_sch_eq + PMF.bind_apply + h_inner_eval into LHS.
  have h_lhs_per_mu : ∀ μ' : PMF State,
      pe'.ofDist.scheduler.next e'_pre (some (l, μ')) * μ' q
      = (∑' E : AlterSeq (PMF State) Label,
            pe'.belief e'_pre E *
            ∑' ω : PMF (PMF State),
              pe'.scheduler.next E (some (l, ω)) *
              pe'.distHyperKernel E l ω (e'_pre.endState h_e'_pre_term) μ') * μ' q := by
    intro μ'
    rw [h_sch_eq μ', PMF.bind_apply]
    congr 1
    apply tsum_congr
    intro E
    rw [h_inner_eval E μ']
  rw [tsum_congr h_lhs_per_mu]
  -- Now LHS: ∑' μ', (∑' E, belief · ∑' ω, sched · distHyperKernel μ') · μ' q.
  -- Pull μ' q inside the E-sum.
  conv_lhs => rw [tsum_congr (fun μ' => by rw [← ENNReal.tsum_mul_right])]
  -- LHS: ∑' μ', ∑' E, (belief * (∑' ω, sched * distHyperKernel μ')) * μ' q.
  rw [ENNReal.tsum_comm]
  -- LHS: ∑' E, ∑' μ', (belief * (∑' ω, sched * distHyperKernel μ')) * μ' q.
  apply tsum_congr
  intro E
  -- Inner E term.
  conv_lhs =>
    rw [tsum_congr (fun μ' => by rw [mul_assoc])]
    rw [ENNReal.tsum_mul_left]
  congr 1
  -- ∑' μ', (∑' ω, sched · distHyperKernel μ') · μ' q
  --   = ∑' ω, sched · ((distHyperKernel _).bind id) q.
  conv_lhs => rw [tsum_congr (fun μ' => by rw [← ENNReal.tsum_mul_right])]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro ω
  -- ∑' μ', sched · distHyperKernel _ μ' · μ' q = sched · (distHyperKernel _).bind id q.
  conv_lhs => rw [tsum_congr (fun μ' => by rw [mul_assoc])]
  rw [ENNReal.tsum_mul_left, PMF.bind_apply]
  rfl

/-- **Focused sub-sorry: inversion at `E_full`.**

Statement of `belief_bayes_inversion` specialised to the extended sequence
`E_full = ⟨μ_0, rest_prev ++ [(l, μ_new)]⟩`, taking the inductive hypothesis
at `E_pre = ⟨μ_0, rest_prev⟩` as input. Cannot be discharged directly here
because of declaration order — `belief_bayes_inversion_step` is proved AFTER
this file location and itself depends on `bayes_inversion_crux_averaging`.
This sub-sorry is reconciled at the level of `belief_bayes_inversion_list`
later, by structuring the recursion to produce both proofs simultaneously. -/
private theorem ProbabilisticExecution.inversion_at_E_full
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (μ_0 : PMF State) (rest_prev : List (Label × PMF State))
    (l : Label) (μ_new : PMF State)
    (h_pre : (Seq.ofList rest_prev).Terminates)
    (h_app : ((Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)).Terminates)
    (_ih :
      pe'.probOf ⟨μ_0, Seq.ofList rest_prev⟩ h_pre =
      ∑' (e : {e : AlterSeq State Label // e.trans.Terminates}),
        pe'.ofDist.probOf e.1 e.2 * pe'.belief e.1 ⟨μ_0, Seq.ofList rest_prev⟩) :
    pe'.probOf ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ h_app =
    ∑' (e : {e : AlterSeq State Label // e.trans.Terminates}),
      pe'.ofDist.probOf e.1 e.2 *
        pe'.belief e.1
          ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons (l, μ_new) Seq.nil)⟩ := sorry

/-- **Bayes inversion, inductive step (cons-end).** Direct restatement of
`inversion_at_E_full` with `last := (l, μ_new)` destructured. The deep
algebraic content lives in `inversion_at_E_full` (the sole remaining
sorry in the chain). -/
private theorem ProbabilisticExecution.belief_bayes_inversion_step
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (μ_0 : PMF State) (rest_prev : List (Label × PMF State))
    (last : Label × PMF State)
    (h_pre : (Seq.ofList rest_prev).Terminates)
    (h_app : ((Seq.ofList rest_prev).append (Seq.cons last Seq.nil)).Terminates)
    (ih :
      pe'.probOf ⟨μ_0, Seq.ofList rest_prev⟩ h_pre =
      ∑' (e : {e : AlterSeq State Label // e.trans.Terminates}),
        pe'.ofDist.probOf e.1 e.2 * pe'.belief e.1 ⟨μ_0, Seq.ofList rest_prev⟩) :
    pe'.probOf ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons last Seq.nil)⟩ h_app =
      ∑' (e : {e : AlterSeq State Label // e.trans.Terminates}),
        pe'.ofDist.probOf e.1 e.2 *
          pe'.belief e.1 ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons last Seq.nil)⟩ := by
  rcases last with ⟨l, μ_new⟩
  exact pe'.inversion_at_E_full μ_0 rest_prev l μ_new h_pre h_app ih

/-- **Auxiliary**: list-keyed disintegration identity. For any `μ_0` and
finite list `L : List (Label × PMF State)`, the disintegration holds for
`E = ⟨μ_0, Seq.ofList L⟩`. Proved by `List.reverseRecOn`, dispatching to
`belief_bayes_inversion_nil` (base) and `belief_bayes_inversion_step`
(cons-end). -/
private theorem ProbabilisticExecution.belief_bayes_inversion_list
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (μ_0 : PMF State) (L : List (Label × PMF State))
    (h_term : (Seq.ofList L).Terminates) :
    pe'.probOf ⟨μ_0, Seq.ofList L⟩ h_term =
      ∑' (e : {e : AlterSeq State Label // e.trans.Terminates}),
        pe'.ofDist.probOf e.1 e.2 *
          pe'.belief e.1 ⟨μ_0, Seq.ofList L⟩ := by
  classical
  induction L using List.reverseRecOn with
  | nil =>
    -- `Seq.ofList [] = Seq.nil`; reduce to `belief_bayes_inversion_nil`.
    have h_nil_eq : Seq.ofList ([] : List (Label × PMF State)) = Seq.nil :=
      Stream'.Seq.ofList_nil
    -- Rewrite goal via h_nil_eq.
    have h_E_eq : (⟨μ_0, Seq.ofList ([] : List (Label × PMF State))⟩
        : AlterSeq (PMF State) Label) = ⟨μ_0, Seq.nil⟩ := by
      simp [h_nil_eq]
    rw [show pe'.probOf ⟨μ_0, Seq.ofList ([] : List (Label × PMF State))⟩ h_term
          = pe'.probOf ⟨μ_0, Seq.nil⟩ Stream'.Seq.terminates_nil by
        congr 1]
    have h_rhs :
        (∑' (e : {e : AlterSeq State Label // e.trans.Terminates}),
            pe'.ofDist.probOf e.1 e.2 *
              pe'.belief e.1 ⟨μ_0, Seq.ofList ([] : List (Label × PMF State))⟩)
        = ∑' (e : {e : AlterSeq State Label // e.trans.Terminates}),
            pe'.ofDist.probOf e.1 e.2 * pe'.belief e.1 ⟨μ_0, Seq.nil⟩ := by
      simp only [h_nil_eq]
    rw [h_rhs]
    exact pe'.belief_bayes_inversion_nil μ_0
  | append_singleton rest_prev last ih =>
    -- Convert `Seq.ofList (rest_prev ++ [last])` into
    -- `(Seq.ofList rest_prev).append (Seq.cons last Seq.nil)`.
    have h_seq_eq : Seq.ofList (rest_prev ++ [last])
        = (Seq.ofList rest_prev).append (Seq.cons last Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons,
          Stream'.Seq.ofList_nil]
    have h_pre : (Seq.ofList rest_prev).Terminates :=
      Stream'.Seq.terminates_ofList rest_prev
    -- Rewrite goal via h_seq_eq.
    have h_lhs : pe'.probOf ⟨μ_0, Seq.ofList (rest_prev ++ [last])⟩ h_term
        = pe'.probOf ⟨μ_0, (Seq.ofList rest_prev).append (Seq.cons last Seq.nil)⟩
            (h_seq_eq ▸ h_term) := by
      congr 1 ; simp [h_seq_eq]
    rw [h_lhs]
    have h_rhs :
        (∑' (e : {e : AlterSeq State Label // e.trans.Terminates}),
            pe'.ofDist.probOf e.1 e.2 *
              pe'.belief e.1 ⟨μ_0, Seq.ofList (rest_prev ++ [last])⟩)
        = ∑' (e : {e : AlterSeq State Label // e.trans.Terminates}),
            pe'.ofDist.probOf e.1 e.2 *
              pe'.belief e.1 ⟨μ_0, (Seq.ofList rest_prev).append
                (Seq.cons last Seq.nil)⟩ := by
      congr 1
      funext e
      congr 1
      simp [h_seq_eq]
    rw [h_rhs]
    exact pe'.belief_bayes_inversion_step μ_0 rest_prev last h_pre _ (ih h_pre)

/-- **Bayes inversion (deep belief spec).** For any finite `𝒟(sys)`-history
`E`, the `pe'.probOf E` mass decomposes as a sum over `sys`-histories of the
joint mass `(ofDist pe').probOf e * pe'.belief e E`:

  `pe'.probOf E hE_term
     = ∑' (e : {e // e.trans.Terminates}),
         (ofDist pe').probOf e.1 e.2 * pe'.belief e.1 E`

This is the disintegration identity for the joint coupling
`((ofDist pe').probOf e) * (belief e E)` along its `𝒟(sys)`-marginal.
The proof is by induction on `E.trans.toList hE_term` via
`belief_bayes_inversion_list`, reducing to `belief_bayes_inversion_nil`
(base) and `belief_bayes_inversion_step` (cons-end). -/
theorem ProbabilisticExecution.belief_bayes_inversion
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem)
    (E : AlterSeq (PMF State) Label) (hE_term : E.trans.Terminates) :
    pe'.probOf E hE_term =
      ∑' (e : {e : AlterSeq State Label // e.trans.Terminates}),
        pe'.ofDist.probOf e.1 e.2 * pe'.belief e.1 E := by
  classical
  -- Reduce to the list-keyed auxiliary at `L = E.trans.toList hE_term`.
  have h_seq : Seq.ofList (E.trans.toList hE_term) = E.trans :=
    Stream'.Seq.ofList_toList E.trans hE_term
  have h_struct : (⟨E.init, Seq.ofList (E.trans.toList hE_term)⟩
      : AlterSeq (PMF State) Label) = E := by
    cases E with
    | mk init trans => simp [h_seq]
  have h_term' : (Seq.ofList (E.trans.toList hE_term)).Terminates := by
    rw [h_seq]; exact hE_term
  have h_aux := pe'.belief_bayes_inversion_list E.init
    (E.trans.toList hE_term) h_term'
  -- Transport via h_struct.
  -- LHS via h_struct: `probOf ⟨E.init, Seq.ofList _⟩ _ = probOf E _`.
  have h_lhs : pe'.probOf ⟨E.init, Seq.ofList (E.trans.toList hE_term)⟩ h_term'
      = pe'.probOf E hE_term := by
    congr 1
  rw [← h_lhs, h_aux]
  -- RHS: identify the sums via `h_struct`.
  simp only [h_struct]

/-- **Trace probability preservation.** For each trace `τ`, the
`sys`-trace probability of `ofDist pe'` equals the `𝒟(sys)`-trace
probability of `pe'`. This is the headline lemma of the superset
direction.

The proof goes via the joint coupling `(e, E)` weighted by
`(ofDist pe').probOf e * pe'.belief e E`, with the marginal over the
`𝒟(sys)`-side given by `belief_bayes_inversion` and the marginal over
the `sys`-side by `(pe'.belief e).tsum_coe = 1`. The label-equality
conjunct of `belief_support_compat` (used via `belief_trace_eq` and
`belief_isTight_iff`) makes the trace constraint transfer fibrewise. -/
theorem ProbabilisticExecution.ofDist_traceProb_eq
    {sys : LabelledSystem State Label}
    (pe' : ProbabilisticExecution 𝒟(sys).toSystem) (τ : Seq Label) :
    sys.traceProb pe'.ofDist τ = 𝒟(sys).traceProb pe' τ := by
  classical
  -- Auxiliary joint sum over `(e, E)` indexed by tight-with-trace-τ `E`'s
  -- (on the `𝒟(sys)` side) and finite `e`'s (on the `sys` side).
  set S : ENNReal :=
    ∑' (E : {E : AlterSeq (PMF State) Label //
        E.trans.Terminates ∧ 𝒟(sys).trace E = τ ∧ 𝒟(sys).IsTight E})
      (e : {e : AlterSeq State Label // e.trans.Terminates}),
        pe'.ofDist.probOf e.1 e.2 * pe'.belief e.1 E.1 with hS_def
  -- (a) `S = 𝒟(sys).traceProb pe' τ` via `belief_bayes_inversion` for each `E`.
  have h_a : 𝒟(sys).traceProb pe' τ = S := by
    unfold LabelledSystem.traceProb
    rw [hS_def]
    refine tsum_congr (fun E => ?_)
    exact pe'.belief_bayes_inversion E.1 E.2.1
  -- (b) `S = sys.traceProb pe'.ofDist τ` via Fubini + inner sum identification.
  have h_b : S = sys.traceProb pe'.ofDist τ := by
    rw [hS_def]
    -- Swap the order of summation (ENNReal tsum_comm).
    rw [ENNReal.tsum_comm]
    -- Now: `∑' e, ∑' E[tight,τ], (ofDist pe').probOf e * belief e E`.
    -- For each e: factor out (ofDist pe').probOf e (independent of E).
    have h_factor : ∀ (e : {e : AlterSeq State Label // e.trans.Terminates}),
        (∑' (E : {E : AlterSeq (PMF State) Label //
            E.trans.Terminates ∧ 𝒟(sys).trace E = τ ∧ 𝒟(sys).IsTight E}),
          pe'.ofDist.probOf e.1 e.2 * pe'.belief e.1 E.1)
        = pe'.ofDist.probOf e.1 e.2 *
          ∑' (E : {E : AlterSeq (PMF State) Label //
            E.trans.Terminates ∧ 𝒟(sys).trace E = τ ∧ 𝒟(sys).IsTight E}),
            pe'.belief e.1 E.1 := by
      intro e; rw [ENNReal.tsum_mul_left]
    simp_rw [h_factor]
    -- Inner sum over tight-trace-τ E's of `pe'.belief e.1 E`. By
    -- `belief_trace_eq` + `belief_isTight_iff`, support of `pe'.belief e.1`
    -- restricted to tight-trace-τ E's is the full support iff e itself is
    -- tight with trace τ; otherwise empty.
    have h_inner : ∀ (e : {e : AlterSeq State Label // e.trans.Terminates}),
        (∑' (E : {E : AlterSeq (PMF State) Label //
            E.trans.Terminates ∧ 𝒟(sys).trace E = τ ∧ 𝒟(sys).IsTight E}),
          pe'.belief e.1 E.1)
        = if sys.trace e.1 = τ ∧ sys.IsTight e.1 then 1 else 0 := by
      intro e
      by_cases h_e : sys.trace e.1 = τ ∧ sys.IsTight e.1
      · rw [if_pos h_e]
        -- The full sum `∑' E_all, pe'.belief e.1 E = 1` by `tsum_coe`.
        have h_full : (∑' E_all : AlterSeq (PMF State) Label, pe'.belief e.1 E_all) = 1 :=
          (pe'.belief e.1).tsum_coe
        rw [← h_full]
        -- Reindex: `∑' E_constrained, belief E.1 = ∑' E_all, belief E_all`
        -- because outside the constraint, belief is 0. Use
        -- `tsum_eq_tsum_of_ne_zero_bij` with:
        --   `f x = belief e.1 x.1` over the constrained subtype `β`,
        --   `g y = belief e.1 y` over `AlterSeq (PMF State) Label`,
        --   `i : support g → β` mapping each E in belief's support to the
        --        constrained-subtype element (constraint auto-satisfied).
        refine tsum_eq_tsum_of_ne_zero_bij
          (i := fun E_supp =>
            (⟨E_supp.1, (pe'.belief_support_compat e.2 (by
              rw [PMF.mem_support_iff]; exact E_supp.2)).1,
              (pe'.belief_trace_eq e.2 (by
                rw [PMF.mem_support_iff]; exact E_supp.2)).trans h_e.1,
              (pe'.belief_isTight_iff e.2 (by
                rw [PMF.mem_support_iff]; exact E_supp.2)).mpr h_e.2⟩ :
              {E : AlterSeq (PMF State) Label //
                E.trans.Terminates ∧ 𝒟(sys).trace E = τ ∧ 𝒟(sys).IsTight E}))
          ?_ ?_ ?_
        · -- Injectivity.
          rintro ⟨E₁, h₁⟩ ⟨E₂, h₂⟩ h_eq
          -- `h_eq` unfolds to equality of the constrained subtype; project to E.
          have h_E : E₁ = E₂ := by
            have := Subtype.ext_iff.mp h_eq
            exact this
          exact Subtype.ext h_E
        · -- Surjectivity: support of `f x = belief e.1 x.1` ⊆ range of `i`.
          rintro ⟨E, hE_term, hE_trace, hE_tight⟩ h_ne
          -- `h_ne : belief e.1 E ≠ 0`, so E ∈ belief.support.
          refine ⟨⟨E, ?_⟩, ?_⟩
          · rw [Function.mem_support]; exact h_ne
          · rfl
        · -- Compatibility.
          intro E_supp; rfl
      · rw [if_neg h_e]
        -- The constrained sum is zero: any E satisfying the constraints would
        -- force e.1 into the same tightness/trace class via the iffs.
        apply ENNReal.tsum_eq_zero.mpr
        rintro ⟨E, hE_term, hE_trace, hE_tight⟩
        -- Show pe'.belief e.1 E = 0.
        by_contra h_ne
        apply h_e
        have h_supp : E ∈ (pe'.belief e.1).support := by
          rw [PMF.mem_support_iff]; exact h_ne
        have h_trace_e : sys.trace e.1 = τ := by
          rw [← pe'.belief_trace_eq e.2 h_supp, hE_trace]
        have h_tight_e : sys.IsTight e.1 :=
          (pe'.belief_isTight_iff e.2 h_supp).mp hE_tight
        exact ⟨h_trace_e, h_tight_e⟩
    simp_rw [h_inner]
    -- Now: `∑' e, (ofDist pe').probOf e.1 e.2 * (if [conditions on e.1] then 1 else 0)`
    -- Simplify the multiplication.
    have h_mul : ∀ (e : {e : AlterSeq State Label // e.trans.Terminates}),
        pe'.ofDist.probOf e.1 e.2 *
          (if sys.trace e.1 = τ ∧ sys.IsTight e.1 then (1 : ENNReal) else 0)
        = if sys.trace e.1 = τ ∧ sys.IsTight e.1 then pe'.ofDist.probOf e.1 e.2 else 0 := by
      intro e
      split_ifs with h
      · rw [mul_one]
      · rw [mul_zero]
    simp_rw [h_mul]
    -- Last step: rewrite the conditional sum as a sum over the constrained subtype.
    unfold LabelledSystem.traceProb
    -- Goal: `∑' e (over {Terminates}), (if trace=τ ∧ IsTight then probOf else 0)
    --     = ∑' e (over {Terminates ∧ trace=τ ∧ IsTight}), probOf`.
    refine tsum_eq_tsum_of_ne_zero_bij
      (i := fun (e_supp :
          {e : {e : AlterSeq State Label // e.trans.Terminates ∧
            sys.trace e = τ ∧ sys.IsTight e} // pe'.ofDist.probOf e.1 e.2.1 ≠ 0}) =>
        (⟨e_supp.1.1, e_supp.1.2.1⟩ : {e : AlterSeq State Label // e.trans.Terminates}))
      ?_ ?_ ?_
    · rintro ⟨⟨e₁, h₁⟩, hne₁⟩ ⟨⟨e₂, h₂⟩, hne₂⟩ h_eq
      -- `h_eq : i ⟨⟨e₁,h₁⟩,_⟩ = i ⟨⟨e₂,h₂⟩,_⟩` unfolds to
      -- `⟨e₁, h₁.1⟩ = ⟨e₂, h₂.1⟩` (in {terminates}), giving e₁ = e₂.
      have h_e : e₁ = e₂ := by
        have := Subtype.ext_iff.mp h_eq
        exact this
      exact Subtype.ext (Subtype.ext h_e)
    · intro e_pair h_ne
      obtain ⟨e, h_term⟩ := e_pair
      change (if sys.trace e = τ ∧ sys.IsTight e then pe'.ofDist.probOf e h_term else 0) ≠ 0
        at h_ne
      by_cases h_cond : sys.trace e = τ ∧ sys.IsTight e
      · rw [if_pos h_cond] at h_ne
        refine ⟨⟨⟨e, h_term, h_cond.1, h_cond.2⟩, ?_⟩, rfl⟩
        change pe'.ofDist.probOf e h_term ≠ 0; exact h_ne
      · rw [if_neg h_cond] at h_ne
        exact absurd rfl h_ne
    · intro e_supp
      obtain ⟨⟨e, h_term, h_trace, h_tight⟩, h_ne⟩ := e_supp
      change (if sys.trace e = τ ∧ sys.IsTight e then pe'.ofDist.probOf e h_term else 0)
        = pe'.ofDist.probOf e h_term
      rw [if_pos ⟨h_trace, h_tight⟩]
  rw [h_b.symm, h_a]

/-- **Superset direction of `dist_traceProb_eq`.** Given an achievable trace
distribution `D` of `𝒟(sys)` (witnessed by `pe'`), the `ofDist`-constructed
`sys`-execution achieves the same trace distribution. -/
theorem dist_traceProb_superset (sys : LabelledSystem State Label) :
    achievableTraceDists 𝒟(sys) ⊆ achievableTraceDists sys := by
  rintro D ⟨pe', h_pe'⟩
  refine ⟨pe'.ofDist, fun τ => ?_⟩
  rw [pe'.ofDist_traceProb_eq τ, h_pe' τ]

/-- **Distribution-monad construction preserves trace distributions.** -/
theorem dist_traceProb_eq (sys : LabelledSystem State Label) :
    achievableTraceDists sys = achievableTraceDists 𝒟(sys) :=
  Set.Subset.antisymm
    (dist_traceProb_subset sys)
    (dist_traceProb_superset sys)

end PLTS
