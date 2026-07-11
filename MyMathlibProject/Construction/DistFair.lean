/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Model.Fairness
import MyMathlibProject.Weak.Step
import MyMathlibProject.Construction.TraceMap

/-!
# The fair distribution-monad construction

The fairness-aware analogue of `System.dist`. It keeps the distribution-monad state space
`PMF State` and the `hyperStep` transitions, but:

* **restricts the clustering** so that every successor belief is *resolvable* — this rules out
  *spurious fair deadlocks* (a belief stuck only because its states share no common fair label,
  while some state could still step fairly), the finite/halting obstruction; and
* **marks a step fair** iff its flattened target is realisable by an all-`F`-fair kernel (the
  `∃`-reading: "induced by fair transitions only").

The intended soundness result, under an **image-finiteness** assumption on `sys` (which lets
König's lemma close the infinite-run / stitching front), is

  `fairAchievableTraceDists F = fairAchievableTraceDists F.dist`.

The subset direction is trivial via the Dirac lift `s ↦ δ_s` (beliefs stay Dirac, nothing mixes);
the superset direction reconstructs a fair `sys`-execution from a fair `𝒟_f`-execution, with the
clustering restriction handling deadlocks and image-finiteness (König) handling infinite runs.
-/

open Stream'

namespace PLTS

variable {State Label : Type} [Silent Label]

/-! ### Belief predicates for the clustering restriction -/

/-- A belief `ν` has a **common fair label**: some label `l` at which *every* state in `ν.support`
enables a fair transition — so a fair `hyperStep` can leave `ν`. -/
def Fairness.CommonFairLabel {sys : System State Label} (F : Fairness sys) (ν : PMF State) : Prop :=
  ∃ l, ∀ s ∈ ν.support, ∃ μ, F.fair s l μ

/-- A belief `ν` is a **genuine fair deadlock**: every state in its support is a fair deadlock. -/
def Fairness.AllFairDeadlock {sys : System State Label} (F : Fairness sys) (ν : PMF State) : Prop :=
  ∀ s ∈ ν.support, F.FairDeadlock s

/-- A belief `ν` is **resolvable**: it can take a fair `hyperStep` (common fair label) or it is a
genuine fair deadlock. The clustering restriction forces every successor belief to be resolvable,
so no spurious fair deadlock is ever reachable and every reachable belief is either fairly-steppable
or a genuine (all-states) fair deadlock. Every Dirac `δ_s` is resolvable, so the restriction is
always dischargeable by clustering to Diracs. -/
def Fairness.Resolvable {sys : System State Label} (F : Fairness sys) (ν : PMF State) : Prop :=
  F.CommonFairLabel ν ∨ F.AllFairDeadlock ν

/-! ### The restricted system `𝒟_f(sys, F)` -/

/-- The **fair distribution-monad construction** `𝒟_f(sys, F)`: `System.dist` with the clustering
restriction. States are `PMF State`; a step `μ −l→ ω` is a `hyperStep` whose successor beliefs are
all resolvable. The state space and step relation depend on `F` because "resolvable" is a
fairness-aware condition. -/
noncomputable def System.distF (sys : System State Label) (F : Fairness sys) :
    System (PMF State) Label where
  init := PMF.pure sys.init
  step μ l ω := hyperStep sys μ l (ω.bind id) ∧ ∀ ν ∈ ω.support, F.Resolvable ν

@[inherit_doc]
scoped notation:max "𝒟f(" sys ", " F ")" => System.distF sys F

/-! ### The fair marking on `𝒟_f(sys, F)` -/

/-- The **fair marking** on `𝒟_f(sys, F)`: a step `μ −l→ ω` is fair iff it is a genuine step and its
flattened target `ω.bind id` is realisable by an all-`F`-fair kernel `p` (the `∃`-reading). External
steps are automatically fair (their underlying `sys`-steps are external, hence `F`-fair). -/
noncomputable def Fairness.dist {sys : System State Label} (F : Fairness sys) :
    Fairness (sys.distF F) where
  fair μ l ω :=
    (sys.distF F).step μ l ω ∧
      ∃ p : State → PMF (PMF State),
        (∀ s ∈ μ.support, ∀ μ' ∈ (p s).support, F.fair s l μ') ∧
          ω.bind id = μ.bind (fun s => (p s).bind id)
  step_of_fair := fun _ _ _ h => h.1
  fair_of_external := fun _ _ _ hstep hl => by
    obtain ⟨p, hp, heq⟩ := hstep.1
    exact ⟨hstep, p, fun s hs μ' hμ' => F.fair_of_external s _ μ' (hp s hs μ' hμ') hl, heq⟩

/-! ### The Dirac lift and the subset direction

The subset `fairAchievableTraceDists F ⊆ fairAchievableTraceDists F.dist` is witnessed by the
functional simulation `s ↦ δ_s = PMF.pure s`. Its fibres are singletons (`PMF.pure` is injective),
so the belief pushforward `mapBeliefExec PMF.pure` keeps every belief a Dirac and re-mixes nothing —
fairness transfers verbatim. No finiteness is needed. -/

/-- Every Dirac belief is resolvable, so the Dirac lift satisfies the clustering restriction and the
construction's `init` is valid. -/
theorem Fairness.resolvable_pure {sys : System State Label} (F : Fairness sys) (s : State) :
    F.Resolvable (PMF.pure s) := by
  classical
  by_cases h : F.FairEnabled s
  · obtain ⟨l, μ, hf⟩ := h
    exact Or.inl ⟨l, fun s' hs' => by
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact ⟨μ, hf⟩⟩
  · exact Or.inr fun s' hs' => by rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact h

/-- A `sys`-step lifts to a `𝒟_f(sys, F)`-step on the Dirac embedding: the flattened target is `μ`
(so it is a `hyperStep`) and its successor beliefs are Diracs (hence resolvable). -/
theorem System.distF_pure_step {sys : System State Label} (F : Fairness sys)
    {s : State} {l : Label} {μ : PMF State} (h : sys.step s l μ) :
    (sys.distF F).step (PMF.pure s) l (μ.map PMF.pure) := by
  classical
  refine ⟨?_, fun ν hν => ?_⟩
  · have hbm : (μ.map PMF.pure).bind id = μ := by rw [PMF.bind_map]; exact PMF.bind_pure μ
    rw [hbm]; exact hyperStep_pure_of_step h
  · rw [PMF.mem_support_map_iff] at hν
    obtain ⟨s', _, rfl⟩ := hν
    exact F.resolvable_pure s'

/-- On a **Dirac** belief the lifted marking's fair-enabledness coincides with the underlying one:
`𝒟_f`-fair transitions out of `δ_s` are exactly the `F`-fair transitions out of `s`. In particular a
Dirac `δ_s` is a `F.dist`-fair-deadlock iff `s` is an `F`-fair-deadlock — so the Dirac lift halts
exactly where `sys` does. -/
theorem Fairness.dist_fairEnabled_pure_iff {sys : System State Label} (F : Fairness sys)
    (s : State) : F.dist.FairEnabled (PMF.pure s) ↔ F.FairEnabled s := by
  classical
  constructor
  · rintro ⟨l, ω, _, p, hp, _⟩
    obtain ⟨μ', hμ'⟩ := (p s).support_nonempty
    exact ⟨l, μ', hp s (by rw [PMF.mem_support_pure_iff]) μ' hμ'⟩
  · rintro ⟨l, μ, hf⟩
    refine ⟨l, μ.map PMF.pure, System.distF_pure_step F (F.step_of_fair s l μ hf),
      fun _ => PMF.pure μ, ?_, ?_⟩
    · intro s' hs' μ' hμ'
      rw [PMF.mem_support_pure_iff] at hs' hμ'; subst hs'; subst hμ'; exact hf
    · rw [PMF.bind_map, PMF.pure_bind, PMF.pure_bind]
      exact PMF.bind_pure μ

/-- A Dirac `δ_s` is a `F.dist`-fair-deadlock iff `s` is an `F`-fair-deadlock. -/
theorem Fairness.dist_fairDeadlock_pure_iff {sys : System State Label} (F : Fairness sys)
    (s : State) : F.dist.FairDeadlock (PMF.pure s) ↔ F.FairDeadlock s := by
  unfold Fairness.FairDeadlock
  rw [F.dist_fairEnabled_pure_iff s]

/-! #### The generic injective resolved pushforward

The resolved analogue of `mapBeliefExec`. Given an injective, step-lifting `f : X → Y` we push a
resolved `sys_X`-execution forward to a resolved `sys_Y`-execution by applying `f` to every state
*and* every recorded distribution `μ` (via `μ.map f`). Because `f` is injective the fibre of every
`Y`-history is a singleton, so the pushforward re-mixes nothing and the resolved path-measure and
trace distribution transfer verbatim. We build it generically and specialise to `f := PMF.pure`
below to obtain the Dirac lift. -/

section ResolvedMapConstruction

-- The systems `sys_X`/`sys_Y` and `[Silent L]` are threaded as section variables but the pure
-- `rmap`/`stepmap` infrastructure lemmas do not use them; silence the over-inclusion linter (as in
-- `Construction/TraceMap.lean`).
set_option linter.unusedSectionVars false

variable {X Y L : Type} [Silent L] {sys_X : System X L} {sys_Y : System Y L}

/-- `PMF.pure` is injective (local copy; `Util.Pmf` is not on this file's import path). -/
private theorem pure_injective_local : Function.Injective (@PMF.pure X) := by
  intro a b h
  by_contra hne
  simpa [PMF.pure_apply, hne] using DFunLike.congr_fun h a

/-- `PMF.map f` is injective whenever `f` is (local copy). -/
private theorem pmf_map_injective {f : X → Y} (hf : Function.Injective f) :
    Function.Injective (PMF.map f) := by
  intro p q h
  ext a
  have h1 : (p.map f) (f a) = (q.map f) (f a) := by rw [h]
  rw [PMF.map_apply, PMF.map_apply] at h1
  rw [tsum_eq_single a (fun b hb => if_neg (fun heq => hb (hf heq).symm))] at h1
  rw [tsum_eq_single a (fun b hb => if_neg (fun heq => hb (hf heq).symm))] at h1
  rwa [if_pos rfl, if_pos rfl] at h1

/-- The pushforward map on resolved steps: push the recorded distribution and the sampled next
state forward along `f`, keeping the label. -/
noncomputable def stepmap (f : X → Y) : (L × PMF X) × X → (L × PMF Y) × Y :=
  fun p => ((p.1.1, p.1.2.map f), f p.2)

/-- The pushforward of a resolved execution along `f`: apply `f` to the initial state and
`stepmap f` to every recorded step. -/
noncomputable def rmap (f : X → Y) (r : ResolvedExec X L) : ResolvedExec Y L :=
  ⟨f r.init, r.trans.map (stepmap f)⟩

/-- `probOfR` depends only on the resolved history, not the termination proof. -/
theorem ResolvedProbabilisticExecution.probOfR_congr {Z : Type} {sys : System Z L}
    (pe : ResolvedProbabilisticExecution sys)
    (r r' : ResolvedExec Z L) (h : r = r') (hr : r.trans.Terminates) (hr' : r'.trans.Terminates) :
    pe.probOfR r hr = pe.probOfR r' hr' := by subst h; rfl

@[simp] theorem rmap_init (f : X → Y) (r : ResolvedExec X L) : (rmap f r).init = f r.init := rfl

theorem rmap_trans (f : X → Y) (r : ResolvedExec X L) :
    (rmap f r).trans = r.trans.map (stepmap f) := rfl

/-- `stepmap f` is injective when `f` is (both `f` and `PMF.map f` are injective). -/
theorem stepmap_injective {f : X → Y} (h_inj : Function.Injective f) :
    Function.Injective (stepmap (L := L) f) := by
  rintro ⟨⟨l₁, μ₁⟩, s₁⟩ ⟨⟨l₂, μ₂⟩, s₂⟩ h
  simp only [stepmap, Prod.mk.injEq] at h
  obtain ⟨⟨hl, hμ⟩, hs⟩ := h
  obtain rfl := hl
  obtain rfl := pmf_map_injective h_inj hμ
  obtain rfl := h_inj hs
  rfl

/-- A `Seq.map` of an injective function is injective (pointwise via `Stream'.Seq.ext`). -/
private theorem seq_map_injective {α β : Type} {g : α → β} (hg : Function.Injective g) :
    Function.Injective (fun s : Seq α => s.map g) := by
  intro s t h
  apply Stream'.Seq.ext
  intro n
  have hn := congr_arg (·.get? n) h
  simp only [Stream'.Seq.map_get?] at hn
  cases h1 : s.get? n with
  | none => cases h2 : t.get? n with
    | none => rfl
    | some b => rw [h1, h2] at hn; simp at hn
  | some a => cases h2 : t.get? n with
    | none => rw [h1, h2] at hn; simp at hn
    | some b => rw [h1, h2] at hn; simp only [Option.map_some, Option.some.injEq] at hn;
                rw [hg hn]

/-- `rmap f` is injective when `f` is. -/
theorem rmap_injective {f : X → Y} (h_inj : Function.Injective f) :
    Function.Injective (rmap (L := L) f) := by
  rintro ⟨i₁, t₁⟩ ⟨i₂, t₂⟩ h
  simp only [rmap, AlterSeq.mk.injEq] at h
  obtain ⟨hi, ht⟩ := h
  obtain rfl := h_inj hi
  obtain rfl := seq_map_injective (stepmap_injective h_inj) ht
  rfl

theorem rmap_terminatedAt_iff (f : X → Y) (r : ResolvedExec X L) (n : ℕ) :
    (rmap f r).trans.TerminatedAt n ↔ r.trans.TerminatedAt n := by
  unfold Stream'.Seq.TerminatedAt
  rw [rmap_trans, Stream'.Seq.map_get?, Option.map_eq_none_iff]

theorem rmap_terminates_iff (f : X → Y) (r : ResolvedExec X L) :
    (rmap f r).trans.Terminates ↔ r.trans.Terminates := by
  rw [rmap_trans]; exact Stream'.Seq.terminates_map_iff

theorem rmap_stateAt (f : X → Y) (r : ResolvedExec X L) (n : ℕ) :
    (rmap f r).stateAt n = (r.stateAt n).map f := by
  cases n with
  | zero => rfl
  | succ k =>
    change ((r.trans.map (stepmap f)).get? k).map Prod.snd = ((r.trans.get? k).map Prod.snd).map f
    rw [Stream'.Seq.map_get?]
    cases r.trans.get? k with
    | none => rfl
    | some p => rfl

/-- **Key.** The plain image of the resolved pushforward is the pushforward of the plain image —
so traces/tightness transfer through `AlterSeq.trace_map` / `AlterSeq.isTight_map`. -/
theorem rmap_toExec (f : X → Y) (r : ResolvedExec X L) :
    (rmap f r).toExec = (r.toExec).map f := by
  unfold ResolvedExec.toExec
  simp only [rmap, AlterSeq.map, AlterSeq.mk.injEq, true_and]
  rw [← Stream'.Seq.map_comp, ← Stream'.Seq.map_comp]
  rfl

theorem rmap_append_singleton (f : X → Y) (r : ResolvedExec X L)
    (last : (L × PMF X) × X) :
    rmap f ⟨r.init, r.trans.append (Seq.cons last Seq.nil)⟩
      = ⟨f r.init, (rmap f r).trans.append (Seq.cons (stepmap f last) Seq.nil)⟩ := by
  simp only [rmap, Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil]

/-- `R` is in the image of `rmap f`. -/
def RoundTrips (f : X → Y) (R : ResolvedExec Y L) : Prop := ∃ r : ResolvedExec X L, rmap f r = R

theorem roundTrips_rmap (f : X → Y) (r : ResolvedExec X L) : RoundTrips f (rmap f r) := ⟨r, rfl⟩

open Classical in
/-- The lifted resolved scheduler: on a `Y`-history `R` in the image of `rmap f`, emit the
`mapEmit f`-pushforward of `pe`'s emission at the (unique, by injectivity) `X`-preimage; off the
image, halt. -/
noncomputable def resolvedMapSched (f : X → Y) (_h_inj : Function.Injective f)
    (h_step : ∀ s l μ, sys_X.step s l μ → sys_Y.step (f s) l (μ.map f))
    (pe : ResolvedProbabilisticExecution sys_X) : ResolvedScheduler sys_Y where
  next R := if h : RoundTrips f R then (pe.scheduler.next h.choose).map (mapEmit f)
    else PMF.pure none
  valid := by
    intro R n y hterm hstate l ν hsupp
    by_cases hRT : RoundTrips f R
    · rw [dif_pos hRT] at hsupp
      set r₀ := hRT.choose with hr₀
      have hReq : rmap f r₀ = R := hRT.choose_spec
      rw [PMF.mem_support_map_iff] at hsupp
      obtain ⟨o, ho, hoν⟩ := hsupp
      -- `o = some (l, μ)` with `ν = μ.map f`.
      obtain ⟨μ, hμmem, hνeq⟩ : ∃ μ : PMF X, o = some (l, μ) ∧ ν = μ.map f := by
        cases o with
        | none => simp [mapEmit] at hoν
        | some lμ =>
          obtain ⟨l', μ⟩ := lμ
          simp only [mapEmit, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hoν
          exact ⟨μ, by rw [hoν.1], hoν.2.symm⟩
      -- pull `hstate`/`hterm` back to `r₀`.
      have hstateX : (r₀.stateAt n).map f = some y := by
        rw [← rmap_stateAt f r₀ n, hReq]; exact hstate
      obtain ⟨x, hxn, hfx⟩ : ∃ x : X, r₀.stateAt n = some x ∧ f x = y := by
        cases hc : r₀.stateAt n with
        | none => rw [hc] at hstateX; simp at hstateX
        | some x => rw [hc] at hstateX; exact ⟨x, rfl, by simpa using hstateX⟩
      have htermX : r₀.trans.TerminatedAt n :=
        (rmap_terminatedAt_iff f r₀ n).mp (by rw [hReq]; exact hterm)
      have hμne : pe.scheduler.next r₀ (some (l, μ)) ≠ 0 := by
        rw [← hμmem]; exact (PMF.mem_support_iff _ _).mp ho
      have hstepX : sys_X.step x l μ :=
        pe.scheduler.valid r₀ n x htermX hxn l μ ((PMF.mem_support_iff _ _).mpr hμne)
      have hres := h_step x l μ hstepX
      rw [hfx, ← hνeq] at hres
      exact hres
    · rw [dif_neg hRT, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
      exact absurd rfl hsupp

/-- The lifted resolved probabilistic execution: pushforward initial distribution + lifted
scheduler. -/
noncomputable def resolvedMapExec (f : X → Y) (h_inj : Function.Injective f)
    (h_step : ∀ s l μ, sys_X.step s l μ → sys_Y.step (f s) l (μ.map f))
    (pe : ResolvedProbabilisticExecution sys_X) : ResolvedProbabilisticExecution sys_Y :=
  ⟨pe.initState.map f, resolvedMapSched f h_inj h_step pe⟩

open Classical in
/-- On a history in the image of `rmap f`, the lifted scheduler's emission is the `mapEmit f`
pushforward at the (unique) preimage `r`. -/
theorem resolvedMapSched_next_rmap (f : X → Y) (h_inj : Function.Injective f)
    (h_step : ∀ s l μ, sys_X.step s l μ → sys_Y.step (f s) l (μ.map f))
    (pe : ResolvedProbabilisticExecution sys_X) (r : ResolvedExec X L) :
    (resolvedMapSched f h_inj h_step pe).next (rmap f r)
      = (pe.scheduler.next r).map (mapEmit f) := by
  have hRT : RoundTrips f (rmap f r) := roundTrips_rmap f r
  have hchoose : hRT.choose = r := rmap_injective h_inj hRT.choose_spec
  change (if h : RoundTrips f (rmap f r) then _ else _) = _
  rw [dif_pos hRT, hchoose]

/-- `(μ.map f) (f s') = μ s'` for injective `f` (the fibre of `f s'` is the single point `s'`). -/
theorem map_apply_f {f : X → Y} (h_inj : Function.Injective f) (μ : PMF X) (s' : X) :
    (μ.map f) (f s') = μ s' := by
  rw [PMF.map_apply, tsum_eq_single s' (fun b hb => if_neg (fun heq => hb (h_inj heq).symm)),
    if_pos rfl]

/-- `((σ.map (mapEmit f)) (some (l, μ.map f))) = σ (some (l, μ))` for injective `f`. -/
theorem mapEmit_apply_some {f : X → Y} (h_inj : Function.Injective f)
    (σ : PMF (Option (L × PMF X))) (l : L) (μ : PMF X) :
    (σ.map (mapEmit f)) (some (l, μ.map f)) = σ (some (l, μ)) := by
  rw [PMF.map_apply, tsum_eq_single (some (l, μ)) ?_]
  · rw [show mapEmit f (some (l, μ)) = some (l, μ.map f) from rfl, if_pos rfl]
  · intro o ho
    refine if_neg (fun heq => ho ?_)
    cases o with
    | none => simp [mapEmit] at heq
    | some lμ =>
      obtain ⟨l', μ'⟩ := lμ
      simp only [mapEmit, Option.map_some, Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, hμ⟩ := heq
      rw [pmf_map_injective h_inj hμ]

/-- The resolved kernel transfers along `rmap f` / `stepmap f`. -/
theorem rkernel_rmap (f : X → Y) (h_inj : Function.Injective f)
    (h_step : ∀ s l μ, sys_X.step s l μ → sys_Y.step (f s) l (μ.map f))
    (pe : ResolvedProbabilisticExecution sys_X) (r : ResolvedExec X L)
    (step : (L × PMF X) × X) :
    (resolvedMapExec f h_inj h_step pe).rkernel (rmap f r) (stepmap f step)
      = pe.rkernel r step := by
  obtain ⟨⟨l, μ⟩, s'⟩ := step
  unfold ResolvedProbabilisticExecution.rkernel
  change (resolvedMapExec f h_inj h_step pe).scheduler.next (rmap f r) (some (l, μ.map f))
      * (μ.map f) (f s') = _
  change (resolvedMapSched f h_inj h_step pe).next (rmap f r) (some (l, μ.map f)) * _ = _
  rw [resolvedMapSched_next_rmap f h_inj h_step pe r, mapEmit_apply_some h_inj _ l μ,
    map_apply_f h_inj μ s']

/-- The lifted initial distribution at `f x` recovers the original initial mass at `x`. -/
theorem resolvedMapExec_initState_apply (f : X → Y) (h_inj : Function.Injective f)
    (h_step : ∀ s l μ, sys_X.step s l μ → sys_Y.step (f s) l (μ.map f))
    (pe : ResolvedProbabilisticExecution sys_X) (x : X) :
    (resolvedMapExec f h_inj h_step pe).initState (f x) = pe.initState x := by
  change (pe.initState.map f) (f x) = pe.initState x
  exact map_apply_f h_inj pe.initState x

/-- **Resolved path-measure transfer.** The lifted path-measure of `rmap f r` equals the original
path-measure of `r`. Cons-end (`exists_split_last`) length induction, using the kernel transfer
`rkernel_rmap` and the initial-mass transfer at the base. -/
theorem probOfR_rmap (f : X → Y) (h_inj : Function.Injective f)
    (h_step : ∀ s l μ, sys_X.step s l μ → sys_Y.step (f s) l (μ.map f))
    (pe : ResolvedProbabilisticExecution sys_X) (r : ResolvedExec X L)
    (h : r.trans.Terminates) :
    (resolvedMapExec f h_inj h_step pe).probOfR (rmap f r) ((rmap_terminates_iff f r).mpr h)
      = pe.probOfR r h := by
  set peY := resolvedMapExec f h_inj h_step pe with hpeY
  suffices H : ∀ n (r : ResolvedExec X L) (h : r.trans.Terminates),
      (r.trans.toList h).length = n →
      peY.probOfR (rmap f r) ((rmap_terminates_iff f r).mpr h) = pe.probOfR r h from H _ r h rfl
  intro n
  induction n with
  | zero =>
    intro r h hlen
    have htoList : r.trans.toList h = [] := List.length_eq_zero_iff.mp hlen
    obtain ⟨i, t⟩ := r
    have h_nil : t = Seq.nil := by
      have hh := Stream'.Seq.ofList_toList t h
      rw [htoList, Stream'.Seq.ofList_nil] at hh
      exact hh.symm
    subst h_nil
    have hrmap_nil : rmap f (⟨i, Seq.nil⟩ : ResolvedExec X L) = ⟨f i, Seq.nil⟩ := by
      simp only [rmap, Stream'.Seq.map_nil]
    rw [peY.probOfR_congr (rmap f ⟨i, Seq.nil⟩) ⟨f i, Seq.nil⟩ hrmap_nil _
        Stream'.Seq.terminates_nil, peY.probOfR_nil (f i), pe.probOfR_nil i]
    exact resolvedMapExec_initState_apply f h_inj h_step pe i
  | succ k ih =>
    intro r h hlen
    have hne : r.trans.toList h ≠ [] := by
      intro hnil; rw [hnil, List.length_nil] at hlen; exact Nat.succ_ne_zero k hlen.symm
    obtain ⟨prev, last, hprev, hsplit, hprevlist, -⟩ :=
      Stream'.Seq.exists_split_last r.trans h hne
    have happ : (prev.append (Seq.cons last Seq.nil)).Terminates := hsplit ▸ h
    have hr_eq : r = ⟨r.init, prev.append (Seq.cons last Seq.nil)⟩ := by
      obtain ⟨ri, rt⟩ := r; exact congrArg (AlterSeq.mk ri) hsplit
    have hlen_prev : (prev.toList hprev).length = k := by
      have h1 : (prev.toList hprev).length = (r.trans.toList h).length - 1 := by
        rw [hprevlist, List.length_dropLast]
      omega
    have hprevY : (rmap f ⟨r.init, prev⟩).trans.Terminates :=
      (rmap_terminates_iff f ⟨r.init, prev⟩).mpr hprev
    -- the prefix factor by IH; the last kernel by `rkernel_rmap`.
    have hprefix : peY.probOfR (rmap f ⟨r.init, prev⟩) hprevY
        = pe.probOfR ⟨r.init, prev⟩ hprev := ih ⟨r.init, prev⟩ hprev hlen_prev
    have hkern : peY.rkernel (rmap f ⟨r.init, prev⟩) (stepmap f last)
        = pe.rkernel ⟨r.init, prev⟩ last :=
      rkernel_rmap f h_inj h_step pe ⟨r.init, prev⟩ last
    -- LHS: peel the last step off the pushforward.
    have hLHS : peY.probOfR (rmap f r) ((rmap_terminates_iff f r).mpr h)
        = peY.probOfR (rmap f ⟨r.init, prev⟩) hprevY
          * peY.rkernel (rmap f ⟨r.init, prev⟩) (stepmap f last) := by
      rw [peY.probOfR_congr (rmap f r) (rmap f ⟨r.init, prev.append (Seq.cons last Seq.nil)⟩)
        (by rw [hr_eq]) ((rmap_terminates_iff f r).mpr h)
        ((rmap_terminates_iff f _).mpr happ)]
      rw [peY.probOfR_congr (rmap f ⟨r.init, prev.append (Seq.cons last Seq.nil)⟩)
        ⟨f r.init, (rmap f ⟨r.init, prev⟩).trans.append (Seq.cons (stepmap f last) Seq.nil)⟩
        (rmap_append_singleton f ⟨r.init, prev⟩ last) ((rmap_terminates_iff f _).mpr happ)
        (by rw [← rmap_append_singleton f ⟨r.init, prev⟩ last];
            exact (rmap_terminates_iff f _).mpr happ)]
      exact peY.probOfR_append_singleton (rmap f ⟨r.init, prev⟩).init
        (rmap f ⟨r.init, prev⟩).trans hprevY (stepmap f last) _
    -- RHS: peel the last step off `r`.
    have hRHS : pe.probOfR r h
        = pe.probOfR ⟨r.init, prev⟩ hprev * pe.rkernel ⟨r.init, prev⟩ last := by
      rw [pe.probOfR_congr r ⟨r.init, prev.append (Seq.cons last Seq.nil)⟩ hr_eq h happ]
      exact pe.probOfR_append_singleton r.init prev hprev last happ
    rw [hLHS, hRHS, hprefix, hkern]

/-- **Support surjectivity.** A `Y`-history with nonzero lifted path-measure is in the image of
`rmap f`. Cons-end length induction: the base uses `PMF.mem_support_map_iff` on the pushforward
initial distribution; the step peels the last transition, applies the IH to the prefix, and uses
`resolvedMapSched_next_rmap` and `PMF.mem_support_map_iff` on the emission to recover the step. -/
theorem probOfR_ne_zero_imp_image (f : X → Y) (h_inj : Function.Injective f)
    (h_step : ∀ s l μ, sys_X.step s l μ → sys_Y.step (f s) l (μ.map f))
    (pe : ResolvedProbabilisticExecution sys_X) (R : ResolvedExec Y L)
    (hFin : R.trans.Terminates)
    (hne : (resolvedMapExec f h_inj h_step pe).probOfR R hFin ≠ 0) :
    ∃ r : ResolvedExec X L, rmap f r = R := by
  set peY := resolvedMapExec f h_inj h_step pe with hpeY
  suffices H : ∀ n (R : ResolvedExec Y L) (hFin : R.trans.Terminates),
      (R.trans.toList hFin).length = n → peY.probOfR R hFin ≠ 0 →
      ∃ r : ResolvedExec X L, rmap f r = R by
    exact H _ R hFin rfl hne
  intro n
  induction n with
  | zero =>
    intro R hFin hlen hRne
    have htoList : R.trans.toList hFin = [] := List.length_eq_zero_iff.mp hlen
    obtain ⟨Ri, Rt⟩ := R
    have h_nil : Rt = Seq.nil := by
      have hh := Stream'.Seq.ofList_toList Rt hFin
      rw [htoList, Stream'.Seq.ofList_nil] at hh
      exact hh.symm
    subst h_nil
    rw [peY.probOfR_nil Ri] at hRne
    -- `peY.initState Ri = (pe.initState.map f) Ri ≠ 0`, so `Ri` is in the image of `f`.
    have hmem : Ri ∈ (pe.initState.map f).support := (PMF.mem_support_iff _ _).mpr hRne
    rw [PMF.mem_support_map_iff] at hmem
    obtain ⟨x, _, hfx⟩ := hmem
    refine ⟨⟨x, Seq.nil⟩, ?_⟩
    simp only [rmap, Stream'.Seq.map_nil, hfx]
  | succ k ih =>
    intro R hFin hlen hRne
    have hne' : R.trans.toList hFin ≠ [] := by
      intro hnil; rw [hnil, List.length_nil] at hlen; exact Nat.succ_ne_zero k hlen.symm
    obtain ⟨prev, last, hprev, hsplit, hprevlist, -⟩ :=
      Stream'.Seq.exists_split_last R.trans hFin hne'
    have happ : (prev.append (Seq.cons last Seq.nil)).Terminates := hsplit ▸ hFin
    have hR_eq : R = ⟨R.init, prev.append (Seq.cons last Seq.nil)⟩ := by
      obtain ⟨Ri, Rt⟩ := R; exact congrArg (AlterSeq.mk Ri) hsplit
    have hlen_prev : (prev.toList hprev).length = k := by
      have h1 : (prev.toList hprev).length = (R.trans.toList hFin).length - 1 := by
        rw [hprevlist, List.length_dropLast]
      omega
    -- factor the path-measure through the last step.
    rw [peY.probOfR_congr R ⟨R.init, prev.append (Seq.cons last Seq.nil)⟩ hR_eq hFin happ,
      peY.probOfR_append_singleton R.init prev hprev last happ] at hRne
    have hprefixne : peY.probOfR ⟨R.init, prev⟩ hprev ≠ 0 := fun h0 => hRne (by rw [h0, zero_mul])
    have hkernne : peY.rkernel ⟨R.init, prev⟩ last ≠ 0 := fun h0 => hRne (by rw [h0, mul_zero])
    -- apply IH to the prefix.
    obtain ⟨r', hr'⟩ := ih ⟨R.init, prev⟩ hprev hlen_prev hprefixne
    -- recover the last step from the kernel via `resolvedMapSched_next_rmap`.
    obtain ⟨⟨l, ν⟩, y'⟩ := last
    unfold ResolvedProbabilisticExecution.rkernel at hkernne
    have hemitne : peY.scheduler.next ⟨R.init, prev⟩ (some (l, ν)) ≠ 0 :=
      fun h0 => hkernne (by rw [h0, zero_mul])
    have hνy'ne : ν y' ≠ 0 := fun h0 => hkernne (by rw [h0, mul_zero])
    -- rewrite the scheduler emission at `⟨R.init, prev⟩ = rmap f r'`.
    rw [← hr', show peY.scheduler.next = (resolvedMapSched f h_inj h_step pe).next from rfl,
      resolvedMapSched_next_rmap f h_inj h_step pe r'] at hemitne
    have hmem : some (l, ν) ∈ ((pe.scheduler.next r').map (mapEmit f)).support :=
      (PMF.mem_support_iff _ _).mpr hemitne
    rw [PMF.mem_support_map_iff] at hmem
    obtain ⟨o, _, hoeq⟩ := hmem
    obtain ⟨μ, hν⟩ : ∃ μ : PMF X, o = some (l, μ) ∧ ν = μ.map f := by
      cases o with
      | none => simp [mapEmit] at hoeq
      | some lμ =>
        obtain ⟨l', μ⟩ := lμ
        simp only [mapEmit, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hoeq
        exact ⟨μ, by rw [hoeq.1], hoeq.2.symm⟩
    obtain ⟨-, hνeq⟩ := hν
    -- `ν y' ≠ 0` and `ν = μ.map f` give `y'` in the image of `f`.
    have hy'mem : y' ∈ (μ.map f).support := by
      rw [← hνeq]; exact (PMF.mem_support_iff _ _).mpr hνy'ne
    rw [PMF.mem_support_map_iff] at hy'mem
    obtain ⟨x', _, hfx'⟩ := hy'mem
    -- assemble the preimage resolved execution.
    refine ⟨⟨r'.init, r'.trans.append (Seq.cons ((l, μ), x') Seq.nil)⟩, ?_⟩
    rw [rmap_append_singleton f r' ((l, μ), x')]
    -- `stepmap f ((l,μ),x') = ((l, ν), y')` and `rmap f r' = ⟨R.init, prev⟩`.
    have hstepmap : stepmap f ((l, μ), x') = ((l, ν), y') := by
      simp only [stepmap]; rw [hfx', hνeq]
    have hinit' : f r'.init = R.init := congrArg AlterSeq.init hr'
    have htrans' : (rmap f r').trans = prev := congrArg AlterSeq.trans hr'
    rw [hstepmap, hinit', htrans', hR_eq]

/-- **Resolved trace-distribution transfer.** The lifted resolved trace distribution equals the
original: traces, tightness and termination are `f`-invariant (`rmap_toExec` + `AlterSeq.trace_map`
/ `AlterSeq.isTight_map` / `rmap_terminates_iff`), the path-measure transfers (`probOfR_rmap`), and
`rmap f` is injective onto the nonzero support (`probOfR_ne_zero_imp_image`). -/
theorem resolvedMapExec_traceProbR (f : X → Y) (h_inj : Function.Injective f)
    (h_step : ∀ s l μ, sys_X.step s l μ → sys_Y.step (f s) l (μ.map f))
    (pe : ResolvedProbabilisticExecution sys_X)
    (_h_init_X : pe.initState = PMF.pure sys_X.init) (_h_init : f sys_X.init = sys_Y.init)
    (τ : Seq L) :
    (resolvedMapExec f h_inj h_step pe).traceProbR τ = pe.traceProbR τ := by
  set peY := resolvedMapExec f h_inj h_step pe with hpeY
  unfold ResolvedProbabilisticExecution.traceProbR
  -- Biject the (nonzero-mass) tight-`X` runs onto the tight-`Y` runs via `rmap f`.
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun x : {x : {r : ResolvedExec X L //
            r.trans.Terminates ∧ sys_X.trace r.toExec = τ ∧ sys_X.IsTight r.toExec} //
            pe.probOfR x.1 x.2.1 ≠ 0} =>
      (⟨rmap f x.1.1,
        (rmap_terminates_iff f x.1.1).mpr x.1.2.1,
        by rw [rmap_toExec, AlterSeq.trace_map]; exact x.1.2.2.1,
        by rw [rmap_toExec]; exact (AlterSeq.isTight_map f x.1.1.toExec).mpr x.1.2.2.2⟩ :
        {R : ResolvedExec Y L //
          R.trans.Terminates ∧ sys_Y.trace R.toExec = τ ∧ sys_Y.IsTight R.toExec}))
    ?inj ?surj ?val
  case inj =>
    rintro ⟨⟨r₁, hr₁⟩, hne₁⟩ ⟨⟨r₂, hr₂⟩, hne₂⟩ hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext (Subtype.ext (rmap_injective h_inj hab))
  case surj =>
    rintro ⟨R, hRterm, hRtrace, hRtight⟩ hRne
    rw [Function.mem_support] at hRne
    -- `R` has nonzero lifted path-measure, so it is in the image of `rmap f`.
    obtain ⟨r, hr⟩ := probOfR_ne_zero_imp_image f h_inj h_step pe R hRterm hRne
    have hrterm : r.trans.Terminates := (rmap_terminates_iff f r).mp (by rw [hr]; exact hRterm)
    have hrtrace : sys_X.trace r.toExec = τ := by
      rw [← AlterSeq.trace_map (sys_Y := sys_Y) f r.toExec, ← rmap_toExec, hr]; exact hRtrace
    have hrtight : sys_X.IsTight r.toExec := by
      rw [← AlterSeq.isTight_map (sys_Y := sys_Y) f r.toExec, ← rmap_toExec, hr]; exact hRtight
    -- value nonzero: pull `hRne` through `probOfR_rmap`.
    have hval : peY.probOfR (rmap f r) ((rmap_terminates_iff f r).mpr hrterm)
        = pe.probOfR r hrterm := probOfR_rmap f h_inj h_step pe r hrterm
    have hrne : pe.probOfR r hrterm ≠ 0 := by
      intro h0
      apply hRne
      rw [peY.probOfR_congr R (rmap f r) hr.symm hRterm ((rmap_terminates_iff f r).mpr hrterm),
        hval, h0]
    refine ⟨⟨⟨r, hrterm, hrtrace, hrtight⟩, hrne⟩, ?_⟩
    exact Subtype.ext hr
  case val =>
    rintro ⟨⟨r, hrterm, hrtrace, hrtight⟩, hrne⟩
    exact probOfR_rmap f h_inj h_step pe r hrterm

end ResolvedMapConstruction

/-! #### The Dirac lift, specialised to `f := PMF.pure` -/

/-- The **Dirac lift** of a resolved `sys`-execution to a resolved `𝒟_f(sys, F)`-execution: the
resolved pushforward along the injective, step-lifting `s ↦ δ_s = PMF.pure s`. Every belief stays a
Dirac and nothing re-mixes, so the resolved path-measure and trace distribution transfer. -/
noncomputable def ResolvedProbabilisticExecution.distFDiracLift {sys : System State Label}
    (pe : ResolvedProbabilisticExecution sys) (F : Fairness sys) :
    ResolvedProbabilisticExecution (sys.distF F) :=
  resolvedMapExec PMF.pure pure_injective_local (fun _ _ _ h => sys.distF_pure_step F h) pe

@[simp] theorem ResolvedProbabilisticExecution.distFDiracLift_initState {sys : System State Label}
    (pe : ResolvedProbabilisticExecution sys) (F : Fairness sys)
    (h_init : pe.initState = PMF.pure sys.init) :
    (pe.distFDiracLift F).initState = PMF.pure (sys.distF F).init := by
  change pe.initState.map PMF.pure = PMF.pure (sys.distF F).init
  rw [h_init, PMF.pure_map]
  rfl

/-- The Dirac lift realises the same resolved trace distribution as `pe`. -/
theorem ResolvedProbabilisticExecution.distFDiracLift_traceProbR {sys : System State Label}
    (pe : ResolvedProbabilisticExecution sys) (F : Fairness sys)
    (h_init : pe.initState = PMF.pure sys.init) (τ : Seq Label) :
    (pe.distFDiracLift F).traceProbR τ = pe.traceProbR τ :=
  resolvedMapExec_traceProbR PMF.pure pure_injective_local
    (fun _ _ _ h => sys.distF_pure_step F h) pe h_init rfl τ

/-- **Subset direction of the fair `dist_traceProb` equivalence.** Every fairly-achievable trace
distribution of `sys` is fairly-achievable on `𝒟_f(sys, F)`, witnessed by the (resolved) Dirac lift.
No finiteness is needed. The only fairness content is the transfer `distFDiracLift_isFair`: the
Dirac lift of a fair execution is fair — provided as a hypothesis here, since its proof is the
resolved-execution consistency correspondence for the (injective, non-mixing) Dirac pushforward. Its
*local* ingredients are already discharged above: `dist_fairDeadlock_pure_iff` (halting matches),
`distF_pure_step` (steps lift), and `resolvable_pure` (restriction satisfied). -/
theorem fairAchievableTraceDists_subset_distF {sys : System State Label} (F : Fairness sys)
    (distFDiracLift_isFair : ∀ pe : ResolvedProbabilisticExecution sys,
      pe.initState = PMF.pure sys.init → pe.IsFair F → (pe.distFDiracLift F).IsFair F.dist) :
    fairAchievableTraceDists F ⊆ fairAchievableTraceDists F.dist := by
  rintro D ⟨pe, h_init, h_fair, h_tp⟩
  exact ⟨pe.distFDiracLift F, pe.distFDiracLift_initState F h_init,
    distFDiracLift_isFair pe h_init h_fair,
    fun τ => (pe.distFDiracLift_traceProbR F h_init τ).trans (h_tp τ)⟩

/-! ### The reverse inclusion `⊇`, and a note on the resolved semantics

Only the Dirac-lift `⊆` (`fairAchievableTraceDists_subset_distF`) is proven here.

⚠️ **The analysis below was written for the former *plain*-scheduler reading of
`fairAchievableTraceDists`.** Now that `fairAchievableTraceDists` is defined via *resolved*-history
schedulers (`Model/Fairness.lean`), its separation argument no longer applies: the very
belief/mass-splitting "memory" that makes `𝒟f` more expressive than a *plain* `sys`-scheduler is
*also* available to a resolved `sys`-scheduler (which reads its own `μ`-history and alternates —
exactly the `Model/ResolvedGap.lean` construction). So the witness `D` below *is* achievable by a
fair resolved `sys`-execution, i.e. `D ∈ fairAchievableTraceDists F`; the strict separation holds
only against the *plain* set `fairAchievableTraceDistsPlain F`. Whether
`fairAchievableTraceDists F = fairAchievableTraceDists F.dist` is therefore now **open** — plausibly
an *equality*, since resolved-history power and `𝒟f`-belief power coincide. The plain-scheduler
discussion is kept below only as historical context (read `fairAchievableTraceDists` there as the
plain `fairAchievableTraceDistsPlain`).

**Why `𝒟f` is more expressive than a *plain* scheduler: mass-splitting records hidden randomness.**
A `𝒟f`-step `μ −l→ ω`
has `ω : PMF (PMF State)`, and by `System.distF` it depends on `ω` only through `ω.bind id`. So from
`δ_{q_0}` the scheduler may take a probabilistic step and choose to MERGE it into one successor
belief or to SPLIT it into several — recording, in the *belief weights*, which branch was taken. A
plain `sys`-scheduler has no such memory. This is exactly the resolved-scheduler power exploited by
the finite-branching counterexample in `Model/ResolvedScheduler.lean`.

**Gadget** (image-finite). States `q_n`, `q'_n`, deadlock `b`; `q_0` initial. From `q_n`, two silent
(`τ`) transitions, both landing in `{q_{n+1}, q'_n}`: fair `μ_A = ½δ_{q_{n+1}} + ½δ_{q'_n}` (exits
w.p. ½), unfair `μ_B = ⅔δ_{q_{n+1}} + ⅓δ_{q'_n}` (exits w.p. ⅓). Each `q'_n` has an external
transition labelled `n` to `b`, AND a fair `τ`-self-loop `q'_n → δ_{q'_n}`. The self-loop is
essential: a mixed belief `a·δ_{q_{n+1}} + b·δ_{q'_n}` needs a *common fair label* to be
`Resolvable`, and `τ` is it (both `q_{n+1}` and `q'_n` fair-enable `τ`); being a self-loop, it lets
the run split off the pure Dirac belief `δ_{q'_n}` (Resolvable) to emit `n` (a `→ b` internal
transition would instead drain the exit mass silently).

**Resolved/belief witness.** A fair `𝒟f`-execution achieving the mixture `D`:
1. at `δ_{q_0}`, SPLIT the coin into the belief-branches `½δ_{q_1}+½δ_{q'_0}` and
   `⅔δ_{q_1}+⅓δ_{q'_0}` (the belief weights record the coin);
2. in each branch ALTERNATE fair/unfair hypersteps (the branch is visible in the belief), splitting
   off `δ_{q'_k}` to emit `k` as mass exits;
3. every infinite belief-run alternates ⇒ ∞ `F.dist`-fair steps ⇒ fair (a `μ_B`-hyperstep is
   genuinely `F.dist`-unfair: its flattened `⅔/⅓` target is realizable by no all-`F`-fair kernel —
   `μ_A`'s `½/½` is the only fair one).
Its trace is the ½/½ mixture `D`, so `D ∈ fairAchievableTraceDists F.dist`.

**No fair `sys`-execution achieves `D`** (see `Model/ResolvedScheduler.lean`). After `k` non-exit
steps the `sys`-history is "advanced `k` times", so a plain scheduler emits `μ_A` w.p. `α_k` with
exit rate `ρ_k = ½·α_k + ⅓·(1−α_k)`. Sure-fairness — killing the all-`μ_B` advancing run
`q_0→q_1→⋯`, which never reaches any `q'_k` — forces `ρ_k = ½` at infinitely many `k`; but `D` pins
`ρ_k ∈ (⅓,½)` strictly for all `k` (a genuine ½/½ posterior mixture). Incompatible, so
`D ∉ fairAchievableTraceDistsPlain F` (`Model/ResolvedScheduler.lean`) — but, as noted above,
`D ∈ fairAchievableTraceDists F` under the resolved semantics now in force.

**Consequence.** `ProbabilisticExecution.lowerFair_inf_fair` and its residual
`exists_coherent_decoration` are UNPROVABLE (false), not merely hard; the whole `lowerFair`
fair-reconstruction has been removed. What remains proven is the true `⊆` direction (the Dirac lift
`fairAchievableTraceDists_subset_distF`) and the trace-equivalence — the fair sets differ strictly.
-/

end PLTS
