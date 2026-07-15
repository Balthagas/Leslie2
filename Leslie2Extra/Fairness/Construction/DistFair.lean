/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2Extra.Fairness.Model.Fairness
import Leslie2.Weak.Step
import Leslie2.Simulation.TraceMap

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

/-! ### The lowering Markov chain

The reverse inclusion `fairAchievableTraceDists F.dist ⊆ fairAchievableTraceDists F` reconstructs a
fair `sys`-execution from a fair `𝒟f(sys,F)`-execution by an **algorithmic disintegration**, in the
spirit of the weak-closure unfolding (`Expansion/Algorithm.lean`). Given a resolved-history
scheduler `s` on `𝒟f(sys,F)` we run a Markov chain whose state (`LowerConfig`) is a pair of coupled
resolved executions advanced *in lockstep*, together with the pending emission `h = s(de)`:

* `de : ResolvedExec (PMF State) Label` — the abstract `𝒟f`-run; steps recorded as `((l, ω), dq)`
  with `ω : PMF (PMF State)` the emitted next-belief distribution and `dq : PMF State` the sampled
  next belief;
* `e  : ResolvedExec State Label` — the concrete `sys`-run; steps recorded as `((l, μ'), q)`;
* `h  : Option (Label × PMF (PMF State))` — the pending `𝒟f`-emission (`none` = halt).

The **critical invariant** (`Coupled`) is `last e ∈ (last de).support`.

**One instruction**, from a state with pending emission `h = some (l, ω)`:

1. `t = (l, μ')` — the concrete transition out of `qₚ := last e`: a *deterministic* single
   `sys`-step chosen from the fairness data of the emission (`tOutcome`), `F.fair`-fair whenever the
   emission is `F.dist`-fair and plain otherwise. This clause carries `inf_fair` downward.
2. `e` **first**: sample `q ~ μ'`, append `((l, μ'), q)`.
3. `de` **follows**: sample `dq ~ ω` reweighted by `dq(q) / μ'(q)`, append `((l, ω), dq)`. Choosing
   `dq` *after* `q`, with weight `∝ dq(q)`, restores `q ∈ dq.support` by construction — so the
   invariant can never be stranded.
4. draw the next pending emission `h' = s(de')`.

The chain is deliberately **sub-stochastic**: the abstract marginal of one instruction is `pe`'s
kernel `s(de)(l,ω)·ω(dq)` tilted by the *evidence factor* `dq(μ'.support)` — the fraction of the
belief branch that the single concrete step can physically reach. This evidence telescopes over a
run and is meant to be renormalised away by the concrete scheduler's `reachDep/reachArr` Bayes
ratio, built later. In `LowerStep` the `μ'(q)` of step 2 cancels the `1/μ'(q)` of step 3, so
`reachProb` stays a clean product.

Only the chain and its reaching probability are defined here; the concrete resolved scheduler and
the trace/fairness soundness are deferred. -/

section LoweringChain

variable {sys : System State Label}

/-- The last state of a finite alternating sequence (its `endState`), with `init` as junk on the
non-terminating executions the chain never reaches. -/
noncomputable def lastStateOf {S L : Type} (e : AlterSeq S L) : S := by
  classical
  exact if h : e.trans.Terminates then e.endState h else e.init

/-- The recorded transition-distribution `μ` of the last step of a resolved `sys`-execution
(`init`'s Dirac as junk when there are no transitions / the run is infinite). The chain reads the
*sampled* `μ'` off `c'.e` here. -/
noncomputable def lastMuOf (e : ResolvedExec State Label) : PMF State := by
  classical
  exact if h : e.trans.Terminates then
    ((e.trans.toList h).getLast?).elim (PMF.pure e.init) (fun p => p.1.2)
  else PMF.pure e.init

/-- The **fair-aware transition kernel** at `qₚ` for the `𝒟f`-emission `(l, ω)` at belief `β`: the
distribution `p qₚ : PMF (PMF State)` over `sys`-transitions out of `qₚ` given by the emission's
witness kernel — the `F.fair`-fair kernel when the step is `F.dist`-fair, the plain `hyperStep`
witness otherwise (`PMF.pure (PMF.pure qₚ)` as junk when the emission is not a valid `𝒟f`-step). The
concrete transition `μ'` is **sampled** from this kernel. -/
noncomputable def tKernel (F : Fairness sys) (β : PMF State) (l : Label) (ω : PMF (PMF State))
    (qₚ : State) : PMF (PMF State) := by
  classical
  exact
    if h : F.dist.fair β l ω then h.2.choose qₚ
    else if h' : (sys.distF F).step β l ω then h'.1.choose qₚ
    else PMF.pure (PMF.pure qₚ)

/-- A state of the lowering Markov chain: an abstract `𝒟f`-run `de`, a concrete `sys`-run `e`, and
the pending `𝒟f`-emission `h = s(de)` (`none` = halt). -/
structure LowerConfig (sys : System State Label) where
  /-- The abstract `𝒟f(sys,F)`-execution built so far. -/
  de : ResolvedExec (PMF State) Label
  /-- The concrete `sys`-execution built so far. -/
  e  : ResolvedExec State Label
  /-- The pending `𝒟f`-emission `s(de)` (`none` = halt). -/
  h  : Option (Label × PMF (PMF State))

/-- One instruction of the lowering chain, as a transition weight `c → c'` (a genuine stochastic
kernel on `LowerConfig`). Halted (`c.h = none`) states have no outgoing transition. For a pending
emission `c.h = some (l, ω)`, the successor `c'` appends the concrete step `((l, μ'), q)` to `e` and
the abstract step `((l, ω), dq)` to `de`, then carries the next pending emission `c'.h`, where
`μ' = lastMuOf c'.e` is the recorded concrete transition, `q = lastStateOf c'.e`,
`dq = lastStateOf c'.de`. The weight `tKernel(…) μ' * μ' q * ω dq * (dq q / (ω.bind id) q) *
s(de')(h')` factors the four draws: `μ' ∼ tKernel(qₚ)` (the fair kernel — concrete transition
sampled), `q ∼ μ'` (outcome, keeps `e` valid), `dq ∼ ω` reweighted by the **proper Bayes posterior**
`dq(q) / (ω.bind id)(q)`. Sampling `μ'` from the kernel (rather than a fixed choice) makes the
concrete run track the belief, so both marginals are faithful. -/
noncomputable def LowerStep (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (c c' : LowerConfig sys) : ENNReal := by
  classical
  exact
    match c.h with
    | none => 0
    | some (l, ω) =>
        let μ' : PMF State := lastMuOf c'.e
        let dq : PMF State := lastStateOf c'.de
        let q  : State := lastStateOf c'.e
        if c'.de.init = c.de.init ∧ c'.e.init = c.e.init ∧
           c'.de.trans = c.de.trans.append (Seq.cons ((l, ω), dq) Seq.nil) ∧
           c'.e.trans  = c.e.trans.append (Seq.cons ((l, μ'), q) Seq.nil)
        then (tKernel F (lastStateOf c.de) l ω (lastStateOf c.e)) μ' * μ' q * ω dq
              * (dq q / (ω.bind id) q) * s.next c'.de c'.h
        else 0

/-- The chain-state distribution after `n` instructions. `n = 0` is the start:
`de = ⟨δ_{init}, nil⟩`, `e = ⟨init, nil⟩`, drawing the first pending emission from `s`. -/
noncomputable def LowerReachAfter (F : Fairness sys) (s : ResolvedScheduler (sys.distF F)) :
    ℕ → LowerConfig sys → ENNReal := by
  classical
  exact fun n c => Nat.rec
    (motive := fun _ => LowerConfig sys → ENNReal)
    (fun c =>
      if c.de = ⟨PMF.pure sys.init, Seq.nil⟩ ∧ c.e = ⟨sys.init, Seq.nil⟩
      then s.next ⟨PMF.pure sys.init, Seq.nil⟩ c.h
      else 0)
    (fun _ ih c => ∑' c₀ : LowerConfig sys, ih c₀ * LowerStep F s c₀ c)
    n c

/-- **The reaching probability** of a chain state `c`: the total probability, over every instruction
count, of the algorithm's state being exactly `c`. -/
noncomputable def LowerReachProb (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (c : LowerConfig sys) : ENNReal :=
  ∑' n, LowerReachAfter F s n c

-- Unfolding `LowerReachAfter` at `0` (definitional): the start distribution.
open Classical in
theorem LowerReachAfter_zero (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (c : LowerConfig sys) :
    LowerReachAfter F s 0 c =
      (if c.de = ⟨PMF.pure sys.init, Seq.nil⟩ ∧ c.e = ⟨sys.init, Seq.nil⟩
       then s.next ⟨PMF.pure sys.init, Seq.nil⟩ c.h else 0) := rfl

/-- Unfolding `LowerReachAfter` at `n+1` (definitional): one more instruction convolves with
`LowerStep`. -/
theorem LowerReachAfter_succ (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (n : ℕ) (c : LowerConfig sys) :
    LowerReachAfter F s (n + 1) c
      = ∑' c₀ : LowerConfig sys, LowerReachAfter F s n c₀ * LowerStep F s c₀ c := rfl

/-- The coupling invariant carried by every reachable chain state: both runs are finite and the
concrete end-state lies in the support of the belief end-state. (Reachable states moreover have
equal length and pointwise-equal labels, giving `sys.trace e = 𝒟f.trace de`.) -/
def Coupled (c : LowerConfig sys) : Prop :=
  c.de.trans.Terminates ∧ c.e.trans.Terminates ∧
    lastStateOf c.e ∈ (lastStateOf c.de).support

/-! ### The reconstructed resolved scheduler `s'` on `sys`

`lowerSched F s` is the concrete resolved-history scheduler read off the lowering chain: at a
concrete history `e` it emits each option in proportion to the chain's reach-mass of the configs
that produce it out of `e` (marginalising the abstract run `de` away).

* `lowerArrHalt e` — the **halt numerator**: reach-mass of configs `⟨de, e, none⟩` (the run has
  reached `e` and `s` scheduled `none`);
* `lowerArrStep e (l, μ)` — the **step numerator**: reach-mass of configs whose concrete run is `e`
  extended by one step `((l, μ), q')`, over any `q'`.

`lowerNext e` normalises these by `lowerDenom e := lowerArrHalt e + ∑' t, lowerArrStep e t` — the
*resolved* mass at `e`, **not** the total arrival mass. The gap between them is the evidence defect,
which is thereby renormalised into the genuine transitions rather than into `none`. So `none` keeps
the *genuine-halt* fraction `lowerArrHalt e / lowerDenom e`, which is what makes `halt_fairDeadlock`
survive (had `none` absorbed the defect, `s'` would halt off the fair deadlocks). `lowerDenom e = 0`
(an unreachable `e`) falls back to `pure none`. -/

/-- Halt numerator: reach-mass of configs at `e` whose pending emission is `none`. -/
noncomputable def lowerArrHalt (F : Fairness sys) (sch : ResolvedScheduler (sys.distF F))
    (e : ResolvedExec State Label) : ENNReal :=
  ∑' de : ResolvedExec (PMF State) Label, LowerReachProb F sch ⟨de, e, none⟩

/-- Step numerator: reach-mass of configs whose concrete run is `e` extended by `((l, μ), q')`, for
any next state `q'`. -/
noncomputable def lowerArrStep (F : Fairness sys) (sch : ResolvedScheduler (sys.distF F))
    (e : ResolvedExec State Label) (x : Label × PMF State) : ENNReal :=
  ∑' (de : ResolvedExec (PMF State) Label) (q' : State)
      (h' : Option (Label × PMF (PMF State))),
    LowerReachProb F sch ⟨de, ⟨e.init, e.trans.append (Seq.cons (x, q') Seq.nil)⟩, h'⟩

/-- The numerator function of `lowerNext e`: `none ↦ lowerArrHalt`, `some x ↦ lowerArrStep x`. -/
noncomputable def lowerNumer (F : Fairness sys) (sch : ResolvedScheduler (sys.distF F))
    (e : ResolvedExec State Label) : Option (Label × PMF State) → ENNReal
  | none => lowerArrHalt F sch e
  | some x => lowerArrStep F sch e x

/-- The normalising denominator: the total resolved (halt + step) reach-mass at `e`. -/
noncomputable def lowerDenom (F : Fairness sys) (sch : ResolvedScheduler (sys.distF F))
    (e : ResolvedExec State Label) : ENNReal :=
  ∑' o, lowerNumer F sch e o

/-- **H1.** The induced concrete transition `tOutcome F β l ω qₚ` is a genuine `sys`-step out of
`qₚ`, whenever `qₚ ∈ β.support` and `(l, ω)` is a valid `𝒟f`-step out of `β`. Reads the "all fair"
(resp. "all `sys.step`") clause of the fairness (resp. step) witness at the successor state `qₚ`. -/
theorem tKernel_step (F : Fairness sys) (β : PMF State) (l : Label) (ω : PMF (PMF State))
    (qₚ : State) (μ' : PMF State) (hμ' : μ' ∈ (tKernel F β l ω qₚ).support)
    (hq : qₚ ∈ β.support) (hstep : (sys.distF F).step β l ω) :
    sys.step qₚ l μ' := by
  classical
  unfold tKernel at hμ'
  by_cases hf : F.dist.fair β l ω
  · rw [dif_pos hf] at hμ'
    exact F.step_of_fair qₚ l _ (hf.2.choose_spec.1 qₚ hq _ hμ')
  · rw [dif_neg hf, dif_pos hstep] at hμ'
    exact hstep.1.choose_spec.1 qₚ hq _ hμ'

/-- Every sampled transition in `tKernel`'s support is `F.fair` when the emission is `F.dist`-fair —
the clause that carries `inf_fair` down to the concrete run. -/
theorem tKernel_fair (F : Fairness sys) (β : PMF State) (l : Label) (ω : PMF (PMF State))
    (qₚ : State) (μ' : PMF State) (hμ' : μ' ∈ (tKernel F β l ω qₚ).support)
    (hq : qₚ ∈ β.support) (hfair : F.dist.fair β l ω) :
    F.fair qₚ l μ' := by
  classical
  unfold tKernel at hμ'
  rw [dif_pos hfair] at hμ'
  exact hfair.2.choose_spec.1 qₚ hq _ hμ'

/-- **H2 (nil).** The last state of a nil-transition execution is its `init`. -/
theorem lastStateOf_nil {S L : Type} (i : S) :
    lastStateOf (⟨i, Seq.nil⟩ : AlterSeq S L) = i := by
  classical
  unfold lastStateOf
  rw [dif_pos Stream'.Seq.terminates_nil]
  exact AlterSeq.endState_of_trans_nil _ rfl _

/-- **H2 (append).** The last state of an execution extended by appending a single transition
`(lbl, x)` is `x` (the destination of the appended transition), for a terminating base. -/
theorem lastStateOf_append_singleton {S L : Type} (a : AlterSeq S L)
    (ha : a.trans.Terminates) (lbl : L) (x : S) :
    lastStateOf (⟨a.init, a.trans.append (Seq.cons (lbl, x) Seq.nil)⟩ : AlterSeq S L) = x := by
  classical
  have hnew_term :
      (⟨a.init, a.trans.append (Seq.cons (lbl, x) Seq.nil)⟩ : AlterSeq S L).trans.Terminates :=
    ⟨Nat.find ha + 1, Stream'.Seq.terminatedAt_append_find ha
      (show (Seq.cons (lbl, x) Seq.nil).TerminatedAt 1 from rfl)⟩
  unfold lastStateOf
  rw [dif_pos hnew_term]
  exact AlterSeq.endState_append_singleton a ha lbl x

omit [Silent Label] in
/-- The recorded `μ` of the last step of an execution extended by appending `((l, μ), x)` is `μ`. -/
theorem lastMuOf_append_singleton (a : ResolvedExec State Label)
    (ha : a.trans.Terminates) (l : Label) (μ : PMF State) (x : State) :
    lastMuOf (⟨a.init, a.trans.append (Seq.cons ((l, μ), x) Seq.nil)⟩ : ResolvedExec State Label)
      = μ := by
  classical
  have hnew_term :
      (⟨a.init, a.trans.append (Seq.cons ((l, μ), x) Seq.nil)⟩ :
        ResolvedExec State Label).trans.Terminates :=
    ⟨Nat.find ha + 1, Stream'.Seq.terminatedAt_append_find ha
      (show (Seq.cons ((l, μ), x) Seq.nil).TerminatedAt 1 from rfl)⟩
  unfold lastMuOf
  rw [dif_pos hnew_term]
  have htoList :
      (⟨a.init, a.trans.append (Seq.cons ((l, μ), x) Seq.nil)⟩ :
        ResolvedExec State Label).trans.toList hnew_term
        = a.trans.toList ha ++ [((l, μ), x)] := by
    change (a.trans.append (Seq.cons ((l, μ), x) Seq.nil)).toList hnew_term
      = a.trans.toList ha ++ [((l, μ), x)]
    rw [Stream'.Seq.toList_append a.trans (Seq.cons ((l, μ), x) Seq.nil) ha
      (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil) hnew_term]
    congr 1
    rw [Stream'.Seq.toList_cons]; simp [Stream'.Seq.toList_nil]
  rw [htoList]
  simp

/-- Extensionality for `AlterSeq`: equal `init` and `trans` give equal executions. -/
theorem alterSeq_ext {S L : Type} {a b : AlterSeq S L}
    (hi : a.init = b.init) (ht : a.trans = b.trans) : a = b := by
  cases a; cases b; cases hi; cases ht; rfl

/-- A nonzero `ENNReal`-valued tsum has a nonzero term. -/
theorem tsum_ne_zero_exists {α : Type _} {f : α → ENNReal} (h : ∑' i, f i ≠ 0) :
    ∃ i, f i ≠ 0 := by
  by_contra hall
  push Not at hall
  exact h (ENNReal.tsum_eq_zero.mpr hall)

/-- **H3.** A config with nonzero reach-mass at any level has a nonzero pending emission
`s.next c.de c.h`. At level `0` the config is the start (`de = ⟨δ_init, nil⟩`); at level `n+1` the
weight of the last instruction carries `s.next c.de c.h` as its final factor. -/
theorem reachAfter_next_ne_zero (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (n : ℕ) (c : LowerConfig sys) (hne : LowerReachAfter F s n c ≠ 0) :
    s.next c.de c.h ≠ 0 := by
  classical
  induction n generalizing c with
  | zero =>
    rw [LowerReachAfter_zero] at hne
    by_cases hc : c.de = ⟨PMF.pure sys.init, Seq.nil⟩ ∧ c.e = ⟨sys.init, Seq.nil⟩
    · rw [if_pos hc] at hne
      rw [hc.1]; exact hne
    · rw [if_neg hc] at hne; exact absurd rfl hne
  | succ k ih =>
    rw [LowerReachAfter_succ] at hne
    obtain ⟨c₀, hc₀⟩ := tsum_ne_zero_exists hne
    have hstep : LowerStep F s c₀ c ≠ 0 := fun h => hc₀ (by rw [h, mul_zero])
    -- unfold LowerStep to extract the final factor s.next c.de c.h
    revert hstep
    unfold LowerStep
    cases hh : c₀.h with
    | none => intro hstep; exact absurd rfl hstep
    | some lω =>
      obtain ⟨l₀, ω₀⟩ := lω
      simp only
      by_cases hif : c.de.init = c₀.de.init ∧ c.e.init = c₀.e.init ∧
          c.de.trans = c₀.de.trans.append (Seq.cons ((l₀, ω₀), lastStateOf c.de) Seq.nil) ∧
          c.e.trans = c₀.e.trans.append (Seq.cons ((l₀, lastMuOf c.e), lastStateOf c.e) Seq.nil)
      · rw [if_pos hif]
        intro hstep
        exact fun h => hstep (by rw [h, mul_zero])
      · rw [if_neg hif]; intro hstep; exact absurd rfl hstep
/-- **H4.** Every config with nonzero reach-mass at any level is `Coupled`: both runs terminate and
the concrete end-state lies in the belief end-state's support. Preserved by one instruction because
`de`'s next belief `dq` is drawn reweighted by `dq(q)`, so a nonzero weight forces `dq(q) ≠ 0`,
i.e. `q ∈ dq.support`. -/
theorem reachAfter_coupled (F : Fairness sys) (s : ResolvedScheduler (sys.distF F))
    (n : ℕ) (c : LowerConfig sys) (hne : LowerReachAfter F s n c ≠ 0) : Coupled c := by
  classical
  induction n generalizing c with
  | zero =>
    rw [LowerReachAfter_zero] at hne
    by_cases hc : c.de = ⟨PMF.pure sys.init, Seq.nil⟩ ∧ c.e = ⟨sys.init, Seq.nil⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hc.1]; exact Stream'.Seq.terminates_nil
      · rw [hc.2]; exact Stream'.Seq.terminates_nil
      · rw [hc.1, hc.2, lastStateOf_nil, lastStateOf_nil, PMF.mem_support_iff, PMF.pure_apply,
          if_pos rfl]
        exact one_ne_zero
    · rw [if_neg hc] at hne; exact absurd rfl hne
  | succ k ih =>
    rw [LowerReachAfter_succ] at hne
    obtain ⟨c₀, hc₀⟩ := tsum_ne_zero_exists hne
    have hreach₀ : LowerReachAfter F s k c₀ ≠ 0 := fun h => hc₀ (by rw [h, zero_mul])
    have hstep : LowerStep F s c₀ c ≠ 0 := fun h => hc₀ (by rw [h, mul_zero])
    have hcoup₀ : Coupled c₀ := ih c₀ hreach₀
    -- Unfold LowerStep to extract the if-condition and the nonzero weight.
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
        intro hweight
        obtain ⟨_, _, hde_trans, he_trans⟩ := hif
        -- nonzero weight ⇒ dq q ≠ 0
        have hdq : lastStateOf c.de (lastStateOf c.e) ≠ 0 := by
          intro h0
          apply hweight
          simp only [h0, ENNReal.zero_div, mul_zero, zero_mul]
        refine ⟨?_, ?_, ?_⟩
        · rw [hde_trans]
          exact ⟨Nat.find hcoup₀.1 + 1, Stream'.Seq.terminatedAt_append_find hcoup₀.1
            (show (Seq.cons ((l₀, ω₀), lastStateOf c.de) Seq.nil).TerminatedAt 1 from rfl)⟩
        · rw [he_trans]
          exact ⟨Nat.find hcoup₀.2.1 + 1, Stream'.Seq.terminatedAt_append_find hcoup₀.2.1
            (show (Seq.cons ((l₀, μ'), lastStateOf c.e) Seq.nil).TerminatedAt 1 from rfl)⟩
        · rw [PMF.mem_support_iff]; exact hdq
      · rw [if_neg hif]; intro hstep; exact absurd rfl hstep
/-- **H5.** If `e` terminates at `n` and its state at `n` is `some st`, then `st = lastStateOf e`.
The canonical terminating position `Nat.find hT` must equal `n`: it is `≤ n`, and a strictly earlier
one would leave `e.stateAt n = none` (positions past termination are `none`), contradicting
`hstate`. -/
theorem stateAt_terminatedAt_eq_lastStateOf {S L : Type} (e : AlterSeq S L) (n : ℕ) (st : S)
    (hterm : e.trans.TerminatedAt n) (hstate : e.stateAt n = some st) : st = lastStateOf e := by
  classical
  have hT : e.trans.Terminates := ⟨n, hterm⟩
  have hlast : lastStateOf e = e.endState hT := by unfold lastStateOf; rw [dif_pos hT]
  have hfind : Nat.find hT = n := by
    rcases lt_or_eq_of_le (Nat.find_le hterm) with hlt | heq
    · exfalso
      -- e.stateAt n = none since a strictly earlier terminated position stabilises to none.
      have hterm_find : e.trans.TerminatedAt (Nat.find hT) := Nat.find_spec hT
      have hnpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
      have hle : Nat.find hT ≤ m := Nat.lt_succ_iff.mp hlt
      have hget : e.trans.get? m = none := Stream'.Seq.terminated_stable e.trans hle hterm_find
      have : e.stateAt (m + 1) = none := by
        change (e.trans.get? m).map Prod.snd = none
        rw [hget]; rfl
      rw [this] at hstate; simp at hstate
    · exact heq
  have h_eq := AlterSeq.stateAt_find_eq_endState e hT
  rw [hfind, hstate] at h_eq
  rw [hlast]; exact Option.some.inj h_eq

/-- A `tsum` over an `Option` type splits as the value at `none` plus the `tsum` over the
`some`-fibres (local `ENNReal` specialisation; every `ENNReal` family is summable). -/
theorem lower_tsum_option {β : Type*} (f : Option β → ENNReal) :
    (∑' x, f x) = f none + ∑' y, f (some y) := by
  rw [ENNReal.tsum_eq_add_tsum_ite none]
  congr 1
  rw [tsum_eq_tsum_of_ne_zero_bij (i := fun y : {y : β // f (some y) ≠ 0} => some y.1)]
  · intro a b hab; exact Subtype.ext (Option.some_injective β hab)
  · intro x hx
    cases hx2 : (x : Option β) with
    | none => simp [Function.mem_support, hx2] at hx
    | some y =>
      refine ⟨⟨y, ?_⟩, ?_⟩
      · simp only [Function.mem_support] at hx ⊢
        rw [hx2] at hx; simpa using hx
      · simp
  · intro y; simp

/-- **L1 (sub-stochasticity).** One instruction of the lowering chain is a sub-probability kernel:
out of a config whose two runs terminate, the total transition weight is `≤ 1`. The nonzero
successors of `c₀` (with pending emission `some (l, ω)`) are parameterised injectively by
`(dq, q, h')`; reindexing along that bijection, `∑' h', s.next _ h' = 1` (a `PMF`), then
`μ' q * (dq q / μ' q) ≤ dq q` collapses the `μ'`-factors, leaving
`∑' dq, ω dq * ∑' q, dq q = ∑' dq, ω dq = 1`. -/
theorem lowerStep_tsum_le_one (F : Fairness sys) (sch : ResolvedScheduler (sys.distF F))
    (c₀ : LowerConfig sys) (hde : c₀.de.trans.Terminates) (he : c₀.e.trans.Terminates) :
    ∑' c', LowerStep F sch c₀ c' ≤ 1 := by
  classical
  cases hh : c₀.h with
  | none =>
    have : ∀ c', LowerStep F sch c₀ c' = 0 := by
      intro c'; unfold LowerStep; rw [hh]
    simp only [this, tsum_zero]; exact zero_le_one
  | some lω =>
    obtain ⟨l, ω⟩ := lω
    set β := lastStateOf c₀.de with hβ
    set qₚ := lastStateOf c₀.e with hqₚ
    -- Successor configs: `de` extended by `dq`, `e` extended by the sampled step `((l, μ), q)`.
    set De : PMF State → ResolvedExec (PMF State) Label :=
      fun dq => ⟨c₀.de.init, c₀.de.trans.append (Seq.cons ((l, ω), dq) Seq.nil)⟩ with hDe
    set Ec : PMF State → State → ResolvedExec State Label :=
      fun μ q => ⟨c₀.e.init, c₀.e.trans.append (Seq.cons ((l, μ), q) Seq.nil)⟩ with hEc
    -- The injective reindexing map `(μ, dq, q, h') ↦ c'`.
    set φ : PMF State × PMF State × State × Option (Label × PMF (PMF State)) → LowerConfig sys :=
      fun p => ⟨De p.2.1, Ec p.1 p.2.2.1, p.2.2.2⟩ with hφ
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
    -- The value of `LowerStep` on an image config `φ (μ, dq, q, h')`.
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
    -- The reindexed summand.
    set g : PMF State × PMF State × State × Option (Label × PMF (PMF State)) → ENNReal :=
      fun p => (tKernel F β l ω qₚ) p.1 * p.1 p.2.2.1 * ω p.2.1
        * (p.2.1 p.2.2.1 / (ω.bind id) p.2.2.1) * sch.next (De p.2.1) p.2.2.2 with hg
    -- Reindex `∑' c', LowerStep c₀ c'` along `φ` to `∑' p, g p`.
    have hreindex : ∑' c', LowerStep F sch c₀ c' = ∑' p, g p := by
      refine tsum_eq_tsum_of_ne_zero_bij (i := fun p : Function.support g => φ p.1)
        ?inj ?supp ?val
      · rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hab
        exact Subtype.ext (hφinj hab)
      · intro c' hc'
        have hne : LowerStep F sch c₀ c' ≠ 0 := hc'
        -- Read the shape of a nonzero-weight successor.
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
    -- The `(ω.bind id)`-normalised belief fibre `≤ 1`.
    have hfibre : ∀ q : State, ∑' dq : PMF State, ω dq * (dq q / (ω.bind id) q) ≤ 1 := by
      intro q
      have h2 : ∑' dq : PMF State, ω dq * (dq q / (ω.bind id) q)
          = (ω.bind id) q * ((ω.bind id) q)⁻¹ := by
        calc ∑' dq : PMF State, ω dq * (dq q / (ω.bind id) q)
            = ∑' dq : PMF State, (ω dq * dq q) * ((ω.bind id) q)⁻¹ := by
              refine tsum_congr fun dq => ?_; rw [div_eq_mul_inv]; ring
          _ = (∑' dq : PMF State, ω dq * dq q) * ((ω.bind id) q)⁻¹ := ENNReal.tsum_mul_right
          _ = (ω.bind id) q * ((ω.bind id) q)⁻¹ := by rw [hbind]
      rw [h2]
      rcases eq_or_ne ((ω.bind id) q) 0 with h0 | h0
      · rw [h0, zero_mul]; exact zero_le_one
      · exact le_of_eq (ENNReal.mul_inv_cancel h0 (PMF.apply_ne_top (ω.bind id) q))
    -- Sum out `h'` (a `PMF`); the belief fibre `≤ 1`; the `μ`-kernel and each `μ` are `PMF`s.
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
      _ ≤ ∑' (μ : PMF State) (q : State), (tKernel F β l ω qₚ) μ * μ q := by
          refine ENNReal.tsum_le_tsum fun μ => ENNReal.tsum_le_tsum fun q => ?_
          calc ∑' dq : PMF State, (tKernel F β l ω qₚ) μ * μ q * ω dq * (dq q / (ω.bind id) q)
              = (tKernel F β l ω qₚ) μ * μ q
                * ∑' dq : PMF State, ω dq * (dq q / (ω.bind id) q) := by
                  rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun dq => by ring
            _ ≤ (tKernel F β l ω qₚ) μ * μ q * 1 := by gcongr; exact hfibre q
            _ = (tKernel F β l ω qₚ) μ * μ q := mul_one _
      _ = ∑' μ : PMF State, (tKernel F β l ω qₚ) μ := by
          refine tsum_congr fun μ => ?_
          rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
      _ = 1 := PMF.tsum_coe _

/-- Appending one transition to a sequence that terminates exactly at `n` gives a sequence that
terminates exactly at `n + 1`. -/
theorem terminatedAt_append_singleton_iff {S L : Type} (s : Seq (L × S)) (n : ℕ)
    (hn : s.TerminatedAt n) (hmin : ∀ k < n, ¬ s.TerminatedAt k) (x : L × S) :
    (s.append (Seq.cons x Seq.nil)).TerminatedAt (n + 1) ∧
      ∀ k < n + 1, ¬ (s.append (Seq.cons x Seq.nil)).TerminatedAt k := by
  classical
  have hT : s.Terminates := ⟨n, hn⟩
  have hfind : Nat.find hT = n := by
    apply le_antisymm (Nat.find_le hn)
    by_contra h; push Not at h; exact hmin _ h (Nat.find_spec hT)
  refine ⟨?_, ?_⟩
  · have := Stream'.Seq.terminatedAt_append_find hT (s' := Seq.cons x Seq.nil) (n := 1)
      (show (Seq.cons x Seq.nil).TerminatedAt 1 from rfl)
    rwa [hfind] at this
  · intro k hk
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | heq
    · intro hterm
      rw [Stream'.Seq.TerminatedAt, Stream'.Seq.get?_append_before_length (hmin k hlt)] at hterm
      exact hmin k hlt hterm
    · subst heq
      intro hterm
      have happ : (s.append (Seq.cons x Seq.nil)).get? k = some x := by
        have hg := Stream'.Seq.get?_append_find hT (Seq.cons x Seq.nil) 0
        rw [hfind, Nat.add_zero] at hg
        rw [hg]; rfl
      rw [Stream'.Seq.TerminatedAt, happ] at hterm
      exact Option.some_ne_none x hterm

/-- **L2 (length-tracking).** A config with nonzero reach-mass at level `n` has its concrete run
terminate exactly at `n` (and no earlier). Appending one transition per instruction, so `n` counts
the length of `c.e.trans`. -/
theorem reachAfter_length (F : Fairness sys) (sch : ResolvedScheduler (sys.distF F))
    (n : ℕ) (c : LowerConfig sys) (hne : LowerReachAfter F sch n c ≠ 0) :
    c.e.trans.TerminatedAt n ∧ ∀ k < n, ¬ c.e.trans.TerminatedAt k := by
  classical
  induction n generalizing c with
  | zero =>
    rw [LowerReachAfter_zero] at hne
    by_cases hc : c.de = ⟨PMF.pure sys.init, Seq.nil⟩ ∧ c.e = ⟨sys.init, Seq.nil⟩
    · rw [hc.2]
      exact ⟨Stream'.Seq.terminatedAt_nil, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    · rw [if_neg hc] at hne; exact absurd rfl hne
  | succ k ih =>
    rw [LowerReachAfter_succ] at hne
    obtain ⟨c₀, hc₀⟩ := tsum_ne_zero_exists hne
    have hreach₀ : LowerReachAfter F sch k c₀ ≠ 0 := fun h => hc₀ (by rw [h, zero_mul])
    have hstep : LowerStep F sch c₀ c ≠ 0 := fun h => hc₀ (by rw [h, mul_zero])
    obtain ⟨hterm₀, hmin₀⟩ := ih c₀ hreach₀
    -- Extract the `e`-append shape from `LowerStep c₀ c ≠ 0`.
    have het : ∃ x : (Label × PMF State) × State,
        c.e.trans = c₀.e.trans.append (Seq.cons x Seq.nil) := by
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
        · intro _; exact ⟨((l₀, μ'), lastStateOf c.e), hif.2.2.2⟩
        · rw [if_neg hif]; intro h0; exact absurd rfl h0
    obtain ⟨x, hx⟩ := het
    rw [hx]
    exact terminatedAt_append_singleton_iff c₀.e.trans k hterm₀ hmin₀ x

/-- **L3 (level-mass).** The total reach-mass at any fixed level is `≤ 1`. Base: the start config's
mass is `∑' h, s.next _ h = 1`. Step: `∑' c, (∑' c₀, R n c₀ * step c₀ c)` swaps to
`∑' c₀, R n c₀ * (∑' c, step c₀ c) ≤ ∑' c₀, R n c₀ ≤ 1`. -/
theorem reachAfter_level_le_one (F : Fairness sys) (sch : ResolvedScheduler (sys.distF F))
    (n : ℕ) : ∑' c, LowerReachAfter F sch n c ≤ 1 := by
  classical
  induction n with
  | zero =>
    -- The start config is determined by its pending emission `c.h`.
    set D₀ : ResolvedExec (PMF State) Label := ⟨PMF.pure sys.init, Seq.nil⟩ with hD₀
    set E₀ : ResolvedExec State Label := ⟨sys.init, Seq.nil⟩ with hE₀
    have heq : ∑' c, LowerReachAfter F sch 0 c
        = ∑' hopt : Option (Label × PMF (PMF State)), sch.next D₀ hopt := by
      refine tsum_eq_tsum_of_ne_zero_bij
        (i := fun hopt : Function.support (fun hopt => sch.next D₀ hopt) =>
          (⟨D₀, E₀, hopt.1⟩ : LowerConfig sys)) ?inj ?supp ?val
      · rintro ⟨h₁, _⟩ ⟨h₂, _⟩ hab
        exact Subtype.ext (congrArg LowerConfig.h hab)
      · intro c hc
        rw [Function.mem_support, LowerReachAfter_zero] at hc
        by_cases hcc : c.de = D₀ ∧ c.e = E₀
        · refine ⟨⟨c.h, ?_⟩, ?_⟩
          · rw [if_pos hcc] at hc
            rw [Function.mem_support]; exact hc
          · change (⟨D₀, E₀, c.h⟩ : LowerConfig sys) = c
            rw [← hcc.1, ← hcc.2]
        · rw [if_neg hcc] at hc; exact absurd rfl hc
      · rintro ⟨hopt, hne⟩
        rw [LowerReachAfter_zero, if_pos ⟨rfl, rfl⟩]
    rw [heq, PMF.tsum_coe]
  | succ n ih =>
    -- Convolution: swap the two sums, then bound the inner `LowerStep`-sum by `1` (L1).
    have hswap : ∑' c, LowerReachAfter F sch (n + 1) c
        = ∑' c₀, LowerReachAfter F sch n c₀ * (∑' c, LowerStep F sch c₀ c) := by
      simp_rw [LowerReachAfter_succ]
      rw [ENNReal.tsum_comm]
      exact tsum_congr fun c₀ => ENNReal.tsum_mul_left
    rw [hswap]
    refine le_trans (ENNReal.tsum_le_tsum fun c₀ => ?_) ih
    -- Each term `R n c₀ * (∑' c, step c₀ c) ≤ R n c₀`.
    by_cases h0 : LowerReachAfter F sch n c₀ = 0
    · rw [h0, zero_mul]
    · have hcoup : Coupled c₀ := reachAfter_coupled F sch n c₀ h0
      have hle : ∑' c, LowerStep F sch c₀ c ≤ 1 :=
        lowerStep_tsum_le_one F sch c₀ hcoup.1 hcoup.2.1
      exact mul_le_of_le_one_right zero_le hle

/-- The reach-prob of a config collapses to the single level equal to its concrete run's length:
`LowerReachProb c = LowerReachAfter (Nat.find hE) c` when `c.e.trans` terminates (each
`LowerReachAfter` at any other level vanishes by **L2**), and `= 0` when it does not. -/
theorem LowerReachProb_collapse (F : Fairness sys) (sch : ResolvedScheduler (sys.distF F))
    (c : LowerConfig sys) (hE : c.e.trans.Terminates) :
    LowerReachProb F sch c = LowerReachAfter F sch (Nat.find hE) c := by
  classical
  unfold LowerReachProb
  refine tsum_eq_single (Nat.find hE) ?_
  intro n hn
  by_contra hne
  obtain ⟨hterm, hmin⟩ := reachAfter_length F sch n c hne
  -- `n` is then the minimal terminating position, i.e. `Nat.find hE`.
  have : n = Nat.find hE := by
    apply le_antisymm
    · by_contra h; push Not at h
      exact hmin _ h (Nat.find_spec hE)
    · exact Nat.find_le hterm
  exact hn this

/-- A config whose concrete run does not terminate has zero reach-prob (each level requires the run
to terminate there, by **L2**). -/
theorem LowerReachProb_of_not_terminates (F : Fairness sys)
    (sch : ResolvedScheduler (sys.distF F)) (c : LowerConfig sys)
    (hE : ¬ c.e.trans.Terminates) : LowerReachProb F sch c = 0 := by
  classical
  unfold LowerReachProb
  rw [ENNReal.tsum_eq_zero]
  intro n
  by_contra hne
  exact hE ⟨n, (reachAfter_length F sch n c hne).1⟩

/-- The **halt arrival** at `e` is `≤ 1`: it is a marginal (over `de`) of the reach-mass at the
single level `Nat.find hE` (the length of `e`), which is `≤ 1` by **L3**. Zero when `e` does not
terminate. -/
theorem lowerArrHalt_le_one (F : Fairness sys) (sch : ResolvedScheduler (sys.distF F))
    (e : ResolvedExec State Label) : lowerArrHalt F sch e ≤ 1 := by
  classical
  unfold lowerArrHalt
  by_cases hE : e.trans.Terminates
  · -- Collapse each `LowerReachProb` to level `N := Nat.find hE`.
    have hcollapse : ∀ de : ResolvedExec (PMF State) Label,
        LowerReachProb F sch ⟨de, e, none⟩ = LowerReachAfter F sch (Nat.find hE) ⟨de, e, none⟩ := by
      intro de
      exact LowerReachProb_collapse F sch ⟨de, e, none⟩ hE
    simp_rw [hcollapse]
    -- Inject `de ↦ ⟨de, e, none⟩` into all configs; apply L3.
    have hinj : Function.Injective
        (fun de : ResolvedExec (PMF State) Label => (⟨de, e, none⟩ : LowerConfig sys)) := by
      intro a b hab; exact congrArg LowerConfig.de hab
    refine le_trans (ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun c => LowerReachAfter F sch (Nat.find hE) c)) ?_
    exact reachAfter_level_le_one F sch (Nat.find hE)
  · have : ∀ de : ResolvedExec (PMF State) Label, LowerReachProb F sch ⟨de, e, none⟩ = 0 := by
      intro de; exact LowerReachProb_of_not_terminates F sch ⟨de, e, none⟩ hE
    simp_rw [this, tsum_zero]; exact zero_le_one

/-- The **total step arrival** at `e` is `≤ 1`: flattening the four sums, it is a marginal (over
`(x, de, q', h')`) of the reach-mass at the single level `Nat.find hE + 1`, which is `≤ 1` by
**L3**. The flattening map is injective because the appended last transition `(x, q')` is recovered
from the concrete run's end. -/
theorem lowerArrStep_tsum_le_one (F : Fairness sys) (sch : ResolvedScheduler (sys.distF F))
    (e : ResolvedExec State Label) : ∑' x, lowerArrStep F sch e x ≤ 1 := by
  classical
  by_cases hE : e.trans.Terminates
  · -- Set up the extended concrete run and the flattening injection.
    set N := Nat.find hE with hN
    set Ex : (Label × PMF State) → State → ResolvedExec State Label :=
      fun x q' => ⟨e.init, e.trans.append (Seq.cons (x, q') Seq.nil)⟩ with hEx
    have hExterm : ∀ x q', (Ex x q').trans.Terminates := by
      intro x q'
      exact ⟨Nat.find hE + 1, Stream'.Seq.terminatedAt_append_find hE
        (show (Seq.cons (x, q') Seq.nil).TerminatedAt 1 from rfl)⟩
    -- `Ex x q'` has minimal terminating position `N + 1`.
    have hExfind : ∀ x q', Nat.find (hExterm x q') = N + 1 := by
      intro x q'
      obtain ⟨_, hmin⟩ := terminatedAt_append_singleton_iff e.trans N (Nat.find_spec hE)
        (fun k hk => Nat.find_min hE hk) (x, q')
      obtain ⟨hterm', _⟩ := terminatedAt_append_singleton_iff e.trans N (Nat.find_spec hE)
        (fun k hk => Nat.find_min hE hk) (x, q')
      apply le_antisymm (Nat.find_le hterm')
      by_contra h; push Not at h
      exact hmin _ h (Nat.find_spec (hExterm x q'))
    -- Rewrite each summand's `LowerReachProb` as the single level-`N+1` reach-mass.
    have hnest : ∑' x, lowerArrStep F sch e x
        = ∑' (x : Label × PMF State) (de : ResolvedExec (PMF State) Label) (q' : State)
            (h' : Option (Label × PMF (PMF State))),
          LowerReachAfter F sch (N + 1) ⟨de, Ex x q', h'⟩ := by
      unfold lowerArrStep
      refine tsum_congr fun x => tsum_congr fun de => tsum_congr fun q' => tsum_congr fun h' => ?_
      rw [show (⟨de, ⟨e.init, e.trans.append (Seq.cons (x, q') Seq.nil)⟩, h'⟩ : LowerConfig sys)
        = ⟨de, Ex x q', h'⟩ from rfl]
      rw [LowerReachProb_collapse F sch ⟨de, Ex x q', h'⟩ (hExterm x q'), hExfind x q']
    -- Flatten the four nested sums into one product sum.
    have hflat : (∑' (p : (Label × PMF State) × ResolvedExec (PMF State) Label × State ×
              Option (Label × PMF (PMF State))),
          LowerReachAfter F sch (N + 1) ⟨p.2.1, Ex p.1 p.2.2.1, p.2.2.2⟩)
        = ∑' (x : Label × PMF State) (de : ResolvedExec (PMF State) Label) (q' : State)
            (h' : Option (Label × PMF (PMF State))),
          LowerReachAfter F sch (N + 1) ⟨de, Ex x q', h'⟩ := by
      rw [ENNReal.tsum_prod']
      refine tsum_congr fun x => ?_
      rw [ENNReal.tsum_prod']
      refine tsum_congr fun de => ?_
      rw [ENNReal.tsum_prod']
    rw [hnest, ← hflat]
    -- Injection into all configs; apply L3.
    have hinj : Function.Injective
        (fun p : (Label × PMF State) × ResolvedExec (PMF State) Label × State ×
              Option (Label × PMF (PMF State)) =>
          (⟨p.2.1, Ex p.1 p.2.2.1, p.2.2.2⟩ : LowerConfig sys)) := by
      rintro ⟨x₁, de₁, q₁, h₁⟩ ⟨x₂, de₂, q₂, h₂⟩ hab
      have hde := congrArg LowerConfig.de hab
      have he := congrArg LowerConfig.e hab
      have hhh := congrArg LowerConfig.h hab
      simp only at hde he hhh
      -- `Ex`-equality recovers `(x, q')` from the appended last transition.
      have hxq : (x₁, q₁) = (x₂, q₂) := by
        have htrans : e.trans.append (Seq.cons ((x₁, q₁)) Seq.nil)
            = e.trans.append (Seq.cons ((x₂, q₂)) Seq.nil) := congrArg AlterSeq.trans he
        exact Stream'.Seq.append_singleton_inj_right _ _ hE hE _ _ htrans
      have hx : x₁ = x₂ := congrArg Prod.fst hxq
      have hq : q₁ = q₂ := congrArg Prod.snd hxq
      subst hde; subst hhh; subst hx; subst hq; rfl
    refine le_trans (ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun c => LowerReachAfter F sch (N + 1) c)) ?_
    exact reachAfter_level_le_one F sch (N + 1)
  · -- `e` does not terminate ⇒ every extended run does not either ⇒ all reach-probs vanish.
    have : ∀ x, lowerArrStep F sch e x = 0 := by
      intro x
      unfold lowerArrStep
      rw [ENNReal.tsum_eq_zero]; intro de
      rw [ENNReal.tsum_eq_zero]; intro q'
      rw [ENNReal.tsum_eq_zero]; intro h'
      apply LowerReachProb_of_not_terminates
      intro hterm
      apply hE
      by_contra hns
      have heq : e.trans.append (Seq.cons (x, q') Seq.nil) = e.trans := by
        apply Stream'.Seq.ext
        intro m
        rw [Stream'.Seq.get?_append_before_length]
        intro ht; exact hns ⟨m, ht⟩
      rw [heq] at hterm; exact hns hterm
    simp_rw [this, tsum_zero]; exact zero_le_one

/-- **Finiteness of the reach-mass** (`lowerDenom e ≠ ⊤`), needed for `lowerDenom / lowerDenom = 1`.
The reach-mass at any fixed chain-level is `≤ 1`; both the halt and step arrivals are marginals of a
single level's mass, so `lowerDenom e ≤ 2`. -/
theorem lowerDenom_ne_top (F : Fairness sys) (sch : ResolvedScheduler (sys.distF F))
    (e : ResolvedExec State Label) : lowerDenom F sch e ≠ ⊤ := by
  classical
  -- `lowerDenom = lowerArrHalt + ∑' x, lowerArrStep`; bound each by `1`.
  have hsplit : lowerDenom F sch e
      = lowerArrHalt F sch e + ∑' x, lowerArrStep F sch e x := by
    unfold lowerDenom
    rw [lower_tsum_option (lowerNumer F sch e)]
    rfl
  rw [hsplit]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top (lowerArrHalt_le_one F sch e)
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top (lowerArrStep_tsum_le_one F sch e)

/-- The reconstructed scheduler's emission at `e`: `lowerNumer e / lowerDenom e`, normalised to a
`PMF`; `pure none` when `e` is unreachable (`lowerDenom e = 0`). -/
noncomputable def lowerNext (F : Fairness sys) (sch : ResolvedScheduler (sys.distF F))
    (e : ResolvedExec State Label) : PMF (Option (Label × PMF State)) := by
  classical
  exact
    if h : lowerDenom F sch e = 0 then PMF.pure none
    else ⟨fun o => lowerNumer F sch e o / lowerDenom F sch e, by
      have hsum : ∑' o, lowerNumer F sch e o / lowerDenom F sch e = 1 := by
        simp_rw [div_eq_mul_inv]
        rw [ENNReal.tsum_mul_right,
          show (∑' o, lowerNumer F sch e o) = lowerDenom F sch e from rfl]
        exact ENNReal.mul_inv_cancel h (lowerDenom_ne_top F sch e)
      rw [← hsum]
      exact ENNReal.summable.hasSum⟩

theorem lowerNext_valid_step (F : Fairness sys) (sch : ResolvedScheduler (sys.distF F))
    (e : ResolvedExec State Label) (n : ℕ) (st : State) (l : Label) (μ : PMF State)
    (hterm : e.trans.TerminatedAt n) (hstate : e.stateAt n = some st)
    (hmem : some (l, μ) ∈ (lowerNext F sch e).support) : sys.step st l μ := by
  classical
  rw [PMF.mem_support_iff] at hmem
  -- Step 1: reduce to `lowerArrStep F sch e (l, μ) ≠ 0`.
  have hstepNe : lowerArrStep F sch e (l, μ) ≠ 0 := by
    unfold lowerNext at hmem
    by_cases hd : lowerDenom F sch e = 0
    · rw [dif_pos hd] at hmem
      exact absurd (by rw [PMF.pure_apply]; simp) hmem
    · rw [dif_neg hd] at hmem
      have hmem' : lowerNumer F sch e (some (l, μ)) / lowerDenom F sch e ≠ 0 := hmem
      exact (ENNReal.div_ne_zero.mp hmem').1
  -- Step 2: extract a config recording the step `((l, μ), q')` with nonzero reach-prob.
  unfold lowerArrStep at hstepNe
  obtain ⟨de, hde⟩ := tsum_ne_zero_exists hstepNe
  obtain ⟨q', hq'⟩ := tsum_ne_zero_exists hde
  obtain ⟨h', hh'⟩ := tsum_ne_zero_exists hq'
  set e' : ResolvedExec State Label :=
    ⟨e.init, e.trans.append (Seq.cons ((l, μ), q') Seq.nil)⟩ with he'
  -- Step 3: some level `N` has nonzero reach-after; `N ≠ 0` since `e'.trans` is nonempty.
  unfold LowerReachProb at hh'
  obtain ⟨N, hN⟩ := tsum_ne_zero_exists hh'
  set c : LowerConfig sys := ⟨de, e', h'⟩ with hc
  have hT : e.trans.Terminates := ⟨n, hterm⟩
  have he'_get : e'.trans.get? (Nat.find hT) = some ((l, μ), q') := by
    rw [he']
    change (e.trans.append (Seq.cons ((l, μ), q') Seq.nil)).get? (Nat.find hT + 0) = _
    rw [Stream'.Seq.get?_append_find hT]; rfl
  have he'_ne_nil : e'.trans ≠ Seq.nil := by
    intro hnil
    rw [hnil, Stream'.Seq.get?_nil] at he'_get
    exact absurd he'_get (by simp)
  have hN0 : N ≠ 0 := by
    intro h0
    subst h0
    rw [LowerReachAfter_zero] at hN
    by_cases hcnd : c.de = ⟨PMF.pure sys.init, Seq.nil⟩ ∧ c.e = ⟨sys.init, Seq.nil⟩
    · exact he'_ne_nil (by rw [show e' = c.e from rfl, hcnd.2])
    · rw [if_neg hcnd] at hN; exact hN rfl
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  -- Step 4: the last instruction has a nonzero-mass predecessor `c₀`, which is `Coupled`.
  rw [LowerReachAfter_succ] at hN
  obtain ⟨c₀, hc₀ne⟩ := tsum_ne_zero_exists hN
  have hreach₀ : LowerReachAfter F sch k c₀ ≠ 0 := fun h => hc₀ne (by rw [h, zero_mul])
  have hstep₀ : LowerStep F sch c₀ c ≠ 0 := fun h => hc₀ne (by rw [h, mul_zero])
  have hcoup₀ : Coupled c₀ := reachAfter_coupled F sch k c₀ hreach₀
  -- Step 5: unfold `LowerStep` to read off `c₀.h`, the labels and `μ`, and identify `c₀.e = e`.
  revert hstep₀
  unfold LowerStep
  cases hh : c₀.h with
  | none => intro hstep₀; exact absurd rfl hstep₀
  | some lω =>
    obtain ⟨l₀, ω₀⟩ := lω
    simp only
    set μ'₀ : PMF State := lastMuOf c.e with hμ'₀
    by_cases hif : c.de.init = c₀.de.init ∧ c.e.init = c₀.e.init ∧
        c.de.trans = c₀.de.trans.append (Seq.cons ((l₀, ω₀), lastStateOf c.de) Seq.nil) ∧
        c.e.trans = c₀.e.trans.append (Seq.cons ((l₀, μ'₀), lastStateOf c.e) Seq.nil)
    · rw [if_pos hif]
      intro hweight
      obtain ⟨_, hinit_e, _, he_trans⟩ := hif
      -- Two append-of-singleton forms for `c.e.trans` (`= e'.trans`).
      have hcet : c.e.trans = e.trans.append (Seq.cons ((l, μ), q') Seq.nil) := by
        rw [show c.e = e' from rfl, he']
      have happ : e.trans.append (Seq.cons ((l, μ), q') Seq.nil)
          = c₀.e.trans.append (Seq.cons ((l₀, μ'₀), lastStateOf c.e) Seq.nil) := by
        rw [← hcet]; exact he_trans
      have hlast := Stream'.Seq.append_singleton_inj_right e.trans c₀.e.trans hT hcoup₀.2.1
        _ _ happ
      have htrans_eq := Stream'.Seq.append_singleton_inj_left e.trans c₀.e.trans hT hcoup₀.2.1
        _ _ happ
      -- Decode the last-element equality: `l₀ = l`, `μ'₀ = μ`.
      rw [Prod.mk.injEq, Prod.mk.injEq] at hlast
      obtain ⟨⟨hl, hμeq⟩, _⟩ := hlast
      -- Identify `c₀.e = e`: same init and same trans.
      have hce_init : c.e.init = e.init := rfl
      have hc₀e_init : c₀.e.init = e.init := by rw [← hinit_e, hce_init]
      have hc₀e_eq : c₀.e = e := alterSeq_ext hc₀e_init htrans_eq.symm
      -- Step 6: rewrite the goal into `tKernel_step` shape.
      have hst : st = lastStateOf c₀.e := by
        rw [hc₀e_eq]; exact stateAt_terminatedAt_eq_lastStateOf e n st hterm hstate
      -- The sampled `μ'₀` lies in the kernel's support (nonzero first weight factor).
      have hmemK : μ'₀ ∈ (tKernel F (lastStateOf c₀.de) l₀ ω₀ (lastStateOf c₀.e)).support := by
        rw [PMF.mem_support_iff]
        intro h0; apply hweight
        simp only [h0, zero_mul]
      -- (b) `(sys.distF F).step (lastStateOf c₀.de) l₀ ω₀` via scheduler validity.
      have hde_term : c₀.de.trans.Terminates := hcoup₀.1
      have hnext_ne : sch.next c₀.de c₀.h ≠ 0 :=
        reachAfter_next_ne_zero F sch k c₀ hreach₀
      rw [hh] at hnext_ne
      have hmem_sch : some (l₀, ω₀) ∈ (sch.next c₀.de).support :=
        (PMF.mem_support_iff _ _).mpr hnext_ne
      have hde_state : c₀.de.stateAt (Nat.find hde_term) = some (lastStateOf c₀.de) := by
        have := AlterSeq.stateAt_find_eq_endState c₀.de hde_term
        rw [this]
        congr 1
        unfold lastStateOf; rw [dif_pos hde_term]
      have hstepF : (sys.distF F).step (lastStateOf c₀.de) l₀ ω₀ :=
        sch.valid c₀.de (Nat.find hde_term) (lastStateOf c₀.de) (Nat.find_spec hde_term)
          hde_state l₀ ω₀ hmem_sch
      -- Assemble: `sys.step st l μ = sys.step (last c₀.e) l₀ μ'₀`.
      rw [hst, hμeq, hl]
      exact tKernel_step F (lastStateOf c₀.de) l₀ ω₀ (lastStateOf c₀.e) μ'₀ hmemK hcoup₀.2.2 hstepF
    · rw [if_neg hif]; intro hstep₀; exact absurd rfl hstep₀

/-- The **reconstructed resolved scheduler** `s'` on `sys`, read off the lowering chain of `sch`. -/
noncomputable def lowerSched (F : Fairness sys) (sch : ResolvedScheduler (sys.distF F)) :
    ResolvedScheduler sys where
  next := fun e => lowerNext F sch e
  valid := fun e n st hterm hstate l μ hmem =>
    lowerNext_valid_step F sch e n st l μ hterm hstate hmem

end LoweringChain

end PLTS
