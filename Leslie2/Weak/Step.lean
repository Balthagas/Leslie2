/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Weak.Scheduler

/-!
# Weak transitions

A probabilistic forward simulation between two PLTS over a common label
alphabet is a state relation `R` such that initial concrete states are
matched by initial abstract states with which they are `R`-related, and every
concrete transition can be matched by an abstract transition whose resulting
distribution is related to the concrete one in the sense of a *coupling*: a
joint distribution with the appropriate marginals whose support lies in `R`.
-/

open Stream'

namespace PLTS

-- The canonical-`τ` instance `[Silent Label]` is threaded as a section variable
-- but is unused by the pure helper lemmas; silence the over-inclusion linter.
set_option linter.unusedSectionVars false

variable {α β State State_C State_A Label : Type} [Silent Label]

open Classical in
/-- Weak (internal) transition `μ_init ⇒^τ μ`: there is a weak (internal-only)
scheduler `σ` that, run from `μ_init`, **halts almost surely** — the total
halting mass `∑' e, σ.haltMass μ_init e` (over terminating finite executions)
equals `1` — and whose distribution of *final* states equals `μ`, i.e. `μ` is
the image of the halting distribution on executions under the last-state map
`AlterSeq.endState`.

This is the run-to-halt semantics of the τ-closure: the process takes
internal steps until it spontaneously stops, and `μ` records where it stops. The
"from a single state" case is recovered as `weakTau sys (PMF.pure s) μ`. -/
def weakTau (sys : System State Label)
    (μ_init : PMF State) (μ : PMF State) : Prop :=
  ∃ σ : WeakScheduler sys,
    (∑' e, σ.haltMass μ_init e) = 1 ∧
    ∀ s, μ s = ∑' e, σ.haltMass μ_init e * (if e.1.endState e.2 = s then 1 else 0)

namespace weakTau

variable {sys : System State Label} {μ_init μ : PMF State}

/-- Classical extraction of the witnessing a.s.-stopping weak scheduler. -/
noncomputable def witnessScheduler (h : weakTau sys μ_init μ) : WeakScheduler sys :=
  h.choose

/-- The witnessing scheduler halts almost surely: its total halting mass is `1`. -/
theorem witness_halts (h : weakTau sys μ_init μ) :
    (∑' e, h.witnessScheduler.haltMass μ_init e) = 1 :=
  h.choose_spec.1

open Classical in
/-- The target distribution `μ` is the halting pushforward of the witness under
the last-state map. -/
theorem witness_pushforward (h : weakTau sys μ_init μ) (s : State) :
    μ s = ∑' e, h.witnessScheduler.haltMass μ_init e * (if e.1.endState e.2 = s then 1 else 0) :=
  h.choose_spec.2 s

/-- **Single-step τ-collapse (`g`-integrated).** Running the witnessing internal
scheduler and integrating any `g` over the halting end-state equals integrating
`g` against the τ-closure outcome `μ` — the run-to-halt analogue of the
`bind id`-collapse, and the form the trace-cone induction (M2) consumes. -/
theorem integrate (h : weakTau sys μ_init μ) (g : State → ENNReal) :
    (∑' e, h.witnessScheduler.haltMass μ_init e * g (e.1.endState e.2))
      = ∑' s, μ s * g s := by
  classical
  symm
  calc (∑' s, μ s * g s)
      = ∑' s, (∑' e, h.witnessScheduler.haltMass μ_init e *
            (if e.1.endState e.2 = s then 1 else 0)) * g s :=
        tsum_congr (fun s => by rw [h.witness_pushforward s])
    _ = ∑' s, ∑' e, h.witnessScheduler.haltMass μ_init e *
            (if e.1.endState e.2 = s then 1 else 0) * g s :=
        tsum_congr (fun s => by rw [ENNReal.tsum_mul_right])
    _ = ∑' e, ∑' s, h.witnessScheduler.haltMass μ_init e *
            (if e.1.endState e.2 = s then 1 else 0) * g s := ENNReal.tsum_comm
    _ = ∑' e, h.witnessScheduler.haltMass μ_init e * g (e.1.endState e.2) := by
        refine tsum_congr (fun e => ?_)
        rw [tsum_congr (fun s => by ring :
            ∀ s, h.witnessScheduler.haltMass μ_init e *
                (if e.1.endState e.2 = s then 1 else 0) * g s
              = h.witnessScheduler.haltMass μ_init e *
                ((if e.1.endState e.2 = s then 1 else 0) * g s)),
          ENNReal.tsum_mul_left]
        congr 1
        rw [tsum_eq_single (e.1.endState e.2)
            (fun s' hs' => by rw [if_neg (fun heq => hs' heq.symm), zero_mul]),
          if_pos rfl, one_mul]

end weakTau

/-- Reindexing helper for halting-mass sums supported on a single state-indexed
fiber of terminating executions: if `F` is supported on `{fiber s | s : State}`
and `fiber` is injective, then `∑' e, F e = ∑' s, F ⟨fiber s, hterm s⟩`. -/
private theorem weakTau_reindex_fiber
    {State Label : Type}
    (fiber : State → AlterSeq State Label)
    (hterm : ∀ s, (fiber s).trans.Terminates)
    (hinj : Function.Injective fiber)
    (F : {e : AlterSeq State Label // e.trans.Terminates} → ENNReal)
    (hsupp : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
        F e ≠ 0 → ∃ s, fiber s = e.1) :
    (∑' e, F e) = ∑' s, F ⟨fiber s, hterm s⟩ := by
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun x =>
      (⟨fiber (x : State), hterm x⟩ : {e : AlterSeq State Label // e.trans.Terminates}))
    ?_ ?_ ?_
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext (hinj hab)
  · intro e he
    obtain ⟨s, hs⟩ := hsupp e (Function.mem_support.mp he)
    have hes : (⟨fiber s, hterm s⟩ : {e : AlterSeq State Label // e.trans.Terminates}) = e :=
      Subtype.ext hs
    refine ⟨⟨s, ?_⟩, ?_⟩
    · change F ⟨fiber s, hterm s⟩ ≠ 0
      rw [hes]; exact Function.mem_support.mp he
    · exact Subtype.ext hs
  · intro x
    rfl

/-- Reflexivity of `weakTau`: every distribution is weak-τ-related to itself,
witnessed by the stop-everywhere weak scheduler (it halts immediately, so its
halting distribution is `μ` placed on the empty executions `⟨·, nil⟩`). -/
theorem weakTau_refl (ls : System State Label) (μ : PMF State) :
    weakTau ls μ μ := by
  classical
  set pe : ProbabilisticExecution ls := ⟨μ, (WeakScheduler.stop ls).toScheduler⟩ with hpe
  -- The stop scheduler's one-step kernel vanishes everywhere.
  have hker : ∀ (e' : AlterSeq State Label) (st : Label × State), pe.kernel e' st = 0 := by
    intro e' st
    unfold ProbabilisticExecution.kernel
    have h0 : ∀ ν : PMF State, pe.scheduler.next e' (some (st.1, ν)) = 0 := by
      intro ν; exact PMF.pure_apply_of_ne _ _ (by simp)
    simp only [h0, zero_mul, tsum_zero]
  -- `probOf` of any non-trivial execution vanishes.
  have hprob_nonnil : ∀ (e' : AlterSeq State Label) (h : e'.trans.Terminates),
      e'.trans ≠ Seq.nil → pe.probOf e' h = 0 := by
    rintro ⟨init', trans'⟩ h hne
    simp only at h hne ⊢
    have hnonempty : trans'.toList h ≠ [] := by
      intro hnil; apply hne
      have := Stream'.Seq.ofList_toList trans' h
      rw [hnil, Stream'.Seq.ofList_nil] at this; exact this.symm
    obtain ⟨previous, last, h_prev, h_split, _, _⟩ :=
      Stream'.Seq.exists_split_last trans' h hnonempty
    subst h_split
    rw [ProbabilisticExecution.probOf_append_singleton _ _ _ h_prev _ h, hker, mul_zero]
  -- The halting mass is supported on the nil fiber `fiber s = ⟨s, nil⟩`, with value `μ s`.
  have hfiber_term : ∀ s : State, (⟨s, Seq.nil⟩ : AlterSeq State Label).trans.Terminates :=
    fun _ => Stream'.Seq.terminates_nil
  have hfiber_inj :
      Function.Injective (fun s : State => (⟨s, Seq.nil⟩ : AlterSeq State Label)) := by
    intro a b hab; exact congrArg AlterSeq.init hab
  have hnext1 : ∀ e' : AlterSeq State Label, (WeakScheduler.stop ls).next e' none = 1 :=
    fun _ => PMF.pure_apply_self none
  have hhalt_fiber : ∀ s : State,
      (WeakScheduler.stop ls).haltMass μ ⟨⟨s, Seq.nil⟩, hfiber_term s⟩ = μ s := by
    intro s
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [← hpe]
    have hp : pe.probOf ⟨s, Seq.nil⟩ Stream'.Seq.terminates_nil = μ s := by
      rw [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState]
    rw [hp, hnext1, mul_one]
  -- Support condition: any `e` with nonzero halting mass has `nil` trans, so lies on the fiber.
  have hsupp : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      (WeakScheduler.stop ls).haltMass μ e ≠ 0 →
      ∃ s, (⟨s, Seq.nil⟩ : AlterSeq State Label) = e.1 := by
    intro e hne
    refine ⟨e.1.init, ?_⟩
    by_contra hcontra
    apply hne
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [← hpe]
    have htrans : e.1.trans ≠ Seq.nil := by
      intro hnil
      apply hcontra
      cases e with | mk e' he' => cases e' with | mk i t => simp only at hnil ⊢; rw [hnil]
    rw [hprob_nonnil e.1 e.2 htrans, zero_mul]
  refine ⟨WeakScheduler.stop ls, ?_, ?_⟩
  · rw [weakTau_reindex_fiber (fun s => ⟨s, Seq.nil⟩) hfiber_term hfiber_inj
      ((WeakScheduler.stop ls).haltMass μ) hsupp]
    simp only [hhalt_fiber]
    exact μ.tsum_coe
  · intro s
    rw [weakTau_reindex_fiber (fun s' => ⟨s', Seq.nil⟩) hfiber_term hfiber_inj
      (fun e => (WeakScheduler.stop ls).haltMass μ e *
        (if e.1.endState e.2 = s then 1 else 0)) ?_]
    · -- collapse the indicator: endState ⟨s', nil⟩ = s' and `tsum_eq_single s`
      have hterm_eq : ∀ s' : State,
          (WeakScheduler.stop ls).haltMass μ ⟨⟨s', Seq.nil⟩, hfiber_term s'⟩ *
            (if (⟨s', Seq.nil⟩ : AlterSeq State Label).endState (hfiber_term s') = s
              then 1 else 0)
          = μ s' * (if s' = s then 1 else 0) := by
        intro s'
        rw [hhalt_fiber s', AlterSeq.endState_of_trans_nil _ rfl]
      rw [tsum_congr hterm_eq, tsum_eq_single s (by
        intro b hb; rw [if_neg hb, mul_zero])]
      rw [if_pos rfl, mul_one]
    · intro e hne
      refine ⟨e.1.init, ?_⟩
      by_contra hcontra
      apply hne
      have htrans : e.1.trans ≠ Seq.nil := by
        intro hnil
        apply hcontra
        cases e with | mk e' he' => cases e' with | mk i t => simp only at hnil ⊢; rw [hnil]
      have : (WeakScheduler.stop ls).haltMass μ e = 0 := by
        unfold WeakScheduler.haltMass Scheduler.haltMass
        rw [← hpe, hprob_nonnil e.1 e.2 htrans, zero_mul]
      rw [this, zero_mul]

/-- The lifting of `sys.step` from `State → Label → PMF State → Prop` to a
relation on initial and final distributions, parameterised by a label, *closed
under convex combinations* of valid system steps.

`hyperStep sys μ_pre l μ_post` holds iff there is an assignment
`p : State → PMF (PMF State)` choosing, for every starting state, a
randomised mixture of successor-distributions, such that

* every `s ∈ μ_pre.support` and every `μ ∈ (p s).support` takes a valid step
  `sys.step s l μ`;
* `μ_post` is the resulting bind:
  `μ_post = μ_pre.bind (fun s => (p s).bind id)`.

Allowing `p s` to be a `PMF (PMF State)` (rather than a single `PMF State`)
makes the relation closed under convex combinations of hyper-steps. In the
singleton case `μ_pre = PMF.pure s` it reduces to: `μ_post` is in the convex
hull of `{μ | sys.step s l μ}`. Every state in `μ_pre.support` must
contribute a real step — there is no stutter freedom for internal labels. -/
def hyperStep (sys : System State Label)
    (μ_pre : PMF State) (l : Label) (μ_post : PMF State) : Prop :=
  ∃ p : State → PMF (PMF State),
    (∀ s ∈ μ_pre.support, ∀ μ ∈ (p s).support, sys.step s l μ) ∧
    μ_post = μ_pre.bind (fun s => (p s).bind id)

namespace hyperStep

variable {sys : System State Label} {μ_pre μ_post : PMF State} {l : Label}

/-- Classical extraction of the per-state successor kernel from a `hyperStep`
proof. -/
noncomputable def kernel (h : hyperStep sys μ_pre l μ_post) :
    State → PMF (PMF State) := h.choose

/-- Every distribution in the kernel's support is a valid system step. -/
theorem kernel_step (h : hyperStep sys μ_pre l μ_post) :
    ∀ s ∈ μ_pre.support, ∀ μ ∈ (h.kernel s).support, sys.step s l μ :=
  h.choose_spec.1

/-- The post-distribution is the bind of `μ_pre` with the flattened kernel. -/
theorem post_eq_bind (h : hyperStep sys μ_pre l μ_post) :
    μ_post = μ_pre.bind (fun s => (h.kernel s).bind id) :=
  h.choose_spec.2

end hyperStep

/-- A strong system step lifts to a hyper-step on a singleton initial
distribution: if `sys.step s l μ`, then `hyperStep sys (PMF.pure s) l μ`. -/
theorem hyperStep_pure_of_step
    {sys : System State Label} {s : State} {l : Label} {μ : PMF State}
    (h : sys.step s l μ) :
    hyperStep sys (PMF.pure s) l μ := by
  refine ⟨fun _ => PMF.pure μ, ?_, ?_⟩
  · intro s' h_s' μ' h_μ'
    rw [PMF.mem_support_pure_iff] at h_s' h_μ'
    subst h_s'
    subst h_μ'
    exact h
  · simp [PMF.pure_bind]

/-- The weak external step `μ_init ⇒^l μ_final`, composing the three layers
`τ-closure → hyper-step with label l → τ-closure`. Concretely there exist
intermediate distributions `μ, μ'` with

* `μ_init ⇒^τ μ` (a `weakTau`),
* `μ -[l]→ μ'` (a `hyperStep` with label `l`),
* `μ' ⇒^τ μ_final` (another `weakTau`).

Defined uniformly for any label `l`. For external (non-`internal`) labels this
is the standard weak step; for internal labels it is one strictly forced
internal hyper-step sandwiched between two τ-closures (which is *not* the same
as `weakTau` — for τ-labels, prefer `weakTau` directly). -/
def weakStep (sys : System State Label)
    (μ_init : PMF State) (l : Label) (μ_final : PMF State) : Prop :=
  ∃ μ μ' : PMF State,
    weakTau sys μ_init μ ∧
    hyperStep sys μ l μ' ∧
    weakTau sys μ' μ_final

namespace weakStep

variable {sys : System State Label} {μ_init μ_final : PMF State} {l : Label}

/-- Classical extraction of the post-τ-closure intermediate distribution. -/
noncomputable def preDist (h : weakStep sys μ_init l μ_final) : PMF State :=
  h.choose

/-- Classical extraction of the post-`l`-step intermediate distribution. -/
noncomputable def postDist (h : weakStep sys μ_init l μ_final) : PMF State :=
  h.choose_spec.choose

/-- The τ-closure before the external step. -/
theorem weakTau_pre (h : weakStep sys μ_init l μ_final) :
    weakTau sys μ_init h.preDist :=
  h.choose_spec.choose_spec.1

/-- The external step itself, as a `hyperStep`. -/
theorem hyperStep_mid (h : weakStep sys μ_init l μ_final) :
    hyperStep sys h.preDist l h.postDist :=
  h.choose_spec.choose_spec.2.1

/-- The τ-closure after the external step. -/
theorem weakTau_post (h : weakStep sys μ_init l μ_final) :
    weakTau sys h.postDist μ_final :=
  h.choose_spec.choose_spec.2.2

end weakStep

/-- A strong system step lifts to a weak step on a singleton initial
distribution: if `sys.step s l μ`, then `weakStep sys (PMF.pure s) l μ`. Both
τ-closure layers are trivial reflexivities. -/
theorem weakStep_strong {ls : System State Label}
    {s : State} {l : Label} {μ : PMF State}
    (h_step : ls.step s l μ) :
    weakStep ls (PMF.pure s) l μ :=
  ⟨PMF.pure s, μ, weakTau_refl ls (PMF.pure s),
    hyperStep_pure_of_step h_step, weakTau_refl ls μ⟩

/-- A strong system step at an *internal* label lifts to a `weakTau` from the
Dirac source: a one-step WeakScheduler emitting `(l, μ)` then halting witnesses
`weakTau ls (PMF.pure s) μ`. -/
theorem weakTau_of_step {ls : System State Label}
    {s : State} {l : Label} {μ : PMF State}
    (h_int : (l = Silent.τ)) (h_step : ls.step s l μ) :
    weakTau ls (PMF.pure s) μ := by
  classical
  let σ : WeakScheduler ls :=
    { next := fun e' =>
        if e'.init = s ∧ e'.trans = Seq.nil then PMF.pure (some (l, μ)) else PMF.pure none
      valid := by
        intro e' n s' h_term h_state l' μ' h_supp
        by_cases h_cond : e'.init = s ∧ e'.trans = Seq.nil
        · simp only [if_pos h_cond, PMF.mem_support_pure_iff, Option.some.injEq,
            Prod.mk.injEq] at h_supp
          obtain ⟨h_l, h_μ⟩ := h_supp; subst h_l; subst h_μ
          have h_init_eq : s' = s := by
            rcases Nat.eq_zero_or_pos n with hn | hn
            · subst hn
              have : e'.stateAt 0 = some e'.init := rfl
              rw [this, h_cond.1] at h_state; exact (Option.some.inj h_state).symm
            · exfalso
              obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
              rw [hk] at h_state
              change (e'.trans.get? k).map Prod.snd = some s' at h_state
              rw [h_cond.2] at h_state; simp at h_state
          rw [h_init_eq]; exact h_step
        · simp only [if_neg h_cond, PMF.mem_support_pure_iff] at h_supp
          exact absurd h_supp (by simp)
      internal_only := by
        intro e' l' μ' h_supp
        by_cases h_cond : e'.init = s ∧ e'.trans = Seq.nil
        · simp only [if_pos h_cond, PMF.mem_support_pure_iff, Option.some.injEq,
            Prod.mk.injEq] at h_supp
          rw [h_supp.1]; exact h_int
        · simp only [if_neg h_cond, PMF.mem_support_pure_iff] at h_supp
          exact absurd h_supp (by simp) }
  set pe : ProbabilisticExecution ls := ⟨PMF.pure s, σ.toScheduler⟩ with hpe
  -- The scheduler's emission at the empty prefix `⟨s, nil⟩` is `pure (some (l, μ))`.
  have hnext_nil : σ.next ⟨s, Seq.nil⟩ = PMF.pure (some (l, μ)) := by
    change (if (s = s ∧ (Seq.nil : Seq (Label × State)) = Seq.nil)
      then PMF.pure (some (l, μ)) else PMF.pure none) = _
    rw [if_pos ⟨rfl, rfl⟩]
  -- The single-transition fiber `⟨s, cons (l, s') nil⟩` terminates.
  have hcons_term : ∀ s' : State, (Seq.cons (l, s') Seq.nil : Seq (Label × State)).Terminates :=
    fun _ => Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
  -- The one-step kernel at the empty prefix sends `(l, s')` to `μ s'`.
  have hker_nil : ∀ s' : State, pe.kernel ⟨s, Seq.nil⟩ (l, s') = μ s' := by
    intro s'
    unfold ProbabilisticExecution.kernel
    have hsched : pe.scheduler.next ⟨s, Seq.nil⟩ = PMF.pure (some (l, μ)) := by
      rw [hpe]; exact hnext_nil
    simp only [hsched]
    have hnn : ∀ ν : PMF State,
        (PMF.pure (some (l, μ)) : PMF (Option (Label × PMF State))) (some ((l, s').1, ν))
          = if ν = μ then 1 else 0 := by
      intro ν
      by_cases h : ν = μ
      · rw [h, if_pos rfl]; exact PMF.pure_apply_self _
      · rw [if_neg h]; exact PMF.pure_apply_of_ne _ _ (by simp [h])
    simp only [hnn]
    rw [tsum_eq_single μ (by intro b hb; rw [if_neg hb, zero_mul]), if_pos rfl, one_mul]
  -- `probOf` of the single-transition fiber is `μ s'`.
  have hprob_fiber : ∀ s' : State,
      pe.probOf ⟨s, Seq.cons (l, s') Seq.nil⟩ (hcons_term s') = μ s' := by
    intro s'
    have happ : (Seq.nil.append (Seq.cons (l, s') Seq.nil) : Seq (Label × State)).Terminates := by
      rw [Stream'.Seq.nil_append]; exact hcons_term s'
    have hrw : pe.probOf ⟨s, Seq.cons (l, s') Seq.nil⟩ (hcons_term s')
        = pe.probOf ⟨s, Seq.nil.append (Seq.cons (l, s') Seq.nil)⟩ happ := by
      congr 1
      rw [Stream'.Seq.nil_append]
    rw [hrw, ProbabilisticExecution.probOf_append_singleton _ _ _ Stream'.Seq.terminates_nil _ happ,
      ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState, hker_nil]
    rw [hpe]; change (PMF.pure s) s * μ s' = μ s'
    rw [PMF.pure_apply_self, one_mul]
  -- The scheduler emits `⊥` (mass 1) off the active prefix, mass 0 on it.
  have hnext_none : ∀ e' : AlterSeq State Label,
      ¬(e'.init = s ∧ e'.trans = Seq.nil) → σ.next e' none = 1 := by
    intro e' hcond
    change (if e'.init = s ∧ e'.trans = Seq.nil
      then PMF.pure (some (l, μ)) else PMF.pure none) none = 1
    rw [if_neg hcond]; exact PMF.pure_apply_self none
  have hnext_none_zero : ∀ e' : AlterSeq State Label,
      (e'.init = s ∧ e'.trans = Seq.nil) → σ.next e' none = 0 := by
    intro e' hcond
    change (if e'.init = s ∧ e'.trans = Seq.nil
      then PMF.pure (some (l, μ)) else PMF.pure none) none = 0
    rw [if_pos hcond]; exact PMF.pure_apply_of_ne _ _ (by simp)
  -- A nonzero one-step kernel forces the active-prefix shape.
  have hker_ne : ∀ (init : State) (previous : Seq (Label × State)) (last : Label × State),
      pe.kernel ⟨init, previous⟩ last ≠ 0 → (init = s ∧ previous = Seq.nil ∧ last.1 = l) := by
    intro init previous last hne
    by_cases hcond : init = s ∧ previous = Seq.nil
    · refine ⟨hcond.1, hcond.2, ?_⟩
      by_contra hl
      apply hne
      unfold ProbabilisticExecution.kernel
      have hsched : pe.scheduler.next ⟨init, previous⟩ = PMF.pure (some (l, μ)) := by
        rw [hpe]
        change (if init = s ∧ previous = Seq.nil
          then PMF.pure (some (l, μ)) else PMF.pure none) = _
        rw [if_pos hcond]
      simp only [hsched]
      have hz : ∀ ν : PMF State,
          (PMF.pure (some (l, μ)) : PMF (Option (Label × PMF State))) (some (last.1, ν)) = 0 :=
        fun ν => PMF.pure_apply_of_ne _ _ (by simp [hl])
      simp only [hz, zero_mul, tsum_zero]
    · exfalso
      apply hne
      unfold ProbabilisticExecution.kernel
      have hsched : pe.scheduler.next ⟨init, previous⟩ = PMF.pure none := by
        rw [hpe]
        change (if init = s ∧ previous = Seq.nil
          then PMF.pure (some (l, μ)) else PMF.pure none) = _
        rw [if_neg hcond]
      simp only [hsched]
      have hz : ∀ ν : PMF State,
          (PMF.pure none : PMF (Option (Label × PMF State))) (some (last.1, ν)) = 0 :=
        fun ν => PMF.pure_apply_of_ne _ _ (by simp)
      simp only [hz, zero_mul, tsum_zero]
  -- Fiber data for reindexing.
  have hfiber_term : ∀ s' : State,
      (⟨s, Seq.cons (l, s') Seq.nil⟩ : AlterSeq State Label).trans.Terminates :=
    fun s' => hcons_term s'
  have hfiber_inj :
      Function.Injective
        (fun s' : State => (⟨s, Seq.cons (l, s') Seq.nil⟩ : AlterSeq State Label)) := by
    intro a b hab
    have htrans := congrArg AlterSeq.trans hab
    simp only at htrans
    have hpair := (Stream'.Seq.cons_eq_cons.mp htrans).1
    exact (Prod.mk.injEq l a l b ▸ hpair).2
  -- The halting mass on the fiber is `μ s'`.
  have hhalt_fiber : ∀ s' : State,
      σ.haltMass (PMF.pure s) ⟨⟨s, Seq.cons (l, s') Seq.nil⟩, hfiber_term s'⟩ = μ s' := by
    intro s'
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [← hpe, hprob_fiber s']
    rw [hnext_none ⟨s, Seq.cons (l, s') Seq.nil⟩ (by
      rintro ⟨_, htr⟩; exact absurd htr (by simp)), mul_one]
  -- Support condition: nonzero halting mass forces the single-transition fiber.
  have hsupp : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      σ.haltMass (PMF.pure s) e ≠ 0 →
      ∃ s', (⟨s, Seq.cons (l, s') Seq.nil⟩ : AlterSeq State Label) = e.1 := by
    rintro ⟨⟨init', trans'⟩, hterm⟩ hne
    simp only at hterm hne ⊢
    -- Split the two factors of `haltMass`.
    have hprob_ne : pe.probOf ⟨init', trans'⟩ hterm ≠ 0 := by
      intro h0; apply hne
      unfold WeakScheduler.haltMass Scheduler.haltMass; rw [← hpe, h0, zero_mul]
    have hnone_ne : σ.next ⟨init', trans'⟩ none ≠ 0 := by
      intro h0; apply hne
      unfold WeakScheduler.haltMass Scheduler.haltMass; rw [← hpe, h0, mul_zero]
    have hncond : ¬((⟨init', trans'⟩ : AlterSeq State Label).init = s ∧
        (⟨init', trans'⟩ : AlterSeq State Label).trans = Seq.nil) := by
      intro hcond; exact hnone_ne (hnext_none_zero _ hcond)
    -- `trans' ≠ nil`: else `probOf` would be `(pure s) init' = 0` since `init' ≠ s`.
    have htrans_ne : trans' ≠ Seq.nil := by
      intro hnil
      apply hncond
      refine ⟨?_, hnil⟩
      by_contra hinit
      apply hprob_ne
      have hrw : pe.probOf ⟨init', trans'⟩ hterm
          = pe.probOf ⟨init', Seq.nil⟩ Stream'.Seq.terminates_nil := by
        subst hnil; rfl
      rw [hrw, ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState, hpe]
      exact PMF.pure_apply_of_ne _ _ hinit
    -- Peel the last transition.
    have hnonempty : trans'.toList hterm ≠ [] := by
      intro hnil; apply htrans_ne
      have := Stream'.Seq.ofList_toList trans' hterm
      rw [hnil, Stream'.Seq.ofList_nil] at this; exact this.symm
    obtain ⟨previous, last, h_prev, h_split, _, _⟩ :=
      Stream'.Seq.exists_split_last trans' hterm hnonempty
    -- `probOf = probOf ⟨init', previous⟩ * kernel ⟨init', previous⟩ last`.
    have hprob_split : pe.probOf ⟨init', trans'⟩ hterm
        = pe.probOf ⟨init', previous⟩ h_prev * pe.kernel ⟨init', previous⟩ last := by
      have happ : (previous.append (Seq.cons last Seq.nil)).Terminates := h_split ▸ hterm
      have hrw : pe.probOf ⟨init', trans'⟩ hterm
          = pe.probOf ⟨init', previous.append (Seq.cons last Seq.nil)⟩ happ := by
        exact h_split ▸ rfl
      rw [hrw, ProbabilisticExecution.probOf_append_singleton _ _ _ h_prev _ happ]
    have hker_ne' : pe.kernel ⟨init', previous⟩ last ≠ 0 := by
      intro h0; apply hprob_ne; rw [hprob_split, h0, mul_zero]
    obtain ⟨hinit_eq, hprev_nil, hlast⟩ := hker_ne _ _ _ hker_ne'
    -- Reassemble: `trans' = cons (l, last.2) nil`, `init' = s`.
    refine ⟨last.2, ?_⟩
    have htrans_eq : trans' = Seq.cons (l, last.2) Seq.nil := by
      rw [h_split, hprev_nil, Stream'.Seq.nil_append]
      obtain ⟨l', s'⟩ := last
      simp only at hlast
      rw [hlast]
    rw [hinit_eq] at *
    exact AlterSeq.mk.injEq .. ▸ ⟨rfl, htrans_eq.symm⟩
  -- Assemble the `weakTau` witness.
  refine ⟨σ, ?_, ?_⟩
  · rw [weakTau_reindex_fiber (fun s' => ⟨s, Seq.cons (l, s') Seq.nil⟩) hfiber_term hfiber_inj
      (σ.haltMass (PMF.pure s)) hsupp]
    simp only [hhalt_fiber]
    exact μ.tsum_coe
  · intro t
    rw [weakTau_reindex_fiber (fun s' => ⟨s, Seq.cons (l, s') Seq.nil⟩) hfiber_term hfiber_inj
      (fun e => σ.haltMass (PMF.pure s) e * (if e.1.endState e.2 = t then 1 else 0)) ?_]
    · have hterm_eq : ∀ s' : State,
          σ.haltMass (PMF.pure s) ⟨⟨s, Seq.cons (l, s') Seq.nil⟩, hfiber_term s'⟩ *
            (if (⟨s, Seq.cons (l, s') Seq.nil⟩ : AlterSeq State Label).endState
              (hfiber_term s') = t then 1 else 0)
          = μ s' * (if s' = t then 1 else 0) := by
        intro s'
        rw [hhalt_fiber s', AlterSeq.endState_singleton_cons]
      rw [tsum_congr hterm_eq, tsum_eq_single t (by intro b hb; rw [if_neg hb, mul_zero]),
        if_pos rfl, mul_one]
    · intro e hne
      obtain ⟨s', hs'⟩ := hsupp e (by
        intro h0; apply hne; rw [h0, zero_mul])
      exact ⟨s', hs'⟩

/-! ### Helpers for `weakTau` transitivity -/

/-- `AlterSeq` equality from equal components. -/
private theorem AlterSeq.ext_of {e₁ e₂ : AlterSeq State Label}
    (hi : e₁.init = e₂.init) (ht : e₁.trans = e₂.trans) : e₁ = e₂ := by
  cases e₁; cases e₂; simp_all

/-- `endState` only depends on the underlying `AlterSeq` (termination proofs are
irrelevant). -/
private theorem AlterSeq.endState_congr {e₁ e₂ : AlterSeq State Label}
    (heq : e₁ = e₂) (h₁ : e₁.trans.Terminates) (h₂ : e₂.trans.Terminates) :
    e₁.endState h₁ = e₂.endState h₂ := by
  subst heq; rfl

/-- The end-state of the `j`-suffix `⟨stateAfter e j, e.trans.drop j⟩` equals the
end-state of `e`, for any split `j ≤ length` (extends `endState_drop` to the
boundary case `j = length`). -/
private theorem WeakScheduler.endState_suf (e : AlterSeq State Label)
    (hT : e.trans.Terminates) (j : ℕ) (hj : j ≤ e.trans.length hT) :
    (⟨WeakScheduler.stateAfter e j, e.trans.drop j⟩ : AlterSeq State Label).endState
        (WeakScheduler.drop_terminates hT j) = e.endState hT := by
  rcases lt_or_eq_of_le hj with hlt | heq
  · exact WeakScheduler.endState_drop e hT j hlt
  · -- `j = length`: the suffix's trans is `nil`, end-state is its init = endState.
    subst heq
    have hnil : e.trans.drop (e.trans.length hT) = Seq.nil := by
      apply Stream'.Seq.ext
      intro n
      rw [Stream'.Seq.drop_get?]
      have hterm : e.trans.TerminatedAt (e.trans.length hT) := Nat.find_spec hT
      change e.trans.get? (e.trans.length hT) = none at hterm
      rw [Stream'.Seq.get?_nil]
      exact Stream'.Seq.terminated_stable e.trans (Nat.le_add_right _ n) hterm
    rw [AlterSeq.endState_of_trans_nil _ hnil,
      WeakScheduler.stateAfter_length_eq_endState e hT]

/-- The concatenation of two terminating executions `f₁`, `f₂`: start at
`f₁.init`, follow `f₁`'s transitions then `f₂`'s (as lists). -/
noncomputable def WeakScheduler.concat
    (f₁ f₂ : {e : AlterSeq State Label // e.trans.Terminates}) :
    AlterSeq State Label :=
  ⟨f₁.1.init, Seq.ofList (f₁.1.trans.toList f₁.2 ++ f₂.1.trans.toList f₂.2)⟩

theorem WeakScheduler.concat_terminates
    (f₁ f₂ : {e : AlterSeq State Label // e.trans.Terminates}) :
    (WeakScheduler.concat f₁ f₂).trans.Terminates :=
  Stream'.Seq.terminates_ofList _

/-- The length of the concatenation is the sum of the two lengths. -/
private theorem WeakScheduler.length_concat
    (f₁ f₂ : {e : AlterSeq State Label // e.trans.Terminates}) :
    (WeakScheduler.concat f₁ f₂).trans.length (WeakScheduler.concat_terminates f₁ f₂)
      = f₁.1.trans.length f₁.2 + f₂.1.trans.length f₂.2 := by
  unfold WeakScheduler.concat
  rw [length_ofList, List.length_append, Stream'.Seq.length_toList,
    Stream'.Seq.length_toList]

/-- The `|f₁|`-prefix of `concat f₁ f₂` recovers `f₁`'s transition sequence. -/
private theorem WeakScheduler.take_concat
    (f₁ f₂ : {e : AlterSeq State Label // e.trans.Terminates}) :
    Seq.ofList (Seq.take (f₁.1.trans.length f₁.2) (WeakScheduler.concat f₁ f₂).trans)
      = f₁.1.trans := by
  unfold WeakScheduler.concat
  rw [take_ofList]
  rw [show f₁.1.trans.length f₁.2 = (f₁.1.trans.toList f₁.2).length from
    (Stream'.Seq.length_toList _ _).symm]
  rw [List.take_left, Stream'.Seq.ofList_toList]

/-- The `|f₁|`-suffix of `concat f₁ f₂` recovers `f₂`'s transition sequence. -/
private theorem WeakScheduler.drop_concat
    (f₁ f₂ : {e : AlterSeq State Label // e.trans.Terminates}) :
    (WeakScheduler.concat f₁ f₂).trans.drop (f₁.1.trans.length f₁.2) = f₂.1.trans := by
  unfold WeakScheduler.concat
  rw [drop_ofList]
  rw [show f₁.1.trans.length f₁.2 = (f₁.1.trans.toList f₁.2).length from
    (Stream'.Seq.length_toList _ _).symm]
  rw [List.drop_left, Stream'.Seq.ofList_toList]

/-- `stateAfter (concat f₁ f₂) |f₁|` is `f₁`'s end-state. -/
private theorem WeakScheduler.stateAfter_concat
    (f₁ f₂ : {e : AlterSeq State Label // e.trans.Terminates}) :
    WeakScheduler.stateAfter (WeakScheduler.concat f₁ f₂) (f₁.1.trans.length f₁.2)
      = f₁.1.endState f₁.2 := by
  -- `stateAt (concat) |f₁| = stateAt f₁ |f₁|`, then reduce to `stateAfter f₁ |f₁|`.
  have hinit : (WeakScheduler.concat f₁ f₂).init = f₁.1.init := rfl
  have hstateAt : (WeakScheduler.concat f₁ f₂).stateAt (f₁.1.trans.length f₁.2)
      = f₁.1.stateAt (f₁.1.trans.length f₁.2) := by
    set n := f₁.1.trans.length f₁.2 with hn
    cases hn0 : n with
    | zero => simp only [AlterSeq.stateAt, hinit]
    | succ m =>
      simp only [AlterSeq.stateAt]
      congr 1
      -- `(concat).trans.get? m = f₁.trans.get? m` for `m < |f₁|`.
      have hmlt : m < (f₁.1.trans.toList f₁.2).length := by
        rw [Stream'.Seq.length_toList, ← hn, hn0]; exact Nat.lt_succ_self m
      unfold WeakScheduler.concat
      rw [Stream'.Seq.ofList_get?, List.getElem?_append_left hmlt,
        ← Stream'.Seq.ofList_get?, Stream'.Seq.ofList_toList]
  unfold WeakScheduler.stateAfter
  rw [hstateAt, hinit]
  exact WeakScheduler.stateAfter_length_eq_endState f₁.1 f₁.2

/-- `stateAfter` only depends on the underlying `AlterSeq`. -/
private theorem WeakScheduler.stateAfter_congr {e₁ e₂ : AlterSeq State Label}
    (heq : e₁ = e₂) (j : ℕ) : WeakScheduler.stateAfter e₁ j = WeakScheduler.stateAfter e₂ j := by
  rw [heq]

/-- `toList` only depends on the underlying `Seq` (termination proofs irrelevant). -/
private theorem WeakScheduler.toList_congr_eq {γ : Type} {s₁ s₂ : Seq γ} (heq : s₁ = s₂)
    (h₁ : s₁.Terminates) (h₂ : s₂.Terminates) : s₁.toList h₁ = s₂.toList h₂ := by
  subst heq; rfl

/-- `Seq.take j s` is the `List.take j` of `s.toList`. -/
private theorem WeakScheduler.take_eq_toList_take {γ : Type} (s : Seq γ) (h : s.Terminates)
    (j : ℕ) : Stream'.Seq.take j s = (s.toList h).take j := by
  conv_lhs => rw [← Stream'.Seq.ofList_toList s h]
  rw [take_ofList]

/-- `(s.drop j).toList` is the `List.drop j` of `s.toList`. -/
private theorem WeakScheduler.drop_toList_eq {γ : Type} (s : Seq γ) (h : s.Terminates) (j : ℕ)
    (hd : (s.drop j).Terminates) : (s.drop j).toList hd = (s.toList h).drop j := by
  have key : s.drop j = Seq.ofList ((s.toList h).drop j) := by
    conv_lhs => rw [← Stream'.Seq.ofList_toList s h]
    rw [drop_ofList]
  rw [WeakScheduler.toList_congr_eq key hd (Stream'.Seq.terminates_ofList _),
    Stream'.Seq.toList_ofList]

/-- **Split-then-concatenate is the identity.** Concatenating the `j`-prefix and
`j`-suffix of a terminating execution `e` recovers `e` (`j ≤ length`). -/
private theorem WeakScheduler.concat_split (e : {e : AlterSeq State Label // e.trans.Terminates})
    (j : ℕ) :
    WeakScheduler.concat
        ⟨⟨e.1.init, Seq.ofList (Seq.take j e.1.trans)⟩, Stream'.Seq.terminates_ofList _⟩
        ⟨⟨WeakScheduler.stateAfter e.1 j, e.1.trans.drop j⟩,
          WeakScheduler.drop_terminates e.2 j⟩
      = e.1 := by
  unfold WeakScheduler.concat
  -- the underlying trans is `ofList (take j ++ (drop j).toList) = e.trans`.
  have hlist : (⟨e.1.init, Seq.ofList (Seq.take j e.1.trans)⟩
        : AlterSeq State Label).trans.toList (Stream'.Seq.terminates_ofList _)
      ++ (⟨WeakScheduler.stateAfter e.1 j, e.1.trans.drop j⟩ : AlterSeq State Label).trans.toList
          (WeakScheduler.drop_terminates e.2 j)
      = e.1.trans.toList e.2 := by
    change (Seq.ofList (Seq.take j e.1.trans)).toList (Stream'.Seq.terminates_ofList _)
        ++ (e.1.trans.drop j).toList (WeakScheduler.drop_terminates e.2 j)
      = e.1.trans.toList e.2
    rw [Stream'.Seq.toList_ofList,
      WeakScheduler.take_eq_toList_take e.1.trans e.2 j,
      WeakScheduler.drop_toList_eq e.1.trans e.2 j (WeakScheduler.drop_terminates e.2 j),
      List.take_append_drop]
  -- assemble the `AlterSeq` equality
  change (⟨e.1.init, Seq.ofList _⟩ : AlterSeq State Label) = e.1
  rw [hlist]
  obtain ⟨ev, eh⟩ := e
  simp only
  rw [Stream'.Seq.ofList_toList]

/-- The prefix `pre e j` has length exactly `j` (for `j ≤ length`). -/
private theorem WeakScheduler.length_pre (e : {e : AlterSeq State Label // e.trans.Terminates})
    (j : ℕ) (hj : j ≤ e.1.trans.length e.2) :
    (Seq.ofList (Seq.take j e.1.trans)).length (Stream'.Seq.terminates_ofList _) = j := by
  rw [length_ofList, WeakScheduler.take_eq_toList_take e.1.trans e.2 j,
    List.length_take, Stream'.Seq.length_toList]
  omega

open Classical in
/-- **Generalized bind/compose integration identity.** The fully-general bijection core: a
test `F` on the *whole* halting execution (not just its end-state) integrated against the
halt-mass of `bind σ k` (from `μ_init`) equals the convolution over the split point, with `F`
evaluated at the concatenation `concat f₁ f₂` of each prefix/suffix pair. The split↔pair
reindexing is `(f₁, f₂) ↦ (concat f₁ f₂, |f₁|)`. This refines `bind_compose_integrate` (which is
the end-state-test special case) and supports trace-restricted tests via `WeakScheduler.concat`'s
trace decomposition. -/
theorem Scheduler.bind_compose_integrate_gen {sys : System State Label}
    (σ : Scheduler sys) (k : State → Scheduler sys)
    (μ_init : PMF State) (F : {e : AlterSeq State Label // e.trans.Terminates} → ENNReal) :
    (∑' e, (Scheduler.bind σ k).haltMass μ_init e * F e)
      = ∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
          σ.haltMass μ_init f₁ *
            ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
              (k (f₁.1.endState f₁.2)).haltMass (PMF.pure (f₁.1.endState f₁.2)) f₂
                * F ⟨WeakScheduler.concat f₁ f₂, WeakScheduler.concat_terminates f₁ f₂⟩ := by
  classical
  -- Off-diagonal vanishing: `k s'` from a Dirac at `s` ignores executions not starting at `s`.
  have hoff : ∀ (s : State) (f₂ : {e : AlterSeq State Label // e.trans.Terminates}),
      f₂.1.init ≠ s → (k s).haltMass (PMF.pure s) f₂ = 0 := by
    intro s f₂ hne
    unfold Scheduler.haltMass
    rw [ProbabilisticExecution.probOf_init_factor (k s) (PMF.pure s) f₂.1 f₂.2,
      PMF.pure_apply_of_ne _ _ hne, zero_mul, zero_mul]
  -- Recast the RHS as a single `tsum` over the pair type.
  rw [show (∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
        σ.haltMass μ_init f₁ *
          ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
            (k (f₁.1.endState f₁.2)).haltMass (PMF.pure (f₁.1.endState f₁.2)) f₂
              * F ⟨WeakScheduler.concat f₁ f₂, WeakScheduler.concat_terminates f₁ f₂⟩)
      = ∑' p : {e : AlterSeq State Label // e.trans.Terminates} ×
          {e : AlterSeq State Label // e.trans.Terminates},
          σ.haltMass μ_init p.1
            * (k (p.1.1.endState p.1.2)).haltMass (PMF.pure (p.1.1.endState p.1.2)) p.2
            * F ⟨WeakScheduler.concat p.1 p.2, WeakScheduler.concat_terminates p.1 p.2⟩ from by
    rw [ENNReal.tsum_prod']
    refine tsum_congr fun f₁ => ?_
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun f₂ => by ring]
  simp_rw [Scheduler.bind_haltMass σ k μ_init, Finset.sum_mul]
  -- Step 2a: turn each `Finset.range` sum into a capped `tsum`.
  rw [show (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
      ∑ i ∈ Finset.range (e.1.trans.length e.2 + 1),
        σ.haltMass μ_init ⟨⟨e.1.init, Seq.ofList (Seq.take i e.1.trans)⟩,
            Stream'.Seq.terminates_ofList _⟩ *
          (k (WeakScheduler.stateAfter e.1 i)).haltMass
            (PMF.pure (WeakScheduler.stateAfter e.1 i))
            ⟨⟨WeakScheduler.stateAfter e.1 i, e.1.trans.drop i⟩,
              WeakScheduler.drop_terminates e.2 i⟩ *
          F e)
    = ∑' e : {e : AlterSeq State Label // e.trans.Terminates}, ∑' i : ℕ,
        (if i ≤ e.1.trans.length e.2 then
          σ.haltMass μ_init ⟨⟨e.1.init, Seq.ofList (Seq.take i e.1.trans)⟩,
              Stream'.Seq.terminates_ofList _⟩ *
            (k (WeakScheduler.stateAfter e.1 i)).haltMass
              (PMF.pure (WeakScheduler.stateAfter e.1 i))
              ⟨⟨WeakScheduler.stateAfter e.1 i, e.1.trans.drop i⟩,
                WeakScheduler.drop_terminates e.2 i⟩ *
            F e
          else 0) from
    tsum_congr fun e => by
      rw [tsum_eq_sum (s := Finset.range (e.1.trans.length e.2 + 1)) (fun i hi => by
        rw [Finset.mem_range, Nat.lt_succ_iff] at hi; rw [if_neg hi])]
      exact (Finset.sum_congr rfl (fun i hi => by
        rw [Finset.mem_range, Nat.lt_succ_iff] at hi; rw [if_pos hi])).symm]
  -- Step 2b: combine into a single `tsum` over `{e//T} × ℕ`.
  rw [← ENNReal.tsum_prod (f := fun (e : {e : AlterSeq State Label // e.trans.Terminates})
      (i : ℕ) =>
      (if i ≤ e.1.trans.length e.2 then
        σ.haltMass μ_init ⟨⟨e.1.init, Seq.ofList (Seq.take i e.1.trans)⟩,
            Stream'.Seq.terminates_ofList _⟩ *
          (k (WeakScheduler.stateAfter e.1 i)).haltMass
            (PMF.pure (WeakScheduler.stateAfter e.1 i))
            ⟨⟨WeakScheduler.stateAfter e.1 i, e.1.trans.drop i⟩,
              WeakScheduler.drop_terminates e.2 i⟩ *
          F e
        else 0))]
  -- Step 2c: reindex by the bijection `(f₁, f₂) ↦ (concat f₁ f₂, |f₁|)`.
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun p => (⟨WeakScheduler.concat p.1.1 p.1.2, WeakScheduler.concat_terminates p.1.1 p.1.2⟩,
      p.1.1.1.trans.length p.1.1.2)) ?_ ?_ ?_
  · -- hinj : injective on the support of the pair-summand
    rintro ⟨⟨f₁, f₂⟩, hp⟩ ⟨⟨f₁', f₂'⟩, hp'⟩ hii
    simp only [Function.mem_support, ne_eq] at hp hp'
    have hc : f₂.1.init = f₁.1.endState f₁.2 := by
      by_contra hne
      exact hp (by rw [hoff (f₁.1.endState f₁.2) f₂ hne, mul_zero, zero_mul])
    have hc' : f₂'.1.init = f₁'.1.endState f₁'.2 := by
      by_contra hne
      exact hp' (by rw [hoff (f₁'.1.endState f₁'.2) f₂' hne, mul_zero, zero_mul])
    simp only [Prod.mk.injEq] at hii
    obtain ⟨hconcat, hleneq⟩ := hii
    have hcc : WeakScheduler.concat f₁ f₂ = WeakScheduler.concat f₁' f₂' :=
      Subtype.ext_iff.mp hconcat
    have hf₁ : f₁ = f₁' := by
      apply Subtype.ext
      have hinit : f₁.1.init = f₁'.1.init := by
        have : (WeakScheduler.concat f₁ f₂).init = (WeakScheduler.concat f₁' f₂').init := by
          rw [hcc]
        exact this
      have htrans : f₁.1.trans = f₁'.1.trans := by
        rw [← WeakScheduler.take_concat f₁ f₂, ← WeakScheduler.take_concat f₁' f₂',
          hleneq, hcc]
      exact AlterSeq.ext_of hinit htrans
    have hf₂ : f₂ = f₂' := by
      apply Subtype.ext
      have htrans : f₂.1.trans = f₂'.1.trans := by
        rw [← WeakScheduler.drop_concat f₁ f₂, ← WeakScheduler.drop_concat f₁' f₂',
          hleneq, hcc]
      have hinit : f₂.1.init = f₂'.1.init := by
        rw [hc, hc', ← hf₁]
      exact AlterSeq.ext_of hinit htrans
    simp only [hf₁, hf₂]
  · -- hf : support ⊆ range i
    rintro ⟨e, j⟩ hq
    simp only [Function.mem_support, ne_eq] at hq
    have hjle : j ≤ e.1.trans.length e.2 := by
      by_contra hlt
      exact hq (if_neg hlt)
    rw [if_pos hjle] at hq
    set pre : {e : AlterSeq State Label // e.trans.Terminates} :=
      ⟨⟨e.1.init, Seq.ofList (Seq.take j e.1.trans)⟩, Stream'.Seq.terminates_ofList _⟩ with hpredef
    set suf : {e : AlterSeq State Label // e.trans.Terminates} :=
      ⟨⟨WeakScheduler.stateAfter e.1 j, e.1.trans.drop j⟩,
        WeakScheduler.drop_terminates e.2 j⟩ with hsufdef
    have hcs : WeakScheduler.concat pre suf = e.1 := WeakScheduler.concat_split e j
    have hlen : pre.1.trans.length pre.2 = j := WeakScheduler.length_pre e j hjle
    have hpreend : pre.1.endState pre.2 = WeakScheduler.stateAfter e.1 j := by
      rw [← WeakScheduler.stateAfter_concat pre suf, hlen,
        WeakScheduler.stateAfter_congr hcs j]
    have hconcat_eq : (⟨WeakScheduler.concat pre suf, WeakScheduler.concat_terminates pre suf⟩
        : {e : AlterSeq State Label // e.trans.Terminates}) = e := Subtype.ext hcs
    refine ⟨⟨(pre, suf), ?_⟩, ?_⟩
    · simp only [Function.mem_support, ne_eq]
      rw [hpreend, hconcat_eq]
      exact hq
    · apply Prod.ext
      · exact Subtype.ext hcs
      · exact hlen
  · -- hfg : f (i x) = g x
    rintro ⟨⟨f₁, f₂⟩, hx⟩
    simp only [Function.mem_support, ne_eq] at hx
    have hcomp : f₂.1.init = f₁.1.endState f₁.2 := by
      by_contra hne
      exact hx (by
        rw [hoff (f₁.1.endState f₁.2) f₂ hne, mul_zero, zero_mul])
    have hcap : f₁.1.trans.length f₁.2
        ≤ (WeakScheduler.concat f₁ f₂).trans.length (WeakScheduler.concat_terminates f₁ f₂) := by
      rw [WeakScheduler.length_concat]; exact Nat.le_add_right _ _
    simp only
    rw [if_pos hcap, WeakScheduler.stateAfter_concat]
    have hpre : (⟨(WeakScheduler.concat f₁ f₂).init,
          Seq.ofList (Seq.take (f₁.1.trans.length f₁.2)
            (WeakScheduler.concat f₁ f₂).trans)⟩ : AlterSeq State Label) = f₁.1 := by
      rw [WeakScheduler.take_concat]
      rfl
    have hsuf : (⟨f₁.1.endState f₁.2,
          (WeakScheduler.concat f₁ f₂).trans.drop (f₁.1.trans.length f₁.2)⟩
          : AlterSeq State Label) = f₂.1 := by
      rw [WeakScheduler.drop_concat, ← hcomp]
    rw [Scheduler.haltMass_congr_eq σ μ_init hpre,
      Scheduler.haltMass_congr_eq (k (f₁.1.endState f₁.2))
        (PMF.pure (f₁.1.endState f₁.2)) hsuf]

open Classical in
/-- **Bind/compose integration identity** (the split↔pair reindexing core of the
chain rule): integrating a test `g` against the halting end-state of `bind σ k`
(from `μ_init`) equals the convolution over the split point — sum over `σ`'s
halting prefixes `f₁`, weighted by `k`'s halting suffix `f₂` from `f₁`'s
end-state. This is `bind_haltMass` followed by the bijection
`(f₁, f₂) ↦ (concat f₁ f₂, |f₁|)`; it is fully general in `σ`, the continuation
`k`, the source `μ_init`, and the test `g`. -/
theorem Scheduler.bind_compose_integrate {sys : System State Label}
    (σ : Scheduler sys) (k : State → Scheduler sys)
    (μ_init : PMF State) (g : State → ENNReal) :
    (∑' e, (Scheduler.bind σ k).haltMass μ_init e * g (e.1.endState e.2))
      = ∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
          σ.haltMass μ_init f₁ *
            ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
              (k (f₁.1.endState f₁.2)).haltMass (PMF.pure (f₁.1.endState f₁.2)) f₂
                * g (f₂.1.endState f₂.2) := by
  classical
  -- Off-diagonal vanishing: `k s'` from a Dirac at `s` ignores executions not
  -- starting at `s`.
  have hoff : ∀ (s : State) (f₂ : {e : AlterSeq State Label // e.trans.Terminates}),
      f₂.1.init ≠ s → (k s).haltMass (PMF.pure s) f₂ = 0 := by
    intro s f₂ hne
    unfold Scheduler.haltMass
    rw [ProbabilisticExecution.probOf_init_factor (k s) (PMF.pure s) f₂.1 f₂.2,
      PMF.pure_apply_of_ne _ _ hne, zero_mul, zero_mul]
  -- Recast the RHS as a single `tsum` over the pair type (to match the bijection
  -- target), pushing `σ.haltMass μ_init f₁` into the inner sum.
  rw [show (∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
        σ.haltMass μ_init f₁ *
          ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
            (k (f₁.1.endState f₁.2)).haltMass (PMF.pure (f₁.1.endState f₁.2)) f₂
              * g (f₂.1.endState f₂.2))
      = ∑' p : {e : AlterSeq State Label // e.trans.Terminates} ×
          {e : AlterSeq State Label // e.trans.Terminates},
          σ.haltMass μ_init p.1
            * (k (p.1.1.endState p.1.2)).haltMass (PMF.pure (p.1.1.endState p.1.2)) p.2
            * g (p.2.1.endState p.2.2) from by
    rw [ENNReal.tsum_prod']
    refine tsum_congr fun f₁ => ?_
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun f₂ => by ring]
  -- **Steps 1+2.** Align `g`, convert each `Finset.range` sum to a capped `tsum`,
  -- combine into a single `tsum` over `{e//T} × ℕ`, then reindex by the bijection
  -- `(f₁, f₂) ↦ (concat f₁ f₂, |f₁|)`.
  simp_rw [Scheduler.bind_haltMass σ k μ_init, Finset.sum_mul]
  -- Step 1: replace `g (e.endState)` by `g ((suf e i).endState)` within each summand.
  rw [show (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
      ∑ i ∈ Finset.range (e.1.trans.length e.2 + 1),
        σ.haltMass μ_init ⟨⟨e.1.init, Seq.ofList (Seq.take i e.1.trans)⟩,
            Stream'.Seq.terminates_ofList _⟩ *
          (k (WeakScheduler.stateAfter e.1 i)).haltMass
            (PMF.pure (WeakScheduler.stateAfter e.1 i))
            ⟨⟨WeakScheduler.stateAfter e.1 i, e.1.trans.drop i⟩,
              WeakScheduler.drop_terminates e.2 i⟩ *
          g (e.1.endState e.2))
    = ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        ∑ i ∈ Finset.range (e.1.trans.length e.2 + 1),
          σ.haltMass μ_init ⟨⟨e.1.init, Seq.ofList (Seq.take i e.1.trans)⟩,
              Stream'.Seq.terminates_ofList _⟩ *
            (k (WeakScheduler.stateAfter e.1 i)).haltMass
              (PMF.pure (WeakScheduler.stateAfter e.1 i))
              ⟨⟨WeakScheduler.stateAfter e.1 i, e.1.trans.drop i⟩,
                WeakScheduler.drop_terminates e.2 i⟩ *
            g ((⟨⟨WeakScheduler.stateAfter e.1 i, e.1.trans.drop i⟩,
                WeakScheduler.drop_terminates e.2 i⟩ :
                {e : AlterSeq State Label // e.trans.Terminates}).1.endState
                (WeakScheduler.drop_terminates e.2 i)) from
    tsum_congr fun e => Finset.sum_congr rfl fun i hi => by
      rw [Finset.mem_range, Nat.lt_succ_iff] at hi
      rw [WeakScheduler.endState_suf e.1 e.2 i hi]]
  -- Step 2a: turn each `Finset.range` sum into a capped `tsum`.
  rw [show (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
      ∑ i ∈ Finset.range (e.1.trans.length e.2 + 1),
        σ.haltMass μ_init ⟨⟨e.1.init, Seq.ofList (Seq.take i e.1.trans)⟩,
            Stream'.Seq.terminates_ofList _⟩ *
          (k (WeakScheduler.stateAfter e.1 i)).haltMass
            (PMF.pure (WeakScheduler.stateAfter e.1 i))
            ⟨⟨WeakScheduler.stateAfter e.1 i, e.1.trans.drop i⟩,
              WeakScheduler.drop_terminates e.2 i⟩ *
          g ((⟨⟨WeakScheduler.stateAfter e.1 i, e.1.trans.drop i⟩,
              WeakScheduler.drop_terminates e.2 i⟩ :
              {e : AlterSeq State Label // e.trans.Terminates}).1.endState
              (WeakScheduler.drop_terminates e.2 i)))
    = ∑' e : {e : AlterSeq State Label // e.trans.Terminates}, ∑' i : ℕ,
        (if i ≤ e.1.trans.length e.2 then
          σ.haltMass μ_init ⟨⟨e.1.init, Seq.ofList (Seq.take i e.1.trans)⟩,
              Stream'.Seq.terminates_ofList _⟩ *
            (k (WeakScheduler.stateAfter e.1 i)).haltMass
              (PMF.pure (WeakScheduler.stateAfter e.1 i))
              ⟨⟨WeakScheduler.stateAfter e.1 i, e.1.trans.drop i⟩,
                WeakScheduler.drop_terminates e.2 i⟩ *
            g ((⟨⟨WeakScheduler.stateAfter e.1 i, e.1.trans.drop i⟩,
                WeakScheduler.drop_terminates e.2 i⟩ :
                {e : AlterSeq State Label // e.trans.Terminates}).1.endState
                (WeakScheduler.drop_terminates e.2 i))
          else 0) from
    tsum_congr fun e => by
      rw [tsum_eq_sum (s := Finset.range (e.1.trans.length e.2 + 1)) (fun i hi => by
        rw [Finset.mem_range, Nat.lt_succ_iff] at hi; rw [if_neg hi])]
      exact (Finset.sum_congr rfl (fun i hi => by
        rw [Finset.mem_range, Nat.lt_succ_iff] at hi; rw [if_pos hi])).symm]
  -- Step 2b: combine into a single `tsum` over `{e//T} × ℕ`.
  rw [← ENNReal.tsum_prod (f := fun (e : {e : AlterSeq State Label // e.trans.Terminates})
      (i : ℕ) =>
      (if i ≤ e.1.trans.length e.2 then
        σ.haltMass μ_init ⟨⟨e.1.init, Seq.ofList (Seq.take i e.1.trans)⟩,
            Stream'.Seq.terminates_ofList _⟩ *
          (k (WeakScheduler.stateAfter e.1 i)).haltMass
            (PMF.pure (WeakScheduler.stateAfter e.1 i))
            ⟨⟨WeakScheduler.stateAfter e.1 i, e.1.trans.drop i⟩,
              WeakScheduler.drop_terminates e.2 i⟩ *
          g ((⟨⟨WeakScheduler.stateAfter e.1 i, e.1.trans.drop i⟩,
              WeakScheduler.drop_terminates e.2 i⟩ :
              {e : AlterSeq State Label // e.trans.Terminates}).1.endState
              (WeakScheduler.drop_terminates e.2 i))
        else 0))]
  -- Step 2c: reindex by the bijection `(f₁, f₂) ↦ (concat f₁ f₂, |f₁|)`.
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun p => (⟨WeakScheduler.concat p.1.1 p.1.2, WeakScheduler.concat_terminates p.1.1 p.1.2⟩,
      p.1.1.1.trans.length p.1.1.2)) ?_ ?_ ?_
  · -- hinj : injective on the support of the pair-summand
    rintro ⟨⟨f₁, f₂⟩, hp⟩ ⟨⟨f₁', f₂'⟩, hp'⟩ hii
    simp only [Function.mem_support, ne_eq] at hp hp'
    -- composability on both sides
    have hc : f₂.1.init = f₁.1.endState f₁.2 := by
      by_contra hne
      exact hp (by rw [hoff (f₁.1.endState f₁.2) f₂ hne, mul_zero, zero_mul])
    have hc' : f₂'.1.init = f₁'.1.endState f₁'.2 := by
      by_contra hne
      exact hp' (by rw [hoff (f₁'.1.endState f₁'.2) f₂' hne, mul_zero, zero_mul])
    -- unpack the `i`-equality into equal concats and equal `f₁`-lengths
    simp only [Prod.mk.injEq] at hii
    obtain ⟨hconcat, hleneq⟩ := hii
    have hcc : WeakScheduler.concat f₁ f₂ = WeakScheduler.concat f₁' f₂' :=
      Subtype.ext_iff.mp hconcat
    -- recover `f₁ = f₁'`
    have hf₁ : f₁ = f₁' := by
      apply Subtype.ext
      have hinit : f₁.1.init = f₁'.1.init := by
        have : (WeakScheduler.concat f₁ f₂).init = (WeakScheduler.concat f₁' f₂').init := by
          rw [hcc]
        exact this
      have htrans : f₁.1.trans = f₁'.1.trans := by
        rw [← WeakScheduler.take_concat f₁ f₂, ← WeakScheduler.take_concat f₁' f₂',
          hleneq, hcc]
      exact AlterSeq.ext_of hinit htrans
    -- recover `f₂ = f₂'`
    have hf₂ : f₂ = f₂' := by
      apply Subtype.ext
      have htrans : f₂.1.trans = f₂'.1.trans := by
        rw [← WeakScheduler.drop_concat f₁ f₂, ← WeakScheduler.drop_concat f₁' f₂',
          hleneq, hcc]
      have hinit : f₂.1.init = f₂'.1.init := by
        rw [hc, hc', ← hf₁]
      exact AlterSeq.ext_of hinit htrans
    simp only [hf₁, hf₂]
  · -- hf : support ⊆ range i
    rintro ⟨e, j⟩ hq
    simp only [Function.mem_support, ne_eq] at hq
    -- the cap must hold (else the summand is `0`)
    have hjle : j ≤ e.1.trans.length e.2 := by
      by_contra hlt
      exact hq (if_neg hlt)
    rw [if_pos hjle] at hq
    -- the preimage pair: the `j`-prefix and `j`-suffix of `e`
    set pre : {e : AlterSeq State Label // e.trans.Terminates} :=
      ⟨⟨e.1.init, Seq.ofList (Seq.take j e.1.trans)⟩, Stream'.Seq.terminates_ofList _⟩ with hpredef
    set suf : {e : AlterSeq State Label // e.trans.Terminates} :=
      ⟨⟨WeakScheduler.stateAfter e.1 j, e.1.trans.drop j⟩,
        WeakScheduler.drop_terminates e.2 j⟩ with hsufdef
    -- `concat pre suf = e` and `|pre| = j`, so `i (pre, suf) = (e, j)`.
    have hcs : WeakScheduler.concat pre suf = e.1 := WeakScheduler.concat_split e j
    have hlen : pre.1.trans.length pre.2 = j := WeakScheduler.length_pre e j hjle
    -- `pre.endState = stateAfter e j` (via `stateAfter_concat` along `hcs`, `hlen`)
    have hpreend : pre.1.endState pre.2 = WeakScheduler.stateAfter e.1 j := by
      rw [← WeakScheduler.stateAfter_concat pre suf, hlen,
        WeakScheduler.stateAfter_congr hcs j]
    refine ⟨⟨(pre, suf), ?_⟩, ?_⟩
    · -- membership in `support pairSummand`
      simp only [Function.mem_support, ne_eq]
      rw [hpreend]
      exact hq
    · -- `i (pre, suf) = (e, j)`
      apply Prod.ext
      · exact Subtype.ext hcs
      · exact hlen
  · -- hfg : f (i x) = g x
    rintro ⟨⟨f₁, f₂⟩, hx⟩
    simp only [Function.mem_support, ne_eq] at hx
    -- composability: `f₂.init = f₁.endState` (else off-diagonal vanishes)
    have hcomp : f₂.1.init = f₁.1.endState f₁.2 := by
      by_contra hne
      exact hx (by
        rw [hoff (f₁.1.endState f₁.2) f₂ hne, mul_zero, zero_mul])
    -- the cap condition holds
    have hcap : f₁.1.trans.length f₁.2
        ≤ (WeakScheduler.concat f₁ f₂).trans.length (WeakScheduler.concat_terminates f₁ f₂) := by
      rw [WeakScheduler.length_concat]; exact Nat.le_add_right _ _
    simp only
    rw [if_pos hcap, WeakScheduler.stateAfter_concat]
    -- `pre (concat) |f₁|` has underlying `AlterSeq` equal to `f₁`
    have hpre : (⟨(WeakScheduler.concat f₁ f₂).init,
          Seq.ofList (Seq.take (f₁.1.trans.length f₁.2)
            (WeakScheduler.concat f₁ f₂).trans)⟩ : AlterSeq State Label) = f₁.1 := by
      rw [WeakScheduler.take_concat]
      rfl
    -- the post-rewrite suffix has underlying `AlterSeq` equal to `f₂`
    have hsuf : (⟨f₁.1.endState f₁.2,
          (WeakScheduler.concat f₁ f₂).trans.drop (f₁.1.trans.length f₁.2)⟩
          : AlterSeq State Label) = f₂.1 := by
      rw [WeakScheduler.drop_concat, ← hcomp]
    rw [Scheduler.haltMass_congr_eq σ μ_init hpre,
      Scheduler.haltMass_congr_eq (k (f₁.1.endState f₁.2))
        (PMF.pure (f₁.1.endState f₁.2)) hsuf]
    congr 1
    -- the `g`-argument: end-state of the suffix equals `f₂`'s end-state
    rw [AlterSeq.endState_congr hsuf _ f₂.2]

/-- **Master identity** for `weakTau` transitivity: integrating any `g` against
the halting end-state of `bind σ₁ σ₂` (run from `a`) equals integrating `g`
against `c`. Both conjuncts of `weakTau sys a c` are special cases. -/
private theorem master_identity {sys : System State Label} {a b c : PMF State}
    (h₁ : weakTau sys a b) (h₂ : weakTau sys b c) (g : State → ENNReal) :
    (∑' e, (WeakScheduler.bind h₁.witnessScheduler (fun _ => h₂.witnessScheduler)).haltMass a e
        * g (e.1.endState e.2))
      = ∑' s', c s' * g s' := by
  classical
  set σ₁ := h₁.witnessScheduler with hσ₁
  set σ₂ := h₂.witnessScheduler with hσ₂
  -- Off-diagonal vanishing: `σ₂` from a Dirac at `s` ignores executions not starting at `s`.
  have hoff : ∀ (s : State) (f₂ : {e : AlterSeq State Label // e.trans.Terminates}),
      f₂.1.init ≠ s → σ₂.haltMass (PMF.pure s) f₂ = 0 := by
    intro s f₂ hne
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [ProbabilisticExecution.probOf_init_factor σ₂.toScheduler (PMF.pure s) f₂.1 f₂.2,
      PMF.pure_apply_of_ne _ _ hne, zero_mul, zero_mul]
  -- **Step 3 (analytic collapse).** The pair-sum collapses to `∑' s', c s' * g s'`.
  have step3 :
      (∑' p : {e : AlterSeq State Label // e.trans.Terminates} ×
          {e : AlterSeq State Label // e.trans.Terminates},
          σ₁.haltMass a p.1 * σ₂.haltMass (PMF.pure (p.1.1.endState p.1.2)) p.2
            * g (p.2.1.endState p.2.2))
        = ∑' s', c s' * g s' := by
    rw [ENNReal.tsum_prod']
    -- inner sum over `f₂` factors out `σ₁.haltMass a f₁`
    have hinner : ∀ f₁ : {e : AlterSeq State Label // e.trans.Terminates},
        (∑' f₂, σ₁.haltMass a f₁ * σ₂.haltMass (PMF.pure (f₁.1.endState f₁.2)) f₂
            * g (f₂.1.endState f₂.2))
          = σ₁.haltMass a f₁
              * (∑' f₂, σ₂.haltMass (PMF.pure (f₁.1.endState f₁.2)) f₂
                  * g (f₂.1.endState f₂.2)) := by
      intro f₁
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr (fun f₂ => by ring)
    rw [tsum_congr hinner]
    -- `weakTau.integrate h₁` with test `G s := ∑' f₂, σ₂.haltMass (pure s) f₂ * g (f₂.end)`
    have hint1 := h₁.integrate
      (fun s => ∑' f₂, σ₂.haltMass (PMF.pure s) f₂ * g (f₂.1.endState f₂.2))
    rw [← hσ₁] at hint1
    rw [hint1]
    -- now `∑' s, b s * G s`; commute and use `haltMass_init_mix` + `integrate h₂`
    have hstep : ∀ s, b s * (∑' f₂, σ₂.haltMass (PMF.pure s) f₂ * g (f₂.1.endState f₂.2))
        = ∑' f₂, b s * σ₂.haltMass (PMF.pure s) f₂ * g (f₂.1.endState f₂.2) := by
      intro s
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr (fun f₂ => by ring)
    rw [tsum_congr hstep, ENNReal.tsum_comm]
    -- fold the source-mixture over `b` back into `σ₂.haltMass b`
    have hmix : ∀ f₂ : {e : AlterSeq State Label // e.trans.Terminates},
        (∑' s, b s * σ₂.haltMass (PMF.pure s) f₂ * g (f₂.1.endState f₂.2))
          = σ₂.haltMass b f₂ * g (f₂.1.endState f₂.2) := by
      intro f₂
      rw [ENNReal.tsum_mul_right, ← WeakScheduler.haltMass_init_mix σ₂ b f₂]
    rw [tsum_congr hmix]
    -- `weakTau.integrate h₂` with test `g`
    have hint2 := h₂.integrate g
    rw [← hσ₂] at hint2
    exact hint2
  rw [← step3]
  -- **Steps 1+2 (extracted).** The split↔pair reindexing is exactly
  -- `Scheduler.bind_compose_integrate` for `σ₁`, the constant continuation
  -- `fun _ => σ₂`, source `a`, and test `g` (using the Phase-B defeq
  -- `WeakScheduler.bind`/`haltMass` ↦ `Scheduler.bind`/`haltMass`); the remaining
  -- step is `tsum_prod'` plus pulling `σ₁.haltMass a f₁` out of the inner sum.
  rw [show (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        (σ₁.bind fun _ => σ₂).haltMass a e * g (e.1.endState e.2))
      = ∑' e, (Scheduler.bind σ₁.toScheduler (fun _ => σ₂.toScheduler)).haltMass a e
          * g (e.1.endState e.2) from rfl,
    Scheduler.bind_compose_integrate σ₁.toScheduler (fun _ => σ₂.toScheduler) a g,
    ENNReal.tsum_prod']
  refine tsum_congr fun f₁ => ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun f₂ => by ac_rfl

/-- Transitivity of `weakTau` (via `WeakScheduler.bind` and `bind_haltMass`). -/
theorem weakTau_trans {sys : System State Label} {a b c : PMF State}
    (h₁ : weakTau sys a b) (h₂ : weakTau sys b c) : weakTau sys a c := by
  classical
  set σ₁ := h₁.witnessScheduler with hσ₁
  set σ₂ := h₂.witnessScheduler with hσ₂
  refine ⟨WeakScheduler.bind σ₁ (fun _ => σ₂), ?_, ?_⟩
  · -- conjunct 1: total halting mass is 1
    have hm := master_identity h₁ h₂ (fun _ => 1)
    simp only [mul_one] at hm
    rw [hm, c.tsum_coe]
  · -- conjunct 2: pushforward to `c`
    intro s
    have hm := master_identity h₁ h₂ (fun s' => if s' = s then 1 else 0)
    rw [hm, tsum_eq_single s (fun s' hs' => by rw [if_neg hs', mul_zero]), if_pos rfl, mul_one]

end PLTS
