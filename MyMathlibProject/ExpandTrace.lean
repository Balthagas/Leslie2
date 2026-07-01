/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import MyMathlibProject.Expand

/-!
# Trace invariant for the unfolding algorithm

The configuration `c` of the unfolding algorithm carries an abstract `sys^w`-execution
`c.we` and a concrete `sys`-execution `c.e`. We prove that for every **reachable**
configuration (positive `reachProb`) the two committed executions have the same trace,
`c.we.trace = c.e.trace`.

The key point is that `we` and the *committed* `e` are always updated in the same
(outer) instruction, so they never drift — the in-progress segment `e'` is the only
thing that lags, and it is deliberately excluded from the comparison. The invariant
`Inv` additionally records that `e'` is a positive-probability run of the witness `s`
of the current weak step, so that at each commit the segment's trace equals the weak
step's external trace (via `Realises`), preserving `we.trace = e.trace`.
-/

open Stream'

namespace PLTS

variable {State Label : Type} [Silent Label] {sys : System State Label}

/-! ### Trace helpers (append/singleton splitting and weak-scheduler nil traces) -/

open Classical in
/-- The trace of a singleton-transition execution: `[l]` for an external label,
`[]` for an internal one. -/
private theorem trace_singleton (i : State) (l : Label) (s' : State) :
    sys.trace (⟨i, Seq.cons (l, s') Seq.nil⟩ : AlterSeq State Label)
      = if l = Silent.τ then Seq.nil else Seq.cons l Seq.nil := by
  by_cases hl : l = Silent.τ
  · rw [if_pos hl]
    unfold System.trace
    rw [Stream'.Seq.filter_cons_neg (l, s') Seq.nil (not_not.mpr hl),
      Stream'.Seq.filter_nil, Stream'.Seq.map_nil]
  · rw [if_neg hl, System.trace_cons_external sys i l s' Seq.nil hl, System.trace_init]

/-- The trace of an append splits (the trace depends only on `trans`, and `filter`
distributes over `append` for a terminating prefix). -/
theorem trace_append (i : State) (s t : Seq (Label × State)) (h_s : s.Terminates) :
    sys.trace (⟨i, s.append t⟩ : AlterSeq State Label)
      = (sys.trace (⟨i, s⟩ : AlterSeq State Label)).append
          (sys.trace (⟨i, t⟩ : AlterSeq State Label)) := by
  simp only [System.trace]
  rw [Stream'.Seq.filter_append _ s t h_s, Stream'.Seq.map_append]

/-- A finite execution produced (with positive probability) by a weak scheduler has
empty trace: every committed transition has an internal label. -/
private theorem trace_nil_of_probOf_list (σ : WeakScheduler sys) (μ_init : PMF State) (i : State) :
    ∀ L : List (Label × State),
      (⟨μ_init, σ.toScheduler⟩ : ProbabilisticExecution sys).probOf
         ⟨i, Seq.ofList L⟩ (Stream'.Seq.terminates_ofList L) ≠ 0 →
      sys.trace (⟨i, Seq.ofList L⟩ : AlterSeq State Label) = Seq.nil := by
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    intro _
    rw [Stream'.Seq.ofList_nil]
    exact System.trace_init sys i
  | append_singleton rest last ih =>
    intro hpos
    obtain ⟨l, s'⟩ := last
    have hofl : (Seq.ofList (rest ++ [(l, s')]) : Seq (Label × State))
        = (Seq.ofList rest).append (Seq.cons (l, s') Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have hterm_app : ((Seq.ofList rest).append (Seq.cons (l, s') Seq.nil)).Terminates := by
      rw [← hofl]; exact Stream'.Seq.terminates_ofList _
    have hfact : (⟨μ_init, σ.toScheduler⟩ : ProbabilisticExecution sys).probOf
          ⟨i, Seq.ofList (rest ++ [(l, s')])⟩ (Stream'.Seq.terminates_ofList _)
        = (⟨μ_init, σ.toScheduler⟩ : ProbabilisticExecution sys).probOf
            ⟨i, Seq.ofList rest⟩ (Stream'.Seq.terminates_ofList _)
          * (⟨μ_init, σ.toScheduler⟩ : ProbabilisticExecution sys).kernel
              ⟨i, Seq.ofList rest⟩ (l, s') := by
      rw [ProbabilisticExecution.probOf_congr _
          ⟨i, Seq.ofList (rest ++ [(l, s')])⟩
          ⟨i, (Seq.ofList rest).append (Seq.cons (l, s') Seq.nil)⟩ (by rw [hofl])
          (Stream'.Seq.terminates_ofList _) hterm_app]
      exact ProbabilisticExecution.probOf_append_singleton _ i (Seq.ofList rest)
        (Stream'.Seq.terminates_ofList _) (l, s') hterm_app
    rw [hfact, mul_ne_zero_iff] at hpos
    obtain ⟨hrest, hker⟩ := hpos
    have hτ : l = Silent.τ := by
      unfold ProbabilisticExecution.kernel at hker
      have hex : ∃ μ, σ.toScheduler.next ⟨i, Seq.ofList rest⟩ (some (l, μ)) * μ s' ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hker (ENNReal.tsum_eq_zero.mpr hcon)
      obtain ⟨μ, hμ⟩ := hex
      rw [mul_ne_zero_iff] at hμ
      exact σ.internal_only ⟨i, Seq.ofList rest⟩ l μ ((PMF.mem_support_iff _ _).mpr hμ.1)
    rw [hofl, trace_append i (Seq.ofList rest) _ (Stream'.Seq.terminates_ofList _), ih hrest,
      trace_singleton i l s', if_pos hτ, Stream'.Seq.nil_append]

/-- A positive-halt-mass run of a weak scheduler has empty trace. -/
private theorem weakSched_trace_nil (σ : WeakScheduler sys) (μ_init : PMF State)
    (e : {e : AlterSeq State Label // e.trans.Terminates})
    (hpos : σ.haltMass μ_init e ≠ 0) :
    sys.trace e.1 = Seq.nil := by
  obtain ⟨e, hT⟩ := e
  unfold WeakScheduler.haltMass Scheduler.haltMass at hpos
  rw [mul_ne_zero_iff] at hpos
  set L := e.trans.toList hT with hL
  have he_eq : (⟨e.init, Seq.ofList L⟩ : AlterSeq State Label) = e := by
    rw [hL, Stream'.Seq.ofList_toList e.trans hT]
  have hpos' : (⟨μ_init, σ.toScheduler⟩ : ProbabilisticExecution sys).probOf
      ⟨e.init, Seq.ofList L⟩ (Stream'.Seq.terminates_ofList L) ≠ 0 := by
    rw [ProbabilisticExecution.probOf_congr _ _ e he_eq (Stream'.Seq.terminates_ofList L) hT]
    exact hpos.1
  have htr := trace_nil_of_probOf_list σ μ_init e.init L hpos'
  rwa [he_eq] at htr

/-! ### Helpers for the external (non-τ) witness construction -/

omit [Silent Label] in
/-- Fiber-reindexing for halt-mass sums (local copy of `weakTau_reindex_fiber`,
which is `private` to `WeakStep`). -/
private theorem reindex_fiber
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

/-- The trace of a concatenation of two terminating executions splits as the
append of the two traces. -/
private theorem trace_concat (f₁ f₂ : {e : AlterSeq State Label // e.trans.Terminates}) :
    sys.trace (WeakScheduler.concat f₁ f₂)
      = (sys.trace f₁.1).append (sys.trace f₂.1) := by
  obtain ⟨e₁, hT₁⟩ := f₁
  obtain ⟨e₂, hT₂⟩ := f₂
  change sys.trace (⟨e₁.init, Seq.ofList (e₁.trans.toList hT₁ ++ e₂.trans.toList hT₂)⟩
      : AlterSeq State Label) = (sys.trace e₁).append (sys.trace e₂)
  rw [Stream'.Seq.ofList_append,
    show Seq.ofList (e₁.trans.toList hT₁) = e₁.trans from Stream'.Seq.ofList_toList e₁.trans hT₁,
    trace_append e₁.init e₁.trans (Seq.ofList (e₂.trans.toList hT₂)) hT₁,
    show Seq.ofList (e₂.trans.toList hT₂) = e₂.trans from Stream'.Seq.ofList_toList e₂.trans hT₂]
  congr 1

/-- A nonzero-halt-mass run of a `weakTau` witness ends in the target's support. -/
private theorem weakTau_endState_mem {a b : PMF State} (h : weakTau sys a b)
    (f : {e : AlterSeq State Label // e.trans.Terminates})
    (hpos : h.witnessScheduler.haltMass a f ≠ 0) :
    f.1.endState f.2 ∈ b.support := by
  classical
  rw [PMF.mem_support_iff]
  intro hb
  rw [h.witness_pushforward (f.1.endState f.2)] at hb
  have hle : h.witnessScheduler.haltMass a f *
        (if f.1.endState f.2 = f.1.endState f.2 then (1 : ENNReal) else 0)
      ≤ ∑' e, h.witnessScheduler.haltMass a e *
          (if e.1.endState e.2 = f.1.endState f.2 then (1 : ENNReal) else 0) :=
    ENNReal.le_tsum f
  rw [if_pos rfl, mul_one, hb, le_zero_iff] at hle
  exact hpos hle

/-- **Init-mix-lifted `integrate`** for `weakTau`: integrating `ψ` against the
halting end-state, summed over Dirac sources weighted by `a`, equals integrating
`ψ` against the target `b`. -/
private theorem weakTau_pure_integrate {a b : PMF State} (h : weakTau sys a b)
    (ψ : State → ENNReal) :
    (∑' s, a s * ∑' e, h.witnessScheduler.haltMass (PMF.pure s) e * ψ (e.1.endState e.2))
      = ∑' s, b s * ψ s := by
  classical
  rw [← h.integrate ψ]
  symm
  calc (∑' e, h.witnessScheduler.haltMass a e * ψ (e.1.endState e.2))
      = ∑' e, ∑' s, a s * h.witnessScheduler.haltMass (PMF.pure s) e * ψ (e.1.endState e.2) := by
        refine tsum_congr (fun e => ?_)
        rw [h.witnessScheduler.haltMass_init_mix a e, ENNReal.tsum_mul_right]
    _ = ∑' s, ∑' e, a s * h.witnessScheduler.haltMass (PMF.pure s) e * ψ (e.1.endState e.2) :=
        ENNReal.tsum_comm
    _ = ∑' s, a s * ∑' e, h.witnessScheduler.haltMass (PMF.pure s) e * ψ (e.1.endState e.2) := by
        refine tsum_congr (fun s => ?_)
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr (fun e => by ring)

open Classical in
/-- The **single external `l`-step scheduler** of a `hyperStep sys μ₁ l μ₂`: at an
empty history whose state lies in `μ₁.support` it emits one `l`-step distributed
as the hyper-step kernel (`(kernel s).map (some (l, ·))` — a convex mixture of
valid successors); everywhere else it halts. Run from `pure s` (for
`s ∈ μ₁.support`) it takes exactly one external `l`-transition into
`(kernel s).bind id` and stops. -/
private noncomputable def hyperStepSched {μ₁ μ₂ : PMF State} {l : Label}
    (hhs : hyperStep sys μ₁ l μ₂) : Scheduler sys where
  next e := if e.trans = Seq.nil ∧ e.init ∈ μ₁.support
            then (hhs.kernel e.init).map (fun μ' => some (l, μ')) else PMF.pure none
  valid := by
    intro e n s h_term h_state l' μ' h_supp
    by_cases hcond : e.trans = Seq.nil ∧ e.init ∈ μ₁.support
    · simp only [if_pos hcond, PMF.mem_support_map_iff] at h_supp
      obtain ⟨ν, hν_mem, hν_eq⟩ := h_supp
      rw [Option.some.injEq, Prod.mk.injEq] at hν_eq
      obtain ⟨hl', hμ'⟩ := hν_eq
      have hs_eq : s = e.init := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          have h0 : e.stateAt 0 = some e.init := rfl
          rw [h0] at h_state; exact (Option.some.inj h_state).symm
        · exfalso
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
          rw [hk] at h_state
          change (e.trans.get? k).map Prod.snd = some s at h_state
          rw [hcond.1] at h_state; simp at h_state
      rw [hs_eq, ← hl', ← hμ']
      exact hhs.kernel_step e.init hcond.2 ν hν_mem
    · simp only [if_neg hcond, PMF.mem_support_pure_iff] at h_supp
      exact absurd h_supp (by simp)

variable {μ₁ μ₂ : PMF State}

open Classical in
/-- The defining `next` of `hyperStepSched` (definitional unfolding). -/
private theorem hyperStepSched_next_eq {l : Label} (hhs : hyperStep sys μ₁ l μ₂)
    (e : AlterSeq State Label) :
    (hyperStepSched hhs).next e
      = if e.trans = Seq.nil ∧ e.init ∈ μ₁.support
        then (hhs.kernel e.init).map (fun μ' => some (l, μ')) else PMF.pure none := rfl

/-- `hyperStepSched` halts (`next ⊥ = 1`) off the active empty-history prefix. -/
private theorem hyperStepSched_next_none {l : Label} (hhs : hyperStep sys μ₁ l μ₂)
    (e : AlterSeq State Label) (hc : ¬(e.trans = Seq.nil ∧ e.init ∈ μ₁.support)) :
    (hyperStepSched hhs).next e none = 1 := by
  rw [hyperStepSched_next_eq, if_neg hc, PMF.pure_apply_self]

/-- The one-step kernel of `hyperStepSched` at the empty history `⟨s₁, nil⟩`
(with `s₁ ∈ μ₁.support`) sends `(l, s'')` to `((kernel s₁).bind id) s''`. -/
private theorem hyperStepSched_kernel_nil {l : Label} (hhs : hyperStep sys μ₁ l μ₂)
    {s₁ : State} (hs₁ : s₁ ∈ μ₁.support) (s'' : State) :
    (⟨PMF.pure s₁, hyperStepSched hhs⟩ : ProbabilisticExecution sys).kernel
        ⟨s₁, Seq.nil⟩ (l, s'') = ((hhs.kernel s₁).bind id) s'' := by
  classical
  unfold ProbabilisticExecution.kernel
  have hnext : (hyperStepSched hhs).next ⟨s₁, Seq.nil⟩
      = (hhs.kernel s₁).map (fun μ' => some (l, μ')) := by
    rw [hyperStepSched_next_eq, if_pos ⟨rfl, hs₁⟩]
  have hmap : ∀ ν : PMF State,
      ((hhs.kernel s₁).map (fun μ' => some (l, μ'))) (some (l, ν))
        = (hhs.kernel s₁) ν := by
    intro ν
    rw [PMF.map_apply, tsum_eq_single ν (by
      intro μ'' hμ''
      rw [if_neg]
      intro h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact hμ'' h.2.symm), if_pos rfl]
  change ∑' ν, (hyperStepSched hhs).next ⟨s₁, Seq.nil⟩ (some (l, ν)) * ν s'' = _
  simp only [hnext, hmap]
  rw [PMF.bind_apply]
  rfl

/-- The halting mass of `hyperStepSched` on the single-transition fiber
`⟨s₁, [(l, s'')]⟩` is `((kernel s₁).bind id) s''`. -/
private theorem hyperStepSched_fiber {l : Label} (hhs : hyperStep sys μ₁ l μ₂)
    {s₁ : State} (hs₁ : s₁ ∈ μ₁.support) (s'' : State) :
    (hyperStepSched hhs).haltMass (PMF.pure s₁)
        ⟨⟨s₁, Seq.cons (l, s'') Seq.nil⟩,
          Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil⟩
      = ((hhs.kernel s₁).bind id) s'' := by
  classical
  change (⟨PMF.pure s₁, hyperStepSched hhs⟩ : ProbabilisticExecution sys).probOf
      ⟨s₁, Seq.cons (l, s'') Seq.nil⟩
      (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)
    * (hyperStepSched hhs).next ⟨s₁, Seq.cons (l, s'') Seq.nil⟩ none = ((hhs.kernel s₁).bind id) s''
  rw [hyperStepSched_next_none hhs ⟨s₁, Seq.cons (l, s'') Seq.nil⟩ (by
    rintro ⟨hnil, _⟩; exact absurd hnil (by simp)), mul_one]
  have happ : (Seq.nil.append (Seq.cons (l, s'') Seq.nil) : Seq (Label × State)).Terminates := by
    rw [Stream'.Seq.nil_append]
    exact Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
  rw [ProbabilisticExecution.probOf_congr _ ⟨s₁, Seq.cons (l, s'') Seq.nil⟩
      ⟨s₁, Seq.nil.append (Seq.cons (l, s'') Seq.nil)⟩ (by rw [Stream'.Seq.nil_append])
      (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil) happ,
    ProbabilisticExecution.probOf_append_singleton _ _ _ Stream'.Seq.terminates_nil _ happ,
    ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState]
  change (PMF.pure s₁) s₁ * (⟨PMF.pure s₁, hyperStepSched hhs⟩ : ProbabilisticExecution sys).kernel
      ⟨s₁, Seq.nil⟩ (l, s'') = _
  rw [PMF.pure_apply_self, one_mul, hyperStepSched_kernel_nil hhs hs₁ s'']

/-- A nonzero-halt-mass run of `hyperStepSched` (from `pure s₁`, `s₁ ∈ μ₁.support`)
is the single-transition fiber `⟨s₁, [(l, s'')]⟩` for some `s''`. -/
private theorem hyperStepSched_supp {l : Label} (hhs : hyperStep sys μ₁ l μ₂)
    {s₁ : State} (hs₁ : s₁ ∈ μ₁.support)
    (e : {e : AlterSeq State Label // e.trans.Terminates})
    (hne : (hyperStepSched hhs).haltMass (PMF.pure s₁) e ≠ 0) :
    ∃ s'', (⟨s₁, Seq.cons (l, s'') Seq.nil⟩ : AlterSeq State Label) = e.1 := by
  classical
  obtain ⟨⟨init', trans'⟩, hterm⟩ := e
  simp only at hterm hne ⊢
  set pe : ProbabilisticExecution sys := ⟨PMF.pure s₁, hyperStepSched hhs⟩ with hpe
  have hprob_ne : pe.probOf ⟨init', trans'⟩ hterm ≠ 0 := by
    intro h0; apply hne; unfold Scheduler.haltMass; rw [← hpe, h0, zero_mul]
  have hnone_ne : (hyperStepSched hhs).next ⟨init', trans'⟩ none ≠ 0 := by
    intro h0; apply hne; unfold Scheduler.haltMass; rw [← hpe, h0, mul_zero]
  -- `init' = s₁`: else `probOf` factors through `(pure s₁) init' = 0`.
  have hinit : init' = s₁ := by
    by_contra hne'
    apply hprob_ne
    rw [ProbabilisticExecution.probOf_init_factor (hyperStepSched hhs) (PMF.pure s₁)
      ⟨init', trans'⟩ hterm]
    change (PMF.pure s₁) init' * _ = 0
    rw [PMF.pure_apply_of_ne _ _ hne', zero_mul]
  -- `trans' ≠ nil`: else the empty history at `s₁ ∈ support` would not halt.
  have htrans_ne : trans' ≠ Seq.nil := by
    intro hnil
    apply hnone_ne
    rw [hyperStepSched_next_eq, if_pos ⟨hnil, by rw [hinit]; exact hs₁⟩, PMF.map_apply,
      ENNReal.tsum_eq_zero]
    intro μ''; rw [if_neg (by simp)]
  have hnonempty : trans'.toList hterm ≠ [] := by
    intro hnil; apply htrans_ne
    have := Stream'.Seq.ofList_toList trans' hterm
    rw [hnil, Stream'.Seq.ofList_nil] at this; exact this.symm
  obtain ⟨previous, last, h_prev, h_split, _, _⟩ :=
    Stream'.Seq.exists_split_last trans' hterm hnonempty
  have happ : (previous.append (Seq.cons last Seq.nil)).Terminates := h_split ▸ hterm
  have hprob_split : pe.probOf ⟨init', trans'⟩ hterm
      = pe.probOf ⟨init', previous⟩ h_prev * pe.kernel ⟨init', previous⟩ last := by
    rw [ProbabilisticExecution.probOf_congr pe ⟨init', trans'⟩
        ⟨init', previous.append (Seq.cons last Seq.nil)⟩ (by rw [h_split]) hterm happ,
      ProbabilisticExecution.probOf_append_singleton _ _ _ h_prev _ happ]
  have hker_ne : pe.kernel ⟨init', previous⟩ last ≠ 0 := by
    intro h0; apply hprob_ne; rw [hprob_split, h0, mul_zero]
  -- The kernel forces `previous = nil` and `last.1 = l`.
  have hprev_l : previous = Seq.nil ∧ last.1 = l := by
    by_cases hc : previous = Seq.nil ∧ init' ∈ μ₁.support
    · refine ⟨hc.1, ?_⟩
      by_contra hl
      apply hker_ne
      unfold ProbabilisticExecution.kernel
      have hsn : pe.scheduler.next ⟨init', previous⟩
          = (hhs.kernel init').map (fun μ' => some (l, μ')) := by
        rw [hpe]; change (hyperStepSched hhs).next ⟨init', previous⟩ = _
        rw [hyperStepSched_next_eq, if_pos hc]
      simp only [hsn]
      have hz : ∀ ν : PMF State,
          ((hhs.kernel init').map (fun μ' => some (l, μ'))) (some (last.1, ν)) = 0 := by
        intro ν
        rw [PMF.map_apply, ENNReal.tsum_eq_zero]
        intro μ''; rw [if_neg]
        intro h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact hl h.1
      simp only [hz, zero_mul, tsum_zero]
    · exfalso
      apply hker_ne
      unfold ProbabilisticExecution.kernel
      have hsn : pe.scheduler.next ⟨init', previous⟩ = PMF.pure none := by
        rw [hpe]; change (hyperStepSched hhs).next ⟨init', previous⟩ = _
        rw [hyperStepSched_next_eq, if_neg hc]
      simp only [hsn]
      have hz : ∀ ν : PMF State,
          (PMF.pure none : PMF (Option (Label × PMF State))) (some (last.1, ν)) = 0 :=
        fun ν => PMF.pure_apply_of_ne _ _ (by simp)
      simp only [hz, zero_mul, tsum_zero]
  refine ⟨last.2, ?_⟩
  obtain ⟨l₀, s₀⟩ := last
  simp only at hprev_l
  rw [hinit, h_split, hprev_l.1, Stream'.Seq.nil_append, hprev_l.2]

/-- A nonzero-halt-mass run of `hyperStepSched` (from `pure s₁`, `s₁ ∈ μ₁.support`,
`l ≠ τ`) has external trace `[l]`. -/
private theorem hyperStepSched_trace {l : Label} (hl : ¬ l = Silent.τ)
    (hhs : hyperStep sys μ₁ l μ₂) {s₁ : State} (hs₁ : s₁ ∈ μ₁.support)
    (e : {e : AlterSeq State Label // e.trans.Terminates})
    (hne : (hyperStepSched hhs).haltMass (PMF.pure s₁) e ≠ 0) :
    sys.trace e.1 = Seq.cons l Seq.nil := by
  obtain ⟨s'', hs''⟩ := hyperStepSched_supp hhs hs₁ e hne
  rw [← hs'', trace_singleton s₁ l s'', if_neg hl]

/-- **`g`-integrated single step.** Integrating `ψ` over the halting end-state of
`hyperStepSched` from `pure s₁` (for `s₁ ∈ μ₁.support`) equals integrating `ψ`
against the hyper-step outcome `(kernel s₁).bind id`. -/
private theorem hyperStepSched_integrate {l : Label} (hhs : hyperStep sys μ₁ l μ₂)
    {s₁ : State} (hs₁ : s₁ ∈ μ₁.support) (ψ : State → ENNReal) :
    (∑' g₁, (hyperStepSched hhs).haltMass (PMF.pure s₁) g₁ * ψ (g₁.1.endState g₁.2))
      = ∑' s'', ((hhs.kernel s₁).bind id) s'' * ψ s'' := by
  classical
  rw [reindex_fiber (fun s'' => (⟨s₁, Seq.cons (l, s'') Seq.nil⟩ : AlterSeq State Label))
    (fun _ => Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil)
    (by
      intro a b hab
      have h := (Stream'.Seq.cons_eq_cons.mp (congrArg AlterSeq.trans hab)).1
      exact (Prod.mk.injEq l a l b ▸ h).2)
    (fun g => (hyperStepSched hhs).haltMass (PMF.pure s₁) g * ψ (g.1.endState g.2))
    (fun g hg => hyperStepSched_supp hhs hs₁ g (fun h0 => hg (by rw [h0, zero_mul])))]
  refine tsum_congr (fun s'' => ?_)
  rw [hyperStepSched_fiber hhs hs₁ s'', AlterSeq.endState_singleton_cons]

/-! ### Witness existence and the segment-trace consequence -/

/-- **Witness existence**: every `sys^w` weak step `x ⤳[l] μ` is realised by some
`sys`-scheduler (τ via `weakTau.witnessScheduler`; external via
`pre-τ ; hyperStep l ; post-τ` glued with `Scheduler.bind`). Hence `schedOf` is a
genuine witness on valid steps. -/
theorem Realises_exists {x : State} {l : Label} {μ : PMF State}
    (h : sys^w.step x l μ) : ∃ σ : Scheduler sys, Realises σ x l μ := by
  obtain (⟨hτ, hwt⟩ | ⟨hl, hws⟩) := h
  · -- **τ-case**: the τ-closure witness scheduler realises the step.
    subst hτ
    refine ⟨hwt.witnessScheduler.toScheduler, hwt.witness_halts, ?_, ?_⟩
    · intro x'
      rw [hwt.witness_pushforward x']
      refine tsum_congr (fun e => ?_)
      rw [WeakScheduler.stateAfter_length_eq_endState e.1 e.2]
      rfl
    · intro e hpos
      rw [if_pos rfl]
      exact weakSched_trace_nil hwt.witnessScheduler (PMF.pure x) e hpos
  · -- **external case** (`l ≠ τ`): `weakStep = pre-τ ; hyperStep l ; post-τ`.  The
    -- witness is `pre.witness ; hyperStepSched ; post.witness` glued by `Scheduler.bind`.
    classical
    obtain ⟨μ₁, μ₂, hpre, hhs, hpost⟩ := hws
    have hμ₂ : ∀ s₂ : State, μ₂ s₂ = ∑' s₁, μ₁ s₁ * ((hhs.kernel s₁).bind id) s₂ := by
      intro s₂
      conv_lhs => rw [hhs.post_eq_bind]
      rw [PMF.bind_apply]
    -- `hmid_bad`: the middle+post block, run from any `s₁ ∈ μ₁.support`, puts all its
    -- halting mass on trajectories with external trace `[l]` (zero "bad-trace" mass).
    have hmid_bad : ∀ s₁ : State, s₁ ∈ μ₁.support →
        (∑' f₂, (Scheduler.bind (hyperStepSched hhs)
              (fun _ => hpost.witnessScheduler.toScheduler)).haltMass (PMF.pure s₁) f₂
            * (if sys.trace f₂.1 = Seq.cons l Seq.nil then (0 : ENNReal) else 1)) = 0 := by
      intro s₁ hs₁
      rw [Scheduler.bind_compose_integrate_gen (hyperStepSched hhs)
        (fun _ => hpost.witnessScheduler.toScheduler) (PMF.pure s₁)
        (fun e => if sys.trace e.1 = Seq.cons l Seq.nil then (0 : ENNReal) else 1)]
      refine ENNReal.tsum_eq_zero.mpr (fun g₁ => ?_)
      by_cases hg1 : (hyperStepSched hhs).haltMass (PMF.pure s₁) g₁ = 0
      · rw [hg1, zero_mul]
      · have htrg1 : sys.trace g₁.1 = Seq.cons l Seq.nil :=
          hyperStepSched_trace hl hhs hs₁ g₁ hg1
        have hinner : (∑' g₂, hpost.witnessScheduler.toScheduler.haltMass
              (PMF.pure (g₁.1.endState g₁.2)) g₂
            * (if sys.trace (WeakScheduler.concat g₁ g₂) = Seq.cons l Seq.nil then (0 : ENNReal)
                else 1)) = 0 := by
          refine ENNReal.tsum_eq_zero.mpr (fun g₂ => ?_)
          by_cases hg2 : hpost.witnessScheduler.toScheduler.haltMass
              (PMF.pure (g₁.1.endState g₁.2)) g₂ = 0
          · rw [hg2, zero_mul]
          · have htr2 : sys.trace g₂.1 = Seq.nil :=
              weakSched_trace_nil hpost.witnessScheduler _ g₂ hg2
            rw [trace_concat, htrg1, htr2, Stream'.Seq.append_nil, if_pos rfl, mul_zero]
        rw [hinner, mul_zero]
    -- `key`: the composed scheduler's `g`-integral over the halting end-state equals
    -- the `μ`-integral (the chained `weakTau`/`hyperStep` pushforwards).
    have key : ∀ g : State → ENNReal,
        (∑' e, (Scheduler.bind hpre.witnessScheduler.toScheduler
            (fun _ => Scheduler.bind (hyperStepSched hhs)
              (fun _ => hpost.witnessScheduler.toScheduler))).haltMass (PMF.pure x) e
            * g (e.1.endState e.2))
          = ∑' s, μ s * g s := by
      intro g
      -- middle pushforward `μ₁ → μ₂` against any test `P`.
      have step5 : ∀ P : State → ENNReal,
          (∑' s₁, μ₁ s₁ * ∑' s₂, ((hhs.kernel s₁).bind id) s₂ * P s₂)
            = ∑' s₂, μ₂ s₂ * P s₂ := by
        intro P
        calc (∑' s₁, μ₁ s₁ * ∑' s₂, ((hhs.kernel s₁).bind id) s₂ * P s₂)
            = ∑' s₁, ∑' s₂, μ₁ s₁ * (((hhs.kernel s₁).bind id) s₂ * P s₂) :=
              tsum_congr (fun _ => (ENNReal.tsum_mul_left).symm)
          _ = ∑' s₂, ∑' s₁, μ₁ s₁ * (((hhs.kernel s₁).bind id) s₂ * P s₂) := ENNReal.tsum_comm
          _ = ∑' s₂, (∑' s₁, μ₁ s₁ * ((hhs.kernel s₁).bind id) s₂) * P s₂ := by
              refine tsum_congr (fun s₂ => ?_)
              rw [← ENNReal.tsum_mul_right]
              exact tsum_congr (fun _ => by ring)
          _ = ∑' s₂, μ₂ s₂ * P s₂ := by
              refine tsum_congr (fun s₂ => ?_)
              rw [hμ₂ s₂]
      calc (∑' e, (Scheduler.bind hpre.witnessScheduler.toScheduler
              (fun _ => Scheduler.bind (hyperStepSched hhs)
                (fun _ => hpost.witnessScheduler.toScheduler))).haltMass (PMF.pure x) e
              * g (e.1.endState e.2))
          = ∑' f₁, hpre.witnessScheduler.toScheduler.haltMass (PMF.pure x) f₁
              * ∑' f₂, (Scheduler.bind (hyperStepSched hhs)
                  (fun _ => hpost.witnessScheduler.toScheduler)).haltMass
                  (PMF.pure (f₁.1.endState f₁.2)) f₂ * g (f₂.1.endState f₂.2) :=
            Scheduler.bind_compose_integrate hpre.witnessScheduler.toScheduler
              (fun _ => Scheduler.bind (hyperStepSched hhs)
                (fun _ => hpost.witnessScheduler.toScheduler)) (PMF.pure x) g
        _ = ∑' s₁, μ₁ s₁
              * ∑' f₂, (Scheduler.bind (hyperStepSched hhs)
                  (fun _ => hpost.witnessScheduler.toScheduler)).haltMass (PMF.pure s₁) f₂
                  * g (f₂.1.endState f₂.2) :=
            hpre.integrate (fun s₁ => ∑' f₂, (Scheduler.bind (hyperStepSched hhs)
              (fun _ => hpost.witnessScheduler.toScheduler)).haltMass (PMF.pure s₁) f₂
              * g (f₂.1.endState f₂.2))
        _ = ∑' s₁, μ₁ s₁
              * ∑' g₁, (hyperStepSched hhs).haltMass (PMF.pure s₁) g₁
                  * ∑' g₂, hpost.witnessScheduler.toScheduler.haltMass
                      (PMF.pure (g₁.1.endState g₁.2)) g₂ * g (g₂.1.endState g₂.2) := by
            refine tsum_congr (fun s₁ => ?_)
            rw [Scheduler.bind_compose_integrate (hyperStepSched hhs)
              (fun _ => hpost.witnessScheduler.toScheduler) (PMF.pure s₁) g]
        _ = ∑' s₁, μ₁ s₁
              * ∑' s₂, ((hhs.kernel s₁).bind id) s₂
                  * ∑' g₂, hpost.witnessScheduler.toScheduler.haltMass (PMF.pure s₂) g₂
                      * g (g₂.1.endState g₂.2) := by
            refine tsum_congr (fun s₁ => ?_)
            by_cases hmem : s₁ ∈ μ₁.support
            · rw [hyperStepSched_integrate hhs hmem
                (fun s₂ => ∑' g₂, hpost.witnessScheduler.toScheduler.haltMass (PMF.pure s₂) g₂
                  * g (g₂.1.endState g₂.2))]
            · rw [PMF.mem_support_iff, not_not] at hmem
              rw [hmem, zero_mul, zero_mul]
        _ = ∑' s₂, μ₂ s₂
              * ∑' g₂, hpost.witnessScheduler.toScheduler.haltMass (PMF.pure s₂) g₂
                  * g (g₂.1.endState g₂.2) :=
            step5 (fun s₂ => ∑' g₂, hpost.witnessScheduler.toScheduler.haltMass (PMF.pure s₂) g₂
              * g (g₂.1.endState g₂.2))
        _ = ∑' s, μ s * g s := weakTau_pure_integrate hpost g
    refine ⟨Scheduler.bind hpre.witnessScheduler.toScheduler
        (fun _ => Scheduler.bind (hyperStepSched hhs)
          (fun _ => hpost.witnessScheduler.toScheduler)), ?_, ?_, ?_⟩
    · -- (a) halts almost surely
      have h1 := key (fun _ => (1 : ENNReal))
      simp only [mul_one] at h1
      rw [h1]; exact μ.tsum_coe
    · -- (b) end-state pushforward is `μ`
      intro x'
      rw [show μ x' = ∑' s, μ s * (if s = x' then (1 : ENNReal) else 0) from by
        rw [tsum_eq_single x' (fun s hs => by rw [if_neg hs, mul_zero]), if_pos rfl, mul_one]]
      rw [← key (fun s => if s = x' then (1 : ENNReal) else 0)]
      refine tsum_congr (fun e => ?_)
      rw [WeakScheduler.stateAfter_length_eq_endState e.1 e.2]
    · -- (c) every halting trajectory has external trace `[l]`
      intro e hpos
      rw [if_neg hl]
      have hzero : (∑' e, (Scheduler.bind hpre.witnessScheduler.toScheduler
            (fun _ => Scheduler.bind (hyperStepSched hhs)
              (fun _ => hpost.witnessScheduler.toScheduler))).haltMass (PMF.pure x) e
          * (if sys.trace e.1 = Seq.cons l Seq.nil then (0 : ENNReal) else 1)) = 0 := by
        rw [Scheduler.bind_compose_integrate_gen hpre.witnessScheduler.toScheduler
          (fun _ => Scheduler.bind (hyperStepSched hhs)
            (fun _ => hpost.witnessScheduler.toScheduler)) (PMF.pure x)
          (fun e => if sys.trace e.1 = Seq.cons l Seq.nil then (0 : ENNReal) else 1)]
        refine ENNReal.tsum_eq_zero.mpr (fun f₁ => ?_)
        by_cases hf1 : hpre.witnessScheduler.toScheduler.haltMass (PMF.pure x) f₁ = 0
        · rw [hf1, zero_mul]
        · have hmem : f₁.1.endState f₁.2 ∈ μ₁.support := weakTau_endState_mem hpre f₁ hf1
          have htr1 : sys.trace f₁.1 = Seq.nil :=
            weakSched_trace_nil hpre.witnessScheduler (PMF.pure x) f₁ hf1
          rw [show (∑' f₂, (Scheduler.bind (hyperStepSched hhs)
                  (fun _ => hpost.witnessScheduler.toScheduler)).haltMass
                  (PMF.pure (f₁.1.endState f₁.2)) f₂
                * (if sys.trace (WeakScheduler.concat f₁ f₂) = Seq.cons l Seq.nil then (0 : ENNReal)
                    else 1))
              = ∑' f₂, (Scheduler.bind (hyperStepSched hhs)
                  (fun _ => hpost.witnessScheduler.toScheduler)).haltMass
                  (PMF.pure (f₁.1.endState f₁.2)) f₂
                * (if sys.trace f₂.1 = Seq.cons l Seq.nil then (0 : ENNReal) else 1) from
            tsum_congr (fun f₂ => by rw [trace_concat, htr1, Stream'.Seq.nil_append])]
          rw [hmid_bad (f₁.1.endState f₁.2) hmem, mul_zero]
      have he := ENNReal.tsum_eq_zero.mp hzero e
      rw [mul_eq_zero] at he
      rcases he with h | h
      · exact absurd h hpos
      · by_contra htr
        rw [if_neg htr] at h
        exact one_ne_zero h

/-- `schedOf` of a valid weak step realises it. -/
theorem schedOf_realises {x : State} {l : Label} {μ : PMF State}
    (h : sys^w.step x l μ) : Realises (schedOf sys x l μ) x l μ := by
  classical
  unfold schedOf
  rw [dif_pos (Realises_exists h)]
  exact (Realises_exists h).choose_spec

open Classical in
/-- **Segment-trace lemma**: a positive-halt-mass run of a realising witness has
exactly the weak step's external trace (`[]` for an internal step, `[l]` otherwise).
This is just the third `Realises` clause. -/
theorem trace_of_halt {σ : Scheduler sys} {x : State} {l : Label} {μ : PMF State}
    (hR : Realises σ x l μ) (e : {e : AlterSeq State Label // e.trans.Terminates})
    (hpos : σ.haltMass (PMF.pure x) e ≠ 0) :
    sys.trace e.1 = if l = Silent.τ then Seq.nil else Seq.cons l Seq.nil :=
  hR.2.2 e hpos

/-! ### The invariant -/

/-- The trace invariant maintained at every reachable configuration:

* `trace_eq` — the committed `sys^w`- and `sys`-executions have equal traces;
* `e_fin`/`e'_fin` — the committed concrete execution and the current segment are finite;
* `e'_init` — the current segment starts at the end of the committed concrete execution;
* `seg` — while a weak step is in progress (`wt = some (lw, μw)`), it is valid, `s` is
  its witness, and `e'` is a positive-probability run of `s`. -/
structure Inv (c : Config sys) : Prop where
  trace_eq : sys.trace c.we = sys.trace c.e
  e_fin : c.e.trans.Terminates
  e'_fin : c.e'.trans.Terminates
  e'_init : c.e'.init = lastOf c.e
  seg : ∀ lw μw, c.wt = some (lw, μw) →
     sys^w.step (lastOf c.e) lw μw ∧
     c.s = schedOf sys (lastOf c.e) lw μw ∧
     (⟨PMF.pure (lastOf c.e), c.s⟩ : ProbabilisticExecution sys).probOf c.e' e'_fin ≠ 0

/-- If a guarded weight `if P then a else 0` is nonzero, then `a` is nonzero
(regardless of the guard). Used to peel a `step`/`reachAfter` guard without
`split_ifs` descending into nested `if`s. -/
private theorem ne_zero_of_ite_ne_zero {P : Prop} [Decidable P] {a : ENNReal}
    (h : (if P then a else 0) ≠ 0) : a ≠ 0 := by
  intro ha; rw [ha, ite_self] at h; exact h rfl

/-- A nonzero guarded weight forces its guard. -/
private theorem of_ite_ne_zero {P : Prop} [Decidable P] {a : ENNReal}
    (h : (if P then a else 0) ≠ 0) : P := by
  by_contra hP; rw [if_neg hP] at h; exact h rfl

open Classical in
/-- **Inner-draw positivity**: at every reachable configuration with an active weak step
(`wt = some p`), the witness scheduler emitted its current inner draw `t` with positive
probability, `s.next e' t ≠ 0` (whether `t` is a real step or the halt `none`). Each
instruction that sets `t` while `wt` is active multiplies by exactly this factor. -/
theorem reachAfter_inner_pos (ws : Scheduler sys^w) :
    ∀ (n : ℕ) (c : Config sys), reachAfter ws n c ≠ 0 →
      ∀ p, c.wt = some p → c.s.next c.e' c.t ≠ 0 := by
  have wtMatch : ∀ (cc : Config sys) (p : Label × PMF State), cc.wt = some p →
      (match cc.wt with
       | none => if cc.t = none then (1 : ENNReal) else 0
       | some _ => cc.s.next cc.e' cc.t) ≠ 0 →
      cc.s.next cc.e' cc.t ≠ 0 := by
    intro cc p hwt hm
    simp only [hwt] at hm; exact hm
  intro n
  induction n with
  | zero =>
    intro c hreach p hwt
    simp only [reachAfter] at hreach
    by_cases hcond : (c.we = (⟨sys.init, Seq.nil⟩ : AlterSeq State Label) ∧
        c.e = ⟨sys.init, Seq.nil⟩ ∧ c.e' = ⟨sys.init, Seq.nil⟩ ∧
        (∀ p, c.wt = some p → c.s = schedOf sys sys.init p.1 p.2) ∧
        (c.wt = none → c.s = Scheduler.halt sys))
    · rw [if_pos hcond] at hreach
      exact wtMatch c p hwt (mul_ne_zero_iff.mp hreach).2
    · rw [if_neg hcond] at hreach; exact absurd rfl hreach
  | succ n _ =>
    intro c hreach p hwt
    rw [reachAfter] at hreach
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, reachAfter ws n c₀ * step ws c₀ c ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hreach (ENNReal.tsum_eq_zero.mpr hcon)
    have hstep := (mul_ne_zero_iff.mp hc₀).2
    obtain ⟨we₀, e₀, wt₀, s₀, e'₀, t₀⟩ := c₀
    cases wt₀ with
    | none => simp only [step] at hstep; exact absurd rfl hstep
    | some wtp =>
      obtain ⟨lw, μw⟩ := wtp
      cases t₀ with
      | none =>
        simp only [step] at hstep
        exact wtMatch c p hwt (mul_ne_zero_iff.mp (ne_zero_of_ite_ne_zero hstep)).2
      | some tp =>
        obtain ⟨l'', μ''⟩ := tp
        simp only [step] at hstep
        split_ifs at hstep with hcond
        · obtain ⟨_, _, _, hcs, _, _⟩ := hcond
          rw [hcs]; exact (mul_ne_zero_iff.mp hstep).2
        · exact absurd rfl hstep

open Classical in
/-- **Finiteness of the committed abstract execution `we`.** It starts at `nil` and
each commit appends one transition, so it stays finite at every reachable config. -/
private theorem reachAfter_we_fin (ws : Scheduler sys^w) :
    ∀ (n : ℕ) (c : Config sys), reachAfter ws n c ≠ 0 → c.we.trans.Terminates := by
  intro n
  induction n with
  | zero =>
    intro c hreach
    by_cases hcond : (c.we = (⟨sys.init, Seq.nil⟩ : AlterSeq State Label) ∧
        c.e = ⟨sys.init, Seq.nil⟩ ∧ c.e' = ⟨sys.init, Seq.nil⟩ ∧
        (∀ p, c.wt = some p → c.s = schedOf sys sys.init p.1 p.2) ∧
        (c.wt = none → c.s = Scheduler.halt sys))
    · rw [hcond.1]; exact Stream'.Seq.terminates_nil
    · simp only [reachAfter] at hreach; rw [if_neg hcond] at hreach; exact absurd rfl hreach
  | succ n ih =>
    intro c hreach
    rw [reachAfter] at hreach
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, reachAfter ws n c₀ * step ws c₀ c ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hreach (ENNReal.tsum_eq_zero.mpr hcon)
    rw [mul_ne_zero_iff] at hc₀
    obtain ⟨hreach₀, hstep⟩ := hc₀
    have hwe₀ := ih c₀ hreach₀
    obtain ⟨we₀, e₀, wt₀, s₀, e'₀, t₀⟩ := c₀
    cases wt₀ with
    | none => simp only [step] at hstep; exact absurd rfl hstep
    | some wtp =>
      obtain ⟨lw, μw⟩ := wtp
      cases t₀ with
      | none =>
        simp only [step] at hstep
        set eN : AlterSeq State Label := ⟨e₀.init, e₀.trans.append e'₀.trans⟩ with heN
        have hcond := of_ite_ne_zero hstep
        rw [hcond.2.1]
        exact ⟨_, Stream'.Seq.terminatedAt_append_find hwe₀
          (show (Seq.cons (lw, lastOf eN) Seq.nil).TerminatedAt 1 from rfl)⟩
      | some tp =>
        simp only [step] at hstep
        have hcond := of_ite_ne_zero hstep
        rw [hcond.1]; exact hwe₀

open Classical in
/-- **The invariant holds at every configuration reachable after `n` instructions.**
Induction on `n`: the base case is the start; the `inner` step preserves `we`/`e`; the
`outer` (commit) step appends a weak step to `we` and its concrete segment to `e`, and
the segment-trace lemma gives them equal trace contributions. -/
theorem reachAfter_Inv (ws : Scheduler sys^w) :
    ∀ (n : ℕ) (c : Config sys), reachAfter ws n c ≠ 0 → Inv c := by
  intro n
  induction n with
  | zero =>
      intro c h
      -- `reachAfter 0 c ≠ 0`: `c` is the start (`we = e = e' = ⟨init, nil⟩`), so the
      -- traces are both `nil`; the `seg` clause uses `ws.valid` on the first draw.
      simp only [reachAfter] at h
      have key : (c.we = (⟨sys.init, Seq.nil⟩ : AlterSeq State Label) ∧
          c.e = ⟨sys.init, Seq.nil⟩ ∧ c.e' = ⟨sys.init, Seq.nil⟩ ∧
          (∀ p, c.wt = some p → c.s = schedOf sys sys.init p.1 p.2) ∧
          (c.wt = none → c.s = Scheduler.halt sys)) ∧
          ws.next ⟨sys.init, Seq.nil⟩ c.wt ≠ 0 := by
        by_cases hc : (c.we = (⟨sys.init, Seq.nil⟩ : AlterSeq State Label) ∧
            c.e = ⟨sys.init, Seq.nil⟩ ∧ c.e' = ⟨sys.init, Seq.nil⟩ ∧
            (∀ p, c.wt = some p → c.s = schedOf sys sys.init p.1 p.2) ∧
            (c.wt = none → c.s = Scheduler.halt sys))
        · rw [if_pos hc] at h; exact ⟨hc, (mul_ne_zero_iff.mp h).1⟩
        · rw [if_neg hc] at h; exact absurd rfl h
      obtain ⟨⟨hwe, hce, hce', hwt_s, _⟩, hnext⟩ := key
      have hlast : lastOf (⟨sys.init, Seq.nil⟩ : AlterSeq State Label) = sys.init := by
        unfold lastOf
        rw [dif_pos Stream'.Seq.terminates_nil]
        exact AlterSeq.endState_of_trans_nil _ rfl _
      have hlastc : lastOf c.e = sys.init := by rw [hce]; exact hlast
      have he'fin : c.e'.trans.Terminates := by rw [hce']; exact Stream'.Seq.terminates_nil
      refine
        { trace_eq := by rw [hwe, hce]
          e_fin := by rw [hce]; exact Stream'.Seq.terminates_nil
          e'_fin := he'fin
          e'_init := by rw [hce', hce]; exact hlast.symm
          seg := ?_ }
      intro lw μw hwt
      refine ⟨?_, ?_, ?_⟩
      · -- `sys^w.step (lastOf c.e) lw μw`
        rw [hlastc]
        have hmem : some (lw, μw) ∈ (ws.next ⟨sys.init, Seq.nil⟩).support := by
          rw [PMF.mem_support_iff, ← hwt]; exact hnext
        exact ws.valid ⟨sys.init, Seq.nil⟩ 0 sys.init rfl rfl lw μw hmem
      · -- `c.s = schedOf sys (lastOf c.e) lw μw`
        rw [hlastc]; exact hwt_s (lw, μw) hwt
      · -- `probOf c.e' ≠ 0`
        rw [ProbabilisticExecution.probOf_congr _ c.e' ⟨sys.init, Seq.nil⟩ hce' he'fin
            Stream'.Seq.terminates_nil, ProbabilisticExecution.probOf_nil, hlastc]
        change (PMF.pure sys.init) sys.init ≠ 0
        rw [PMF.pure_apply_self]; exact one_ne_zero
  | succ n ih =>
      intro c h
      -- `reachAfter (n+1) c = ∑' c₀, reachAfter n c₀ * step ws c₀ c ≠ 0`, so some `c₀`
      -- has `reachAfter n c₀ ≠ 0` (hence `Inv c₀` by `ih`) and `step ws c₀ c ≠ 0`.
      -- Case on `step` (inner vs outer commit); the outer case invokes `trace_of_halt`.
      rw [reachAfter] at h
      obtain ⟨c₀, hc₀⟩ : ∃ c₀, reachAfter ws n c₀ * step ws c₀ c ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact h (ENNReal.tsum_eq_zero.mpr hcon)
      rw [mul_ne_zero_iff] at hc₀
      obtain ⟨hreach₀, hstep⟩ := hc₀
      have hInv₀ := ih c₀ hreach₀
      obtain ⟨we₀, e₀, wt₀, s₀, e'₀, t₀⟩ := c₀
      cases wt₀ with
      | none => simp only [step] at hstep; exact absurd rfl hstep
      | some wtp =>
        obtain ⟨lw, μw⟩ := wtp
        cases t₀ with
        | none =>
          -- **OUTER** (commit): `c.t = none`. Commit `e ⌢ e'`, append `(lw, ·)` to `we`.
          simp only [step] at hstep
          set eN : AlterSeq State Label := ⟨e₀.init, e₀.trans.append e'₀.trans⟩ with heN
          set weN : AlterSeq State Label :=
            ⟨we₀.init, we₀.trans.append (Seq.cons (lw, lastOf eN) Seq.nil)⟩ with hweN
          obtain ⟨hce, hcwe, hce', hcsched, _⟩ := of_ite_ne_zero hstep
          have ht_eq := hInv₀.trace_eq
          have he_fin := hInv₀.e_fin
          have he'_fin := hInv₀.e'_fin
          obtain ⟨hstepw, hsched₀, hprob₀⟩ := hInv₀.seg lw μw rfl
          have hwe_fin := reachAfter_we_fin ws n ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩ hreach₀
          dsimp only at ht_eq he_fin he'_fin hstepw hsched₀ hprob₀ hwe_fin
          have heN_fin : eN.trans.Terminates :=
            ⟨_, Stream'.Seq.terminatedAt_append_find he_fin he'_fin.choose_spec⟩
          -- The committed segment `e'₀` has the weak step's external trace.
          have hRealises : Realises s₀ (lastOf e₀) lw μw := by
            rw [hsched₀]; exact schedOf_realises hstepw
          have hnext_halt : s₀.next e'₀ none ≠ 0 :=
            reachAfter_inner_pos ws n ⟨we₀, e₀, some (lw, μw), s₀, e'₀, none⟩ hreach₀ (lw, μw) rfl
          have hhalt : s₀.haltMass (PMF.pure (lastOf e₀)) ⟨e'₀, he'_fin⟩ ≠ 0 := by
            unfold Scheduler.haltMass; exact mul_ne_zero hprob₀ hnext_halt
          have htrace_e' : sys.trace e'₀ = if lw = Silent.τ then Seq.nil else Seq.cons lw Seq.nil :=
            trace_of_halt hRealises ⟨e'₀, he'_fin⟩ hhalt
          have hce'_fin : c.e'.trans.Terminates := by rw [hce']; exact Stream'.Seq.terminates_nil
          refine
            { trace_eq := ?_
              e_fin := by rw [hce]; exact heN_fin
              e'_fin := hce'_fin
              e'_init := by rw [hce', hce]
              seg := ?_ }
          · -- **trace_eq**: `we = we₀ ++ [(lw,·)]`, `e = e₀ ⌢ e'₀`; the contributions match.
            rw [hcwe, hce, hweN, trace_append we₀.init we₀.trans _ hwe_fin,
              trace_singleton we₀.init lw (lastOf eN), heN,
              trace_append e₀.init e₀.trans _ he_fin]
            congr 1
            rw [show sys.trace (⟨e₀.init, e'₀.trans⟩ : AlterSeq State Label) = sys.trace e'₀
              from rfl, htrace_e']
          · -- **seg** for the freshly drawn weak step.
            intro lw' μw' hwt'
            have hweN_term : weN.trans.Terminates := by
              rw [hweN]
              exact ⟨_, Stream'.Seq.terminatedAt_append_find hwe_fin
                (show (Seq.cons (lw, lastOf eN) Seq.nil).TerminatedAt 1 from rfl)⟩
            refine ⟨?_, ?_, ?_⟩
            · -- `sys^w.step (lastOf c.e) lw' μw'` from `ws.valid` at `weN`.
              rw [hce]
              have hmem : some (lw', μw') ∈ (ws.next weN).support := by
                rw [PMF.mem_support_iff]
                have hw := (mul_ne_zero_iff.mp (ne_zero_of_ite_ne_zero hstep)).1
                rwa [hwt'] at hw
              have hstate : weN.stateAt (Nat.find hweN_term) = some (lastOf eN) := by
                rw [AlterSeq.stateAt_find_eq_endState weN hweN_term]
                congr 1
                exact AlterSeq.endState_append_singleton ⟨we₀.init, we₀.trans⟩ hwe_fin lw
                  (lastOf eN)
              exact ws.valid weN (Nat.find hweN_term) (lastOf eN) (Nat.find_spec hweN_term)
                hstate lw' μw' hmem
            · -- `c.s = schedOf sys (lastOf c.e) lw' μw'`.
              rw [hce]; exact hcsched (lw', μw') hwt'
            · -- `probOf c.e' ≠ 0`: the reset segment is the empty run.
              rw [ProbabilisticExecution.probOf_congr _ c.e' ⟨lastOf eN, Seq.nil⟩ hce' hce'_fin
                  Stream'.Seq.terminates_nil, ProbabilisticExecution.probOf_nil, hce]
              change (PMF.pure (lastOf eN)) (lastOf eN) ≠ 0
              rw [PMF.pure_apply_self]; exact one_ne_zero
        | some tp =>
          obtain ⟨l', μ'⟩ := tp
          -- **INNER**: `c.t = some (l', μ')`. `we`/`e` unchanged; `e'` gains one step.
          simp only [step] at hstep
          split_ifs at hstep with hcond
          · obtain ⟨hwe, hce, hcwt, hcs, hce'i, hce't⟩ := hcond
            have ht_eq := hInv₀.trace_eq
            have he_fin := hInv₀.e_fin
            have he'_fin := hInv₀.e'_fin
            have he'_init := hInv₀.e'_init
            have hμ' : μ' (lastOf c.e') ≠ 0 := (mul_ne_zero_iff.mp hstep).1
            have happ_fin : (e'₀.trans.append (Seq.cons (l', lastOf c.e') Seq.nil)).Terminates :=
              ⟨_, Stream'.Seq.terminatedAt_append_find he'_fin
                (show (Seq.cons (l', lastOf c.e') Seq.nil).TerminatedAt 1 from rfl)⟩
            have hce'_fin : c.e'.trans.Terminates := by rw [hce't]; exact happ_fin
            refine
              { trace_eq := by rw [hwe, hce]; exact ht_eq
                e_fin := by rw [hce]; exact he_fin
                e'_fin := hce'_fin
                e'_init := by rw [hce'i, he'_init, hce]
                seg := ?_ }
            intro lw' μw' hwt'
            rw [hcwt] at hwt'
            simp only [Option.some.injEq, Prod.mk.injEq] at hwt'
            obtain ⟨rfl, rfl⟩ := hwt'
            obtain ⟨hstepw, hsched, hprob₀⟩ := hInv₀.seg lw μw rfl
            refine ⟨by rw [hce]; exact hstepw, by rw [hcs, hce]; exact hsched, ?_⟩
            -- `probOf c.e' ≠ 0`
            have hnext : s₀.next e'₀ (some (l', μ')) ≠ 0 :=
              reachAfter_inner_pos ws n ⟨we₀, e₀, some (lw, μw), s₀, e'₀, some (l', μ')⟩
                hreach₀ (lw, μw) rfl
            have hkernel : (⟨PMF.pure (lastOf e₀), s₀⟩ : ProbabilisticExecution sys).kernel e'₀
                (l', lastOf c.e') ≠ 0 := by
              unfold ProbabilisticExecution.kernel
              intro h0
              have hz := (ENNReal.tsum_eq_zero.mp h0) μ'
              rw [mul_eq_zero] at hz
              rcases hz with hz | hz
              · exact hnext hz
              · exact hμ' hz
            have hce'_eq : c.e' = (⟨e'₀.init,
                e'₀.trans.append (Seq.cons (l', lastOf c.e') Seq.nil)⟩ : AlterSeq State Label) := by
              rw [← hce'i, ← hce't]
            rw [hcs, hce, ProbabilisticExecution.probOf_congr
                (⟨PMF.pure (lastOf e₀), s₀⟩ : ProbabilisticExecution sys) c.e'
                ⟨e'₀.init, e'₀.trans.append (Seq.cons (l', lastOf c.e') Seq.nil)⟩
                hce'_eq hce'_fin happ_fin,
              ProbabilisticExecution.probOf_append_singleton _ e'₀.init e'₀.trans he'_fin
                (l', lastOf c.e') happ_fin]
            exact mul_ne_zero hprob₀ hkernel
          · exact absurd rfl hstep

open Classical in
/-- **Trace preservation (the goal).** Every reachable configuration has matching
`sys^w`- and `sys`-traces on its committed executions. -/
theorem reachProb_trace_eq (ws : Scheduler sys^w) (c : Config sys)
    (h : reachProb ws c ≠ 0) : sys.trace c.we = sys.trace c.e := by
  rw [reachProb] at h
  obtain ⟨n, hn⟩ : ∃ n, reachAfter ws n c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h (ENNReal.tsum_eq_zero.mpr hcon)
  exact (reachAfter_Inv ws n c hn).trace_eq

end PLTS
