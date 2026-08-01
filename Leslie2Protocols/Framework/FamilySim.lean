/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.Framework.IdleFamily
import Leslie2.Simulation.ForwardLTS

/-!
# Forward simulation is a congruence for `System.family`

Per-instance forward simulations lift to the ℕ-indexed families of
`System.family` (`Framework/IdleFamily.lean`): if every instance `instC r`
forward-simulates `instA r` along `R r`, and the broadcast transforms are
compatible with `R` (`hglob`), then the concrete family forward-simulates the
abstract family along the pointwise relation `fun s t => ∀ r, R r (s r) (t r)`
(`ForwardSimulation.family`).

The proof transports the abstract instance's weak-transition witness execution
into the family via `AlterSeq.map (Function.update t r)` — the non-moving
coordinates just carry the ambient joint state along:

* `System.weakLSilent_of_step` / `System.weakLStep_of_step` — a single Dirac
  step is a (one-transition) weak run; `weakLStep_tauThen` is the two-step
  burst, a silent step followed by an external one;
* `AlterSeq.stateAt_map`, `AlterSeq.endState_map`, `System.trace_map_state` —
  `AlterSeq.map` glue: pointwise state maps commute with `stateAt`/`endState`
  and leave the trace unchanged (the trace only reads labels);
* `System.weakLSilent_family` / `System.weakLStep_family` — a weak run of the
  instance `inst r` embeds into the family, moving only coordinate `r`.

The broadcast and idle disjuncts of the family are matched by the abstract
family's own one-step broadcast/idle transitions, so no instance simulation is
consulted there — broadcast compatibility comes from `hglob` and idling
preserves the relation trivially.
-/

open Stream'

namespace PLTS

variable {State State' σ Label : Type}

/-! ### Single-step weak transitions -/

section SingleStep

variable {sys : System State Label}

private theorem singleStep_partial_exec {q q' : State} {l : Label}
    (h : sys.step q l (PMF.pure q')) :
    is_partial_exec ⟨q, Seq.cons (l, q') Seq.nil⟩ sys := by
  intro k l' s' hk
  cases k with
  | zero =>
    rw [Stream'.Seq.get?_cons_zero] at hk
    injection hk with hk
    injection hk with h1 h2
    subst h1
    subst h2
    exact ⟨q, PMF.pure q', rfl, h, by rw [PMF.mem_support_pure_iff]⟩
  | succ k =>
    rw [Stream'.Seq.get?_cons_succ, Stream'.Seq.get?_nil] at hk
    exact absurd hk (by simp)

private theorem terminates₂ {l₀ l₁ : Label} {q₁ q₂ : State} :
    (Seq.cons (l₀, q₁) (Seq.cons (l₁, q₂) Seq.nil) : Seq (Label × State)).Terminates :=
  Seq.terminates_cons_iff.mpr (Seq.terminates_cons_iff.mpr Seq.terminates_nil)

/-- `endState` of a two-transition alternating sequence. -/
private theorem endState₂ (q₀ : State) (l₀ : Label) (q₁ : State) (l₁ : Label)
    (q₂ : State) :
    (⟨q₀, Seq.cons (l₀, q₁) (Seq.cons (l₁, q₂) Seq.nil)⟩ : AlterSeq State Label).endState
      terminates₂ = q₂ := by
  classical
  set e : AlterSeq State Label := ⟨q₀, Seq.cons (l₀, q₁) (Seq.cons (l₁, q₂) Seq.nil)⟩ with he
  have hterm : e.trans.Terminates := terminates₂
  have hfind : Nat.find hterm = 2 := by
    refine le_antisymm (Nat.find_le (show e.trans.TerminatedAt 2 from rfl)) ?_
    rw [Nat.le_find_iff]
    intro m hm
    interval_cases m
    · exact Seq.cons_not_terminatedAt_zero
    · intro hc
      exact absurd (hc : e.trans.get? 1 = none) (by simp [he])
  have hstate := AlterSeq.stateAt_find_eq_endState e hterm
  rw [hfind] at hstate
  have h2 : e.stateAt 2 = some q₂ := rfl
  rw [h2] at hstate
  exact (Option.some.inj hstate).symm

variable [Silent Label]

/-- A single internal Dirac step is a silent weak transition. -/
theorem System.weakLSilent_of_step {q q' : State}
    (h : sys.step q Silent.τ (PMF.pure q')) : sys.weakLSilent q q' :=
  ⟨⟨q, Seq.cons (Silent.τ, q') Seq.nil⟩,
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil,
    singleStep_partial_exec h, rfl,
    AlterSeq.endState_singleton_cons q Silent.τ q',
    by
      unfold System.trace
      rw [Stream'.Seq.filter_cons_neg _ _ (by simp)]
      exact sys.trace_init q'⟩

/-- A single external Dirac step is a weak transition. -/
theorem System.weakLStep_of_step {q q' : State} {l : Label}
    (hl : ¬ l = Silent.τ) (h : sys.step q l (PMF.pure q')) :
    sys.weakLStep q l q' :=
  ⟨⟨q, Seq.cons (l, q') Seq.nil⟩,
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil,
    singleStep_partial_exec h, rfl,
    AlterSeq.endState_singleton_cons q l q',
    by rw [System.trace_cons_external sys q l q' Seq.nil hl, System.trace_init]⟩

/-- **The burst.** A silent step followed by an external step is a weak
`l`-transition: the τ-step is the leading τ-closure. -/
theorem weakLStep_tauThen {q q₁ q' : State} {l : Label}
    (h1 : sys.LStep q Silent.τ q₁) (h2 : sys.LStep q₁ l q')
    (hl : ¬ l = Silent.τ) : sys.weakLStep q l q' := by
  refine ⟨⟨q, Seq.cons (Silent.τ, q₁) (Seq.cons (l, q') Seq.nil)⟩, terminates₂,
    ?_, rfl, endState₂ q Silent.τ q₁ l q', ?_⟩
  · intro k l' s' hk
    match k with
    | 0 =>
      rw [Seq.get?_cons_zero] at hk
      injection hk with hk
      injection hk with ha hb
      subst ha; subst hb
      exact ⟨q, PMF.pure q₁, rfl, h1, by rw [PMF.mem_support_pure_iff]⟩
    | 1 =>
      rw [Seq.get?_cons_succ, Seq.get?_cons_zero] at hk
      injection hk with hk
      injection hk with ha hb
      subst ha; subst hb
      exact ⟨q₁, PMF.pure q', rfl, h2, by rw [PMF.mem_support_pure_iff]⟩
    | (k + 2) =>
      rw [Seq.get?_cons_succ, Seq.get?_cons_succ, Seq.get?_nil] at hk
      exact absurd hk (by simp)
  · have htail : sys.trace ⟨q₁, Seq.cons (l, q') Seq.nil⟩ = Seq.cons l Seq.nil := by
      rw [System.trace_cons_external sys q₁ l q' Seq.nil hl, System.trace_init]
    unfold System.trace at htail ⊢
    rw [Seq.filter_cons_neg _ _ (by simp)]
    exact htail

end SingleStep

/-! ### `AlterSeq.map` transport glue -/

/-- `AlterSeq.map` commutes with `stateAt`. -/
theorem AlterSeq.stateAt_map (f : State → State') (e : AlterSeq State Label) (n : ℕ) :
    (e.map f).stateAt n = (e.stateAt n).map f := by
  cases n with
  | zero => rfl
  | succ k =>
    change ((e.trans.map fun lq => (lq.1, f lq.2)).get? k).map Prod.snd
      = ((e.trans.get? k).map Prod.snd).map f
    rw [Stream'.Seq.map_get?]
    cases e.trans.get? k with
    | none => rfl
    | some lq => rfl

/-- `AlterSeq.map` commutes with `endState`. -/
theorem AlterSeq.endState_map (f : State → State') (e : AlterSeq State Label)
    (h : e.trans.Terminates) (h' : (e.map f).trans.Terminates) :
    (e.map f).endState h' = f (e.endState h) := by
  have hterm_iff : ∀ n, (e.map f).trans.TerminatedAt n ↔ e.trans.TerminatedAt n := by
    intro n
    change (e.trans.map fun lq => (lq.1, f lq.2)).get? n = none ↔ e.trans.get? n = none
    rw [Stream'.Seq.map_get?]
    cases e.trans.get? n <;> simp
  have hfind : Nat.find h' = Nat.find h := by
    apply le_antisymm
    · exact Nat.find_le ((hterm_iff _).mpr (Nat.find_spec h))
    · exact Nat.find_le ((hterm_iff _).mp (Nat.find_spec h'))
  have h1 := AlterSeq.stateAt_find_eq_endState (e.map f) h'
  rw [hfind, AlterSeq.stateAt_map, AlterSeq.stateAt_find_eq_endState e h] at h1
  simp only [Option.map_some, Option.some.injEq] at h1
  exact h1.symm

/-- The trace only reads labels, so it is invariant under pointwise state maps
(for any two systems over the same label type). -/
theorem System.trace_map_state [Silent Label] (sys' : System State' Label)
    (sys : System State Label) (f : State → State') (e : AlterSeq State Label) :
    sys'.trace (e.map f) = sys.trace e := by
  unfold System.trace
  rw [show (e.map f).trans = e.trans.map (fun lq : Label × State => (lq.1, f lq.2)) from rfl,
    Stream'.Seq.filter_map, ← Stream'.Seq.map_comp]
  rfl

section FamilyEmbedding

variable [Silent Label]

/-- Every external label occurring in a terminating execution occurs in its
trace. -/
private theorem mem_trace_of_external {sys : System State Label}
    {e : AlterSeq State Label} (hterm : e.trans.Terminates) {n : ℕ} {l : Label}
    {s' : State} (hn : e.trans.get? n = some (l, s')) (hl : ¬ l = Silent.τ) :
    ∃ m, (sys.trace e).get? m = some l := by
  classical
  have hLn : (e.trans.toList hterm)[n]? = some (l, s') := by
    have h1 : (Seq.ofList (e.trans.toList hterm)).get? n = some (l, s') := by
      rw [Stream'.Seq.ofList_toList e.trans hterm]
      exact hn
    rwa [Stream'.Seq.ofList_get?] at h1
  have htr : sys.trace e = ((Seq.ofList (e.trans.toList hterm)).filter
      (fun p => ¬ (p.1 = Silent.τ))).map Prod.fst := by
    unfold System.trace
    conv_lhs => rw [← Stream'.Seq.ofList_toList e.trans hterm]
  rw [htr, Stream'.Seq.ofList_filter, Stream'.Seq.map_ofList_pub]
  simp only [Stream'.Seq.ofList_get?]
  rw [← List.mem_iff_getElem?]
  refine List.mem_map.mpr ⟨(l, s'),
    List.mem_filter.mpr ⟨List.mem_of_getElem? hLn, ?_⟩, rfl⟩
  simpa using hl

/-- Transport a partial execution of the instance `inst r` into the family via
`Function.update t r`, provided every transition label is silent or owned by
round `r`. -/
private theorem is_partial_exec_map_family {inst : ℕ → System σ Label}
    {owns : Label → Option ℕ} {glob : Label → Prop} {act : Label → σ → σ}
    {r : ℕ} (t : ℕ → σ) {e : AlterSeq σ Label}
    (hpe : is_partial_exec e (inst r))
    (hlab : ∀ n l s', e.trans.get? n = some (l, s') → l = Silent.τ ∨ owns l = some r) :
    is_partial_exec (e.map (Function.update t r))
      (System.family inst owns glob act) := by
  intro n l s' hn
  rw [show (e.map (Function.update t r)).trans
      = e.trans.map (fun lq : Label × σ => (lq.1, Function.update t r lq.2)) from rfl,
    Stream'.Seq.map_get?] at hn
  cases hg : e.trans.get? n with
  | none =>
    rw [hg] at hn
    exact absurd hn (by simp)
  | some lq =>
    obtain ⟨l₀, x⟩ := lq
    rw [hg] at hn
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    obtain ⟨sn, μ, hsn, hstep, hmem⟩ := hpe n l₀ x hg
    refine ⟨Function.update t r sn,
      μ.map (Function.update (Function.update t r sn) r), ?_, ?_, ?_⟩
    · rw [AlterSeq.stateAt_map, hsn]
      rfl
    · refine (System.family_step_iff inst owns glob act).mpr ?_
      rcases hlab n l₀ x hg with hτ | howns
      · exact Or.inl ⟨hτ, r, μ, by rw [Function.update_self]; exact hstep, rfl⟩
      · exact Or.inr (Or.inl ⟨r, howns, μ,
          by rw [Function.update_self]; exact hstep, rfl⟩)
    · rw [PMF.mem_support_map_iff]
      exact ⟨x, hmem, Function.update_idem ..⟩

/-- A silent weak run of the instance `inst r` embeds into the family, moving
only coordinate `r`. -/
theorem System.weakLSilent_family {inst : ℕ → System σ Label}
    (owns : Label → Option ℕ) (glob : Label → Prop) (act : Label → σ → σ)
    {r : ℕ} {t : ℕ → σ} {q' : σ} (h : (inst r).weakLSilent (t r) q') :
    (System.family inst owns glob act).weakLSilent t (Function.update t r q') := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := h
  refine ⟨e.map (Function.update t r),
    (AlterSeq.map_trans_terminates_iff (Function.update t r) e).mpr hterm,
    ?_, ?_, ?_, ?_⟩
  · refine is_partial_exec_map_family t hpe ?_
    intro n l₀ s₀ hn
    left
    by_contra hl₀
    obtain ⟨m, hm⟩ := mem_trace_of_external (sys := inst r) hterm hn hl₀
    rw [htr, Stream'.Seq.get?_nil] at hm
    exact absurd hm (by simp)
  · change Function.update t r e.init = t
    rw [hinit]
    exact Function.update_eq_self r t
  · rw [AlterSeq.endState_map (Function.update t r) e hterm, hend]
  · rw [System.trace_map_state _ (inst r)]
    exact htr

/-- A labelled weak run of the instance `inst r`, on a label owned by round
`r`, embeds into the family, moving only coordinate `r`. -/
theorem System.weakLStep_family {inst : ℕ → System σ Label}
    (owns : Label → Option ℕ) (glob : Label → Prop) (act : Label → σ → σ)
    {r : ℕ} {t : ℕ → σ} {l : Label} {q' : σ} (howns : owns l = some r)
    (h : (inst r).weakLStep (t r) l q') :
    (System.family inst owns glob act).weakLStep t l (Function.update t r q') := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := h
  refine ⟨e.map (Function.update t r),
    (AlterSeq.map_trans_terminates_iff (Function.update t r) e).mpr hterm,
    ?_, ?_, ?_, ?_⟩
  · refine is_partial_exec_map_family t hpe ?_
    intro n l₀ s₀ hn
    by_cases hl₀ : l₀ = Silent.τ
    · exact Or.inl hl₀
    · obtain ⟨m, hm⟩ := mem_trace_of_external (sys := inst r) hterm hn hl₀
      rw [htr] at hm
      cases m with
      | zero =>
        rw [Stream'.Seq.get?_cons_zero] at hm
        obtain rfl := Option.some.inj hm
        exact Or.inr howns
      | succ k =>
        rw [Stream'.Seq.get?_cons_succ, Stream'.Seq.get?_nil] at hm
        exact absurd hm (by simp)
  · change Function.update t r e.init = t
    rw [hinit]
    exact Function.update_eq_self r t
  · rw [AlterSeq.endState_map (Function.update t r) e hterm, hend]
  · rw [System.trace_map_state _ (inst r)]
    exact htr

end FamilyEmbedding

/-! ### The congruence -/

/-- `Function.update` preserves the pointwise family relation when the updated
coordinates are related. -/
private theorem update_rel {σC σA : Type} {R : ℕ → σC → σA → Prop}
    {s : ℕ → σC} {t : ℕ → σA} (hR : ∀ r, R r (s r) (t r)) {r : ℕ} {x : σC}
    {y : σA} (hxy : R r x y) (r' : ℕ) :
    R r' (Function.update s r x r') (Function.update t r y r') := by
  by_cases hr' : r' = r
  · subst hr'
    rw [Function.update_self, Function.update_self]
    exact hxy
  · rw [Function.update_of_ne hr', Function.update_of_ne hr']
    exact hR r'

/-- **Forward simulation is a congruence for `System.family`.** Per-instance
forward simulations `R r` lift to the pointwise relation on families, provided
the broadcast transforms are `R`-compatible (`hglob`). Silent/owned steps are
matched through the per-instance simulation and the coordinate embeddings;
broadcast and idle steps are matched by the abstract family's own one-step
broadcast/idle transitions. -/
theorem ForwardSimulation.family {σC σA : Type} {Label : Type} [Silent Label]
    {instC : ℕ → System σC Label} {instA : ℕ → System σA Label}
    {R : ℕ → σC → σA → Prop} (owns : Label → Option ℕ) (glob : Label → Prop)
    (actC : Label → σC → σC) (actA : Label → σA → σA)
    (sim : ∀ r, ForwardSimulation (instC r) (instA r) (R r))
    (hglob : ∀ l, glob l → ∀ r x y, R r x y → R r (actC l x) (actA l y)) :
    ForwardSimulation (System.family instC owns glob actC)
      (System.family instA owns glob actA)
      (fun s t => ∀ r, R r (s r) (t r)) := by
  constructor
  intro s t hR l μ hstep s' hs'
  rw [System.family_step_iff instC owns glob actC] at hstep
  rcases hstep with ⟨hτ, r, μr, hstepr, rfl⟩ | ⟨r, howns, μr, hstepr, rfl⟩ |
    ⟨hnτ, hnowns, hg, rfl⟩ | ⟨hnτ, hnowns, hng, rfl⟩
  · -- (i) silent instance step: match through `sim r`, embed silently.
    rw [PMF.mem_support_map_iff] at hs'
    obtain ⟨x, hx, rfl⟩ := hs'
    obtain ⟨y, hdisj, hRxy⟩ := (sim r).step (s r) (t r) (hR r) l μr hstepr x hx
    rcases hdisj with ⟨-, hsil⟩ | ⟨hnτ, -⟩
    · exact ⟨Function.update t r y,
        Or.inl ⟨hτ, System.weakLSilent_family owns glob actA hsil⟩,
        update_rel hR hRxy⟩
    · exact absurd hτ hnτ
  · -- (ii) owned instance step: match through `sim r`; a τ label goes through
    -- the silent embedding, an external one through the labelled embedding.
    rw [PMF.mem_support_map_iff] at hs'
    obtain ⟨x, hx, rfl⟩ := hs'
    obtain ⟨y, hdisj, hRxy⟩ := (sim r).step (s r) (t r) (hR r) l μr hstepr x hx
    rcases hdisj with ⟨hτ, hsil⟩ | ⟨hnτ, hlab⟩
    · exact ⟨Function.update t r y,
        Or.inl ⟨hτ, System.weakLSilent_family owns glob actA hsil⟩,
        update_rel hR hRxy⟩
    · exact ⟨Function.update t r y,
        Or.inr ⟨hnτ, System.weakLStep_family owns glob actA howns hlab⟩,
        update_rel hR hRxy⟩
  · -- (iii) broadcast: the abstract family broadcasts in one step.
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨fun r' => actA l (t r'),
      Or.inr ⟨hnτ, System.weakLStep_of_step hnτ
        ((System.family_step_iff instA owns glob actA).mpr
          (Or.inr (Or.inr (Or.inl ⟨hnτ, hnowns, hg, rfl⟩))))⟩, ?_⟩
    intro r'
    exact hglob l hg r' _ _ (hR r')
  · -- (iv) idle: the abstract family idles in one step.
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨t, Or.inr ⟨hnτ, System.weakLStep_of_step hnτ
      ((System.family_step_iff instA owns glob actA).mpr
        (Or.inr (Or.inr (Or.inr ⟨hnτ, hnowns, hng, rfl⟩))))⟩, hR⟩

end PLTS
