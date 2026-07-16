/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Other.Seq
import Leslie2.Other.Pmf

/-!
# Probabilistic Labelled Transition System (PLTS)

PLTS are the basic model used to represent protocols.
-/

open Stream'

namespace PLTS

structure System (State : Type) (Label : Type) where
  /-- The unique initial state of the system. -/
  init : State
  step : State → Label → PMF State → Prop

/-- An alternating sequence of states and labels: an initial state followed by a
possibly infinite sequence of `(label, next state)` transitions. -/
structure AlterSeq (State : Type) (Label : Type) where
  init : State
  trans : Seq (Label × State)

namespace AlterSeq

variable {State State' : Type} {Label : Type}

/-- Apply a state-transformation `f` pointwise to an `AlterSeq`, leaving labels
untouched. -/
def map (f : State → State') (e : AlterSeq State Label) : AlterSeq State' Label where
  init := f e.init
  trans := e.trans.map (fun lq => (lq.1, f lq.2))

/-- `AlterSeq.map` preserves termination: an execution is finite iff its image
under `map f` is. -/
@[simp] theorem map_trans_terminates_iff (f : State → State') (e : AlterSeq State Label) :
    (e.map f).trans.Terminates ↔ e.trans.Terminates :=
  Stream'.Seq.terminates_map_iff

/-- `AlterSeq.map f` is injective whenever `f` is. -/
theorem map_injective {f : State → State'} (hf : Function.Injective f) :
    Function.Injective (AlterSeq.map (Label := Label) f) := by
  rintro ⟨i₁, t₁⟩ ⟨i₂, t₂⟩ h
  have h_init : f i₁ = f i₂ := congr_arg AlterSeq.init h
  have h_trans :
      t₁.map (fun lq : Label × State => (lq.1, f lq.2))
      = t₂.map (fun lq : Label × State => (lq.1, f lq.2)) :=
    congr_arg AlterSeq.trans h
  obtain rfl := hf h_init
  congr 1
  apply Stream'.Seq.ext
  intro n
  have hn := congr_arg (·.get? n) h_trans
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
      obtain ⟨rfl, h_f⟩ := hn
      obtain rfl := hf h_f
      rfl

/-- `AlterSeq.map` commutes with appending a single transition. -/
theorem map_append_singleton (f : State → State') (e : AlterSeq State Label)
    (l : Label) (s : State) :
    (⟨e.init, e.trans.append (Seq.cons (l, s) Seq.nil)⟩ : AlterSeq State Label).map f
    = ⟨(e.map f).init, (e.map f).trans.append (Seq.cons (l, f s) Seq.nil)⟩ := by
  simp [AlterSeq.map, Stream'.Seq.map_append, Stream'.Seq.map_cons, Stream'.Seq.map_nil]

/-- The state reached after `n` transitions: position `0` is the initial state,
position `n + 1` is the destination of the `n`-th transition (or `none` if the
sequence has already terminated). -/
def stateAt (e : AlterSeq State Label) : ℕ → Option State
  | 0     => some e.init
  | n + 1 => (e.trans.get? n).map Prod.snd

/-- At the canonical terminating position `Nat.find h`, the state is defined. -/
lemma stateAt_find_isSome (e : AlterSeq State Label) (h : e.trans.Terminates) :
    (e.stateAt (Nat.find h)).isSome := by
  rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | hpos
  · rw [h0]; rfl
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hNotT : ¬ e.trans.TerminatedAt k :=
      Nat.find_min h (by rw [hk]; exact Nat.lt_succ_self k)
    rw [hk]
    change ((e.trans.get? k).map Prod.snd).isSome
    rw [Option.isSome_map]
    exact Option.isSome_iff_ne_none.mpr hNotT

lemma exists_endpoint (e : AlterSeq State Label) (h : e.trans.Terminates) :
    ∃ n s, e.trans.TerminatedAt n ∧ e.stateAt n = some s :=
  ⟨Nat.find h, (e.stateAt (Nat.find h)).get (stateAt_find_isSome e h),
    Nat.find_spec h, Option.eq_some_of_isSome _⟩

/-- The end-state of a finite alternating sequence: the state reached after
the last transition (or `e.init` if there are no transitions). Defined as
the state at the canonical terminating position `Nat.find h`. -/
noncomputable def endState (e : AlterSeq State Label) (h : e.trans.Terminates) :
    State :=
  (e.stateAt (Nat.find h)).get (stateAt_find_isSome e h)

/-- The end-state is the state at `Nat.find h`. -/
theorem stateAt_find_eq_endState (e : AlterSeq State Label)
    (h : e.trans.Terminates) :
    e.stateAt (Nat.find h) = some (e.endState h) :=
  Option.eq_some_of_isSome _

/-- If `e.trans = Seq.nil`, the `endState` of `e` is its `init`. -/
theorem endState_of_trans_nil
    (e : AlterSeq State Label) (h_nil : e.trans = Seq.nil)
    (h : e.trans.Terminates) :
    e.endState h = e.init := by
  have h_term0 : e.trans.TerminatedAt 0 := by
    rw [h_nil]; rfl
  have h_find : Nat.find h = 0 := (Nat.find_eq_zero h).mpr h_term0
  have h_stateAt := stateAt_find_eq_endState e h
  rw [h_find] at h_stateAt
  have h_zero : e.stateAt 0 = some e.init := rfl
  rw [h_zero] at h_stateAt
  exact (Option.some.inj h_stateAt).symm

/-- The `endState` of an alterSeq extended by appending a single transition
`(l, s)` is `s` (the destination of the appended transition). -/
theorem endState_append_singleton
    (e : AlterSeq State Label) (h : e.trans.Terminates)
    (l : Label) (s : State) :
    (⟨e.init, e.trans.append (Seq.cons (l, s) Seq.nil)⟩ : AlterSeq State Label).endState
      ⟨Nat.find h + 1, Stream'.Seq.terminatedAt_append_find h
        (show (Seq.cons (l, s) Seq.nil).TerminatedAt 1 from rfl)⟩ = s := by
  classical
  set new_e : AlterSeq State Label :=
    ⟨e.init, e.trans.append (Seq.cons (l, s) Seq.nil)⟩
  set new_h : new_e.trans.Terminates :=
    ⟨Nat.find h + 1, Stream'.Seq.terminatedAt_append_find h
      (show (Seq.cons (l, s) Seq.nil).TerminatedAt 1 from rfl)⟩
  -- Step 1: Nat.find new_h = Nat.find h + 1.
  have h_find : Nat.find new_h = Nat.find h + 1 := by
    apply le_antisymm
    · exact Nat.find_le (Stream'.Seq.terminatedAt_append_find h
        (show (Seq.cons (l, s) Seq.nil).TerminatedAt 1 from rfl))
    · -- Show Nat.find h + 1 ≤ Nat.find new_h via contradiction.
      by_contra h_not
      have h_lt_succ : Nat.find new_h < Nat.find h + 1 := Nat.not_le.mp h_not
      have h_le : Nat.find new_h ≤ Nat.find h := Nat.lt_succ_iff.mp h_lt_succ
      have h_term_spec : new_e.trans.TerminatedAt (Nat.find new_h) := Nat.find_spec new_h
      by_cases h_eq : Nat.find new_h = Nat.find h
      · -- Nat.find new_h = Nat.find h: new_e.trans.get? (Nat.find h) = some (l, s).
        have h_get : new_e.trans.get? (Nat.find h) = some (l, s) := by
          change (e.trans.append (Seq.cons (l, s) Seq.nil)).get? (Nat.find h) = _
          have := Stream'.Seq.get?_append_find h (Seq.cons (l, s) Seq.nil) 0
          rw [Nat.add_zero] at this; rw [this]; rfl
        rw [h_eq] at h_term_spec
        change new_e.trans.get? (Nat.find h) = none at h_term_spec
        rw [h_get] at h_term_spec
        exact absurd h_term_spec (by simp)
      · -- Nat.find new_h < Nat.find h: get? value is in e.trans.
        have hk' : Nat.find new_h < Nat.find h := lt_of_le_of_ne h_le h_eq
        have h_not_term_e : ¬ e.trans.TerminatedAt (Nat.find new_h) := Nat.find_min h hk'
        have h_get_eq : new_e.trans.get? (Nat.find new_h) = e.trans.get? (Nat.find new_h) :=
          Stream'.Seq.get?_append_before_length h_not_term_e
        change new_e.trans.get? (Nat.find new_h) = none at h_term_spec
        rw [h_get_eq] at h_term_spec
        exact h_not_term_e h_term_spec
  -- Step 2: new_e.stateAt (Nat.find h + 1) = some s.
  have h_state : new_e.stateAt (Nat.find h + 1) = some s := by
    change (new_e.trans.get? (Nat.find h)).map Prod.snd = some s
    have h_get : new_e.trans.get? (Nat.find h) = some (l, s) := by
      change (e.trans.append (Seq.cons (l, s) Seq.nil)).get? (Nat.find h) = _
      have := Stream'.Seq.get?_append_find h (Seq.cons (l, s) Seq.nil) 0
      rw [Nat.add_zero] at this
      rw [this]
      rfl
    rw [h_get]
    rfl
  -- Combine via stateAt_find_eq_endState.
  have h_stateAt := AlterSeq.stateAt_find_eq_endState new_e new_h
  rw [h_find, h_state] at h_stateAt
  exact (Option.some.inj h_stateAt).symm

/-- The `endState` of the singleton-transition alterSeq `⟨s₀, cons (l₀, s₁) nil⟩`
is `s₁`. Useful for matching constraints involving `endState` against `s₁`. -/
theorem endState_singleton_cons
    (s₀ : State) (l₀ : Label) (s₁ : State) :
    (⟨s₀, Seq.cons (l₀, s₁) Seq.nil⟩ : AlterSeq State Label).endState
      (Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil) = s₁ := by
  set h_hist_term : (Seq.cons (l₀, s₁) Seq.nil : Seq (Label × State)).Terminates :=
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
  have h_find : Nat.find h_hist_term = 1 := by
    apply le_antisymm
    · exact Nat.find_le (show (Seq.cons (l₀, s₁) Seq.nil).TerminatedAt 1 from rfl)
    · rw [Nat.one_le_iff_ne_zero]
      intro h_zero
      exact Stream'.Seq.cons_not_terminatedAt_zero
        (h_zero ▸ Nat.find_spec h_hist_term)
  have h_eq := AlterSeq.stateAt_find_eq_endState
    ({ init := s₀, trans := Seq.cons (l₀, s₁) Seq.nil
      : AlterSeq State Label }) h_hist_term
  rw [h_find] at h_eq
  exact (Option.some.inj h_eq).symm

end AlterSeq

variable {State : Type} {Label : Type}

def is_partial_exec (e : AlterSeq State Label) (sys : System State Label) : Prop :=
  ∀ n l s', e.trans.get? n = some (l, s') →
    ∃ s μ, e.stateAt n = some s ∧ sys.step s l μ ∧ s' ∈ μ.support

def is_exec (e : AlterSeq State Label) (sys : System State Label) : Prop :=
  is_partial_exec e sys ∧ sys.init = e.init

/-- A randomized scheduler for a PLTS `sys`. Given a finite execution prefix it
either returns `none` (the scheduler stops on this prefix, producing no further
step) or `some` distribution over the next step `(label, distribution)` of the
system. The well-formedness condition `valid` requires every step in the support
of a `some` output to be a valid transition of `sys` from the current state. -/
structure Scheduler (sys : System State Label) where
  next : AlterSeq State Label → PMF (Option (Label × PMF State))
  valid : ∀ (e : AlterSeq State Label) (n : ℕ) (s : State),
    e.trans.TerminatedAt n → e.stateAt n = some s →
    ∀ (l : Label) (μ : PMF State),
      some (l, μ) ∈ (next e).support → sys.step s l μ

/-- A probabilistic execution: a unique initial state together with a scheduler
resolving each step of the trace. -/
structure ProbabilisticExecution (sys : System State Label) where
  /-- The unique initial state of this execution. -/
  initState : PMF State
  scheduler : Scheduler sys

namespace ProbabilisticExecution

variable {sys : System State Label}

/-- The initial distribution alias: `pe.init = pe.initState`. The `init`
projection is kept for code that uniformly reads `pe.init` regardless of how
the structure stores the initial distribution. -/
noncomputable def init (pe : ProbabilisticExecution sys) : PMF State :=
  pe.initState

@[simp] theorem init_eq_initState (pe : ProbabilisticExecution sys) :
    pe.init = pe.initState := rfl

/-- The one-step kernel of a probabilistic execution. Given a finite prefix `e`
and a concrete next step `(l, s')`, returns the probability mass that the
scheduler emits `(l, s')` as the next step. With the PMF-out-Option scheduler
shape, this aggregates over all `μ : PMF State` that the scheduler might emit
alongside label `l`, weighted by the emission probability and `μ s'`:

  `kernel pe e (l, s') = ∑' μ, pe.scheduler.next e (some (l, μ)) * μ s'` -/
noncomputable def kernel (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (step : Label × State) : ENNReal :=
  ∑' μ, pe.scheduler.next e (some (step.1, μ)) * μ step.2

/-- The one-step kernel is bounded by `1`. -/
theorem kernel_le_one (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (step : Label × State) :
    pe.kernel e step ≤ 1 := by
  unfold kernel
  calc ∑' μ, pe.scheduler.next e (some (step.1, μ)) * μ step.2
      ≤ ∑' μ, pe.scheduler.next e (some (step.1, μ)) := by
        refine ENNReal.tsum_le_tsum (fun μ => ?_)
        exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
    _ ≤ ∑' (lμ : Label × PMF State), pe.scheduler.next e (some lμ) := by
        exact ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun μ => (step.1, μ))
          (fun μ₁ μ₂ h_eq => (Prod.mk.inj h_eq).2)
          (fun lμ => pe.scheduler.next e (some lμ))
    _ ≤ ∑' opt, pe.scheduler.next e opt := by
        exact ENNReal.tsum_comp_le_tsum_of_injective
          (f := some) (fun _ _ h => Option.some.inj h)
          (fun opt => pe.scheduler.next e opt)
    _ = 1 := (pe.scheduler.next e).tsum_coe

/-- The probability that the probabilistic execution `pe` produces the finite
concrete execution `e`.

Defined recursively from the END of the transition list (cons-end form):
* base (`e.trans = Seq.nil`): the initial mass `pe.init e.init`;
* step (`e.trans = sq.append (Seq.cons (l, s') Seq.nil)`): the probability of
  the truncated execution `⟨e.init, sq⟩` times the one-step kernel
  `pe.kernel ⟨e.init, sq⟩ (l, s')`.

Implementation reduces `e.trans` to a finite list via `Stream'.Seq.toList hFin`
and uses `List.reverseRecOn` (reverse / cons-end induction). The cons-end
factorisation `probOf_append_singleton` is then near-definitional. -/
noncomputable def probOf (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (hFin : e.trans.Terminates) : ENNReal :=
  (e.trans.toList hFin).reverseRecOn
    (motive := fun _ => ENNReal)
    (pe.init e.init)
    (fun rest last ih => ih * pe.kernel ⟨e.init, Seq.ofList rest⟩ last)

/-- `probOf` on an execution with empty trans reduces to the initial mass. -/
@[simp] theorem probOf_nil (pe : ProbabilisticExecution sys) (s₀ : State) :
    pe.probOf ⟨s₀, Seq.nil⟩ Stream'.Seq.terminates_nil = pe.init s₀ := by
  unfold probOf
  simp [Stream'.Seq.toList_nil]

/-- **Cons-end factorisation** (near-definitional from the cons-end recursion):
appending a single transition `last` at the end multiplies `probOf` by the
one-step kernel at the truncated prefix. -/
theorem probOf_append_singleton (pe : ProbabilisticExecution sys)
    (s₀ : State) (sq : Seq (Label × State)) (h_sq : sq.Terminates)
    (last : Label × State)
    (h_app : (sq.append (Seq.cons last Seq.nil)).Terminates) :
    pe.probOf ⟨s₀, sq.append (Seq.cons last Seq.nil)⟩ h_app =
      pe.probOf ⟨s₀, sq⟩ h_sq * pe.kernel ⟨s₀, sq⟩ last := by
  unfold probOf
  have h_singleton_term : (Seq.cons last Seq.nil : Seq (Label × State)).Terminates :=
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil
  have h_toList : (sq.append (Seq.cons last Seq.nil)).toList h_app =
      sq.toList h_sq ++ [last] := by
    rw [Stream'.Seq.toList_append sq (Seq.cons last Seq.nil) h_sq h_singleton_term h_app]
    congr 1
    rw [Stream'.Seq.toList_cons]
    simp [Stream'.Seq.toList_nil]
  -- (⟨s₀, sq.append (cons last nil)⟩).trans = sq.append (cons last nil),
  -- so its toList equals sq.toList h_sq ++ [last] by h_toList.
  rw [show (⟨s₀, sq.append (Seq.cons last Seq.nil)⟩ : AlterSeq State Label).trans.toList h_app
        = sq.toList h_sq ++ [last] from h_toList]
  rw [List.reverseRecOn_concat]
  -- Seq.ofList (sq.toList h_sq) = sq.
  rw [Stream'.Seq.ofList_toList sq h_sq]

/-- `probOf e ≤ pe.init e.init`: a finite execution's probability is bounded by
the mass on its starting state. -/
theorem probOf_le_init (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (hFin : e.trans.Terminates) :
    pe.probOf e hFin ≤ pe.init e.init := by
  unfold probOf
  induction e.trans.toList hFin using List.reverseRecOn with
  | nil =>
    rw [List.reverseRecOn_nil]
  | append_singleton rest last _ih =>
    rw [List.reverseRecOn_concat]
    calc rest.reverseRecOn (motive := fun _ => ENNReal) (pe.init e.init) _
            * pe.kernel ⟨e.init, Seq.ofList rest⟩ last
        ≤ pe.init e.init * 1 := by gcongr; exact pe.kernel_le_one _ _
      _ = pe.init e.init := mul_one _

/-- `probOf` depends only on the execution, not on the chosen termination proof:
equal executions have equal `probOf` (the `Terminates` proofs being irrelevant). -/
theorem probOf_congr (pe : ProbabilisticExecution sys)
    (e e' : AlterSeq State Label) (h_eq : e = e')
    (hFin : e.trans.Terminates) (hFin' : e'.trans.Terminates) :
    pe.probOf e hFin = pe.probOf e' hFin' := by
  subst h_eq; rfl

end ProbabilisticExecution

/-!
# Execution-structure helpers

Two generic `AlterSeq.endState` lemmas used downstream (by `TraceMap` /
`SimulationTrace`): `endState` is invariant under equality of the underlying
`AlterSeq`, and `endState` equals the `.2` of the last transition (or `init` when
there are none).
-/

/-- `endState` depends only on the underlying `AlterSeq` (termination proofs are
irrelevant). -/
theorem AlterSeq.endState_congr_pub {e₁ e₂ : AlterSeq State Label}
    (heq : e₁ = e₂) (h₁ : e₁.trans.Terminates) (h₂ : e₂.trans.Terminates) :
    e₁.endState h₁ = e₂.endState h₂ := by subst heq; rfl

/-- `endState e` is the `.2` of the last transition of `e` (or `e.init` if there
are none), read off `e.trans.toList`. -/
theorem AlterSeq.endState_eq_getLast? (e : AlterSeq State Label) (h : e.trans.Terminates) :
    e.endState h = ((e.trans.toList h).getLast?).elim e.init Prod.snd := by
  classical
  rcases Nat.eq_zero_or_pos (e.trans.length h) with hl | hl
  · have htoNil : e.trans.toList h = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Stream'.Seq.length_toList]; exact hl
    have hnil : e.trans = Seq.nil := by
      have := Stream'.Seq.ofList_toList e.trans h
      rw [htoNil] at this; rw [← this]; rfl
    rw [AlterSeq.endState_of_trans_nil e hnil h, htoNil]; rfl
  · have hgl : (e.trans.toList h).getLast? = e.trans.get? (e.trans.length h - 1) :=
      Stream'.Seq.getLast?_toList e.trans h
    have hfind : Nat.find h = e.trans.length h := rfl
    have hes := AlterSeq.stateAt_find_eq_endState e h
    rw [hfind] at hes
    obtain ⟨m, hm⟩ : ∃ m, e.trans.length h = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
    rw [hm] at hes
    change (e.trans.get? m).map Prod.snd = some (e.endState h) at hes
    rw [hgl, hm, Nat.add_sub_cancel]
    cases hg : e.trans.get? m with
    | none => rw [hg] at hes; simp at hes
    | some p =>
      rw [hg] at hes; simp only [Option.map_some, Option.some.injEq] at hes; simp [hes]

/-! ### Kraft-bound infrastructure: front-peel of `probOf`

Generic machinery over an arbitrary `System`,
preparing an upcoming Kraft-style bound. We bound the total one-step kernel
mass by `1`, factor `probOf` as the initial mass times a *conditional path
weight* `pathWeight`, and prove the key front-peel recursion on `pathWeight`. -/

/-- The total one-step kernel mass over all next steps is `≤ 1`. -/
theorem ProbabilisticExecution.kernel_tsum_le_one {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) :
    (∑' p : Label × State, pe.kernel e p) ≤ 1 := by
  calc (∑' p : Label × State, pe.kernel e p)
      = ∑' (l : Label) (s' : State), pe.kernel e (l, s') := by
        rw [ENNReal.tsum_prod']
    _ = ∑' (l : Label) (s' : State) (μ : PMF State),
          pe.scheduler.next e (some (l, μ)) * μ s' := by rfl
    _ = ∑' (l : Label) (μ : PMF State) (s' : State),
          pe.scheduler.next e (some (l, μ)) * μ s' := by
        refine tsum_congr fun l => ?_
        exact ENNReal.tsum_comm
    _ = ∑' (l : Label) (μ : PMF State), pe.scheduler.next e (some (l, μ)) := by
        refine tsum_congr fun l => tsum_congr fun μ => ?_
        rw [ENNReal.tsum_mul_left, μ.tsum_coe, mul_one]
    _ = ∑' lμ : Label × PMF State, pe.scheduler.next e (some lμ) := by
        rw [ENNReal.tsum_prod']
    _ ≤ ∑' opt, pe.scheduler.next e opt :=
        ENNReal.tsum_comp_le_tsum_of_injective (f := fun lμ : Label × PMF State => some lμ)
          (fun _ _ h => Option.some.inj h) _
    _ = 1 := (pe.scheduler.next e).tsum_coe

/-- The conditional path weight of a transition list `trans` given a base
history `base`: the product of one-step kernels along `trans`, each evaluated at
`base` extended by the already-consumed prefix. End-recursive, mirroring `probOf`. -/
noncomputable def ProbabilisticExecution.pathWeight {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (base : AlterSeq State Label) (trans : List (Label × State)) : ENNReal :=
  trans.reverseRecOn (motive := fun _ => ENNReal) 1
    (fun rest last ih => ih * pe.kernel ⟨base.init, base.trans.append (Seq.ofList rest)⟩ last)

/-- `probOf` factors as the initial mass times the conditional path weight from
the empty base. -/
theorem ProbabilisticExecution.probOf_eq_pathWeight {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (s₀ : State) (trans : List (Label × State))
    (hFin : (Seq.ofList trans : Seq (Label × State)).Terminates) :
    pe.probOf ⟨s₀, Seq.ofList trans⟩ hFin
      = pe.init s₀ * pe.pathWeight ⟨s₀, Seq.nil⟩ trans := by
  induction trans using List.reverseRecOn with
  | nil =>
    unfold ProbabilisticExecution.probOf ProbabilisticExecution.pathWeight
    rw [Stream'.Seq.toList_ofList, List.reverseRecOn_nil, List.reverseRecOn_nil, mul_one]
  | append_singleton rest last ih =>
    have hL : pe.probOf { init := s₀, trans := ↑(rest ++ [last]) } hFin
        = pe.init s₀ * pe.pathWeight { init := s₀, trans := Seq.nil } rest
          * pe.kernel { init := s₀, trans := ↑rest } last := by
      unfold ProbabilisticExecution.probOf
      rw [Stream'.Seq.toList_ofList, List.reverseRecOn_concat]
      rw [← ih (Stream'.Seq.terminates_ofList rest)]
      unfold ProbabilisticExecution.probOf
      rw [Stream'.Seq.toList_ofList]
    rw [hL]
    unfold ProbabilisticExecution.pathWeight
    rw [List.reverseRecOn_concat]
    simp only [Stream'.Seq.nil_append]
    ring

/-- Front-peel: the path weight of `(l, s') :: rest` is the first kernel step times
the path weight of `rest` from the base extended by `(l, s')`. -/
theorem ProbabilisticExecution.pathWeight_cons {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (base : AlterSeq State Label) (l : Label) (s' : State)
    (rest : List (Label × State)) :
    pe.pathWeight base ((l, s') :: rest)
      = pe.kernel base (l, s')
        * pe.pathWeight ⟨base.init, base.trans.append (Seq.cons (l, s') Seq.nil)⟩ rest := by
  induction rest using List.reverseRecOn with
  | nil =>
    unfold ProbabilisticExecution.pathWeight
    rw [show ((l, s') :: [] : List (Label × State)) = [] ++ [(l, s')] from rfl]
    rw [List.reverseRecOn_concat, List.reverseRecOn_nil, List.reverseRecOn_nil]
    simp only [Stream'.Seq.ofList_nil, Stream'.Seq.append_nil, one_mul, mul_one]
  | append_singleton rest' last ih =>
    have hhist : base.trans.append (Seq.ofList ((l, s') :: rest'))
        = (base.trans.append (Seq.cons (l, s') Seq.nil)).append (Seq.ofList rest') := by
      rw [Stream'.Seq.ofList_cons, Stream'.Seq.append_assoc, Stream'.Seq.cons_append,
        Stream'.Seq.nil_append]
    have hcons : ((l, s') :: (rest' ++ [last]) : List (Label × State))
        = ((l, s') :: rest') ++ [last] := rfl
    rw [hcons]
    unfold ProbabilisticExecution.pathWeight
    rw [List.reverseRecOn_concat, List.reverseRecOn_concat]
    have ih' := ih
    unfold ProbabilisticExecution.pathWeight at ih'
    rw [ih', hhist]
    ring

/-- **Append split for `pathWeight`.** The path weight of `L₁ ++ L₂` from `base`
factors as the path weight of `L₁` times the path weight of `L₂` from the base
extended by `L₁`. -/
theorem ProbabilisticExecution.pathWeight_append {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (base : AlterSeq State Label) (L₁ L₂ : List (Label × State)) :
    pe.pathWeight base (L₁ ++ L₂)
      = pe.pathWeight base L₁
        * pe.pathWeight ⟨base.init, base.trans.append (Seq.ofList L₁)⟩ L₂ := by
  induction L₂ using List.reverseRecOn with
  | nil =>
    rw [List.append_nil]
    have : pe.pathWeight ⟨base.init, base.trans.append (Seq.ofList L₁)⟩ [] = 1 := by
      unfold ProbabilisticExecution.pathWeight; rw [List.reverseRecOn_nil]
    rw [this, mul_one]
  | append_singleton rest last ih =>
    rw [← List.append_assoc]
    unfold ProbabilisticExecution.pathWeight
    rw [List.reverseRecOn_concat, List.reverseRecOn_concat]
    have ih' := ih
    unfold ProbabilisticExecution.pathWeight at ih'
    rw [ih']
    have hhist : base.trans.append (Seq.ofList (L₁ ++ rest))
        = (base.trans.append (Seq.ofList L₁)).append (Seq.ofList rest) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.append_assoc]
    rw [hhist]
    ring

/-- **Finite-antichain Kraft bound.** For a prefix-free finite set `F` of
transition lists, the total `pathWeight` from any base is `≤ 1`. (Distinct tight
trace-cone executions are prefix-free, so this bounds the trace probability.) -/
theorem ProbabilisticExecution.pathWeight_antichain {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (base : AlterSeq State Label) (F : Finset (List (Label × State)))
    (hpf : ∀ t ∈ F, ∀ t' ∈ F, t <+: t' → t = t') :
    (∑ t ∈ F, pe.pathWeight base t) ≤ 1 := by
  classical
  suffices aux : ∀ (N : ℕ) (base : AlterSeq State Label)
      (F : Finset (List (Label × State))),
      (∀ t ∈ F, t.length ≤ N) →
      (∀ t ∈ F, ∀ t' ∈ F, t <+: t' → t = t') →
      (∑ t ∈ F, pe.pathWeight base t) ≤ 1 by
    exact aux (F.sup List.length) base F (fun t ht => Finset.le_sup ht) hpf
  intro N
  induction N with
  | zero =>
    intro base F hlen hpf
    -- every t ∈ F has length ≤ 0, so t = []; hence F ⊆ {[]}
    have hsub : F ⊆ {([] : List (Label × State))} := by
      intro t ht
      have : t = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (hlen t ht))
      simp [this]
    calc (∑ t ∈ F, pe.pathWeight base t)
        ≤ ∑ t ∈ ({([] : List (Label × State))} : Finset _), pe.pathWeight base t :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => bot_le)
      _ = pe.pathWeight base [] := Finset.sum_singleton _ _
      _ = 1 := by unfold ProbabilisticExecution.pathWeight; rw [List.reverseRecOn_nil]
  | succ N ih =>
    intro base F hlen hpf
    by_cases hnil : ([] : List (Label × State)) ∈ F
    · -- `[] ∈ F`: prefix-freeness forces every member to equal `[]`.
      have hsub : F ⊆ {([] : List (Label × State))} := by
        intro t ht
        have : ([] : List (Label × State)) = t := hpf [] hnil t ht List.nil_prefix
        simp [← this]
      calc (∑ t ∈ F, pe.pathWeight base t)
          ≤ ∑ t ∈ ({([] : List (Label × State))} : Finset _), pe.pathWeight base t :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => bot_le)
        _ = pe.pathWeight base [] := Finset.sum_singleton _ _
        _ = 1 := by unfold ProbabilisticExecution.pathWeight; rw [List.reverseRecOn_nil]
    · -- `[] ∉ F`: every member is nonempty; group by first element.
      -- group by the head (as an `Option`, so no `Inhabited` is needed)
      set T : Finset (Option (Label × State)) := F.image List.head? with hT
      have hmaps : ∀ t ∈ F, t.head? ∈ T := fun t ht => Finset.mem_image_of_mem _ ht
      rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun t => pe.pathWeight base t)]
      -- now: ∑ o ∈ T, ∑ t ∈ F with t.head? = o, pathWeight base t ≤ 1
      -- per-fiber bound `b`: kernel mass on `some p`, `0` on `none`.
      set b : Option (Label × State) → ENNReal :=
        fun o => o.elim 0 (fun p => pe.kernel base p) with hb
      have hfib : ∀ j ∈ T, (∑ i ∈ F with i.head? = j, pe.pathWeight base i) ≤ b j := by
        intro j hj
        cases j with
        | none =>
          -- the fiber over `none` is empty: `t.head? = none ↔ t = []`, and `[] ∉ F`.
          have hempty : (F.filter (fun i => i.head? = none)) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro t ht
            rw [List.head?_eq_none_iff]
            intro hnull
            exact hnil (hnull ▸ ht)
          rw [hempty, Finset.sum_empty]
          exact bot_le
        | some p =>
          obtain ⟨l, s'⟩ := p
          set base' : AlterSeq State Label :=
            ⟨base.init, base.trans.append (Seq.cons (l, s') Seq.nil)⟩ with hbase'
          -- every `t` in the fiber is `(l, s') :: t.tail`
          have hfiber_cons : ∀ t ∈ F.filter (fun i => i.head? = some (l, s')),
              t = (l, s') :: t.tail := by
            intro t ht
            rw [Finset.mem_filter] at ht
            exact (List.cons_head?_tail (a := (l, s')) ht.2).symm
          set Ft : Finset (List (Label × State)) := F.filter (fun i => i.head? = some (l, s'))
            with hFt
          -- step 1: rewrite each fiber summand via `pathWeight_cons`
          have hstep : (∑ i ∈ Ft, pe.pathWeight base i)
              = ∑ i ∈ Ft, pe.kernel base (l, s') * pe.pathWeight base' i.tail := by
            refine Finset.sum_congr rfl fun t ht => ?_
            conv_lhs => rw [hfiber_cons t ht]
            rw [pe.pathWeight_cons base l s' t.tail]
          rw [hstep, ← Finset.mul_sum]
          -- step 2: reindex the tail sum onto `Gt := Ft.image List.tail`
          set Gt : Finset (List (Label × State)) := Ft.image List.tail with hGt
          have hinj : Set.InjOn List.tail (Ft : Set (List (Label × State))) := by
            intro a ha b hb hab
            have ea := hfiber_cons a ha
            have eb := hfiber_cons b hb
            rw [ea, eb, hab]
          have hreindex : (∑ i ∈ Ft, pe.pathWeight base' i.tail)
              = ∑ u ∈ Gt, pe.pathWeight base' u := by
            rw [hGt, Finset.sum_image hinj]
          rw [hreindex]
          -- step 3: bound the tail sum by `1` via `ih base' Gt`
          have hbound : (∑ u ∈ Gt, pe.pathWeight base' u) ≤ 1 := by
            apply ih base' Gt
            · -- length bound: tails have length ≤ N
              intro u hu
              rw [hGt, Finset.mem_image] at hu
              obtain ⟨t, ht, rfl⟩ := hu
              have htF : t ∈ F := (Finset.mem_filter.mp (hFt ▸ ht)).1
              have htne : t = (l, s') :: t.tail := hfiber_cons t ht
              have : t.length = t.tail.length + 1 := by
                conv_lhs => rw [htne]
                simp
              have hle := hlen t htF
              omega
            · -- prefix-free of `Gt`
              intro u₁ hu₁ u₂ hu₂ hpre
              rw [hGt, Finset.mem_image] at hu₁ hu₂
              obtain ⟨t₁, ht₁, rfl⟩ := hu₁
              obtain ⟨t₂, ht₂, rfl⟩ := hu₂
              have e₁ : t₁ = (l, s') :: t₁.tail := hfiber_cons t₁ ht₁
              have e₂ : t₂ = (l, s') :: t₂.tail := hfiber_cons t₂ ht₂
              have ht₁F : t₁ ∈ F := (Finset.mem_filter.mp (hFt ▸ ht₁)).1
              have ht₂F : t₂ ∈ F := (Finset.mem_filter.mp (hFt ▸ ht₂)).1
              have hpre' : t₁ <+: t₂ := by
                rw [e₁, e₂]
                exact (List.cons_prefix_cons).mpr ⟨rfl, hpre⟩
              have := hpf t₁ ht₁F t₂ ht₂F hpre'
              -- t₁ = t₂ ⟹ tails equal
              rw [e₁, e₂] at this
              exact List.cons.inj this |>.2
          -- conclude
          calc pe.kernel base (l, s') * ∑ u ∈ Gt, pe.pathWeight base' u
              ≤ pe.kernel base (l, s') * 1 := by gcongr
            _ = b (some (l, s')) := by rw [mul_one, hb]; rfl
      calc (∑ j ∈ T, ∑ i ∈ F with i.head? = j, pe.pathWeight base i)
          ≤ ∑ j ∈ T, b j := Finset.sum_le_sum hfib
        _ ≤ ∑' j : Option (Label × State), b j := ENNReal.sum_le_tsum T
        _ = ∑' p : Label × State, pe.kernel base p := by
            have hsupp : Function.support b ⊆ Set.range (Option.some : (Label × State) → _) := by
              intro j hj
              cases j with
              | none => simp [hb, Function.mem_support] at hj
              | some p => exact ⟨p, rfl⟩
            have := (Option.some_injective (Label × State)).tsum_eq (f := b) hsupp
            simpa [hb] using this.symm
        _ ≤ 1 := pe.kernel_tsum_le_one base

/-- **Execution-level antichain Kraft bound.** For a finite set `F` of terminating
executions that is prefix-free among executions sharing an initial state, the total
`probOf` is `≤ 1`. Proven by grouping on the initial state and applying
`pathWeight_antichain` to each group, then `∑ initState ≤ 1`. -/
theorem ProbabilisticExecution.probOf_antichain {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (F : Finset (AlterSeq State Label))
    (hterm : ∀ e ∈ F, e.trans.Terminates)
    (hpf : ∀ e (he : e ∈ F) e' (he' : e' ∈ F), e.init = e'.init →
        e.trans.toList (hterm e he) <+: e'.trans.toList (hterm e' he') → e = e') :
    (∑ e ∈ F.attach, pe.probOf e.1 (hterm e.1 e.2)) ≤ 1 := by
  classical
  -- Per-element factorisation of `probOf` through `pathWeight`.
  -- Generic factorisation through `pathWeight`, for any execution and any
  -- termination proof. Stated over fields so the dependent proof can be
  -- generalised cleanly.
  have hfactor : ∀ (s₀ : State) (sq : Seq (Label × State)) (h : sq.Terminates),
      pe.probOf ⟨s₀, sq⟩ h
        = pe.init s₀ * pe.pathWeight ⟨s₀, Seq.nil⟩ (sq.toList h) := by
    intro s₀ sq h
    have heq : (Seq.ofList (sq.toList h) : Seq (Label × State)) = sq :=
      Stream'.Seq.ofList_toList sq h
    -- Move to the `ofList` form, generalising `h` so the rewrite is valid.
    generalize hL : sq.toList h = L
    rw [hL] at heq
    subst heq
    exact pe.probOf_eq_pathWeight s₀ L h
  -- Rewrite each summand via `hfactor`.
  have hrw : (∑ e ∈ F.attach, pe.probOf e.1 (hterm e.1 e.2))
      = ∑ e ∈ F.attach,
          pe.init (e.1).init
            * pe.pathWeight ⟨(e.1).init, Seq.nil⟩ ((e.1).trans.toList (hterm e.1 e.2)) := by
    refine Finset.sum_congr rfl fun e _ => ?_
    exact hfactor (e.1).init (e.1).trans (hterm e.1 e.2)
  rw [hrw]
  -- Group by initial state.
  set g : {x // x ∈ F} → State := fun e => (e.1).init with hg
  have hmaps : ∀ e ∈ F.attach, g e ∈ F.attach.image g :=
    fun e he => Finset.mem_image_of_mem g he
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun e => pe.init (e.1).init
      * pe.pathWeight ⟨(e.1).init, Seq.nil⟩ ((e.1).trans.toList (hterm e.1 e.2)))]
  -- Per-fiber bound: the `s₀`-fiber sum is `≤ pe.init s₀`.
  have hfib : ∀ s₀ ∈ F.attach.image g,
      (∑ i ∈ F.attach with g i = s₀,
        pe.init (i.1).init
          * pe.pathWeight ⟨(i.1).init, Seq.nil⟩ ((i.1).trans.toList (hterm i.1 i.2)))
        ≤ pe.init s₀ := by
    intro s₀ _
    set Fs : Finset {x // x ∈ F} := F.attach.filter (fun i => g i = s₀) with hFs
    -- On `Fs`, every `i` has `(↑i).init = s₀`.
    have hinit : ∀ i ∈ Fs, (i.1).init = s₀ := by
      intro i hi
      rw [hFs, Finset.mem_filter] at hi
      exact hi.2
    -- Rewrite each fiber summand to `pe.init s₀ * pathWeight ⟨s₀, nil⟩ (toList i)`.
    have hsum_eq : (∑ i ∈ Fs,
          pe.init (i.1).init
            * pe.pathWeight ⟨(i.1).init, Seq.nil⟩ ((i.1).trans.toList (hterm i.1 i.2)))
        = pe.init s₀
          * ∑ i ∈ Fs, pe.pathWeight ⟨s₀, Seq.nil⟩ ((i.1).trans.toList (hterm i.1 i.2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hinit i hi]
    rw [hsum_eq]
    -- Reindex the pathWeight sum onto the image of `toList`.
    set tl : {x // x ∈ F} → List (Label × State) :=
      fun i => (i.1).trans.toList (hterm i.1 i.2) with htl
    set Ts : Finset (List (Label × State)) := Fs.image tl with hTs
    have hinj : Set.InjOn tl (Fs : Set {x // x ∈ F}) := by
      intro a ha b hb hab
      apply Subtype.ext
      refine hpf a.1 a.2 b.1 b.2 ?_ ?_
      · rw [hinit a ha, hinit b hb]
      · rw [show a.1.trans.toList (hterm a.1 a.2) = tl a from rfl,
          show b.1.trans.toList (hterm b.1 b.2) = tl b from rfl, hab]
    have hreindex : (∑ i ∈ Fs, pe.pathWeight ⟨s₀, Seq.nil⟩ (tl i))
        = ∑ u ∈ Ts, pe.pathWeight ⟨s₀, Seq.nil⟩ u := by
      rw [hTs, Finset.sum_image hinj]
    rw [show (∑ i ∈ Fs, pe.pathWeight ⟨s₀, Seq.nil⟩ ((i.1).trans.toList (hterm i.1 i.2)))
        = ∑ i ∈ Fs, pe.pathWeight ⟨s₀, Seq.nil⟩ (tl i) from rfl, hreindex]
    -- `Ts` is prefix-free, so `pathWeight_antichain` bounds the sum by `1`.
    have hpf' : ∀ t ∈ Ts, ∀ t' ∈ Ts, t <+: t' → t = t' := by
      intro t ht t' ht' hpre
      rw [hTs, Finset.mem_image] at ht ht'
      obtain ⟨a, ha, rfl⟩ := ht
      obtain ⟨b, hb, rfl⟩ := ht'
      have : a = b := by
        apply Subtype.ext
        refine hpf a.1 a.2 b.1 b.2 ?_ ?_
        · rw [hinit a ha, hinit b hb]
        · exact hpre
      rw [this]
    have hbound : (∑ u ∈ Ts, pe.pathWeight ⟨s₀, Seq.nil⟩ u) ≤ 1 :=
      pe.pathWeight_antichain ⟨s₀, Seq.nil⟩ Ts hpf'
    calc pe.init s₀ * ∑ u ∈ Ts, pe.pathWeight ⟨s₀, Seq.nil⟩ u
        ≤ pe.init s₀ * 1 := by gcongr
      _ = pe.init s₀ := mul_one _
  calc (∑ j ∈ F.attach.image g,
          ∑ i ∈ F.attach with g i = j,
            pe.init (i.1).init
              * pe.pathWeight ⟨(i.1).init, Seq.nil⟩ ((i.1).trans.toList (hterm i.1 i.2)))
      ≤ ∑ j ∈ F.attach.image g, pe.init j := Finset.sum_le_sum hfib
    _ ≤ ∑' s₀ : State, pe.init s₀ := ENNReal.sum_le_tsum _
    _ = 1 := by rw [pe.init_eq_initState]; exact pe.initState.tsum_coe

end PLTS
